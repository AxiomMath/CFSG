module

public import CFSG.LocalAnalysis.StandardType.GGKG82Defs
import CFSG.LocalAnalysis.StandardType.GGKG82FieldScTorus
import CFSG.LocalAnalysis.StandardType.GGKG82FieldTransport
import CFSG.HardMathSupport.Malle.Proving.CoverThreeField
import CFSG.RankThree.PartTwo.Sec12.Hering129GMod9Mat
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Frame

public section

namespace CFSG.StandardType.KG82

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed CFSG.StandardType.TwE6Lang
  CFSG.StandardType.E6Dep.ZL

theorem exists_inn_rankFive_fieldFixed
    {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) {f : MulAut (TwE6Delta.RecipeR K n)}
    (hf : f ∈ RecipeF K n) (hf3 : orderOf f = 3) :
    ∃ E U : Subgroup (TwE6Delta.RecipeR K n), IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set (TwE6Delta.RecipeR K n)) ∧
      (∀ e ∈ E, f e = e) ∧ (∀ u ∈ U, f u = u) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ n :=
    ⟨iterateFrobeniusEquiv K 2 n, fun c => by
      rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]⟩
  set θ : K →+* K := σ.toRingHom
  have hθ' : ∀ c, θ c = c ^ 2 ^ n := hσ
  have hθθ : ∀ c, θ (θ c) = c := theta_theta_of_card hK hθ'
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨π, hπ1, hπf⟩ := exists_sc_fieldHom hn hK σ hσ
  obtain ⟨δ, hδord, hδfix⟩ := hπf f hf
  have hδ3 : orderOf δ = 3 := hδord.symm.trans hf3
  have hδpow : δ ^ 3 = 1 := by rw [← hδ3]; exact pow_orderOf_eq_one δ
  have h9 : 9 ∣ 2 ^ n + 1 :=
    CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.nine_dvd_add_one_of_orderOf_three
      ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩ hδ3 h3
  have h9K : 9 ∣ Nat.card Kˣ := by
    have h := Nat.sq_sub_sq (2 ^ n) 1
    rw [one_pow] at h
    rw [Nat.card_units, hK, h]
    exact Dvd.dvd.mul_right h9 _
  obtain ⟨η, hη⟩ := CFSG.RankThree.PartTwo.Sec12.Hering129G.exists_unit_orderOf_nine h9K
  have hη9 : η ^ 9 = 1 := by rw [← hη]; exact pow_orderOf_eq_one η
  obtain ⟨i, hi3, hδη⟩ := exists_units_map_eq_pow hδpow hη
  obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t + 1 := ⟨i / 3, by omega⟩
  have hθη : Units.map (θ : K →* K) η = η ^ ((2 ^ n : ℕ) : ℤ) := by
    refine Units.ext ?_
    rw [Units.coe_map, zpow_natCast, Units.val_pow_eq_pow_val]
    exact hθ' η
  have hηm : η ^ (((2 ^ n : ℕ) : ℤ) + 1) = 1 := by
    rw [show ((2 ^ n : ℕ) : ℤ) + 1 = ((2 ^ n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hη]; exact h9)
  have hζ : Units.map (δ.toRingHom : K →* K) (η ^ 3) = η ^ 3 := by
    rw [map_pow, hδη, ← pow_mul, show (3 * t + 1) * 3 = 9 * t + 3 by ring, pow_add, pow_mul, hη9,
      one_pow, one_mul]
  set l : K := ((η ^ 3 : Kˣ) : K)
  have hδl : δ.toRingHom l = l := by
    have h := congrArg Units.val hζ
    rwa [Units.coe_map] at h
  have hδθl : δ.toRingHom (θ l) = θ l := by rw [hθ', map_pow, hδl]
  have hl : θ l ≠ l := by
    intro h
    have hζ3 : orderOf (η ^ 3) = 3 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hη]; norm_num), hη]
    have h' : (η ^ 3) ^ (2 ^ n) = (η ^ 3) ^ 1 := by
      rw [pow_one]
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, ← hθ']
      exact h
    rw [pow_eq_pow_iff_modEq, hζ3] at h'
    unfold Nat.ModEq at h'
    generalize 2 ^ n = N at h3 h'
    omega
  have hφ : ∀ γ c, scBase δ.toRingHom (e6Data_valid.xm K γ c) =
      e6Data_valid.xm K γ (δ.toRingHom c) := fun γ c => scBase_xm δ.toRingHom γ c
  have hjmem : ∀ w : rankSixCond η, torusConj3 K θ l η w ∈ fixedGroup K θ := fun w =>
    torusConj3_mem_fixedGroup θ hθθ hl hθη hηm (mem_rankSixCond.1 w.2).1
  let j : rankSixCond η →* fixedGroup K θ :=
    ((torusConj3 K θ l η).comp (rankSixCond η).subtype).codRestrict _ hjmem
  have hj : ∀ w, ((j w : fixedGroup K θ) : e6Data_valid.minGroup K) = torusConj3 K θ l η w :=
    fun _ => rfl
  have hjinj : Function.Injective j := fun w w' h =>
    Subtype.ext (torusConj3_injective θ l η (congrArg Subtype.val h))
  have hcube : ∀ w, j w ^ 3 ∈ Subgroup.center (fixedGroup K θ) := fun w =>
    mem_center_of_coe_mem_center θ (torusConj3_pow_three_mem_center θ l w.2)
  let q₃ : rankSixCond η →* TwE6Delta.RecipeR K n := π.comp j
  have hq₃ : ∀ w, q₃ w = π (j w) := fun _ => rfl
  have hq₃cube : ∀ w, q₃ w ^ 3 = 1 := fun w => by
    rw [hq₃, ← map_pow]
    exact (hπ1 _).2 (hcube w)
  have hfixE : ∀ w, f (q₃ w) = q₃ w := fun w => by
    rw [hq₃]
    refine hδfix (j w) ?_
    have hiso := e6Isogeny_eq_one_of_mem_center hθθ hK4 (hcube w)
    have hs : scBase δ.toRingHom ((j w : fixedGroup K θ) : e6Data_valid.minGroup K) =
        (((j w ^ 3) ^ t * j w : fixedGroup K θ) : e6Data_valid.minGroup K) := by
      rw [hj, map_torusConj3 hφ θ hδl hδθl hδη, map_pow, ← hj, ← pow_mul, ← pow_succ,
        Subgroup.coe_pow]
    rw [hs, Subgroup.coe_mul, map_mul, Subgroup.coe_pow, map_pow, hiso, one_pow, one_mul]
  have hx₁mem : e6Data_valid.xm K eOne 1 ∈ fixedGroup K θ :=
    (mem_fixedGroup θ).2 (by rw [sigma_xm_single, rhoPerm_nd_one, map_one])
  set x₁ : fixedGroup K θ := ⟨e6Data_valid.xm K eOne 1, hx₁mem⟩
  have hx₁2 : x₁ ^ 2 = 1 := by
    refine Subtype.ext ?_
    change e6Data_valid.xm K eOne 1 ^ 2 = 1
    rw [pow_two, ← MinData.Valid.xm_add, CharTwo.add_self_eq_zero, MinData.Valid.xm_zero]
  have hx₁ne : x₁ ≠ 1 := fun h => by
    have h' : e6Data_valid.xm K eOne 1 = e6Data_valid.xm K eOne 0 := by
      rw [MinData.Valid.xm_zero]
      exact congrArg Subtype.val h
    exact one_ne_zero (e6Data_valid.xm_injective K (IsRoot.basis (nd 1)) h')
  have hcardZ : Nat.card (Subgroup.center (fixedGroup K θ)) = 3 := by
    rw [(card_center_fixedGroup hK hθ').1]
    exact Nat.gcd_eq_left h3
  have hπx : π x₁ ≠ 1 := fun h => by
    have hz := (hπ1 x₁).1 h
    have hx3 : x₁ ^ 3 = 1 := by
      have h1 := pow_card_eq_one' (G := Subgroup.center (fixedGroup K θ)) (x := ⟨x₁, hz⟩)
      rw [hcardZ] at h1
      exact congrArg Subtype.val h1
    apply hx₁ne
    calc x₁ = x₁ ^ 3 * (x₁ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx3, hx₁2, inv_one, mul_one]
  have hfx₁ : f (π x₁) = π x₁ := hδfix x₁ (by
    change e6Isogeny K (scBase δ.toRingHom (e6Data_valid.xm K eOne 1)) =
      e6Isogeny K (e6Data_valid.xm K eOne 1)
    rw [scBase_xm, map_one])
  have hcomm : ∀ w, Commute (π x₁) (q₃ w) := fun w => by
    rw [hq₃]
    refine Commute.map ?_ π
    show x₁ * j w = j w * x₁
    exact Subtype.ext ((torusConj3_commute_xm θ l η (mem_rankSixCond.1 w.2).1 1).symm.eq)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨q₃.range, Subgroup.zpowers (π x₁), ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := a.2
    obtain ⟨v', hv'⟩ := b.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hv, ← hv', ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨w, rfl⟩
    exact hq₃cube w
  ·
    have : Finite (Subgroup.center (fixedGroup K θ)) :=
      Nat.finite_of_card_ne_zero (by rw [hcardZ]; norm_num)
    have hker : Nat.card q₃.ker ≤ 3 := by
      rw [← hcardZ]
      refine Nat.card_le_card_of_injective (fun v => ⟨j v, (hπ1 _).1 v.2⟩) fun v v' h => ?_
      exact Subtype.ext (hjinj (congrArg Subtype.val h))
    have hV : 729 ≤ Nat.card (rankSixCond η) := by
      have h := card_rankSixCond (k := K) hη
      norm_num at h
      exact h
    have hmul := Subgroup.card_ker_mul_card_range q₃
    rw [show (3 : ℕ) ^ 5 = 243 by norm_num]
    by_contra hlt
    have h1 : Nat.card q₃.ker * Nat.card q₃.range ≤ 3 * 242 :=
      Nat.mul_le_mul hker (by omega)
    omega
  · intro h
    apply hπx
    have hm := Subgroup.mem_zpowers (π x₁)
    rwa [h, Subgroup.mem_bot] at hm
  · refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx₁2, map_one])
  · rintro _ ⟨w, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact ((hcomm w).zpow_left m).eq
  · rintro _ ⟨w, rfl⟩
    exact hfixE w
  · intro u hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [map_zpow, hfx₁]

end CFSG.StandardType.KG82
