module

public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofTwoMain
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofUnitary
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofFrameP
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofIrr

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

namespace Res417Frame

variable {K : Type} [Field K]

theorem bar_mul_self_of_cube {n : ℕ} (h : UnitaryFieldData 2 n K) (hq : ModThree false (2 ^ n))
    {ρ : K} (hρ : ρ ^ 3 = 1) : h.bar ρ * ρ = 1 := by
  rw [h.bar_apply, ← pow_succ]
  exact pow_succ_eq_one_of_modThree hq hρ

theorem eq_one_of_pow_two_pow (h2 : (2 : K) = 0) {ζ : Kˣ} {k : ℕ} (hζ : ζ ^ (2 ^ k) = 1) :
    ζ = 1 := by
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ((ζ : K) - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, hζ, Units.val_one, sub_self]
  exact Units.ext (by
    rw [Units.val_one]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h1))

end Res417Frame

open Res417Frame

theorem item417SL3FrameOdd_holds : Item417SL3FrameOdd := by
  intro H _ _ L _ n K _ hK hq _ e A c hA _ hc3 hAc _ hb T hTL hT2 hAT
  obtain ⟨b, hbA, hbL, hbc⟩ := hb
  have h := hK.unitary
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨-, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  set eb : GL (Fin 3) K := (e ⟨b, hbL⟩ : GL (Fin 3) K) with heb
  have hebZ : eb ∉ zPi false 3 (2 ^ n) K := by
    intro hz
    apply hbc
    rw [← hLC]
    exact ⟨hbL, mem_centralizer_of_scalar hbL (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)⟩
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  have heb3 : orderOf eb = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : eb ^ 3 = 1 := by
      rw [heb, ← Subgroup.coe_pow, ← map_pow]
      have : (⟨b, hbL⟩ : L) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hb3]; rfl)
      rw [this, map_one, Subgroup.coe_one]
    refine orderOf_eq_prime h3 fun h1 => hebZ ?_
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨g, -, hgD⟩ := rank3II_4_10_three hK hq hτ hτ1 (e ⟨b, hbL⟩).2 hebZ heb3
  have hegD : (eb : Matrix (Fin 3) (Fin 3) K) * g = g * diagonal ![τ, τ ^ 2, 1] := by
    have h1 : (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![τ, τ ^ 2, 1] =
        ((g * (g⁻¹ * eb * g) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hgD, Units.val_mul, coe_diagTau_eq_diagonal]
    rw [h1, ← Units.val_mul]
    congr 1
    group
  set φ : L →* GL (Fin 3) K := (slPi false 3 (2 ^ n) K).subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ :=
    (slPi false 3 (2 ^ n) K).subtype_injective.comp e.injective
  set P : Subgroup (GL (Fin 3) K) := (T.subgroupOf L).map φ with hP
  have hP2 : IsPGroup 2 P := (hT2.comap_of_injective L.subtype L.subtype_injective).map φ
  have hPu : ∀ M ∈ P, ((M : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * M = 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact ((mem_slPi_false h).mp (e x).2).2
  have hyu : ((eb : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * eb = 1 :=
    ((mem_slPi_false h).mp (e ⟨b, hbL⟩).2).2
  have hyP : ∀ M ∈ P, eb⁻¹ * M * eb ∈ P := by
    rintro _ ⟨x, hx, rfl⟩
    have hxT : (x : H) ∈ T := Subgroup.mem_subgroupOf.mp hx
    have hbN : b⁻¹ ∈ Subgroup.normalizer (T : Set H) := hAT (A.inv_mem hbA)
    have hconj : b⁻¹ * x * b ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp hbN (x : H)).mp hxT
      rwa [inv_inv] at this
    refine ⟨(⟨b, hbL⟩ : L)⁻¹ * x * ⟨b, hbL⟩, Subgroup.mem_subgroupOf.mpr hconj, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl
  have hd : Function.Injective (![τ, τ ^ 2, 1] : Fin 3 → K) :=
    Res417Two.injective_diagTau_entries hτ hτ1
  have hd3 : ∀ i j : Fin 3,
      (![τ, τ ^ 2, 1] : Fin 3 → K) i ^ 3 = (![τ, τ ^ 2, 1] : Fin 3 → K) j ^ 3 := by
    have hc : ∀ i : Fin 3, (![τ, τ ^ 2, 1] : Fin 3 → K) i ^ 3 = 1 := by
      intro i
      fin_cases i
      · exact hτ
      · change (τ ^ 2) ^ 3 = 1
        rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hτ, one_pow]
      · exact one_pow 3
    intro i j
    rw [hc i, hc j]
  have hPbot := eq_bot_of_unitary_eigen (Res417Two.two_eq_zero_of_piField hK) h.bar_bar
    (fun ρ hρ => bar_mul_self_of_cube h hq hρ) hP2 hPu hyu (linearIndependent_cols_of_GL g)
    hd hd3 (mulVec_col_of_conj hegD) hyP
  rw [eq_bot_iff]
  intro t ht
  have hmem : φ ⟨t, hTL ht⟩ ∈ P := ⟨⟨t, hTL ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  rw [hPbot, Subgroup.mem_bot, ← map_one φ] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hφinj hmem))

theorem coe_e_conj_inv {H : Type} [Group H] {L : Subgroup H} [L.Normal] {K : Type} [Field K]
    {π : Bool} {p f : ℕ} {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {a : H} {y : GL (Fin 3) K}
    (hy : IsPGLAtP e a y) {t : H} (ht : t ∈ L) (ht' : a⁻¹ * t * a ∈ L) :
    ((e ⟨a⁻¹ * t * a, ht'⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      (ProjGenLinGroup.mk y)⁻¹ * (e ⟨t, ht⟩ : projImage (slPi π 3 (p ^ f) K)) *
        ProjGenLinGroup.mk y := by
  have h1 := hy.2 (e ⟨a⁻¹ * t * a, ht'⟩)
  rw [coe_slAct_eqP] at h1
  have h2 : (⟨a * ((e.symm (e ⟨a⁻¹ * t * a, ht'⟩) : L) : H) * a⁻¹,
      ‹L.Normal›.conj_mem _ (e.symm (e ⟨a⁻¹ * t * a, ht'⟩)).2 a⟩ : L) = ⟨t, ht⟩ := by
    apply Subtype.ext
    rw [MulEquiv.symm_apply_apply]
    change a * (a⁻¹ * t * a) * a⁻¹ = t
    group
  rw [h2] at h1
  rw [h1]
  group

theorem item417L3FrameOdd_holds : Item417L3FrameOdd := by
  intro H _ _ L _ n K _ hK hq hq2 e A c hA hA27 hc3 hAc hpgl hfr T hTL hT2 hAT
  obtain ⟨b, hb, hbd⟩ := hfr
  have h := hK.unitary
  have := hK.finite
  have : Group.IsPerfect (projImage (slPi false 3 (2 ^ n) K)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  have h2 : (2 : K) = 0 := Res417Two.two_eq_zero_of_piField hK
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨-, a, ha, ya, hya, κ, hκ0, hyab⟩ :=
    exists_regular_liftP_of_frame hK hq hA hA27 hc3 hAc hpgl hb hbd hτ
  have hyau : ((ya : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * ya = 1 :=
    (mem_glPi_false h).mp hya.1
  set Y : Subgroup (projImage (slPi false 3 (2 ^ n) K)) := (T.subgroupOf L).map e.toMonoidHom
    with hY
  have hTsub : IsPGroup 2 (T.subgroupOf L) := hT2.comap_of_injective L.subtype L.subtype_injective
  have hY2 : IsPGroup 2 Y := hTsub.map _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYfin : Finite Y :=
    Finite.of_equiv _ ((T.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY2
    rw [hk]
    intro h3
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  obtain ⟨Ŷ, hŶ, ê, hê⟩ := Sec16.ProofKSL3Two.exists_lift_model hK hq Y hY3
  have hŶ2 : IsPGroup 2 Ŷ := hY2.of_equiv ê.symm
  have hŶu : ∀ M ∈ Ŷ, ((M : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * M = 1 :=
    fun M hM => ((mem_slPi_false h).mp (hŶ hM)).2
  have hYmem : ∀ t ∈ T, ∀ ht : t ∈ L, e ⟨t, ht⟩ ∈ Y := fun t htT ht =>
    ⟨⟨t, ht⟩, Subgroup.mem_subgroupOf.mpr htT, rfl⟩
  have hŶP : ∀ M ∈ Ŷ, ya⁻¹ * M * ya ∈ Ŷ := by
    intro M hM
    obtain ⟨x, hx, hxe⟩ := (ê ⟨M, hM⟩).2
    have hxT : (x : H) ∈ T := Subgroup.mem_subgroupOf.mp hx
    have haN : a⁻¹ ∈ Subgroup.normalizer (T : Set H) := hAT (A.inv_mem ha)
    have ht'T : a⁻¹ * x * a ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp haN (x : H)).mp hxT
      rwa [inv_inv] at this
    have ht'L : a⁻¹ * x * a ∈ L := hTL ht'T
    have hconj := coe_e_conj_inv hya x.2 ht'L
    obtain ⟨x', hx'⟩ := ê.surjective ⟨e ⟨a⁻¹ * x * a, ht'L⟩, hYmem _ ht'T ht'L⟩
    have hmk : ProjGenLinGroup.mk (x' : GL (Fin 3) K) =
        ProjGenLinGroup.mk (ya⁻¹ * M * ya) := by
      rw [← hê x', hx']
      change ((e ⟨a⁻¹ * x * a, ht'L⟩ : projImage (slPi false 3 (2 ^ n) K)) :
        ProjGenLinGroup (Fin 3) K) = _
      rw [hconj, map_mul, map_mul, map_inv]
      congr 2
      have : (e ⟨(x : H), x.2⟩ : projImage (slPi false 3 (2 ^ n) K)) = ê ⟨M, hM⟩ := by
        rw [← hxe]
        rfl
      rw [this, hê]
    have hz : (x' : GL (Fin 3) K)⁻¹ * (ya⁻¹ * M * ya) ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [← ProjGenLinGroup.mk_eq_one, map_mul, map_inv, hmk, inv_mul_cancel]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨ζ, hζ⟩ := hz
    have hyMy : ya⁻¹ * M * ya = (x' : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ζ := by
      rw [hζ]
      group
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hŶ2
    have hM1 : M ^ Nat.card Ŷ = 1 := by
      have := pow_card_eq_one' (x := (⟨M, hM⟩ : Ŷ))
      exact congrArg Subtype.val this
    have hx'1 : (x' : GL (Fin 3) K) ^ Nat.card Ŷ = 1 := by
      have := pow_card_eq_one' (x := x')
      exact congrArg Subtype.val this
    have hζk : GeneralLinearGroup.scalar (Fin 3) (ζ ^ Nat.card Ŷ) = 1 := by
      have h1 : (ya⁻¹ * M * ya) ^ Nat.card Ŷ = 1 := by
        have := conj_pow (a := ya⁻¹) (b := M) (i := Nat.card Ŷ)
        rw [inv_inv] at this
        rw [this, hM1, mul_one, inv_mul_cancel]
      rw [hyMy, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ
        (x' : GL (Fin 3) K)).mul_pow, hx'1, one_mul, ← map_pow] at h1
      exact h1
    have hζ1 : ζ ^ Nat.card Ŷ = 1 := by
      have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hζk
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Units.val_one, Matrix.one_apply_eq] at this
      exact Units.ext this
    rw [hk] at hζ1
    have hζ' := eq_one_of_pow_two_pow h2 hζ1
    rw [hyMy, hζ', map_one, mul_one]
    exact x'.2
  have hŶbot := eq_bot_of_unitary_eigen h2 h.bar_bar
    (fun ρ hρ => bar_mul_self_of_cube h hq hρ) hŶ2 hŶu hyau hb
    (injective_smul_tau hτ hτ1 hκ0) (pow_three_smul_tau hτ) hyab hŶP
  rw [eq_bot_iff]
  intro t ht
  obtain ⟨x', hx'⟩ := ê.surjective ⟨e ⟨t, hTL ht⟩, hYmem t ht (hTL ht)⟩
  have hx'1 : x' = 1 :=
    Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp hŶbot (x' : GL (Fin 3) K) x'.2)
  rw [hx'1, map_one] at hx'
  have h1 : e ⟨t, hTL ht⟩ = 1 := (congrArg Subtype.val hx').symm
  rw [map_eq_one_iff _ e.injective] at h1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)

end CFSG.RankThree.PartTwo.Sec4
