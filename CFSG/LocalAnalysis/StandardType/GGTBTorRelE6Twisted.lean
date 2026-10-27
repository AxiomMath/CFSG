module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Cover
public import CFSG.LocalAnalysis.StandardType.GGTorusE6Relative
public import CFSG.LocalAnalysis.StandardType.GGTorusE6RelativeWeyl
public import CFSG.LocalAnalysis.StandardType.GGTorusCentralLift
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusFrameFusion
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGTorusF4Split
public import CFSG.LocalAnalysis.StandardType.GGTBTorRel

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.TwistedE6Cover CFSG.LieType.SeitzGeneration TableBExc


theorem exists_aligned_splitFrame_twE6_relative {K : Type} [Field K] [Finite K]
    {n p r : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) [Fact p.Prime]
    {L : Type} [Group L] [Finite L] (ψ : L →* TwE6Delta.RecipeR K n)
    (A : Subgroup (MulAut L))
    (hA : GGTorusTBGroup p r (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L ψ A) :
    ∃ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ n)) ∧ (∀ c, σ (σ c) = c) ∧
      ∃ ζ0 : (fixField σ.toRingHom)ˣ, ζ0 ^ p = 1 ∧ ζ0 ≠ 1 ∧
      ∃ (hζp : fixUnit σ.toRingHom ζ0 ^ p = 1)
        (hζσ : σ (fixUnit σ.toRingHom ζ0 : K) = fixUnit σ.toRingHom ζ0)
        (ψ0 : L →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
        (Λ0 : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* MulAut L),
        Function.Surjective ψ0 ∧ ψ0.ker = ψ.ker ∧ Function.Injective Λ0 ∧
        (∀ x : L, Λ0 (ψ0 x) = MulAut.conj x) ∧
        Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ ∧
        orderOf (fixUnit σ.toRingHom ζ0) = p ∧
        (ExcFrames.twE6SplitFrameHom σ.toRingHom (fixUnit σ.toRingHom ζ0) hζp hζσ).range.map Λ0 = A := by
  classical
  obtain ⟨hψ, hker, hperf, hAab, hAI, -, -, hAsc⟩ := hA
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  let : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hple : p ≤ 2 ^ n - 1 := Nat.le_of_dvd (by omega) hpn
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by omega
    rw [hn1] at hple
    norm_num at hple
    omega
  obtain ⟨Λ, hΛ, hΛi, -, -, hEab, hEcard, hEA, hEsc⟩ :=
    exists_innerModel_recipe_twE6 hp hn hK
      (TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3)
      (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3)
      ψ hψ hker hperf hAab hAI hAsc
  let E : Subgroup (TwE6Delta.RecipeR K n) := A.comap Λ
  obtain ⟨σ, hσ, hσord, -, -, -, -, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hn K hK
  have hσord2 : orderOf σ = 2 := hσord
  have hσ2 : σ ^ 2 = 1 := by
    rw [← hσord2]
    exact pow_orderOf_eq_one σ
  have hσσ : ∀ c, σ (σ c) = c := by
    intro c
    have h := congrArg (fun f : K ≃+* K => f c) hσ2
    exact h
  have hfixcard : Nat.card (fixField σ.toRingHom) = 2 ^ n :=
    E6RelativeTorus.natCard_fixField σ.toRingHom hn hK hσ
  have hpU : p ∣ Nat.card (fixField σ.toRingHom)ˣ := by
    rw [Nat.card_units, hfixcard]
    exact hpn
  obtain ⟨ζ0, hζ0o⟩ := exists_prime_orderOf_dvd_card' p hpU
  have hζ0p : ζ0 ^ p = 1 := hζ0o ▸ pow_orderOf_eq_one ζ0
  have hζ01 : ζ0 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ0o
    exact hp.ne_one hζ0o.symm
  let ζ : Kˣ := fixUnit σ.toRingHom ζ0
  have hfixinj : Function.Injective (fixUnit σ.toRingHom) := by
    intro a b h
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun z : Kˣ => (z : K)) h
  have hζp : ζ ^ p = 1 := by
    change fixUnit σ.toRingHom ζ0 ^ p = 1
    rw [← map_pow, hζ0p, map_one]
  have hζ1 : ζ ≠ 1 := by
    intro h
    exact hζ01 (hfixinj (h.trans (map_one (fixUnit σ.toRingHom)).symm))
  have hζo : orderOf ζ = p := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hζp) with h | h
    · exact False.elim (hζ1 (orderOf_eq_one_iff.mp h))
    · exact h
  have hζσ : σ (ζ : K) = ζ := by
    change σ (((ζ0 : fixField σ.toRingHom) : K)) = ((ζ0 : fixField σ.toRingHom) : K)
    exact mem_fixField.mp (ζ0 : fixField σ.toRingHom).property
  let C0 := ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK σ.toRingHom hσ
  let E0 : Subgroup C0 := (ExcFrames.twE6SplitFrameHom σ.toRingHom ζ hζp hζσ).range
  have hE0ab : IsElemAbelian p E0 :=
    ExcFrames.isElemAbelian_range_frame (ExcFrames.twE6SplitFrameHom σ.toRingHom ζ hζp hζσ)
  have hE0card : Nat.card E0 = p ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
        (ExcFrames.twE6SplitFrameHom_injective σ.toRingHom hp5 hζo hζp hζσ)).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hmod : ((2 ^ n : ℕ) : ZMod p) = 1 := by
    have hsub : ((2 ^ n - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (2 ^ n - 1) p).mpr hpn
    rw [Nat.cast_sub (by omega), Nat.cast_one] at hsub
    exact sub_eq_zero.mp hsub
  have hpq : ¬ p ∣ 2 ^ n := by
    intro h
    have h2 := hp.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hSylow : SylowTorus (TwE6Delta.RecipeR K n) p 4 :=
    (ExcFrames.sylowTorus_twistedE6_one Nat.prime_two hn K hK σ hσ hp hp5 hpq
      (by rw [hmod, orderOf_one])).of_mulEquiv e.symm
  obtain ⟨c, hc⟩ := exists_conj_eq_of_selfCentralizing_of_sylowTorus hp
    hSylow
    (hE0ab.map e.symm.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.symm.injective]; exact hE0card)
    hEab hEsc
  let j : C0 ≃* TwE6Delta.RecipeR K n := e.symm.trans (MulAut.conj c)
  have hEj : E0.map j.toMonoidHom = E := by
    change E0.map ((MulAut.conj c).toMonoidHom.comp e.symm.toMonoidHom) = E
    simpa only [Subgroup.map_map] using hc.symm
  let ψ0 : L →* C0 := j.symm.toMonoidHom.comp ψ
  let Λ0 : C0 →* MulAut L := Λ.comp j.toMonoidHom
  have hψ0 : Function.Surjective ψ0 := j.symm.surjective.comp hψ
  have hk0 : ψ0.ker = ψ.ker := MonoidHom.ker_mulEquiv_comp ψ j.symm
  have hΛ0 : Function.Injective Λ0 := hΛi.comp j.injective
  have hΛψ0 : ∀ x : L, Λ0 (ψ0 x) = MulAut.conj x := by
    intro x
    change Λ (j (j.symm (ψ x))) = MulAut.conj x
    rw [j.apply_symm_apply]
    exact hΛ rfl
  have hZ : Subgroup.center C0 = ⊥ := by
    rw [← Subgroup.map_center_eq e, TwE6Delta.center_recipeR_eq_bot hn hK, Subgroup.map_bot]
  have hAout : E0.map Λ0 = A := by
    change E0.map (Λ.comp j.toMonoidHom) = A
    rw [← Subgroup.map_map, hEj]
    exact hEA
  exact ⟨σ, hσ, hσσ, ζ0, hζ0p, hζ01, hζp, hζσ, ψ0, Λ0,
    hψ0, hk0, hΛ0, hΛψ0, hZ, hζo, hAout⟩


theorem ggTorusTorW_recipe_twE6_relative {K : Type} [Field K] [Finite K]
    {n p r : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) :
    GGTorusTorW p r (2 ^ n - 1) 4 CartanMatrix.F₄ CoxeterMatrix.F₄
      (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  classical
  intro L _ _ ψ A hA
  have hTB := hA
  obtain ⟨hψ, hker, hperf, -, -, -, -, -⟩ := hA
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ, hσσ, ζ0, hζ0p, hζ01, hζp, hζσ, ψ0, Λ0,
    hψ0, hk0, hΛ0, hΛψ0, hZ, hζo, hAout⟩ :=
    exists_aligned_splitFrame_twE6_relative hn hK hp hp5 hpn ψ A hTB
  let ζ : Kˣ := fixUnit σ.toRingHom ζ0
  let C0 := ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
  let E0 : Subgroup C0 := (ExcFrames.twE6SplitFrameHom σ.toRingHom ζ hζp hζσ).range
  have hfixcard : Nat.card (fixField σ.toRingHom) = 2 ^ n :=
    E6RelativeTorus.natCard_fixField σ.toRingHom hn hK hσ
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hple : p ≤ 2 ^ n - 1 := Nat.le_of_dvd (by omega) hpn
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by omega
    rw [hn1] at hple
    norm_num at hple
    omega
  obtain ⟨l⟩ := F4SplitTorus.exists_unitValue_equiv (K := fixField σ.toRingHom)
  rw [hfixcard] at l
  let φ := E6RelativeTorus.coordHom σ.toRingHom hσσ
  let S := E6RelativeTorus.fullTorus σ.toRingHom
  let nn : Fin 4 → C0 := fun k => E6RelativeWeyl.nNative (σ := σ.toRingHom) (f4FoldedIndex k)
  obtain ⟨hnN, eW, heW⟩ := E6RelativeWeyl.exists_markedWeyl_standard_conventional
    (σ := σ.toRingHom) (hp := hp) (hp5 := hp5) (hζo := hζo) (hζ := hζp) (hζσ := hζσ)
  have hFormula : ∀ k (a : Fin 4 → (fixField σ.toRingHom)ˣ),
      nn k * φ a * (nn k)⁻¹ =
        φ a * (φ (corTuple CartanMatrix.F₄.transpose k (a k)))⁻¹ := by
    intro k a
    apply Subtype.ext
    change
      (orbitN TwistTag.E6 K σ.toRingHom (f4FoldedIndex k) 1 : ModGL TwistTag.E6.tag K) *
          (φ a : ModGL TwistTag.E6.tag K) *
          (orbitN TwistTag.E6 K σ.toRingHom (f4FoldedIndex k) 1 : ModGL TwistTag.E6.tag K)⁻¹ =
        (φ a : ModGL TwistTag.E6.tag K) *
          (φ (corTuple CartanMatrix.F₄.transpose k (a k)) : ModGL TwistTag.E6.tag K)⁻¹
    exact E6RelativeTorus.orbitN_conj_coordHom σ.toRingHom hσσ k a
  obtain ⟨B, hCB, hBC⟩ := exists_int_matrix_inverse_mod_of_isUnit_det
    (m := 2 ^ n - 1) CartanMatrix.F₄ (by
      have hdet : CartanMatrix.F₄.det = 1 := by decide +kernel
      rw [hdet]
      simpa using (isUnit_one : IsUnit (1 : ZMod (2 ^ n - 1))))
  rw [← hAout]
  exact ggTorusTorData_of_centralLift_rootCoordinates ψ0 hψ0 (by rw [hk0]; exact hker)
    (by omega) (by rw [hk0]; exact coprime_card_ker_recipe_twE6_relative hn2 hK ψ hψ hker hperf)
    l φ (E6RelativeTorus.coordHom_injective σ.toRingHom hσσ) CartanMatrix.F₄ B hCB hBC
    Λ0 hΛ0 hΛψ0 E0
    (E6RelativeTorus.mem_standardFrame_iff_pow_mem_range σ.toRingHom hσσ (by omega) hσ hpn
      hp5 hζo hζp hζσ)
    ζ0 hζ0p hζ01 nn hnN hFormula S hZ
    (E6RelativeTorus.centralizer_standardFrame_le_fullTorus σ.toRingHom hp5 hζo hζp hζσ)
    (fun a t ht => E6RelativeTorus.commute_coordHom_of_mem_fullTorus σ.toRingHom hσσ a ht)
    (fun t ht hp => E6RelativeTorus.mem_range_coordHom_of_mem_fullTorus σ.toRingHom hσσ
      (by omega) hσ ht hp) CoxeterMatrix.F₄ eW heW

theorem ggTorusTorW_label_twE6_relative {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twE6)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusTorW p 4 (ggTorMpm p lab) 4 CartanMatrix.F₄ CoxeterMatrix.F₄ R I := by
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
    have hpge := hp.two_le
    omega
  have hm : ggTorMpm p lab = 2 ^ lab.n - 1 := by simp [ggTorMpm, hpn]
  rw [hm]
  exact TwE6Delta.labelAll htag fun K _ _ hK =>
    ggTorusTorW_recipe_twE6_relative hlab.1 hK hp hp5 hpn
theorem ggTBTorRelE6_of_split (h : GGTBTorRelE6Split) : GGTBTorRelE6 := by
  intro p hp hp2 hp3 lab hlab hrow
  rcases hrow with ⟨htag, hpm⟩ | ⟨htag, hpm⟩
  · exact h p hp hp2 hp3 lab hlab htag hpm
  · exact ggTorusTorW_label_twE6_relative hp hp2 hp3 hlab htag hpm

end CFSG.StandardType
