module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldGamma
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestEndRankMinus
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal

public section

namespace CFSG.StandardType

namespace IOneFieldCF

open CFSG.Assembly CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL Matrix
  OrthBstarOdd Module QuadraticMap LIDTwDF

section Card

variable {G : Type*} [Group G]

theorem eq_of_lt_of_card_le [Finite G] {p : ℕ} (hp : p.Prime) {Eb E' Eh : Subgroup G}
    (hE' : IsPGroup p E') (hlt : Eb < E') (hle : E' ≤ Eh)
    (hcard : Nat.card Eh ≤ p * Nat.card Eb) : E' = Eh := by
  have := Fact.mk hp
  have hEb : IsPGroup p Eb := hE'.to_le hlt.le
  obtain ⟨a, ha⟩ := hEb.exists_card_eq
  obtain ⟨b, hb⟩ := hE'.exists_card_eq
  have hlt' : Nat.card Eb < Nat.card E' := by
    by_contra h
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le (not_lt.mp h))
  rw [ha, hb] at hlt'
  have hab : a + 1 ≤ b := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt'
  have h1 : p * Nat.card Eb ≤ Nat.card E' := by
    rw [ha, hb, ← pow_succ']
    exact Nat.pow_le_pow_right hp.pos hab
  exact Subgroup.eq_of_le_of_card_ge hle (hcard.trans h1)

end Card

theorem isPGroup_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsPGroup p E := fun x =>
  ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩

section Inn

variable {R R' : Type} [Group R] [Group R']

theorem congr_mem_innSet (e : R ≃* R') {φ : MulAut R} (h : φ ∈ LargeEvenInnSet R) :
    MulAut.congr e φ ∈ LargeEvenInnSet R' := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨e x, (OuterAutomorphisms.congr_conj e x).symm⟩

theorem mem_innSet_of_congr (e : R ≃* R') {φ : MulAut R}
    (h : MulAut.congr e φ ∈ LargeEvenInnSet R') : φ ∈ LargeEvenInnSet R := by
  obtain ⟨y, hy⟩ := h
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hy]

end Inn

section Count

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem not_dvd_card_singular_Qm {n p : ℕ} (hn4 : 4 ≤ n) (hne : Even n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) :
    ¬ p ∣ Nat.card {v : Fin (2 * n) → K // v ≠ 0 ∧ Qm n hn4 b c v = 0} := by
  have hmo : Odd (n - 1) := by
    obtain ⟨k, hk⟩ := hne
    exact ⟨k - 1, by omega⟩
  have h1 := OrthRestEnd.not_dvd_card_nonzero_singular_qMinus (K := K) hirr hmo hp hp2 hpq
  have hn : 1 ≤ n := by omega
  intro hdvd
  apply h1
  have hQ : Qm n hn4 b c = reindexQuadraticForm (RecipeFieldOmega.minusIdx n hn)
      (TableBOrth.qMinusForm K (n - 1) b c) :=
    (RecipeFieldOmega.reindex_qMinusForm hn b c).symm
  have hcard : Nat.card {v : LargeEvenMinusIdx (n - 1) → K //
      v ≠ 0 ∧ TableBOrth.qMinusForm K (n - 1) b c v = 0} =
      Nat.card {v : Fin (2 * n) → K // v ≠ 0 ∧ Qm n hn4 b c v = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquiv
      (reindexVectorEquiv (RecipeFieldOmega.minusIdx n hn)).toEquiv fun v => ?_)
    rw [hQ]
    change _ ↔ _ ∧ reindexQuadraticForm (RecipeFieldOmega.minusIdx n hn)
      (TableBOrth.qMinusForm K (n - 1) b c)
        (reindexVectorEquiv (RecipeFieldOmega.minusIdx n hn) v) = 0
    rw [reindexQuadraticForm_map]
    refine and_congr_left fun _ => ?_
    exact (LinearEquiv.map_ne_zero_iff
      (reindexVectorEquiv (RecipeFieldOmega.minusIdx n hn))).symm
  rw [hcard]
  exact hdvd

end Count

section TwoSub

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_twoSubgroup_of_inn_gamma {n p : ℕ} (hn4 : 4 ≤ n) (hne : Even n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1)
    {Eb : Subgroup (MulAut (matrixDerived (Qm n hn4 b c)))}
    (hEbI : (Eb : Set (MulAut (matrixDerived (Qm n hn4 b c)))) ⊆
      LargeEvenInnSet (matrixDerived (Qm n hn4 b c)))
    (hEb : IsElemAbelian p Eb) :
    ∃ U : Subgroup (matrixDerived (Qm n hn4 b c)), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ φ ∈ Eb, ∀ v ∈ U, φ v ∈ U := by
  classical
  have := Fact.mk hp
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hZ : Subgroup.center (matrixDerived (Qm n hn4 b c)) = ⊥ :=
    OrthRestOdd.center_matrixDerived_eq_bot hnd (by omega)
  have hinj := OrthRest.conj_injective hZ
  have : Finite (GL (Fin (2 * n)) K) := Finite.of_injective (fun g : GL (Fin (2 * n)) K =>
    (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) Units.val_injective
  have hIsoΓ : ∀ x : matrixDerived (Qm n hn4 b c), ∀ v,
      Qm n hn4 b c (((x : GL (Fin (2 * n)) K)).val *ᵥ v) = Qm n hn4 b c v := fun x v =>
    (mem_matrixIsometries_iff _ _).1 (matrixDerived_le_isometries _ x.2) v
  set Ab := Eb.comap (MulAut.conj : matrixDerived (Qm n hn4 b c) →* _) with hAb
  have hAbab : IsElemAbelian p Ab := isElemAbelian_comap hEb hinj
  have hAbp : IsPGroup p Ab := isPGroup_of_isElemAbelian hAbab
  set E : Subgroup (GL (Fin (2 * n)) K) := Ab.map (matrixDerived (Qm n hn4 b c)).subtype with hE
  have hEp : IsPGroup p E := hAbp.map _
  have hEiso : ∀ g ∈ E, ∀ v, Qm n hn4 b c ((g : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *ᵥ v) =
      Qm n hn4 b c v := by
    rintro _ ⟨x, -, rfl⟩ v
    exact hIsoΓ x v
  obtain ⟨v, hv0, hvQ, hvfix⟩ := OrthRestEnd.exists_fixed_singular (Qm n hn4 b c) E hEp hEiso
    (not_dvd_card_singular_Qm hn4 hne hirr hp hp2 hpq)
  set Y : Submodule K (Fin (2 * n) → K) := K ∙ v with hY
  have hY0 : Y ≠ ⊥ := by
    rw [hY, Ne, Submodule.span_singleton_eq_bot]
    exact hv0
  have hYsing : ∀ y ∈ Y, Qm n hn4 b c y = 0 := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [QuadraticMap.map_smul, hvQ, smul_zero]
  have hYp := polar_zero_of_sing hYsing
  have hfin : finrank K (Fin (2 * n) → K) = 2 * n := Module.finrank_fin_fun K
  set ι : matrixDerived (Qm n hn4 b c) →* ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) :=
    matrixLinearIso.toMonoidHom.comp (matrixDerived (Qm n hn4 b c)).subtype with hι
  have hιinj : Function.Injective ι := matrixLinearIso.injective.comp Subtype.val_injective
  have hιQ : ∀ x : matrixDerived (Qm n hn4 b c), ∀ w, (Qm n hn4 b c) (ι x w) = (Qm n hn4 b c) w :=
    fun x w => hIsoΓ x w
  set El := Ab.map ι with hEl
  have hElY : ∀ g ∈ El, ∀ y ∈ Y, g y ∈ Y := by
    rintro _ ⟨x, hx, rfl⟩ y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have h1 : ι x v = v := hvfix _ ⟨x, hx, rfl⟩
    rw [map_smul, h1]
    exact Y.smul_mem a (Submodule.mem_span_singleton_self v)
  obtain ⟨x, hxY, w, hwP, hsing, hind⟩ :=
    exists_siegel_pair hnd (by rw [hfin]; omega) hY0 hYsing
  set H := (matrixDerived (Qm n hn4 b c)).map
    (matrixLinearIso (d := 2 * n) (K := K)).toMonoidHom with hH
  have hlinH : ∀ g, ι g ∈ H := fun g => ⟨g.val, g.2, rfl⟩
  have hsiegH : siegEquiv hsing ∈ H := by
    refine ⟨matrixLinearIso.symm (siegEquiv hsing), ?_, by simp⟩
    rw [SetLike.mem_coe, mem_matrixDerived_iff hnd hT3, MulEquiv.apply_symm_apply]
    exact siegEquiv_mem_omegaGroup hnd hsing
  set U₂ := (radSub (Qm n hn4 b c) Y hYp H).comap ι with hU₂
  have hsieg := siegEquiv_mem_radSub (hY := hYp) hsing hxY hwP hsiegH
  obtain ⟨h₀, hh₀Γ, hh₀⟩ := hsiegH
  have hU₂1 : U₂ ≠ ⊥ := by
    intro h0
    have hmem : (⟨h₀, hh₀Γ⟩ : matrixDerived (Qm n hn4 b c)) ∈ U₂ := by
      change ι ⟨h₀, hh₀Γ⟩ ∈ radSub (Qm n hn4 b c) Y hYp H
      rw [show ι ⟨h₀, hh₀Γ⟩ = siegEquiv hsing from hh₀]
      exact hsieg
    rw [h0, Subgroup.mem_bot] at hmem
    apply siegEquiv_ne_one hnd hsing hind
    rw [← hh₀]
    change ι ⟨h₀, hh₀Γ⟩ = 1
    rw [hmem, map_one]
  have hU₂2 : IsPGroup 2 U₂ := fun u => ⟨2, Subtype.ext (hιinj (by
    rw [show 2 ^ 2 = 4 from rfl, Subgroup.coe_pow, map_pow, OneMemClass.coe_one, map_one]
    exact radSub_pow_four (hY := hYp) (H := H) u.2))⟩
  have hEbU : ∀ ψ ∈ Eb, ∀ u ∈ U₂, ψ u ∈ U₂ := by
    intro ψ hψ u hu
    obtain ⟨e, rfl⟩ := hEbI hψ
    have he : e ∈ Ab := hψ
    have heE : ι e ∈ El := ⟨e, he, rfl⟩
    change ι (MulAut.conj e u) ∈ radSub (Qm n hn4 b c) Y hYp H
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    refine conj_mem_radSub (hιQ e) (hElY _ heE) (hElY _ (El.inv_mem heE)) ?_ hu
    rintro _ ⟨h', hh', rfl⟩
    refine ⟨(e : GL (Fin (2 * n)) K) * h' * (e : GL (Fin (2 * n)) K)⁻¹,
      mul_mem (mul_mem e.2 hh') (inv_mem e.2), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    rfl
  exact ⟨U₂, hU₂1, hU₂2, hEbU⟩

end TwoSub

section Bound

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggInnerDiagBound_gamma {f n p : ℕ} (hf : Nat.card K = 2 ^ f) (hn4 : 4 ≤ n)
    (hne : Even n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1) (hpq : p ∣ Nat.card K + 1) :
    GGInnerDiagBound p (n - 1) (matrixDerived (Qm n hn4 b c))
      (LargeEvenInnSet (matrixDerived (Qm n hn4 b c))) := by
  intro Eb Eh hEbI hEb hr h3 hle hEh hcard hnot
  obtain ⟨V, hV1, hV2, hV⟩ := exists_twoSubgroup_of_inn_gamma hn4 hne hirr hp hp2 hpq hEbI hEb
  obtain ⟨φ, hφEh, hφI⟩ : ∃ φ ∈ Eh, φ ∉ LargeEvenInnSet (matrixDerived (Qm n hn4 b c)) := by
    by_contra hcon
    push Not at hcon
    exact hnot fun φ hφ => hcon φ hφ
  obtain ⟨E', hlt, hE'le, W, hW1, hW2, hW⟩ := ggFieldInnR_gamma hf hn4 hirr hp hp2 hK1 Eb Eh
    hEbI hEb hr h3 ⟨V, hV1, hV2, hV⟩ hle hEh ⟨φ, hφEh, hφI⟩
  have hE'Eh : E' = Eh :=
    eq_of_lt_of_card_le hp ((isPGroup_of_isElemAbelian hEh).to_le hE'le) hlt hE'le hcard
  exact ⟨W, hW1, hW2, fun ψ hψ => hW ψ (hE'Eh ▸ hψ)⟩

theorem ggInnerDiagBound_omegaMinus {n m p : ℕ} {b c : K} (hK : Nat.card K = 2 ^ n)
    (hm : 3 ≤ m) (hmo : Odd m) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGInnerDiagBound p m (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0, pow_zero] at h1
      omega
    · exact h0
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
      rw [Nat.dvd_add_right (dvd_pow_self 2 (by omega))]
      norm_num
    exact hodd hpq
  have hn4 : 4 ≤ m + 1 := by omega
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  exact ggInnerDiagBound_of_mulEquiv (RecipeFieldOmega.minusEquiv hn4 b c)
    (fun _ h => congr_mem_innSet _ h) (fun _ h => mem_innSet_of_congr _ h)
    (ggInnerDiagBound_gamma hK hn4 hmo.add_one hbc hp hp2
      (OrthRestOdd.eq_one_of_pow_eq_one_of_dvd hK hp hpq) hpq')

end Bound

theorem recipeOmegaMinus_innerDiagBound
    {m n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ n + 1) (hm : 3 ≤ m) (hmo : Odd m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hlift := ggOrthRestTorusLiftInput_holds.1 K n m p b c hK hm hp hpn hbc
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, m, hlift,
    ggInnerDiagBound_omegaMinus hK hm hmo hp hpn hbc⟩

end IOneFieldCF

end CFSG.StandardType
