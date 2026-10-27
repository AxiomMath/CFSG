module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfield
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBYAlgebra
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBYCommute

public section

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

namespace CFSG.RankThree.PartOne.KCOrthogonalSubfield

section Hyp

variable {k : Type} [Field k] {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}

theorem exists_hyp_triple (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0) :
    ∃ P : Fin 3 → HypPair Q₀, ∀ i j, i ≠ j → (P i).Orth (P j) := by
  obtain ⟨U, hU3, hUQ⟩ := hT₀
  obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ := exists_three_hypPairs hnd₀ (T := U) hU3.ge hUQ
  refine ⟨![P₁, P₂, P₃], fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp [h12, h13, h23, h12.symm,
    h13.symm, h23.symm]

end Hyp


section Forward

open CFSG.RankThree.Classical2 CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem semilinear_scalar_on_k (hext : IsExtension k Q₀ Q) (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (g : similarityPairs Q)
    (hfix : ∀ t ∈ subfieldDerivedImage k hext, matrixProjectiveConjugationHom Q g t = t) :
    (∀ c ∈ k, g.val.right c = c) ∧ ∃ a : K, a ≠ 0 ∧
      ∀ x : Fin d → k, coordinateSemilinearMap g.val (vecIncl k x) = a • vecIncl k x := by
  classical
  obtain ⟨P, hPorth⟩ := exists_hyp_triple hnd₀ hT₀
  let τ := g.val.right
  let F : (Fin d → K) →+ (Fin d → K) := (coordinateSemilinearMap g.val).toAddMonoidHom
  have hFsmul : ∀ (c : K) v, F (c • v) = τ c • F v := fun c v =>
    coordinateSemilinearMap_smul g.val c v
  have hFinj : Function.Injective F := (coordinateSemilinearMap g.val).injective
  have hcomm : ∀ {u w : Fin d → k}, Q₀ u = 0 → polar Q₀ u w = 0 → ∀ v,
      F (eichler Q (vecIncl k u) (vecIncl k w) v) =
        eichler Q (vecIncl k u) (vecIncl k w) (F v) := fun hu huw v =>
    commute_eichler hext hnd₀ hT₀ g hfix hu huw v
  set e : Fin 3 → (Fin d → K) := fun i => vecIncl k (P i).e with he
  set f : Fin 3 → (Fin d → K) := fun i => vecIncl k (P i).f with hf
  have hBsymm : ∀ x y, polarBilin Q x y = polarBilin Q y x := fun x y => by
    simp only [polarBilin_apply_apply]
    exact polar_comm Q x y
  have hef : ∀ i j, polarBilin Q (e i) (f j) = if i = j then 1 else 0 := by
    intro i j
    rw [polarBilin_apply_apply, he, hf]
    simp only
    rw [polar_vecIncl k hext]
    by_cases hij : i = j
    · subst hij
      simp [(P i).polar_ef]
    · simp [hij, (hPorth i j hij).ef]
  have hee : ∀ i j, polarBilin Q (e i) (e j) = 0 := by
    intro i j
    rw [polarBilin_apply_apply, he]
    simp only
    rw [polar_vecIncl k hext]
    by_cases hij : i = j
    · subst hij
      rw [(P i).polar_ee]
      rfl
    · rw [(hPorth i j hij).ee]
      rfl
  have hff : ∀ i j, polarBilin Q (f i) (f j) = 0 := by
    intro i j
    rw [polarBilin_apply_apply, hf]
    simp only
    rw [polar_vecIncl k hext]
    by_cases hij : i = j
    · subst hij
      rw [(P i).polar_ff]
      rfl
    · rw [(hPorth i j hij).ff]
      rfl
  have hfe : ∀ i j, polarBilin Q (f i) (e j) = if j = i then 1 else 0 := fun i j => by
    rw [hBsymm]
    exact hef j i
  have hQe : ∀ i, Q (e i) = 0 := fun i => by
    rw [he]
    simp only
    rw [hext, (P i).Q_e]
    rfl
  have hQf : ∀ i, Q (f i) = 0 := fun i => by
    rw [hf]
    simp only
    rw [hext, (P i).Q_f]
    rfl
  have he0 : e 0 ≠ 0 := fun h => by
    have := hef 0 0
    rw [h] at this
    simp at this
  have hcore : ∀ i j, i ≠ j → ∀ x, F (polarBilin Q x (f j) • e i - polarBilin Q x (e i) • f j) =
      polarBilin Q (F x) (f j) • e i - polarBilin Q (F x) (e i) • f j := by
    intro i j hij x
    have hu : Q₀ (P i).e = 0 := (P i).Q_e
    have huw : polar Q₀ (P i).e (-(P j).f) = 0 := by
      rw [polar_neg_right, (hPorth i j hij).ef, neg_zero]
    have hc : F (eichler Q (e i) (vecIncl k (-(P j).f)) x) =
        eichler Q (e i) (vecIncl k (-(P j).f)) (F x) := hcomm hu huw x
    have hneg : vecIncl k (-(P j).f) = - f j := funext fun l => by simp [vecIncl, hf]
    have hpol : polar Q (e i) (-f j) = 0 := by
      rw [polar_neg_right, ← polarBilin_apply_apply, hef i j]
      simp [hij]
    have hE : ∀ y, eichler Q (e i) (vecIncl k (-(P j).f)) y =
        y + (polarBilin Q y (f j) • e i - polarBilin Q y (e i) • f j) := by
      intro y
      rw [hneg, eichler_apply (hQe i) hpol, QuadraticMap.map_neg, hQf j, zero_mul, add_zero,
        polar_neg_right, polarBilin_apply_apply, polarBilin_apply_apply]
      module
    rw [hE, hE, map_add] at hc
    exact add_left_cancel hc
  obtain ⟨a, b, hae, hbf⟩ := core_alg (polarBilin Q) hBsymm F e f hef hee hff hcore
  have ha0 : a ≠ 0 := fun ha => he0 (hFinj (by rw [hae 0, ha, zero_smul, map_zero]))
  have he1 : e 1 ≠ 0 := fun h => by
    have := hef 1 1
    rw [h] at this
    simp at this
  have hcomb : ∀ c : k, τ (c : K) * a = b * c := by
    intro c
    have hu : Q₀ (P 0).e = 0 := (P 0).Q_e
    have h01 : polar Q₀ (P 0).e (c • (P 1).e) = 0 := by
      rw [polar_smul_right_eq, (hPorth 0 1 (by decide)).ee, mul_zero]
    have hc : F (eichler Q (e 0) (vecIncl k (c • (P 1).e)) (f 0)) =
        eichler Q (e 0) (vecIncl k (c • (P 1).e)) (F (f 0)) := hcomm hu h01 (f 0)
    have hw : vecIncl k (c • (P 1).e) = (c : K) • e 1 := vecIncl_smul c (P 1).e
    have hpol : polar Q (e 0) ((c : K) • e 1) = 0 := by
      rw [polar_smul_right_eq, ← polarBilin_apply_apply, hee, mul_zero]
    have hQw : Q ((c : K) • e 1) = 0 := by rw [map_smul_eq_sq, hQe, mul_zero]
    have hE : eichler Q (e 0) ((c : K) • e 1) (f 0) = f 0 + (c : K) • e 1 := by
      rw [eichler_apply (hQe 0) hpol, hQw, zero_mul, add_zero, polar_smul_right_eq,
        ← polarBilin_apply_apply, ← polarBilin_apply_apply, hfe, hfe]
      simp
    rw [hw, hE, map_add, hbf 0, hFsmul, hae 1, LinearEquiv.map_smul, hE] at hc
    have h2 : (τ (c : K) * a) • e 1 = (b * c) • e 1 := by
      linear_combination (norm := module) hc
    exact smul_left_injective K he1 h2
  have hab : a = b := by
    have := hcomb 1
    simpa using this
  have hτk : ∀ c : k, τ (c : K) = c := fun c => by
    have := hcomb c
    rw [← hab] at this
    exact mul_right_cancel₀ ha0 (by rw [this, mul_comm])
  subst hab
  have kee : ∀ i j, polar Q₀ (P i).e (P j).e = 0 := fun i j => by
    by_cases h : i = j
    · subst h
      exact (P i).polar_ee
    · exact (hPorth i j h).ee
  have kfe : ∀ i j, polar Q₀ (P i).f (P j).e = if j = i then 1 else 0 := fun i j => by
    by_cases h : i = j
    · subst h
      simp [(P i).polar_fe]
    · simp [Ne.symm h, (hPorth i j h).fe]
  have kfe' : ∀ i j, polar Q₀ (P i).e (P j).f = if i = j then 1 else 0 := fun i j => by
    by_cases h : i = j
    · subst h
      simp [(P i).polar_ef]
    · simp [h, (hPorth i j h).ef]
  have kff : ∀ i j, polar Q₀ (P i).f (P j).f = 0 := fun i j => by
    by_cases h : i = j
    · subst h
      exact (P i).polar_ff
    · exact (hPorth i j h).ff
  have hw_step : ∀ w : Fin d → k, (∀ j, polar Q₀ w (P j).e = 0) → (∀ j, polar Q₀ w (P j).f = 0) →
      F (vecIncl k w) = a • vecIncl k w := by
    intro w hwe hwf
    have hu : Q₀ (P 0).e = 0 := (P 0).Q_e
    have huw : polar Q₀ (P 0).e w = 0 := by rw [polar_comm, hwe 0]
    have hc : F (eichler Q (e 0) (vecIncl k w) (f 0)) =
        eichler Q (e 0) (vecIncl k w) (F (f 0)) := hcomm hu huw (f 0)
    have hpol : polar Q (e 0) (vecIncl k w) = 0 := by
      rw [show e 0 = vecIncl k (P 0).e from rfl, polar_vecIncl k hext, huw]
      rfl
    have hpf : polar Q (f 0) (vecIncl k w) = 0 := by
      rw [show f 0 = vecIncl k (P 0).f from rfl, polar_vecIncl k hext, polar_comm, hwf 0]
      rfl
    have hQw : Q (vecIncl k w) = ((Q₀ w : k) : K) := hext w
    have hfe0 : polar Q (f 0) (e 0) = 1 := by
      rw [← polarBilin_apply_apply, hfe]
      simp
    have hE : eichler Q (e 0) (vecIncl k w) (f 0) =
        f 0 + vecIncl k w - ((Q₀ w : k) : K) • e 0 := by
      rw [eichler_apply (hQe 0) hpol, hpf, hQw, hfe0]
      module
    have hR : eichler Q (e 0) (vecIncl k w) (a • f 0) =
        a • (f 0 + vecIncl k w - ((Q₀ w : k) : K) • e 0) := by
      rw [LinearEquiv.map_smul, hE]
    have hL : F (f 0 + vecIncl k w - ((Q₀ w : k) : K) • e 0) =
        a • f 0 + F (vecIncl k w) - (((Q₀ w : k) : K) * a) • e 0 := by
      rw [map_sub, map_add, hbf 0, hFsmul, hae 0, hτk]
      module
    rw [hE, hL, hbf 0, hR] at hc
    linear_combination (norm := module) hc
  have hdecomp : ∀ x : Fin d → k, ∃ w : Fin d → k, (∀ j, polar Q₀ w (P j).e = 0) ∧
      (∀ j, polar Q₀ w (P j).f = 0) ∧ x = w + ∑ i : Fin 3,
        (polar Q₀ x (P i).f • (P i).e + polar Q₀ x (P i).e • (P i).f) := by
    intro x
    refine ⟨x - ∑ i : Fin 3, (polar Q₀ x (P i).f • (P i).e + polar Q₀ x (P i).e • (P i).f),
      fun j => ?_, fun j => ?_, by abel⟩
    · have h : polarBilin Q₀ (x - ∑ i : Fin 3,
          (polar Q₀ x (P i).f • (P i).e + polar Q₀ x (P i).e • (P i).f)) (P j).e = 0 := by
        simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, map_add, map_smul,
          LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, polarBilin_apply_apply, kee,
          kfe]
        simp [Finset.sum_ite_eq]
      rwa [polarBilin_apply_apply] at h
    · have h : polarBilin Q₀ (x - ∑ i : Fin 3,
          (polar Q₀ x (P i).f • (P i).e + polar Q₀ x (P i).e • (P i).f)) (P j).f = 0 := by
        simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, map_add, map_smul,
          LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, polarBilin_apply_apply, kff,
          kfe']
        simp
      rwa [polarBilin_apply_apply] at h
  have hF1 : ∀ (c : k) (i : Fin 3), F ((c : K) • e i) = ((c : K) * a) • e i := fun c i => by
    rw [hFsmul, hτk, hae i, smul_smul]
  have hF2 : ∀ (c : k) (i : Fin 3), F ((c : K) • f i) = ((c : K) * a) • f i := fun c i => by
    rw [hFsmul, hτk, hbf i, smul_smul]
  have hall : ∀ x : Fin d → k, F (vecIncl k x) = a • vecIncl k x := by
    intro x
    obtain ⟨w, hwe, hwf, hx⟩ := hdecomp x
    set α : Fin 3 → k := fun i => polar Q₀ x (P i).f with hα
    set β : Fin 3 → k := fun i => polar Q₀ x (P i).e with hβ
    have hxK : vecIncl k x = vecIncl k w + (((α 0 : K) • e 0 + (β 0 : K) • f 0) +
        ((α 1 : K) • e 1 + (β 1 : K) • f 1) + ((α 2 : K) • e 2 + (β 2 : K) • f 2)) := by
      conv_lhs => rw [hx]
      rw [Fin.sum_univ_three]
      simp only [vecIncl_add, vecIncl_smul, he, hf]
      rfl
    rw [hxK]
    simp only [map_add, hF1, hF2, hw_step w hwe hwf]
    module
  exact ⟨fun c hc => hτk ⟨c, hc⟩, a, ha0, hall⟩

end Forward

section Main

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ}

theorem glFieldAut_glIncl_of_fixes {τ : K ≃+* K} (hτ : ∀ c ∈ k, τ c = c) (x : GL (Fin d) k) :
    glFieldAut (Fin d) K τ (glIncl k x) = glIncl k x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change τ ((glIncl k x).val i j) = (glIncl k x).val i j
  exact hτ _ (x.val i j).2

end Main

end CFSG.RankThree.PartOne.KCOrthogonalSubfield

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.Assembly.LowTwoRank

theorem orthogonal_high_Witt_subfield_pointwise_centralizer :
    HighWittSubfieldSemilinearPointwiseCentralizer := by
  intro K _ _ k d Q₀ Q hext hnd₀ hT₀ g
  constructor
  · intro hfix
    obtain ⟨hτ, a, ha0, hall⟩ := semilinear_scalar_on_k hext hnd₀ hT₀ g hfix
    refine ⟨hτ, Units.mk0 a ha0, Units.ext (Matrix.ext fun j i => ?_)⟩
    rw [scalar_entry]
    have h1 := hall (Pi.single i 1)
    have h2 : coordinateFieldMap d g.val.right (Pi.single i 1 : Fin d → K) = Pi.single i 1 := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp [coordinateFieldMap_apply]
      · simp [coordinateFieldMap_apply, hl]
    rw [vecIncl_single, coordinateSemilinearMap_apply] at h1
    have h3 := congrFun h1 j
    by_cases hji : j = i
    · subst hji
      simp [Matrix.mulVec, dotProduct, Pi.single_apply] at h3
      simp [h3]
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply, hji] at h3
      simp [hji, h3]
  · rintro ⟨hτ, b, hb⟩ t ht
    obtain ⟨z, rfl⟩ := ht
    obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective Q₀ z
    rw [incl_mk]
    change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q (inclHom k hext y)) =
      matrixProjectiveProjection Q (inclHom k hext y)
    rw [matrixProjectiveConjugation_mk]
    congr 1
    apply Subtype.ext
    change matrixConjugation g.val (glIncl k y.val) = glIncl k y.val
    rw [matrixConjugation_apply, hb, glFieldAut_glIncl_of_fixes hτ, mul_inv_eq_iff_eq_mul]
    have hcz : (GeneralLinearGroup.scalar (Fin d) b : GL (Fin d) K) ∈
        Subgroup.center (GL (Fin d) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨b, rfl⟩
    exact (Subgroup.mem_center_iff.mp hcz _).symm

theorem orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
    (c : StatedLieTag) (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus)
    (n ℓ e p : ℕ) : ModelOrthogonalSubfield c n ℓ e p :=
  orthogonal_prime_subfield_fixed_group_and_full_centralizer
    orthogonal_high_Witt_subfield_pointwise_centralizer c hc n ℓ e p

theorem orthogonal_prime_subfield_core_clause_unconditional : OrthogonalSubfieldCoreClause :=
  orthogonal_prime_subfield_core_clause orthogonal_high_Witt_subfield_pointwise_centralizer

end CFSG.RankThree.PartOne
