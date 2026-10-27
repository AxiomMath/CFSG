module

public import CFSG.ClassicalGroups.Orthogonal.SingularPairPerp
public import CFSG.ClassicalGroups.Orthogonal.Lines
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

namespace HS6

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

section Eichler

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_eq_one_of_smul {u w : V} (hu : Q u = 0) {c : K} (hw : w = c • u) :
    eichler Q u w = 1 := by
  have := eichler_add_smul_self hu 0 c
  rw [zero_add, eichler_zero_right] at this
  rw [hw]
  exact this

theorem eichler_fix_iff {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (hu0 : u ≠ 0)
    (hwu : ∀ c : K, w ≠ c • u) (x : V) :
    eichler Q u w x = x ↔ polar Q x u = 0 ∧ polar Q x w = 0 := by
  constructor
  · intro h
    rw [eichler_apply hu hw] at h
    have h1 : polar Q x u • w = (polar Q x w + Q w * polar Q x u) • u := by
      rw [add_sub_assoc] at h
      exact sub_eq_zero.mp (add_eq_left.mp h)
    have ha : polar Q x u = 0 := by
      by_contra ha
      apply hwu ((polar Q x w + Q w * polar Q x u) / polar Q x u)
      rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [ha, zero_smul, mul_zero, add_zero] at h1
    exact ⟨ha, (smul_eq_zero.mp h1.symm).resolve_right hu0⟩
  · rintro ⟨h1, h2⟩
    exact eichler_apply_of_polar_eq_zero h1 h2

theorem exists_smul_of_fix_eq (hQ : (polarBilin Q).Nondegenerate) {u w w' : V} (hu : Q u = 0)
    (hu0 : u ≠ 0) (hw : polar Q u w = 0) (hw' : polar Q u w' = 0) (hwu : ∀ c : K, w ≠ c • u)
    (hwu' : ∀ c : K, w' ≠ c • u)
    (hfix : ∀ x, eichler Q u w x = x ↔ eichler Q u w' x = x) :
    ∃ c : K, c ≠ 0 ∧ eichler Q u w' = eichler Q u (c • w) := by
  let L : Fin 2 → V →ₗ[K] K := ![polarBilin Q u, polarBilin Q w]
  have hker : ⨅ i, LinearMap.ker (L i) ≤ LinearMap.ker (polarBilin Q w') := by
    intro x hx
    rw [Submodule.mem_iInf] at hx
    have h0 : polar Q u x = 0 := by simpa [L] using hx 0
    have h1 : polar Q w x = 0 := by simpa [L] using hx 1
    have hx0 : polar Q x u = 0 := by rw [polar_comm]; exact h0
    have hx1 : polar Q x w = 0 := by rw [polar_comm]; exact h1
    have h2 := (hfix x).mp ((eichler_fix_iff hu hw hu0 hwu x).mpr ⟨hx0, hx1⟩)
    have h3 := ((eichler_fix_iff hu hw' hu0 hwu' x).mp h2).2
    rw [LinearMap.mem_ker, polarBilin_apply_apply, polar_comm]
    exact h3
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (mem_span_of_iInf_ker_le_ker hker)
  have hw'eq : w' = c 0 • u + c 1 • w := by
    have hz : w' - (c 0 • u + c 1 • w) = 0 := by
      apply eq_zero_of_polar_eq_zero hQ
      intro y
      have := congrArg (fun f => f y) hc
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Fin.sum_univ_two,
        L, Matrix.cons_val_zero, Matrix.cons_val_one, polarBilin_apply_apply, smul_eq_mul] at this
      rw [polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq]
      have h2 : polar Q (c 0 • u + c 1 • w) y = polar Q w' y := by
        rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq]
        exact this
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq] at h2
      rw [← h2]
      ring
    exact sub_eq_zero.mp hz
  have hc1 : c 1 ≠ 0 := by
    intro h
    apply hwu' (c 0)
    rw [hw'eq, h, zero_smul, add_zero]
  refine ⟨c 1, hc1, ?_⟩
  rw [hw'eq, add_comm]
  exact eichler_add_smul_self hu (c 1 • w) (c 0)

end Eichler

section Pairs

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)}

theorem finrank_le_finrank_perp_add_two (u w : ι → K) :
    Module.finrank K (ι → K) ≤ Module.finrank K
      (LinearMap.ker (polarBilin Q' u) ⊓ LinearMap.ker (polarBilin Q' w) :
        Submodule K (ι → K)) + 2 := by
  let f : (ι → K) →ₗ[K] K × K := (polarBilin Q' u).prod (polarBilin Q' w)
  have hker : LinearMap.ker f =
      LinearMap.ker (polarBilin Q' u) ⊓ LinearMap.ker (polarBilin Q' w) :=
    LinearMap.ker_prod _ _
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank K (LinearMap.range f) ≤ 2 := by
    calc _ ≤ Module.finrank K (K × K) := Submodule.finrank_le _
      _ = 2 := by simp [Module.finrank_prod]
  rw [hker] at h1
  omega

theorem exists_pair_in_perp_of_ne (hQ : (polarBilin Q').Nondegenerate)
    (h6 : 6 ≤ Module.finrank K (ι → K)) {u w : ι → K} (hw : polar Q' u w = 0) (hQw : Q' w ≠ 0) :
    ∃ x₁ x₂ : ι → K, Q' x₁ = 0 ∧ Q' x₂ = 0 ∧ polar Q' x₁ x₂ = 1 ∧ polar Q' x₁ u = 0 ∧
      polar Q' x₁ w = 0 ∧ polar Q' x₂ u = 0 ∧ polar Q' x₂ w = 0 := by
  have hww : polar Q' w w = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  let U : Submodule K (ι → K) :=
    LinearMap.ker (polarBilin Q' u) ⊓ LinearMap.ker (polarBilin Q' w)
  have hmem : ∀ x, x ∈ U ↔ polar Q' u x = 0 ∧ polar Q' w x = 0 := by
    intro x
    simp [U]
  obtain ⟨x₁, h1, x₂, h2, hx1, hx2, hx12⟩ := exists_singular_pair_of_le_perp hQ h6 hQw U
    ((hmem w).mpr ⟨hw, hww⟩) (fun x hx => ((hmem x).mp hx).2) (finrank_le_finrank_perp_add_two u w)
  refine ⟨x₁, x₂, hx1, hx2, hx12, ?_, ?_, ?_, ?_⟩
  · rw [polar_comm]
    exact ((hmem x₁).mp h1).1
  · rw [polar_comm]
    exact ((hmem x₁).mp h1).2
  · rw [polar_comm]
    exact ((hmem x₂).mp h2).1
  · rw [polar_comm]
    exact ((hmem x₂).mp h2).2

theorem exists_pair_in_perp_of_threePairs (hQ : (polarBilin Q').Nondegenerate)
    (hthree : ∃ P₁ P₂ P₃ : HypPair Q', P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃) {u w : ι → K}
    (hu : Q' u = 0) (hu0 : u ≠ 0) (hw : polar Q' u w = 0) (hwQ : Q' w = 0)
    (hwu : ∀ c : K, w ≠ c • u) :
    ∃ x₁ x₂ : ι → K, Q' x₁ = 0 ∧ Q' x₂ = 0 ∧ polar Q' x₁ x₂ = 1 ∧ polar Q' x₁ u = 0 ∧
      polar Q' x₁ w = 0 ∧ polar Q' x₂ u = 0 ∧ polar Q' x₂ w = 0 := by
  obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ := hthree
  obtain ⟨g₁, hg₁, hg₁u⟩ := exists_mem_elementaryGroup_apply_eq hQ h12 hu0 P₁.e_ne_zero
    (by rw [hu, P₁.Q_e])
  have hQ₁ : ∀ x, Q' (g₁ x) = Q' x := map_of_mem (elementaryGroup_le_orthogonalGroup Q' hg₁)
  have hp₁ : ∀ x y, polar Q' (g₁ x) (g₁ y) = polar Q' x y :=
    polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q' hg₁)
  have hxQ : Q' (g₁ w) = 0 := by rw [hQ₁, hwQ]
  have hex : polar Q' P₁.e (g₁ w) = 0 := by rw [← hg₁u, hp₁, hw]
  have hxe : ∀ c : K, g₁ w ≠ c • P₁.e := by
    intro c hc
    apply hwu c
    apply g₁.injective
    rw [hc, ← hg₁u, map_smul]
  obtain ⟨g₂, hg₂, hg₂e, hg₂x⟩ :=
    exists_fix_apply_eq_of_polar_eq_zero h12 h13 h23 hQ hxQ hex hxe
  have hQ₂ : ∀ x, Q' (g₂ x) = Q' x := map_of_mem (elementaryGroup_le_orthogonalGroup Q' hg₂)
  have hp₂ : ∀ x y, polar Q' (g₂ x) (g₂ y) = polar Q' x y :=
    polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q' hg₂)
  let y : (ι → K) → (ι → K) := fun z => g₁.symm (g₂.symm z)
  have hy1 : ∀ z, g₁ (y z) = g₂.symm z := fun z => g₁.apply_symm_apply _
  have hy2 : ∀ z, g₂ (g₂.symm z) = z := fun z => g₂.apply_symm_apply z
  have hyQ : ∀ z, Q' (y z) = Q' z := fun z => by
    rw [← hQ₁, hy1, ← hQ₂, hy2]
  have hyu : ∀ z, polar Q' z P₁.e = 0 → polar Q' (y z) u = 0 := fun z hz => by
    rw [← hp₁, hy1, hg₁u, ← hp₂, hy2, hg₂e]
    exact hz
  have hyw : ∀ z, polar Q' z P₂.e = 0 → polar Q' (y z) w = 0 := fun z hz => by
    rw [← hp₁, hy1, ← hp₂, hy2, hg₂x]
    exact hz
  have hyy : ∀ z z', polar Q' (y z) (y z') = polar Q' z z' := fun z z' => by
    rw [← hp₁, hy1, hy1, ← hp₂, hy2, hy2]
  refine ⟨y P₃.e, y P₃.f, by rw [hyQ, P₃.Q_e], by rw [hyQ, P₃.Q_f], by rw [hyy, P₃.polar_ef],
    hyu _ ?_, hyw _ ?_, hyu _ ?_, hyw _ ?_⟩
  · rw [polar_comm]
    exact h13.ee
  · rw [polar_comm]
    exact h23.ee
  · rw [polar_comm]
    exact h13.ef
  · rw [polar_comm]
    exact h23.ef

end Pairs


end HS6

end CFSG.RankThree.GF2n.Stroth80
