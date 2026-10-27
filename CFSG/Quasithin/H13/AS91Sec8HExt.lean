module

public import CFSG.Quasithin.H13.AS91Sec8HPi
public import CFSG.GroupTheory.ExtendMulEquivIndexTwo
public import CFSG.Quasithin.Background.TwoM22TwoQuotient

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup

namespace Loc41

variable {G : Type} [Group G] [Finite G] {z : G}

theorem CX_normal_NX' (c : Loc41 G z) :
    ∀ n ∈ c.NX, ∀ x ∈ c.CX, n * x * n⁻¹ ∈ c.CX := by
  intro n hn x hx
  exact (Subgroup.normal_subgroupOf_iff c.CX_le_NX).mp c.CX_normal_NX x n hx hn

end Loc41

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_mulEquiv_NX
    {G' : Type} [Group G'] [Finite G'] {z' : G'}
    (c : Loc49 G z) (c' : Loc49 G' z')
    (hkey' : ∀ n ∈ c'.NX, n ∉ c'.CX → (∀ x ∈ c'.CX, n * n * x = x * (n * n)) → n * n = 1)
    (θ : ↥c.CX ≃* ↥c'.CX) :
    ∃ θN : ↥c.NX ≃* ↥c'.NX, ∀ h : ↥c.CX,
      ((θN ⟨h, c.CX_le_NX h.2⟩ : ↥c'.NX) : G') = θ h := by
  obtain ⟨t, htN, htC, htt, -, hsup⟩ := c.exists_t
  obtain ⟨t', htN', htC', htt', -, hsup'⟩ := c'.exists_t
  have houtM22 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥CFSG.Blueprint.NativeSporadic.M22) ≤ 2 :=
    CFSG.GH74.GLS.IVK.GHInv.card_outer_le_of_card_mulAut_le
      CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card
  let e : ↥c'.CX ⧸ Subgroup.center ↥c'.CX ≃* ↥CFSG.Blueprint.NativeSporadic.M22 :=
    (QuotientGroup.quotientMulEquivOfEq c'.qC_ker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective c'.qC c'.qC_surjective)
  have hOut' : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥c'.CX ⧸ Subgroup.center ↥c'.CX)) ≤ 2 := by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact houtM22
  exact CFSG.GroupTheory.exists_mulEquiv_extend_of_mul_self_eq_one
    c.CX_le_NX c'.CX_le_NX c.CX_normal_NX' c'.CX_normal_NX'
    htC htC' htt htt' hsup hsup'
    (fun g hg hcomm => c.self_centralizing_NX hg hcomm)
    (fun g hg hcomm => c'.self_centralizing_NX hg hcomm)
    c'.isPerfect_CX hOut' hkey' θ

theorem relIndex_CX_NX (c : Loc49 G z) : c.CX.relIndex c.NX = 2 := by
  obtain ⟨t, htN, htC, htt, -, hsup⟩ := c.exists_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hconj : ∀ y ∈ c.CX, t * y * t⁻¹ ∈ c.CX := fun y hy => c.CX_normal_NX' t htN y hy
  have key : ∀ x ∈ Subgroup.closure ((c.CX : Set G) ∪ (Subgroup.zpowers t : Set G)),
      x ∈ c.CX ∨ x * t ∈ c.CX := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact Or.inl hy
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
        · left
          rw [zpow_mul, zpow_two, htt, one_zpow]
          exact c.CX.one_mem
        · right
          rw [zpow_add, zpow_mul, zpow_two, htt, one_zpow, one_mul, zpow_one, htt]
          exact c.CX.one_mem
    | one => exact Or.inl c.CX.one_mem
    | mul a b _ _ iha ihb =>
      rcases iha with iha | iha <;> rcases ihb with ihb | ihb
      · exact Or.inl (c.CX.mul_mem iha ihb)
      · exact Or.inr (by rw [mul_assoc]; exact c.CX.mul_mem iha ihb)
      · right
        have h := c.CX.mul_mem iha (hconj b ihb)
        have he : a * t * (t * b * t⁻¹) = a * b * t :=
          calc a * t * (t * b * t⁻¹) = a * (t * t) * b * t⁻¹ := by group
            _ = a * b * t := by rw [htt, mul_one, htinv]
        rwa [he] at h
      · left
        have h := c.CX.mul_mem iha (hconj _ ihb)
        have he : a * t * (t * (b * t) * t⁻¹) = a * b :=
          calc a * t * (t * (b * t) * t⁻¹) = a * (t * t) * b := by group
            _ = a * b := by rw [htt, mul_one]
        rwa [he] at h
    | inv a _ iha =>
      rcases iha with iha | iha
      · exact Or.inl (c.CX.inv_mem iha)
      · right
        have h := hconj _ (c.CX.inv_mem iha)
        have he : t * (a * t)⁻¹ * t⁻¹ = a⁻¹ * t :=
          calc t * (a * t)⁻¹ * t⁻¹ = a⁻¹ * t⁻¹ := by group
            _ = a⁻¹ * t := by rw [htinv]
        rwa [he] at h
  have hct : ∀ x ∈ c.NX, x ∈ c.CX ∨ x * t ∈ c.CX := fun x hx =>
    key x (by rw [← Subgroup.sup_eq_closure, ← hsup]; exact hx)
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨t, htN⟩, ?_⟩
  rintro ⟨x, hx⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases hct x hx with h | h
  · refine Or.inr ⟨h, fun h' => htC ?_⟩
    simpa using c.CX.mul_mem (c.CX.inv_mem h) h'
  · exact Or.inl ⟨h, fun h' => htC (by simpa using c.CX.mul_mem (c.CX.inv_mem h') h)⟩

theorem mul_self_eq_one_of_mem_NX
    {W : Type} [Group W] [Finite W] {M : Subgroup W} {T : W}
    (hmod : CFSG.Quasithin.TwoM22.IsTwoM22TwoModel M T) (c : Loc49 G z) :
    ∀ n ∈ c.NX, n ∉ c.CX → (∀ x ∈ c.CX, n * n * x = x * (n * n)) → n * n = 1 := by
  intro n hn hnC hcomm
  obtain ⟨t, htN, htC, htt, htX, -⟩ := c.exists_t
  have hXN : ∀ m ∈ c.NX, ∀ y ∈ c.X, m * y * m⁻¹ ∈ c.X := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp hm.2 y).mp hy
  exact CFSG.Quasithin.TwoM22.mul_self_eq_one_of_isTwoM22TwoModel_of_card_ker_eq_six hmod
    c.CX_le_NX c.CX_normal_NX' c.relIndex_CX_NX
    (fun g hg hcomm => c.self_centralizing_NX hg hcomm) c.isPerfect_CX c.qC c.qC_surjective
    c.qC_ker_le_center c.card_qC_ker c.X_le_CX c.card_X (fun y hy => c.qC_of_mem_X hy) hXN
    htN htC htt htX hn hnC hcomm

end Loc49

end CFSG.Quasithin.H13.AS91
