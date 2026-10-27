module

public import CFSG.Monster.B.GSide.NativeCompletionCore
public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
public import CFSG.Monster.B.Recog.GenericTits

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

@[expose] def cw0 :
    CVert := nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ 1)

theorem cgraph_adj_cv0_cw0 :
    cgraph.Adj cv0 cw0 := nbr_adj a0_mem_Ehat a0_not_mem_N1 _

@[expose, reducible] def cvLeftAction :
    MulAction Shat CVert where
  smul g x := cvMul x g⁻¹
  one_smul x := by
    show cvMul x 1⁻¹ = x
    rw [inv_one, cvMul_one]
  mul_smul g h x := by
    show cvMul x (g * h)⁻¹ = cvMul (cvMul x h⁻¹) g⁻¹
    rw [mul_inv_rev, cvMul_mul]

theorem native_universal_completion_of_ambient
    (hamb : AmbientRootOrbitsHyp)
    (u : Fin 2 → CVert) (hu : ∀ j, cgraph.Adj cv0 (u j) ∧ cgraph.Adj cw0 (u j))
    (htype : triType cv0 cw0 (u 0) = 1782 ∧ triType cv0 cw0 (u 1) = 44352)
    {Y : Type*} [Group Y] (φv : vStab cv0 →* Y) (φe : cvSetStab {cv0, cw0} →* Y)
    (φt : ∀ j, cvSetStab {cv0, cw0, u j} →* Y)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, u j}),
      φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, u j}),
      φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    ∃! Φ : Shat →* Y, (∀ a : vStab cv0, Φ a = φv a) ∧ (∀ a : cvSetStab {cv0, cw0}, Φ a = φe a) ∧
      ∀ j (a : cvSetStab {cv0, cw0, u j}), Φ a = φt j a := by
  let _ : MulAction Shat CVert := cvLeftAction
  have hvw := cgraph_adj_cv0_cw0
  have hne : cv0 ≠ cw0 := hvw.ne
  have hmem : ∀ j (s : Shat), (cvMul cv0 s = cw0 ∧ cvMul cw0 s = cv0 ∧ cvMul (u j) s = u j) ∨
      (cvMul cv0 s = cw0 ∧ cvMul cw0 s = u j ∧ cvMul (u j) s = cv0) →
        s⁻¹ ∈ cvSetStab {cv0, cw0, u j} := by
    rintro j s (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · refine (cvSetStab _).inv_mem (mem_cvSetStab_triple ⟨?_, ?_, ?_⟩ ?_)
      · rw [h1]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · rw [h2]; exact Set.mem_insert _ _
      · rw [h3]; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
      · rintro y (rfl | rfl | rfl)
        · exact ⟨cw0, Set.mem_insert_of_mem _ (Set.mem_insert _ _), h2⟩
        · exact ⟨cv0, Set.mem_insert _ _, h1⟩
        · exact ⟨u j, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), h3⟩
    · refine (cvSetStab _).inv_mem (mem_cvSetStab_triple ⟨?_, ?_, ?_⟩ ?_)
      · rw [h1]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · rw [h2]; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
      · rw [h3]; exact Set.mem_insert _ _
      · rintro y (rfl | rfl | rfl)
        · exact ⟨u j, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), h3⟩
        · exact ⟨cv0, Set.mem_insert _ _, h1⟩
        · exact ⟨cw0, Set.mem_insert_of_mem _ (Set.mem_insert _ _), h2⟩
  refine CFSG.Monster.B.Recog.tits_universal_completion_of_arcTransitive
    (fun g a b h => (cgraph_adj_cvMul a b g⁻¹).2 h) cgraph_connected.preconnected
    (cgraph_triangulable_of_ambient hamb) (fun a b c d hab hcd => ?_) hvw (vStab cv0)
    (cvSetStab {cv0, cw0}) (fun g => ?_) (fun g => ?_) u (fun j => cvSetStab {cv0, cw0, u j})
    (fun j g hg => ?_) (fun j => ?_) (fun j => ?_) (fun y₁ y₂ h₁ h₁₂ h₂ => ?_) φv φe φt hve hvt
    het
  ·
    obtain ⟨s, h1, h2⟩ := cvMul_edge_transitive hab hcd
    refine ⟨s⁻¹, ?_, ?_⟩
    · show cvMul a s⁻¹⁻¹ = c
      rw [inv_inv, h1]
    · show cvMul b s⁻¹⁻¹ = d
      rw [inv_inv, h2]
  ·
    show cvMul cv0 g = cv0 ↔ cvMul cv0 g⁻¹ = cv0
    refine ⟨cvMul_inv_eq_of_cvMul_eq, fun h => ?_⟩
    have h' := cvMul_inv_eq_of_cvMul_eq h
    rwa [inv_inv] at h'
  ·
    rw [← Subgroup.inv_mem_iff, mem_cvSetStab_pair hne]
    rfl
  ·
    have h := ((mem_cvSetStab.1 ((cvSetStab _).inv_mem hg)) cv0).2 (Set.mem_insert _ _)
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  ·
    obtain ⟨s, h1, h2, h3⟩ := exists_swap_of_isCTriangle ⟨hvw, (hu j).1, (hu j).2⟩
    refine ⟨s⁻¹, hmem j s (Or.inl ⟨h1, h2, h3⟩), ?_, ?_⟩
    · show cvMul cv0 s⁻¹⁻¹ = cw0
      rw [inv_inv, h1]
    · show cvMul cw0 s⁻¹⁻¹ = cv0
      rw [inv_inv, h2]
  ·
    obtain ⟨s, h1, h2, h3⟩ := exists_cycle_of_isCTriangle ⟨hvw, (hu j).1, (hu j).2⟩
    refine ⟨s⁻¹, hmem j s (Or.inr ⟨h1, h2, h3⟩), ?_, ?_, ?_⟩
    · show cvMul cv0 s⁻¹⁻¹ = cw0
      rw [inv_inv, h1]
    · show cvMul cw0 s⁻¹⁻¹ = u j
      rw [inv_inv, h2]
    · show cvMul (u j) s⁻¹⁻¹ = cv0
      rw [inv_inv, h3]
  ·
    obtain ⟨j, s, h1, h2, h3⟩ := exists_triangle_orbit hvw hu htype h₁ h₁₂ h₂
    refine ⟨j, s⁻¹, ?_, ?_, ?_⟩
    · show cvMul cv0 s⁻¹⁻¹ = cv0
      rw [inv_inv, h1]
    · show cvMul cw0 s⁻¹⁻¹ = y₁
      rw [inv_inv, h2]
    · show cvMul (u j) s⁻¹⁻¹ = y₂
      rw [inv_inv, h3]

@[expose] def cu :
    Fin 2 → CVert := Classical.choose (exists_triangle_types cgraph_adj_cv0_cw0)

theorem cgraph_adj_cu
    (j : Fin 2) : cgraph.Adj cv0 (cu j) ∧ cgraph.Adj cw0 (cu j) :=
  (Classical.choose_spec (exists_triangle_types cgraph_adj_cv0_cw0)).1 j

theorem triType_cu :
    triType cv0 cw0 (cu 0) = 1782 ∧ triType cv0 cw0 (cu 1) = 44352 :=
  (Classical.choose_spec (exists_triangle_types cgraph_adj_cv0_cw0)).2

theorem native_universal_completion_of_ambient_cu
    (hamb : AmbientRootOrbitsHyp)
    {Y : Type*} [Group Y] (φv : vStab cv0 →* Y) (φe : cvSetStab {cv0, cw0} →* Y)
    (φt : ∀ j, cvSetStab {cv0, cw0, cu j} →* Y)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu j}),
      φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu j}),
      φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    ∃! Φ : Shat →* Y, (∀ a : vStab cv0, Φ a = φv a) ∧ (∀ a : cvSetStab {cv0, cw0}, Φ a = φe a) ∧
      ∀ j (a : cvSetStab {cv0, cw0, cu j}), Φ a = φt j a :=
  native_universal_completion_of_ambient hamb cu cgraph_adj_cu triType_cu φv φe φt hve hvt het

end CFSG.Monster.B.GSide
