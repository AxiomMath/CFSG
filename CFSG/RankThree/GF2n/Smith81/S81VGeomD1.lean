module

public import CFSG.RankThree.GF2n.Smith81.S81VDefs

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem genPts_mono {X Y : Set (Submodule F (Fin 6 → F))} (hXY : X ⊆ Y)
    {W : Submodule F (Fin 6 → F)} (h : GenPts σ X W) : GenPts σ Y W := by
  induction h with
  | base hW => exact GenPts.base (hXY hW)
  | line hG1 hG2 hne h1 h2 h3 hfin hle ih1 ih2 =>
    exact GenPts.line ih1 ih2 hne h1 h2 h3 hfin hle

private theorem herm_sum_smul_right_aux {n : ℕ} (t : Finset (Fin n)) (y : Fin 6 → F)
    (c : Fin n → F) (x : Fin n → Fin 6 → F) :
    herm σ y (∑ i ∈ t, c i • x i) = ∑ i ∈ t, c i * herm σ y (x i) := by
  refine Finset.induction_on t ?_ ?_
  · simp
  · intro a u ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right, herm_smul_right, ih]

private theorem herm_span_zero {S : Set (Fin 6 → F)} (hS : ∀ a ∈ S, ∀ b ∈ S, herm σ a b = 0) :
    ∀ u ∈ Submodule.span F S, ∀ v ∈ Submodule.span F S, herm σ u v = 0 := by
  intro u hu
  have h1 : ∀ v ∈ S, herm σ u v = 0 := by
    induction hu using Submodule.span_induction with
    | mem a ha => intro v hv; exact hS a ha v hv
    | zero => intro v _; exact herm_zero_left σ v
    | add a b _ _ iha ihb => intro v hv; rw [herm_add_left, iha v hv, ihb v hv, add_zero]
    | smul c a _ iha => intro v hv; rw [herm_smul_left, iha v hv, mul_zero]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem b hb => exact h1 b hb
  | zero => exact herm_zero_right σ u
  | add a b _ _ iha ihb => rw [herm_add_right, iha, ihb, add_zero]
  | smul c a _ iha => rw [herm_smul_right, iha, mul_zero]

theorem isPt_span_triple (hσ : ∀ c, σ (σ c) = c) {x y z : Fin 6 → F} (hx : herm σ x x = 0)
    (hy : herm σ y y = 0) (hz : herm σ z z = 0) (hxy : herm σ x y = 0) (hxz : herm σ x z = 0)
    (hyz : herm σ y z = 0) (hli : LinearIndependent F ![x, y, z]) :
    IsPt σ (Submodule.span F {x, y, z}) := by
  have hS : ∀ a ∈ ({x, y, z} : Set (Fin 6 → F)), ∀ b ∈ ({x, y, z} : Set (Fin 6 → F)),
      herm σ a b = 0 := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | assumption
      | exact herm_eq_zero_comm σ hσ (by assumption)
  have hti : IsTotIso σ (Submodule.span F {x, y, z}) := herm_span_zero hS
  have hr : Set.range ![x, y, z] = ({x, y, z} : Set (Fin 6 → F)) := by
    rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]
  have hfin : finrank F (Submodule.span F {x, y, z}) = 3 := by
    have h := finrank_span_eq_card hli
    rw [hr, Fintype.card_fin] at h
    exact h
  exact ⟨hti, hfin⟩

theorem nonDeg_span_of_gram {k : ℕ} (hσ : ∀ c, σ (σ c) = c) (v : Fin k → Fin 6 → F)
    (hdet : (Matrix.of fun i j => herm σ (v i) (v j)).det ≠ 0) :
    NonDeg σ (Submodule.span F (Set.range v)) := by
  intro x hx horth
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hx
  have hmul : (Matrix.of fun i j => herm σ (v i) (v j)).mulVec c = 0 := by
    funext j
    have h0 := horth (v j) (Submodule.subset_span (Set.mem_range_self j))
    rw [herm_sum_smul_right_aux Finset.univ (v j) c v] at h0
    have h1 : ∑ i, herm σ (v j) (v i) * c i = ∑ i, c i * herm σ (v j) (v i) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    exact h1.trans h0
  have hc : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  simp [hc]

theorem genPts_of_two_through {X : Set (Submodule F (Fin 6 → F))} {x y : Fin 6 → F}
    (hxy : LinearIndependent F ![x, y]) {G₁ G₂ : Submodule F (Fin 6 → F)} (h1 : IsPt σ G₁)
    (h2 : IsPt σ G₂) (hne : G₁ ≠ G₂) (hx1 : x ∈ G₁) (hy1 : y ∈ G₁) (hx2 : x ∈ G₂) (hy2 : y ∈ G₂)
    (hG1 : GenPts σ X G₁) (hG2 : GenPts σ X G₂) :
    ∀ G, IsPt σ G → x ∈ G → y ∈ G → GenPts σ X G := by
  intro G hG hxG hyG
  have hf1 : finrank F G₁ = 3 := h1.2
  have hf2 : finrank F G₂ = 3 := h2.2
  have hfinS : finrank F (Submodule.span F {x, y}) = 2 := by
    have h := finrank_span_eq_card hxy
    rw [Matrix.range_cons_cons_empty x y ![], Fintype.card_fin] at h
    exact h
  have hle12 : Submodule.span F {x, y} ≤ G₁ ⊓ G₂ :=
    Submodule.span_le.mpr (Set.insert_subset_iff.mpr
      ⟨Submodule.mem_inf.mpr ⟨hx1, hx2⟩,
        Set.singleton_subset_iff.mpr (Submodule.mem_inf.mpr ⟨hy1, hy2⟩)⟩)
  have hd12 : finrank F (Submodule.span F {x, y}) ≤ finrank F ↥(G₁ ⊓ G₂) :=
    Submodule.finrank_mono hle12
  have hlt : G₁ ⊓ G₂ < G₁ := by
    refine lt_of_le_of_ne inf_le_left fun hpeq => hne ?_
    have hle : G₁ ≤ G₂ := (le_of_eq hpeq.symm).trans inf_le_right
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hf1, hf2])
  have hd1 : finrank F ↥(G₁ ⊓ G₂) < finrank F G₁ := Submodule.finrank_lt_finrank_of_lt hlt
  have hfin12 : finrank F ↥(G₁ ⊓ G₂) = 2 := by omega
  have heq12 : Submodule.span F {x, y} = G₁ ⊓ G₂ :=
    Submodule.eq_of_le_of_finrank_eq hle12 (by omega)
  have hsub : G₁ ⊓ G₂ ≤ G := by
    rw [← heq12]
    exact Submodule.span_le.mpr (Set.insert_subset_iff.mpr
      ⟨hxG, Set.singleton_subset_iff.mpr hyG⟩)
  exact GenPts.line hG1 hG2 hne h1 h2 hG hfin12 hsub

end CFSG.RankThree.GF2n.Smith81.S81V
