module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6Frame

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggIndepE6_radical_ne_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {h : Fin 6 → V}
    (hind : LinearIndependent (ZMod 3) h) : h 0 - h 2 + h 4 - h 5 ≠ 0 := by
  classical
  intro h0
  have hsum : ∑ i : Fin 6, (fun i : Fin 6 => if i = 0 then (1 : ZMod 3) else if i = 2 then -1
      else if i = 4 then 1 else if i = 5 then -1 else 0) i • h i = 0 := by
    rw [Fin.sum_univ_six]
    simp
    first
      | (rw [sub_eq_add_neg, sub_eq_add_neg] at h0; exact h0)
      | (rw [← h0]; abel)
      | (rw [← sub_eq_zero] at h0; rw [← h0]; abel)
      | (simpa [sub_eq_add_neg] using h0)
  have h2 := (Fintype.linearIndependent_iff.mp hind)
    (fun i : Fin 6 => if i = 0 then (1 : ZMod 3) else if i = 2 then -1
      else if i = 4 then 1 else if i = 5 then -1 else 0) hsum 0
  simp at h2

theorem ggIndepE6Frame_radical {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {h : Fin 6 → V}
    {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h) :
    GGIndepE6Frame h α (h 0 - h 2 + h 4 - h 5) := by
  refine ⟨hpair, hind, ggIndepE6_radical_ne_zero hind, ?_, ?_⟩
  · intro i
    simp only [map_sub, map_add, hpair]
    exact e6F_cartan_kernel i
  · exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _
      (Submodule.subset_span ⟨0, rfl⟩) (Submodule.subset_span ⟨2, rfl⟩))
      (Submodule.subset_span ⟨4, rfl⟩)) (Submodule.subset_span ⟨5, rfl⟩)

theorem ggXDatumE6_indep_frame_K {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hMK : MK = CoxeterMatrix.E₆.reindex e) (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p)) (hind : LinearIndependent (ZMod p) h) :
    GGIndepE6Frame (fun i => h (e i)) (fun i => α (e i))
      (h (e 0) - h (e 2) + h (e 4) - h (e 5)) := by
  classical
  subst hp3
  have hpair' : ∀ i j, α (e i) (h (e j)) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair (e i) (e j), ggIndep_cartan_of_reindexE6 e hCK hMK i j]
  have hind' : LinearIndependent (ZMod 3) (fun i => h (e i)) :=
    (linearIndependent_equiv (R := ZMod 3) e).mpr hind
  exact ggIndepE6Frame_radical hpair' hind'

end CFSG.StandardType

end
