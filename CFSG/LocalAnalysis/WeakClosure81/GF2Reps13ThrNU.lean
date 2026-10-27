module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

theorem s13_map_conj_eq_of_normalizes {O P : Subgroup (MulAut W)}
    (h : ∀ y ∈ O, ∀ x ∈ P, y * x * y⁻¹ ∈ P) {n : MulAut W} (hn : n ∈ O) :
    P.map (MulAut.conj n).toMonoidHom = P := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact h n hn x hx
  · intro x hx
    refine ⟨n⁻¹ * x * n, ?_, ?_⟩
    · simpa using h n⁻¹ (O.inv_mem hn) x hx
    · change n * (n⁻¹ * x * n) * n⁻¹ = x
      group

theorem s13_commSub_invariant_of_normalizes {N L : Subgroup (MulAut W)}
    (h : ∀ n ∈ N, L.map (MulAut.conj n).toMonoidHom = L) :
    ∀ n ∈ N, ∀ w ∈ commSub ⊤ L, n w ∈ commSub ⊤ L := by
  intro n hn w hw
  have hmem : ∀ x ∈ L, n * x * n⁻¹ ∈ L := by
    intro x hx
    have : n * x * n⁻¹ ∈ L.map (MulAut.conj n).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h n hn] at this
  rw [commSub] at hw
  refine Subgroup.closure_induction (p := fun c _ => n c ∈ commSub ⊤ L) ?_ ?_ ?_ ?_ hw
  · rintro c ⟨x, hx, v, -, rfl⟩
    have h1 : n (x v * v⁻¹) = (n * x * n⁻¹) (n v) * (n v)⁻¹ := by
      simp [MulAut.mul_apply]
    rw [h1]
    exact Subgroup.subset_closure ⟨n * x * n⁻¹, hmem x hx, n v, Subgroup.mem_top _, rfl⟩
  · simp
  · intro a b ha hb iha ihb
    rw [map_mul]
    exact (commSub ⊤ L).mul_mem iha ihb
  · intro a ha iha
    rw [map_inv]
    exact (commSub ⊤ L).inv_mem iha

end CFSG.LocalAnalysis.WeakClosure81
