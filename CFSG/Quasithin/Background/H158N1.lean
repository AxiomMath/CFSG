module

public import CFSG.Quasithin.Background.HZ82Base

public section

namespace CFSG.Quasithin.H158N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H.ZTrans

variable {V : Type*} [CommGroup V]

theorem le_stabSub_commV {P N : Subgroup (MulAut V)}
    (hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : P ≤ stabSub (commV N) := by
  have key : ∀ g ∈ P, ∀ w ∈ commV N, g w ∈ commV N := by
    intro g hg w hw
    unfold commV at hw ⊢
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, v, rfl⟩ := hx
      have e : g (a v * v⁻¹) = ((g * a * g⁻¹) (g v)) * (g v)⁻¹ := by
        simp [MulAut.mul_apply, MulAut.apply_inv_self]
      rw [e]
      exact Subgroup.subset_closure ⟨g * a * g⁻¹, hN g hg a ha, g v, rfl⟩
    | one => simp
    | mul x y _ _ ihx ihy =>
      rw [map_mul]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ih =>
      rw [map_inv]
      exact Subgroup.inv_mem _ ih
  intro g hg u
  constructor
  · intro h
    have h' := key g⁻¹ (P.inv_mem hg) (g u) h
    rwa [MulAut.inv_apply_self] at h'
  · exact key g hg u

theorem conj_mem_pCoreOf {G : Type*} [Group G] (p : ℕ) {P : Subgroup G} {g n : G}
    (hg : g ∈ P) (hn : n ∈ pCoreOf p P) : g * n * g⁻¹ ∈ pCoreOf p P := by
  unfold pCoreOf at hn ⊢
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hn
  refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : P) * y * (⟨g, hg⟩ : P)⁻¹,
    (CFSG.pCore_normal (p := p) (G := P)).conj_mem y hy ⟨g, hg⟩, ?_⟩
  simp

end CFSG.Quasithin.H158N
