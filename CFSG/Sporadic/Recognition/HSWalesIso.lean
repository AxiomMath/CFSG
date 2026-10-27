module

public import CFSG.Sporadic.Recognition.HSWalesModel
public import CFSG.Sporadic.Recognition.HSGraphModel

public section

namespace CFSG.Sporadic.Recognition.HSWales

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Sporadic.Recognition.HSGraph

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] {a b c : Ω}
  {φ : stabilizer G a ≃* M22} (𝓜 : Model G a b c φ)

namespace Model

open Classical in
@[expose] noncomputable def toVert (x : Ω) : Vert hexads :=
  if hx : x ∈ orbit (stabilizer G a) b then vPt (𝓜.ψ ⟨x, hx⟩)
  else if hy : x ∈ orbit (stabilizer G a) c then vBlk (𝓜.θ ⟨x, hy⟩) else vInf

theorem toVert_of_mem_Δ {x : Ω} (hx : x ∈ orbit (stabilizer G a) b) :
    𝓜.toVert x = vPt (𝓜.ψ ⟨x, hx⟩) := by
  simp [toVert, hx]

theorem toVert_of_mem_Γ (D : Rank3 G a b c) {x : Ω} (hx : x ∈ orbit (stabilizer G a) c) :
    𝓜.toVert x = vBlk (𝓜.θ ⟨x, hx⟩) := by
  have hΔ : x ∉ orbit (stabilizer G a) b := fun h => D.notMem_Γ_of_mem_Δ h hx
  simp [toVert, hx, hΔ]

theorem toVert_a (D : Rank3 G a b c) : 𝓜.toVert a = vInf := by
  simp [toVert, D.a_notMem_Δ, D.a_notMem_Γ]

theorem toVert_injective (D : Rank3 G a b c) : Function.Injective 𝓜.toVert := by
  intro x y h
  rcases D.cover x with hxa | hx | hx <;> rcases D.cover y with hya | hy | hy
  · rw [hxa, hya]
  · rw [hxa, toVert_a 𝓜 D, 𝓜.toVert_of_mem_Δ hy] at h
    exact absurd h (by simp)
  · rw [hxa, toVert_a 𝓜 D, 𝓜.toVert_of_mem_Γ D hy] at h
    exact absurd h (by simp)
  · rw [hya, toVert_a 𝓜 D, 𝓜.toVert_of_mem_Δ hx] at h
    exact absurd h (by simp)
  · rw [𝓜.toVert_of_mem_Δ hx, 𝓜.toVert_of_mem_Δ hy] at h
    have := 𝓜.ψ.injective (Sum.inl_injective (Option.some_injective _ h))
    exact congrArg Subtype.val this
  · rw [𝓜.toVert_of_mem_Δ hx, 𝓜.toVert_of_mem_Γ D hy] at h
    exact absurd h (by simp)
  · rw [hya, toVert_a 𝓜 D, 𝓜.toVert_of_mem_Γ D hx] at h
    exact absurd h (by simp)
  · rw [𝓜.toVert_of_mem_Γ D hx, 𝓜.toVert_of_mem_Δ hy] at h
    exact absurd h (by simp)
  · rw [𝓜.toVert_of_mem_Γ D hx, 𝓜.toVert_of_mem_Γ D hy] at h
    have := 𝓜.θ.injective (Sum.inr_injective (Option.some_injective _ h))
    exact congrArg Subtype.val this

theorem toVert_surjective (D : Rank3 G a b c) : Function.Surjective 𝓜.toVert := by
  intro v
  rcases v with _ | p | B
  · exact ⟨a, toVert_a 𝓜 D⟩
  · refine ⟨(𝓜.ψ.symm p : Ω), ?_⟩
    rw [𝓜.toVert_of_mem_Δ (𝓜.ψ.symm p).2]
    simp
  · refine ⟨(𝓜.θ.symm B : Ω), ?_⟩
    rw [𝓜.toVert_of_mem_Γ D (𝓜.θ.symm B).2]
    simp

@[expose] noncomputable def toVertEquiv (D : Rank3 G a b c) : Ω ≃ Vert hexads :=
  Equiv.ofBijective 𝓜.toVert ⟨𝓜.toVert_injective D, 𝓜.toVert_surjective D⟩

variable [Finite Ω] [IsPretransitive G Ω] (D : Rank3 G a b c)

include 𝓜 D

theorem adj_toVert
    (x y : Ω) :
    (hsGraph hexads).Adj (𝓜.toVert x) (𝓜.toVert y) ↔ (rGraph G a b).Adj x y := by
  rcases D.cover x with hxa | hx | hx <;> rcases D.cover y with hya | hy | hy
  · rw [hxa, hya, toVert_a 𝓜 D]
    simp
  · rw [hxa, toVert_a 𝓜 D, 𝓜.toVert_of_mem_Δ hy, D.adj_a]
    simp [hy]
  · have hyΔ : y ∉ orbit (stabilizer G a) b := fun h => D.notMem_Γ_of_mem_Δ h hy
    rw [hxa, toVert_a 𝓜 D, 𝓜.toVert_of_mem_Γ D hy, D.adj_a]
    simp [hyΔ]
  · rw [hya, toVert_a 𝓜 D, 𝓜.toVert_of_mem_Δ hx, SimpleGraph.adj_comm _ x, D.adj_a]
    simp [hx]
  · rw [𝓜.toVert_of_mem_Δ hx, 𝓜.toVert_of_mem_Δ hy]
    exact iff_of_false (by simp) (𝓜.not_adj_Δ D ⟨x, hx⟩ ⟨y, hy⟩)
  · rw [𝓜.toVert_of_mem_Δ hx, 𝓜.toVert_of_mem_Γ D hy]
    exact (𝓜.adj_Δ_Γ D ⟨x, hx⟩ ⟨y, hy⟩).symm
  · have hxΔ : x ∉ orbit (stabilizer G a) b := fun h => D.notMem_Γ_of_mem_Δ h hx
    rw [hya, toVert_a 𝓜 D, 𝓜.toVert_of_mem_Γ D hx, SimpleGraph.adj_comm _ x, D.adj_a]
    simp [hxΔ]
  · rw [𝓜.toVert_of_mem_Γ D hx, 𝓜.toVert_of_mem_Δ hy, SimpleGraph.adj_comm _ x,
      SimpleGraph.adj_comm]
    exact (𝓜.adj_Δ_Γ D ⟨y, hy⟩ ⟨x, hx⟩).symm
  · rw [𝓜.toVert_of_mem_Γ D hx, 𝓜.toVert_of_mem_Γ D hy]
    exact (𝓜.adj_Γ_Γ D ⟨x, hx⟩ ⟨y, hy⟩).symm

@[expose] noncomputable def graphIso :
    rGraph G a b ≃g hsGraph hexads :=
  ⟨𝓜.toVertEquiv D, fun {x y} => 𝓜.adj_toVert D x y⟩

theorem isSRGWith
    [Fintype Ω] [DecidableRel (rGraph G a b).Adj] :
    (rGraph G a b).IsSRGWith 100 22 0 6 :=
  isSRGWith_of_equiv (𝓜.toVertEquiv D) (fun u w => 𝓜.adj_toVert D u w) isSRGWith_hexads

end Model

end CFSG.Sporadic.Recognition.HSWales
