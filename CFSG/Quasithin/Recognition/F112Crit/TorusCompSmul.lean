module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusComp

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

open CosetGeom (graph stab)

variable {G₀ G₁ G₂ : Subgroup G} {X : Subgroup G} {δ : CosetGeom G₀ G₁ G₂}

theorem smul_mem_torusComp_smul {n : ↥G₀} (hn : (n : G) ∈ normalizer (X : Set G))
    {v : CosetGeom G₀ G₁ G₂} (hv : v ∈ torusComp X δ) : n • v ∈ torusComp X (n • δ) := by
  induction hv with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih =>
    exact ih.tail ⟨le_stab_smul_of_mem_normalizer hn h.1, le_stab_smul_of_mem_normalizer hn h.2.1,
      (CosetGeom.smul_adj n).mpr h.2.2⟩

theorem smul_torusComp {n : ↥G₀} (hn : (n : G) ∈ normalizer (X : Set G))
    (δ : CosetGeom G₀ G₁ G₂) : n • torusComp X δ = torusComp X (n • δ) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact smul_mem_torusComp_smul hn hv
  · intro hw
    have hn' : ((n⁻¹ : ↥G₀) : G) ∈ normalizer (X : Set G) := by
      rw [Subgroup.coe_inv]
      exact inv_mem hn
    have h := smul_mem_torusComp_smul hn' hw
    rw [inv_smul_smul] at h
    exact ⟨n⁻¹ • w, h, smul_inv_smul n w⟩

private theorem mem_torusComp_symm {v : CosetGeom G₀ G₁ G₂} (hv : v ∈ torusComp X δ) :
    δ ∈ torusComp X v := by
  induction hv with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact Relation.ReflTransGen.head ⟨h.2.1, h.1, h.2.2.symm⟩ ih

theorem torusComp_eq_of_mem {v : CosetGeom G₀ G₁ G₂} (hv : v ∈ torusComp X δ) :
    torusComp X v = torusComp X δ := by
  ext w
  exact ⟨fun hw => Relation.ReflTransGen.trans hv hw,
    fun hw => Relation.ReflTransGen.trans (mem_torusComp_symm hv) hw⟩

theorem smul_torusComp_eq {n : ↥G₀} (hn : (n : G) ∈ normalizer (X : Set G))
    {v : CosetGeom G₀ G₁ G₂} (hv : v ∈ torusComp X δ) (hnv : n • v ∈ torusComp X δ) :
    n • torusComp X δ = torusComp X δ :=
  calc n • torusComp X δ = n • torusComp X v := by rw [torusComp_eq_of_mem hv]
    _ = torusComp X (n • v) := smul_torusComp hn v
    _ = torusComp X δ := torusComp_eq_of_mem hnv

theorem IsEdgeHall.smul {μ : CosetGeom G₀ G₁ G₂} (h : IsEdgeHall μ δ X) (g : ↥G₀) :
    IsEdgeHall (g • μ) (g • δ) (conjSub (g : G) X) := by
  unfold IsEdgeHall at h ⊢
  obtain ⟨hle, hodd, k, hk⟩ := h
  have e : stab (g • μ) ⊓ stab (g • δ) = conjSub (g : G) (stab μ ⊓ stab δ) := by
    rw [CosetGeom.stab_smul, CosetGeom.stab_smul, conjSub_inf]
  refine ⟨?_, ?_, k, ?_⟩
  · rw [e]
    exact conjSub_mono _ hle
  · rwa [show Nat.card (conjSub (g : G) X) = Nat.card X from
      Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj (g : G)))]
  · rw [e, ← hk]
    exact Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj (g : G)).toMonoidHom) X _
      (MulEquiv.injective _)

end CFSG.Quasithin.F112Crit

end
