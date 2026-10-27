module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.ASVolI.ChH

open CFSG.Open

variable {G : Type*} [Group G]

theorem pCoreOf_le_self (p : ℕ) (H : Subgroup G) : pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

theorem isPGroup_pCoreOf (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreOf p H) :=
  (CFSG.pCore_isPGroup (p := p) (G := H)).map H.subtype

theorem pCoreOf_conj_mem {p : ℕ} {H : Subgroup G} {s : G} (hs : s ∈ H) {k : G}
    (hk : k ∈ pCoreOf p H) : s * k * s⁻¹ ∈ pCoreOf p H := by
  obtain ⟨y, hy, rfl⟩ := hk
  refine ⟨⟨s, hs⟩ * y * ⟨s, hs⟩⁻¹, ?_, rfl⟩
  exact (CFSG.pCore_normal (p := p) (G := H)).conj_mem y hy ⟨s, hs⟩

theorem le_pCoreOf_of_isPGroup_normal {p : ℕ} {H K : Subgroup G} (hKH : K ≤ H)
    (hKn : ∀ s ∈ H, ∀ k ∈ K, s * k * s⁻¹ ∈ K) (hK : IsPGroup p K) : K ≤ pCoreOf p H := by
  have hN : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff hKH).mpr fun k s hk hs => hKn s hs k hk
  have h1 : K.subgroupOf H ≤ CFSG.pCore p H := le_sSup ⟨hN, hK.comap_subtype⟩
  intro x hx
  exact ⟨⟨x, hKH hx⟩, h1 hx, rfl⟩

theorem pCoreOf_map_of_injective (p : ℕ) {G' : Type*} [Group G'] (f : G →* G')
    (hf : Function.Injective f) (H : Subgroup G) :
    pCoreOf p (H.map f) = (pCoreOf p H).map f := by
  have h := CFSG.pCore_map_iso p (Subgroup.equivMapOfInjective H f hf)
  unfold pCoreOf
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1

end CFSG.ASVolI.ChH
