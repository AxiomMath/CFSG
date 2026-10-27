module

public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G] {Kb : Subgroup G}

theorem isSylowTwoOf_subgroupOf {S H : Subgroup G} (hS : S ≤ Kb) (hH : H ≤ Kb)
    (h : IsSylowTwoOf S H) : IsSylowTwoOf (S.subgroupOf Kb) (H.subgroupOf Kb) := by
  refine ⟨fun x hx => h.1 hx, ?_, ?_⟩
  · exact h.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hS).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hS).injective
  · have h1 := Subgroup.relIndex_subgroupOf (H := S) (K := H) (L := Kb) hH
    show ¬ 2 ∣ (S.subgroupOf Kb).relIndex (H.subgroupOf Kb)
    rw [h1]
    exact h.2.2

theorem subgroupOf_centralizer_singleton {g : G} (hg : g ∈ Kb) :
    (Subgroup.centralizer ({g} : Set G)).subgroupOf Kb =
      Subgroup.centralizer ({(⟨g, hg⟩ : Kb)} : Set Kb) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem centerOf_subgroupOf {X : Subgroup G} (hX : X ≤ Kb) :
    centerOf (X.subgroupOf Kb) = (centerOf X).subgroupOf Kb := by
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hc) ⟨y, hX hy⟩ hy)
  · rintro ⟨hx, hc⟩
    exact ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 hc) y.1 hy)⟩

theorem commutator_subgroupOf {X : Subgroup G} (hX : X ≤ Kb) :
    ⁅X.subgroupOf Kb, X.subgroupOf Kb⁆ = (⁅X, X⁆).subgroupOf Kb := by
  apply Subgroup.map_injective Kb.subtype_injective
  have hXX : ⁅X, X⁆ ≤ X := Subgroup.commutator_le.2 fun a ha b hb =>
    X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (hXX.trans hX)]

theorem mem_centerOf_inf_commutator_subgroupOf {X : Subgroup G} (hX : X ≤ Kb) (x : Kb) :
    x ∈ centerOf (X.subgroupOf Kb) ⊓ ⁅X.subgroupOf Kb, X.subgroupOf Kb⁆ ↔
      (x : G) ∈ centerOf X ⊓ ⁅X, X⁆ := by
  rw [centerOf_subgroupOf hX, commutator_subgroupOf hX]
  rfl

theorem card_subgroupOf {X : Subgroup G} (hX : X ≤ Kb) :
    Nat.card (X.subgroupOf Kb) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem mem_normalizer_of_conj_mem {S : Subgroup G} {α : G} (h : ∀ s ∈ S, α * s * α⁻¹ ∈ S)
    (h' : ∀ s ∈ S, α⁻¹ * s * α ∈ S) : α ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact h s
  · intro hs
    have := h' _ hs
    simpa [mul_assoc] using this

end CFSG.Quasithin.H13.F431.D4q.Out
