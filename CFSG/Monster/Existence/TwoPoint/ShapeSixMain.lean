module

public import CFSG.Monster.Existence.TwoPointConj
public import CFSG.Monster.GMS.S342
public import CFSG.LieType.Chevalley.AdjointCenter

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

section Transport

variable {H H' : Type*} [Group H] [Group H']

theorem shapeSix_centralizer_pair_eq_inf (c e : H) :
    Subgroup.centralizer ({c, e} : Set H) =
      Subgroup.centralizer {c} ⊓ Subgroup.centralizer {e} := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem map_centralizer_pair_equiv (f : H ≃* H') (c e : H) :
    (Subgroup.centralizer ({c, e} : Set H)).map f.toMonoidHom =
      Subgroup.centralizer {f c} ⊓ Subgroup.centralizer {f e} := by
  rw [shapeSix_centralizer_pair_eq_inf, Subgroup.map_inf _ _ _ f.injective,
    map_centralizer_singleton, map_centralizer_singleton]

theorem pairCent_transport_equiv (f : H ≃* H') (c e : H) :
    Nat.card ↥(Subgroup.centralizer ({f c} : Set H') ⊓ Subgroup.centralizer ({f e} : Set H')) =
        Nat.card ↥(Subgroup.centralizer ({c, e} : Set H)) ∧
      Nat.card ↥⁅Subgroup.centralizer ({f c} : Set H') ⊓ Subgroup.centralizer ({f e} : Set H'),
          Subgroup.centralizer ({f c} : Set H') ⊓ Subgroup.centralizer ({f e} : Set H')⁆ =
        Nat.card ↥⁅Subgroup.centralizer ({c, e} : Set H), Subgroup.centralizer ({c, e} : Set H)⁆ ∧
      Nonempty (↥⁅Subgroup.centralizer ({f c} : Set H') ⊓ Subgroup.centralizer ({f e} : Set H'),
          Subgroup.centralizer ({f c} : Set H') ⊓ Subgroup.centralizer ({f e} : Set H')⁆ ≃*
        ↥⁅Subgroup.centralizer ({c, e} : Set H), Subgroup.centralizer ({c, e} : Set H)⁆) := by
  have hR := map_centralizer_pair_equiv f c e
  have hF : ⁅Subgroup.centralizer ({f c} : Set H') ⊓ Subgroup.centralizer ({f e} : Set H'),
      Subgroup.centralizer ({f c} : Set H') ⊓ Subgroup.centralizer ({f e} : Set H')⁆ =
      (⁅Subgroup.centralizer ({c, e} : Set H), Subgroup.centralizer ({c, e} : Set H)⁆).map
        f.toMonoidHom := by
    rw [← hR, Subgroup.map_commutator]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hR, Subgroup.card_map_of_injective f.injective]
  · rw [hF, Subgroup.card_map_of_injective f.injective]
  · exact ⟨(MulEquiv.subgroupCongr hF).trans
      (Subgroup.equivMapOfInjective _ f.toMonoidHom f.injective).symm⟩

end Transport

theorem lieModel_F4_of_mulEquiv
    {X : Type} [Group X]
    (e : X ≃* ↥(adjointGroup Tag.F4 (ZMod 2))) : LieModel X .F4 0 2 1 := by
  refine Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl⟩, ZMod 2, inferInstance,
    inferInstance, by simp, ⟨?_⟩⟩)
  exact e.trans ((QuotientGroup.quotientBot (G := ↥(adjointGroup Tag.F4 (ZMod 2)))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.F4) (K := ZMod 2)).symm))

theorem exists_base_rep_fourB {G : Type} [Group G] {a z₀ α β : G} (hα : IsConj a α)
    (hβ : β ∈ tableVIISet a z₀ α .four_B) (hs : TwoPointShape (cent2 α β) 6) :
    ∃ y, y ∈ tableVIISet a z₀ a .four_B ∧ TwoPointShape (cent2 a y) 6 := by
  obtain ⟨k, rfl⟩ := isConj_iff.1 hα.symm
  obtain ⟨h1, h2, h3⟩ := hβ
  have e : k * α * k⁻¹ * (k * β * k⁻¹) = k * (α * β) * k⁻¹ := by group
  have hconj : ∀ w : G, IsConj w (k * w * k⁻¹) := fun w => isConj_iff.2 ⟨k, rfl⟩
  refine ⟨k * β * k⁻¹, ⟨h1.trans (hconj β), ?_, ?_⟩, TwoPointShape.conj k hs⟩
  · rw [e, ← orderOf_eq_of_isConj (hconj (α * β))]
    exact h2
  · rw [e, conj_pow]
    exact h3.trans (hconj _)

end CFSG.Monster.Existence
