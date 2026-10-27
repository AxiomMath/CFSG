module

public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

open scoped commutatorElement

namespace CFSG.Quasithin

open CFSG.Open

namespace S1421NS

theorem prime_card_of_isSimpleGroup_of_isSolvable {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] [Group.IsSolvable Y] : (Nat.card Y).Prime := by
  have h1 : commutator Y < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial Y
  have h2 : commutator Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
    · exact h
    · exact absurd h h1.ne
  let _ : CommGroup Y := { ‹Group Y› with
    mul_comm := fun a b => by
      have : ⁅a, b⁆ ∈ commutator Y :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this }
  exact IsSimpleGroup.prime_card

variable {G : Type} [Group G] [Finite G]

theorem solvRad_le_pCoreOf_of_simple {K1 : Subgroup G}
    (hsimple : IsSimpleGroup (OTwoQuot K1)) (hcard : ¬ (Nat.card (OTwoQuot K1)).Prime) :
    solvRad K1 ≤ pCoreOf 2 K1 := by
  intro x hx
  have hxK : x ∈ K1 := solvRad_le K1 hx
  set π : ↥K1 →* OTwoQuot K1 := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1) with hπ
  set P : Subgroup ↥K1 := (solvRad K1).subgroupOf K1 with hP
  have hPn : P.Normal := solvRad_normal K1
  have hmapn : (P.map π).Normal := hPn.map π (QuotientGroup.mk'_surjective _)
  have hxP : (⟨x, hxK⟩ : ↥K1) ∈ P := hx
  rcases hsimple.eq_bot_or_eq_top_of_normal (P.map π) with h | h
  · have h1 : π ⟨x, hxK⟩ ∈ P.map π := Subgroup.mem_map_of_mem _ hxP
    rw [h, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hxK⟩ : ↥K1) ∈ CFSG.Open.pCore 2 ↥K1 := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨⟨x, hxK⟩, h2, rfl⟩
  · exfalso
    have hPs : Group.IsSolvable ↥P := by
      have := solvRad_isSolvable K1
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (solvRad_le K1)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (solvRad_le K1)).injective
    have hsurj : Function.Surjective (π.comp P.subtype) := by
      intro y
      have : y ∈ P.map π := h ▸ Subgroup.mem_top y
      obtain ⟨z, hz, rfl⟩ := this
      exact ⟨⟨z, hz⟩, rfl⟩
    have hYs : Group.IsSolvable (OTwoQuot K1) := Group.isSolvable_of_surjective hsurj
    have := hsimple
    exact hcard (prime_card_of_isSimpleGroup_of_isSolvable)

end S1421NS

end CFSG.Quasithin
