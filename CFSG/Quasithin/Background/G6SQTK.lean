module

public import CFSG.Quasithin.Background.G6Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

namespace G6

theorem isKGroup_subgroup {S : Type} [Group S] (hS : CFSG.SectionRank.IsKGroupCat S)
    (Y : Subgroup S) : CFSG.SectionRank.IsKGroupCat Y :=
  hS.subgroup Y

private theorem isElementaryAbelian_map {S : Type*} [Group S] (Y : Subgroup S) (p : ℕ)
    (A : Subgroup Y) [hA : CFSG.IsElementaryAbelian p A] :
    CFSG.IsElementaryAbelian p (A.map Y.subtype) :=
  CFSG.IsElementaryAbelian.subgroup_map inferInstance _

theorem pRank_subgroup_le {S : Type} [Group S] [Finite S] (Y : Subgroup S) {p : ℕ}
    (hp : p.Prime) : CFSG.pRank p Y ≤ CFSG.pRank p S := by
  unfold CFSG.pRank
  set sY : Set ℕ := {r | ∃ A : Subgroup Y, CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ r}
    with hsY
  set sS : Set ℕ := {r | ∃ A : Subgroup S, CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ r}
    with hsS
  rcases sY.eq_empty_or_nonempty with h | h
  · rw [h]
    simp
  · refine csSup_le_csSup ?_ h ?_
    · refine ⟨Nat.card S, ?_⟩
      rintro r ⟨A, _, hA⟩
      have h1 : p ^ r ≤ Nat.card S := hA ▸ Subgroup.card_le_card_group A
      exact (Nat.lt_pow_self hp.one_lt).le.trans h1
    · rintro r ⟨A, hA, hr⟩
      refine ⟨A.map Y.subtype, isElementaryAbelian_map Y p A, ?_⟩
      rw [Subgroup.card_map_of_injective Y.subtype_injective, hr]

theorem _root_.CFSG.Quasithin.IsQuotientOfSQTK.of_le {G : Type*} [Group G] {K X : Subgroup G}
    (hKX : K ≤ X) (h : IsQuotientOfSQTK X) : IsQuotientOfSQTK K := by
  obtain ⟨S, _, _, ⟨hst, hkg⟩, φ, hφ⟩ := h
  let S' : Subgroup S := (K.subgroupOf X).comap φ
  let ψ : S' →* K :=
    { toFun := fun s => ⟨((φ s : X) : G), Subgroup.mem_subgroupOf.1 s.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hψ : Function.Surjective ψ := by
    intro k
    obtain ⟨s, hs⟩ := hφ ⟨(k : G), hKX k.2⟩
    exact ⟨⟨s, Subgroup.mem_subgroupOf.2 (by rw [hs]; exact k.2)⟩, Subtype.ext (by simp [ψ, hs])⟩
  refine ⟨S', inferInstance, inferInstance, ⟨?_, isKGroup_subgroup hkg S'⟩, ψ, hψ⟩
  intro p hp hp2
  exact (pRank_subgroup_le S' hp).trans (hst p hp hp2)

end G6

end CFSG.Quasithin
