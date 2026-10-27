module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NHyp
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG

theorem gl32_isPerfect : Group.IsPerfect (GL (Fin 3) (ZMod 2)) := by
  haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (commutator (GL (Fin 3) (ZMod 2))) with h | h
  · exfalso
    haveI : IsMulCommutative (GL (Fin 3) (ZMod 2)) := (commutator_eq_bot_iff _).mp h
    have hp := (Group.is_simple_iff_prime_card (α := GL (Fin 3) (ZMod 2))).mp inferInstance
    rw [CFSG.ComponentClassification.GHarris.card_GL32_gh] at hp
    exact absurd hp (by norm_num)
  · exact h

variable {G : Type} [Group G]

theorem isSimpleGroup_of_iso {L : Subgroup G} (e : L ≃* GL (Fin 3) (ZMod 2)) :
    IsSimpleGroup L := by
  haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  exact e.isSimpleGroup

theorem commutator_self_of_iso {L : Subgroup G} (e : L ≃* GL (Fin 3) (ZMod 2)) :
    ⁅L, L⁆ = L := by
  haveI := gl32_isPerfect
  haveI : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  exact Subgroup.commutator_eq_self

theorem not_mem_of_hyp [Finite G] {Q L : Subgroup G} {b : G} (h : NHyp Q L b) {R : Subgroup G}
    (hRQ : R ≤ Q) : b ∉ R := by
  intro hb
  have h3 : 3 ∣ Nat.card Q :=
    h.order ▸ (Subgroup.orderOf_dvd_natCard R hb).trans (Subgroup.card_dvd_of_le hRQ)
  exact absurd (Nat.Coprime.eq_one_of_dvd h.coprime h3) (by norm_num)

theorem eq_one_of_mem_inf [Finite G] {Q L : Subgroup G} {b : G} (h : NHyp Q L b)
    {R : Subgroup G} (hRQ : R ≤ Q) (hRL : ∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ ∈ R) {l : G}
    (hl : l ∈ L) (hlR : l ∈ R) : l = 1 := by
  obtain ⟨e⟩ := h.iso
  haveI := isSimpleGroup_of_iso e
  haveI : (R.subgroupOf L).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hRL g g.2 n hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf L) with h1 | h1
  · have : (⟨l, hl⟩ : L) ∈ R.subgroupOf L := hlR
    rw [h1, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  · exfalso
    have : (⟨b, h.mem⟩ : L) ∈ R.subgroupOf L := by rw [h1]; trivial
    exact not_mem_of_hyp h hRQ this

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
