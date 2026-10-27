module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Single

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

namespace Sec4PSU

theorem mem_ker_of_mem_commutator_commutator {G T : Type*} [Group G] [Finite T]
    (hT : Nat.card T = 3) {C : Subgroup G} (f : ↥C →* Equiv.Perm T) {x : G}
    (hx : x ∈ ⁅⁅C, C⁆, ⁅C, C⁆⁆) : ∃ hxC : x ∈ C, f ⟨x, hxC⟩ = 1 := by
  classical
  haveI : Fintype T := Fintype.ofFinite T
  haveI : Nontrivial T := by
    rw [← Finite.one_lt_card_iff_nontrivial, hT]
    norm_num
  have hcardA : Nat.card (alternatingGroup T) = 3 := by
    rw [nat_card_alternatingGroup, hT]
    rfl
  haveI : Fact (Nat.Prime (Nat.card (alternatingGroup T))) := ⟨by rw [hcardA]; norm_num⟩
  haveI : IsCyclic (alternatingGroup T) := isCyclic_of_prime_card rfl
  have hAcomm : ∀ σ ∈ alternatingGroup T, ∀ τ ∈ alternatingGroup T, σ * τ = τ * σ := by
    intro σ hσ τ hτ
    have := (IsCyclic.commGroup (α := alternatingGroup T)).mul_comm ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact congrArg Subtype.val this
  set P : Subgroup (Equiv.Perm T) := ⊤ with hPdef
  have hP1 : ⁅P, P⁆ ≤ alternatingGroup T := by
    rw [Subgroup.commutator_le]
    intro σ _ τ _
    rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have hP2 : ⁅⁅P, P⁆, ⁅P, P⁆⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro σ hσ τ hτ
    rw [Subgroup.mem_bot, commutatorElement_def, hAcomm σ (hP1 hσ) τ (hP1 hτ)]
    group
  set U : Subgroup ↥C := ⊤ with hUdef
  have hmapTop : U.map C.subtype = C := by
    rw [hUdef, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hC'' : ⁅⁅C, C⁆, ⁅C, C⁆⁆ = (⁅⁅U, U⁆, ⁅U, U⁆⁆).map C.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hmapTop]
  rw [hC''] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y.2, ?_⟩
  have hfy : f y ∈ (⁅⁅U, U⁆, ⁅U, U⁆⁆).map f := Subgroup.mem_map_of_mem f hy
  have hle : (⁅⁅U, U⁆, ⁅U, U⁆⁆).map f ≤ ⁅⁅P, P⁆, ⁅P, P⁆⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_top)
      (Subgroup.commutator_mono le_top le_top)
  have := hle hfy
  rw [hP2, Subgroup.mem_bot] at this
  simpa using this

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

noncomputable instance commSpaceMulAction (S : Setting z E F) (β : Hbar z) :
    MulAction ↥(Subgroup.centralizer {β})
      {w : ↥(commSpace (rhoLin S β)) // w ≠ 0} where
  smul c w := ⟨⟨rhoLin S c w.1, rhoLin_mem_commSpace_of_commute S
      (Subgroup.mem_centralizer_singleton_iff.1 c.2) w.1.2⟩, fun h => w.2 (by
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero] at h'
    simpa using (rhoLin S c).injective (h'.trans (map_zero _).symm))⟩
  one_smul w := by
    apply Subtype.ext
    apply Subtype.ext
    change rhoLin S 1 w.1 = w.1
    rw [rhoLin, map_one]
    rfl
  mul_smul c d w := by
    apply Subtype.ext
    apply Subtype.ext
    change rhoLin S (c * d) w.1 = rhoLin S c (rhoLin S d w.1)
    rw [rhoLin_mul]
    rfl

theorem commutator_commutator_centralizer_le_commSpaceFixer (S : Setting z E F) {β : Hbar z}
    (hβ : β ∈ A2set S) :
    ⁅⁅Subgroup.centralizer {β}, Subgroup.centralizer {β}⁆,
        ⁅Subgroup.centralizer {β}, Subgroup.centralizer {β}⁆⁆ ≤ commSpaceFixer S β := by
  classical
  have hdim := finrank_commSpace_rhoLin_eq_two S hβ
  have hcard : Nat.card {w : ↥(commSpace (rhoLin S β)) // w ≠ 0} = 3 := by
    have h4 : Nat.card ↥(commSpace (rhoLin S β)) = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hdim, Nat.card_zmod]
      norm_num
    haveI : Fintype ↥(commSpace (rhoLin S β)) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card, h4]
    simp
  intro x hx
  obtain ⟨hxC, hfx⟩ := mem_ker_of_mem_commutator_commutator hcard
    (MulAction.toPermHom ↥(Subgroup.centralizer {β}) {w : ↥(commSpace (rhoLin S β)) // w ≠ 0})
    hx
  rw [mem_commSpaceFixer]
  intro w hw
  by_cases hw0 : (⟨w, hw⟩ : ↥(commSpace (rhoLin S β))) = 0
  · have : w = 0 := congrArg Subtype.val hw0
    rw [this, map_zero]
  · have := congrArg (fun σ : Equiv.Perm {w : ↥(commSpace (rhoLin S β)) // w ≠ 0} =>
      ((σ ⟨⟨w, hw⟩, hw0⟩ : {w : ↥(commSpace (rhoLin S β)) // w ≠ 0}).1 :
        Additive (QbarOf S))) hfx
    exact this

end Sec4PSU

end CFSG.RankThree.GF2n.Stroth78
