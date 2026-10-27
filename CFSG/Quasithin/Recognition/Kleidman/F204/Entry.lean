module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Frame
public import CFSG.Quasithin.EmptyFaithful.SzF53A2

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.FA5

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem hyp111R_of (hyp : Hyp111 L1 L2 S)
    (h1 : Nonempty (OTwoQuot L1 ≃* DihedralGroup 5) ∨ Nonempty (OTwoQuot L1 ≃* ↥(Sz 0)))
    (h2 : Nonempty (OTwoQuot L2 ≃* ↥(alternatingGroup (Fin 5)))) : Hyp111R L1 L2 S := by
  obtain ⟨e₂⟩ := h2
  refine ⟨hyp, ?_, F1.rankOneAt_of_isRankOneSylow hyp.h2.sylow
    (isRankOneSylow_alternatingGroup_five.of_mulEquiv e₂.symm)⟩
  rcases h1 with h | h
  · obtain ⟨e₁⟩ := h
    exact F1.rankOneAt_of_isRankOneSylow hyp.h1.sylow
      (isRankOneSylow_dihedral_five.of_mulEquiv e₁.symm)
  · obtain ⟨e₁⟩ := h
    exact F1.rankOneAt_of_isRankOneSylow hyp.h1.sylow
      (isRankOneSylow_sz_zero.of_mulEquiv e₁.symm)

omit [Finite G] in
theorem card_quot_left
    (h1 : Nonempty (OTwoQuot L1 ≃* DihedralGroup 5) ∨ Nonempty (OTwoQuot L1 ≃* ↥(Sz 0))) :
    Nat.card (OTwoQuot L1) = 10 ∨ Nat.card (OTwoQuot L1) = 20 := by
  rcases h1 with h | h
  · obtain ⟨e⟩ := h
    left
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  · obtain ⟨e⟩ := h
    right
    rw [Nat.card_congr e.toEquiv, card_sz_zero_eq_twenty]

theorem pair_of (hyp : Hyp111 L1 L2 S)
    (h1 : Nonempty (OTwoQuot L1 ≃* DihedralGroup 5) ∨ Nonempty (OTwoQuot L1 ≃* ↥(Sz 0)))
    (h2 : Nonempty (OTwoQuot L2 ≃* ↥(alternatingGroup (Fin 5)))) : Pair L1 L2 S := by
  refine ⟨hyp111R_of hyp h1 h2, ?_, h2⟩
  rcases card_quot_left h1 with h | h
  · exact ⟨1, le_rfl, by rw [h]; norm_num⟩
  · exact ⟨2, by norm_num, by rw [h]; norm_num⟩

theorem exists_frame_of (hyp : Hyp111 L1 L2 S)
    (h1 : Nonempty (OTwoQuot L1 ≃* DihedralGroup 5) ∨ Nonempty (OTwoQuot L1 ≃* ↥(Sz 0)))
    (h2 : Nonempty (OTwoQuot L2 ≃* ↥(alternatingGroup (Fin 5))))
    (hu : ∀ s ∈ S, ∃ l ∈ L2, ∃ q ∈ pCoreOf 2 (L2 ⊔ bigB L1 L2 S), s = l * q) :
    ∃ D X : Subgroup G, Frame L1 L2 S D X :=
  (pair_of hyp h1 h2).exists_frame (card_quot_left h1) hu

end CFSG.Quasithin.Kleidman.F204
