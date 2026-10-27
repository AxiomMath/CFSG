module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Kit
public import Certificates.Certificate9521
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Gen

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.Sporadic.Th (J gA gB thEquivJ th_kernel_facts
  rowsMatrix_rowsOf_seedA rowsMatrix_rowsOf_seedB)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

namespace Item434SporTh

theorem factorization_J :
    (Nat.card J).factorization 3 = 10 := by
  rw [CFSG.Sporadic.Bridge.Th.card_J,
    show (90745943887872000 : ℕ) = 3 ^ 10 * 1536790528000 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 10 (by norm_num)]

theorem card_outer_congr_sub {W : Type*} [Group W] (J : Subgroup W) {X : Type*} [Group X]
    (e : X ≃* J) : Nat.card (Outer X) = Nat.card (Outer J) :=
  Nat.card_congr (equivalence e).toEquiv

end Item434SporTh

section Families

theorem item434Spor_Th_27 :
    Item434Spor_Th_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have b₀ : NativeSporadic.Th ≃* Spor .Th := b
  have e : layer G ⧸ Subgroup.center (layer G) ≃* J := e₀.trans (b₀.symm.trans thEquivJ)
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases hc.card_layerStar with h9 | ⟨-, hZ⟩
    · have : Nat.card hc.layerStar = 27 := h27
      omega
    · exact hZ
  have : IsSimpleGroup J := CFSG.Sporadic.Th.Kernel.isSimpleGroup_J th_kernel_facts
  have hcen : Subgroup.center J = ⊥ :=
    Item434Spor.center_eq_bot_of_simple (by rw [CFSG.Sporadic.Bridge.Th.card_J]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer J) := by
    have e' : NativeSporadic.Th ≃* J := thEquivJ
    have hq : Nat.card (Outer NativeSporadic.Th) = Nat.card (Outer J) :=
      Item434SporTh.card_outer_congr_sub J (X := NativeSporadic.Th) e'
    rw [← hq]
    have h' : Nat.card (Outer NativeSporadic.Th) = 1 :=
      CFSG.RankThree.PartOne.SPOR.card_outer_Th
    rw [h']
    norm_num
  have hgA : gA ∈ J := Subgroup.subset_closure (Set.mem_insert _ _)
  have hgB : gB ∈ J := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact (Item434SporE81.false_of_e27 hc e hcen hout
    (fun P hP hP27 => by
      obtain ⟨Q, z, hQJ, hQ, hz3, hz1, hzQ, hzc, hgood⟩ := Certificates.certificate9521
      have hQ' : Nat.card Q = 3 ^ (Nat.card J).factorization 3 := by
        rw [Item434SporTh.factorization_J, hQ]
      refine Item434SporE81.exists_e81_of_e27_ambient hQJ hQ' hz3 hz1 hzQ hzc le_rfl (by omega)
        (fun s hs hs3 hsz => ?_) hP hP27
      obtain ⟨E, hEQ, hE, hE81, hsE, hzE⟩ := hgood s hs hs3 hsz
      exact ⟨E, hEQ.trans hQJ, hE, hE81, hsE, hzE⟩) hZ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
