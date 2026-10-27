module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Kit
public import Certificates.Certificate9520

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.Sporadic.Ly (J gA gB lyEquivJ isSimpleGroup_J card_J toMat_matA)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

namespace Item434SporLy

theorem factorization_J : (Nat.card J).factorization 3 = 7 := by
  rw [card_J, show (51765179004000000 : ℕ) = 3 ^ 7 * 23669492000000 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 7 (by norm_num)]

theorem card_outer_congr_sub {W : Type*} [Group W] (J : Subgroup W) {X : Type*} [Group X]
    (e : X ≃* J) : Nat.card (Outer X) = Nat.card (Outer J) :=
  Nat.card_congr (equivalence e).toEquiv

theorem rp_A : Rp CFSG.Sporadic.Ly.Native.matA gA := by
  show CFSG.Sporadic.He.Native.toMat 5 111 CFSG.Sporadic.Ly.Native.matA = _
  rw [toMat_matA]
  rfl

theorem rp_B : Rp CFSG.Sporadic.Ly.Native.matB gB := by
  show CFSG.Sporadic.He.Native.toMat 5 111 CFSG.Sporadic.Ly.Native.matB = _
  rw [CFSG.Sporadic.Ly.toMat_matB]
  rfl

end Item434SporLy

section Families


theorem item434Spor_Ly_27 :
    Item434Spor_Ly_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  have b₀ : NativeSporadic.Ly ≃* Spor .Ly := b
  have e : layer G ⧸ Subgroup.center (layer G) ≃* J := e₀.trans (b₀.symm.trans lyEquivJ)
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases hc.card_layerStar with h9 | ⟨-, hZ⟩
    · have : Nat.card hc.layerStar = 27 := h27
      omega
    · exact hZ
  have : IsSimpleGroup J := isSimpleGroup_J
  have hcen : Subgroup.center J = ⊥ :=
    Item434Spor.center_eq_bot_of_simple (by rw [card_J]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer J) := by
    have e' : NativeSporadic.Ly ≃* J := lyEquivJ
    have hq : Nat.card (Outer NativeSporadic.Ly) = Nat.card (Outer J) :=
      Item434SporLy.card_outer_congr_sub J (X := NativeSporadic.Ly) e'
    rw [← hq]
    have h' : Nat.card (Outer NativeSporadic.Ly) = 1 ∨ Nat.card (Outer NativeSporadic.Ly) = 2 :=
      CFSG.RankThree.PartOne.SPOR.card_outer_Ly
    rcases h' with h | h <;> rw [h] <;> norm_num
  have hgA : gA ∈ J := Subgroup.subset_closure (Set.mem_insert _ _)
  have hgB : gB ∈ J := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact (Item434SporE81.false_of_e27 hc e hcen hout
    (fun P hP hP27 => Item434SporLy.exists_e81_of_lyE81Check Item434SporLy.lyE81
      Item434SporLy.rp_A Item434SporLy.rp_B (J := J) hgA hgB Item434SporLy.factorization_J
      Certificates.certificate9520 hP hP27) hZ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
