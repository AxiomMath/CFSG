module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Kit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Local
public import CFSG.RankThree.PartOne.KS.Co3
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import Certificates.Certificate9456

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.Sporadic.Schreier.Co3 (co3P co3PermEquiv co3GenPerm_mem card_co3P co3ChainArrs)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Monster.B.Co2 Item434SporE81

namespace Item434SporCo3

theorem pg_get0 : co3E81.pg[0]! = co3ChainArrs[0]! := by simp [co3E81]

theorem pg_get1 : co3E81.pg[1]! = co3ChainArrs[1]! := by simp [co3E81]

theorem pg_size : co3E81.pg.size = 2 := by simp [co3E81]

theorem pg_mem : ∀ l < co3E81.pg.size, permOfArr co3E81.n co3E81.pg[l]! ∈ co3P := by
  intro l hl
  rw [pg_size] at hl
  have : l = 0 ∨ l = 1 := by omega
  rcases this with rfl | rfl
  · rw [pg_get0]
    exact co3GenPerm_mem 0 (by norm_num)
  · rw [pg_get1]
    exact co3GenPerm_mem 1 (by norm_num)

theorem qOrd_eq :
    co3E81.qOrd = 3 ^ (Nat.card co3P).factorization 3 := by
  have h : co3E81.qOrd = 3 ^ 7 := by simp [co3E81]
  rw [h, card_co3P, show (495766656000 : ℕ) = 3 ^ 7 * 226688000 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 7 (by norm_num)]

end Item434SporCo3

section Families


theorem item434Spor_Co3_27 :
    Item434Spor_Co3_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  have b₀ : NativeSporadic.Co3 ≃* Spor .Co3 := b
  have e : layer G ⧸ Subgroup.center (layer G) ≃* co3P :=
    e₀.trans (b₀.symm.trans co3PermEquiv)
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases hc.card_layerStar with h9 | ⟨-, hZ⟩
    · have : Nat.card hc.layerStar = 27 := h27
      omega
    · exact hZ
  have hcen : Subgroup.center co3P = ⊥ := CFSG.RankThree.PartOne.co3P_center
  have hout : ¬ 3 ∣ Nat.card (Outer co3P) := by
    rw [CFSG.RankThree.PartOne.card_outer_eq_one_of_allInner
      CFSG.RankThree.PartOne.co3P_allInner]
    norm_num
  exact (Item434SporE81.false_of_e27 hc e hcen hout
    (fun P hP hP27 => exists_e81_of_e81Check co3E81 Certificates.certificate9456
      Item434SporCo3.pg_mem Item434SporCo3.qOrd_eq hP hP27) hZ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
