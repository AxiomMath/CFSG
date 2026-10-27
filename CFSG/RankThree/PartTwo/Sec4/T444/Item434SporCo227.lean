module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Kit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Local
public import CFSG.RankThree.PartOne.KS.Co2
public import CFSG.Sporadic.Co2Schreier.Model
public import Certificates.Certificate9457

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.Sporadic.Co2Cert (co2P co2PermEquiv co2Gen co2OrigArrs card_co2P)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Monster.B.Co2 Item434SporE81

namespace Item434SporCo2

theorem pg_get0 : co2E81.pg[0]! = co2OrigArrs[0]! := by simp [co2E81]

theorem pg_get1 : co2E81.pg[1]! = co2OrigArrs[1]! := by simp [co2E81]

theorem pg_size : co2E81.pg.size = 2 := by simp [co2E81]

theorem pg_mem : ∀ l < co2E81.pg.size, permOfArr co2E81.n co2E81.pg[l]! ∈ co2P := by
  intro l hl
  rw [pg_size] at hl
  have : l = 0 ∨ l = 1 := by omega
  rcases this with rfl | rfl
  · rw [pg_get0]
    exact (Subgroup.subset_closure (Set.mem_insert _ _) : co2Gen 0 ∈ co2P)
  · rw [pg_get1]
    exact (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl) : co2Gen 1 ∈ co2P)

theorem qOrd_eq :
    co2E81.qOrd = 3 ^ (Nat.card co2P).factorization 3 := by
  have h : co2E81.qOrd = 3 ^ 6 := by simp [co2E81]
  rw [h, card_co2P, show (42305421312000 : ℕ) = 3 ^ 6 * 58032128000 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 6 (by norm_num)]

theorem not_three_dvd_outer :
    ¬ 3 ∣ Nat.card (Outer co2P) := by
  obtain ⟨hfin, hp, -⟩ := CFSG.Sporadic.Co2Schreier.AT_Co2_model_Schreier co2P co2PermEquiv.symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  rw [hk]
  intro h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end Item434SporCo2

section Families


theorem item434Spor_Co2_27 :
    Item434Spor_Co2_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have b₀ : NativeSporadic.Co2 ≃* Spor .Co2 := b
  have e : layer G ⧸ Subgroup.center (layer G) ≃* co2P :=
    e₀.trans (b₀.symm.trans co2PermEquiv)
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases hc.card_layerStar with h9 | ⟨-, hZ⟩
    · have : Nat.card hc.layerStar = 27 := h27
      omega
    · exact hZ
  have hcen : Subgroup.center co2P = ⊥ := CFSG.RankThree.PartOne.co2P_center
  exact (Item434SporE81.false_of_e27 hc e hcen Item434SporCo2.not_three_dvd_outer
    (fun P hP hP27 => exists_e81_of_e81Check co2E81 Certificates.certificate9457
      Item434SporCo2.pg_mem Item434SporCo2.qOrd_eq hP hP27) hZ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
