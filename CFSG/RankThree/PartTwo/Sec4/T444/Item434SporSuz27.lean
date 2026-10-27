module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Kit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Local
public import CFSG.Sporadic.SuzOddCore.Outer
public import Certificates.Certificate9458

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.Sporadic.SuzOddCore (suzM suzB0 suzB1 b0Arr b1Arr rep_b0 rep_b1 suzM_isSimpleGroup
  suzM_card suzEquivM outer_carrier_suz)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Monster.B.Co2 CFSG.RankThree.Native Item434SporE81

namespace Item434SporSuz

theorem pg_get0 : suzE81.pg[0]! = b0Arr := by simp [suzE81]

theorem pg_get1 : suzE81.pg[1]! = b1Arr := by simp [suzE81]

theorem pg_size : suzE81.pg.size = 2 := by simp [suzE81]

theorem pg_mem :
    ∀ l < suzE81.pg.size, permOfArr suzE81.n suzE81.pg[l]! ∈ suzM := by
  intro l hl
  rw [pg_size] at hl
  have : l = 0 ∨ l = 1 := by omega
  rcases this with rfl | rfl
  · rw [pg_get0]
    exact (permOfArr_eq_of_rep rep_b0).symm ▸
      (Subgroup.subset_closure (Set.mem_insert _ _) : suzB0 ∈ suzM)
  · rw [pg_get1]
    exact (permOfArr_eq_of_rep rep_b1).symm ▸
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl) : suzB1 ∈ suzM)

theorem qOrd_eq :
    suzE81.qOrd = 3 ^ (Nat.card suzM).factorization 3 := by
  have h : suzE81.qOrd = 3 ^ 7 := by simp [suzE81]
  rw [h, suzM_card, show (448345497600 : ℕ) = 3 ^ 7 * 205004800 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 7 (by norm_num)]

end Item434SporSuz

section Families


theorem item434Spor_Suz_27 :
    Item434Spor_Suz_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have b₀ : NativeSporadic.Suz ≃* Spor .Suz := b
  have e : layer G ⧸ Subgroup.center (layer G) ≃* suzM :=
    e₀.trans (b₀.symm.trans suzEquivM)
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases hc.card_layerStar with h9 | ⟨-, hZ⟩
    · have : Nat.card hc.layerStar = 27 := h27
      omega
    · exact hZ
  have : IsSimpleGroup suzM := suzM_isSimpleGroup
  have hcen : Subgroup.center suzM = ⊥ :=
    Item434Spor.center_eq_bot_of_simple (by rw [suzM_card]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer suzM) := by
    have e' : NativeSporadic.Carrier .Suz ≃* suzM := suzEquivM
    rw [← Nat.card_congr (equivalence e').toEquiv, outer_carrier_suz.1]
    norm_num
  exact (Item434SporE81.false_of_e27 hc e hcen hout
    (fun P hP hP27 => exists_e81_of_e81Check suzE81 Certificates.certificate9458
      Item434SporSuz.pg_mem Item434SporSuz.qOrd_eq hP hP27) hZ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
