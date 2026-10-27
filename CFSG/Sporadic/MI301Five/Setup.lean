module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveHN

public section

namespace CFSG.Sporadic.MI301Five

open CFSG.Blueprint CFSG.Open CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271 Subgroup

variable {G : Type} [Group G]

structure FiveFrame (α d z : G) : Prop where
  orderOf_inv : orderOf α = 2
  orderOf_d : orderOf d = 5
  inverts : α * d * α⁻¹ = d⁻¹
  hn : Nonempty (↥(cent2 α d) ≃* NativeSporadic.HN)
  card_cent_d : Nat.card ↥(cent d) ≤ 5 * 273030912000000
  orderOf_z : orderOf z = 2
  mem_z : z ∈ cent2 α d
  twoB : IsTwoBCentralizer z
  card_z : Nat.card ↥(cent2 α d ⊓ cent z) = 3686400

theorem exists_fiveFrame
    (hE : MonsterExistenceStatement G)
    (h2B : ∀ t k : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder →
      orderOf k = 5 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        18432000)
    (hG5 : ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = twoBCentralizerOrder)
    {d : G} (hd : orderOf d = 5) (hinv : InvertedByTwoA d)
    (hcd : Nat.card ↥(cent d) ≤ 5 * 273030912000000) :
    ∃ α z : G, FiveFrame α d z := by
  obtain ⟨hfin, α, hα2, hαc, hαd, i, hi, hsh⟩ :=
    TabMFive.invertedByTwoA_data' hE Nat.prime_five (by norm_num) hd hinv
  haveI : Finite G := hfin
  have hHN : Nonempty (↥(cent2 α d) ≃* NativeSporadic.HN) := by
    fin_cases i <;> first | exact hsh | (exfalso; simp [suborbitClassOrder] at hi)
  obtain ⟨e⟩ := hHN
  have hHI : TabMFive.HNInvolutions (cent2 α d) := TabMFive.HNInvolutions.of_equiv e
  obtain ⟨A, hAc, hAs, hA8, hAH⟩ := hHI.exists_E8
  obtain ⟨u, huA, huo, huc⟩ := hG5 A hAc hAs hA8
  have huH : u ∈ cent2 α d := hAH huA
  have hu3 : Nat.card ↥(cent2 α d ⊓ cent u) = 3686400 := by
    rcases hHI.cases u huH huo with h | h
    · exfalso
      have h1 := TabMFive.mul_card_le_cent_inf Nat.prime_five (by norm_num) hd hαd inf_le_left
        inf_le_right huH
      have h2 := h2B u d huo huc hd (Subgroup.mem_centralizer_singleton_iff.1 huH.2)
      rw [h] at h1
      omega
    · exact h
  obtain ⟨-, a, z₀, -, -, -, hcls, -, hB, -⟩ := id hE
  have hαA : IsConj a α := by
    rcases hcls α hα2 with h | h
    · exact h
    · exfalso
      have h2 := (hB α h).2.2.2.2.1
      rw [hαc] at h2
      norm_num [twoBCentralizerOrder, monsterBabyOrder] at h2
  have hu2B : IsTwoBCentralizer u := by
    rcases hcls u huo with h | h
    · exfalso
      have h1 := TabMSeven.card_centralizer_eq_of_isConj (hαA.symm.trans h)
      rw [hαc, huc] at h1
      norm_num [twoBCentralizerOrder, monsterBabyOrder] at h1
    · exact hB u h
  exact ⟨α, u, hα2, hd, hαd, ⟨e⟩, hcd, huo, huH, hu2B, hu3⟩

end CFSG.Sporadic.MI301Five
