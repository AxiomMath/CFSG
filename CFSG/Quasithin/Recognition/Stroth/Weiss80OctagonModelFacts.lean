module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctLab
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSys
public import CFSG.Quasithin.Recognition.Stroth.Weiss80AssemblyFacts
public import CFSG.Quasithin.Recognition.Stroth.MoufangApartment
public import CFSG.GH74.GLS.SP.Local.SPLFaith
public import CFSG.GH74.GLS.SP.Local.SPLRestrict

public section

namespace CFSG.Quasithin.Stroth

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Quasithin.H13.F431.TwoF4
open CFSG.Geometry.GeneralizedPolygons
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.LocalAnalysis.EvenBN.TwoF4

set_option linter.unusedSectionVars false

variable {X : Type} [Group X]

private theorem card_conjBy (D : RankTwoSystem X 8) (m : D.N) (i : ℤ) :
    Nat.card (CFSG.GH74.BNPair.conjBy (m : X) (D.root i)) = Nat.card (D.root i) := by
  change Nat.card ((D.root i).map (MulAut.conj ((m : X)⁻¹)).toMonoidHom) =
    Nat.card (D.root i)
  rw [Subgroup.card_map_of_injective (MulAut.conj ((m : X)⁻¹)).injective]

private theorem card_eq_of_conj (D : RankTwoSystem X 8) (m : D.N) {i j : ℤ}
    (h : CFSG.GH74.BNPair.conjBy (m : X) (D.root i) = D.root j) :
    Nat.card (D.root i) = Nat.card (D.root j) := by
  rw [← card_conjBy D m i]
  exact congrArg (fun A : Subgroup X => Nat.card A) h

private theorem root_two_eq_eight (D : RankTwoSystem X 8) :
    Nat.card (D.root 2) = Nat.card (D.root 8) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective D.w₁
  have h := (D.roots.action₁ m hm).2.2 2 (by norm_num) (by norm_num)
  exact card_eq_of_conj D m h.1

private theorem root_four_eq_six (D : RankTwoSystem X 8) :
    Nat.card (D.root 4) = Nat.card (D.root 6) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective D.w₁
  have h := (D.roots.action₁ m hm).2.2 4 (by norm_num) (by norm_num)
  exact card_eq_of_conj D m h.1

private theorem root_three_eq_seven (D : RankTwoSystem X 8) :
    Nat.card (D.root 3) = Nat.card (D.root 7) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective D.w₁
  have h := (D.roots.action₁ m hm).2.2 3 (by norm_num) (by norm_num)
  exact card_eq_of_conj D m h.1

private theorem root_one_eq_seven (D : RankTwoSystem X 8) :
    Nat.card (D.root 1) = Nat.card (D.root 7) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective D.w₂
  have h := (D.roots.action₂ m hm).2.2 1 (by norm_num) (by norm_num)
  exact card_eq_of_conj D m h.1

private theorem root_three_eq_five (D : RankTwoSystem X 8) :
    Nat.card (D.root 3) = Nat.card (D.root 5) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective D.w₂
  have h := (D.roots.action₂ m hm).2.2 3 (by norm_num) (by norm_num)
  exact card_eq_of_conj D m h.1

private theorem root_two_eq_six (D : RankTwoSystem X 8) :
    Nat.card (D.root 2) = Nat.card (D.root 6) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective D.w₂
  have h := (D.roots.action₂ m hm).2.2 2 (by norm_num) (by norm_num)
  exact card_eq_of_conj D m h.1

theorem rankTwoSystem_root_odd_eq_one (D : RankTwoSystem X 8) {i : ℤ}
    (h1 : 1 ≤ i) (h8 : i ≤ 8) (hodd : Odd i) :
    Nat.card (D.root i) = Nat.card (D.root 1) := by
  obtain ⟨k, rfl⟩ := hodd
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · norm_num
  · exact (root_three_eq_seven D).trans (root_one_eq_seven D).symm
  · exact (root_three_eq_five D).symm.trans
      ((root_three_eq_seven D).trans (root_one_eq_seven D).symm)
  · exact (root_one_eq_seven D).symm

theorem rankTwoSystem_root_even_eq_eight (D : RankTwoSystem X 8) {i : ℤ}
    (h1 : 1 ≤ i) (h8 : i ≤ 8) (heven : Even i) :
    Nat.card (D.root i) = Nat.card (D.root 8) := by
  obtain ⟨k, rfl⟩ := heven
  have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · exact root_two_eq_eight D
  · exact (root_four_eq_six D).trans
      ((root_two_eq_six D).symm.trans (root_two_eq_eight D))
  · exact (root_two_eq_six D).symm.trans (root_two_eq_eight D)
  · norm_num

section CertificateScoped


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

private theorem card_subgroupOf_rootV (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    Nat.card ((rootV K a i).subgroupOf (F4.reeGamma K a)) = Nat.card (rootV K a i) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootV_le_reeGamma hK i)).toEquiv

variable (hK : Nat.card K = 2 ^ (2 * a + 1))
variable (hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a))
variable [IsSimpleGroup (Gm K a)]

theorem octSystemOf_root_one_card (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card ((octSystemOf hR).root 1) = (Nat.card K) ^ 2 := by
  rw [octSystemOf_root, octRoot_eq_rootV hK (by norm_num) (by norm_num),
    card_subgroupOf_rootV hK, card_rootV hK, hK]
  norm_num [octLab, Idx.isSz]

theorem octSystemOf_root_eight_card (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card ((octSystemOf hR).root 8) = Nat.card K := by
  rw [octSystemOf_root, octRoot_eq_rootV hK (by norm_num) (by norm_num),
    card_subgroupOf_rootV hK, card_rootV hK, hK]
  norm_num [octLab, Idx.isSz]

theorem octagon_orders_of_root_cards {m : ℕ} (hTits : Tits83Orders) (R : RankTwoSystem X 8)
    [Finite X] (hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a))
    [IsSimpleGroup (Gm K a)] (ha : 1 ≤ a) (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hroot1 : Nat.card (R.root 1) = 2 ^ (2 * (2 * a + 1)))
    (hroot8 : Nat.card (R.root 8) = 2 ^ m) :
    m = 2 * a + 1 ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ 8 →
        Nat.card (R.root i) = Nat.card ((octSystemOf hR).root i)) := by
  obtain ⟨f, hfodd, hpat⟩ := hTits X R
  rcases hpat with ⟨hodd, heven⟩ | ⟨heven, hodd⟩
  · have h1 : Nat.card (R.root 1) = 2 ^ f :=
      hodd 1 (by norm_num) (by norm_num) (by norm_num)
    have h8 : Nat.card (R.root 8) = 2 ^ (2 * f) := by
      simpa using heven 8 (by norm_num) (by norm_num) (by norm_num)
    have hpow : 2 ^ f = 2 ^ (2 * (2 * a + 1)) := by rw [← h1, hroot1]
    have hf : f = 2 * (2 * a + 1) :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
    obtain ⟨k, hk⟩ := hfodd
    omega
  · have h1 : Nat.card (R.root 1) = 2 ^ (2 * f) :=
      hodd 1 (by norm_num) (by norm_num) (by norm_num)
    have h8 : Nat.card (R.root 8) = 2 ^ f :=
      heven 8 (by norm_num) (by norm_num) (by norm_num)
    have hpow : 2 ^ (2 * f) = 2 ^ (2 * (2 * a + 1)) := by rw [← h1, hroot1]
    have hf2 : 2 * f = 2 * (2 * a + 1) :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
    have hf : f = 2 * a + 1 := by omega
    have hpowm : 2 ^ m = 2 ^ f := by rw [← hroot8, h8]
    have hm_f : m = f := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpowm
    have hm_eq : m = 2 * a + 1 := hm_f.trans hf
    refine ⟨hm_eq, ?_⟩
    intro i hi1 hi8
    by_cases hi_odd : Odd i
    · rw [rankTwoSystem_root_odd_eq_one R hi1 hi8 hi_odd, hroot1,
        rankTwoSystem_root_odd_eq_one (octSystemOf hR) hi1 hi8 hi_odd,
        octSystemOf_root_one_card (hR := hR) hK, hK]
      rw [← pow_mul]
      congr 1
      ring
    · have hi_even : Even i := Int.not_odd_iff_even.mp hi_odd
      rw [rankTwoSystem_root_even_eq_eight R hi1 hi8 hi_even, hroot8, hm_eq,
        rankTwoSystem_root_even_eq_eight (octSystemOf hR) hi1 hi8 hi_even,
        octSystemOf_root_eight_card (hR := hR) hK, hK]

theorem octSystemOf_card_U (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (octSystemOf hR).U = (Nat.card K) ^ 12 := by
  have hlist : intList 1 ((8 : ℕ) : ℤ) = [1, 2, 3, 4, 5, 6, 7, 8] := by decide
  rw [rankTwoSystem_card_U, hlist]
  norm_num
  rw [rankTwoSystem_root_odd_eq_one (octSystemOf hR) (i := 1) (by norm_num) (by norm_num)
      (by norm_num),
    rankTwoSystem_root_odd_eq_one (octSystemOf hR) (i := 3) (by norm_num) (by norm_num)
      (by norm_num),
    rankTwoSystem_root_odd_eq_one (octSystemOf hR) (i := 5) (by norm_num) (by norm_num)
      (by norm_num),
    rankTwoSystem_root_odd_eq_one (octSystemOf hR) (i := 7) (by norm_num) (by norm_num)
      (by norm_num),
    rankTwoSystem_root_even_eq_eight (octSystemOf hR) (i := 2) (by norm_num) (by norm_num)
      (by norm_num),
    rankTwoSystem_root_even_eq_eight (octSystemOf hR) (i := 4) (by norm_num) (by norm_num)
      (by norm_num),
    rankTwoSystem_root_even_eq_eight (octSystemOf hR) (i := 6) (by norm_num) (by norm_num)
      (by norm_num),
    rankTwoSystem_root_even_eq_eight (octSystemOf hR) (i := 8) (by norm_num) (by norm_num)
      (by norm_num),
    octSystemOf_root_one_card (hR := hR) hK,
    octSystemOf_root_eight_card (hR := hR) hK]
  ring

variable {D : Type} [Group D] {L : Subgroup D} {R : RankTwoSystem ↥L 8}

theorem octagon_rootSystem_card_U (hrootOrders : ∀ i : ℤ, 1 ≤ i → i ≤ 8 →
      Nat.card (R.root i) = Nat.card ((octSystemOf hR).root i)) :
    Nat.card R.U = Nat.card (octSystemOf hR).U := by
  rw [rankTwoSystem_card_U R, rankTwoSystem_card_U (octSystemOf hR)]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hrootOrders i (mem_intList_iff.mp hi).1 (mem_intList_iff.mp hi).2

end CertificateScoped

end CFSG.Quasithin.Stroth
