module

public import CFSG.Quasithin.EmptyFaithful.LRed4IrrA
public import CFSG.Quasithin.EmptyFaithful.LRed4IrrB
public import CFSG.Quasithin.EmptyFaithful.Insp11Irr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def IrrFixShape : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H : Subgroup (MulAut V), commV H = ⊤ → B53Hyp H → IsInspList ↥H →
      quasithinGenFitting H ≠ H → fixV (quasithinGenFitting H) = fixV H

namespace LRed4

section CaseOne

variable {V : Type} [CommGroup V] [Finite V]

theorem case1ii_conclusion
    {H L : Subgroup (MulAut V)} (hI : IsInspList ↥H)
    (h : B51Case1ii H L) : Nonempty (↥H ≃* ↥(StatedSL 3 (ZMod 2))) := by
  obtain ⟨hHL, n, K, hKf, hKfin, hK, I, π, -, -, hreal, -, -⟩ := h
  have hπ := hreal 0
  have hLcard : Nat.card ↥L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) :=
    card_eq_of_nat_realizes1527d hπ
  have hHcard : Nat.card ↥H = Nat.card ↥L := by rw [hHL]
  obtain ⟨hmem, -, -⟩ := inspList_facts hI
  rw [hHcard, hLcard, card_statedSL_three1527d, hK] at hmem
  have hn1 : n = 1 := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · simp [inspOrders] at hmem
      · rfl
    · exfalso
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
      have h64 : 64 ≤ (2 ^ n) ^ 3 := by
        calc 64 = 4 ^ 3 := by norm_num
          _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h4 3
      have h16 : 16 ≤ (2 ^ n) ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h4 2
      have h1 : 15 ≤ (2 ^ n) ^ 2 - 1 := by omega
      have h2 : 63 ≤ (2 ^ n) ^ 3 - 1 := by omega
      have hbig : 64 * (15 * 63) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
        Nat.mul_le_mul h64 (Nat.mul_le_mul h1 h2)
      simp only [inspOrders, Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
  subst hn1
  have hbij : Function.Bijective π := ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩
  let e1 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) ≃* ↥L := MulEquiv.ofBijective π hbij
  let e2 := Insp9.statedSLEquivZMod2 K (by simpa using hK) 3
  exact ⟨(MulEquiv.subgroupCongr hHL).trans (e1.symm.trans e2)⟩

theorem case1iii_false
    {H L : Subgroup (MulAut V)} (hI : IsInspList ↥H) {n : ℕ}
    (h : B51Case1iii H L n) : False := by
  obtain ⟨hHL, hn, π, U₁, U₂, -, hreal, -⟩ := h
  have hLcard := card_eq_of_nat_realizes1527d hreal
  obtain ⟨hmem, -, -⟩ := inspList_facts hI
  rw [hHL, hLcard] at hmem
  rcases hn with rfl | rfl
  · rw [card_statedSL_four_zmod1527d] at hmem
    simp [inspOrders] at hmem
  · rw [card_statedSL_five_zmod1527d] at hmem
    simp [inspOrders] at hmem

theorem case1iv_false
    {H L : Subgroup (MulAut V)} (hI : IsInspList ↥H)
    (h : B51Case1iv H L) : False := by
  obtain ⟨hHL, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := h
  have hLcard := card_eq_of_nat_realizes1527d (hreal ⟨0, by omega⟩)
  obtain ⟨hmem, -, -⟩ := inspList_facts hI
  rw [hHL, hLcard] at hmem
  rcases hn with rfl | rfl
  · rw [card_statedSL_four_zmod1527d] at hmem
    simp [inspOrders] at hmem
  · rw [card_statedSL_five_zmod1527d] at hmem
    simp [inspOrders] at hmem

end CaseOne

theorem irrModShape_of_b56
    (h56 : AsB56) (hfix : IrrFixShape) : IrrModShape := by
  intro V _ _ hV H hH1 hB hcomm hI hnS3
  rcases h56 V hV H hH1 hB with h1 | h2 | h3 | h4 | h5
  · obtain ⟨-, ⟨⟨-, hcases⟩, -⟩, -⟩ := h1
    rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
    · left
      obtain ⟨hirr, -, hsyl⟩ := hi
      set L := quasithinGenFitting H with hL
      have hLH : L ≤ H := quasithinGenFitting_le H
      by_cases hHL : L = H
      · have hLtop : commV L = ⊤ := by rw [hHL]; exact hcomm
        have hsec := isIrrSec_of_mem_irrPlus hLtop hirr
        rw [hHL] at hsec
        exact fun U hU => irr_dichotomy hsec hU
      · obtain ⟨T, hT⟩ := exists_isSylowTwoOf H
        rcases hsyl T hT with hHL' | ⟨hHT, -⟩
        · exact absurd hHL'.symm hHL
        · have hTL : T ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
            hT.1.trans (le_normalizer_quasithinGenFitting H)
          have hc' : commV (L ⊔ T) = ⊤ := by rw [← hHT]; exact hcomm
          have hLtop : commV L = ⊤ := commV_eq_top_of_sup_two hV hT.2.1 hTL hc'
          have hfixLH : fixV L = fixV H := hfix V hV H hcomm hB hI hHL
          have hsec := isIrrSec_of_mem_irrPlus hLtop hirr
          intro U hU
          have hUL : XMod.IsInv ↥L U := fun a u hu => hU ⟨a, hLH a.2⟩ u hu
          have hd := irr_dichotomy hsec hUL
          rwa [hfixLH] at hd
    · exact Or.inr (case1ii_conclusion hI hii)
    · exact (case1iii_false hI hiii).elim
    · exact (case1iv_false hI hiv).elim
  · exact (hnS3 h2.1).elim
  · exact (not_case3 hI h3).elim
  · exact (not_case4 hI h4).elim
  · exact (not_case5 hI h5).elim


end LRed4

end CFSG.Quasithin
