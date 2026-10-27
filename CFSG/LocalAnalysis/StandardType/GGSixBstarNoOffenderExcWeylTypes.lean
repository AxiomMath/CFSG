module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylowE8Five
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace NoOffExc

local instance noOffExcFactThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

local instance noOffExcFactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance noOffExcFactSeven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem cartan_symm_E6 : ∀ i j : Fin Tag.E6.rank, Tag.E6.cartan i j = Tag.E6.cartan j i := by
  have h : ∀ i j : Fin 6, decide (Tag.cartanE 6 i j = Tag.cartanE 6 j i) = true := by decide
  exact fun i j => of_decide_eq_true (h i j)

theorem card_fix_eq_filter {τ : Tag} {p : ℕ} [NeZero p] (ω : List (Fin τ.rank)) :
    Nat.card {x : Fin τ.rank → ZMod p //
      TableBExc.torusAct τ p ((coxeterSystem τ).wordProd ω) x = x} =
    (Finset.univ.filter fun x : Fin τ.rank → ZMod p => rootWord τ p ω x = x).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  exact Finset.filter_congr fun x _ => by rw [rootWord_eq_torusAct]

theorem card_fix_rootWord_F4 : ∀ a b : Fin 3, (a, b) ≠ (0, 0) →
    (Finset.univ.filter fun x : Fin Tag.F4.rank → ZMod 3 =>
      rootWord .F4 3 (TableBF4.wordAB a b) x = x).card ≤ 9 := by
  decide +kernel

theorem card_fix_rootWord_F4_both : (Finset.univ.filter fun x : Fin Tag.F4.rank → ZMod 3 =>
    rootWord .F4 3 TableBF4.word1 x = x ∧ rootWord .F4 3 TableBF4.word2 x = x).card ≤ 3 := by
  decide +kernel

theorem sLevel_F4_three : ∀ A : Subgroup (WeylGroup .F4), A ≤ TableBF4.weylS →
    IsElemAbelian 3 A → A ≠ ⊥ →
    Nat.card A * Nat.card {x : Fin Tag.F4.rank → ZMod 3 //
      ∀ a ∈ A, TableBExc.torusAct .F4 3 a x = x} < 3 ^ Tag.F4.rank := by
  intro A hAS _ hA1
  have hfix1 : ∀ w ∈ TableBF4.weylS, w ≠ 1 →
      Nat.card {x : Fin Tag.F4.rank → ZMod 3 // TableBExc.torusAct .F4 3 w x = x} ≤ 9 := by
    intro w hw hw1
    obtain ⟨a, b, ha, hb, rfl⟩ := TableBF4.exists_eq_of_mem_weylS hw
    have hab : ((⟨a, ha⟩ : Fin 3), (⟨b, hb⟩ : Fin 3)) ≠ (0, 0) := by
      intro h
      apply hw1
      have h1 : a = 0 := congrArg Fin.val (Prod.ext_iff.mp h).1
      have h2 : b = 0 := congrArg Fin.val (Prod.ext_iff.mp h).2
      rw [h1, h2, pow_zero, pow_zero, one_mul]
    have h := card_fix_rootWord_F4 ⟨a, ha⟩ ⟨b, hb⟩ hab
    rw [← TableBF4.wordProd_wordAB, card_fix_eq_filter]
    exact h
  have hcardS : Nat.card TableBF4.weylS = 9 := TableBF4.card_weylS
  obtain ⟨⟨w, hwA⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hf := (card_fixAll_le hwA).trans (hfix1 w (hAS hwA) hw1')
  have hdvd : Nat.card A ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le hAS
    rwa [hcardS] at this
  obtain ⟨k, hk, hkA⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  by_cases h9 : k = 2
  · subst h9
    have hAeq : A = TableBF4.weylS :=
      Subgroup.eq_of_le_of_card_ge hAS (by rw [hkA, hcardS]; norm_num)
    have h3 : Nat.card {x : Fin Tag.F4.rank → ZMod 3 //
        ∀ a ∈ A, TableBExc.torusAct .F4 3 a x = x} ≤ 3 := by
      have h1 : TableBF4.weylW1 ∈ A := hAeq ▸ TableBF4.weylW1_mem_weylS
      have h2 : TableBF4.weylW2 ∈ A := hAeq ▸ TableBF4.weylW2_mem_weylS
      calc Nat.card {x : Fin Tag.F4.rank → ZMod 3 // ∀ a ∈ A, TableBExc.torusAct .F4 3 a x = x}
          ≤ Nat.card {x : Fin Tag.F4.rank → ZMod 3 //
              rootWord .F4 3 TableBF4.word1 x = x ∧ rootWord .F4 3 TableBF4.word2 x = x} := by
            refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_, ?_⟩) fun x y h =>
              Subtype.ext (by simpa using congrArg Subtype.val h)
            · rw [rootWord_eq_torusAct]
              exact x.2 _ h1
            · rw [rootWord_eq_torusAct]
              exact x.2 _ h2
        _ = (Finset.univ.filter fun x : Fin Tag.F4.rank → ZMod 3 =>
              rootWord .F4 3 TableBF4.word1 x = x ∧ rootWord .F4 3 TableBF4.word2 x = x).card := by
            rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        _ ≤ 3 := card_fix_rootWord_F4_both
    calc Nat.card A * Nat.card {x : Fin Tag.F4.rank → ZMod 3 //
          ∀ a ∈ A, TableBExc.torusAct .F4 3 a x = x}
        ≤ 3 ^ 2 * 3 := Nat.mul_le_mul hkA.le h3
      _ < 3 ^ Tag.F4.rank := by decide
  · have hk1 : k ≤ 1 := by omega
    have hA3 : Nat.card A ≤ 3 := by
      rw [hkA]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := by norm_num
    calc Nat.card A * Nat.card {x : Fin Tag.F4.rank → ZMod 3 //
          ∀ a ∈ A, TableBExc.torusAct .F4 3 a x = x}
        ≤ 3 * 9 := Nat.mul_le_mul hA3 hf
      _ < 3 ^ Tag.F4.rank := by decide

theorem sLevel_E8_five : ∀ A : Subgroup (WeylGroup .E8), A ≤ TableBExc.weylE8S →
    IsElemAbelian 5 A → A ≠ ⊥ →
    Nat.card A * Nat.card {x : Fin Tag.E8.rank → ZMod 5 //
      ∀ a ∈ A, TableBExc.torusAct .E8 5 a x = x} < 5 ^ Tag.E8.rank := by
  intro A hAS _ hA1
  have hcardS : Nat.card TableBExc.weylE8S = 25 := TableBExc.card_weylE8S
  have hle : Nat.card A ≤ 25 := hcardS ▸ Subgroup.card_le_of_le hAS
  obtain ⟨⟨s, hsA⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := TableBExc.exists_pow_eq_rep (hAS hsA) hs1'
  have hskA : s ^ k ∈ A := A.pow_mem hsA k
  have hfix : Nat.card {x : Fin Tag.E8.rank → ZMod 5 //
      TableBExc.torusAct .E8 5 (s ^ k) x = x} ≤ 5 ^ (8 - 3) := by
    rcases hk with hk | ⟨c, hc, hk⟩
    · rw [hk, TableBExc.weylE8B, card_fix_torusAct_eq TableBExc.Three.cartan_symm_E8]
      exact TableBExc.card_fix_wordE8B
    · rw [hk, ← TableBExc.wordProd_wordE8AB, card_fix_torusAct_eq TableBExc.Three.cartan_symm_E8]
      exact TableBExc.card_fix_wordE8AB hc
  calc Nat.card A * Nat.card {x : Fin Tag.E8.rank → ZMod 5 //
        ∀ a ∈ A, TableBExc.torusAct .E8 5 a x = x}
      ≤ 25 * 5 ^ (8 - 3) := Nat.mul_le_mul hle ((card_fixAll_le hskA).trans hfix)
    _ < 5 ^ Tag.E8.rank := by decide

section Final


theorem ggWeylNoOffender_F4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : GGWeylNoOffender .F4 p := by
  by_cases h3 : p = 3
  · subst h3
    refine ggWeylNoOffender_of_sylow Nat.prime_three (S := TableBF4.weylS) ?_ sLevel_F4_three
    rw [index_eq_of_card TableBF4.card_weylS CFSG.Monster.B.Geometry.card_f4WeylGroup
      (show 9 * 128 = 1152 by norm_num) (by norm_num)]
    norm_num
  · refine ggWeylNoOffender_of_not_dvd hp fun h => ?_
    rw [CFSG.Monster.B.Geometry.card_f4WeylGroup] at h
    rcases prime_eq_of_dvd_smooth hp (a := 7) (b := 2) (c := 0) (d := 0) (by norm_num; exact h)
      with rfl | rfl | rfl | rfl
    · exact hp2 rfl
    · exact h3 rfl
    · norm_num at h
    · norm_num at h

theorem ggWeylNoOffender_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    GGWeylNoOffender .E6 p := by
  by_cases h5 : p = 5
  · subst h5
    refine ggWeylNoOffender_of_sylow Nat.prime_five
      (S := Subgroup.zpowers ((coxeterSystem .E6).wordProd TableBExc.wordE6Five)) ?_
      (sLevel_cyclic Nat.prime_five TableBExc.orderOf_wordE6Five (k := 4) ?_ (by decide))
    · rw [index_eq_of_card (by rw [Nat.card_zpowers, TableBExc.orderOf_wordE6Five]) card_weyl_E6
        (show 5 * 10368 = 51840 by norm_num) (by norm_num)]
      norm_num
    · rw [card_fix_torusAct_eq cartan_symm_E6]
      exact TableBExc.card_fix_wordE6Five
  · refine ggWeylNoOffender_of_not_dvd hp fun h => ?_
    rw [card_weyl_E6] at h
    rcases prime_eq_of_dvd_smooth hp (a := 7) (b := 4) (c := 1) (d := 0) (by norm_num; exact h)
      with rfl | rfl | rfl | rfl
    · exact hp2 rfl
    · exact hp3 rfl
    · exact h5 rfl
    · norm_num at h

theorem ggWeylNoOffender_E7 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : GGWeylNoOffender .E7 p := by
  by_cases h3 : p = 3
  · subst h3
    refine ggWeylNoOffender_of_sylow Nat.prime_three (S := TableBExc.Three.modelHomE7.range) ?_
      fun A hAS hA hA1 => TableBExc.Three.noOffender_E7 A hAS hA hA1
    rw [index_eq_of_card TableBExc.Three.card_range_modelHomE7 card_weyl_E7
      (show 81 * 35840 = 2903040 by norm_num) (by norm_num)]
    norm_num
  by_cases h5 : p = 5
  · subst h5
    refine ggWeylNoOffender_of_sylow Nat.prime_five
      (S := Subgroup.zpowers ((coxeterSystem .E7).wordProd TableBExc.wordE7Five)) ?_
      (sLevel_cyclic Nat.prime_five TableBExc.orderOf_wordE7Five (k := 5) ?_ (by decide))
    · rw [index_eq_of_card (by rw [Nat.card_zpowers, TableBExc.orderOf_wordE7Five]) card_weyl_E7
        (show 5 * 580608 = 2903040 by norm_num) (by norm_num)]
      norm_num
    · rw [card_fix_torusAct_eq TableBExc.Three.cartan_symm_E7]
      exact TableBExc.card_fix_wordE7Five
  by_cases h7 : p = 7
  · subst h7
    refine ggWeylNoOffender_of_sylow (by norm_num)
      (S := Subgroup.zpowers ((coxeterSystem .E7).wordProd TableBExc.wordE7Seven)) ?_
      (sLevel_cyclic (by norm_num) TableBExc.orderOf_wordE7Seven (k := 5) ?_ (by decide))
    · rw [index_eq_of_card (by rw [Nat.card_zpowers, TableBExc.orderOf_wordE7Seven]) card_weyl_E7
        (show 7 * 414720 = 2903040 by norm_num) (by norm_num)]
      norm_num
    · rw [card_fix_torusAct_eq TableBExc.Three.cartan_symm_E7]
      exact TableBExc.card_fix_wordE7Seven
  refine ggWeylNoOffender_of_not_dvd hp fun h => ?_
  rw [card_weyl_E7] at h
  rcases prime_eq_of_dvd_smooth hp (a := 10) (b := 4) (c := 1) (d := 1) (by norm_num; exact h)
    with rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact h3 rfl
  · exact h5 rfl
  · exact h7 rfl

theorem ggWeylNoOffender_E8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : GGWeylNoOffender .E8 p := by
  by_cases h3 : p = 3
  · subst h3
    refine ggWeylNoOffender_of_sylow Nat.prime_three (S := TableBExc.Three.modelHomE8.range) ?_
      fun A hAS hA hA1 => TableBExc.Three.noOffender_E8 A hAS hA hA1
    rw [index_eq_of_card TableBExc.Three.card_range_modelHomE8 card_weyl_E8
      (show 243 * 2867200 = 696729600 by norm_num) (by norm_num)]
    norm_num
  by_cases h5 : p = 5
  · subst h5
    refine ggWeylNoOffender_of_sylow Nat.prime_five (S := TableBExc.weylE8S) ?_ sLevel_E8_five
    rw [index_eq_of_card TableBExc.card_weylE8S card_weyl_E8
      (show 25 * 27869184 = 696729600 by norm_num) (by norm_num)]
    norm_num
  by_cases h7 : p = 7
  · subst h7
    refine ggWeylNoOffender_of_sylow (by norm_num)
      (S := Subgroup.zpowers ((coxeterSystem .E8).wordProd TableBExc.wordE8Seven)) ?_
      (sLevel_cyclic (by norm_num) TableBExc.orderOf_wordE8Seven (k := 6) ?_ (by decide))
    · rw [index_eq_of_card (by rw [Nat.card_zpowers, TableBExc.orderOf_wordE8Seven]) card_weyl_E8
        (show 7 * 99532800 = 696729600 by norm_num) (by norm_num)]
      norm_num
    · rw [card_fix_torusAct_eq TableBExc.Three.cartan_symm_E8]
      exact TableBExc.card_fix_wordE8Seven
  refine ggWeylNoOffender_of_not_dvd hp fun h => ?_
  rw [card_weyl_E8] at h
  rcases prime_eq_of_dvd_smooth hp (a := 14) (b := 5) (c := 2) (d := 1) (by norm_num; exact h)
    with rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact h3 rfl
  · exact h5 rfl
  · exact h7 rfl

end Final

end NoOffExc

end CFSG.StandardType
