module

public import CFSG.RankThree.GF2n.Tim81.Sec6.RootRankOne
public import CFSG.RankThree.GF2n.Tim81.Sec6.RootRecog
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Setup
import CFSG.RankThree.GF2n.Tim81.Sec6.RootRigid
import CFSG.RankThree.GF2n.Tim81.Sec6.S61Rec

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

private theorem pow_two_mul_sub_three_ne (q n : ℕ) (hq : 4 ≤ q) (hn : 4 ≤ n) :
    q ^ (2 * n - 3) ≠ q := by
  intro h
  have hexp : 2 * n - 3 = 1 :=
    Nat.pow_right_injective (a := q) (lt_of_lt_of_le (by norm_num : 1 < 4) hq)
      (h.trans (pow_one q).symm)
  have hn8 : 8 ≤ 2 * n := Nat.mul_le_mul_left 2 hn
  omega

private theorem two_mul_pow_three_lt {q n : ℕ} (hq : 4 ≤ q) (hn : 4 ≤ n) :
    2 * q ^ 3 < q ^ (2 * n - 3) := by
  have hqpos : 0 < q := by omega
  have hn8 : 8 ≤ 2 * n := Nat.mul_le_mul_left 2 hn
  have hexp : 5 ≤ 2 * n - 3 := by omega
  have h5 : q ^ 5 ≤ q ^ (2 * n - 3) := Nat.pow_le_pow_right hqpos hexp
  have h16 : 16 ≤ q ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hlt : 2 * q ^ 3 < q ^ 2 * q ^ 3 :=
    Nat.mul_lt_mul_of_pos_right (by omega : 2 < q ^ 2) (pow_pos hqpos 3)
  have h5eq : q ^ 2 * q ^ 3 = q ^ 5 := by rw [← pow_add]
  rw [h5eq] at hlt
  exact hlt.trans_le h5

private theorem lOf_facts (hS : Sec6Hyp M V) {f n : ℕ} (hV : Nat.card V = 2 ^ f)
    (hR : RootSetup (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f)
    (hn : Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1)) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    IsPGroup 2 (imgQ M (lOf M V g)) ∧
      imgQ M (conjSubgroup g V) ≤ imgQ M (lOf M V g) ∧
      imgQ M (lOf M V g) ≤ cenOf (imgQ M (conjSubgroup g V)) ∧
      imgQ M (m0Of M V) ⊓ Subgroup.normalizer (imgQ M (conjSubgroup g V) : Set (MBar M)) ≤
        Subgroup.normalizer (imgQ M (lOf M V g) : Set (MBar M)) ∧
      imgQ M (lOf M V g) ⊓ cenOf (imgQ M (lOf M V g)) ≤ imgQ M (conjSubgroup g V) ∧
      imgQ M (lOf M V g) ⊓ cenOf (imgQ M (m0Of M V)) = ⊥ ∧
      Nat.card (imgQ M (lOf M V g)) = (2 ^ f) ^ (2 * n - 3) := by
  have hT : imgQ M (conjSubgroup g V) ∈ imgQ M '' sigmaSet M V := ⟨_, hg, rfl⟩
  have hP : IsPGroup 2 (imgQ M (lOf M V g)) := isPGroup_imgQ_lOf g
  have hTL : imgQ M (conjSubgroup g V) ≤ imgQ M (lOf M V g) :=
    hS.sec5.imgQ_le_imgQ_lOf hg
  have hLT : imgQ M (lOf M V g) ≤ cenOf (imgQ M (conjSubgroup g V)) :=
    imgQ_lOf_le_cenOf M V g
  have hNL : imgQ M (m0Of M V) ⊓
      Subgroup.normalizer (imgQ M (conjSubgroup g V) : Set (MBar M)) ≤
        Subgroup.normalizer (imgQ M (lOf M V g) : Set (MBar M)) :=
    inf_le_right.trans (hS.normalizer_imgQ_le hg)
  have hZ : imgQ M (lOf M V g) ⊓ cenOf (imgQ M (lOf M V g)) ≤
      imgQ M (conjSubgroup g V) := (hS.center_imgQ_lOf hg).le
  have hbot : imgQ M (lOf M V g) ⊓ cenOf (imgQ M (m0Of M V)) = ⊥ :=
    hR.inf_cenOf_eq_bot hT hP hZ
  have hcard : Nat.card (imgQ M (lOf M V g)) = Nat.card V ^ (2 * n - 3) :=
    hS.card_imgQ_lOf hn hg
  exact ⟨hP, hTL, hLT, hNL, hZ, hbot, by rw [hcard, hV]⟩

private theorem exists_suImage
    (hS : Sec6Hyp M V) {f : ℕ} (hf2 : 2 ≤ f)
    (hV : Nat.card V = 2 ^ f)
    (hT : Timmesfeld.Transvection.SubgroupTransvectionStatement)
    (hB : Timmesfeld.Bridge.OddTranspBender) (hPts : Tim90Points)
    {n : ℕ} (hn : Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1)) (h4 : 4 ≤ n) :
    IsSUImage (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f n (by omega) (by omega) := by
  have hR : RootSetup (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f := hS.rootSetup hf2 hV
  have hone : 1 ≤ f := by omega
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨A, hA⟩ := hS.ne
  obtain ⟨g, rfl, hH⟩ := hA
  have hg : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hH⟩
  have hTmem : imgQ M (conjSubgroup g V) ∈ imgQ M '' sigmaSet M V := ⟨_, hg, rfl⟩
  obtain ⟨hP, hTL, hLT, hNL, hZ, hbot, hcard⟩ := lOf_facts hS hV hR hn hg
  have hlarge : 2 * (2 ^ f) ^ 3 < Nat.card (imgQ M (lOf M V g)) := by
    rw [hcard]
    exact two_mul_pow_three_lt hq4 h4
  obtain ⟨B, hBmem, C, hCmem, hBC, hcomm⟩ :=
    hR.exists_commuting_of_large hB hTmem hP hLT hbot hlarge
  rcases hR.recog hT hPts ⟨B, hBmem, C, hCmem, hBC, hcomm⟩ with
    ⟨m, hm4, hSU⟩ | ⟨m, hm2, hSp⟩
  · have hrig := hR.rigid_su hone hm4 hSU hTmem hP hTL hLT hNL hbot
    rcases hrig with hEq | ⟨-, hcardR⟩
    · exact absurd (by rw [← hcard, hEq, hR.card _ hTmem])
        (pow_two_mul_sub_three_ne (2 ^ f) n hq4 h4)
    · have hmn : m = n := by
        have hexp : 2 * m - 3 = 2 * n - 3 :=
          Nat.pow_right_injective (a := 2 ^ f) (by omega) (hcardR.symm.trans hcard)
        omega
      subst m
      exact hSU
  · have hEq := hR.rigid_sp hone hm2 hSp hTmem hP hTL hLT hNL hbot hZ
    exact absurd (by rw [← hcard, hEq, hR.card _ hTmem])
      (pow_two_mul_sub_three_ne (2 ^ f) n hq4 h4)

theorem Sec6Hyp.exists_sec7Hyp
    (hS : Sec6Hyp M V)
    (hT : Timmesfeld.Transvection.SubgroupTransvectionStatement)
    (hB : Timmesfeld.Bridge.OddTranspBender) (hPts : Tim90Points)
    {n : ℕ} (hn : Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1)) (h4 : 4 ≤ n) :
    ∃ f, Sec7Hyp M V n f := by
  obtain ⟨f, hf2, hV⟩ := hS.exists_card_V
  refine ⟨f, ?_⟩
  have hone : 1 ≤ f := by omega
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hm0 := exists_suImage hS hf2 hV hT hB hPts hn h4
  have hR : RootSetup (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f := hS.rootSetup hf2 hV
  refine ⟨hS, h4, hone, hV, hn, hm0, ?_⟩
  intro g hg
  have hTmem : imgQ M (conjSubgroup g V) ∈ imgQ M '' sigmaSet M V := ⟨_, hg, rfl⟩
  obtain ⟨hP, hTL, hLT, hNL, hZ, hbot, hcard⟩ := lOf_facts hS hV hR hn hg
  have hrig := hR.rigid_su hone h4 hm0 hTmem hP hTL hLT hNL hbot
  rcases hrig with hEq | ⟨hLR, -⟩
  · exact absurd (by rw [← hcard, hEq, hR.card _ hTmem])
      (pow_two_mul_sub_three_ne (2 ^ f) n hq4 h4)
  · exact hLR

end CFSG.RankThree.GF2n.Tim81
