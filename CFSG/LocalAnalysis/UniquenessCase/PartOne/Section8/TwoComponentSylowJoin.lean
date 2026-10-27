module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralProductExtraspecial
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.L34SylowExtraspecial
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UCK

theorem isExtraspecial_sup_of_two_SL3Four_sylow
    {Y : Type} [Group Y] [Finite Y] {A B P Q : Subgroup Y}
    (hA : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four ↥A)
    (hB : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four ↥B)
    (hne : A ≠ B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hZA : A ⊓ B ≤ (Subgroup.center ↥A).map A.subtype)
    (hZB : A ⊓ B ≤ (Subgroup.center ↥B).map B.subtype)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P A)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q B) :
    CFSG.IsExtraspecial 3 ↥(P ⊔ Q) ∧ Nat.card ↥(P ⊔ Q) = 3 ^ 5 ∧
      CFSG.Open.pRank 3 (P ⊔ Q) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hArank : CFSG.Open.pRank 3 A = 2 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := A)]
    exact pRank_three_eq_two_of_isSL3Four hA
  have hBrank : CFSG.Open.pRank 3 B = 2 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := B)]
    exact pRank_three_eq_two_of_isSL3Four hB
  have hne_bot : A ⊓ B ≠ ⊥ := by
    intro hbot
    obtain ⟨EA, hEA_le, hEA_el, hEA_card⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) A
    obtain ⟨EB, hEB_le, hEB_el, hEB_card⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) B
    have hEA9 : Nat.card EA = 9 := by
      rw [hEA_card, hArank]
      norm_num
    have hEB9 : Nat.card EB = 9 := by
      rw [hEB_card, hBrank]
      norm_num
    have hcommE : ∀ a ∈ EA, ∀ b ∈ EB, a * b = b * a :=
      fun a ha b hb => hcomm a (hEA_le ha) b (hEB_le hb)
    have hinfE : EA ⊓ EB = ⊥ := by
      apply le_antisymm _ bot_le
      calc EA ⊓ EB ≤ A ⊓ B := inf_le_inf hEA_le hEB_le
        _ = ⊥ := hbot
    have hEAsup_el : IsElemAbelian 3 (EA ⊔ EB) :=
      isElemAbelian_sup_of_commute hEA_el hEB_el hcommE
    have hEAsup_card : Nat.card ↥(EA ⊔ EB) = 81 := by
      have h := card_sup_mul_card_inf_of_commute hcommE
      rw [hinfE, Subgroup.card_bot, hEA9, hEB9] at h
      simpa using h
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
      CFSG.SectionRank.le_pRank (p := 3) (H := (⊤ : Subgroup Y)) (k := 4)
        (by norm_num) le_top hEAsup_el (by rw [hEAsup_card]; norm_num)
    omega
  have hZAmapcard : Nat.card ↥((Subgroup.center ↥A).map A.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hA.2]
  have hZBmapcard : Nat.card ↥((Subgroup.center ↥B).map B.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hB.2]
  have hinfcard : Nat.card ↥(A ⊓ B) = 3 := by
    have hdvd : Nat.card ↥(A ⊓ B) ∣ 3 := by
      rw [← hZAmapcard]
      exact Subgroup.card_dvd_of_le hZA
    have hne_one : Nat.card ↥(A ⊓ B) ≠ 1 := by
      intro hone
      exact hne_bot (Subgroup.eq_bot_of_card_eq (A ⊓ B) hone)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne_one
    · exact h
  have hZAg : A ⊓ B = (Subgroup.center ↥A).map A.subtype :=
    Subgroup.eq_of_le_of_card_ge hZA (by rw [hZAmapcard, hinfcard])
  have hZBg : A ⊓ B = (Subgroup.center ↥B).map B.subtype :=
    Subgroup.eq_of_le_of_card_ge hZB (by rw [hZBmapcard, hinfcard])
  have hPle : P ≤ A := hP.le
  have hQle : Q ≤ B := hQ.le
  have hP'sylow : CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf A)
      (⊤ : Subgroup ↥A) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
    refine ⟨le_top, ?_, ?_⟩
    · exact hS ▸ S.isPGroup'
    · rw [Subgroup.relIndex_top_right]
      exact hS ▸ S.not_dvd_index
  have hQ'sylow : CFSG.ABGLocalTools.IsSylowOf 3 (Q.subgroupOf B)
      (⊤ : Subgroup ↥B) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    obtain ⟨S, hS⟩ := hQ.exists_sylow_eq_subgroupOf
    refine ⟨le_top, ?_, ?_⟩
    · exact hS ▸ S.isPGroup'
    · rw [Subgroup.relIndex_top_right]
      exact hS ▸ S.not_dvd_index
  obtain ⟨hPext', hPcard'⟩ :=
    isExtraspecial_sylow_three_of_isSL3Four_of_certificates hA hP'sylow
  obtain ⟨hQext', hQcard'⟩ :=
    isExtraspecial_sylow_three_of_isSL3Four_of_certificates hB hQ'sylow
  have hPexp' : ∀ x : P.subgroupOf A, x ^ 3 = 1 :=
    pow_three_of_isSL3Four_sylow hA hP'sylow
  have hQexp' : ∀ x : Q.subgroupOf B, x ^ 3 = 1 :=
    pow_three_of_isSL3Four_sylow hB hQ'sylow
  have hPext : CFSG.IsExtraspecial 3 P := by
    haveI : CFSG.IsExtraspecial 3 (P.subgroupOf A) := hPext'
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPle).symm
  have hQext : CFSG.IsExtraspecial 3 Q := by
    haveI : CFSG.IsExtraspecial 3 (Q.subgroupOf B) := hQext'
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hQle).symm
  have hPcard : Nat.card P = 27 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv]
    exact hPcard'
  have hQcard : Nat.card Q = 27 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv]
    exact hQcard'
  have hPexp : ∀ x : P, x ^ 3 = 1 := by
    intro x
    have h := hPexp' ((Subgroup.subgroupOfEquivOfLe hPle).symm x)
    have h' := congrArg (Subgroup.subgroupOfEquivOfLe hPle) h
    simpa using h'
  have hQexp : ∀ x : Q, x ^ 3 = 1 := by
    intro x
    have h := hQexp' ((Subgroup.subgroupOfEquivOfLe hQle).symm x)
    have h' := congrArg (Subgroup.subgroupOfEquivOfLe hQle) h
    simpa using h'
  have hZP : (Subgroup.center ↥A).map A.subtype ≤ P := by
    obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
    have hZp : IsPGroup 3 (Subgroup.center ↥A) :=
      IsPGroup.of_card (n := 1) (by rw [hA.2]; norm_num)
    have hZS : Subgroup.center ↥A ≤ (S : Subgroup ↥A) :=
      IsPGroup.le_sylow_of_normal hZp S
    calc (Subgroup.center ↥A).map A.subtype
        ≤ (S : Subgroup ↥A).map A.subtype := Subgroup.map_mono hZS
      _ = P := by
          rw [hS, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPle]
  have hZQ : (Subgroup.center ↥B).map B.subtype ≤ Q := by
    obtain ⟨S, hS⟩ := hQ.exists_sylow_eq_subgroupOf
    have hZp : IsPGroup 3 (Subgroup.center ↥B) :=
      IsPGroup.of_card (n := 1) (by rw [hB.2]; norm_num)
    have hZS : Subgroup.center ↥B ≤ (S : Subgroup ↥B) :=
      IsPGroup.le_sylow_of_normal hZp S
    calc (Subgroup.center ↥B).map B.subtype
        ≤ (S : Subgroup ↥B).map B.subtype := Subgroup.map_mono hZS
      _ = Q := by
          rw [hS, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQle]
  have hPQ : P ⊓ Q = A ⊓ B := by
    apply le_antisymm
    · exact inf_le_inf hPle hQle
    · exact le_inf (by rw [hZAg]; exact hZP) (by rw [hZBg]; exact hZQ)
  have hZAP : (Subgroup.center ↥A).map A.subtype ≤
      (Subgroup.center ↥P).map P.subtype := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    have haP : (a : Y) ∈ P := hZP (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    refine Subgroup.mem_map.mpr ⟨⟨(a : Y), haP⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro p
    apply Subtype.ext
    have h := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp ha (⟨(p : Y), hPle p.2⟩ : ↥A))
    simpa using h
  have hZBQ : (Subgroup.center ↥B).map B.subtype ≤
      (Subgroup.center ↥Q).map Q.subtype := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
    have hbQ : (b : Y) ∈ Q := hZQ (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
    refine Subgroup.mem_map.mpr ⟨⟨(b : Y), hbQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    have h := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hb (⟨(q : Y), hQle q.2⟩ : ↥B))
    simpa using h
  have hZPmapcard : Nat.card ↥((Subgroup.center ↥P).map P.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hPext.center_order_p]
  have hZQmapcard : Nat.card ↥((Subgroup.center ↥Q).map Q.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hQext.center_order_p]
  have hZPmap : (Subgroup.center ↥P).map P.subtype =
      (Subgroup.center ↥A).map A.subtype :=
    (Subgroup.eq_of_le_of_card_ge hZAP (by rw [hZPmapcard, hZAmapcard])).symm
  have hZQmap : (Subgroup.center ↥Q).map Q.subtype =
      (Subgroup.center ↥B).map B.subtype :=
    (Subgroup.eq_of_le_of_card_ge hZBQ (by rw [hZQmapcard, hZBmapcard])).symm
  have hZPfinal : P ⊓ Q = (Subgroup.center ↥P).map P.subtype := by
    rw [hPQ, hZAg]
    exact hZPmap.symm
  have hZQfinal : P ⊓ Q = (Subgroup.center ↥Q).map Q.subtype := by
    rw [hPQ, hZBg]
    exact hZQmap.symm
  have hcommPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p :=
    fun p hp q hq => hcomm p (hPle hp) q (hQle hq)
  obtain ⟨hext, hcard⟩ :=
    isExtraspecial_sup_of_two_extraspecial_27 (A := P) (B := Q)
      hPext hQext hPcard hQcard hPexp hQexp hcommPQ hZPfinal hZQfinal
  refine ⟨hext, hcard, ?_⟩
  exact pRank_three_sup_of_two_extraspecial_27 (A := P) (B := Q)
    hPext hQext hPcard hQcard hPexp hQexp hcommPQ hZPfinal hZQfinal

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
