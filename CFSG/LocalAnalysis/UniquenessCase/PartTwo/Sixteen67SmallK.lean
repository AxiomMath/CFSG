module

public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKOut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup

theorem isCatalogGroup_of_isKGroup_of_simple {J : Type} [Group J] (hJ : CFSG.Open.IsKGroup J)
    (hs : IsSimpleGroup J) (hnonab : ∃ a b : J, a * b ≠ b * a) : IsCatalogGroup J :=
  hJ.isCatalogGroup_of_surjective ⊤ hnonab (Subgroup.topEquiv (G := J)).toMonoidHom
    (Subgroup.topEquiv (G := J)).surjective

@[expose] def K67ThreeIndex : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (J : Subgroup Q), J.Normal →
    CFSG.Open.IsKGroup ↥J → IsSimpleGroup ↥J → (∃ a b : ↥J, a * b ≠ b * a) →
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) = 1 → centralizer (J : Set Q) = ⊥ →
    CFSG.Open.pRank 3 (⊤ : Subgroup Q) ≤ 1 → ¬ 3 ∣ J.index

theorem k67ThreeIndex_of_split
    (hsplit : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KFactSylowSplit) : K67ThreeIndex := by
  unfold K67ThreeIndex
  intro Q _ _ J hJ hK hs hnab hr1 hC hrQ h3
  haveI : J.Normal := hJ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcat : CFSG.Open.IsCatalogGroup ↥J := isCatalogGroup_of_isKGroup_of_simple hK hs hnab
  obtain ⟨t₀, -, ht₀⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank (p := 3) Nat.prime_three
      (H := (⊤ : Subgroup ↥J)) hr1.ge
  let t : Q := (t₀ : Q)
  have htJ : t ∈ J := t₀.2
  have ht3 : orderOf t = 3 := (Subgroup.orderOf_coe t₀).trans ht₀
  have hzp : IsPGroup 3 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht3]
    norm_num
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow hzp
  have htP : t ∈ (P : Subgroup Q) := hPle (Subgroup.mem_zpowers t)
  have hPJ : ¬ (P : Subgroup Q) ≤ J := by
    intro hle
    have hdvd : 3 ∣ (P : Subgroup Q).index := h3.trans (Subgroup.index_dvd_of_le hle)
    exact Sylow.not_dvd_index P hdvd
  obtain ⟨x, hxP, hxJ, hx3⟩ :=
    exists_orderOf_three_of_split hsplit J hcat hs hnab hr1.le hC P hPJ
  let N : Subgroup ↥P := J.subgroupOf (P : Subgroup Q)
  haveI hNnormal : N.Normal := hJ.subgroupOf (P : Subgroup Q)
  haveI hPnil : Group.IsNilpotent ↥P := IsPGroup.isNilpotent P.isPGroup'
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hmem : (⟨t, htP⟩ : ↥P) ∈ N := by
      change (⟨t, htP⟩ : ↥P) ∈ J.subgroupOf (P : Subgroup Q)
      rw [Subgroup.mem_subgroupOf]
      exact htJ
    rw [hbot] at hmem
    have h1 : (⟨t, htP⟩ : ↥P) = 1 := Subgroup.mem_bot.1 hmem
    have ht1 : t = 1 := congrArg Subtype.val h1
    have hc : (3 : ℕ) = 1 := by rw [← ht3, ht1, orderOf_one]
    exact absurd hc (by norm_num)
  let Z : Subgroup ↥P := N ⊓ Subgroup.center ↥P
  have hZne : Z ≠ ⊥ := by
    change N ⊓ Subgroup.center ↥P ≠ ⊥
    exact Group.IsNilpotent.inf_center_ne_bot_of_normal hNne
  have hZp : IsPGroup 3 ↥Z := P.isPGroup'.to_subgroup Z
  have hZcard : 3 ∣ Nat.card Z := by
    rcases hZp.card_eq_or_dvd with h1 | hd
    · exact absurd (Subgroup.eq_bot_of_card_eq Z h1) hZne
    · exact hd
  obtain ⟨y', hy'3⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 hZcard
  let yp : ↥P := (y' : ↥P)
  let y : Q := (yp : Q)
  have hypN : yp ∈ N := y'.2.1
  have hyP : y ∈ (P : Subgroup Q) := yp.2
  have hyJ : y ∈ J := by
    have h := hypN
    change yp ∈ J.subgroupOf (P : Subgroup Q) at h
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  have hy3 : orderOf y = 3 := by
    have h1 : orderOf y = orderOf yp := Subgroup.orderOf_coe yp
    have h2 : orderOf yp = orderOf y' := Subgroup.orderOf_coe y'
    exact h1.trans (h2.trans hy'3)
  have hycentral : ∀ g : Q, g ∈ (P : Subgroup Q) → g * y = y * g := by
    intro g hg
    have h := (Subgroup.mem_center_iff.mp y'.2.2) (⟨g, hg⟩ : ↥P)
    exact congrArg Subtype.val h
  have hxy : x * y = y * x := hycentral x hxP
  have hyzx : y ∉ Subgroup.zpowers x := by
    intro hy
    have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hy
    have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
    have hcardy : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hy3]
    have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardx, hcardy])
    have hxmem : x ∈ Subgroup.zpowers y := by
      rw [heq]
      exact Subgroup.mem_zpowers x
    exact hxJ ((Subgroup.zpowers_le.2 hyJ) hxmem)
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
  have hcomm : ∀ a ∈ Subgroup.zpowers x, a * y = y * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left hxy n).eq
  obtain ⟨hEa, hEcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
      (X := Subgroup.zpowers x) (v := y) hcardx hy3 hyzx hcomm
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) :=
    CFSG.SectionRank.le_pRank (p := 3) (G := Q) (H := ⊤)
      (E := Subgroup.zpowers x ⊔ Subgroup.zpowers y) (k := 2)
      (by norm_num) le_top hEa hEcard
  omega

@[expose] def K67BPrimeOne : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (J : Subgroup Q), J.Normal →
    CFSG.Open.IsKGroup ↥J → IsSimpleGroup ↥J → (∃ a b : ↥J, a * b ≠ b * a) →
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) = 1 → centralizer (J : Set Q) = ⊥ → ¬ 3 ∣ J.index →
    ∀ x : Q, x ∈ J → orderOf x = 3 → ∀ A : Subgroup Q, IsElemAbelian 2 A →
      A ≤ centralizer ({x} : Set Q) →
      (∀ t ∈ J ⊓ centralizer ({x} : Set Q), t ∈ normalizer (A : Set Q)) → 4 ≤ Nat.card A →
      CFSG.Blueprint.LieModel ↥J .PSL 2 5 2 ∧ A ⊓ J ≠ ⊥

@[expose] def K67CaseIII : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (J : Subgroup Q), J.Normal →
    CFSG.Open.IsKGroup ↥J → IsSimpleGroup ↥J → (∃ a b : ↥J, a * b ≠ b * a) →
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) = 1 → centralizer (J : Set Q) = ⊥ → ¬ 3 ∣ J.index →
    ∀ x : Q, x ∈ J → orderOf x = 3 → ∀ E : Subgroup Q, IsElemAbelian 2 E → Nat.card E = 4 →
      E ≤ J → E ⊓ centralizer ({x} : Set Q) = ⊥ →
      ∀ W : Subgroup Q, IsElemAbelian 2 W → W ≠ ⊥ → W ≤ centralizer ({x} : Set Q) →
        W ≤ centralizer (E : Set Q) →
        (∀ n : Q, n ∈ normalizer (Subgroup.zpowers x : Set Q) →
          n ∈ normalizer (E : Set Q) ∧ n ∈ normalizer (W : Set Q)) → False

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
