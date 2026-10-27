module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFResidue

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.Quasithin

variable {H : Type} [Group H] [Finite H]

theorem no_rankOne_component (hsq : CFSG.Open.SQTKTauCeti.StronglyQuasithin H)
    (hA : Input15338Rank1) (hlist : ∀ C : Subgroup H, IsComponent C →
      A23List (↥C ⧸ Subgroup.center ↥C))
    {B : Subgroup H} (hB : IsPOnePlusTwo 3 ↥B) {C : Subgroup H} (hC : IsComponent C)
    (h1 : CFSG.Open.pRank 3 C = 1) : False := by
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 2 := hsq 3 Nat.prime_three (by norm_num)
  by_cases hex : ∃ b ∈ B, b ∉ Subgroup.normalizer (C : Set H)
  · obtain ⟨b, hbB, hbN⟩ := hex
    have hb3 : b ^ 3 = 1 := by
      have := hB.2.2 ⟨b, hbB⟩
      simpa using congrArg Subtype.val this
    obtain ⟨a, haC, ha3, hnc⟩ := exists_noncentral_order_three hC.1 h1
    have : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) := three_le_pRank_of_moved hC hb3 hbN haC ha3 hnc
    omega
  · have hN : B ≤ Subgroup.normalizer (C : Set H) := fun b hb => by
      by_contra hbN
      exact hex ⟨b, hb, hbN⟩
    have h3 := hA H C B hC.1 (hlist C hC) h1 hN hB
    have h4 : CFSG.Open.pRank 3 (C ⊔ B) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) :=
      CFSG.SectionRank.pRank_mono (by norm_num) le_top
    omega

theorem sqtkGroup_subgroup {X : Type} [Group X] [Finite X] (hX : SQTKGroup X) (Y : Subgroup X) :
    SQTKGroup ↥Y := by
  refine ⟨fun p hp hp2 => ?_, CFSG.SectionRank.IsKGroupCat.subgroup hX.2 Y⟩
  have : Fact p.Prime := ⟨hp⟩
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥Y) = CFSG.Open.pRank p Y := pRank_top_subtype Y
  have h2 : CFSG.Open.pRank p Y ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_mono hp.one_lt le_top
  exact (h1.le.trans h2).trans (hX.1 p hp hp2)

theorem card_le_three_of_le_center (hZ : Input15338CenterRank)
    {C : Subgroup H} (hC : IsQuasisimple ↥C) (hCs : SQTKGroup ↥C)
    {F : Subgroup H} (hFC : F ≤ C) (hFc : F ≤ Subgroup.centralizer (C : Set H))
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : Nat.card F ≤ 3 := by
  have hF' : F.subgroupOf C ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hFc hx) c c.2))
  have hel : CFSG.Assembly.IsElemAbelian 3 (F.subgroupOf C) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥F => (w : H)) (hF.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
    · apply Subtype.ext
      simpa using hF.2 (x : H) hx
  have := hZ ↥C hC hCs (F.subgroupOf C) hF' hel
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv] at this

theorem False_of_two_rankTwo (hsqtk : SQTKGroup H) (hZ : Input15338CenterRank)
    {C C' : Subgroup H} (hC : IsComponent C) (hC' : IsComponent C') (hne : C ≠ C')
    (h2 : CFSG.Open.pRank 3 C = 2) (h2' : CFSG.Open.pRank 3 C' = 2) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 2 := hsqtk.1 3 Nat.prime_three (by norm_num)
  have hcomm : ∀ x ∈ C', ∀ y ∈ C, x * y = y * x := by
    rcases distinct_components_commute hC' hC with h | h
    · exact absurd h.symm hne
    · intro x hx y hy
      exact (Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) hx) y hy).symm
  obtain ⟨E, hEC, hEel, hEcard⟩ := CFSG.RankThree.PartTwo.Sec5.exists_elemAbelian_le_of_le_pRank
    Nat.prime_three (show 2 ≤ CFSG.Assembly.pRank 3 C from h2.ge)
  obtain ⟨E', hEC', hEel', hEcard'⟩ := CFSG.RankThree.PartTwo.Sec5.exists_elemAbelian_le_of_le_pRank
    Nat.prime_three (show 2 ≤ CFSG.Assembly.pRank 3 C' from h2'.ge)
  obtain ⟨x, hxE', hxE⟩ : ∃ x ∈ E', x ∉ E := by
    by_contra hcon
    push Not at hcon
    have hle : E' ≤ E := hcon
    have hbig := card_le_three_of_le_center hZ hC.1 (sqtkGroup_subgroup hsqtk C) (F := E')
      (hle.trans hEC) (fun x hx y hy => (hcomm x (hEC' hx) y hy).symm) hEel'
    rw [hEcard'] at hbig
    norm_num at hbig
  have hx3 : x ^ 3 = 1 := hEel'.2 x hxE'
  have hxC' : x ∈ C' := hEC' hxE'
  obtain ⟨hel, hcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hEel hxE hx3
    (fun e he => (hcomm x hxC' e (hEC he)).symm)
  have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) :=
    CFSG.RankThree.PartTwo.Sec5.le_pRank_of_elemAbelian Nat.prime_three
      (le_top : E ⊔ Subgroup.zpowers x ≤ ⊤) hel (k := 3) (by rw [hcard, hEcard]; norm_num)
  omega

end CFSG.Quasithin.SBd19F
