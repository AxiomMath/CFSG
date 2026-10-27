module

public import CFSG.RankThree.GF2n.Tim79aSec23Statements
public import CFSG.Timmesfeld.Transvection.QTwo
public import CFSG.RankThree.GF2n.Tim79aSec23NoSq
public import CFSG.RankThree.GF2n.Tim79aSec25

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {G : Type} [Group G]

namespace MinCex

theorem sec25Concl_of_bar {M V Q P H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
    (hS : Sec25Bar V H P) : Sec25Concl V H P := by
  refine ⟨fun g hgX hg => ?_, hc.xOf_sup_cPbar_eq_H hS.2, hc.isElemAbelian_wOf_sup_cPbar⟩
  have ha := hc.sec25a_of_bar hgX (hS.1 g hgX hg)
  exact ⟨ha, hc.sec25b_of_a hgX hg ha⟩

variable {M V Q P H : Subgroup G} [Finite G]

theorem rootClassZ_eq_of_card_two (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hq : qBar V H = 2) :
    {A : Subgroup (XbarZ V H) | ∃ d ∈ Dy V H,
      A = Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center (Xbar V H)) d)} =
      rootClassZ V H := by
  classical
  have h2 : Nat.card (barOf V H V) = 2 := hq
  obtain ⟨v, hv1, huniq⟩ := (Nat.card_eq_two_iff' (1 : barOf V H V)).1 h2
  set d₀ : Xbar V H := ⟨v.1, barOf_V_le V H v.2⟩ with hd₀
  have hd₀D : d₀ ∈ Dy V H := hc.barOf_V_subset_dbarOf v.2 (fun h => hv1 (Subtype.ext h))
  have hDy : Dy V H = {g | IsConj d₀ g} := by
    obtain ⟨d₁, hd₁⟩ := hd.isClass
    have h1 : IsConj d₁ d₀ := by
      rw [hd₁] at hd₀D
      exact hd₀D
    rw [hd₁]
    ext g
    exact ⟨fun hg => h1.symm.trans hg, fun hg => h1.trans hg⟩
  have hVy : Vy V H = Subgroup.zpowers d₀ := by
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 v.2))
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · have hxV : (x : Hbar V H) ∈ barOf V H V := Subgroup.mem_subgroupOf.1 hx
      have hne : (⟨(x : Hbar V H), hxV⟩ : barOf V H V) ≠ 1 := fun h => hx1 (by
        have h3 : (x : Hbar V H) = 1 := congrArg Subtype.val h
        exact Subtype.ext h3)
      have h4 := huniq _ hne
      have h5 : (x : Hbar V H) = v.1 := congrArg Subtype.val h4
      have hxd : x = d₀ := Subtype.ext h5
      rw [hxd]
      exact Subgroup.mem_zpowers d₀
  have hVZ : VZ V H = Subgroup.zpowers (projZ V H d₀) := by
    unfold VZ
    rw [hVy, MonoidHom.map_zpowers]
  have hconj : ∀ c : Xbar V H, conjSub (VZ V H) (projZ V H c) =
      Subgroup.zpowers (projZ V H (c * d₀ * c⁻¹)) := by
    intro c
    rw [hVZ, conjSub, MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, map_mul, map_inv]
  ext A
  constructor
  · rintro ⟨d, hdD, rfl⟩
    rw [hDy] at hdD
    obtain ⟨c, hcd⟩ := isConj_iff.1 hdD
    refine ⟨projZ V H c, ?_⟩
    rw [hconj, hcd]
    rfl
  · rintro ⟨x, rfl⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨c * d₀ * c⁻¹, ?_, ?_⟩
    · rw [hDy]
      exact isConj_iff.2 ⟨c, rfl⟩
    · exact (hconj c).trans rfl

theorem sec23_three_or_four_of_noSquare (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hns : ¬ MeetsSq V H)
    (hT : TransvectionHyp (XbarZ V H) {A | ∃ d ∈ Dy V H,
      A = Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center (Xbar V H)) d)}) :
    Sec23Three V H ∨ Sec23Four V H := by
  have hq : qBar V H = 2 := hc.card_barOf_V_eq_two_of_not_meetsSq hd hns
  obtain ⟨d₁, hd₁⟩ := hd.isClass
  have hdD : d₁ ∈ Dy V H := by
    rw [hd₁]
    exact IsConj.refl d₁
  have hd2 : orderOf d₁ = 2 := hd.root.1 d₁ hdD
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : d₁ ^ 2 = 1 := by
    have := pow_orderOf_eq_one d₁
    rwa [hd2] at this
  have hord : orderOf (QuotientGroup.mk' (Subgroup.center (Xbar V H)) d₁) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hsq, map_one]
    · exact fun h => hd.noncentral d₁ hdD ((QuotientGroup.eq_one_iff d₁).mp h)
  have hcard : Nat.card (Subgroup.zpowers
      (QuotientGroup.mk' (Subgroup.center (Xbar V H)) d₁)) = 2 := by
    rw [Nat.card_zpowers, hord]
  have hConc := transvectionConclusion_of_card_two hT ⟨d₁, hdD, rfl⟩ hcard
  rw [hc.rootClassZ_eq_of_card_two hd hq] at hConc
  rcases (transvectionConclusion_iff _ _ 1 le_rfl).1 hConc with hSp | hSU
  · exact Or.inl ⟨1, le_rfl, by rw [hq]; norm_num, hSp⟩
  · exact Or.inr ⟨1, le_rfl, by rw [hq]; norm_num, hSU⟩

end MinCex

theorem tim79aIdentBenderStatement_of_parts (h1 : Tim79aIdentL2SzStatement)
    (h2 : Tim79aIdentU3Statement) : Tim79aIdentBenderStatement := by
  intro G _ _ M V Q P H hs hms hdisc
  rcases hs.mc.toMinCex.tilde_isBender hs.data hs.degenerate hms hdisc with
    ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact h1 G M V Q P H hs hms hdisc (Or.inl ⟨n, hn, ⟨e⟩⟩)
  · exact h1 G M V Q P H hs hms hdisc (Or.inr ⟨n, hn, ⟨e⟩⟩)
  · exact h2 G M V Q P H hs hms hdisc ⟨n, hn, ⟨e⟩⟩

end CFSG.RankThree.GF2n.Tim79a
