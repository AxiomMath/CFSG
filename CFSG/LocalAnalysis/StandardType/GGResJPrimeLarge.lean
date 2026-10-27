module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutElemRankCatalog
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviFive
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PartOne


theorem card_elemAbelian_aut_le_prime_of_not_dvd
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    [IsSimpleGroup (H ⧸ Subgroup.center H)]
    (hnab : ∃ a b : H ⧸ Subgroup.center H, a * b ≠ b * a)
    (hcat : CFSG.Open.IsCatalogGroup (H ⧸ Subgroup.center H))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpH : ¬ p ∣ Nat.card H)
    (A : Subgroup (MulAut H)) [IsElementaryAbelian p A] : Nat.card A ≤ p := by
  let q := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom H
  have hq : Function.Injective q :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective H
  have hnp : ¬ p ∣ Nat.card (H ⧸ Subgroup.center H) :=
    fun hd => hpH (hd.trans (Subgroup.card_quotient_dvd_card (Subgroup.center H)))
  have hEA : IsElementaryAbelian p (A.map q) :=
    IsElementaryAbelian.subgroup_map (inferInstance : IsElementaryAbelian p A) q
  have hsmall := CFSG.AGLEmbedding.OutElemRank.elementaryRankAtMostOne_of_catalogGroup hnab hcat hp hp2 hnp
  have hcard : Nat.card A = Nat.card (A.map q) :=
    Nat.card_congr (A.equivMapOfInjective q hq).toEquiv
  exact hcard.trans_le (hsmall (A.map q) hEA)

theorem GGResHyp.prime_dvd_card_J_of_five_le_card_bstar
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (h5 : p ^ 5 ≤ Nat.card Bs) : p ∣ Nat.card J := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hICopy := hH.1.1
  obtain ⟨hsimple, hnabG, hKP, -, -, hβ, hS, hst⟩ := hICopy
  letI : IsSimpleGroup G := hsimple
  have hcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hJq : CFSG.Open.IsQuasisimple J :=
    (CFSG.Assembly.isComponentOf_iff_open.mp hcomp).2.2
  letI : Group.IsPerfect J := ⟨hJq.1⟩
  letI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJq.2
  have hnab : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian J hJq
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hJproper : J ≠ ⊤ := by
    intro htop
    have hLtop : L = ⊤ := eq_top_iff.mpr (htop ▸ hJL)
    have hCtop : Subgroup.centralizer ({x} : Set G) = ⊤ := eq_top_iff.mpr (hLtop ▸ hLx)
    exact centralizer_singleton_ne_top_of_isSimpleGroup hnabG hS.2.2.1 hCtop
  have hcat : CFSG.Open.IsCatalogGroup (J ⧸ Subgroup.center J) :=
    CFSG.ComponentClassification.CatalogueKProper.simple_quotient_of_surjective G hKP J hJproper
      (J ⧸ Subgroup.center J) hnab (QuotientGroup.mk' (Subgroup.center J))
      (QuotientGroup.mk'_surjective (Subgroup.center J))
  let f := ggGamma J hH.Bs_le_normalizer_J
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hEA : CFSG.Open.IsElemAbelian p f.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a₀, ha⟩ := a.2
      obtain ⟨b₀, hb⟩ := b.2
      apply Subtype.ext
      change (a : MulAut J) * (b : MulAut J) = (b : MulAut J) * (a : MulAut J)
      rw [← ha, ← hb, ← map_mul, ← map_mul, hBs.1.is_comm.comm a₀ b₀]
    · intro a ha
      obtain ⟨b, rfl⟩ := ha
      rw [← map_pow, show b ^ p = 1 from Subtype.ext (hBs.2 _ b.2), map_one]
  letI : IsElementaryAbelian p f.range := hEA.isElementaryAbelian
  by_contra hnp
  have hAut : Nat.card f.range ≤ p := card_elemAbelian_aut_le_prime_of_not_dvd hnab hcat hp hp2 hnp f.range
  have hmul := NbrU63.card_range_ggGamma_mul_card_inf hH.Bs_le_normalizer_J
  have hC := hH.1.card_bstar_inf_centralizer_J_le
  have hsize : Nat.card Bs ≤ p ^ 4 := by
    calc Nat.card Bs = Nat.card f.range * Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := hmul.symm
      _ ≤ p * p ^ 3 := Nat.mul_le_mul hAut hC
      _ = p ^ 4 := by ring
  have hbad := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h5.trans hsize)
  omega

theorem GGResHyp.five_le_card_bstar_of_twE6_plus
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel (fun p lab => lab.tag = .twE6 ∧ 5 < p ∧ p ∣ 2 ^ lab.n + 1) p Bs K) :
    p ^ 5 ≤ Nat.card Bs := by
  have hp : p.Prime := Fact.out
  have hall : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      (lab.tag = .twE6 ∧ 5 < p ∧ p ∣ 2 ^ lab.n + 1) →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ _ _ => GGTorusLift p 5 R) := by
    intro lab hΛ hS
    refine nbrC_labelAll_guard ?_
    have h := largeEvenLabelAll_torusLift_twE6Add_holds hp hΛ ⟨hS.1, hS.2.2⟩
    rwa [TwE6Delta.liftRank_of_ne (by omega)] at h
  obtain ⟨hKc, lab, hΛ, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => lab.tag = .twE6 ∧ 5 < p ∧ p ∣ 2 ^ lab.n + 1)
    (P' := fun R _ _ _ => GGTorusLift p 5 R) hall
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨R, _, I, Fm, -, -, θ, ⟨-, hN, h3I⟩, hLift⟩ := largeEvenRawDatum_exists hraw
  have hr := pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hH.2.2.2.2.1 hKc θ hN hLift
  have hcard : Nat.card (ggGamma K hN).range ≤ Nat.card Bs :=
    Nat.card_le_card_of_surjective (ggGamma K hN).rangeRestrict (ggGamma K hN).rangeRestrict_surjective
  exact hr.trans hcard

theorem GGResHyp.J_le_K_of_twE6_plus
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel (fun p lab => lab.tag = .twE6 ∧ 5 < p ∧ p ∣ 2 ^ lab.n + 1) p Bs K) :
    J ≤ K := by
  have hpJ := hH.prime_dvd_card_J_of_five_le_card_bstar (hH.five_le_card_bstar_of_twE6_plus hmark)
  have hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier :=
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
  exact le_of_ggNbr (ggLBalanceInput_of_catalogueSchreier hSch) hH.1.1 hH.1.2.2 hpJ hH.2.2.2.2.1

end CFSG.StandardType

end
