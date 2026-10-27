module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB1AAA
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.KGroups.L27
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_H5_row_L3_three_cent_seven_triv {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    ∀ g ∈ autSub (A ⊓ normalizer (L : Set (MulAut W))) (commSub ⊤ L),
      g ∈ Subgroup.centralizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) →
      g ^ 7 = 1 → g = 1 := by
  intro g hg hgc hg7
  by_cases hn : ∀ u : ↥(commSub ⊤ L), g u * u⁻¹ ∈ fixV (autSub L (commSub ⊤ L))
  · obtain ⟨-, -, -, -, -, -, hfaith⟩ := s16h_L3_res_algebra hc h.1
    exact hfaith g hg hn
  · exact (hn (s16h_H5_row_L3_three_central_seven_triv hc h hZ hd2 g hg hgc hg7)).elim

theorem s16h_H5_row_L3_three_seven_rank {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    ∀ E : Subgroup (MulAut W), E ≤ A ⊓ normalizer (L : Set (MulAut W)) →
      IsElemAbelian 7 E → Nat.card ↥(autSub E (commSub ⊤ L)) ≤ 7 := by
  intro E hE hEab
  have hEAN : autSub E (commSub ⊤ L) ≤
      autSub (A ⊓ normalizer (L : Set (MulAut W))) (commSub ⊤ L) :=
    autSub_mono hE (commSub ⊤ L)
  obtain ⟨-, -, hnorm, -, hsl3, -, -⟩ := s16h_L3_res_algebra hc h.1
  have hN : autSub E (commSub ⊤ L) ≤
      Subgroup.normalizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) :=
    le_trans hEAN hnorm
  let φ : autSub E (commSub ⊤ L) →* MulAut ↥(autSub L (commSub ⊤ L)) :=
    (Subgroup.normalizerMonoidHom (autSub L (commSub ⊤ L))).comp
      (Subgroup.inclusion hN)
  have hEab' : IsElemAbelian 7 (autSub E (commSub ⊤ L)) := by
    have h1 := IsElemAbelian.map (hEab.subgroupOf (stabSub (commSub ⊤ L)))
      (resHom (commSub ⊤ L))
    simpa [autSub] using h1
  have hker : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxker : (Subgroup.inclusion hN x) ∈
        (Subgroup.normalizerMonoidHom (autSub L (commSub ⊤ L))).ker := by
      rw [MonoidHom.mem_ker]
      simpa [φ] using MonoidHom.mem_ker.mp hx
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hxker
    have hxc : (x : MulAut ↥(commSub ⊤ L)) ∈
        Subgroup.centralizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) := by
      simpa using hxker
    have hx7 : (x : MulAut ↥(commSub ⊤ L)) ^ 7 = 1 := hEab'.2 x x.2
    exact Subtype.ext (by
      simpa using s16h_H5_row_L3_three_cent_seven_triv hc h hZ hd2
        (x : MulAut ↥(commSub ⊤ L)) (hEAN x.2) hxc hx7)
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have hM : Nat.card (MulAut ↥(autSub L (commSub ⊤ L))) ∣ 336 :=
    card_mulAut_dvd_of_isL3 (s16k_isLn_of_isSLn (by norm_num) hsl3)
  have hcardEq : Nat.card (autSub E (commSub ⊤ L)) = Nat.card ↥(φ.range) :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hdvd : Nat.card (autSub E (commSub ⊤ L)) ∣ 336 := by
    rw [hcardEq]
    exact (Subgroup.card_subgroup_dvd_card φ.range).trans hM
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 7)).mp hEab'.isPGroup
  have hm1 : m ≤ 1 := by
    have h7m : 7 ^ m ∣ 336 := by rw [← hm]; exact hdvd
    by_contra hlt
    have h2 : 2 ≤ m := by omega
    have h49 : (7 : ℕ) ^ 2 ∣ 336 := dvd_trans (pow_dvd_pow 7 h2) h7m
    norm_num at h49
  rw [hm]
  calc (7 : ℕ) ^ m ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
    _ = 7 := pow_one 7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
