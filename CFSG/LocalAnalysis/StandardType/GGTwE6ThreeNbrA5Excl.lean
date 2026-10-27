module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
public import CFSG.LocalAnalysis.StandardType.GGNbrTwE6Prop87
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentLLocal
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

variable {G : Type} [Group G] [Finite G]

theorem ggTwE6ThreeNbrCaseII_false_of_a5 (hA5 : GGTwE6A5LKnown)
    (hB : GGTwE6ThreeBstarRankInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hBeq : B = Bs) (hBs5 : Nat.card Bs = 3 ^ 5)
    (hm : LargeEvenTwoLocalRank 3 G = 5) (hJK : J ≤ K) {n : ℕ} (hn : 3 ∣ 2 ^ n + 1)
    (hMJ : LargeEvenMarking ↥(J.subgroupOf K) (fun lab _ _ _ _ _ => lab = ⟨.twA, 5, n⟩))
    (hnc : ¬ GGUnitaryCommLifts (J.subgroupOf K) n 6 (ggGamma K hN).range) : False := by
  classical
  subst Bs
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hst := hcfg.1.2.2.2.2.2.2.2
  have hBNL : B ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_largeEvenStandardType hst
  have hyB : y ∈ B := hnb.1.2.1
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hJ1 := isComponentOf_subgroupOf_ggFix_ggGamma_y hcfg hnb hBNL hyB
  have hMJL : LargeEvenMarking ↥(J.subgroupOf L) (fun lab _ _ _ _ _ => lab = ⟨.twA, 5, n⟩) :=
    largeEvenMarking_congr
      ((Subgroup.subgroupOfEquivOfLe hJL).trans (Subgroup.subgroupOfEquivOfLe hJK).symm)
      (fun _ _ _ _ _ _ h => h) hMJ
  let B' : Subgroup (MulAut ↥L) := (ggGamma L hBNL).range
  let s : MulAut ↥L := ggGamma L hBNL ⟨y, hyB⟩
  have hlocal := ggD4OddCent_lLocal hcfg.1 hcfg.2.2 hnb.2.1 hyB hBNL
  have hB'abel : IsElemAbelian 3 B' := by
    change IsElemAbelian 3 (ggAutsOf L B hBNL)
    exact hlocal.1
  have hsB' : s ∈ B' := ⟨⟨y, hyB⟩, rfl⟩
  have hs1 : s ≠ 1 := by
    change L.normalizerMonoidHom ⟨y, hBNL hyB⟩ ≠ 1
    exact hlocal.2.2.1
  have hB'card : 3 ^ 4 ≤ Nat.card B' := by
    change 3 ^ 4 ≤ Nat.card (ggAutsOf L B hBNL)
    have hcard := ggD4OddCent_card_lAuts hcfg.1 hBNL
    rw [hm] at hcard
    exact hcard.ge
  have hB'norm : ∀ a ∈ B', ∀ l ∈ J.subgroupOf L, a l ∈ J.subgroupOf L := hlocal.2.2.2.2
  obtain ⟨hperf, labL, hlabL, hrawL⟩ := hst.1
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, -, h3⟩, hP⟩ :=
    largeEvenRawDatum_exists (hA5 labL hlabL _ hrawL)
  have hB'ind : ∀ a ∈ B', ∃ φ ∈ I, ∀ l : ↥L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    intro a ha
    change a ∈ (ggGamma L hBNL).range at ha
    rcases ha with ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBNL b, ggBeta_mem L θ hBNL h3 b,
      fun l => ggBeta_ggQuotHom L hBNL θ b l⟩
  have hres := hP hs hna ↥L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hperf B' s n hB'abel hB'ind hsB' hs1 hB'card hn
    (J.subgroupOf L) hJ1 hB'norm hMJL
  rcases hres with hC | hrest
  · exact hnc (ggUnitaryCommLifts_ggGamma_of_le hN hBNL hJK hJL hC)
  · rcases hrest with ⟨htw, hd⟩ | hlift
    · have hLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 B L := by
        refine ⟨hperf, labL, hlabL, largeEvenRawDatum_mono ?_ hrawL⟩
        rintro R' _ I' F' ⟨hs', hna', θ', hsplit', hBN', h3'⟩
        exact ⟨hs', hna', θ', ⟨htw, rfl, hd⟩, hsplit', hBN', h3'⟩
      have h5 := hB G 3 B B x L D J hcfg hLab hBNL
      have hmul := card_ggAutsOf_mul_card hBNL
      change Nat.card (ggGamma L hBNL).range * _ = _ at hmul
      have hxL : x ∈ B ⊓ Subgroup.centralizer (L : Set G) :=
        ⟨hxB, Subgroup.mem_centralizer_iff.mpr fun l hl =>
          Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)⟩
      have hx2 : 2 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
        have h1 : 1 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
          rw [Subgroup.one_lt_card_iff_ne_bot]
          intro hbot
          rw [hbot] at hxL
          exact hx1 (Subgroup.mem_bot.mp hxL)
        omega
      have h6 : 3 ^ 5 * 2 ≤ 3 ^ 5 :=
        calc 3 ^ 5 * 2 ≤ Nat.card (ggGamma L hBNL).range *
              Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.mul_le_mul h5 hx2
          _ = Nat.card B := hmul
          _ ≤ 3 ^ 5 := le_of_eq hBs5
      norm_num at h6
    · have hx3 : x ^ 3 = 1 := hBs.2 x hxB
      have h5le := succ_le_twoLocalRank_of_torusLift Nat.prime_three hLx hx3 hx1 hperf θ hlift
      omega

end CFSG.StandardType

end
