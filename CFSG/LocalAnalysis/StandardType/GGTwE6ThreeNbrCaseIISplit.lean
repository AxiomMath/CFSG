module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLSplitDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrCaseIIDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrSCFourData
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrA5Excl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

theorem ggTwE6ThreeNbrCaseII_false_of_outsideSplit {G : Type} [Group G] [Finite G]
    (hOut : GGTwE6OfOutsideSplitKnown) (hB : GGTwE6ThreeBstarRankInput) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hBeq : B = Bs)
    (hBs5 : Nat.card Bs = 3 ^ 5) (hm : LargeEvenTwoLocalRank 3 G = 5) (hJK : J ≤ K) {n : ℕ}
    (hn : 3 ∣ 2 ^ n + 1)
    (hMJ : LargeEvenMarking ↥(J.subgroupOf K) (fun lab _ _ _ _ _ =>
      lab = ⟨.D, 4, n⟩ ∨ lab = ⟨.triD4, 0, n⟩ ∨ lab = ⟨.A, 2, 3 * n⟩ ∨ lab = ⟨.twA, 2, 3 * n⟩))
    (b : Bs) (hout : GGOutsideInndiag (J.subgroupOf K) (ggGamma K hN b)) : False := by
  classical
  subst Bs
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hst := hcfg.1.2.2.2.2.2.2.2
  have hBNL : B ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_largeEvenStandardType hst
  have hyB : y ∈ B := hnb.1.2.1
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hBp : ∀ c : B, c ^ 3 = 1 := fun c => Subtype.ext (by simpa using hBs.2 c c.2)
  have hBc : ∀ c d : B, c * d = d * c := fun c d =>
    Subtype.ext (CFSG.Open.IsElemAbelian.comm hBs c.2 d.2)
  have hJ1 := isComponentOf_subgroupOf_ggFix_ggGamma_y hcfg hnb hBNL hyB
  have hMJL : LargeEvenMarking ↥(J.subgroupOf L) (fun lab _ _ _ _ _ =>
      lab = ⟨.D, 4, n⟩ ∨ lab = ⟨.triD4, 0, n⟩ ∨ lab = ⟨.A, 2, 3 * n⟩ ∨
        lab = ⟨.twA, 2, 3 * n⟩) :=
    largeEvenMarking_congr
      ((Subgroup.subgroupOfEquivOfLe hJL).trans (Subgroup.subgroupOfEquivOfLe hJK).symm)
      (fun _ _ _ _ _ _ h => h) hMJ
  have hOutL := ggOutsideInndiag_ggGamma_of_le hN hBNL hJK hJL b hout
  obtain ⟨hperf, labL, hlabL, hrawL⟩ := hst.1
  obtain ⟨-, -, -, -, -, -, -, hsplit, -⟩ := largeEvenRawDatum_exists hrawL
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, -, h3⟩, hP⟩ :=
    largeEvenRawDatum_exists (hOut labL hlabL hsplit _ hrawL)
  have hres := hP hs hna ↥L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hperf (ggGamma L hBNL ⟨y, hyB⟩) (ggGamma L hBNL b) n
    (by rw [← map_pow, hBp, map_one]) (by rw [← map_pow, hBp, map_one])
    (by rw [← map_mul, ← map_mul, hBc ⟨y, hyB⟩ b])
    ⟨ggBeta L θ hBNL ⟨y, hyB⟩, ggBeta_mem L θ hBNL h3 _,
      fun l => ggBeta_ggQuotHom L hBNL θ _ l⟩
    ⟨ggBeta L θ hBNL b, ggBeta_mem L θ hBNL h3 b, fun l => ggBeta_ggQuotHom L hBNL θ b l⟩
    hn _ hJ1 hMJL hOutL
  rcases hres with ⟨htw, hd⟩ | hlift
  ·
    have hLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 B L := by
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
        intro h
        rw [h] at hxL
        exact hx1 (Subgroup.mem_bot.mp hxL)
      omega
    have h6 : 3 ^ 5 * 2 ≤ 3 ^ 5 :=
      calc 3 ^ 5 * 2 ≤ Nat.card (ggGamma L hBNL).range *
            Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.mul_le_mul h5 hx2
        _ = Nat.card B := hmul
        _ = 3 ^ 5 := hBs5
    norm_num at h6
  ·
    have hx3 : x ^ 3 = 1 := hBs.2 x hxB
    have hle := succ_le_twoLocalRank_of_torusLift Nat.prime_three hLx hx3 hx1 hperf θ hlift
    omega

theorem ggTwE6ThreeNbrCaseII_of_knownSplit (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hK1 : GGTwE6SCFourLabelsKnown) (hKO : GGTwE6SCFourOutKnown) (hKA : GGTwE6A5KKnown)
    (hLO : GGTwE6OfOutsideSplitKnown) (hLA : GGTwE6A5LKnown) (hB : GGTwE6ThreeBstarRankInput) :
    GGTwE6ThreeNbrCaseII := by
  intro G _ _ B Bs x L D J hcfg y K hnb hLab hN hsc hBeq hBs5 hm h4 hC
  obtain ⟨hK, lab, hlab, hraw⟩ := hLab
  obtain ⟨_, _, _, _, _, _, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hbad : GGTwE6BadLabel 3 lab := hP₀.1
  have hAll := largeEvenLabelAll_and (largeEvenLabelAll_and
    (hK1 lab hlab hbad.1 hbad.2.2) (hKO lab hlab hbad.1 hbad.2.2))
    (hKA lab hlab hbad.1 hbad.2.2)
  obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, hP⟩, ⟨⟨hk1, hko⟩, hka⟩⟩⟩ :=
    largeEvenRawDatum_exists (hAll _ hraw)
  obtain ⟨hJK, hset⟩ :=
    ggTwE6SCFourSetting_of_caseII hL hPJ hcfg hnb hN hsc hBeq h4 θ hP.2.2.2
  have hM := hk1 hs hna K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hK (ggGamma K hN).range (ggGamma K hN ⟨x, hcfg.tableB_facts.2.2.1⟩)
    (J.subgroupOf K) hset
  rcases largeEvenMarking_label_or hM with hM4 | hM5
  · obtain ⟨a, ha, hout⟩ := hko hs hna K (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hK (ggGamma K hN).range
      (ggGamma K hN ⟨x, hcfg.tableB_facts.2.2.1⟩) (J.subgroupOf K) hset hM4
    obtain ⟨b, rfl⟩ := ha
    exact ggTwE6ThreeNbrCaseII_false_of_outsideSplit hLO hB hcfg hnb hN hBeq hBs5 hm hJK
      hbad.2.2 hM4 b hout
  · exact ggTwE6ThreeNbrCaseII_false_of_a5 hLA hB hcfg hnb hN hBeq hBs5 hm hJK hbad.2.2
      hM5 (hka hs hna K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
        hK (ggGamma K hN).range (ggGamma K hN ⟨x, hcfg.tableB_facts.2.2.1⟩)
        (J.subgroupOf K) hset hM5)

end CFSG.StandardType

end
