module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType


theorem excTwE6_noTwo {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hM : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs (ggG0 3 B x L D J))
    (h4 : Nat.card Bs = 3 ^ 4) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSG : S ≤ ggG0 3 B x L D J) (hSN : Bs ≤ Subgroup.normalizer (S : Set G))
    (hSZ : ¬ S ≤ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) : False := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  set G0 : Subgroup G := ggG0 3 B x L D J with hG0
  have hlab0 : GGTableBTwE6ThreeLabel 3 (⟨.twE6, 0, 1⟩ : LargeEvenLabel) := by
    refine ⟨rfl, rfl, ?_⟩
    norm_num
  have hM1 : LargeEvenMarking G0 (fun lab R _ I F θ =>
      GGTableBTwE6ThreeLabel 3 lab ∧ Bs ≤ Subgroup.normalizer (G0 : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
    refine largeEvenMarking_mono ?_ hM
    rintro lab R _ I F θ ⟨hlab, hN, h3⟩
    exact ⟨by rw [hlab]; exact hlab0, hN, h3⟩
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel 3 lab)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ GGTwE6SCFourNotTwoLocal R I)
    (fun lab hlab hs => largeEvenLabelAll_twE6Three_of hlab hs
      (P := fun R _ I => GGTwE6SCFourNotTwoLocal R I)
      (fun K _ _ n hn hK hd => ggTwE6ThreeSCFourNotTwoLocalInput_holds K n hn hK hd))
    (fun _ _ _ _ _ _ hP => hP.1) hM1
  obtain ⟨R, _, I, F, -, -, θ, hP, hlift, hKG⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, hBsN, h3⟩ := hP
  have hAhyps : IsElemAbelian 3 (ggGamma G0 hBsN).range ∧
      (∀ a ∈ (ggGamma G0 hBsN).range, ∃ φ ∈ I, ∀ l : G0,
        φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      GGTorusSelfCent 3 (ggGamma G0 hBsN).range := by
    have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
    have hBp : ∀ b : Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
    have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
      Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
    refine ⟨isElemAbelian_range hBc hBp _, ?_,
      ggTorusSelfCent_ggGamma hBsN hcfg.2.1.2.2.2⟩
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta G0 θ hBsN b, ggBeta_mem G0 θ hBsN h3 b,
      fun l => ggBeta_ggQuotHom G0 hBsN θ b l⟩
  obtain ⟨hAE, hAI, hASC⟩ := hAhyps
  have h3n : ¬ 3 ∣ Nat.card (Subgroup.centralizer (G0 : Set G)) :=
    not_dvd_card_centralizer_ggG0_of_stdSub Nat.prime_three hcfg.1.2.2.2.2.2.2.1
      hcfg.1.2.2.2.2.2.2.2 hcfg.2.2
  have hTbot : Bs ⊓ Subgroup.centralizer (G0 : Set G) = ⊥ := by
    have hTp : IsPGroup 3 ↥(Bs ⊓ Subgroup.centralizer (G0 : Set G)) :=
      TableB.isPGroup_of_isElemAbelian
        (TableB.isElemAbelian_mono hcfg.2.1.2.1 inf_le_left)
    have hTdvd : Nat.card ↥(Bs ⊓ Subgroup.centralizer (G0 : Set G)) ∣
        Nat.card ↥(Subgroup.centralizer (G0 : Set G)) := by
      have h := Subgroup.card_subgroup_dvd_card
        ((Bs ⊓ Subgroup.centralizer (G0 : Set G)).subgroupOf
          (Subgroup.centralizer (G0 : Set G)))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases hTp.card_eq_or_dvd with h1 | h3dvd
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd (h3dvd.trans hTdvd) h3n
  have hA4 : Nat.card (ggGamma G0 hBsN).range = 3 ^ 4 := by
    have hmul := NbrU63.card_range_ggGamma_mul_card_inf (Bs := Bs) (K := G0) hBsN
    rwa [hTbot, Subgroup.card_bot, mul_one, h4] at hmul
  let V : Subgroup R := (S.subgroupOf G0).map (ggQuotHom θ)
  have hV2 : IsPGroup 2 V := (hS2.comap_subtype (K := G0)).map (ggQuotHom θ)
  have hV1 : V ≠ ⊥ := by
    intro hVbot
    apply hSZ
    intro s hs
    have hmem : ggQuotHom θ ⟨s, hSG hs⟩ ∈ V :=
      Subgroup.mem_map.mpr ⟨⟨s, hSG hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [hVbot] at hmem
    have h1 : ggQuotHom θ ⟨s, hSG hs⟩ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : (⟨s, hSG hs⟩ : G0) ∈ Subgroup.center G0 := by
      rw [← ker_ggQuotHom θ, MonoidHom.mem_ker]
      exact h1
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h2 ⟨g, hg⟩)
  have hVinv : ∀ a ∈ (ggGamma G0 hBsN).range, ∀ l : G0,
      ggQuotHom θ l ∈ V → ggQuotHom θ (a l) ∈ V := by
    rintro _ ⟨b, rfl⟩ l hl
    obtain ⟨s, hs, hψ⟩ := Subgroup.mem_map.mp hl
    have hconj : (b : G) * (s : G) * (b : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hSN b.2) (s : G)).mp
        (Subgroup.mem_subgroupOf.mp hs)
    have has : ggGamma G0 hBsN b s ∈ S.subgroupOf G0 := by
      rw [Subgroup.mem_subgroupOf, ggGamma_coe]
      exact hconj
    have hEq : ggQuotHom θ (ggGamma G0 hBsN b l) =
        ggQuotHom θ (ggGamma G0 hBsN b s) := by
      rw [← ggBeta_ggQuotHom G0 hBsN θ b l, ← ggBeta_ggQuotHom G0 hBsN θ b s, hψ]
    rw [hEq]
    exact Subgroup.mem_map.mpr ⟨ggGamma G0 hBsN b s, has, rfl⟩
  exact hKG G0 (ggQuotHom θ) (ggQuotHom_surjective θ) (le_of_eq (ker_ggQuotHom θ)) hL
    (ggGamma G0 hBsN).range hAE hAI hA4 hASC ⟨V, hV1, hV2, hVinv⟩

end CFSG.StandardType.GGQ2Frame.ExcPlacement
