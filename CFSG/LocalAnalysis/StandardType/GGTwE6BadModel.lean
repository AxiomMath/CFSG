module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelData
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem tm_innerDiagOnLab {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L) :
    GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs L := by
  refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hM
  obtain ⟨⟨ht, hp3, hpn⟩, hBN, hBI⟩ := hP
  refine ⟨⟨ht, hp3, hpn⟩, Or.inr (Or.inl ⟨?_, ?_, by rw [hp3]; exact hpn⟩), hBN, hBI⟩
  · rw [ht]; exact fun h => h
  · rw [ht]; decide

private theorem tm_labelAll_guard {lab : LargeEvenLabel} {P : LargeEvenRawCont}
    (h : LargeEvenLabelAll lab P) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard P) :=
  fun Q hQ => largeEvenRawDatum_mono
    (fun _ _ _ _ hp => ⟨hp.1, fun _ _ => hp.2⟩) (h Q hQ)

theorem ggTwE6Bad_model_of_rank
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G}
    (hX : GGInnerDiagOnLabel GGTwE6BadLabel p Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hr : 3 ^ 5 ≤ Nat.card (ggGamma X hN).range) :
    ∃ (Φ : ↥(ggGamma X hN).range →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup ↥X)
      (w : Fin 6 → ↥X), GGE6ThreeData (Subgroup.center ↥X) (ggGamma X hN).range Φ T w := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hM' : GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs X := tm_innerDiagOnLab hX
  obtain ⟨-, _, _, hraw⟩ := hX
  obtain ⟨_, _, _, _, _, _, _, hP, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, hp3, -⟩ := hP
  rw [hp3] at hp hBs hSC
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range :=
    (Nat.pow_le_pow_right (by norm_num) (by norm_num : 3 ≤ 5)).trans hr
  have hmod : ∀ (lab : LargeEvenLabel), LargeEvenInLambda2 lab → GGTableBTwE6ThreeLabel p lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        GGTorusLift 3 4 R ∧ GGE6ThreeModelSCr R I) := by
    intro lab hlab hbad
    exact tm_labelAll_guard (largeEvenLabelAll_twE6Three_of (p := p)
      (P := fun R _ I => GGE6ThreeModelSCr R I) hlab hbad
      (fun K _ _ n hn hK hd => E6ThreeModel.e6ThreeModel_holds.2 K n hn hK hd))
  have hmark := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGTableBTwE6ThreeLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ GGE6ThreeModelSCr R I)
    (fun lab hlab hs => hmod lab hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hM'
  have hXc : commutator ↥X = ⊤ := hmark.1
  obtain ⟨_, _, hraw2⟩ := hmark.2
  obtain ⟨_, _, I, _, -, -, θ, hP, hP'⟩ := largeEvenRawDatum_exists hraw2
  obtain ⟨-, -, -, h3I⟩ := hP
  obtain ⟨-, hmodel⟩ := hP'
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN h3I hb
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, -, hsc⟩ :=
    ggTorusTBGroup_of_marking (p := 3) (r := 5) hp hBs hSC hXc θ hN hBsI hr h3
  have hdata := (hmodel ↥X (ggQuotHom θ) hψ hker hperf (ggGamma X hN).range
    hAe hAI hr hsc).exists_data
  rwa [ker_ggQuotHom θ] at hdata

theorem ggTwE6Bad_model_of_config
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (Φ : ↥(ggGamma L hN).range →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup ↥L)
      (w : Fin 6 → ↥L), GGE6ThreeData (Subgroup.center ↥L) (ggGamma L hN).range Φ T w := by
  have hM' : GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs L := tm_innerDiagOnLab hL
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma L hN).range :=
    ggTwE6ThreeBstarRankInput_holds G p B Bs x L D J hcfg hM' hN
  exact ggTwE6Bad_model_of_rank hcfg hL hN hr


theorem ggTwE6Bad_model
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rest : Prop} (hHyp : GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧
      GGInnerDiagAll p B Bs x L D J ∧ GGNoTransvection p Bs ∧ Rest)
    (hL : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (Φ : ↥(ggGamma L hN).range →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup ↥L)
      (w : Fin 6 → ↥L), GGE6ThreeData (Subgroup.center ↥L) (ggGamma L hN).range Φ T w :=
  ggTwE6Bad_model_of_config hHyp.1 hL hN

end CFSG.StandardType

end
