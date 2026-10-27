module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeTwoLocalCover
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB


theorem le_centralizer_of_isPGroup_two_twE6Three {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L)
    {U : Subgroup G} (hU2 : IsPGroup 2 U) (hUL : U ≤ L)
    (hBsU : Bs ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ Subgroup.centralizer (L : Set G) := by
  let P : ∀ (R : Type) [Group R], Set (MulAut R) → Prop := fun R _ I =>
    ∀ (Y : Type) [Group Y] [Finite Y] (ψ : Y →* R) (A : Subgroup (MulAut Y)),
      GGTorusTBGroup 3 5 R I Y ψ A → ∀ V : Subgroup Y, IsPGroup 2 V →
        (∀ a ∈ A, ∀ v ∈ V, a v ∈ V) → V ≤ ψ.ker
  obtain ⟨hLc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel 3 lab)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ P R I)
    (fun lab hlab hs => largeEvenLabelAll_twE6Three_of hlab hs
      (P := fun R _ I => P R I)
      (fun K _ _ n hn hK hd Y _ _ ψ A hTB V hV hAV =>
        TwE6ThreeRootGen.le_ker_of_isPGroup_two_recipe hn hK hd hTB hV hAV))
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨R, _, I, F, -, -, θ, hP, -, hNoTwo⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, hN, hInd⟩ := hP
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have h5 : 3 ^ 5 ≤ Nat.card (ggGamma L hN).range :=
    ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg hmark hN
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma L hN).range := (by norm_num : 3 ^ 3 ≤ 3 ^ 5).trans h5
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hN hInd hb
  have hTB := ggTorusTBGroup_of_marking (p := 3) (r := 5) hp hBs hSC hLc θ hN hBsI h5 h3
  have hnorm : ∀ a ∈ (ggGamma L hN).range, ∀ u ∈ U.subgroupOf L,
      a u ∈ U.subgroupOf L := by
    rintro _ ⟨b, rfl⟩ u hu
    change ((ggGamma L hN b u : L) : G) ∈ U
    rw [ggGamma_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hBsU b.2) (u : G)).1 hu
  have hker : U.subgroupOf L ≤ (ggQuotHom θ).ker :=
    hNoTwo L (ggQuotHom θ) (ggGamma L hN).range hTB (U.subgroupOf L)
      (hU2.comap_subtype (K := L)) hnorm
  rw [ker_ggQuotHom] at hker
  intro u hu
  refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
  have hc : (⟨u, hUL hu⟩ : L) ∈ Subgroup.center L := hker hu
  exact congrArg (fun y : L => (y : G))
    ((Subgroup.mem_center_iff.mp hc) ⟨l, hl⟩)

theorem le_centralizer_of_isPGroup_two_of_twE6Two_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L)
    {U : Subgroup G} (hU2 : IsPGroup 2 U) (hUL : U ≤ L)
    (hBsU : Bs ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  obtain ⟨lab, -, -, -, -, -, -, -, ⟨⟨-, hdvd⟩, hn⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hp3 : p = 3 := by
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  have hM : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L := by
    refine largeEvenMarking_mono ?_ hmark
    rintro lab R _ I F θ ⟨⟨⟨ht, hpn⟩, -⟩, hN, hBI⟩
    refine ⟨⟨ht, rfl, hpn⟩, Or.inr (Or.inl ⟨?_, ?_, hpn⟩), hN, hBI⟩
    · rw [ht]; exact fun h => h
    · rw [ht]; decide
  exact le_centralizer_of_isPGroup_two_twE6Three hcfg hM hU2 hUL hBsU

end CFSG.StandardType

end
