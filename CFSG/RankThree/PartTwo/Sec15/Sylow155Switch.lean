module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTools
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511

variable {G : Type} [Group G] [Finite G]

namespace Sylow155Switch

theorem not_isZ3PGLThreePi_of_meets {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {c' : G} {L' : Subgroup G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c')
    (h1511 : ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
      Sec4.IsoLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') p e →
      ∀ P : Subgroup G, A ≤ P → CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c' : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      Nonempty (lBarA c' L' A ≃* Multiplicative (ZMod 3) × Sec12.lBar c' L')) :
    ¬ Sec8.IsZ3PGLThreePi (lBarA c' L' A) := by
  intro hPGL
  have hD' := (sec15R_point h hc' hL').toSec13Data
  obtain ⟨⟨p, e, hp, he, hiso⟩, hZ, -⟩ := facts_of_isZ3PGLThreePi hD' hPGL
  have hc'L' : c' ∉ L' := not_mem_of_center_eq_bot hD' hZ
  obtain ⟨P, hAP, hP⟩ := Proof1513Steps.exists_sylow_normalizer_inf
    (Proof1513Steps.isPGroup_of_sec13Data h.toSec13Data) hD'.A_le_normalizer_zpowers hAY
  exact Proof1514.false_of_prod_of_isZ3PGLThreePi hD' hc'L' (h1511 p e he hiso P hAP hP) hPGL

theorem isEmpty_m12_of_meets (h137 : Item137) (hcl : Claim1515M12) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A)) {c' : G}
    {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c')
    (hm : MeetsY4 A (lB A) L' Y) :
    IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  refine ⟨fun ψ => ?_⟩
  have h' := sec15R_point h hc' hL'
  obtain ⟨X, hX4, hXLY⟩ := hm
  have hXL : X ≤ L' := hXLY.trans inf_le_left
  exact Proof1514.false_of_m12_of_le h' h137 ⟨ψ⟩ hY.2 (hXLY.trans inf_le_right) hXL hX4.1.2
    (Proof1514.not_dvd_relIndex_of_eq_sup_theta hXL (hcl G A c' L' h' ⟨ψ⟩ X hX4 hXL))

theorem exists_point_j2_or_good (h137 : Item137) (hcl : Claim1515M12) (h1511 : Item1511StarR)
    (hpt : Step1513MeetsPoint) {A L : Subgroup G} {c : G} (h : Sec15R G A c L) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) :
    (∃ (b : G) (Lb : Subgroup G), Sec15R G A b Lb ∧
        Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2)) ∨
      ∃ (b : G) (Lb : Subgroup G), Sec15R G A b Lb ∧ ¬ Sec8.IsZ3PGLThreePi (lBarA b Lb A) ∧
        IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  by_cases hJ : ∃ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A ∧ Lb ∈ lA A b ∧
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2)
  · obtain ⟨b, Lb, hb, hLb, hJb⟩ := hJ
    exact Or.inl ⟨b, Lb, sec15R_point h hb hLb, hJb⟩
  · have hno : ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
        IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) :=
      fun b Lb hb hLb => not_nonempty_iff.mp fun hJb => hJ ⟨b, Lb, hb, hLb, hJb⟩
    obtain ⟨c', L', hc', hL', hm⟩ := hpt G A c L h hno K hK.prop
    have h' := sec15R_point h hc' hL'
    refine Or.inr ⟨c', L', h', ?_, isEmpty_m12_of_meets h137 hcl h hK.prop hc' hL' hm⟩
    exact not_isZ3PGLThreePi_of_meets h hK.prop.1.1.2 hc' hL'
      fun p e _ he hiso P hAP hP => (h1511 G A c' L' h' p e he hiso K hK hm P hAP hP).1

end Sylow155Switch

end CFSG.RankThree.PartTwo.Sec15
