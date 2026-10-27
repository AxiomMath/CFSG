module

public import CFSG.RankThree.PartTwo.Sec13.Item137ProofCore
public import CFSG.RankThree.PartTwo.KFacts.KS18M12
import CFSG.RankThree.PartTwo.Sec13.Item137ProofM12
import CFSG.RankThree.PartTwo.Sec13.Item137ProofHJ

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item137InvertPGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) →
        ∀ (P E F : Subgroup G) (t : G), Config137 A c L P E F t → HypS E ∨ HypT E →
          Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
            ∀ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E → K ∈ lA E e →
              e ∈ Subgroup.centralizer (P : Set G) → e ∉ Subgroup.zpowers c →
              Sec8.IsZ3PGLThreePi (lBarA e K E) →
                ∃ s ∈ K ⊓ Subgroup.normalizer (P : Set G), ∀ z ∈ ⁅P, P⁆, s * z * s⁻¹ = z⁻¹

theorem item137Invert_of (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hspor : SporadicModels131) (h414 : Sec4.Item4_14_local) (h415 : Sec4.Item4_15)
    (hK18 : KFacts.KS18M12) (hPGL : Item137InvertPGL) : Item137Invert := by
  intro G _ _ A c L h hM P E F t hcfg hST hU e K heΩ hK heZ hec htype
  rcases htype with hP | hM12 | hJ2
  · exact hPGL G A c L h hM P E F t hcfg hST hU e K heΩ hK heZ hec hP
  · exact exists_inverting_of_m12 h131 hspor h414 hK18 h hM hcfg hST heΩ hK heZ hM12
  · exfalso
    have hXE : E ∈ partTwoE G ∧ E ∉ partTwoT G := by
      rcases hST with hS | hT
      · exact ⟨hS.1, hS.2.1⟩
      · exact ⟨hT.1, hT.2.1⟩
    have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
    have hXF : E ∈ partTwoF G := hFE ▸ hXE.1
    obtain ⟨u, -, huE, hτ, -⟩ := exists_tau_of_config h131 hspor h hM hcfg
    exact false_of_lBarA_j2 h131 h134 h48 h415 hspor h hM hXF hXE.2 heΩ hK hec huE hτ hJ2

end CFSG.RankThree.PartTwo.Sec13
