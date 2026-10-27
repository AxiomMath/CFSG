module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4SetupLayer
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.LocalAnalysis.UniquenessCase.UC22


theorem r891D4Setup_d4ShortSL2 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    R891D4Setup n (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
      (centralizer ((CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  have h3 : ¬ 3 ∣ 2 ^ n := by
    intro h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    rw [CFSG.LieType.Chevalley.ringEquiv_pow_three_apply]
    simpa using CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hσ c
  refine ⟨hn, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨CFSG.LieType.Chevalley.orbitField TwistTag.D4 K σ.toRingHom
        CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer, inferInstance, inferInstance,
      ?_, ?_⟩
    · rw [CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.natCard_orbitField_d4Outer hσ3, hK]
    · obtain ⟨e⟩ :=
        CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2
          (K := K) (σ := σ) hσ3
      exact ⟨e.symm⟩
  ·
    obtain ⟨F, hFfield, hFfin, -, hFcard, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar.nonempty_mulEquiv_centralizer_d4ShortSL2
        (K := K) (σ := σ) (ℓ := 2) (f := n) hn (by norm_num) hK hσ
    exact ⟨F, hFfield, hFfin, hFcard, ⟨e.symm⟩⟩
  ·
    exact CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_D4_two hn hK σ.toRingHom hσ
  ·
    intro z hz3 hz1
    exact CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeConj_holds K (2 ^ n) σ hK hσ h3
      z hz3 hz1
  ·
    intro t ht ht3 ht1 a ha b hb
    exact (((CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeBCent_holds K (2 ^ n) σ hK hσ
      h3) t ht ht3 ht1).1) a ha b hb
  ·
    intro P hP t ht ht3 ht1
    exact D4ThreeBCentralizer.not_le_centralizer_of_threeB_triality_two hn hK σ hσ hP ht ht3 ht1
  ·
    intro y hy hyk hy3 g hg
    exact CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4NormCent_holds K (2 ^ n) σ hK hσ h3
      y hy hyk hy3 g hg
  ·
    intro z hz hz3 hz1
    exact exists_r891D4Layer_d4ShortSL2 hn hK σ hσ hz hz3 hz1

theorem exists_r891D4Setup {X : Type} [Group X] {n : ℕ} (hX : Is3D4 X n) :
    ∃ S B : Subgroup X, R891D4Setup n S B := by
  obtain ⟨hn, K, hfield, hfin, σ, hK, hσ, ⟨e⟩⟩ := r891_is3D4_model hX
  let := hfield
  let := hfin
  exact ⟨_, _, (r891D4Setup_d4ShortSL2 hn hK σ hσ).map e.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
