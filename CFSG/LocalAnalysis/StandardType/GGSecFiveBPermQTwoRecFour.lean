module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoRecFive
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLGenerate
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameMp
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCrossingFour
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoSingleton
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoKReflect

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  Polynomial CFSG.RankThree.CALinearPlane
open scoped MatrixGroups

theorem ggSecFiveBPermQTwo_four_exists_lFrame
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J K : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {m : ℕ} {i0 : Fin 4}
    (hRt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3)))
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 3)
    (hc : GGSecFiveBPermQTwoCell 3 Bs L 𝒦 4 eta m K i0)
    (π : Fin 4 ≃ Fin 4) :
    ∃ (σ : SL(4, GaloisField 2 2) →* G)
      (χ : Multiplicative (ZMod 3) →* (GaloisField 2 2)ˣ),
      GGSecFiveBPermSpLFrame Bs L eta π σ χ := by
  have hcfg := hRt.1.1
  obtain ⟨ψ, hker, hrange⟩ := hc.2.2.2.1
  exact exists_ggSecFiveBPermSpLFrame ggInnerDiagMpInput_holds hcfg.tableB_facts.1
    hcfg.1.2.2.2.2.2.1.2.1 hcfg.2.1.2.1 hcfg.2.1.2.2.2 hRt.1.2.2.1.1
    hcfg.card_bstar_inf_centralizer_L.le (by omega) eta hAL
    (f := 2) (by omega) hker hrange 2 π

theorem ggSecFiveBPermQTwo_four_crossing_of_matching_sources
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J K : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {m : ℕ} {i0 : Fin 4}
    (hRt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3)))
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 3)
    (hc : GGSecFiveBPermQTwoCell 3 Bs L 𝒦 4 eta m K i0)
    (π : Fin 4 ≃ Fin 4) {g : (ZMod 2)[X]} [Fact (Irreducible g)] {d : ℕ}
    (ε : Fin m ≃ (Fin (CoordSL.rootPB g).dim × Fin 3) ⊕ Fin d)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : CoordSL.rootMat g ^ 3 = 1)
    (κ : SL(m, ZMod 2) →* G)
    (hFK : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hDim : (CoordSL.rootPB g).dim = 2) {y : G} (hy : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (S : Fin 4 → Subgroup G)
    (hSK : ∀ a : Fin 3, S (π a.succ) =
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {a})).map κ)
    (hSeq : ∀ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G))
      (τ : Equiv.Perm (Fin 4)),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut τ →
        ∀ i, (S i).map (MulAut.conj w).toMonoidHom = S (τ i))
    (hRK : ∀ a b : Fin 3, a ≠ b →
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
        ((coordBlockSL (AdjoinRoot g) {a, b}).map (CoordSL.theta g ε)).map κ) :
    GGSecFiveBPermQTwoCrossing Bs eta π d := by
  obtain ⟨σ, χ, hLF⟩ := ggSecFiveBPermQTwo_four_exists_lFrame hRt eta hAL hc π
  have hBsC : ∀ z ∈ Subgroup.centralizer (Bs : Set G), z ^ 3 = 1 → z ∈ Bs :=
    hRt.1.1.2.1.2.2.2
  obtain ⟨-, hBs, hxBs, -, -⟩ := hRt.1.1.tableB_facts
  have hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    (hRt.1.1.1.2.2.2.2.2.2.1 : LargeEvenSStar 3 B x L).2.2.2.1
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hBs.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  exact ⟨fun hd => hFK.crossing_even_four_of_LFrame hBsC hy hK hDim hd S hSK hSeq hRK
      hBc hxBs hLcomp hLF hAL,
    fun hd => hFK.crossing_odd_four_of_LFrame hBsC hy hK hDim hd S hSK hSeq hRK hLF hAL⟩

theorem ggSecFiveBPermQTwoRecFourInput_of_matching_sources
    (hSources : ∀ (G : Type) [Group G] [Finite G]
      (B Bs : Subgroup G) (x : G) (L D J K : Subgroup G) (𝒦 : Finset (Subgroup G))
      (m : ℕ) (i0 : Fin 4) (hRt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
      (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3)))
      (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 3)
      (hc : GGSecFiveBPermQTwoCell 3 Bs L 𝒦 4 eta m K i0)
      (π : Fin 4 ≃ Fin 4) (g : (ZMod 2)[X]) [Fact (Irreducible g)] (d : ℕ)
      (ε : Fin m ≃ (Fin (CoordSL.rootPB g).dim × Fin 3) ⊕ Fin d)
      (hC : (CoordSL.rootMat g).det = 1) (hCp : CoordSL.rootMat g ^ 3 = 1)
      (κ : SL(m, ZMod 2) →* G)
      (hFK : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
      (hDim : (CoordSL.rootPB g).dim = 2) (hπ0 : π 0 = i0)
      (y : G) (hy : y ∈ Bs)
      (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G))),
      ∃ S : Fin 4 → Subgroup G,
        (∀ a : Fin 3, S (π a.succ) =
          (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {a})).map κ) ∧
        (∀ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G))
          (τ : Equiv.Perm (Fin 4)),
          MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut τ →
            ∀ i, (S i).map (MulAut.conj w).toMonoidHom = S (τ i)) ∧
        (∀ a b : Fin 3, a ≠ b →
          ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
            ((coordBlockSL (AdjoinRoot g) {a, b}).map (CoordSL.theta g ε)).map κ)) :
    GGSecFiveBPermQTwoRecFourInput := by
  intro G _ _ p B Bs x L D J 𝒦 hRt hTier n e hPres hn eta hJoin hAL hNbr hG0 hBB hLab m K i0 hc
  subst n
  obtain rfl := hc.1
  refine ggSecFiveBPermQTwo_recognition_of_crossing ggInnerDiagMpInput_holds hRt
    (r := 2) (by decide) hAL hc ?_
  intro π g _ d ε hC hCp κ hFK hDim hπ0 y hy hK
  obtain ⟨S, hSK, hSeq, hRK⟩ :=
    hSources G B Bs x L D J K 𝒦 m i0 hRt eta hAL hc π g d ε hC hCp κ hFK hDim hπ0 y hy hK
  exact ggSecFiveBPermQTwo_four_crossing_of_matching_sources hRt eta hAL hc π ε hC hCp κ
    hFK hDim hy hK S hSK hSeq hRK

theorem ggSecFiveBPermQTwoRecFourInput_holds : GGSecFiveBPermQTwoRecFourInput := by
  apply ggSecFiveBPermQTwoRecFourInput_of_matching_sources
  intro G _ _ B Bs x L D J K 𝒦 m i0 hRt eta hAL hc π g _ d ε hC hCp κ hFK
    hDim hπ0 y hy hK
  obtain ⟨σ, χ, hLF⟩ := ggSecFiveBPermQTwo_four_exists_lFrame hRt eta hAL hc π
  have hBsC : ∀ z ∈ Subgroup.centralizer (Bs : Set G), z ^ 3 = 1 → z ∈ Bs :=
    hRt.1.1.2.1.2.2.2
  have hm : m = 6 ∨ m = 7 := by
    rcases hc.2.1 with h | h
    · left; omega
    · right; omega
  have hsize : m = 6 + d := by
    simpa only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod, hDim] using
      Fintype.card_congr ε
  have hd : d ≤ 1 := by omega
  obtain ⟨S, hSK, hSeq⟩ := hFK.exists_singleton_family hLF hAL hBsC hy hK
    (by decide : 2 ≤ 2) hd
  refine ⟨S, hSK, hSeq, ?_⟩
  intro a b hab
  simpa only [Subgroup.map_map] using hFK.reflComm hm hBsC hy hK a b hab

end CFSG.StandardType

end
