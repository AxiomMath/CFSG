module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.LineTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Adjust
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLFlagMat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Line
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Parabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O6pLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O8mLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O8mParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LinePlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

theorem leastParabolic_of_model {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {Γ : Type} [Group Γ] [Finite Γ] (U Qα Q₀ : Subgroup Γ)
    (hmodel : ∀ S : Sylow 2 ↥H, ∃ φ : Γ ≃* ↥H,
      U.map φ.toMonoidHom = (S : Subgroup ↥H) ∧ KTabD.pointStab H S = Q₀.map φ.toMonoidHom)
    (hpar : IsParabolicTwo Γ Qα) (hUQ : U ≤ Qα) (hnot : ¬ Qα ≤ Q₀)
    (hleast : ∀ P : Subgroup Γ, IsParabolicTwo Γ P → U ≤ P → ¬ P ≤ Q₀ → Qα ≤ P)
    (S : Sylow 2 ↥H) :
    ∃ Qα : Subgroup ↥H, IsParabolicTwo ↥H Qα ∧ (S : Subgroup ↥H) ≤ Qα ∧
      ¬ Qα ≤ KTabD.pointStab H S ∧ ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P →
        (S : Subgroup ↥H) ≤ P → ¬ P ≤ KTabD.pointStab H S → Qα ≤ P := by
  obtain ⟨φ, hφU, hφP⟩ := hmodel S
  rw [hφP]
  exact ⟨_, KAdjE.leastParabolic_map φ hφU hpar hUQ hnot hleast⟩

variable {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}

private theorem charP_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

theorem leastParabolic_binaryNaturalSL {d n : ℕ} (hd : 2 ≤ d)
    (h : CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ d n) (S : Sylow 2 ↥H) :
    ∃ Qα : Subgroup ↥H, IsParabolicTwo ↥H Qα ∧ (S : Subgroup ↥H) ≤ Qα ∧
      ¬ Qα ≤ KTabD.pointStab H S ∧ ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P →
        (S : Subgroup ↥H) ≤ P → ¬ P ≤ KTabD.pointStab H S → Qα ≤ P := by
  obtain ⟨K, _, _, hK, hreal⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero d := ⟨by omega⟩
  refine leastParabolic_of_model (KAdjE.slU d K) (KAdjE.slQAlpha d K) (KAdjE.slQZero d K) ?_
    (KAdjE.isParabolicTwo_slQAlpha (by omega)) (KAdjE.slU_le_slQAlpha d K)
    (KAdjE.not_slQAlpha_le_slQZero hd)
    (fun P hP hU hnot => KAdjE.slQAlpha_le_of_parabolic hd hP hU hnot) S
  intro S'
  obtain ⟨U, hU⟩ := KAdjE.exists_sylow_slU (k := d) (K := K) (by omega)
  obtain ⟨φ, h1, h2⟩ := KAdjE.exists_mulEquiv_pointStab_eq_map_sylow hreal
    (KTabD.sylowFixedLine_statedSL (K := K) (d := d) hd) U (hU ▸ KAdjE.slU_le_slQZero) S'
  exact ⟨φ, hU ▸ h1, h2⟩

section Sp

open CFSG.LocalAnalysis.ComponentInitial

private theorem leastParabolic_sp (m : ℕ) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hreal : (FFModel.nat (StatedSp (m + 2) K)).Realizes H ⊤ ⊥) (S : Sylow 2 ↥H) :
    ∃ Qα : Subgroup ↥H, IsParabolicTwo ↥H Qα ∧ (S : Subgroup ↥H) ≤ Qα ∧
      ¬ Qα ≤ KTabD.pointStab H S ∧ ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P →
        (S : Subgroup ↥H) ≤ P → ¬ P ≤ KTabD.pointStab H S → Qα ≤ P := by
  refine leastParabolic_of_model (SymplecticFlag.unipotent (m + 2) K)
    (SymplecticHigher.flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)))
    (KTabD.lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)) ?_
    (KAdjE.isParabolicTwo_flagStabilizer_alpha m K) (KAdjE.unipotent_le_flagStabilizer_alpha m K)
    (KAdjE.not_flagStabilizer_alpha_le_lineStab m K)
    (fun P hP hU hnot => KAdjE.flagStabilizer_alpha_le_of_parabolic m hP hU hnot) S
  intro S'
  obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 (m + 2)
  have hUle : (U : Subgroup ↥(StatedSp (m + 2) K)) ≤
      KTabD.lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1) := by
    rw [hU]
    exact KAdjE.unipotent_le_lineStab m K
  obtain ⟨φ, h1, h2⟩ := KAdjE.exists_mulEquiv_pointStab_eq_map_sylow hreal
    (KTabD.sylowFixedLine_statedSp (K := K) (m + 2)) U hUle S'
  exact ⟨φ, hU ▸ h1, h2⟩

end Sp

theorem leastParabolic_natSp4 {n : ℕ} (h : NatSpn H ⊤ ⊥ 4 n) (S : Sylow 2 ↥H) :
    ∃ Qα : Subgroup ↥H, IsParabolicTwo ↥H Qα ∧ (S : Subgroup ↥H) ≤ Qα ∧
      ¬ Qα ≤ KTabD.pointStab H S ∧ ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P →
        (S : Subgroup ↥H) ≤ P → ¬ P ≤ KTabD.pointStab H S → Qα ≤ P := by
  obtain ⟨-, K, _, _, hK, hreal⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  exact leastParabolic_sp 0 hreal S

theorem leastParabolic_natSp6 {n : ℕ} (h : NatSpn H ⊤ ⊥ 6 n) (S : Sylow 2 ↥H) :
    ∃ Qα : Subgroup ↥H, IsParabolicTwo ↥H Qα ∧ (S : Subgroup ↥H) ≤ Qα ∧
      ¬ Qα ≤ KTabD.pointStab H S ∧ ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P →
        (S : Subgroup ↥H) ≤ P → ¬ P ≤ KTabD.pointStab H S → Qα ≤ P := by
  obtain ⟨-, K, _, _, hK, hreal⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  exact leastParabolic_sp 1 hreal S

section SU4

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par

theorem leastParabolic_natSU4 {a : ℕ} (h : NatSUn H ⊤ ⊥ 4 a) (S : Sylow 2 ↥H) :
    ∃ Qα : Subgroup ↥H, IsParabolicTwo ↥H Qα ∧ (S : Subgroup ↥H) ≤ Qα ∧
      ¬ Qα ≤ KTabD.pointStab H S ∧ ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P →
        (S : Subgroup ↥H) ≤ P → ¬ P ≤ KTabD.pointStab H S → Qα ≤ P := by
  obtain ⟨K, _, _, hK, hreal⟩ := h
  have hF : UnitaryFieldData 2 a K := unitaryFieldDataOfCard hK
  exact leastParabolic_of_model (hypUnitriangular hF 2 0) (UnitaryHigher.flagStabilizer hF 2 0 {2})
    (parP hF) (KAdjE.su4_exists_mulEquiv_pointStab hF hreal)
    (KAdjE.su4_isParabolicTwo_flagStabilizer_two hF)
    (KAdjE.su4_hypUnitriangular_le_flagStabilizer_two hF)
    (KAdjE.su4_not_flagStabilizer_two_le_parP hF)
    (fun P hP hU hnot => KAdjE.su4_flagStabilizer_two_le_of_parabolic hF hP hU hnot) S

end SU4

section Om6m

open CFSG.AGLEmbedding.LeviBlock (orthParab)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

theorem leastParabolic_natOmegaMinusSix {n : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 6 n) (S : Sylow 2 ↥H) :
    ∃ Qα : Subgroup ↥H, IsParabolicTwo ↥H Qα ∧ (S : Subgroup ↥H) ≤ Qα ∧
      ¬ Qα ≤ KTabD.pointStab H S ∧ ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P →
        (S : Subgroup ↥H) ≤ P → ¬ P ≤ KTabD.pointStab H S → Qα ≤ P := by
  obtain ⟨-, K, _, _, b, c, hK, hirr, hreal⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  rw [show (6 : ℕ) / 2 = 3 by norm_num] at hreal
  exact leastParabolic_of_model
    ((tailUnipotent 2 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 2 (minusTailForm K b c))))
    (orthParab 2 (minusTailForm K b c) ![0, 2]) (orthParab 2 (minusTailForm K b c) ![0, 1])
    (KAdjE.om6m_exists_mulEquiv_pointStab hirr hreal) (KAdjE.om6m_isParabolicTwo_orthParab_two hirr)
    ((KAdjE.om6m_tailUnipotent_le_orthParab hirr).trans inf_le_right)
    (KAdjE.om6m_not_orthParab_two_le_one hirr)
    (fun _ hP hU hnot => KAdjE.om6m_orthParab_two_le_of_parabolic hirr hP hU hnot) S

end Om6m

section O6p

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel (plusDerivedUnipotent)

theorem leastParabolic_natOmegaPlusSix {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 6 n) (S : Sylow 2 ↥H) :
    ∃ Qα : Subgroup ↥H, IsParabolicTwo ↥H Qα ∧ (S : Subgroup ↥H) ≤ Qα ∧
      ¬ Qα ≤ KTabD.pointStab H S ∧ ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P →
        (S : Subgroup ↥H) ≤ P → ¬ P ≤ KTabD.pointStab H S → Qα ≤ P := by
  obtain ⟨-, K, _, _, hK, hreal⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  rw [show (6 : ℕ) / 2 = 3 by norm_num] at hreal
  obtain ⟨hpar, hUQ, hnot, hleast⟩ := KAdjE.leastParabolic_omegaPlusQAlpha K
  refine leastParabolic_of_model (plusDerivedUnipotent 3 K) (KAdjE.omegaPlusQAlpha K)
    (KAdjE.omegaPlusQZero K) ?_ hpar hUQ hnot hleast S
  intro S'
  obtain ⟨U, hU⟩ := KAdjE.exists_sylow_plusDerivedUnipotent K
  have : Nonempty (Fin 3 ⊕ Fin 3) := ⟨Sum.inl 0⟩
  obtain ⟨U₀, hU₀, hfix⟩ :=
    KTabA.exists_fixedLine_statedOmega_plus_single (K := K) (p := 2) (m := 3) (by norm_num)
  obtain ⟨φ, h1, h2⟩ := KAdjE.exists_mulEquiv_pointStab_eq_map_sylow hreal
    (KTabC.sylowFixedLine_of_isPGroup U₀ hU₀ _ hfix) U
    (hU ▸ KAdjE.plusDerivedUnipotent_le_omegaPlusQZero K) S'
  exact ⟨φ, hU ▸ h1, h2⟩

end O6p

theorem leastParabolic_natOmegaMinusEight {n : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 8 n)
    (S : Sylow 2 ↥H) :
    ∃ Qα : Subgroup ↥H, IsParabolicTwo ↥H Qα ∧ (S : Subgroup ↥H) ≤ Qα ∧
      ¬ Qα ≤ KTabD.pointStab H S ∧ ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P →
        (S : Subgroup ↥H) ≤ P → ¬ P ≤ KTabD.pointStab H S → Qα ≤ P := by
  obtain ⟨-, K, _, _, b, c, hK, hirr, hreal⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  rw [show (8 : ℕ) / 2 = 4 by norm_num] at hreal
  obtain ⟨φ, hφ⟩ := KAdjE.exists_mulEquiv_omegaMinusQZero hirr
  obtain ⟨hpar, hUQ, hnot, hleast⟩ := KAdjE.leastParabolic_omegaMinusQAlpha hirr φ hφ
  refine leastParabolic_of_model ((t3U K b c).map φ.symm.toMonoidHom) (KAdjE.omegaMinusQAlpha φ)
    (KAdjE.omegaMinusQZero K b c) ?_ hpar hUQ hnot hleast S
  intro S'
  have hUle : (t3U K b c).map φ.symm.toMonoidHom ≤ KAdjE.omegaMinusQZero K b c := by
    rw [← KAdjE.map_symm_omegaMinusTailQZero φ hφ]
    exact Subgroup.map_mono (KAdjE.t3U_le_omegaMinusTailQZero hirr)
  obtain ⟨U, hUc⟩ : ∃ U : Sylow 2 ↥(StatedOmega (StatedQuadMinus 4 K b c)),
      (U : Subgroup _) = (t3U K b c).map φ.symm.toMonoidHom :=
    ⟨(t3Sylow hirr).mapSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective, by
      change ((t3Sylow hirr : Subgroup _)).map φ.symm.toMonoidHom = _
      rw [t3Sylow_coe]⟩
  obtain ⟨ψ, h1, h2⟩ := KAdjE.exists_mulEquiv_pointStab_eq_map_sylow hreal
    (KTabD.sylowFixedLine_omegaMinus (K := K) (m := 4) (b := b) (c := c) (by norm_num) hirr)
    U (hUc.symm ▸ hUle) S'
  exact ⟨ψ, hUc ▸ h1, h2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
