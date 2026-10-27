module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModel
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDeltaNode
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdCore

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.TableBUE CFSG.StandardType.SmallU
  CFSG.StandardType.IOneUDelta CFSG.StandardType.IOneUDvdR
open scoped commutatorElement

theorem six_center_eq_bot {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Subgroup.center (UnitaryR K 1 6) = ⊥ :=
  TableBUE.center_proj_eq_bot hK (by norm_num) (by norm_num)

theorem six_package {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* UnitaryR K 1 6} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ UnitaryI K 1 6, ∀ l : L', x (ψ l) = ψ (a l)) :
    ∃ ψb : Qt L' →* UnitaryR K 1 6, (∀ l, ψb (qmk L' l) = ψ l) ∧ Function.Surjective ψb ∧
      ψb.ker ≤ Subgroup.center (Qt L') ∧ commutator (Qt L') = ⊤ ∧ Odd (Nat.card ψb.ker) ∧
      CFSG.Open.IsElemAbelian 3 (A.map (qAutHom L')) ∧
      Nat.card (A.map (qAutHom L')) = Nat.card A ∧
      ∀ a ∈ A.map (qAutHom L'), ∃ x ∈ UnitaryI K 1 6, ∀ lb, x (ψb lb) = ψb (a lb) := by
  have hzk : zTwo L' ≤ ψ.ker := zTwo_le_ker hψ (six_center_eq_bot hK)
  refine ⟨qLift ψ hzk, qLift_mk hzk, qLift_surjective hzk hψ, qLift_ker_le_center hzk hker,
    qmk_perfect hperf, qLift_odd_ker hzk hker, CFSG.SectionRank.isElemAbelian_map hA _,
    Subgroup.card_map_of_injective (qAutHom_injective hperf), ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨x, hx, hxa⟩ := hAI a ha
  exact ⟨x, hx, fun lb => qLift_qAut hzk a x hxa lb⟩

theorem normTwoR_down {R L' : Type} [Group R] [Group L'] [Finite L'] {ψ : L' →* R}
    {ψb : Qt L' →* R} (hψb : ∀ l, ψb (qmk L' l) = ψ l) {A : Subgroup (MulAut L')}
    (h : GGNormTwoR ψ A) :
    ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ a ∈ A.map (qAutHom L'), ∀ lb : Qt L', ψb lb ∈ U → ψb (a lb) ∈ U := by
  obtain ⟨U, hU1, hU2, hUA⟩ := h
  refine ⟨U, hU1, hU2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ lb hlb
  obtain ⟨l, rfl⟩ := qmk_surjective lb
  rw [qAutHom_mk, hψb] at *
  exact hUA a ha l hlb

end CFSG.StandardType.USixTwo

end
