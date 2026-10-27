module

public import CFSG.LocalAnalysis.WeakClosure81.SixNineConcrete
public import CFSG.LocalAnalysis.WeakClosure81.SevenOneOddFpf
public import CFSG.LocalAnalysis.WeakClosure81.NineStep6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75
  CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_second_case_of_mQuot_eq_one {H A : Subgroup G}
    (hAel : IsElemAbelian 2 A) (hTI : IsTI A) (hrk : 2 < rk ↥A) (hAH : A ≤ H)
    (hAO : ¬ A ≤ pCoreOf 2 H) (hk : E3.mQuot A (A ⊓ pCoreOf 2 H) = 1)
    (hfb : ∀ g ∈ H, conjSubgroup (A ⊓ pCoreOf 2 H) g ≤ normalizer (A : Set G))
    (hodd : ∀ x ∈ H, Odd (orderOf x) → x = 1 ∨ (orderOf x).Prime) :
    ∃ h ∈ H, InCalO 1 (normalizer (A : Set G)) ⊥ A h ∧
      A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h) ≤ pCoreOf 2 H ∧
      ∀ x ∈ A ⊔ conjSubgroup A h, Odd (orderOf x) → x ≠ 1 →
        ∀ b ∈ (A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h)) ⊔
            conjSubgroup (A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h)) h,
          x * b = b * x → b = 1 := by
  classical
  have hA2 : IsPGroup 2 A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAel
  obtain ⟨h, hh, hX⟩ := exists_not_isPGroup_sup_conj_of_not_le_pCore hAH hA2 hAO
  have hO : InCalO 1 (normalizer (A : Set G)) ⊥ A h :=
    inCalO_of_conj_inf_pCoreOf_le hAel (le_of_eq hk) hfb hh hX
  have hU1 : E3.mQuot A (nVSub A h) = 1 := mQuot_nVSub_eq_one hAel hO
  have hUne : nVSub A h ≠ ⊥ := nVSub_ne_bot hAel hrk hO
  have hBle : A ⊓ pCoreOf 2 H ≤ nVSub A h := inf_pCoreOf_le_nVSub hfb hh
  have hB0 : nVSub A h = A ⊓ pCoreOf 2 H := by
    have hadd : E3.mQuot A (A ⊓ pCoreOf 2 H) =
        E3.mQuot (nVSub A h) (A ⊓ pCoreOf 2 H) + E3.mQuot A (nVSub A h) :=
      E3.mQuot_add hBle inf_le_left
    rw [hk, hU1] at hadd
    have hV2 : IsPGroup 2 (nVSub A h) := hA2.to_le inf_le_left
    exact ((E3.mQuot_eq_zero_iff hV2 hBle).1 (by omega)).symm
  have hinf : A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h) = nVSub A h :=
    inf_pCoreOf_sup_conj_eq hAel hTI hrk hO
  have hAHH : A ⊔ conjSubgroup A h ≤ H := by
    refine sup_le hAH fun y hy => ?_
    rw [mem_conjSubgroup_iff] at hy
    have hmem : h * y * h⁻¹ ∈ H := hAH hy
    have hy' : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [hy']
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hmem) hh
  have hconjle : conjSubgroup (A ⊓ pCoreOf 2 H) h ≤ bSub A h :=
    conj_inf_pCoreOf_le_bSub hfb hh
  refine ⟨h, hh, hO, ?_, ?_⟩
  · rw [hinf, hB0]
    exact inf_le_right
  · intro x hx hxo hx1 b hb hxb
    rw [hinf] at hb
    have hb' : b ∈ nVSub A h ⊔ bSub A h := by
      have hconjle' : conjSubgroup (nVSub A h) h ≤ bSub A h := by
        rw [hB0]
        exact hconjle
      exact (sup_le le_sup_left (hconjle'.trans le_sup_right)) hb
    exact eq_one_of_commute_of_odd_of_mQuot_eq_one hAel hTI hUne hU1
      (fun y hy hyo => hodd y (hAHH hy) hyo) hx hxo hx1 hb' hxb

end CFSG.LocalAnalysis.WeakClosure81
