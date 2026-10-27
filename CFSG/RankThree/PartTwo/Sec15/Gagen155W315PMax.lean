module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xFacts
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Proof155P

theorem pCoreOf_sup_le_of_scriptQ {A X K Y M T P : Subgroup G} (hA : Late.IsE27 A)
    (h146 : Item146 A (lB A)) (hE : End155N A X K Y M T P)
    (hf : Proof155Wx.Facts155W A X Y M P)
    (hQ2 : ∀ V ≤ w155 A M X, IsPGroup 2 V → A ≤ Subgroup.normalizer (V : Set G) →
      V ∈ scriptQ A (lB A)) :
    CFSG.Open.pCoreOf 2 (w155 A M X ⊔ CFSG.Open.pCoreOf 2 Y) ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := w155 A M X with hW
  set R := CFSG.Open.pCoreOf 2 Y with hR
  set V := CFSG.Open.pCoreOf 2 (W ⊔ R) with hV
  have hfin : P ⊓ (W ⊔ R) = R := by
    simpa [hW, hR, sup_comm] using hf.inf_sup_eq
  have hRP : R ≤ P := hfin ▸ inf_le_left
  have hPW : P ≤ Subgroup.normalizer (W : Set G) := by simpa [hW] using hf.p_le_normalizer_w
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := by simpa [hR] using hf.p_le_normalizer_r
  have hPWR : P ≤ Subgroup.normalizer ((W ⊔ R : Subgroup G) : Set G) :=
    Sec14.le_normalizer_sup hPW hPR
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := by
    rw [hV]
    exact hPWR.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := by simpa [hW] using hf.a_le_normalizer_w
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := (mem_scriptQ_iff.mp hf.mem_p).2.1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hf.mem_x4.1.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    rw [hR, hE.eq_rq]
    exact (Sec14.le_normalizer_sup hAP hAX).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hAWR : A ≤ Subgroup.normalizer ((W ⊔ R : Subgroup G) : Set G) :=
    Sec14.le_normalizer_sup hAW hAR
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [hV]
    exact hAWR.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (W ⊔ R)
  have hP2 : IsPGroup 2 P := hf.isPGroup_p
  have hVP2 : IsPGroup 2 (V ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hV2 hP2 hPV
  set Q₀ := (V ⊔ P) ⊓ W with hQ0
  have hQ0W : Q₀ ≤ W := by rw [hQ0]; exact inf_le_right
  have hQ02 : IsPGroup 2 Q₀ := by
    rw [hQ0]
    exact hVP2.to_le inf_le_left
  have hAVP : A ≤ Subgroup.normalizer ((V ⊔ P : Subgroup G) : Set G) :=
    Sec14.le_normalizer_sup hAV hAP
  have hAQ0 : A ≤ Subgroup.normalizer (Q₀ : Set G) := by
    rw [hQ0]
    exact Late.le_normalizer_inf hAVP hAW
  have hQ0𝓠 : Q₀ ∈ scriptQ A (lB A) := hQ2 Q₀ hQ0W hQ02 hAQ0
  have hPVP : P ≤ Subgroup.normalizer ((V ⊔ P : Subgroup G) : Set G) :=
    Sec14.le_normalizer_sup hPV Subgroup.le_normalizer
  have hPQ0 : P ≤ Subgroup.normalizer (Q₀ : Set G) := by
    rw [hQ0]
    exact Late.le_normalizer_inf hPVP hPW
  have hVPQ : P ⊔ Q₀ = V ⊔ P := by
    have hVWP : V ≤ W ⊔ P :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (W ⊔ R)).trans (sup_le_sup_left hRP W)
    refine le_antisymm ?_ ?_
    · exact sup_le le_sup_right (by rw [hQ0]; exact inf_le_left)
    · refine sup_le ?_ le_sup_left
      intro v hv
      have hv' : v ∈ ((W : Subgroup G) : Set G) * ((P : Subgroup G) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left W P hPW]
        exact hVWP hv
      obtain ⟨w, hwW, p, hpP, hwp⟩ := Set.mem_mul.mp hv'
      have hwVP : w ∈ V ⊔ P := by
        have hvP : w * p ∈ V ⊔ P := by rw [hwp]; exact Subgroup.mem_sup_left hv
        have hw : w = (w * p) * p⁻¹ := by group
        rw [hw]
        exact (V ⊔ P).mul_mem hvP ((V ⊔ P).inv_mem (Subgroup.mem_sup_right hpP))
      have hwQ : w ∈ Q₀ := Subgroup.mem_inf.mpr ⟨hwVP, hwW⟩
      rw [← hwp, ← sup_comm]
      exact Subgroup.mul_mem_sup hwQ hpP
  have hPQ𝓠 : P ⊔ Q₀ ∈ scriptQ A (lB A) :=
    Sec14.sup_mem_scriptQ_of_item146 hA h146 hf.mem_p hQ0𝓠 hPQ0
  have hW0 : W ≤ oPrimeResidualOf 3 (delta A (lB A) M) := by
    simpa [hW] using hf.w_le_i0
  have hQ0M : Q₀ ≤ M :=
    hQ0W.trans (hW0.trans ((Sec14.oPrimeResidualOf_le_self 3 _).trans (Sec14.delta_le M)))
  have hQ0X : Q₀ ≤ Subgroup.normalizer (X : Set G) :=
    hQ0W.trans (hW0.trans hf.i0_le_normalizer_x)
  have hPQle : P ⊔ Q₀ ≤ M ⊓ Subgroup.normalizer (X : Set G) :=
    le_inf (sup_le (hf.le_p.trans inf_le_left) hQ0M)
      (sup_le (hf.le_p.trans inf_le_right) hQ0X)
  have hPQ2 : IsPGroup 2 (P ⊔ Q₀ : Subgroup G) := by rw [hVPQ]; exact hVP2
  have hPQpi : P ⊔ Q₀ ∈ scriptQPi A (lB A) (M ⊓ Subgroup.normalizer (X : Set G)) (piOf 2) :=
    ⟨⟨hPQ𝓠, hPQle⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hPQ2⟩
  have hmax : P = P ⊔ Q₀ := hE.mem_p.eq_of_le hPQpi le_sup_left
  have hVleP : V ≤ P := by
    have h1 : V ≤ V ⊔ P := le_sup_left
    rw [hVPQ.symm, ← hmax] at h1
    exact h1
  have hVR : V ≤ R := by
    have h1 : V ≤ P ⊓ (W ⊔ R) :=
      le_inf hVleP (CFSG.LieType.BorelTits.pCoreOf_le 2 (W ⊔ R))
    rwa [hfin] at h1
  exact hVR

end Proof155P

end CFSG.RankThree.PartTwo.Sec15
