module

public import CFSG.LocalAnalysis.WeakClosure81.NineStruct
public import CFSG.LocalAnalysis.WeakClosure81.NineStep6
public import CFSG.LocalAnalysis.WeakClosure81.NineStep6b
public import CFSG.Quasithin.Background.E3Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.LocalAnalysis.UniquenessCase.PartTwo
  Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X A : Subgroup G} {p : ℕ} {y : G}

theorem pCoreOf_sup_conj_le_pCoreOf (hA : IsElemAbelian 2 A) (hTI : IsTI A) (hm : 2 < rk ↥A)
    (h : TwoPTwo K S X p) (hAK : A ≤ K) (hyK : y ∈ K)
    (hO : InCalO 1 (normalizer (A : Set G)) ⊥ A y) :
    pCoreOf 2 (A ⊔ conjSubgroup A y) ≤ pCoreOf 2 K := by
  let L : Subgroup G := A ⊔ conjSubgroup A y
  have hconjK : conjSubgroup A y ≤ K := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hxA : y * x * y⁻¹ ∈ A := hx
    have hxK : y * x * y⁻¹ ∈ K := hAK hxA
    have hxe : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    rw [hxe]
    exact K.mul_mem (K.mul_mem (K.inv_mem hyK) hxK) hyK
  have hLK : L ≤ K := sup_le hAK hconjK
  have hpcl : pCoreOf 2 L = nVSub A y ⊔ bSub A y :=
    pCoreOf_sup_conj_eq_nVSub_sup_bSub hA hTI hm hO
  have hleTwo : pCoreOf 2 L ≤ twoResidual L := by
    rw [hpcl]
    exact nVSub_sup_bSub_le_twoResidual hA hTI hm hO
  have hmono : twoResidual L ≤ twoResidual K := E1.twoResidual_mono hLK
  have hK : twoResidual K ≤ pCoreOf 2 K ⊔ X := by
    rw [← TwoPTwo.twoResidual_sup_pCoreOf h]
    exact le_sup_left
  intro k hk
  have hksup : k ∈ pCoreOf 2 K ⊔ X := hK (hmono (hleTwo hk))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨k, hk⟩
  have hn' : k ^ 2 ^ n = 1 := by
    have hv := congrArg Subtype.val hn
    simpa [Subgroup.coe_pow] using hv
  exact TwoPTwo.mem_pCoreOf_of_mem_sup h hksup hn'

theorem inf_pCoreOf_mem_gammaSet (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : TwoPTwo K S X p)
    (hA : IsGConj V A) (hAK : A ≤ K) (hAR : ¬ A ≤ pCoreOf 2 K) (hyK : y ∈ K)
    (hO : InCalO 1 (normalizer (A : Set G)) ⊥ A y) :
    A ⊓ pCoreOf 2 K ∈ E3.gammaSet V 1 (pCoreOf 2 K) ∧ A ⊓ pCoreOf 2 K ≠ ⊥ := by
  obtain ⟨g, hg⟩ := hA
  have hA' : IsElemAbelian 2 A := by
    rw [hg]
    exact isElemAbelian_conjSubgroup' hV.1 g
  have hTI' : IsTI A := by
    rw [hg]
    exact isTI_conj hV.2.2 g
  have hm' : 2 < rk ↥A := by
    rw [hg, E3.rk_conjSubgroup]
    exact hm
  let L : Subgroup G := A ⊔ conjSubgroup A y
  let R : Subgroup G := pCoreOf 2 K
  let U : Subgroup G := nVSub A y
  have hpcle : pCoreOf 2 L ≤ R :=
    pCoreOf_sup_conj_le_pCoreOf hA' hTI' hm' h hAK hyK hO
  have hUeq : A ⊓ pCoreOf 2 L = U := inf_pCoreOf_sup_conj_eq hA' hTI' hm' hO
  have hUleA : U ≤ A := by
    rw [← hUeq]
    exact inf_le_left
  have hUleR : U ≤ R := by
    rw [← hUeq]
    exact inf_le_right.trans hpcle
  have hUleAR : U ≤ A ⊓ R := le_inf hUleA hUleR
  have hUeq' : E3.mQuot A U = 1 := mQuot_nVSub_eq_one hA' hO
  have hmq : E3.mQuot A (A ⊓ R) = 1 := by
    apply le_antisymm ?_ (Nat.one_le_iff_ne_zero.mpr ?_)
    · calc E3.mQuot A (A ⊓ R) ≤ E3.mQuot A U := E3.mQuot_mono hUleAR
        _ = 1 := hUeq'
    · intro h0
      have hAR' : A ≤ R := by
        have hEq : A ⊓ R = A :=
          (E3.mQuot_eq_zero_iff (isPGroup_two_of_isElemAbelian hA') inf_le_left).mp h0
        exact inf_eq_left.mp hEq
      exact hAR hAR'
  refine ⟨?_, ?_⟩
  · rw [E3.mem_gammaSet_iff]
    refine ⟨inf_le_right, ⟨g, ?_, ?_⟩⟩
    · rw [← hg]
      exact inf_le_left
    · simpa [← hg] using hmq
  · intro hbot
    have hUbot : U = ⊥ := by
      rw [← le_bot_iff]
      rw [hbot] at hUleAR
      exact hUleAR
    exact nVSub_ne_bot hA' hm' hO hUbot

end CFSG.LocalAnalysis.WeakClosure81
