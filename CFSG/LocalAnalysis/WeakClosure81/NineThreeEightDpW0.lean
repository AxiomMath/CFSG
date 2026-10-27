module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeDecGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nine3_inf_eq_left_of_sup_eq {I J K W : Subgroup G}
    (hIcomm : IsMulCommutative ↥I) (hJ : J ≤ I) (hK : K ≤ I) (hsup : I = J ⊔ K)
    (hbot : K ⊓ W = ⊥) (hJW : J ≤ W) : I ⊓ W = J := by
  haveI : IsMulCommutative ↥I := hIcomm
  refine le_antisymm ?_ (le_inf hJ hJW)
  rintro x ⟨hxI, hxW⟩
  have hsup' : J.subgroupOf I ⊔ K.subgroupOf I = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hJ hK, ← hsup, Subgroup.subgroupOf_self]
  have hx : (⟨x, hxI⟩ : ↥I) ∈ J.subgroupOf I ⊔ K.subgroupOf I := by
    rw [hsup']; exact Subgroup.mem_top _
  obtain ⟨j, hj, k, hk, hjk⟩ := Subgroup.mem_sup.mp hx
  have hjJ : (j : G) ∈ J := hj
  have hkK : (k : G) ∈ K := hk
  have hval : (j : G) * (k : G) = x := by
    simpa using congrArg (fun z : ↥I => (z : G)) hjk
  have hkW : (k : G) ∈ W := by
    have hk_eq : (k : G) = (j : G)⁻¹ * x := by rw [← hval, inv_mul_cancel_left]
    rw [hk_eq]
    exact W.mul_mem (W.inv_mem (hJW hjJ)) hxW
  have hk1 : (k : G) = 1 := by
    have hkbot : (k : G) ∈ K ⊓ W := ⟨hkK, hkW⟩
    rw [hbot] at hkbot
    exact Subgroup.mem_bot.mp hkbot
  rw [← hval, hk1, mul_one]
  exact hjJ

theorem nine3_nineI_inf_nineW0 (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    nineI V K ⊓ nineW0 V K S g = ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K := by
  have hIeq : nineI V K =
      (⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) ⊔
        conjSubgroup (A ⊓ pCoreOf 2 K) x :=
    (nine3_nineI_eq_J_sup hc hI).1
  have hJ_le_I : (⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) ≤ nineI V K :=
    iSup₂_le fun B hB => hc.inf_pCoreOf_le_nineI hB
  have hK_le_I : conjSubgroup (A ⊓ pCoreOf 2 K) x ≤ nineI V K := by
    rw [hIeq]; exact le_sup_right
  have hbot : conjSubgroup (A ⊓ pCoreOf 2 K) x ⊓ nineW0 V K S g = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h1 : a ∈ conjSubgroup A x ⊓ nineW V S :=
      ⟨E3.conjSubgroup_mono_left x inf_le_left ha.1, hc.nineW0_le_nineW ha.2⟩
    rw [(nine3_conj_inf_nineW hc hI).2] at h1
    exact Subgroup.mem_bot.mp h1
  have hJW : (⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) ≤ nineW0 V K S g := by
    rw [nineW0]; exact le_sup_right
  exact nine3_inf_eq_left_of_sup_eq hI.abelian.1 hJ_le_I hK_le_I hIeq hbot hJW

end CFSG.LocalAnalysis.WeakClosure81
