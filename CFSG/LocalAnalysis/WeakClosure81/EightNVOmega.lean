module

public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenAux
public import CFSG.Quasithin.Background.OddCoprimeFixV

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem cGrp_le_centralizer_omegaOneCenterOf_pCoreOf {H T : Subgroup G} (hTH : IsSylowIn 2 T H)
    (hE : eGrp H T ≤ omegaOneCenterOf (pCoreOf 2 H))
    (hCQ : T ⊓ cGrp H T ≤ pCoreOf 2 H) :
    cGrp H T ≤ centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := pCoreOf 2 H
  let Z0 := omegaOneCenterOf Q
  let C := cGrp H T
  change C ≤ centralizer (Z0 : Set G)
  have hT_le_H : T ≤ H := hTH.le
  have hQ_le_T : Q ≤ T := pCoreOf_le_of_isSylowIn hTH
  have hQ_le_H : Q ≤ H := CFSG.openPCoreOf_le 2 H
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H
  have hH_norm_Q : H ≤ normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H
  have hH_norm_Z0 : H ≤ normalizer (Z0 : Set G) :=
    hH_norm_Q.trans (normalizer_le_normalizer_omegaOneCenterOf Q)
  have hZ0_le_Q : Z0 ≤ Q := omegaOneCenterOf_le Q
  have hZ0_le_H : Z0 ≤ H := hZ0_le_Q.trans hQ_le_H
  have hZ0e : IsElemAbelian 2 Z0 := B2F.isElemAbelian_omegaOneCenterOf Q
  haveI : IsMulCommutative ↥Z0 := hZ0e.1
  have hQ_le_C : Q ≤ C := by
    intro q hq
    refine Subgroup.mem_inf.mpr ⟨hQ_le_H hq, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (mem_centralizer_of_mem_omegaOneCenterOf (hE he) hq).symm
  have hQ_central : Q ≤ centralizer (Z0 : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_of_mem_omegaOneCenterOf hz hq).symm
  have hC_le_H : C ≤ H := inf_le_left
  have hH_norm_E : H ≤ normalizer (eGrp H T : Set G) :=
    le_normalizer_conjClosure (omegaOneCenterOf T) H
  have hH_norm_C : H ≤ normalizer (C : Set G) := by
    have h1 : H ≤ normalizer (H : Set G) := Subgroup.le_normalizer
    have h2 : H ≤ normalizer (centralizer (eGrp H T : Set G) : Set G) :=
      fun h hh => mem_normalizer_centralizer_of_mem_normalizer_set (hH_norm_E hh)
    have h3 : H ≤ normalizer ((H ⊓ centralizer (eGrp H T : Set G) : Subgroup G) : Set G) :=
      (le_inf h1 h2).trans (inf_normalizer_le_normalizer_inf
        (H := H) (K := centralizer (eGrp H T : Set G)))
    exact h3
  have hC_le_N : C ≤ normalizer (Z0 : Set G) := hC_le_H.trans hH_norm_Z0
  haveI hCnormH : (C.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_H).mpr hH_norm_C
  have hCsyl : IsSylowIn 2 (T ⊓ C) C := hTH.inf_normal hC_le_H hCnormH
  have hCQ' : T ⊓ C ≤ Q := hCQ
  have hTQ : T ⊓ C = Q := le_antisymm hCQ' (le_inf hQ_le_T hQ_le_C)
  have hQsyl : IsSylowIn 2 Q C := hTQ ▸ hCsyl
  have hY_le_Z0 : ⁅Z0, C⁆ ≤ Z0 := by
    rw [Subgroup.commutator_le]
    intro z hz c hc
    rw [commutatorElement_def]
    have hcH : c ∈ H := hC_le_H hc
    have h1 : c * z⁻¹ * c⁻¹ ∈ Z0 :=
      (Subgroup.mem_normalizer_iff.mp (hH_norm_Z0 hcH) z⁻¹).1 (Z0.inv_mem hz)
    have he : z * c * z⁻¹ * c⁻¹ = z * (c * z⁻¹ * c⁻¹) := by group
    rw [he]
    exact Z0.mul_mem hz h1
  have hH_norm_Y : H ≤ normalizer (⁅Z0, C⁆ : Subgroup G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hH_norm_Z0 hh),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hH_norm_C hh)]
  have hYbot : ⁅Z0, C⁆ = ⊥ := by
    by_contra hYne
    have hW : IsPGroup 2 ↥(⁅Z0, C⁆ : Subgroup G) := hQ2.to_le (hY_le_Z0.trans hZ0_le_Q)
    have hAW : T ≤ normalizer (⁅Z0, C⁆ : Subgroup G) := hT_le_H.trans hH_norm_Y
    obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (inf_centralizer_ne_bot_of_two_groups hTH.isPGroup hW hAW hYne)
    have hzY : (z : G) ∈ ⁅Z0, C⁆ := (Subgroup.mem_inf.mp z.2).1
    have hzCT : (z : G) ∈ centralizer (T : Set G) := (Subgroup.mem_inf.mp z.2).2
    have hzZ0 : (z : G) ∈ Z0 := hY_le_Z0 hzY
    have hzT : (z : G) ∈ T := hQ_le_T (hZ0_le_Q hzZ0)
    have hz2 : (z : G) ^ 2 = 1 := hZ0e.2 (z : G) hzZ0
    have hzOm : (z : G) ∈ omegaOneCenterOf T :=
      mem_omegaOneCenterOf hzT (fun y hy => Subgroup.mem_centralizer_iff.mp hzCT y hy) hz2
    have hzE : (z : G) ∈ eGrp H T := le_conjClosure _ _ hzOm
    have hcard : Nat.card (autOn C Z0) = (C ⊓ centralizer (Z0 : Set G)).relIndex C :=
      CFSG.Quasithin.AutOn.card_autOn_eq_relIndex hC_le_N
    have hQK : Q ≤ C ⊓ centralizer (Z0 : Set G) := le_inf hQ_le_C hQ_central
    have hKC : C ⊓ centralizer (Z0 : Set G) ≤ C := inf_le_left
    have hdvd : Nat.card (autOn C Z0) ∣ Q.relIndex C := by
      rw [hcard]
      refine ⟨Q.relIndex (C ⊓ centralizer (Z0 : Set G)), ?_⟩
      rw [mul_comm]
      exact (Subgroup.relIndex_mul_relIndex Q (C ⊓ centralizer (Z0 : Set G)) C hQK hKC).symm
    have hodd : Odd (Nat.card (autOn C Z0)) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact fun hdvd2 => hQsyl.not_dvd_relIndex (hdvd2.trans hdvd)
    have hV : ∀ v : ↥Z0, v ^ 2 = 1 := fun v => Subtype.ext (hZ0e.2 (v : G) v.2)
    have hcop := commV_inf_fixV_eq_bot_of_odd_card hV (autOn C Z0) hodd
    have hcomm_mem : (⟨(z : G), hzZ0⟩ : ↥Z0) ∈ commV (autOn C Z0) := by
      rw [CFSG.Quasithin.AutOn.commV_autOn_eq hC_le_N, Subgroup.mem_subgroupOf]
      exact hzY
    have hfix_mem : (⟨(z : G), hzZ0⟩ : ↥Z0) ∈ fixV (autOn C Z0) := by
      rw [CFSG.Quasithin.AutOn.fixV_autOn_eq hC_le_N, Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 (z : G) hzE).symm
    have hmem : (⟨(z : G), hzZ0⟩ : ↥Z0) ∈ commV (autOn C Z0) ⊓ fixV (autOn C Z0) :=
      Subgroup.mem_inf.mpr ⟨hcomm_mem, hfix_mem⟩
    rw [hcop, Subgroup.mem_bot] at hmem
    exact hzne (Subtype.ext (by simpa using congrArg Subtype.val hmem))
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have h1 : ⁅z, c⁆ ∈ ⁅Z0, C⁆ := Subgroup.commutator_mem_commutator hz hc
  rw [hYbot, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end CFSG.LocalAnalysis.WeakClosure81

end
