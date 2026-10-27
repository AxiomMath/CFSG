module

public import CFSG.LocalAnalysis.WeakClosure81.NineTwoB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X : Subgroup G} {p : ℕ}

theorem nine_two_two_R (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {B B' : Subgroup G} (hB : B ∈ nineOmegaIn V K S) (hB' : B' ∈ nineOmegaIn V K S) :
    ∃ r ∈ pCoreOf 2 K, B' = conjSubgroup B r := by
  obtain ⟨a, hBa, -, hBO⟩ := mem_omegaSet.mp hB.1
  obtain ⟨a', hB'a, -, hB'O⟩ := mem_omegaSet.mp hB'.1
  obtain ⟨b, hb, hbR⟩ := SetLike.not_le_iff_exists.mp hBO
  obtain ⟨b', hb', hb'R⟩ := SetLike.not_le_iff_exists.mp hB'O
  have hbS : b ∈ S := hB.2 hb
  have hb'S : b' ∈ S := hB'.2 hb'
  have hbK : b ∈ K := h.base.sylowTwo.le hbS
  have hb'K : b' ∈ K := h.base.sylowTwo.le hb'S
  have hb2 : b * b = 1 := by
    have h := (isElemAbelian_of_mem_omegaSet hV.1 hB.1).2 b hb
    rwa [pow_two] at h
  have hb'2 : b' * b' = 1 := by
    have h := (isElemAbelian_of_mem_omegaSet hV.1 hB'.1).2 b' hb'
    rwa [pow_two] at h
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
  have hb'inv : b'⁻¹ = b' := inv_eq_of_mul_eq_one_left hb'2
  have hcomm : ∀ x ∈ X, ⁅b * b'⁻¹, x⁆ ∈ pCoreOf 2 K := by
    intro x hx
    have hxK : x ∈ K := h.base.sylowP.le hx
    have hu : b * x * b⁻¹ * x ∈ pCoreOf 2 K := nine_two_inv hV hm h hB hb hbR hx
    have hu' : b' * x * b'⁻¹ * x ∈ pCoreOf 2 K := nine_two_inv hV hm h hB' hb' hb'R hx
    have hbu' : b * (b' * x * b'⁻¹ * x) * b⁻¹ ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hbK)
        (b' * x * b'⁻¹ * x)).mp hu'
    have hxu : x * (b * x * b⁻¹ * x)⁻¹ * x⁻¹ ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hxK)
        ((b * x * b⁻¹ * x)⁻¹)).mp ((pCoreOf 2 K).inv_mem hu)
    have heq : ⁅b * b'⁻¹, x⁆
        = (b * (b' * x * b'⁻¹ * x) * b⁻¹) * (x * (b * x * b⁻¹ * x)⁻¹ * x⁻¹) := by
      rw [hb'inv]
      simp only [commutatorElement_def, mul_inv_rev, inv_inv]
      rw [hb'inv]
      group
    rw [heq]
    exact (pCoreOf 2 K).mul_mem hbu' hxu
  have hmemK : b * b'⁻¹ ∈ K := K.mul_mem hbK (K.inv_mem hb'K)
  have hmemSup : b * b'⁻¹ ∈ pCoreOf 2 K ⊔ X :=
    TwoPTwo.mem_sup_of_commutator_mem h.base.toTwoPTwoIrred.toTwoPTwo hmemK hcomm
  have hmemS : b * b'⁻¹ ∈ S := S.mul_mem hbS (S.inv_mem hb'S)
  obtain ⟨n, hn⟩ := h.base.sylowTwo.isPGroup ⟨b * b'⁻¹, hmemS⟩
  have hn' : (b * b'⁻¹) ^ 2 ^ n = 1 := by
    have h := congrArg Subtype.val hn
    simpa using h
  have hmemR : b * b'⁻¹ ∈ pCoreOf 2 K :=
    TwoPTwo.mem_pCoreOf_of_mem_sup h.base.toTwoPTwoIrred.toTwoPTwo hmemSup hn'
  have huveq : b⁻¹ * b' = b * b'⁻¹ := by rw [hbinv, hb'inv]
  have huv : b⁻¹ * b' ∈ pCoreOf 2 K := huveq.symm ▸ hmemR
  obtain ⟨j, hj, hjb⟩ := seven_three_three_in hV.1 hV.2.2
    (isElemAbelian_nineE V K).1
    ((nineE_le_pCoreOf V K).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
    (nineE_subgroupOf_normal V K) (nine_two_transitive hV hm h.base.toTwoPTwoIrred)
    le_rfl ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K)).2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
    ⟨hB.1, hB.2.trans h.base.sylowTwo.le⟩
    ⟨hB'.1, hB'.2.trans h.base.sylowTwo.le⟩ hb hbR hb' hb'R huv
  refine ⟨j⁻¹, (pCoreOf 2 K).inv_mem hj, ?_⟩
  have hbB'j : b ∈ conjSubgroup B' j := by
    rw [mem_conjSubgroup_iff]
    have h : j * b * j⁻¹ = b' := by rw [hjb]; group
    rwa [h]
  have hEqB'j : conjSubgroup B' j = conjSubgroup V (a' * j) := by
    rw [hB'a, CFSG.Quasithin.conjSubgroup_conjSubgroup]
  have hmem : b ∈ conjSubgroup V a ⊓ conjSubgroup V (a' * j) :=
    ⟨hBa ▸ hb, hEqB'j ▸ hbB'j⟩
  have hEqB : B = conjSubgroup V (a' * j) := by
    rcases inf_conjSubgroup_eq_bot_or_eq hV.2.2 a (a' * j) with hbot | heq
    · exfalso
      have hb1 : b = 1 := Subgroup.mem_bot.mp (hbot ▸ hmem)
      exact hbR (hb1.symm ▸ (pCoreOf 2 K).one_mem)
    · exact hBa.trans heq
  rw [hB'a, hEqB, CFSG.Quasithin.conjSubgroup_conjSubgroup]
  congr 1
  group

theorem nine_two_three (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p) :
    IsMulCommutative ↥(⨆ B ∈ nineOmegaIn V K S, B) := by
  refine (Subgroup.le_centralizer_iff_isMulCommutative).mp ?_
  refine iSup₂_le fun B hB => ?_
  refine (Subgroup.le_centralizer_iff).mpr ?_
  refine iSup₂_le fun B' hB' => ?_
  obtain ⟨a, b, ha, hb, hN⟩ :=
    nVSub_conj_ne_bot_of_mem_omegaSet hV.2.2 (isElemAbelian_nineE V K).1 hB.1 hB'.1
  have hN' : B ⊓ Subgroup.normalizer (B' : Set G) ≠ ⊥ := by
    rw [ha, hb]
    exact hN
  have hP : IsPGroup 2 ↥(B ⊔ B') :=
    h.base.sylowTwo.isPGroup.to_le (sup_le hB.2 hB'.2)
  have hcomm := commute_of_isPGroup_sup hV.1 hV.2.2 ⟨a, ha⟩ ⟨b, hb⟩ hN' hP
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact hcomm u hu v hv

end CFSG.LocalAnalysis.WeakClosure81
