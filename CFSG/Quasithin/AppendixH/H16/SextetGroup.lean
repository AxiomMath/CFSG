module

public import CFSG.Quasithin.Background.HLUCode24
public import CFSG.Quasithin.AppendixH.H16.Sextet24
public import CFSG.Quasithin.AppendixH.H16.SextetData

public section

open scoped Pointwise

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU CFSG.Monster.Code
  CFSG.Open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk

private theorem conj_ks6_gen {g : Equiv.Perm (Fin 24)} {a b : Array ℕ} (hga : HasArr g a)
    (hgb : HasArr g⁻¹ b) {f : ℕ → ℕ} (hc : ∀ i < 6, cArr (cArr a (ks6Arr i)) b =
      wArr ((List.range 6).map ks6Arr) (subW (f i))) :
    ∀ i < 6, g * ks6P i * g⁻¹ ∈ sxKS := by
  intro i hi
  have h1 : HasArr (g * ks6P i * g⁻¹) (cArr (cArr a (ks6Arr i)) b) :=
    hasArr_mul (hasArr_mul hga (hasArr_ks6 i)) hgb
  rw [hc i hi] at h1
  rw [perm_eq_of_hasArr h1 (hasArr_wPerm hasArr_ksList _)]
  exact wPerm_ksList_mem _

theorem sxGen_le_AutPerm : sxGen ≤ AutPerm := by
  rw [sxGen, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact sxG1_mem
  · exact sxG2_mem
  · exact sxT_mem

theorem sxGen_le_stabilizer_stdSextet :
    sxGen ≤ MulAction.stabilizer S24 stdSextet := by
  rw [sxGen, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · show sxG1 • stdSextet = stdSextet
    exact (smul_stdSextet_iff sxG1).2 sxG1_blockP
  · show sxG2 • stdSextet = stdSextet
    exact (smul_stdSextet_iff sxG2).2 sxG2_blockP
  · show sxT • stdSextet = stdSextet
    exact (smul_stdSextet_iff sxT).2 sxT_blockP

theorem sxGen_le_normalizer_KS : sxGen ≤ Subgroup.normalizer (sxKS : Set S24) := by
  rw [sxGen, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact sxP0_le_normalizer sxG1_mem_P0
  · exact sxP0_le_normalizer sxG2_mem_P0
  · refine mem_normalizer_KS
      (conj_ks6_gen hasArr_sxT hasArr_sxTinv (f := ksConjT) fun i hi => (ks6_conj_t i hi).1) ?_
    rw [inv_inv]
    exact conj_ks6_gen hasArr_sxTinv hasArr_sxT (f := ksConjTInv) fun i hi => (ks6_conj_t i hi).2

theorem card_sxP0 :
    Nat.card ↥sxP0 = 69120 := by
  haveI : Finite (MulAut W11) := CFSG.Quasithin.H.ZTrans.finite_mulAut_z (V := W11)
  have hP0 : Nat.card ↥(imgCd sxP0) = Nat.card ↥sxP0 := card_imgCd sxP0_le
  have hQ : 69120 ≤ Nat.card ↥sxP0 := by
    rw [← hP0]
    calc 69120 = 360 * 192 := by norm_num
      _ ≤ 360 * Nat.card ↥(imgCd sxP0 ⊓ centSub US) := Nat.mul_le_mul_left 360 le_card_centUS
      _ ≤ Nat.card ↥(imgCd sxP0) := card_centUS_mul_le
  exact (perfectCore_stabUSP (card_stabUSP.trans_le card_stab_US_le) hQ).2

theorem sxGen_eq_stabUSP :
    sxGen = stabUSP := by
  refine Subgroup.eq_of_le_of_card_ge sxGen_le ?_
  calc Nat.card ↥stabUSP ≤ 138240 := card_stabUSP.trans_le card_stab_US_le
    _ = 2 * 69120 := by norm_num
    _ ≤ Nat.card ↥sxGen := by
        have h := two_mul_card_P0_le
        rwa [card_sxP0] at h

theorem card_sxGen :
    Nat.card ↥sxGen = 138240 := by
  have hle : Nat.card ↥sxGen ≤ 138240 := by
    rw [sxGen_eq_stabUSP]
    exact card_stabUSP.trans_le card_stab_US_le
  have hge : 138240 ≤ Nat.card ↥sxGen := by
    have h := two_mul_card_P0_le
    rw [card_sxP0] at h
    norm_num at h
    exact h
  exact le_antisymm hle hge

theorem MY_stdSextet_eq :
    MY M24g stdSextet = sxGen := by
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rw [MY]
    exact le_inf sxGen_le_AutPerm sxGen_le_stabilizer_stdSextet
  · rw [card_sxGen]
    exact card_MY_stdSextet_le

theorem perfectCore_sxGen :
    perfectCore sxGen = sxP0 := by
  rw [sxGen_eq_stabUSP]
  exact (perfectCore_stabUSP (card_stabUSP.trans_le card_stab_US_le) (card_sxP0.ge)).1

theorem card_imgCd_sxKS :
    Nat.card ↥(imgCd sxKS) = 64 := by
  haveI : Finite (MulAut W11) := CFSG.Quasithin.H.ZTrans.finite_mulAut_z (V := W11)
  have hP0 : Nat.card ↥(imgCd sxP0) = Nat.card ↥sxP0 := card_imgCd sxP0_le
  obtain ⟨-, -, -, -, -, -, -, hlast⟩ := lu_code_std (hS := card_stab_US_le)
  have hCK := card_centUS_mul_le
  have h64 := le_card_imgCd_KS
  rw [hlast, hP0, card_sxP0] at hCK
  exact le_antisymm (by nlinarith [hCK]) h64

theorem card_sxKS :
    Nat.card ↥sxKS = 64 := by
  rw [← card_imgCd (sxKS_le_P0.trans sxP0_le)]
  exact card_imgCd_sxKS

end CFSG.ASVolI.H16
