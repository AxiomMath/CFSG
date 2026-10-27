module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1L5
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.StandardType CFSG.Open CliffordAlgebra
  QuadraticMap

private theorem rckHOmM_exists_long {n : ℕ} {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 3 ≤ n)
    {γ : Fin (minusDatum n hirr).rank → ℤ} (hγ : GGLongRoot (minusDatum n hirr) γ) :
    ∃ (i j : Fin (n - 1)) (_ : i ≠ j) (s t : Bool),
      toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hγ
  refine CFSG.StandardType.RootCentOmega.exists_long_weylAction w ?_
  rcases exists_toStdB_eq_of_mem_roots n hγ₀ with h | ⟨k, s, hk⟩
  · exact h
  · exfalso
    set e : Fin (n - 1) → ℤ := Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1 with he
    have h01 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hδ := ofStdB_mem_rootsB (n - 1) (e := e)
      (Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, 1, 1, h01, Or.inl rfl, Or.inl rfl, rfl⟩)
    have h1 : @CFSG.LieType.Steinberg.ht (Fin (n - 1)) _ (ofStdB (n - 1) e) ≤
        @CFSG.LieType.Steinberg.ht (Fin (n - 1)) _ γ₀ := hmax _ hδ
    rw [ht_of_toStdB_eq_add (n - 1) (toStdB_ofStdB (n - 1) e),
      ht_of_toStdB_eq_single (n - 1) hk] at h1
    have hk' := k.isLt
    cases s <;> simp [boolSign] at h1 <;> omega

private theorem rckHOmM_rank_zero {n : ℕ} {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : n ≤ 1)
    {γ : Fin (minusDatum n hirr).rank → ℤ} (hγ : GGLongRoot (minusDatum n hirr) γ) : False := by
  obtain ⟨w, γ₀, hγ₀, -, -⟩ := hγ
  rw [minusDatum_roots, rootsB_eq] at hγ₀
  rcases hγ₀ with ⟨i, -, -, -, -, -, -⟩ | ⟨i, -, -, -⟩
  · have := i.isLt; omega
  · have := i.isLt; omega

private theorem rckHOmM_cent_long {n : ℕ} {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {γ : Fin (minusDatum n hirr).rank → ℤ} {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)
    (hcoord : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    RCKLemmaHCent ⟨spinGroup (quadMinus n K b c), minusDatum n hirr⟩ γ := by
  intro x hx hx1 k hk
  change x ∈ minusRootGroup n hirr γ at hx
  rw [mem_minusRootGroup_long_iff n hirr hij s t hcoord] at hx
  obtain ⟨a, rfl⟩ := hx
  have ha : a ≠ 0 := fun h0 => hx1 (by rw [h0, ofAdd_zero, map_one])
  have hk_eq : (k : CliffordAlgebra (quadMinus n K b c)) *
      ((minusFrame n b c).longRoot hij s t (.ofAdd a) :
        CliffordAlgebra (quadMinus n K b c)) =
      ((minusFrame n b c).longRoot hij s t (.ofAdd a) :
        CliffordAlgebra (quadMinus n K b c)) * (k : CliffordAlgebra (quadMinus n K b c)) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hk
    have h2 := congrArg Subtype.val h
    simpa using h2
  have hcomm : Commute (k : CliffordAlgebra (quadMinus n K b c))
      (1 + a • (ι (quadMinus n K b c) ((minusFrame n b c).vec i s) *
        ι (quadMinus n K b c) ((minusFrame n b c).vec j t))) := by
    rw [← HypFrame.coe_longRoot]
    exact hk_eq
  intro y hy
  change y ∈ minusRootGroup n hirr γ at hy
  rw [mem_minusRootGroup_long_iff n hirr hij s t hcoord] at hy
  obtain ⟨a', rfl⟩ := hy
  have hky : Commute (k : CliffordAlgebra (quadMinus n K b c))
      (((minusFrame n b c).longRoot hij s t (.ofAdd a') :
        spinGroup (quadMinus n K b c)) : CliffordAlgebra (quadMinus n K b c)) := by
    rw [HypFrame.coe_longRoot]
    exact commute_one_add_smul_of_ne_zero ha hcomm a'
  exact Subtype.ext (by simpa using hky.symm.eq)

section RckHOmM2

variable {K : Type} [Field K] [CharP K 2]

private instance rckHOmM2_charP (b c : K) : CharP (CliffordAlgebra (quadMinus 2 K b c)) 2 :=
  charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K _) 2

private noncomputable def rckHOmM2_z (b c : K) : CliffordAlgebra (quadMinus 2 K b c) :=
  ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) * ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) +
    algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b⁻¹ *
      (ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
        ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]))

private theorem rckHOmM2_polar_e_f (b c : K) :
    polar (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) (fVec 2 (0 : Fin 1)) = 1 := by
  rw [polar_eVec_fVec]
  simp

private theorem rckHOmM2_quad_e (b c : K) :
    quadMinus 2 K b c (eVec 2 (0 : Fin 1)) = 0 :=
  quadMinus_eVec 2 b c 0

private theorem rckHOmM2_quad_f (b c : K) :
    quadMinus 2 K b c (fVec 2 (0 : Fin 1)) = 0 :=
  quadMinus_fVec 2 b c 0

private theorem rckHOmM2_quad_p (b c : K) :
    quadMinus 2 K b c (planeVec 2 ![1, 0]) = 1 := by
  rw [quadMinus_planeVec]
  simp

private theorem rckHOmM2_quad_q (b c : K) :
    quadMinus 2 K b c (planeVec 2 ![0, 1]) = c := by
  rw [quadMinus_planeVec]
  simp

private theorem rckHOmM2_polar_p_q (b c : K) :
    polar (quadMinus 2 K b c) (planeVec 2 ![1, 0]) (planeVec 2 ![0, 1]) = b := by
  rw [polar_planeVec_planeVec]
  simp [polarPlane]

private theorem rckHOmM2_polar_e_p (b c : K) (w : Fin 2 → K) :
    polar (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) (planeVec 2 w) = 0 :=
  polar_eVec_planeVec 2 b c 0 w

private theorem rckHOmM2_polar_f_p (b c : K) (w : Fin 2 → K) :
    polar (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) (planeVec 2 w) = 0 :=
  polar_fVec_planeVec 2 b c 0 w

private theorem rckHOmM2_z_mul_e (b c : K) :
    rckHOmM2_z b c * ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) =
      ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) * rckHOmM2_z b c +
        ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) := by
  rw [rckHOmM2_z]
  set E : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) with hE
  set F : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) with hF
  set P : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) with hP
  set R : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) with hR
  set A : CliffordAlgebra (quadMinus 2 K b c) :=
    algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b⁻¹ with hA
  have hEFE : E * F * E = E := by
    rw [hE, hF]
    rw [mul_assoc]
    exact ι_mul_ι_mul_ι_eq_self _ (rckHOmM2_quad_e b c) (rckHOmM2_polar_e_f b c)
  have hEEF : E * (E * F) = 0 := by
    rw [hE, hF, ← mul_assoc]
    rw [ι_mul_ι_self_eq_zero _ (rckHOmM2_quad_e b c), zero_mul]
  have hPRE : (P * R) * E = E * (P * R) := by
    rw [hP, hR, hE]
    exact (ι_mul_ι_mul_ι_comm _ (rckHOmM2_polar_e_p b c ![1, 0])
      (rckHOmM2_polar_e_p b c ![0, 1])).symm
  have hAE : (A * (P * R)) * E = A * (E * (P * R)) := by
    rw [mul_assoc, hPRE]
  have hEA : E * (A * (P * R)) = A * (E * (P * R)) := by
    rw [← mul_assoc, hA, (Algebra.commutes (b⁻¹ : K) E).symm, mul_assoc]
  rw [add_mul, mul_add, hEFE, hEEF, zero_add, hAE, hEA]
  abel

private theorem rckHOmM2_z_mul_f (b c : K) :
    rckHOmM2_z b c * ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) =
      ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) * rckHOmM2_z b c +
        ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) := by
  rw [rckHOmM2_z]
  set E : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) with hE
  set F : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) with hF
  set P : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) with hP
  set R : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) with hR
  set A : CliffordAlgebra (quadMinus 2 K b c) :=
    algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b⁻¹ with hA
  have hEFF : (E * F) * F = 0 := by
    rw [hE, hF, mul_assoc]
    rw [ι_mul_ι_self_eq_zero _ (rckHOmM2_quad_f b c), mul_zero]
  have hPRF : (P * R) * F = F * (P * R) := by
    rw [hP, hR, hF]
    exact (ι_mul_ι_mul_ι_comm _ (rckHOmM2_polar_f_p b c ![1, 0])
      (rckHOmM2_polar_f_p b c ![0, 1])).symm
  have hzF : (E * F + A * (P * R)) * F = A * (F * (P * R)) := by
    rw [add_mul, hEFF, zero_add, mul_assoc, hPRF]
  have hFE : F * E = 1 + E * F := by
    rw [hE, hF]
    have h : ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) *
        ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) +
        ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) *
          ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) = 1 := by
      rw [ι_mul_ι_add_swap, rckHOmM2_polar_e_f b c, map_one]
    have h' : ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) *
        ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) +
        ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) *
          ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) = 1 := by
      rw [add_comm]
      exact h
    rw [eq_sub_of_add_eq h', CharTwo.sub_eq_add]
  have hFEF : F * (E * F) = F := by
    rw [← mul_assoc, hFE, add_mul, one_mul, hEFF, add_zero]
  have hFAPR : F * (A * (P * R)) = A * (F * (P * R)) := by
    rw [← mul_assoc, hA, (Algebra.commutes (b⁻¹ : K) F).symm, mul_assoc]
  have hFz0 : F * (E * F + A * (P * R)) = F + A * (F * (P * R)) := by
    rw [mul_add, hFEF, hFAPR]
  have hFz : F * (E * F + A * (P * R)) = (E * F + A * (P * R)) * F + F := by
    rw [hFz0, hzF]
    exact add_comm _ _
  rw [hFz, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem rckHOmM2_z_mul_p (b c : K) (hb : b ≠ 0) :
    rckHOmM2_z b c * ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) =
      ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) * rckHOmM2_z b c +
        ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) := by
  rw [rckHOmM2_z]
  set E : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) with hE
  set F : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) with hF
  set P : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) with hP
  set R : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) with hR
  set A : CliffordAlgebra (quadMinus 2 K b c) :=
    algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b⁻¹ with hA
  have hPP : P * P = 1 := by
    rw [hP, ι_sq_scalar, rckHOmM2_quad_p b c, map_one]
  have hPE : (E * F) * P = P * (E * F) := by
    rw [hE, hF, hP]
    exact (ι_mul_ι_mul_ι_comm _ (polar_planeVec_eVec 2 b c ![1, 0] 0)
      (polar_planeVec_fVec 2 b c ![1, 0] 0)).symm
  have hRP : R * P = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b + P * R := by
    rw [hP, hR]
    have h : ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
        ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) +
        ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
          ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) = algebraMap K _ b := by
      rw [ι_mul_ι_add_swap, rckHOmM2_polar_p_q b c]
    have h' : ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
        ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) +
        ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
          ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) = algebraMap K _ b := by
      rw [add_comm]
      exact h
    rw [eq_sub_of_add_eq h', CharTwo.sub_eq_add]
  have hbP : algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b * P =
      P * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b :=
    Algebra.commutes b P
  have hPRP : (P * R) * P = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b * P + R := by
    rw [mul_assoc, hRP, mul_add, hbP, ← mul_assoc, hPP, one_mul]
  have hA1 : A * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b = 1 := by
    rw [hA, ← map_mul, inv_mul_cancel₀ hb, map_one]
  have hAPRP : (A * (P * R)) * P = P + A * R := by
    rw [mul_assoc, hPRP, mul_add, ← mul_assoc, hA1, one_mul]
  have hPPR : P * (P * R) = R := by
    rw [← mul_assoc, hPP, one_mul]
  have hPAPR : P * (A * (P * R)) = A * R := by
    rw [← mul_assoc, hA, (Algebra.commutes (b⁻¹ : K) P).symm, mul_assoc, hPPR]
  have hzP : (E * F + A * (P * R)) * P = P * (E * F) + (P + A * R) := by
    rw [add_mul, hPE, hAPRP]
  have hPz : P * (E * F + A * (P * R)) = P * (E * F) + A * R := by
    rw [mul_add, hPAPR]
  rw [hzP, hPz]
  abel

private theorem rckHOmM2_z_mul_q (b c : K) (hb : b ≠ 0) :
    rckHOmM2_z b c * ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) =
      ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) * rckHOmM2_z b c +
        ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) := by
  rw [rckHOmM2_z]
  set E : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) with hE
  set F : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) with hF
  set P : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) with hP
  set R : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) with hR
  set A : CliffordAlgebra (quadMinus 2 K b c) :=
    algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b⁻¹ with hA
  have hRR : R * R = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c := by
    rw [hR, ι_sq_scalar, rckHOmM2_quad_q b c]
  have hRE : (E * F) * R = R * (E * F) := by
    rw [hE, hF, hR]
    exact (ι_mul_ι_mul_ι_comm _ (polar_planeVec_eVec 2 b c ![0, 1] 0)
      (polar_planeVec_fVec 2 b c ![0, 1] 0)).symm
  have hRP : R * P = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b + P * R := by
    rw [hP, hR]
    have h : ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
        ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) +
        ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
          ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) = algebraMap K _ b := by
      rw [ι_mul_ι_add_swap, rckHOmM2_polar_p_q b c]
    have h' : ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
        ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) +
        ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
          ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) = algebraMap K _ b := by
      rw [add_comm]
      exact h
    rw [eq_sub_of_add_eq h', CharTwo.sub_eq_add]
  have hPRR : (P * R) * R = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c * P := by
    rw [mul_assoc, hRR, Algebra.commutes]
  have hAPRR : (A * (P * R)) * R =
      (A * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c) * P := by
    rw [mul_assoc, mul_assoc, hRR, (Algebra.commutes c P).symm, ← mul_assoc]
  have hA1 : A * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b = 1 := by
    rw [hA, ← map_mul, inv_mul_cancel₀ hb, map_one]
  have hRPR : R * (P * R) = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b * R +
      algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c * P := by
    rw [← mul_assoc, hRP, add_mul, hPRR]
  have hRAPR : R * (A * (P * R)) = A * (algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b * R +
      algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c * P) := by
    rw [← mul_assoc, hA, (Algebra.commutes (b⁻¹ : K) R).symm, mul_assoc, hRPR]
  have hzR : (E * F + A * (P * R)) * R = R * (E * F) +
      (A * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c) * P := by
    rw [add_mul, hRE, hAPRR]
  have hAR : A * (algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b * R) = R := by
    rw [← mul_assoc, hA1, one_mul]
  have hAZ : A * (algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c * P) =
      (A * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c) * P := by
    rw [← mul_assoc]
  have hRz0 : R * (E * F + A * (P * R)) = (R * (E * F) + R) +
      (A * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c) * P := by
    rw [mul_add, hRAPR, mul_add, hAR, hAZ]
    abel
  have hRz : R * (E * F + A * (P * R)) = (E * F + A * (P * R)) * R + R := by
    rw [hRz0, hzR]
    abel
  rw [hRz, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem rckHOmM2_z_mul_ι (b c : K) (hb : b ≠ 0) (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → K) :
    rckHOmM2_z b c * ι (quadMinus 2 K b c) w =
      ι (quadMinus 2 K b c) w * rckHOmM2_z b c + ι (quadMinus 2 K b c) w := by
  have hw : w = w (.inl 0) • eVec 2 (0 : Fin 1) + w (.inr (.inl 0)) • fVec 2 (0 : Fin 1) +
      w (.inr (.inr 0)) • planeVec 2 ![1, 0] + w (.inr (.inr 1)) • planeVec 2 ![0, 1] := by
    funext x
    rcases x with i | i | t
    · fin_cases i; simp [eVec, fVec, planeVec]
    · fin_cases i; simp [eVec, fVec, planeVec]
    · fin_cases t <;> simp [eVec, fVec, planeVec]
  conv_lhs => rw [hw]
  conv_rhs => rw [hw]
  simp only [map_add, map_smul, mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  rw [rckHOmM2_z_mul_e b c, rckHOmM2_z_mul_f b c, rckHOmM2_z_mul_p b c hb,
    rckHOmM2_z_mul_q b c hb]
  module

private theorem rckHOmM2_z_mul_pair (b c : K) (hb : b ≠ 0)
    (m₁ m₂ : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → K) :
    rckHOmM2_z b c * (ι (quadMinus 2 K b c) m₁ * ι (quadMinus 2 K b c) m₂) =
      (ι (quadMinus 2 K b c) m₁ * ι (quadMinus 2 K b c) m₂) * rckHOmM2_z b c := by
  have hz2 : ι (quadMinus 2 K b c) m₂ * rckHOmM2_z b c =
      rckHOmM2_z b c * ι (quadMinus 2 K b c) m₂ + ι (quadMinus 2 K b c) m₂ := by
    rw [rckHOmM2_z_mul_ι b c hb m₂, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [← mul_assoc, rckHOmM2_z_mul_ι b c hb m₁, add_mul]
  conv_rhs => rw [mul_assoc, hz2, mul_add, ← mul_assoc]

private theorem rckHOmM2_z_central (b c : K) (hb : b ≠ 0) :
    ∀ x ∈ CliffordAlgebra.even (quadMinus 2 K b c),
      rckHOmM2_z b c * x = x * rckHOmM2_z b c := by
  intro x hx
  refine CliffordAlgebra.even_induction (Q := quadMinus 2 K b c)
    (motive := fun x _ => rckHOmM2_z b c * x = x * rckHOmM2_z b c) ?_ ?_ ?_ x hx
  · intro r
    exact (Algebra.commutes r (rckHOmM2_z b c)).symm
  · intro x y hx hy ihx ihy
    rw [mul_add, add_mul, ihx, ihy]
  · intro m₁ m₂ x hx ih
    rw [← mul_assoc, rckHOmM2_z_mul_pair b c hb m₁ m₂, mul_assoc, ih]
    exact (mul_assoc _ _ _).symm

private theorem rckHOmM2_z_mul_PE (b c : K) (hb : b ≠ 0) :
    rckHOmM2_z b c * (ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
        ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) =
      b⁻¹ • (ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
        ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) := by
  rw [rckHOmM2_z]
  set E : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) with hE
  set F : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) with hF
  set P : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) with hP
  set R : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) with hR
  set A : CliffordAlgebra (quadMinus 2 K b c) :=
    algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b⁻¹ with hA
  have hEFE : (E * F) * E = E := by
    rw [hE, hF, mul_assoc]
    exact ι_mul_ι_mul_ι_eq_self _ (rckHOmM2_quad_e b c) (rckHOmM2_polar_e_f b c)
  have hEFE2 : E * (F * E) = E := by
    rw [← mul_assoc]
    exact hEFE
  have hFP : F * P = P * F := by
    rw [hF, hP]
    exact CharTwo.add_eq_zero.mp (by rw [ι_mul_ι_add_swap, polar_fVec_planeVec, map_zero])
  have hEP : E * P = P * E := by
    rw [hE, hP]
    exact CharTwo.add_eq_zero.mp (by rw [ι_mul_ι_add_swap, polar_eVec_planeVec, map_zero])
  have hPP : P * P = 1 := by
    rw [hP, ι_sq_scalar, rckHOmM2_quad_p b c, map_one]
  have hRP : R * P = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b + P * R := by
    rw [hP, hR]
    have h : ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
        ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) +
        ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
          ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) = algebraMap K _ b := by
      rw [ι_mul_ι_add_swap, rckHOmM2_polar_p_q b c]
    have h' : ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
        ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) +
        ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
          ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) = algebraMap K _ b := by
      rw [add_comm]
      exact h
    rw [eq_sub_of_add_eq h', CharTwo.sub_eq_add]
  have hbP : algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b * P =
      P * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b :=
    Algebra.commutes b P
  have hPRP : (P * R) * P = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b * P + R := by
    rw [mul_assoc, hRP, mul_add, hbP, ← mul_assoc, hPP, one_mul]
  have hA1 : A * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b = 1 := by
    rw [hA, ← map_mul, inv_mul_cancel₀ hb, map_one]
  have hEFPE : (E * F) * (P * E) = P * E := by
    rw [mul_assoc E F (P * E), ← mul_assoc F P E, hFP, mul_assoc P F E,
      ← mul_assoc E P (F * E), hEP, mul_assoc P E (F * E), ← mul_assoc E F E, hEFE]
  have hPRPE : (A * (P * R)) * (P * E) = P * E + A * (R * E) := by
    rw [mul_assoc A (P * R) (P * E), ← mul_assoc (P * R) P E, hPRP, add_mul,
      mul_assoc (algebraMap K _ b) P E, mul_add, ← mul_assoc A (algebraMap K _ b) (P * E),
      hA1, one_mul]
  rw [add_mul, hEFPE, hPRPE]
  rw [show A * (R * E) = b⁻¹ • (R * E) from by rw [hA, Algebra.smul_def]]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem rckHOmM2_z_mul_RE (b c : K) (hb : b ≠ 0) :
    rckHOmM2_z b c * (ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
        ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) =
      ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
          ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) +
        (b⁻¹ * c) • (ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
          ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) := by
  rw [rckHOmM2_z]
  set E : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) with hE
  set F : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) with hF
  set P : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) with hP
  set R : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) with hR
  set A : CliffordAlgebra (quadMinus 2 K b c) :=
    algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b⁻¹ with hA
  have hEFE : (E * F) * E = E := by
    rw [hE, hF, mul_assoc]
    exact ι_mul_ι_mul_ι_eq_self _ (rckHOmM2_quad_e b c) (rckHOmM2_polar_e_f b c)
  have hEFE2 : E * (F * E) = E := by
    rw [← mul_assoc]
    exact hEFE
  have hFR : F * R = R * F := by
    rw [hF, hR]
    exact CharTwo.add_eq_zero.mp (by rw [ι_mul_ι_add_swap, polar_fVec_planeVec, map_zero])
  have hER : E * R = R * E := by
    rw [hE, hR]
    exact CharTwo.add_eq_zero.mp (by rw [ι_mul_ι_add_swap, polar_eVec_planeVec, map_zero])
  have hRR : R * R = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c := by
    rw [hR, ι_sq_scalar, rckHOmM2_quad_q b c]
  have hEFRE : (E * F) * (R * E) = R * E := by
    rw [mul_assoc E F (R * E), ← mul_assoc F R E, hFR, mul_assoc R F E,
      ← mul_assoc E R (F * E), hER, mul_assoc R E (F * E), ← mul_assoc E F E, hEFE]
  have hPRRE : (A * (P * R)) * (R * E) = (b⁻¹ * c) • (P * E) := by
    rw [mul_assoc A (P * R) (R * E), ← mul_assoc (P * R) R E, mul_assoc P R R, hRR,
      (Algebra.commutes c P).symm, mul_assoc (algebraMap K _ c) P E,
      ← mul_assoc A (algebraMap K _ c) (P * E),
      show A * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c =
        algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) (b⁻¹ * c) from by
          rw [hA, ← map_mul],
      Algebra.smul_def]
  rw [add_mul, hEFRE, hPRRE]

private def rckHOmM2_J (b c : K) (w : Fin 2 → K) : Fin 2 → K :=
  ![b⁻¹ * c * w 1, w 1 + b⁻¹ * w 0]

private theorem rckHOmM2_planeVec_decomp (w : Fin 2 → K) :
    planeVec 2 w = w 0 • planeVec 2 ![1, 0] + w 1 • planeVec 2 ![0, 1] := by
  funext x
  rcases x with i | i | t
  · fin_cases i; simp [planeVec]
  · fin_cases i; simp [planeVec]
  · fin_cases t <;> simp [planeVec]

private theorem rckHOmM2_planeVec_J (b c : K) (w : Fin 2 → K) :
    planeVec 2 (rckHOmM2_J b c w) =
      (b⁻¹ * c * w 1) • planeVec 2 ![1, 0] + (w 1 + b⁻¹ * w 0) • planeVec 2 ![0, 1] := by
  funext x
  rcases x with i | i | t
  · fin_cases i; simp [rckHOmM2_J, planeVec]
  · fin_cases i; simp [rckHOmM2_J, planeVec]
  · fin_cases t <;> simp [rckHOmM2_J, planeVec]

private theorem rckHOmM2_z_mul_plane (b c : K) (hb : b ≠ 0) (a d : K) :
    rckHOmM2_z b c *
        ((a • ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) +
          d • ι (quadMinus 2 K b c) (planeVec 2 ![0, 1])) *
          ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) =
      ((b⁻¹ * c * d) • ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) +
        (d + b⁻¹ * a) • ι (quadMinus 2 K b c) (planeVec 2 ![0, 1])) *
        ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) := by
  rw [add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, mul_add,
    Algebra.mul_smul_comm, Algebra.mul_smul_comm, rckHOmM2_z_mul_PE b c hb,
    rckHOmM2_z_mul_RE b c hb]
  rw [add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]
  rw [smul_add]
  module

private theorem rckHOmM2_z_mul_N (b c : K) (hb : b ≠ 0) (w : Fin 2 → K) :
    rckHOmM2_z b c * (ι (quadMinus 2 K b c) (planeVec 2 w) *
        ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) =
      ι (quadMinus 2 K b c) (planeVec 2 (rckHOmM2_J b c w)) *
        ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) := by
  rw [rckHOmM2_planeVec_decomp w, map_add, map_smul, map_smul]
  rw [rckHOmM2_planeVec_J b c w, map_add, map_smul, map_smul]
  exact rckHOmM2_z_mul_plane b c hb (w 0) (w 1)

private theorem rckHOmM2_J_det (b c : K) (hb : b ≠ 0) (w : Fin 2 → K) :
    w 0 * rckHOmM2_J b c w 1 + w 1 * rckHOmM2_J b c w 0 =
      b⁻¹ * (w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2) := by
  simp only [rckHOmM2_J, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  field_simp
  ring

private theorem rckHOmM2_range_pair (x y : Fin 2 → K) : Set.range ![x, y] = {x, y} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

private theorem rckHOmM2_J_linearIndependent (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w : Fin 2 → K} (hw : w ≠ 0) :
    LinearIndependent K ![w, rckHOmM2_J b c w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  have hD : w 0 * rckHOmM2_J b c w 1 + w 1 * rckHOmM2_J b c w 0 ≠ 0 := by
    rw [rckHOmM2_J_det b c hb]
    exact mul_ne_zero (inv_ne_zero hb) (binary_ne_zero hirr hw)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  constructor
  · have hthis : s * (w 0 * rckHOmM2_J b c w 1 + w 1 * rckHOmM2_J b c w 0) = 0 := by
      linear_combination (rckHOmM2_J b c w 1) * h0 + (rckHOmM2_J b c w 0) * h1 -
        (t * rckHOmM2_J b c w 0 * rckHOmM2_J b c w 1) * h2
    exact (mul_eq_zero.mp hthis).resolve_right hD
  · have hthis : t * (w 0 * rckHOmM2_J b c w 1 + w 1 * rckHOmM2_J b c w 0) = 0 := by
      linear_combination (w 1) * h0 + (w 0) * h1 - (s * w 0 * w 1) * h2
    exact (mul_eq_zero.mp hthis).resolve_right hD

private theorem rckHOmM2_J_span (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w : Fin 2 → K} (hw : w ≠ 0) :
    Submodule.span K ({w, rckHOmM2_J b c w} : Set (Fin 2 → K)) = ⊤ := by
  have hli := rckHOmM2_J_linearIndependent b c hb hirr hw
  have hcard : Fintype.card (Fin 2) = Module.finrank K (Fin 2 → K) := by
    simp [Module.finrank_fin_fun]
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  rwa [rckHOmM2_range_pair w (rckHOmM2_J b c w)] at hspan

private theorem rckHOmM2_N_linear (b c : K) (α β : K) (w w' : Fin 2 → K) :
    ι (quadMinus 2 K b c) (planeVec 2 (α • w + β • w')) *
        ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) =
      α • (ι (quadMinus 2 K b c) (planeVec 2 w) *
          ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) +
        β • (ι (quadMinus 2 K b c) (planeVec 2 w') *
          ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) := by
  rw [planeVec_add, planeVec_smul, planeVec_smul, map_add, map_smul, map_smul, add_mul,
    Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]

private theorem rckHOmM2_shortPos_commute (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w₀ : Fin 2 → K} (hw₀ : w₀ ≠ 0)
    (g : spinGroup (quadMinus 2 K b c))
    (hg : g * shortPosHom 2 hirr 0 (.ofAdd w₀) = shortPosHom 2 hirr 0 (.ofAdd w₀) * g) :
    ∀ w, shortPosHom 2 hirr 0 (.ofAdd w) * g = g * shortPosHom 2 hirr 0 (.ofAdd w) := by
  intro w
  have hg' : (g : CliffordAlgebra (quadMinus 2 K b c)) * shortPos 2 b c 0 w₀ =
      shortPos 2 b c 0 w₀ * (g : CliffordAlgebra (quadMinus 2 K b c)) := by
    have := congrArg Subtype.val hg
    simpa [shortPosHom] using this
  have hgN : (g : CliffordAlgebra (quadMinus 2 K b c)) *
        (ι (quadMinus 2 K b c) (planeVec 2 w₀) * ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) =
      (ι (quadMinus 2 K b c) (planeVec 2 w₀) * ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) *
        (g : CliffordAlgebra (quadMinus 2 K b c)) := by
    have h := hg'
    rw [shortPos] at h
    rw [mul_add, mul_one, add_mul, one_mul] at h
    exact add_left_cancel h
  have hgz : (g : CliffordAlgebra (quadMinus 2 K b c)) * rckHOmM2_z b c =
      rckHOmM2_z b c * (g : CliffordAlgebra (quadMinus 2 K b c)) :=
    (rckHOmM2_z_central b c hb (g : CliffordAlgebra (quadMinus 2 K b c))
      (spinGroup.mem_even g.2)).symm
  have hgJN : (g : CliffordAlgebra (quadMinus 2 K b c)) *
        (ι (quadMinus 2 K b c) (planeVec 2 (rckHOmM2_J b c w₀)) *
          ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) =
      (ι (quadMinus 2 K b c) (planeVec 2 (rckHOmM2_J b c w₀)) *
          ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) *
        (g : CliffordAlgebra (quadMinus 2 K b c)) := by
    rw [← rckHOmM2_z_mul_N b c hb w₀]
    rw [← mul_assoc, hgz, mul_assoc, hgN, ← mul_assoc]
  have hspan := rckHOmM2_J_span b c hb hirr hw₀
  have hw_mem : w ∈ Submodule.span K ({w₀, rckHOmM2_J b c w₀} : Set (Fin 2 → K)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hw_mem
  have hNw : ι (quadMinus 2 K b c) (planeVec 2 w) * ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) =
      α • (ι (quadMinus 2 K b c) (planeVec 2 w₀) * ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) +
        β • (ι (quadMinus 2 K b c) (planeVec 2 (rckHOmM2_J b c w₀)) *
          ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) := by
    rw [← hαβ, rckHOmM2_N_linear b c α β w₀ (rckHOmM2_J b c w₀)]
  have hgNw : (g : CliffordAlgebra (quadMinus 2 K b c)) *
        (ι (quadMinus 2 K b c) (planeVec 2 w) * ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) =
      (ι (quadMinus 2 K b c) (planeVec 2 w) * ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1))) *
        (g : CliffordAlgebra (quadMinus 2 K b c)) := by
    rw [hNw, mul_add, add_mul, Algebra.mul_smul_comm, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, hgN, hgJN]
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  change shortPos 2 b c 0 w * (g : CliffordAlgebra (quadMinus 2 K b c)) =
    (g : CliffordAlgebra (quadMinus 2 K b c)) * shortPos 2 b c 0 w
  rw [shortPos, add_mul, one_mul, mul_add, mul_one, hgNw]

private theorem rckHOmM2_shortPos_central (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w₀ : Fin 2 → K} (hw₀ : w₀ ≠ 0) :
    Subgroup.centralizer ({shortPosHom 2 hirr 0 (.ofAdd w₀)} :
        Set (spinGroup (quadMinus 2 K b c))) ≤
      Subgroup.centralizer (((shortPosHom 2 hirr 0).range :
        Subgroup (spinGroup (quadMinus 2 K b c))) : Set (spinGroup (quadMinus 2 K b c))) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hy
  exact rckHOmM2_shortPos_commute b c hb hirr hw₀ g hg w

private theorem rckHOmM2_z_mul_PF (b c : K) (hb : b ≠ 0) :
    rckHOmM2_z b c * (ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
        ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) =
      ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
          ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) +
        b⁻¹ • (ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
          ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) := by
  rw [rckHOmM2_z]
  set E : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) with hE
  set F : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) with hF
  set P : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) with hP
  set R : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) with hR
  set A : CliffordAlgebra (quadMinus 2 K b c) :=
    algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b⁻¹ with hA
  have hFF : F * F = 0 := by
    rw [hF, ι_sq_scalar, rckHOmM2_quad_f b c, map_zero]
  have hFP : F * P = P * F := by
    rw [hF, hP]
    exact CharTwo.add_eq_zero.mp (by rw [ι_mul_ι_add_swap, polar_fVec_planeVec, map_zero])
  have hPP : P * P = 1 := by
    rw [hP, ι_sq_scalar, rckHOmM2_quad_p b c, map_one]
  have hRP : R * P = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b + P * R := by
    rw [hP, hR]
    have h : ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
        ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) +
        ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
          ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) = algebraMap K _ b := by
      rw [ι_mul_ι_add_swap, rckHOmM2_polar_p_q b c]
    have h' : ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
        ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) +
        ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
          ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) = algebraMap K _ b := by
      rw [add_comm]
      exact h
    rw [eq_sub_of_add_eq h', CharTwo.sub_eq_add]
  have hbP : algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b * P =
      P * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b :=
    Algebra.commutes b P
  have hPRP : (P * R) * P = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b * P + R := by
    rw [mul_assoc, hRP, mul_add, hbP, ← mul_assoc, hPP, one_mul]
  have hA1 : A * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b = 1 := by
    rw [hA, ← map_mul, inv_mul_cancel₀ hb, map_one]
  have hEFF : (E * F) * (P * F) = 0 := by
    rw [mul_assoc E F (P * F), ← mul_assoc F P F, hFP, mul_assoc P F F, hFF, mul_zero, mul_zero]
  have hPRPF : (A * (P * R)) * (P * F) = P * F + A * (R * F) := by
    rw [mul_assoc A (P * R) (P * F), ← mul_assoc (P * R) P F, hPRP, add_mul,
      mul_assoc (algebraMap K _ b) P F, mul_add, ← mul_assoc A (algebraMap K _ b) (P * F),
      hA1, one_mul]
  rw [add_mul, hEFF, zero_add, hPRPF]
  rw [show A * (R * F) = b⁻¹ • (R * F) from by rw [hA, Algebra.smul_def]]

private theorem rckHOmM2_z_mul_RF (b c : K) (hb : b ≠ 0) :
    rckHOmM2_z b c * (ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) *
        ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) =
      (b⁻¹ * c) • (ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) *
        ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) := by
  rw [rckHOmM2_z]
  set E : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (eVec 2 (0 : Fin 1)) with hE
  set F : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) with hF
  set P : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) with hP
  set R : CliffordAlgebra (quadMinus 2 K b c) := ι (quadMinus 2 K b c) (planeVec 2 ![0, 1]) with hR
  set A : CliffordAlgebra (quadMinus 2 K b c) :=
    algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) b⁻¹ with hA
  have hFF : F * F = 0 := by
    rw [hF, ι_sq_scalar, rckHOmM2_quad_f b c, map_zero]
  have hFR : F * R = R * F := by
    rw [hF, hR]
    exact CharTwo.add_eq_zero.mp (by rw [ι_mul_ι_add_swap, polar_fVec_planeVec, map_zero])
  have hER : E * R = R * E := by
    rw [hE, hR]
    exact CharTwo.add_eq_zero.mp (by rw [ι_mul_ι_add_swap, polar_eVec_planeVec, map_zero])
  have hRR : R * R = algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c := by
    rw [hR, ι_sq_scalar, rckHOmM2_quad_q b c]
  have hEFF : (E * F) * (R * F) = 0 := by
    rw [mul_assoc E F (R * F), ← mul_assoc F R F, hFR, mul_assoc R F F, hFF, mul_zero, mul_zero]
  have hPRRF : (A * (P * R)) * (R * F) = (b⁻¹ * c) • (P * F) := by
    rw [mul_assoc A (P * R) (R * F), ← mul_assoc (P * R) R F, mul_assoc P R R, hRR,
      (Algebra.commutes c P).symm, mul_assoc (algebraMap K _ c) P F,
      ← mul_assoc A (algebraMap K _ c) (P * F),
      show A * algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) c =
        algebraMap K (CliffordAlgebra (quadMinus 2 K b c)) (b⁻¹ * c) from by
          rw [hA, ← map_mul],
      Algebra.smul_def]
  rw [add_mul, hEFF, zero_add, hPRRF]

private theorem rckHOmM2_z_mul_plane_f (b c : K) (hb : b ≠ 0) (a d : K) :
    rckHOmM2_z b c *
        ((a • ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) +
          d • ι (quadMinus 2 K b c) (planeVec 2 ![0, 1])) *
          ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) =
      ((a + b⁻¹ * c * d) • ι (quadMinus 2 K b c) (planeVec 2 ![1, 0]) +
        (b⁻¹ * a) • ι (quadMinus 2 K b c) (planeVec 2 ![0, 1])) *
        ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) := by
  rw [add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, mul_add,
    Algebra.mul_smul_comm, Algebra.mul_smul_comm, rckHOmM2_z_mul_PF b c hb,
    rckHOmM2_z_mul_RF b c hb]
  rw [add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]
  rw [smul_add]
  module

private def rckHOmM2_Jf (b c : K) (w : Fin 2 → K) : Fin 2 → K :=
  ![w 0 + b⁻¹ * c * w 1, b⁻¹ * w 0]

private theorem rckHOmM2_planeVec_Jf (b c : K) (w : Fin 2 → K) :
    planeVec 2 (rckHOmM2_Jf b c w) =
      (w 0 + b⁻¹ * c * w 1) • planeVec 2 ![1, 0] + (b⁻¹ * w 0) • planeVec 2 ![0, 1] := by
  funext x
  rcases x with i | i | t
  · fin_cases i; simp [rckHOmM2_Jf, planeVec]
  · fin_cases i; simp [rckHOmM2_Jf, planeVec]
  · fin_cases t <;> simp [rckHOmM2_Jf, planeVec]

private theorem rckHOmM2_z_mul_Nf (b c : K) (hb : b ≠ 0) (w : Fin 2 → K) :
    rckHOmM2_z b c * (ι (quadMinus 2 K b c) (planeVec 2 w) *
        ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) =
      ι (quadMinus 2 K b c) (planeVec 2 (rckHOmM2_Jf b c w)) *
        ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) := by
  rw [rckHOmM2_planeVec_decomp w, map_add, map_smul, map_smul]
  rw [rckHOmM2_planeVec_Jf b c w, map_add, map_smul, map_smul]
  exact rckHOmM2_z_mul_plane_f b c hb (w 0) (w 1)

private theorem rckHOmM2_Jf_det (b c : K) (hb : b ≠ 0) (w : Fin 2 → K) :
    w 0 * rckHOmM2_Jf b c w 1 + w 1 * rckHOmM2_Jf b c w 0 =
      b⁻¹ * (w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2) := by
  simp only [rckHOmM2_Jf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  field_simp
  ring

private theorem rckHOmM2_Jf_linearIndependent (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w : Fin 2 → K} (hw : w ≠ 0) :
    LinearIndependent K ![w, rckHOmM2_Jf b c w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  have hD : w 0 * rckHOmM2_Jf b c w 1 + w 1 * rckHOmM2_Jf b c w 0 ≠ 0 := by
    rw [rckHOmM2_Jf_det b c hb]
    exact mul_ne_zero (inv_ne_zero hb) (binary_ne_zero hirr hw)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  constructor
  · have hthis : s * (w 0 * rckHOmM2_Jf b c w 1 + w 1 * rckHOmM2_Jf b c w 0) = 0 := by
      linear_combination (rckHOmM2_Jf b c w 1) * h0 + (rckHOmM2_Jf b c w 0) * h1 -
        (t * rckHOmM2_Jf b c w 0 * rckHOmM2_Jf b c w 1) * h2
    exact (mul_eq_zero.mp hthis).resolve_right hD
  · have hthis : t * (w 0 * rckHOmM2_Jf b c w 1 + w 1 * rckHOmM2_Jf b c w 0) = 0 := by
      linear_combination (w 1) * h0 + (w 0) * h1 - (s * w 0 * w 1) * h2
    exact (mul_eq_zero.mp hthis).resolve_right hD

private theorem rckHOmM2_Jf_span (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w : Fin 2 → K} (hw : w ≠ 0) :
    Submodule.span K ({w, rckHOmM2_Jf b c w} : Set (Fin 2 → K)) = ⊤ := by
  have hli := rckHOmM2_Jf_linearIndependent b c hb hirr hw
  have hcard : Fintype.card (Fin 2) = Module.finrank K (Fin 2 → K) := by
    simp [Module.finrank_fin_fun]
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  rwa [rckHOmM2_range_pair w (rckHOmM2_Jf b c w)] at hspan

private theorem rckHOmM2_Nf_linear (b c : K) (α β : K) (w w' : Fin 2 → K) :
    ι (quadMinus 2 K b c) (planeVec 2 (α • w + β • w')) *
        ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) =
      α • (ι (quadMinus 2 K b c) (planeVec 2 w) *
          ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) +
        β • (ι (quadMinus 2 K b c) (planeVec 2 w') *
          ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) := by
  rw [planeVec_add, planeVec_smul, planeVec_smul, map_add, map_smul, map_smul, add_mul,
    Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]

private theorem rckHOmM2_shortNeg_commute (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w₀ : Fin 2 → K} (hw₀ : w₀ ≠ 0)
    (g : spinGroup (quadMinus 2 K b c))
    (hg : g * shortNegHom 2 hirr 0 (.ofAdd w₀) = shortNegHom 2 hirr 0 (.ofAdd w₀) * g) :
    ∀ w, shortNegHom 2 hirr 0 (.ofAdd w) * g = g * shortNegHom 2 hirr 0 (.ofAdd w) := by
  intro w
  have hg' : (g : CliffordAlgebra (quadMinus 2 K b c)) * shortNeg 2 b c 0 w₀ =
      shortNeg 2 b c 0 w₀ * (g : CliffordAlgebra (quadMinus 2 K b c)) := by
    have := congrArg Subtype.val hg
    simpa [shortNegHom] using this
  have hgN : (g : CliffordAlgebra (quadMinus 2 K b c)) *
        (ι (quadMinus 2 K b c) (planeVec 2 w₀) * ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) =
      (ι (quadMinus 2 K b c) (planeVec 2 w₀) * ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) *
        (g : CliffordAlgebra (quadMinus 2 K b c)) := by
    have h := hg'
    rw [shortNeg] at h
    rw [mul_add, mul_one, add_mul, one_mul] at h
    exact add_left_cancel h
  have hgz : (g : CliffordAlgebra (quadMinus 2 K b c)) * rckHOmM2_z b c =
      rckHOmM2_z b c * (g : CliffordAlgebra (quadMinus 2 K b c)) :=
    (rckHOmM2_z_central b c hb (g : CliffordAlgebra (quadMinus 2 K b c))
      (spinGroup.mem_even g.2)).symm
  have hgJN : (g : CliffordAlgebra (quadMinus 2 K b c)) *
        (ι (quadMinus 2 K b c) (planeVec 2 (rckHOmM2_Jf b c w₀)) *
          ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) =
      (ι (quadMinus 2 K b c) (planeVec 2 (rckHOmM2_Jf b c w₀)) *
          ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) *
        (g : CliffordAlgebra (quadMinus 2 K b c)) := by
    rw [← rckHOmM2_z_mul_Nf b c hb w₀]
    rw [← mul_assoc, hgz, mul_assoc, hgN, ← mul_assoc]
  have hspan := rckHOmM2_Jf_span b c hb hirr hw₀
  have hw_mem : w ∈ Submodule.span K ({w₀, rckHOmM2_Jf b c w₀} : Set (Fin 2 → K)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hw_mem
  have hNw : ι (quadMinus 2 K b c) (planeVec 2 w) * ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1)) =
      α • (ι (quadMinus 2 K b c) (planeVec 2 w₀) * ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) +
        β • (ι (quadMinus 2 K b c) (planeVec 2 (rckHOmM2_Jf b c w₀)) *
          ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) := by
    rw [← hαβ, rckHOmM2_Nf_linear b c α β w₀ (rckHOmM2_Jf b c w₀)]
  have hgNw : (g : CliffordAlgebra (quadMinus 2 K b c)) *
        (ι (quadMinus 2 K b c) (planeVec 2 w) * ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) =
      (ι (quadMinus 2 K b c) (planeVec 2 w) * ι (quadMinus 2 K b c) (fVec 2 (0 : Fin 1))) *
        (g : CliffordAlgebra (quadMinus 2 K b c)) := by
    rw [hNw, mul_add, add_mul, Algebra.mul_smul_comm, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, hgN, hgJN]
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  change shortNeg 2 b c 0 w * (g : CliffordAlgebra (quadMinus 2 K b c)) =
    (g : CliffordAlgebra (quadMinus 2 K b c)) * shortNeg 2 b c 0 w
  rw [shortNeg, add_mul, one_mul, mul_add, mul_one, hgNw]

private theorem rckHOmM2_shortNeg_central (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w₀ : Fin 2 → K} (hw₀ : w₀ ≠ 0) :
    Subgroup.centralizer ({shortNegHom 2 hirr 0 (.ofAdd w₀)} :
        Set (spinGroup (quadMinus 2 K b c))) ≤
      Subgroup.centralizer (((shortNegHom 2 hirr 0).range :
        Subgroup (spinGroup (quadMinus 2 K b c))) : Set (spinGroup (quadMinus 2 K b c))) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hy
  exact rckHOmM2_shortNeg_commute b c hb hirr hw₀ g hg w

private theorem rckHOmM2_cent (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hb : b ≠ 0)
    {β : Fin (minusDatum 2 hirr).rank → ℤ} (hβ : GGLongRoot (minusDatum 2 hirr) β) :
    RCKLemmaHCent ⟨spinGroup (quadMinus 2 K b c), minusDatum 2 hirr⟩ β := by
  intro x hx hx1 k hk
  rw [Subgroup.mem_centralizer_singleton_iff] at hk
  change x ∈ minusRootGroup 2 hirr β at hx
  change k ∈ Subgroup.centralizer
    ((minusRootGroup 2 hirr β : Subgroup (spinGroup (quadMinus 2 K b c))) :
      Set (spinGroup (quadMinus 2 K b c)))
  rw [Subgroup.mem_centralizer_iff]
  have hβroot : β ∈ (minusDatum 2 hirr).roots := by
    obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := hβ
    exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w
  rcases exists_toStdB_eq_of_mem_roots (n := 2) hβroot with
    ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · fin_cases i
    fin_cases j
    exact absurd rfl hij
  · fin_cases i
    have hroot := minusRootGroup_eq_short 2 hirr 0 s h
    cases s
    · rw [hroot, twShortRoot_false] at hx ⊢
      obtain ⟨w₀, rfl⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨v, rfl⟩ : ∃ v, Multiplicative.ofAdd v = w₀ := ⟨Multiplicative.toAdd w₀, rfl⟩
      have hv : v ≠ 0 := by
        intro h0
        exact hx1 (by rw [h0, ofAdd_zero, map_one])
      exact rckHOmM2_shortNeg_central b c hb hirr hv
        (Subgroup.mem_centralizer_singleton_iff.mpr hk)
    · rw [hroot, twShortRoot_true] at hx ⊢
      obtain ⟨w₀, rfl⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨v, rfl⟩ : ∃ v, Multiplicative.ofAdd v = w₀ := ⟨Multiplicative.toAdd w₀, rfl⟩
      have hv : v ≠ 0 := by
        intro h0
        exact hx1 (by rw [h0, ofAdd_zero, map_one])
      exact rckHOmM2_shortPos_central b c hb hirr hv
        (Subgroup.mem_centralizer_singleton_iff.mpr hk)

end RckHOmM2

private theorem rckHOmM2_minusCoeffs_fst_ne_zero (g : ℕ) :
    (minusCoeffs 2 g).1 ≠ 0 := by
  intro hb
  have hirr := minusCoeffs_irr 2 g
  obtain ⟨s, hs⟩ :=
    isSquare_of_charTwo' (R := GaloisField 2 g) (minusCoeffs 2 g).2
  refine hirr s ?_
  rw [hb, zero_mul, add_zero, pow_two, hs]
  exact CharTwo.add_self_eq_zero _

theorem rck_lemmaHC_POmegaMinus
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .POmegaMinus m g).D.rank → ℤ}
    (hβ : GGLongRoot (ggU .POmegaMinus m g).D β) :
    RCKLemmaHCent (ggU .POmegaMinus m g) β := by
  by_cases h1 : m ≤ 1
  · exact (rckHOmM_rank_zero (minusCoeffs_irr 2 g) h1 hβ).elim
  by_cases h2 : m = 2
  · subst h2
    exact rckHOmM2_cent (minusCoeffs 2 g).1 (minusCoeffs 2 g).2
      (minusCoeffs_irr 2 g) (rckHOmM2_minusCoeffs_fst_ne_zero g) hβ
  · have hm3 : 3 ≤ m := by omega
    obtain ⟨i, j, hij, s, t, hcoord⟩ := rckHOmM_exists_long (minusCoeffs_irr 2 g) hm3 hβ
    exact rckHOmM_cent_long (minusCoeffs_irr 2 g) hij s t hcoord

end CFSG.StandardType.RCKC1
