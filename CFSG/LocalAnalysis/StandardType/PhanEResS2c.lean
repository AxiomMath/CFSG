module

public import CFSG.LocalAnalysis.StandardType.PhanEResOrbit
public import CFSG.LocalAnalysis.StandardType.PhanEResPsiStd
public import CFSG.LocalAnalysis.StandardType.PhanEFlagNormal

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.ClassicalInvolution.Phan.PhanE.Flag

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {m : ℕ} {d : List ℕ}

theorem exists_chart_single {I C : Type} (X : ChamberSystem I C)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut (m + 1) d) (S : Set C) (ψ : C → C)
    (Θ₀ : ChamberIso X (flagSys K m)) (M : GL (Fin (m + 1)) K) (pl : List Bool)
    (hM : StabV (m + 1) d M)
    (hS : ∀ c, c ∈ S ↔ Θ₀.Φ c ∈ refSet K (m + 1) d)
    (hψS : ∀ c ∈ S, ψ c ∈ S) (hψψ : ∀ c ∈ S, ψ (ψ c) = c)
    (hkey : ∀ c ∈ S, Θ₀.Φ (ψ c) = flagAct M (flagPsi hK hd pl (Θ₀.Φ c))) :
    ∃ Θ : ChamberIso X (flagSys K m), (∀ c, c ∈ S ↔ Θ.Φ c ∈ refSet K (m + 1) d) ∧
      ∀ c ∈ S, Θ.Φ (ψ c) = flagPsi hK hd pl (Θ.Φ c) := by
  have hinv : ∀ x ∈ refSet K (m + 1) d,
      flagAct M (flagPsi hK hd pl (flagAct M (flagPsi hK hd pl x))) = x := by
    intro x hx
    obtain ⟨c, rfl⟩ : ∃ c, Θ₀.Φ c = x := ⟨Θ₀.Φ.symm x, Θ₀.Φ.apply_symm_apply x⟩
    have hcS : c ∈ S := (hS c).mpr hx
    have h1 := hkey c hcS
    have h2 := hkey (ψ c) (hψS c hcS)
    rw [hψψ c hcS, h1] at h2
    exact h2.symm
  obtain ⟨e, he, heq⟩ := exists_normalForm_flagPsi hK hd pl hM hinv
  let Θ : ChamberIso X (flagSys K m) := Θ₀.trans (flagMapIso (glLin e))
  have hΘ : ∀ c, Θ.Φ c = flagAct e (Θ₀.Φ c) := fun c => rfl
  have himg := flagMap_image_refSet (glLin e) he
  have hiff : ∀ x : FlagK K (m + 1),
      flagAct e x ∈ refSet K (m + 1) d ↔ x ∈ refSet K (m + 1) d := by
    intro x
    constructor
    · intro hx
      have hx' : flagMap (glLin e) x ∈ flagMap (glLin e) '' refSet K (m + 1) d := by
        rw [himg]; exact hx
      obtain ⟨z, hz, hzx⟩ := hx'
      have hzx' : z = x := flagMap_injective (glLin e) hzx
      rwa [hzx'] at hz
    · intro hx
      have hx' : flagMap (glLin e) x ∈ flagMap (glLin e) '' refSet K (m + 1) d :=
        Set.mem_image_of_mem _ hx
      rwa [himg] at hx'
  refine ⟨Θ, ?_, ?_⟩
  · intro c
    rw [hS c, hΘ c]
    exact (hiff (Θ₀.Φ c)).symm
  · intro c hc
    have hxmem : Θ₀.Φ c ∈ refSet K (m + 1) d := (hS c).mp hc
    have hxemem : flagAct e (Θ₀.Φ c) ∈ refSet K (m + 1) d := (hiff (Θ₀.Φ c)).mpr hxmem
    have hn := heq (flagAct e (Θ₀.Φ c)) hxemem
    rw [flagAct_inv_flagAct] at hn
    rw [hΘ (ψ c), hΘ c, hkey c hc]
    exact hn

@[expose] noncomputable def pathMat (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ)
    (d : List ℕ) (N : GL (Fin n) K) (pol : Bool) : GL (Fin n) K :=
  if pol then N * revBlocks K n d else N

theorem stabV_pathMat {n : ℕ} (hd : IsCut n d) {N : GL (Fin n) K} (hN : StabV n d N)
    (pol : Bool) : StabV n d (pathMat K n d N pol) := by
  cases pol
  · simpa [pathMat] using hN
  · simpa [pathMat] using StabV.mul hN (BlockDiag.stabV hd (revBlocks_blockDiag hd))

theorem flagAct_kapMat_stdFlag (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut (m + 1) d)
    (N : GL (Fin (m + 1)) K) (pol : Bool) (P : SpecialLinearGroup (Fin (m + 1)) K)
    (hP : (P : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      if pol then (revBlocks K (m + 1) d : Matrix (Fin (m + 1)) (Fin (m + 1)) K) else 1)
    {A : SpecialLinearGroup (Fin (m + 1)) K} (hA : A ∈ blockSL K m d) :
    flagAct N (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) pol P A))
        (stdFlag K (m + 1))) =
      flagAct (pathMat K (m + 1) d N pol)
        (flagPsi hK hd (List.replicate (d.length - 1) pol)
          (flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1)))) := by
  have hbd : BlockDiag d ((SpecialLinearGroup.toGL A : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) := blockSL_blockDiag hd hA
  cases pol
  · have hP1 : P = 1 := Subtype.ext (by simpa using hP)
    have hkap : kapMat (sg K f) false P A = SpecialLinearGroup.map (sg K f : K →+* K) A := by
      simp [kapMat, hP1]
    have hgg' : ∀ i j,
        (SpecialLinearGroup.toGL (SpecialLinearGroup.map (sg K f : K →+* K) A) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j
        = sg K f (((SpecialLinearGroup.toGL A : GL (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j) := by
      intro i j
      rw [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_GL_coe_matrix,
        SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      rfl
    have heq1 : flagPsi hK hd (List.replicate (d.length - 1) false)
          (flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1)))
        = flagAct (SpecialLinearGroup.toGL
            (SpecialLinearGroup.map (sg K f : K →+* K) A)) (stdFlag K (m + 1)) := by
      rw [flagPsi_flagAct_coll hK hd (SpecialLinearGroup.toGL A)
          (SpecialLinearGroup.toGL (SpecialLinearGroup.map (sg K f : K →+* K) A))
          hbd hgg' (stdFlag_mem_refSet hd), flagPsi_stdFlag_coll hK hd]
    simp only [pathMat, Bool.false_eq_true, if_false]
    rw [hkap, ← heq1]
  · have hPmat : (P : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        (revBlocks K (m + 1) d : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by simpa using hP
    let R : GL (Fin (m + 1)) K := revBlocks K (m + 1) d
    have htoGLP : SpecialLinearGroup.toGL P = R := by
      apply Units.ext
      rw [SpecialLinearGroup.coe_GL_coe_matrix]
      exact hPmat
    have hR : R * R = 1 := revBlocks_mul_self hd
    have hRinv : R⁻¹ = R := inv_eq_of_mul_eq_one_right hR
    let S : SpecialLinearGroup (Fin (m + 1)) K := slSigma (sg K f : K →+* K) (m + 1) A
    have hSval : (S : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        Matrix.adjugate (Matrix.transpose (((A : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).map
          (sg K f : K →+* K))) := by
      rw [show S = slSigma (sg K f : K →+* K) (m + 1) A from rfl, coe_slSigma]
    have hS : (SpecialLinearGroup.toGL S : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (((SpecialLinearGroup.toGL A : GL (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K).map (sg K f : K →+* K)).transpose = 1 := by
      rw [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_GL_coe_matrix, hSval,
        Matrix.adjugate_mul]
      have hdet : (Matrix.transpose ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) K).map
          (sg K f : K →+* K))).det = 1 := by
        rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
          Matrix.SpecialLinearGroup.det_coe, map_one]
      rw [hdet, one_smul]
    have heq1 : flagPsi hK hd (List.replicate (d.length - 1) true)
          (flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1)))
        = flagAct (SpecialLinearGroup.toGL S) (flagAct R (stdFlag K (m + 1))) := by
      rw [flagPsi_flagAct_pol (hK := hK) (hd := hd) (g := SpecialLinearGroup.toGL A)
          (g' := SpecialLinearGroup.toGL S) (hg := hbd) (hgg' := hS)
          (stdFlag_mem_refSet hd), flagPsi_stdFlag_pol hK hd]
    have h1 : kapMat (sg K f) true P A = P * S * P⁻¹ := by
      rw [show kapMat (sg K f) true P A =
          MulAut.conj P (slSigma (sg K f : K →+* K) (m + 1) A) from rfl,
        MulAut.conj_apply]
    have hkapGL : SpecialLinearGroup.toGL (kapMat (sg K f) true P A) =
        R * SpecialLinearGroup.toGL S * R⁻¹ := by
      rw [h1, map_mul, map_mul, map_inv, htoGLP]
    simp only [pathMat, if_true]
    calc flagAct N (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f) true P A))
            (stdFlag K (m + 1)))
        = flagAct N (flagAct R (flagAct
            (SpecialLinearGroup.toGL S)
            (flagAct R (stdFlag K (m + 1))))) := by
          rw [hkapGL, flagAct_mul, flagAct_mul, hRinv]
      _ = flagAct (N * R) (flagAct
            (SpecialLinearGroup.toGL S)
            (flagAct R (stdFlag K (m + 1)))) := by
          rw [← flagAct_mul]
      _ = flagAct (N * R) (flagPsi hK hd (List.replicate (d.length - 1) true)
            (flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1)))) := by
          rw [← heq1]

theorem exists_chart_path {I C : Type} (X : ChamberSystem I C) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hd : IsCut (m + 1) d) (S : Set C) (ψ : C → C) (Θ₀ : ChamberIso X (flagSys K m))
    (N : GL (Fin (m + 1)) K) (hN : StabV (m + 1) d N)
    (hS : ∀ c, c ∈ S ↔ Θ₀.Φ c ∈ refSet K (m + 1) d)
    (hψS : ∀ c ∈ S, ψ c ∈ S) (hψψ : ∀ c ∈ S, ψ (ψ c) = c) (pol : Bool)
    (P : SpecialLinearGroup (Fin (m + 1)) K)
    (hP : (P : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      if pol then (revBlocks K (m + 1) d : Matrix (Fin (m + 1)) (Fin (m + 1)) K) else 1)
    (hψ : ∀ A ∈ blockSL K m d, ∀ c ∈ S,
      Θ₀.Φ c = flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1)) →
        Θ₀.Φ (ψ c) = flagAct N (flagAct
          (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) pol P A)) (stdFlag K (m + 1)))) :
    ∃ Θ : ChamberIso X (flagSys K m), (∀ c, c ∈ S ↔ Θ.Φ c ∈ refSet K (m + 1) d) ∧
      ∀ c ∈ S, Θ.Φ (ψ c) = flagPsi hK hd (List.replicate (d.length - 1) pol) (Θ.Φ c) := by
  refine exists_chart_single X hK hd S ψ Θ₀ (pathMat K (m + 1) d N pol) _
    (stabV_pathMat hd hN pol) hS hψS hψψ ?_
  intro c hc
  obtain ⟨A, hA, hAx⟩ := exists_blockSL_of_mem_refSet hd ((hS c).mp hc)
  rw [hψ A hA c hc hAx, hAx]
  exact flagAct_kapMat_stdFlag hK hd N pol P hP hA

theorem exists_chart_shape {I C : Type} (X : ChamberSystem I C) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hd : IsCut (m + 1) d) (S : Set C) (ψ : C → C) (Θ₀ : ChamberIso X (flagSys K m))
    (N : GL (Fin (m + 1)) K) (hN : StabV (m + 1) d N)
    (hS : ∀ c, c ∈ S ↔ Θ₀.Φ c ∈ refSet K (m + 1) d)
    (hψS : ∀ c ∈ S, ψ c ∈ S) (hψψ : ∀ c ∈ S, ψ (ψ c) = c) (pol : Bool)
    (P : SpecialLinearGroup (Fin (m + 1)) K)
    (hP : (P : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      if pol then (revBlocks K (m + 1) d : Matrix (Fin (m + 1)) (Fin (m + 1)) K) else 1)
    (hψ : ∀ A ∈ blockSL K m d, ∀ c ∈ S,
      Θ₀.Φ c = flagAct (SpecialLinearGroup.toGL A) (stdFlag K (m + 1)) →
        Θ₀.Φ (ψ c) = flagAct N (flagAct
          (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) pol P A)) (stdFlag K (m + 1))))
    (pl : List Bool)
    (hpl : ∀ b, b + 1 < d.length → 2 ≤ blockSize d b → pl.getD b false = pol) :
    ∃ Θ : ChamberIso X (flagSys K m), (∀ c, c ∈ S ↔ Θ.Φ c ∈ refSet K (m + 1) d) ∧
      ∀ c ∈ S, Θ.Φ (ψ c) = flagPsi' K f hK (m + 1) d pl (Θ.Φ c) := by
  obtain ⟨Θ, hΘS, hΘψ⟩ := exists_chart_path X hK hd S ψ Θ₀ N hN hS hψS hψψ pol P hP hψ
  refine ⟨Θ, hΘS, fun c hc => ?_⟩
  rw [hΘψ c hc, flagPsi', dif_pos hd]
  refine flagPsi_eq_of_pol_eq hK hd _ pl (fun b hb h2 => ?_) ((hΘS c).mp hc)
  rw [hpl b hb h2]
  simp [List.getD_replicate, show b < d.length - 1 from by omega]

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
