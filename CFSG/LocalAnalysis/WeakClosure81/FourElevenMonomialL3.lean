module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Mod
public import CFSG.GH74.Generic.BProg.B2.FixFourS3
public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
public import CFSG.Quasithin.EmptyFaithful.S14118RestBasic
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
public import CFSG.Walter.W67.W1Prop24B
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.E2P.Asc80
open CFSG.Blueprint (LieModel)

variable {Q : Type} [Group Q] [Finite Q]

theorem zmod_three_val_sub (i j : ZMod 3) :
    ((j - i).val : ℤ) ≡ (j.val : ℤ) - (i.val : ℤ) [ZMOD 3] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 3).mp ?_
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem zmod_three_val_add (i j : ZMod 3) :
    ((i + j).val : ℤ) ≡ (i.val : ℤ) + (j.val : ℤ) [ZMOD 3] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 3).mp ?_
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem zpow_eq_zpow_of_modEq_three {X : Type*} [Group X] {ρ : X} (hρ3 : ρ ^ 3 = 1)
    {a b : ℤ} (h : a ≡ b [ZMOD 3]) : ρ ^ a = ρ ^ b := by
  have h3 : ρ ^ (3 : ℤ) = 1 := by simpa using hρ3
  calc ρ ^ a = ρ ^ (a % 3) := zpow_eq_zpow_emod a h3
    _ = ρ ^ (b % 3) := by rw [h]
    _ = ρ ^ b := (zpow_eq_zpow_emod b h3).symm

theorem sigma_mul_zpow {X : Type*} [Group X] {ρ σ : X} (hσ2 : σ ^ 2 = 1)
    (hrel : σ * ρ * σ = ρ⁻¹) (n : ℤ) : σ * ρ ^ n = ρ ^ (-n) * σ := by
  have hσ2' : σ * σ = 1 := by simpa [pow_two] using hσ2
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2'
  have hconj : σ * ρ * σ⁻¹ = ρ⁻¹ := by simpa [hσinv] using hrel
  have hpow : σ * ρ ^ n * σ⁻¹ = ρ ^ (-n) := by
    rw [← conj_zpow, hconj, inv_zpow']
  calc σ * ρ ^ n = (σ * ρ ^ n * σ⁻¹) * σ := by group
    _ = ρ ^ (-n) * σ := by rw [hpow]

@[expose] def dihedralWord {X : Type*} [Group X] (ρ σ : X) : DihedralGroup (3 : ℕ) → X
  | DihedralGroup.r i => ρ ^ (-(i.val : ℤ))
  | DihedralGroup.sr i => ρ ^ (i.val : ℤ) * σ

@[simp]
theorem dihedralWord_r {X : Type*} [Group X] (ρ σ : X) (i : ZMod 3) :
    dihedralWord ρ σ (DihedralGroup.r i) = ρ ^ (-(i.val : ℤ)) := rfl

@[simp]
theorem dihedralWord_sr {X : Type*} [Group X] (ρ σ : X) (i : ZMod 3) :
    dihedralWord ρ σ (DihedralGroup.sr i) = ρ ^ (i.val : ℤ) * σ := rfl

theorem card_closure_le_six {X : Type*} [Group X] [Finite X] {ρ σ : X}
    (hρ3 : ρ ^ 3 = 1) (hσ2 : σ ^ 2 = 1) (hrel : σ * ρ * σ * ρ = 1) :
    Nat.card (Subgroup.closure ({ρ, σ} : Set X)) ≤ 6 := by
  classical
  have hσ2' : σ * σ = 1 := by simpa [pow_two] using hσ2
  have hrel' : σ * ρ * σ = ρ⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have h' : ρ * (σ * ρ * σ) = 1 := by
      calc ρ * (σ * ρ * σ) = ρ * σ * ρ * σ := by group
        _ = (σ * σ) * (ρ * σ * ρ * σ) := by rw [hσ2', one_mul]
        _ = σ * (σ * ρ * σ * ρ) * σ := by group
        _ = σ * 1 * σ := by rw [hrel]
        _ = 1 := by rw [mul_one, hσ2']
    exact h' 
  have hσ2' : σ * σ = 1 := by simpa [pow_two] using hσ2
  let f : DihedralGroup (3 : ℕ) →* X :=
    { toFun := dihedralWord ρ σ
      map_one' := by
        change dihedralWord ρ σ (DihedralGroup.r 0) = 1
        rw [dihedralWord_r]
        simp
      map_mul' := by
        intro a b
        cases a with
        | r i =>
          cases b with
          | r j =>
            simp only [DihedralGroup.r_mul_r, dihedralWord_r]
            rw [← zpow_add]
            exact zpow_eq_zpow_of_modEq_three hρ3 (by
              have h := (zmod_three_val_add i j).neg
              simpa [neg_add, add_comm] using h)
          | sr j =>
            simp only [DihedralGroup.r_mul_sr, dihedralWord_r, dihedralWord_sr]
            rw [← mul_assoc, ← zpow_add]
            rw [show ρ ^ (-(i.val : ℤ) + (j.val : ℤ)) * σ =
                ρ ^ ((j - i).val : ℤ) * σ from by
              congr 1
              exact zpow_eq_zpow_of_modEq_three hρ3 (by
                have h := (zmod_three_val_sub i j).symm
                simpa [sub_eq_add_neg, add_comm] using h)]
        | sr i =>
          cases b with
          | r j =>
            simp only [DihedralGroup.sr_mul_r, dihedralWord_r, dihedralWord_sr]
            rw [mul_assoc, sigma_mul_zpow hσ2 hrel']
            rw [← mul_assoc, ← zpow_add]
            congr 1
            exact zpow_eq_zpow_of_modEq_three hρ3 (by
              have h := zmod_three_val_add i j
              simpa [sub_eq_add_neg, add_comm] using h)
          | sr j =>
            simp only [DihedralGroup.sr_mul_sr, dihedralWord_r, dihedralWord_sr]
            have hσj : σ * ρ ^ (j.val : ℤ) = ρ ^ (-(j.val : ℤ)) * σ :=
              sigma_mul_zpow hσ2 hrel' _
            rw [show ρ ^ (i.val : ℤ) * σ * (ρ ^ (j.val : ℤ) * σ) =
                ρ ^ (i.val : ℤ) * (σ * ρ ^ (j.val : ℤ)) * σ by group]
            rw [hσj]
            rw [show ρ ^ (i.val : ℤ) * (ρ ^ (-(j.val : ℤ)) * σ) * σ =
                (ρ ^ (i.val : ℤ) * ρ ^ (-(j.val : ℤ))) * (σ * σ) by group]
            rw [hσ2', mul_one, ← zpow_add]
            exact zpow_eq_zpow_of_modEq_three hρ3 (by
              have h := (zmod_three_val_sub i j).neg
              simpa [sub_eq_add_neg, neg_sub] using h)
    }
  have hle : f.range ≤ Subgroup.closure ({ρ, σ} : Set X) := by
    rintro _ ⟨a, rfl⟩
    cases a with
    | r i =>
      exact (Subgroup.zpow_mem (K := Subgroup.closure ({ρ, σ} : Set X)) (x := ρ)
        (Subgroup.subset_closure (by simp)) (-(i.val : ℤ)))
    | sr i =>
      exact Subgroup.mul_mem _ ((Subgroup.zpow_mem (K := Subgroup.closure ({ρ, σ} : Set X))
        (x := ρ) (Subgroup.subset_closure (by simp)) (i.val : ℤ)))
        (Subgroup.subset_closure (by simp))
  have hge : Subgroup.closure ({ρ, σ} : Set X) ≤ f.range := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨DihedralGroup.r 2, ?_⟩
      change dihedralWord x σ (DihedralGroup.r 2) = x
      rw [dihedralWord_r]
      rw [show (2 : ZMod 3).val = 2 by decide]
      simpa using (zpow_eq_zpow_of_modEq_three hρ3 (a := (-(2 : ℤ))) (b := 1)
        (by norm_num [Int.ModEq]))
    · refine ⟨DihedralGroup.sr 0, ?_⟩
      change dihedralWord ρ x (DihedralGroup.sr 0) = x
      rw [dihedralWord_sr]
      rw [show (0 : ZMod 3).val = 0 by decide]
      simp
  have hrange : f.range = Subgroup.closure ({ρ, σ} : Set X) := le_antisymm hle hge
  rw [← hrange]
  calc Nat.card f.range ≤ Nat.card (DihedralGroup 3) :=
        Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
    _ = 6 := by rw [DihedralGroup.nat_card]

section Model

open CFSG.ClassicalInvolution.Models CFSG.LocalAnalysis.ComponentInitial
open GH74.Generic.BProg.B2.FixFourS3

variable {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)

omit [Finite K] in
theorem Vhat_eq_signGroup : GH74.Generic.BProg.B2.FixFourS3.Vhat K =
    signGroup K 3 := by
  ext s
  rw [mem_signGroup]
  constructor
  · intro hs
    exact ⟨fun i => (s : Matrix (Fin 3) (Fin 3) K) i i,
      fun i => GH74.Generic.BProg.B2.FixFourS3.Vhat_entry hs i,
      (Matrix.IsDiag.diagonal_diag hs.1).symm⟩
  · rintro ⟨d, hd, h_eq⟩
    refine ⟨?_, ?_⟩
    · rw [h_eq]
      exact Matrix.isDiag_diagonal _
    · apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, h_eq]
      change Matrix.diagonal d * Matrix.diagonal d = 1
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rcases hd i with h | h <;> simp [h]

def zProj (T : Pair 3) : LinearFlag.projectiveSL 3 K :=
  LinearFlag.proj 3 K (zElt K T)

omit [Finite K] in
theorem zElt_mem_Vhat (T : Pair 3) : zElt K T ∈ GH74.Generic.BProg.B2.FixFourS3.Vhat K :=
  ⟨Matrix.isDiag_diagonal _, zElt_mul_self T⟩

omit [Finite K] in
theorem zProj_mem_Vproj (T : Pair 3) :
    zProj (K := K) T ∈ GH74.Generic.BProg.B2.FixFourS3.Vproj K := by
  exact ⟨⟨zElt K T, zElt_mem_Vhat T⟩, rfl⟩

theorem zProj_ne_one (h2 : (2 : K) ≠ 0) (T : Pair 3) : zProj (K := K) T ≠ 1 := by
  intro h
  have h' : LinearFlag.proj 3 K (zElt K T) =
      LinearFlag.proj 3 K (1 : Matrix.SpecialLinearGroup (Fin 3) K) := by
    simpa [zProj] using h
  have hz : (⟨zElt K T, zElt_mem_Vhat T⟩ : GH74.Generic.BProg.B2.FixFourS3.Vhat K) =
      ⟨1, one_mem _⟩ :=
    GH74.Generic.BProg.B2.FixFourS3.proj_injective_Vhat h'
  exact zElt_ne_one h2 T (congrArg Subtype.val hz)

theorem zProj_injective (h2 : (2 : K) ≠ 0) : Function.Injective (zProj (K := K)) := by
  intro T T' h
  have h' : LinearFlag.proj 3 K (zElt K T) = LinearFlag.proj 3 K (zElt K T') := h
  have hz : (⟨zElt K T, zElt_mem_Vhat T⟩ : GH74.Generic.BProg.B2.FixFourS3.Vhat K) =
      ⟨zElt K T', zElt_mem_Vhat T'⟩ :=
    GH74.Generic.BProg.B2.FixFourS3.proj_injective_Vhat h'
  exact zElt_injective h2 (congrArg Subtype.val hz)

omit [Finite K] in
theorem exists_scalar_zElt_of_proj_commute {A : Matrix.SpecialLinearGroup (Fin 3) K} (T : Pair 3)
    (hA : LinearFlag.proj 3 K A * zProj (K := K) T =
      zProj (K := K) T * LinearFlag.proj 3 K A) :
    ∃ ν : Kˣ, ν ^ 3 = 1 ∧ ∀ i j : Fin 3,
      (zMat K 3 T.1) i i * (A : Matrix (Fin 3) (Fin 3) K) i j =
        (ν : K) * ((A : Matrix (Fin 3) (Fin 3) K) i j * (zMat K 3 T.1) j j) := by
  let d : Matrix.SpecialLinearGroup (Fin 3) K := zElt K T
  let C : Matrix.SpecialLinearGroup (Fin 3) K := (d * A) * (A * d)⁻¹
  have hC : C ∈ LinearFlag.scalars 3 K := by
    rw [← LinearFlag.proj_eq_one_iff]
    show LinearFlag.proj 3 K C = 1
    simp only [C, map_mul, map_inv]
    rw [show LinearFlag.proj 3 K d = zProj (K := K) T from rfl]
    rw [mul_inv_eq_one]
    exact hA.symm
  obtain ⟨ν, hν3, hνmat⟩ := LinearFlag.mem_scalars.mp hC
  refine ⟨ν, hν3, ?_⟩
  have hdA : d * A = LinearFlag.scalarElement ν hν3 * (A * d) := by
    apply Subtype.ext
    have h1 : d * A = C * (A * d) := by
      dsimp [C]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [h1]
    simp only [Matrix.SpecialLinearGroup.coe_mul, hνmat, LinearFlag.coe_scalarElement]
  intro i j
  have h := congrFun (congrFun (congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) K =>
    (x : Matrix (Fin 3) (Fin 3) K)) hdA) i) j
  simpa [d, coe_zElt, zMat, LinearFlag.coe_scalarElement, Matrix.scalar_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc] using h

omit [Finite K] in
theorem eq_zero_of_neg_eq_mul {ν x : K} (h2 : (2 : K) ≠ 0) (hν3 : ν ^ 3 = 1)
    (h : -x = ν * x) : x = 0 := by
  have hν_ne : ν ≠ -1 := by
    intro hν
    have h1 : ν ^ 3 = -1 := by rw [hν]; norm_num
    rw [h1] at hν3
    have hzero : (2 : K) = 0 := by linear_combination -hν3
    exact h2 hzero
  have hνx : ν * x = -x := by rw [← h]
  have h' : (ν + 1) * x = 0 := by
    calc (ν + 1) * x = ν * x + x := by ring
      _ = -x + x := by rw [hνx]
      _ = 0 := neg_add_cancel x
  exact (mul_eq_zero.mp h').resolve_left fun hc => hν_ne (by linear_combination hc)

omit [Finite K] in
theorem eq_zero_of_eq_neg_mul {ν x : K} (h2 : (2 : K) ≠ 0) (hν3 : ν ^ 3 = 1)
    (h : x = -(ν * x)) : x = 0 := by
  have hν_ne : ν ≠ -1 := by
    intro hν
    have h1 : ν ^ 3 = -1 := by rw [hν]; norm_num
    rw [h1] at hν3
    have hzero : (2 : K) = 0 := by linear_combination -hν3
    exact h2 hzero
  have hνx : ν * x = -x := by
    have := congrArg Neg.neg h
    simpa using this.symm
  have h' : (ν + 1) * x = 0 := by
    calc (ν + 1) * x = ν * x + x := by ring
      _ = -x + x := by rw [hνx]
      _ = 0 := neg_add_cancel x
  exact (mul_eq_zero.mp h').resolve_left fun hc => hν_ne (by linear_combination hc)

omit [Finite K] in
theorem zProj_conj_of_monomial {M : Matrix.SpecialLinearGroup (Fin 3) K}
    {σ : Equiv.Perm (Fin 3)} (hM : IsMonomialFor (M : Matrix (Fin 3) (Fin 3) K) σ)
    (T : Pair 3) :
    LinearFlag.proj 3 K M * zProj (K := K) T * (LinearFlag.proj 3 K M)⁻¹ =
      zProj (K := K) (Pair.map σ T) := by
  have hMN : (M : Matrix (Fin 3) (Fin 3) K) *
      ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hmat : (M : Matrix (Fin 3) (Fin 3) K) * zMat K 3 T.1 *
      ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        zMat K 3 (Pair.map σ T).1 := by
    rw [hM.mul_zMat_mul_inv hMN T.1]
    rfl
  have hsl : M * zElt K T * M⁻¹ = zElt K (Pair.map σ T) := by
    apply Subtype.ext
    simpa [coe_zElt] using hmat
  rw [zProj, zProj, ← map_inv, ← map_mul, ← map_mul, hsl]

def threeCycle : Equiv.Perm (Fin 3) := Fin.cycleRange 2

def swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem swap01_mul_threeCycle_mul_swap01 : swap01 * threeCycle * swap01 = threeCycle⁻¹ := by
  decide

def rhoSL : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.permMatrixHom threeCycle, by
    change (threeCycle⁻¹.permMatrix K).det = 1
    rw [Matrix.det_permutation]
    norm_num [show Equiv.Perm.sign threeCycle⁻¹ = (1 : ℤˣ) by decide]⟩

def sigmaSL : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨(-1 : Matrix (Fin 3) (Fin 3) K) * Matrix.permMatrixHom swap01, by
    rw [Matrix.det_mul, Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_one]
    change (-1 : K) ^ 3 * (swap01⁻¹.permMatrix K).det = 1
    rw [show swap01⁻¹ = Equiv.swap 0 1 by decide,
      Matrix.det_permutation, Equiv.Perm.sign_swap (by decide)]
    norm_num⟩

omit [Finite K] in
theorem rhoSL_isMonomial : IsMonomialFor (rhoSL (K := K) : Matrix (Fin 3) (Fin 3) K)
    threeCycle := by
  change IsMonomialFor (Matrix.permMatrixHom threeCycle) threeCycle
  exact isMonomialFor_permMatrixHom threeCycle

omit [Finite K] in
theorem sigmaSL_isMonomial : IsMonomialFor (sigmaSL (K := K) : Matrix (Fin 3) (Fin 3) K)
    swap01 := by
  change IsMonomialFor ((-1 : Matrix (Fin 3) (Fin 3) K) * Matrix.permMatrixHom swap01) swap01
  rw [show (-1 : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (fun _ => (-1 : K)) by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]]
  have hneg : IsMonomialFor (Matrix.diagonal (fun _ => (-1 : K)) :
      Matrix (Fin 3) (Fin 3) K) 1 :=
    isMonomialFor_diagonal (fun _ => (-1 : K)) (fun _ => by norm_num)
  simpa using hneg.mul (isMonomialFor_permMatrixHom swap01)

omit [Finite K] in
theorem rhoSL_pow_three : rhoSL (K := K) ^ 3 = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change (Matrix.permMatrixHom threeCycle ^ 3 : Matrix (Fin 3) (Fin 3) K) = 1
  rw [← map_pow, show threeCycle ^ 3 = 1 by decide, map_one]

omit [Finite K] in
theorem sigmaSL_mul_self : sigmaSL (K := K) * sigmaSL = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  change ((-1 : Matrix (Fin 3) (Fin 3) K) * Matrix.permMatrixHom swap01) *
    ((-1 : Matrix (Fin 3) (Fin 3) K) * Matrix.permMatrixHom swap01) = 1
  have h : ((-1 : Matrix (Fin 3) (Fin 3) K) * Matrix.permMatrixHom swap01) *
      ((-1 : Matrix (Fin 3) (Fin 3) K) * Matrix.permMatrixHom swap01) =
      Matrix.permMatrixHom swap01 * Matrix.permMatrixHom swap01 := by
    noncomm_ring
  rw [h, ← map_mul, show swap01 * swap01 = 1 by decide, map_one]

omit [Finite K] in
theorem sigmaSL_mul_rhoSL_mul_sigmaSL_mul_rhoSL :
    sigmaSL (K := K) * rhoSL * sigmaSL * rhoSL = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  change ((-1 : Matrix (Fin 3) (Fin 3) K) * Matrix.permMatrixHom swap01) *
      Matrix.permMatrixHom threeCycle *
      ((-1 : Matrix (Fin 3) (Fin 3) K) * Matrix.permMatrixHom swap01) *
      Matrix.permMatrixHom threeCycle = 1
  have h : ((-1 : Matrix (Fin 3) (Fin 3) K) * Matrix.permMatrixHom swap01) *
      Matrix.permMatrixHom threeCycle *
      ((-1 : Matrix (Fin 3) (Fin 3) K) * Matrix.permMatrixHom swap01) *
      Matrix.permMatrixHom threeCycle =
      Matrix.permMatrixHom swap01 * Matrix.permMatrixHom threeCycle *
        Matrix.permMatrixHom swap01 * Matrix.permMatrixHom threeCycle := by
    noncomm_ring
  rw [h, ← map_mul, ← map_mul, ← map_mul,
    show swap01 * threeCycle * swap01 * threeCycle = 1 by decide, map_one]

def rho : LinearFlag.projectiveSL 3 K := LinearFlag.proj 3 K (rhoSL (K := K))

def sigma : LinearFlag.projectiveSL 3 K := LinearFlag.proj 3 K (sigmaSL (K := K))

omit [Finite K] in
theorem zProj_conj_rho (T : Pair 3) :
    rho (K := K) * zProj (K := K) T * (rho (K := K))⁻¹ =
      zProj (K := K) (Pair.map threeCycle T) := by
  rw [rho]
  exact zProj_conj_of_monomial rhoSL_isMonomial T

omit [Finite K] in
theorem zProj_conj_sigma (T : Pair 3) :
    sigma (K := K) * zProj (K := K) T * (sigma (K := K))⁻¹ =
      zProj (K := K) (Pair.map swap01 T) := by
  rw [sigma]
  exact zProj_conj_of_monomial sigmaSL_isMonomial T

omit [Finite K] in
theorem rho_pow_three : rho (K := K) ^ 3 = 1 := by
  rw [rho, ← map_pow, rhoSL_pow_three, map_one]

omit [Finite K] in
theorem sigma_mul_self : sigma (K := K) * sigma = 1 := by
  rw [sigma, ← map_mul, sigmaSL_mul_self, map_one]

omit [Finite K] in
theorem sigma_mul_rho_mul_sigma_mul_rho :
    sigma (K := K) * rho * sigma * rho = 1 := by
  rw [sigma, rho, ← map_mul, ← map_mul, ← map_mul,
    sigmaSL_mul_rhoSL_mul_sigmaSL_mul_rhoSL, map_one]

omit [Finite K] in
theorem eq_zero_of_sign_opposite {d_i d_j ν x : K} (h2 : (2 : K) ≠ 0) (hν3 : ν ^ 3 = 1)
    (hdi : d_i = 1 ∨ d_i = -1) (hdj : d_j = 1 ∨ d_j = -1) (hopp : d_i = -d_j)
    (h : d_i * x = ν * (x * d_j)) : x = 0 := by
  have hne : (1 : K) ≠ -1 := by
    intro hh
    have htwo : (2 : K) = 0 := by
      calc (2 : K) = 1 - (-1) := by ring
        _ = 0 := by rw [← hh, sub_self]
    exact h2 htwo
  rcases hdi with rfl | rfl <;> rcases hdj with rfl | rfl <;>
    simp only [neg_mul, one_mul, mul_one, mul_neg, neg_neg] at h hopp
  all_goals
    first
    | exfalso; exact hne hopp
    | exfalso; exact hne hopp.symm
    | exact eq_zero_of_neg_eq_mul h2 hν3 h
    | exact eq_zero_of_eq_neg_mul h2 hν3 h

omit [Finite K] in
theorem isDiag_of_mem_centralizer_Vproj (h2 : (2 : K) ≠ 0)
    {A : Matrix.SpecialLinearGroup (Fin 3) K}
    (hA : LinearFlag.proj 3 K A ∈ centralizer
      (GH74.Generic.BProg.B2.FixFourS3.Vproj K : Set (LinearFlag.projectiveSL 3 K))) :
    (A : Matrix (Fin 3) (Fin 3) K).IsDiag := by
  classical
  let T1 : Pair 3 := ⟨{0, 1}, by decide⟩
  let T2 : Pair 3 := ⟨{0, 2}, by decide⟩
  have hmem1 : zProj (K := K) T1 ∈ GH74.Generic.BProg.B2.FixFourS3.Vproj K :=
    zProj_mem_Vproj T1
  have hmem2 : zProj (K := K) T2 ∈ GH74.Generic.BProg.B2.FixFourS3.Vproj K :=
    zProj_mem_Vproj T2
  have hc1 : LinearFlag.proj 3 K A * zProj (K := K) T1 =
      zProj (K := K) T1 * LinearFlag.proj 3 K A :=
    (Subgroup.mem_centralizer_iff.mp hA (zProj T1) hmem1).symm
  have hc2 : LinearFlag.proj 3 K A * zProj (K := K) T2 =
      zProj (K := K) T2 * LinearFlag.proj 3 K A :=
    (Subgroup.mem_centralizer_iff.mp hA (zProj T2) hmem2).symm
  obtain ⟨ν1, hν13, hν1⟩ := exists_scalar_zElt_of_proj_commute T1 hc1
  obtain ⟨ν2, hν23, hν2⟩ := exists_scalar_zElt_of_proj_commute T2 hc2
  have hν13K : (ν1 : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hν13, Units.val_one]
  have hν23K : (ν2 : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hν23, Units.val_one]
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · refine eq_zero_of_sign_opposite h2 hν23K (Or.inr rfl) (Or.inl rfl) (by norm_num) ?_
    simpa [T2, zMat] using hν2 0 1
  · refine eq_zero_of_sign_opposite h2 hν13K (Or.inr rfl) (Or.inl rfl) (by norm_num) ?_
    simpa [T1, zMat] using hν1 0 2
  · refine eq_zero_of_sign_opposite h2 hν23K (Or.inl rfl) (Or.inr rfl) (by norm_num) ?_
    simpa [T2, zMat] using hν2 1 0
  · exact absurd rfl hij
  · refine eq_zero_of_sign_opposite h2 hν13K (Or.inr rfl) (Or.inl rfl) (by norm_num) ?_
    simpa [T1, zMat] using hν1 1 2
  · refine eq_zero_of_sign_opposite h2 hν13K (Or.inl rfl) (Or.inr rfl) (by norm_num) ?_
    simpa [T1, zMat] using hν1 2 0
  · refine eq_zero_of_sign_opposite h2 hν13K (Or.inl rfl) (Or.inr rfl) (by norm_num) ?_
    simpa [T1, zMat] using hν1 2 1
  · exact absurd rfl hij

omit [Finite K] in
theorem Vproj_eq_closure_range_zProj (h2 : (2 : K) ≠ 0) :
    GH74.Generic.BProg.B2.FixFourS3.Vproj K =
      Subgroup.closure (Set.range (zProj (K := K))) := by
  calc GH74.Generic.BProg.B2.FixFourS3.Vproj K =
      (GH74.Generic.BProg.B2.FixFourS3.Vhat K).map (LinearFlag.proj 3 K) := by
        ext x
        constructor
        · rintro ⟨s, rfl⟩
          exact ⟨s.1, s.2, rfl⟩
        · rintro ⟨s, hs, rfl⟩
          exact ⟨⟨s, hs⟩, rfl⟩
    _ = (signGroup K 3).map (LinearFlag.proj 3 K) := by rw [Vhat_eq_signGroup]
    _ = (Subgroup.closure (Set.range (zElt K (n := 3)))).map (LinearFlag.proj 3 K) := by
        rw [closure_range_zElt h2]
    _ = Subgroup.closure ((Set.range (zElt K (n := 3))).image (LinearFlag.proj 3 K)) := by
        rw [MonoidHom.map_closure]
    _ = Subgroup.closure (Set.range (zProj (K := K))) := by
        congr 1
        ext x
        simp [zProj]

omit [Finite K] in
theorem isElemAbelian_Vproj : IsElemAbelian 2
    (GH74.Generic.BProg.B2.FixFourS3.Vproj K) :=
  @isElemAbelian_of_isElementaryAbelian (LinearFlag.projectiveSL 3 K) _ 2
    (GH74.Generic.BProg.B2.FixFourS3.Vproj K)
    (GH74.Generic.BProg.B2.FixFourS3.isElementaryAbelian_Vproj)

theorem card_Vproj (h2 : (2 : K) ≠ 0) :
    Nat.card (GH74.Generic.BProg.B2.FixFourS3.Vproj K) = 4 :=
  GH74.Generic.BProg.B2.FixFourS3.card_Vproj h2

theorem card_mulAut_Vproj (h2 : (2 : K) ≠ 0) :
    Nat.card (MulAut ↥(GH74.Generic.BProg.B2.FixFourS3.Vproj K)) = 6 :=
  CFSG.Quasithin.card_mulAut_of_card_four
    (isElemAbelian_Vproj (K := K)) (card_Vproj h2)

theorem rho_not_mem_centralizer (h2 : (2 : K) ≠ 0) :
    rho (K := K) ∉ Subgroup.centralizer
      (GH74.Generic.BProg.B2.FixFourS3.Vproj K : Set (LinearFlag.projectiveSL 3 K)) := by
  intro h
  let T : Pair 3 := ⟨{0, 1}, by decide⟩
  have hcomm : rho (K := K) * zProj (K := K) T = zProj (K := K) T * rho (K := K) :=
    (Subgroup.mem_centralizer_iff.mp h (zProj T) (zProj_mem_Vproj T)).symm
  have hfix : rho (K := K) * zProj (K := K) T * (rho (K := K))⁻¹ = zProj (K := K) T := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [zProj_conj_rho] at hfix
  have hp : Pair.map threeCycle T = T := zProj_injective h2 hfix
  exact absurd hp (by decide)

theorem sigma_not_mem_centralizer (h2 : (2 : K) ≠ 0) :
    sigma (K := K) ∉ Subgroup.centralizer
      (GH74.Generic.BProg.B2.FixFourS3.Vproj K : Set (LinearFlag.projectiveSL 3 K)) := by
  intro h
  let T : Pair 3 := ⟨{0, 2}, by decide⟩
  have hcomm : sigma (K := K) * zProj (K := K) T = zProj (K := K) T * sigma (K := K) :=
    (Subgroup.mem_centralizer_iff.mp h (zProj T) (zProj_mem_Vproj T)).symm
  have hfix : sigma (K := K) * zProj (K := K) T * (sigma (K := K))⁻¹ = zProj (K := K) T := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [zProj_conj_sigma] at hfix
  have hp : Pair.map swap01 T = T := zProj_injective h2 hfix
  exact absurd hp (by decide)

omit [Finite K] in
theorem centralizer_Vproj_isMulCommutative (h2 : (2 : K) ≠ 0) :
    IsMulCommutative ↥(Subgroup.centralizer
      (GH74.Generic.BProg.B2.FixFourS3.Vproj K : Set (LinearFlag.projectiveSL 3 K))) := by
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨A, hA⟩ := (LinearFlag.proj_surjective (n := 3) (K := K))
    (x : LinearFlag.projectiveSL 3 K)
  obtain ⟨B, hB⟩ := (LinearFlag.proj_surjective (n := 3) (K := K))
    (y : LinearFlag.projectiveSL 3 K)
  have hxA : LinearFlag.proj 3 K A ∈ Subgroup.centralizer
      (GH74.Generic.BProg.B2.FixFourS3.Vproj K : Set (LinearFlag.projectiveSL 3 K)) := by
    simp [hA]
  have hyB : LinearFlag.proj 3 K B ∈ Subgroup.centralizer
      (GH74.Generic.BProg.B2.FixFourS3.Vproj K : Set (LinearFlag.projectiveSL 3 K)) := by
    simp [hB]
  have hAdiag := isDiag_of_mem_centralizer_Vproj h2 hxA
  have hBdiag := isDiag_of_mem_centralizer_Vproj h2 hyB
  have hcomm : A * B = B * A := sl_diag_commute (F := K) hAdiag hBdiag
  apply Subtype.ext
  change (x : LinearFlag.projectiveSL 3 K) * (y : LinearFlag.projectiveSL 3 K) =
    (y : LinearFlag.projectiveSL 3 K) * (x : LinearFlag.projectiveSL 3 K)
  rw [← hA, ← hB, ← map_mul, ← map_mul, hcomm]

omit [Finite K] in
theorem commutator_centralizer_Vproj_eq_bot (h2 : (2 : K) ≠ 0) :
    ⁅Subgroup.centralizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
        Set (LinearFlag.projectiveSL 3 K)),
      Subgroup.centralizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
        Set (LinearFlag.projectiveSL 3 K))⁆ = ⊥ :=
  Subgroup.commutator_self_eq_bot_iff.mpr (centralizer_Vproj_isMulCommutative h2)

omit [Finite K] in
theorem rho_mem_normalizer (h2 : (2 : K) ≠ 0) :
    rho (K := K) ∈ Subgroup.normalizer
      (GH74.Generic.BProg.B2.FixFourS3.Vproj K : Set (LinearFlag.projectiveSL 3 K)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Vproj_eq_closure_range_zProj h2, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨T, rfl⟩, rfl⟩
    refine ⟨Pair.map threeCycle T, ?_⟩
    exact (zProj_conj_rho T).symm
  · rintro ⟨T, rfl⟩
    refine ⟨zProj (Pair.map threeCycle⁻¹ T), ⟨Pair.map threeCycle⁻¹ T, rfl⟩, ?_⟩
    change rho (K := K) * zProj (K := K) (Pair.map threeCycle⁻¹ T) * (rho (K := K))⁻¹ =
      zProj (K := K) T
    rw [zProj_conj_rho]
    congr 1
    apply Subtype.ext
    simp only [Pair.map, Finset.map_map]
    simp

omit [Finite K] in
theorem sigma_mem_normalizer (h2 : (2 : K) ≠ 0) :
    sigma (K := K) ∈ Subgroup.normalizer
      (GH74.Generic.BProg.B2.FixFourS3.Vproj K : Set (LinearFlag.projectiveSL 3 K)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Vproj_eq_closure_range_zProj h2, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨T, rfl⟩, rfl⟩
    refine ⟨Pair.map swap01 T, ?_⟩
    exact (zProj_conj_sigma T).symm
  · rintro ⟨T, rfl⟩
    refine ⟨zProj (Pair.map swap01⁻¹ T), ⟨Pair.map swap01⁻¹ T, rfl⟩, ?_⟩
    change sigma (K := K) * zProj (K := K) (Pair.map swap01⁻¹ T) * (sigma (K := K))⁻¹ =
      zProj (K := K) T
    rw [zProj_conj_sigma]
    congr 1
    apply Subtype.ext
    simp only [Pair.map, Finset.map_map]
    simp

theorem exists_monomial_frame_Vproj (h2 : (2 : K) ≠ 0) :
    ⁅Subgroup.centralizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
        Set (LinearFlag.projectiveSL 3 K)),
      Subgroup.centralizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
        Set (LinearFlag.projectiveSL 3 K))⁆ = ⊥ ∧
      (Subgroup.centralizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
        Set (LinearFlag.projectiveSL 3 K))).relIndex
        (Subgroup.normalizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
          Set (LinearFlag.projectiveSL 3 K))) = 6 ∧
      ∃ X0 : Subgroup (LinearFlag.projectiveSL 3 K),
        X0 ≤ Subgroup.normalizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
          Set (LinearFlag.projectiveSL 3 K)) ∧
        X0 ⊓ Subgroup.centralizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
          Set (LinearFlag.projectiveSL 3 K)) =
          pCoreOf 2 (Subgroup.centralizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
            Set (LinearFlag.projectiveSL 3 K))) ∧
        X0 ⊔ Subgroup.centralizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
          Set (LinearFlag.projectiveSL 3 K)) =
          Subgroup.normalizer (GH74.Generic.BProg.B2.FixFourS3.Vproj K :
            Set (LinearFlag.projectiveSL 3 K)) := by
  classical
  let V0 : Subgroup (LinearFlag.projectiveSL 3 K) :=
    GH74.Generic.BProg.B2.FixFourS3.Vproj K
  let C : Subgroup (LinearFlag.projectiveSL 3 K) :=
    Subgroup.centralizer (V0 : Set (LinearFlag.projectiveSL 3 K))
  let N : Subgroup (LinearFlag.projectiveSL 3 K) :=
    Subgroup.normalizer (V0 : Set (LinearFlag.projectiveSL 3 K))
  let O : Subgroup (LinearFlag.projectiveSL 3 K) := pCoreOf 2 C
  let S : Subgroup (LinearFlag.projectiveSL 3 K) :=
    Subgroup.closure ({rho (K := K), sigma (K := K)} : Set (LinearFlag.projectiveSL 3 K))
  have hC_le_N : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hSleN : S ≤ N := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact rho_mem_normalizer (K := K) h2
    · exact sigma_mem_normalizer (K := K) h2
  have hSle6 : Nat.card S ≤ 6 :=
    card_closure_le_six (rho_pow_three (K := K))
      (by simpa [pow_two] using sigma_mul_self (K := K))
      (sigma_mul_rho_mul_sigma_mul_rho (K := K))
  let f : N →* MulAut ↥V0 := V0.normalizerMonoidHom
  let fS : S →* MulAut ↥V0 := f.comp (Subgroup.inclusion hSleN)
  have hker : f.ker = C.subgroupOf N := by
    simpa [f, V0, C, N] using
      (Subgroup.normalizerMonoidHom_ker (H := V0))
  have hkerS : fS.ker = (S ⊓ C).subgroupOf S := by
    ext x
    change f ((Subgroup.inclusion hSleN) x) = 1 ↔ ((x : LinearFlag.projectiveSL 3 K) ∈ S ∧
      (x : LinearFlag.projectiveSL 3 K) ∈ C)
    rw [← MonoidHom.mem_ker, hker]
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hmem_rhoS : rho (K := K) ∈ S := Subgroup.subset_closure (by simp)
  have hmem_sigmaS : sigma (K := K) ∈ S := Subgroup.subset_closure (by simp)
  have hord3 : orderOf (fS ⟨rho (K := K), hmem_rhoS⟩) = 3 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      rw [show (⟨rho (K := K), hmem_rhoS⟩ : S) ^ 3 = 1 by
        apply Subtype.ext
        simpa using rho_pow_three (K := K)]
      rw [map_one]
    · intro h1
      have hmem : (⟨rho (K := K), hmem_rhoS⟩ : S) ∈ fS.ker := by rwa [MonoidHom.mem_ker]
      rw [hkerS] at hmem
      have hxC : rho (K := K) ∈ C := (Subgroup.mem_subgroupOf.mp hmem).2
      exact rho_not_mem_centralizer (K := K) h2 (by simpa [C, V0] using hxC)
  have hord2 : orderOf (fS ⟨sigma (K := K), hmem_sigmaS⟩) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      rw [show (⟨sigma (K := K), hmem_sigmaS⟩ : S) ^ 2 = 1 by
        apply Subtype.ext
        simpa [pow_two] using sigma_mul_self (K := K)]
      rw [map_one]
    · intro h1
      have hmem : (⟨sigma (K := K), hmem_sigmaS⟩ : S) ∈ fS.ker := by rwa [MonoidHom.mem_ker]
      rw [hkerS] at hmem
      have hxC : sigma (K := K) ∈ C := (Subgroup.mem_subgroupOf.mp hmem).2
      exact sigma_not_mem_centralizer (K := K) h2 (by simpa [C, V0] using hxC)
  have hdiv3 : 3 ∣ Nat.card fS.range := by
    have hxmem : fS ⟨rho (K := K), hmem_rhoS⟩ ∈ fS.range := ⟨_, rfl⟩
    have := orderOf_dvd_natCard (⟨fS ⟨rho (K := K), hmem_rhoS⟩, hxmem⟩ : fS.range)
    simpa [hord3] using this
  have hdiv2 : 2 ∣ Nat.card fS.range := by
    have hxmem : fS ⟨sigma (K := K), hmem_sigmaS⟩ ∈ fS.range := ⟨_, rfl⟩
    have := orderOf_dvd_natCard (⟨fS ⟨sigma (K := K), hmem_sigmaS⟩, hxmem⟩ : fS.range)
    simpa [hord2] using this
  have hdiv6 : 6 ∣ Nat.card fS.range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) hdiv2 hdiv3
  have hfs_le6 : Nat.card fS.range ≤ 6 := by
    have hdvd : Nat.card fS.range ∣ Nat.card (MulAut ↥V0) :=
      Subgroup.card_subgroup_dvd_card fS.range
    rw [card_mulAut_Vproj (K := K) h2] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hfs_card : Nat.card fS.range = 6 :=
    Nat.le_antisymm hfs_le6 (Nat.le_of_dvd Nat.card_pos hdiv6)
  have hf_range : Nat.card f.range = 6 := by
    have hle : fS.range ≤ f.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨(x : S), hSleN x.2⟩, rfl⟩
    have hge : Nat.card f.range ≥ 6 := by
      calc 6 = Nat.card fS.range := hfs_card.symm
        _ ≤ Nat.card f.range := Subgroup.card_le_of_le hle
    have hle6 : Nat.card f.range ≤ 6 := by
      have hdvd : Nat.card f.range ∣ Nat.card (MulAut ↥V0) :=
        Subgroup.card_subgroup_dvd_card f.range
      rw [card_mulAut_Vproj (K := K) h2] at hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd
    exact Nat.le_antisymm hle6 hge
  have hrelIndex : C.relIndex N = 6 := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact hf_range
  have hcard_ker_S : Nat.card fS.ker = 1 := by
    have h := Subgroup.card_ker_mul_card_range fS
    rw [hfs_card] at h
    have hle : Nat.card fS.ker * 6 ≤ 6 := by
      rw [h]
      exact hSle6
    have hle' : Nat.card fS.ker * 6 ≤ 1 * 6 := by simpa using hle
    have hle1 : Nat.card fS.ker ≤ 1 :=
      Nat.le_of_mul_le_mul_right hle' (by norm_num)
    exact Nat.le_antisymm hle1 Nat.card_pos
  have hcard_SC : Nat.card ↥(S ⊓ C) = 1 := by
    have h := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : S ⊓ C ≤ S)).toEquiv
    rw [← h, ← hkerS]
    exact hcard_ker_S
  have hSC_bot : S ⊓ C = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    exact hcard_SC
  have hS_card : Nat.card ↥S = 6 := by
    have h := Subgroup.card_ker_mul_card_range fS
    rw [hcard_ker_S, hfs_card, one_mul] at h
    exact h.symm
  have hcard_ker_N : Nat.card f.ker = Nat.card C := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_N).toEquiv
  have hN_card : Nat.card N = 6 * Nat.card C := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hcard_ker_N, hf_range] at h
    rw [← h]
    ring
  have hcard_sup_SC : Nat.card ↥(S ⊔ C) = 6 * Nat.card ↥C := by
    have hnormal : (C.subgroupOf N).Normal := by
      change ((Subgroup.centralizer (V0 : Set (LinearFlag.projectiveSL 3 K))).subgroupOf
        (Subgroup.normalizer (V0 : Set (LinearFlag.projectiveSL 3 K)))).Normal
      infer_instance
    have h := @CFSG.Walter.W67.card_sup_mul_card_inf_of_normal (↥N) _
      (C.subgroupOf N) (S.subgroupOf N) hnormal
    have hsup : (C.subgroupOf N) ⊔ (S.subgroupOf N) = (C ⊔ S).subgroupOf N :=
      (Subgroup.subgroupOf_sup hC_le_N hSleN).symm
    have hinf : (C.subgroupOf N) ⊓ (S.subgroupOf N) = (C ⊓ S).subgroupOf N := by
      ext x
      simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hcard_sup : Nat.card ↥((C ⊔ S).subgroupOf N) = Nat.card ↥(C ⊔ S) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hC_le_N hSleN)).toEquiv
    have hcard_inf : Nat.card ((C ⊓ S).subgroupOf N) = 1 := by
      have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left.trans hC_le_N : C ⊓ S ≤ N)).toEquiv
      rw [h, inf_comm, hSC_bot]
      simp
    have hcardC : Nat.card (C.subgroupOf N) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_N).toEquiv
    have hcardS : Nat.card (S.subgroupOf N) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleN).toEquiv
    rw [hsup, hinf, hcard_sup, hcard_inf, hcardC, hcardS, hS_card] at h
    rw [mul_one, mul_comm] at h
    simpa [sup_comm] using h
  have hSC_sup : S ⊔ C = N := by
    have hle : S ⊔ C ≤ N := sup_le hSleN hC_le_N
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hN_card, hcard_sup_SC]
  have hO_le_C : O ≤ C := CFSG.LieType.BorelTits.pCoreOf_le (r := 2) C
  refine ⟨?_, ?_, O ⊔ S, ?_, ?_, ?_⟩
  · simpa [C, V0] using commutator_centralizer_Vproj_eq_bot (K := K) h2
  · simpa [C, N, V0] using hrelIndex
  · exact sup_le (hO_le_C.trans hC_le_N) hSleN
  · have hN_normC : N ≤ Subgroup.normalizer (C : Set (LinearFlag.projectiveSL 3 K)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_N).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (s := (V0 : Set
          (LinearFlag.projectiveSL 3 K))))
    have hN_normO : N ≤ Subgroup.normalizer (O : Set (LinearFlag.projectiveSL 3 K)) :=
      hN_normC.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) C)
    have hSO : S ≤ Subgroup.normalizer (O : Set (LinearFlag.projectiveSL 3 K)) :=
      hSleN.trans hN_normO
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨hxOS, hxC⟩
      have hxSO : x ∈ (↑(S ⊔ O) : Set (LinearFlag.projectiveSL 3 K)) := by
        simpa [sup_comm] using hxOS
      rw [Subgroup.coe_mul_of_left_le_normalizer_right S O hSO] at hxSO
      rcases hxSO with ⟨s, hs, o, ho, rfl⟩
      have hoC : o ∈ C := hO_le_C ho
      have hsC : s ∈ C := by
        have h : (s * o) * o⁻¹ ∈ C := C.mul_mem hxC (C.inv_mem hoC)
        simpa [mul_assoc] using h
      have hsbot : s ∈ S ⊓ C := Subgroup.mem_inf.mpr ⟨hs, hsC⟩
      rw [hSC_bot] at hsbot
      have hs1 : s = 1 := Subgroup.mem_bot.mp hsbot
      simpa [hs1] using ho
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hx, hO_le_C hx⟩
  · calc (O ⊔ S) ⊔ C = O ⊔ (S ⊔ C) := sup_assoc O S C
      _ = O ⊔ N := by rw [hSC_sup]
      _ = N := sup_eq_right.mpr (hO_le_C.trans hC_le_N)

end Model

def HasMonomialFrame (C N : Subgroup Q) : Prop :=
  ⁅C, C⁆ = ⊥ ∧ C.relIndex N = 6 ∧
    ∃ X₀ : Subgroup Q, X₀ ≤ N ∧ X₀ ⊓ C = pCoreOf 2 C ∧ X₀ ⊔ C = N

theorem HasMonomialFrame.map_mulEquiv {X Y : Type} [Group X] [Group Y]
    {C N : Subgroup X} (h : HasMonomialFrame C N) (e : X ≃* Y) :
    HasMonomialFrame (C.map e.toMonoidHom) (N.map e.toMonoidHom) := by
  rcases h with ⟨hcomm, hidx, X₀, hX₀N, hX₀C, hX₀sup⟩
  refine ⟨?_, ?_, X₀.map e.toMonoidHom, Subgroup.map_mono hX₀N, ?_, ?_⟩
  · rw [← Subgroup.map_commutator (f := e.toMonoidHom) (H₁ := C) (H₂ := C), hcomm,
      Subgroup.map_bot]
  · rw [Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) (H := C) (K := N)
      e.injective, hidx]
  · rw [← Subgroup.map_inf (f := e.toMonoidHom) (H := X₀) (K := C) e.injective, hX₀C,
      CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
  · rw [← Subgroup.map_sup (f := e.toMonoidHom) (H := X₀) (K := C), hX₀sup]

theorem HasMonomialFrame.map_subtype {X : Type} [Group X] {L : Subgroup X}
    {C N : Subgroup ↥L} (h : HasMonomialFrame C N) :
    HasMonomialFrame (C.map L.subtype) (N.map L.subtype) := by
  rcases h with ⟨hcomm, hidx, X₀, hX₀N, hX₀C, hX₀sup⟩
  refine ⟨?_, ?_, X₀.map L.subtype, Subgroup.map_mono hX₀N, ?_, ?_⟩
  · rw [← Subgroup.map_commutator (f := L.subtype) (H₁ := C) (H₂ := C), hcomm,
      Subgroup.map_bot]
  · rw [Subgroup.relIndex_map_map_of_injective (f := L.subtype) (H := C) (K := N)
      L.subtype_injective, hidx]
  · rw [← Subgroup.map_inf (f := L.subtype) (H := X₀) (K := C) L.subtype_injective, hX₀C,
      CFSG.ASVolI.ChH.pCoreOf_map_of_injective 2 L.subtype L.subtype_injective C]
  · rw [← Subgroup.map_sup (f := L.subtype) (H := X₀) (K := C), hX₀sup]

theorem centralizer_subgroupOf_map_subtype {G : Type} [Group G] {W L : Subgroup G}
    (hWL : W ≤ L) :
    (Subgroup.centralizer (W.subgroupOf L : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.centralizer (W : Set G) := by
  have h : Subgroup.centralizer (W.subgroupOf L : Set ↥L) =
      (Subgroup.centralizer (W : Set G)).subgroupOf L := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx w hw
      have hmem : (⟨w, hWL hw⟩ : ↥L) ∈ W.subgroupOf L :=
        Subgroup.mem_subgroupOf.mpr hw
      exact congrArg Subtype.val (hx ⟨w, hWL hw⟩ hmem)
    · intro hx y hy
      apply Subtype.ext
      exact hx y.1 (Subgroup.mem_subgroupOf.mp hy)
  rw [h, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem normalizer_subgroupOf_map_subtype {G : Type} [Group G] {W L : Subgroup G}
    (hWL : W ≤ L) :
    (Subgroup.normalizer (W.subgroupOf L : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.normalizer (W : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hWL, Subgroup.subgroupOf_map_subtype, inf_comm]

open CFSG.LocalAnalysis.ComponentInitial

theorem exists_monomial_frame_psl3 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L : Subgroup Q}
    (e : ↥L ≃* PSL3 p) {W : Subgroup Q} (hWL : W ≤ L) (hW : IsElemAbelian 2 W)
    (hW4 : Nat.card W = 4) :
    ⁅L ⊓ centralizer (W : Set Q), L ⊓ centralizer (W : Set Q)⁆ = ⊥ ∧
      (L ⊓ centralizer (W : Set Q)).relIndex (L ⊓ normalizer (W : Set Q)) = 6 ∧
      ∃ X₀ : Subgroup Q, X₀ ≤ L ⊓ normalizer (W : Set Q) ∧
        X₀ ⊓ (L ⊓ centralizer (W : Set Q)) = pCoreOf 2 (L ⊓ centralizer (W : Set Q)) ∧
        X₀ ⊔ (L ⊓ centralizer (W : Set Q)) = L ⊓ normalizer (W : Set Q) := by
  classical
  have hQ : Finite Q := ‹Finite Q›
  let K := ZMod p
  have h2 : (2 : K) ≠ 0 := by
    dsimp [K]
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hzero)
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hp_ge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hchar : ringChar K ≠ 2 := by
    dsimp [K]
    intro hc
    have h : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
    exact hp2 (h.symm.trans hc)
  have ePSL : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod p) := e
  let e' : ↥L ≃* LinearFlag.projectiveSL 3 (ZMod p) :=
    ePSL.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 (ZMod p))
  let W' : Subgroup (LinearFlag.projectiveSL 3 (ZMod p)) :=
    (W.subgroupOf L).map e'.toMonoidHom
  have hW'card : Nat.card ↥W' = 4 := by
    rw [Subgroup.card_map_of_injective e'.injective]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv]
    exact hW4
  have hW'elem : IsElemAbelian 2 W' :=
    (hW.subgroupOf L).map e'.toMonoidHom
  have hW'elem' : CFSG.IsElementaryAbelian 2 ↥W' :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hW'elem
  obtain ⟨s, hs⟩ :=
    CFSG.GH74.Generic.BProg.B2.FixFourS3.exists_conj_four_projectiveSL3 (F := K) hchar
      hW'elem' hW'card
      (CFSG.GH74.Generic.BProg.B2.FixFourS3.isElementaryAbelian_Vproj)
      (card_Vproj (K := K) h2)
  let g : LinearFlag.projectiveSL 3 K := LinearFlag.proj 3 K s
  let econj : LinearFlag.projectiveSL 3 K ≃* LinearFlag.projectiveSL 3 K :=
    (MulAut.conj g).symm
  have hW'_eq : W' =
      (CFSG.GH74.Generic.BProg.B2.FixFourS3.Vproj K).map econj.toMonoidHom := by
    have hcomp : econj.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (LinearFlag.projectiveSL 3 (ZMod p)) := by
      ext x
      simp [econj]
    have h := congrArg (Subgroup.map econj.toMonoidHom) hs.symm
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
    exact h
  have hVframe : HasMonomialFrame
      (Subgroup.centralizer (CFSG.GH74.Generic.BProg.B2.FixFourS3.Vproj K :
        Set (LinearFlag.projectiveSL 3 K)))
      (Subgroup.normalizer (CFSG.GH74.Generic.BProg.B2.FixFourS3.Vproj K :
        Set (LinearFlag.projectiveSL 3 K))) :=
    exists_monomial_frame_Vproj (K := K) h2
  have hW'frame : HasMonomialFrame
      (Subgroup.centralizer (W' : Set (LinearFlag.projectiveSL 3 K)))
      (Subgroup.normalizer (W' : Set (LinearFlag.projectiveSL 3 K))) := by
    have hmap := hVframe.map_mulEquiv econj
    have hcen : (Subgroup.centralizer
        (CFSG.GH74.Generic.BProg.B2.FixFourS3.Vproj K :
          Set (LinearFlag.projectiveSL 3 K))).map econj.toMonoidHom =
        Subgroup.centralizer (W' : Set (LinearFlag.projectiveSL 3 K)) := by
      have hset : econj '' (CFSG.GH74.Generic.BProg.B2.FixFourS3.Vproj K :
          Set (LinearFlag.projectiveSL 3 K)) = (W' : Set (LinearFlag.projectiveSL 3 K)) := by
        change ((CFSG.GH74.Generic.BProg.B2.FixFourS3.Vproj K).map econj.toMonoidHom :
          Set (LinearFlag.projectiveSL 3 K)) = (W' : Set (LinearFlag.projectiveSL 3 K))
        rw [← hW'_eq]
      have h := CFSG.Fischer.centralizer_image_eq_map econj
        (CFSG.GH74.Generic.BProg.B2.FixFourS3.Vproj K :
          Set (LinearFlag.projectiveSL 3 K))
      rw [hset] at h
      exact h.symm
    have hnorm : (Subgroup.normalizer
        (CFSG.GH74.Generic.BProg.B2.FixFourS3.Vproj K :
          Set (LinearFlag.projectiveSL 3 K))).map econj.toMonoidHom =
        Subgroup.normalizer (W' : Set (LinearFlag.projectiveSL 3 K)) := by
      rw [Subgroup.map_normalizer_eq_of_bijective _ econj.bijective, ← hW'_eq]
    rwa [hcen, hnorm] at hmap
  let CL : Subgroup ↥L :=
    Subgroup.centralizer ((W.subgroupOf L : Subgroup ↥L) : Set ↥L)
  let NL : Subgroup ↥L :=
    Subgroup.normalizer ((W.subgroupOf L : Subgroup ↥L) : Set ↥L)
  have hLframe : HasMonomialFrame CL NL := by
    have hmap := hW'frame.map_mulEquiv e'.symm
    have hW'map : W'.map e'.symm.toMonoidHom = W.subgroupOf L := by
      rw [show W' = (W.subgroupOf L).map e'.toMonoidHom from rfl, Subgroup.map_map]
      simp
    have hcen : (Subgroup.centralizer (W' : Set (LinearFlag.projectiveSL 3 K))).map
        e'.symm.toMonoidHom = CL := by
      have hset : e'.symm '' (W' : Set (LinearFlag.projectiveSL 3 K)) =
          ((W.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        change (W'.map e'.symm.toMonoidHom : Set ↥L) =
          ((W.subgroupOf L : Subgroup ↥L) : Set ↥L)
        rw [hW'map]
      have h := CFSG.Fischer.centralizer_image_eq_map e'.symm
        (W' : Set (LinearFlag.projectiveSL 3 K))
      rw [hset] at h
      exact h.symm
    have hnorm : (Subgroup.normalizer (W' : Set (LinearFlag.projectiveSL 3 K))).map
        e'.symm.toMonoidHom = NL := by
      rw [Subgroup.map_normalizer_eq_of_bijective _ e'.symm.bijective, hW'map]
    rwa [hcen, hnorm] at hmap
  have hCQ : CL.map L.subtype = L ⊓ Subgroup.centralizer (W : Set Q) := by
    dsimp [CL]
    exact centralizer_subgroupOf_map_subtype hWL
  have hNQ : NL.map L.subtype = L ⊓ Subgroup.normalizer (W : Set Q) := by
    dsimp [NL]
    exact normalizer_subgroupOf_map_subtype hWL
  have hQframe : HasMonomialFrame (L ⊓ Subgroup.centralizer (W : Set Q))
      (L ⊓ Subgroup.normalizer (W : Set Q)) := by
    have hmap := hLframe.map_subtype
    rwa [hCQ, hNQ] at hmap
  exact hQframe

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
