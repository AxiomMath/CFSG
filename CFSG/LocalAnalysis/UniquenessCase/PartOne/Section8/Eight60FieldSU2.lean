module

public import CFSG.Open.StatedDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSUArith
import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix
open CFSG.Open (StatedSU)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

private noncomputable def su2DiagHom (K : Type) [Field K] : Kˣ →* GL (Fin 2) K where
  toFun u := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal ![(u : K), ((u⁻¹ : Kˣ) : K)])
    (by rw [Matrix.det_diagonal, Fin.prod_univ_two]; simp)
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.diagonal]
  map_mul' u v := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.diagonal_mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Units.val_mul, mul_comm]

private theorem su2DiagHom_apply (K : Type) [Field K] (u : Kˣ) :
    ((su2DiagHom K u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![(u : K), ((u⁻¹ : Kˣ) : K)] :=
  rfl

private theorem su2DiagHom_injective (K : Type) [Field K] :
    Function.Injective (su2DiagHom K) := by
  intro u v huv
  have h := congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K) 0 0) huv
  rw [su2DiagHom_apply, su2DiagHom_apply] at h
  apply Units.ext
  simpa [Matrix.diagonal] using h

private noncomputable def su2TorusHom {K : Type} [Field K] (P : GL (Fin 2) K) :
    Kˣ →* GL (Fin 2) K where
  toFun u := P * su2DiagHom K u * P⁻¹
  map_one' := by simp
  map_mul' u v := by simp [mul_assoc]

private theorem su2TorusHom_apply {K : Type} [Field K] (P : GL (Fin 2) K) (u : Kˣ) :
    su2TorusHom P u = P * su2DiagHom K u * P⁻¹ := rfl

private theorem su2TorusHom_injective {K : Type} [Field K] (P : GL (Fin 2) K) :
    Function.Injective (su2TorusHom P) := by
  intro u v huv
  have h := congrArg (fun x => P⁻¹ * x * P) huv
  simp only [su2TorusHom_apply] at h
  have h' : su2DiagHom K u = su2DiagHom K v := by
    simpa [mul_assoc] using h
  exact su2DiagHom_injective K h'

private noncomputable def su2TorusSub (q : ℕ) (K : Type) [Field K] : Subgroup Kˣ :=
  (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker

private theorem su2TorusSub_mem {q : ℕ} {K : Type} [Field K] {u : Kˣ} :
    u ∈ su2TorusSub q K ↔ u ^ (q - 1) = 1 := by
  rw [su2TorusSub, MonoidHom.mem_ker, powMonoidHom_apply]

private theorem su2TorusSub_card {p f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (su2TorusSub (p ^ f) K) = p ^ f - 1 := by
  have hcard_units : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
    rw [Nat.card_units, hK]
  rw [su2TorusSub, IsCyclic.card_powMonoidHom_ker, hcard_units]
  have hfac : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    simpa [pow_two, mul_comm] using Nat.mul_self_sub_mul_self_eq (p ^ f) 1
  rw [hfac, Nat.gcd_eq_right]
  exact ⟨p ^ f + 1, by rw [mul_comm]⟩

private theorem su2_diag_mul_antiDiag {K : Type} [Field K] (a : Kˣ) (β β' : K) :
    Matrix.diagonal ![(a : K), ((a⁻¹ : Kˣ) : K)] * !![0, β; β', 0] *
      Matrix.diagonal ![(a : K), ((a⁻¹ : Kˣ) : K)] = !![0, β; β', 0] := by
  rw [Matrix.diagonal_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_inv_eq_inv_val, mul_comm]

private theorem su2_G_eq {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {c c' : K} (hc : c ^ (p ^ f + 1) = -1) (hc' : c' ^ (p ^ f + 1) = -1)
    (P : GL (Fin 2) K) (hP : (P : Matrix (Fin 2) (Fin 2) K) = !![1, 1; c, c']) :
    (((P : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * (P : Matrix (Fin 2) (Fin 2) K)) =
      !![0, 1 + h.bar c * c'; 1 + h.bar c' * c, 0] := by
  have hd0 : 1 + h.bar c * c = 0 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, ← pow_succ, hc]
    ring
  have hd1 : 1 + h.bar c' * c' = 0 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, ← pow_succ, hc']
    ring
  rw [hP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply, hd0, hd1]

private theorem su2_diagHom_bar {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {a : Kˣ} (haq : (a : K) ^ (p ^ f) = (a : K)) :
    ((su2DiagHom K a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map h.bar =
      ((su2DiagHom K a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  rw [su2DiagHom_apply]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.map_apply, Matrix.diagonal,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, haq]
  · simp [Matrix.map_apply, Matrix.diagonal]
  · simp [Matrix.map_apply, Matrix.diagonal]
  · simp [Matrix.map_apply, Matrix.diagonal,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, haq,
      Units.val_inv_eq_inv_val]

private theorem su2_unitary_aux {K : Type} [Field K] (φ : K →+* K)
    (P : GL (Fin 2) K) (a : Kˣ) (β β' : K)
    (hD : ((su2DiagHom K a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map φ =
      ((su2DiagHom K a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (hG : (((P : Matrix (Fin 2) (Fin 2) K).map φ)ᵀ * (P : Matrix (Fin 2) (Fin 2) K)) =
      !![0, β; β', 0]) :
    ((((P * su2DiagHom K a * P⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).map φ)ᵀ) *
      (((P * su2DiagHom K a * P⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) = 1 := by
  let D : GL (Fin 2) K := su2DiagHom K a
  let A : GL (Fin 2) K := P * D * P⁻¹
  let Pbar : GL (Fin 2) K := Matrix.GeneralLinearGroup.map φ P
  let Abar : GL (Fin 2) K := Matrix.GeneralLinearGroup.map φ A
  let Dbar : GL (Fin 2) K := Matrix.GeneralLinearGroup.map φ D
  let Pm : Matrix (Fin 2) (Fin 2) K := (P : Matrix (Fin 2) (Fin 2) K)
  let Dm : Matrix (Fin 2) (Fin 2) K := (D : Matrix (Fin 2) (Fin 2) K)
  let Pbm : Matrix (Fin 2) (Fin 2) K := (Pbar : Matrix (Fin 2) (Fin 2) K)
  have hDm : Dm = Matrix.diagonal ![(a : K), ((a⁻¹ : Kˣ) : K)] := su2DiagHom_apply K a
  have hDm_map : Dm.map φ = Dm := hD
  have hDbar_val : (Dbar : Matrix (Fin 2) (Fin 2) K) = Dm := hDm_map
  have hA : (A : Matrix (Fin 2) (Fin 2) K) = Pm * Dm * Pm⁻¹ := by
    simp only [A, Pm, Dm, D, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv]
  have hAbar_eq : Abar = Pbar * Dbar * Pbar⁻¹ := by
    simp only [Abar, A, Pbar, Dbar, D, Matrix.GeneralLinearGroup.map_mul,
      Matrix.GeneralLinearGroup.map_inv]
  have hAbar : (Abar : Matrix (Fin 2) (Fin 2) K) = Pbm * Dm * Pbm⁻¹ := by
    rw [hAbar_eq, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv, hDbar_val]
  have hDmT : Dmᵀ = Dm := by
    rw [hDm, Matrix.diagonal_transpose]
  have hG' : Pbmᵀ * Pm = !![0, β; β', 0] := hG
  have hDGD : Dm * (Pbmᵀ * Pm) * Dm = Pbmᵀ * Pm := by
    rw [hG', hDm]
    exact su2_diag_mul_antiDiag a β β'
  have hPbmInv : (Pbm⁻¹)ᵀ * Pbmᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have h1 : Pbm * Pbm⁻¹ = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
    rw [h1, Matrix.transpose_one]
  have hPmInv : Pm * Pm⁻¹ = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  calc
    ((A : Matrix (Fin 2) (Fin 2) K).map φ)ᵀ * (A : Matrix (Fin 2) (Fin 2) K)
        = (Abar : Matrix (Fin 2) (Fin 2) K)ᵀ * (A : Matrix (Fin 2) (Fin 2) K) := rfl
    _ = (Pbm * Dm * Pbm⁻¹)ᵀ * (Pm * Dm * Pm⁻¹) := by rw [hAbar, hA]
    _ = (Pbm⁻¹)ᵀ * Dmᵀ * Pbmᵀ * (Pm * Dm * Pm⁻¹) := by
          simp only [Matrix.transpose_mul, mul_assoc]
    _ = (Pbm⁻¹)ᵀ * Dm * Pbmᵀ * (Pm * Dm * Pm⁻¹) := by rw [hDmT]
    _ = (Pbm⁻¹)ᵀ * (Dm * (Pbmᵀ * Pm) * Dm) * Pm⁻¹ := by
          simp only [mul_assoc]
    _ = (Pbm⁻¹)ᵀ * (Pbmᵀ * Pm) * Pm⁻¹ := by rw [hDGD]
    _ = ((Pbm⁻¹)ᵀ * Pbmᵀ) * (Pm * Pm⁻¹) := by simp only [mul_assoc]
    _ = 1 := by rw [hPbmInv, hPmInv, one_mul]

private theorem su2_torusHom_mem {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    {c c' : K} (hc : c ^ (p ^ f + 1) = -1) (hc' : c' ^ (p ^ f + 1) = -1)
    (P : GL (Fin 2) K) (hP : (P : Matrix (Fin 2) (Fin 2) K) = !![1, 1; c, c'])
    (a : Kˣ) (ha : a ∈ su2TorusSub (p ^ f) K) :
    su2TorusHom P a ∈ StatedSU 2 (p ^ f) K := by
  have hUF : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow f p hp.pos
  have ha' : a ^ (p ^ f - 1) = 1 := (su2TorusSub_mem).mp ha
  have haK : (a : K) ^ (p ^ f) = (a : K) := by
    have h1 : a ^ (p ^ f) = a := by
      rw [← Nat.sub_add_cancel hq1, pow_add, ha', one_mul, pow_one]
    exact congrArg (fun u : Kˣ => (u : K)) h1
  have hDbar : ((su2DiagHom K a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map hUF.bar =
      ((su2DiagHom K a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    su2_diagHom_bar hUF haK
  have hG : (((P : Matrix (Fin 2) (Fin 2) K).map hUF.bar)ᵀ *
      (P : Matrix (Fin 2) (Fin 2) K)) =
      !![0, 1 + hUF.bar c * c'; 1 + hUF.bar c' * c, 0] :=
    su2_G_eq hUF hc hc' P hP
  have hunit : ((((su2TorusHom P a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map
        hUF.bar)ᵀ * ((su2TorusHom P a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
    su2_unitary_aux hUF.bar P a _ _ hDbar hG
  have hdetD : Matrix.GeneralLinearGroup.det (su2DiagHom K a) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, su2DiagHom_apply, Matrix.det_diagonal,
      Fin.prod_univ_two]
    simp
  have hdet : (((su2TorusHom P a : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have hgl : Matrix.GeneralLinearGroup.det (su2TorusHom P a) = 1 := by
      rw [su2TorusHom_apply, map_mul, map_mul, map_inv, hdetD]
      simp
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    simpa using congrArg (fun u : Kˣ => (u : K)) hgl
  have hfun : (fun x : K => x ^ (p ^ f)) = ⇑hUF.bar := by
    funext x
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
  unfold StatedSU
  refine Subgroup.subset_closure ⟨hdet, ?_⟩
  rw [hfun]
  exact hunit

private theorem su2_map_phi_diagHom {K : Type} [Field K] (φ : K →+* K) (a : Kˣ) :
    Matrix.GeneralLinearGroup.map φ (su2DiagHom K a) =
      su2DiagHom K (Units.map (φ : K →* K) a) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.map_apply, su2DiagHom_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Units.coe_map, Units.val_inv_eq_inv_val, map_inv₀]

private theorem su2_map_phi_torusHom {K : Type} [Field K] (φ : K →+* K)
    (P : GL (Fin 2) K) (hP : Matrix.GeneralLinearGroup.map φ P = P) (a : Kˣ) :
    Matrix.GeneralLinearGroup.map φ (su2TorusHom P a) =
      su2TorusHom P (Units.map (φ : K →* K) a) := by
  rw [su2TorusHom_apply, su2TorusHom_apply, Matrix.GeneralLinearGroup.map_mul,
    Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_inv, hP,
    su2_map_phi_diagHom]

private theorem su2_torusHom_pow_map {p f : ℕ} {K : Type} [Field K] (φ : RingAut K)
    (hφ : ∀ x : K, φ x = x ^ ((p ^ (f / 3 ^ (f.factorization 3))) ^ 2))
    (P : GL (Fin 2) K) (hP : Matrix.GeneralLinearGroup.map (φ : K →+* K) P = P)
    (a : Kˣ) :
    Matrix.GeneralLinearGroup.map (φ : K →+* K) (su2TorusHom P a) =
      (su2TorusHom P a) ^ ((p ^ (f / 3 ^ (f.factorization 3))) ^ 2) := by
  rw [su2_map_phi_torusHom (φ : K →+* K) P hP a]
  have hua : Units.map ((φ : K →+* K) : K →* K) a =
      a ^ ((p ^ (f / 3 ^ (f.factorization 3))) ^ 2) := by
    apply Units.ext
    simp only [Units.coe_map, Units.val_pow_eq_pow_val, MonoidHom.coe_coe]
    exact hφ (a : K)
  rw [hua, map_pow]

theorem exists_stable_cyclic_sylow_three_statedSU_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    (φ : RingAut K) (hφ : ∀ x : K, φ x = x ^ ((p ^ (f / 3 ^ (f.factorization 3))) ^ 2)) :
    ∃ (C : Subgroup (GL (Fin 2) K)) (s : ℕ), IsSylowOf 3 C (StatedSU 2 (p ^ f) K) ∧
      IsCyclic C ∧ s % 3 = 1 ∧
      ∀ g ∈ C, Matrix.GeneralLinearGroup.map (φ : K →+* K) g = g ^ s := by
  obtain ⟨c, c', hcne, hcq, hc'q, hφc, hφc'⟩ :=
    exists_fixed_pair_norm_neg_one_statedSU hp hf hK φ hφ
  have hdetP : (!![1, 1; c, c'] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simp only [one_mul]
    exact sub_ne_zero.mpr (Ne.symm hcne)
  let P : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; c, c'] hdetP
  have hP : (P : Matrix (Fin 2) (Fin 2) K) = !![1, 1; c, c'] := rfl
  have hphiP : Matrix.GeneralLinearGroup.map (φ : K →+* K) P = P := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.map_apply, hP]
    fin_cases i <;> fin_cases j <;> simp [hφc, hφc']
  let T0 : Subgroup Kˣ := su2TorusSub (p ^ f) K
  let torusT0 : T0 →* GL (Fin 2) K := (su2TorusHom P).comp T0.subtype
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 T0))
  let C : Subgroup (GL (Fin 2) K) := (S : Subgroup T0).map torusT0
  have hinj : Function.Injective torusT0 :=
    (su2TorusHom_injective P).comp T0.subtype_injective
  have hle : C ≤ StatedSU 2 (p ^ f) K := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := hg
    exact su2_torusHom_mem hp hf hK hcq hc'q P hP ((x : T0) : Kˣ) (x : T0).2
  have hcard : Nat.card C = 3 ^ (Nat.card (StatedSU 2 (p ^ f) K)).factorization 3 := by
    rw [show C = (S : Subgroup T0).map torusT0 from rfl,
      Subgroup.card_map_of_injective hinj, Sylow.card_eq_multiplicity S,
      show Nat.card T0 = p ^ f - 1 from su2TorusSub_card hK,
      ← factorization_three_card_statedSU_two hp hf hq hK]
  have hs : ((p ^ (f / 3 ^ (f.factorization 3))) ^ 2) % 3 = 1 := by
    have hps : p ≠ 3 := by
      intro hp3
      subst hp3
      have hdvd : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega : f ≠ 0)
      have h0 : 3 ^ f % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
      omega
    have h3q0 : ¬ 3 ∣ p ^ (f / 3 ^ (f.factorization 3)) := by
      intro hd
      have h3p : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow hd
      exact hps ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p).symm
    have hne : ((p ^ (f / 3 ^ (f.factorization 3)) : ℕ) : ZMod 3) ≠ 0 := by
      intro h
      exact h3q0 ((ZMod.natCast_eq_zero_iff _ 3).mp h)
    have hsq : ((p ^ (f / 3 ^ (f.factorization 3)) : ℕ) : ZMod 3) ^ 2 = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one (p := 3) hne
    have hs3 : (((p ^ (f / 3 ^ (f.factorization 3))) ^ 2 : ℕ) : ZMod 3) = 1 := by
      rw [Nat.cast_pow]
      exact hsq
    have hmod : (((p ^ (f / 3 ^ (f.factorization 3))) ^ 2 : ℕ) : ZMod 3) =
        ((1 : ℕ) : ZMod 3) := hs3
    have hmod2 := (ZMod.natCast_eq_natCast_iff' _ _ 3).mp hmod
    simpa using hmod2
  refine ⟨C, (p ^ (f / 3 ^ (f.factorization 3))) ^ 2,
    CFSG.ABGLocalTools.isSylowOf_of_card hle hcard, ?_, hs, ?_⟩
  · exact (Subgroup.equivMapOfInjective (S : Subgroup T0) torusT0 hinj).symm.isCyclic.mpr
      inferInstance
  · rintro g ⟨x, -, rfl⟩
    exact su2_torusHom_pow_map φ hφ P hphiP ((x : T0) : Kˣ)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
