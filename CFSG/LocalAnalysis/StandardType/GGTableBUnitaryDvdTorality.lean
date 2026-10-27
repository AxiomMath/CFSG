module

public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public section

namespace CFSG.StandardType

namespace TableBUD

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {n d p : ℕ} {K : Type} [Field K]

section Multiplier

@[expose] def herm (n : ℕ) (M : Matrix (Fin d) (Fin d) K) : Matrix (Fin d) (Fin d) K :=
  (M.map (· ^ 2 ^ n))ᵀ * M

theorem map_pow_eq_map_bar (h : UnitaryFieldData 2 n K) (M : Matrix (Fin d) (Fin d) K) :
    M.map (· ^ 2 ^ n) = M.map h.bar := rfl

theorem herm_mul (h : UnitaryFieldData 2 n K) (M N : Matrix (Fin d) (Fin d) K) :
    herm n (M * N) = (N.map (· ^ 2 ^ n))ᵀ * herm n M * N := by
  rw [herm, herm, map_pow_eq_map_bar h, map_pow_eq_map_bar h, map_pow_eq_map_bar h,
    Matrix.map_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

theorem herm_pow (h : UnitaryFieldData 2 n K) {M : Matrix (Fin d) (Fin d) K} {ν : K}
    (hM : herm n M = ν • (1 : Matrix (Fin d) (Fin d) K)) (k : ℕ) :
    herm n (M ^ k) = ν ^ k • (1 : Matrix (Fin d) (Fin d) K) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, one_smul, herm, map_pow_eq_map_bar h, Matrix.map_one _ (map_zero _)
      (map_one _), transpose_one, Matrix.mul_one]
  | succ k ih =>
    rw [pow_succ, herm_mul h, ih, pow_succ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← herm, hM, smul_smul]

theorem norm_pow_fixed (h : UnitaryFieldData 2 n K) (c : K) :
    (c ^ (2 ^ n + 1)) ^ 2 ^ n = c ^ (2 ^ n + 1) := by
  have h1 : (c ^ 2 ^ n) ^ 2 ^ n = c := h.bar_bar c
  rw [← pow_mul, pow_succ, mul_comm (2 ^ n + 1), pow_mul]
  calc (c ^ 2 ^ n) ^ (2 ^ n + 1) = (c ^ 2 ^ n) ^ 2 ^ n * c ^ 2 ^ n := by rw [pow_succ]
    _ = c ^ 2 ^ n * c := by rw [h1, mul_comm]

theorem eq_one_of_fixed_of_pow (h : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n + 1) {ν : K}
    (hνq : ν ^ 2 ^ n = ν) (hνp : ν ^ p = 1) : ν = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨k, hk⟩ := hpq
  have h1 : ν ^ (2 ^ n + 1) = 1 := by rw [hk, pow_mul, hνp, one_pow]
  have h2 : ν ^ 2 = 1 := by rw [pow_succ, hνq, ← sq] at h1; exact h1
  have h3 : (ν + 1) ^ 2 = 0 := by
    rw [add_sq, h2, mul_one, one_pow, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul,
      add_zero, CharTwo.add_self_eq_zero]
  have h4 : ν + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
  calc ν = ν + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h4, zero_add]

theorem mem_primeFormUnitary_of_pow_eq_one (h : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n + 1)
    (hd : 0 < d) {g M : GL (Fin d) K} (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) {c : K}
    (hgM : (g : Matrix (Fin d) (Fin d) K) = c • (M : Matrix (Fin d) (Fin d) K))
    (hgp : g ^ p = 1) : g ∈ primeFormUnitary h (idGram K d) := by
  obtain ⟨μ, -, hμq, hμ⟩ := hM
  set ν := c ^ (2 ^ n + 1) * μ with hν
  have hmap : (c • (M : Matrix (Fin d) (Fin d) K)).map (· ^ 2 ^ n) =
      c ^ 2 ^ n • (M : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ n) := by
    ext i j
    simp [mul_pow]
  have hg : herm n (g : Matrix (Fin d) (Fin d) K) = ν • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [herm, hgM, hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hμ,
      smul_smul, hν, pow_succ]
  have hνq : ν ^ 2 ^ n = ν := by rw [hν, mul_pow, norm_pow_fixed h, hμq]
  have hgp' := herm_pow h hg p
  rw [← Units.val_pow_eq_pow_val, hgp, Units.val_one, herm, map_pow_eq_map_bar h,
    Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.mul_one] at hgp'
  have hνp : ν ^ p = 1 := by
    have h1 := congrArg (fun N : Matrix (Fin d) (Fin d) K => N ⟨0, hd⟩ ⟨0, hd⟩) hgp'
    simpa using h1.symm
  have hν1 := eq_one_of_fixed_of_pow h hpq hνq hνp
  change ((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (1 : GL (Fin d) K) *
    (g : Matrix (Fin d) (Fin d) K) = (1 : GL (Fin d) K)
  rw [Units.val_one, Matrix.mul_one, ← map_pow_eq_map_bar h, ← herm, hg, hν1, one_smul]

end Multiplier

section Torality

theorem scalar_mul_eq_smul (c : K) (M : Matrix (Fin d) (Fin d) K) :
    Matrix.scalar (Fin d) c * M = c • M := by
  rw [scalar_apply, smul_eq_diagonal_mul]

theorem coe_conj (A₀ g : GL (Fin d) K) :
    ((A₀ * g * A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (A₀ : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
        ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  rw [Units.val_mul, Units.val_mul]

theorem commute_of_offDiag {A₀ g g' : GL (Fin d) K}
    (hg : ∀ i j, i ≠ j → ((A₀ : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
      ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0)
    (hg' : ∀ i j, i ≠ j → ((A₀ : Matrix (Fin d) (Fin d) K) * (g' : Matrix (Fin d) (Fin d) K) *
      ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0) :
    g * g' = g' * g := by
  have h1 := CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag hg
  have h2 := CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag hg'
  have hD : (A₀ * g * A₀⁻¹) * (A₀ * g' * A₀⁻¹) = (A₀ * g' * A₀⁻¹) * (A₀ * g * A₀⁻¹) := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [h1, h2, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  calc g * g' = A₀⁻¹ * ((A₀ * g * A₀⁻¹) * (A₀ * g' * A₀⁻¹)) * A₀ := by group
    _ = A₀⁻¹ * ((A₀ * g' * A₀⁻¹) * (A₀ * g * A₀⁻¹)) * A₀ := by rw [hD]
    _ = g' * g := by group

variable [Finite K]

theorem exists_unitary_diag_of_isToral (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 0 < d) {X : Subgroup (MulAut (projectiveSL d K))}
    (hX : IsElemAbelian p X)
    (hXU : ∀ x ∈ X, ∃ M ∈ LargeEvenGUSet (Fin d) K (2 ^ n), conjAut d K M = x)
    (htor : TypeA.PGLTor.IsToral (X.comap (conjAut d K))) :
    ∃ P ∈ primeFormUnitary h (idGram K d), ∀ M : GL (Fin d) K, conjAut d K M ∈ X →
      ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
  classical
  set G := X.comap (conjAut d K) with hGdef
  have hG : TypeA.PGLTor.IsProjElem p G := TypeA.isProjElem_comap hd hX
  obtain ⟨A₀, hA₀⟩ := htor
  have hcomm : ∀ g ∈ G, ∀ g' ∈ G, g * g' = g' * g := fun g hg g' hg' =>
    commute_of_offDiag (hA₀ g hg) (hA₀ g' hg')
  let H₁ : Subgroup (primeFormUnitary h (idGram K d)) :=
    { carrier := {u | (u : GL (Fin d) K) ∈ G ∧ u ^ p = 1}
      mul_mem' := by
        rintro u v ⟨hu, hup⟩ ⟨hv, hvp⟩
        refine ⟨G.mul_mem hu hv, ?_⟩
        have huv : Commute u v := Subtype.ext (hcomm _ hu _ hv)
        rw [huv.mul_pow, hup, hvp, one_mul]
      one_mem' := ⟨G.one_mem, one_pow _⟩
      inv_mem' := by
        rintro u ⟨hu, hup⟩
        exact ⟨G.inv_mem hu, by rw [inv_pow, hup, inv_one]⟩ }
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h hp hpq H₁
    (fun x hx y hy => Subtype.ext (hcomm _ hx.1 _ hy.1)) (fun x hx => hx.2)
  refine ⟨P, P.2, fun M hM => ?_⟩
  have hMG : M ∈ G := hM
  set t : Fin d → K := fun i => ((A₀ : Matrix (Fin d) (Fin d) K) * (M : Matrix (Fin d) (Fin d) K) *
    ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i i with ht
  have hD : ((A₀ * M * A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal t := by
    rw [coe_conj]
    exact CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag (hA₀ M hMG)
  have he0 : t ⟨0, hd⟩ ≠ 0 := TypeA.diag_ne_zero hD _
  obtain ⟨u, hu⟩ := hG.pow_scalar M hMG
  have hep : t ⟨0, hd⟩ ^ p = u := by
    have h1 : ((A₀ * M * A₀⁻¹) ^ p : GL (Fin d) K) = GeneralLinearGroup.scalar (Fin d) u := by
      rw [conj_pow, hu, ← TypeA.PGLTor.scalar_mul_comm u A₀, mul_inv_cancel_right]
    have h2 := congrArg (fun N : GL (Fin d) K => (N : Matrix (Fin d) (Fin d) K) ⟨0, hd⟩ ⟨0, hd⟩) h1
    simp only [Units.val_pow_eq_pow_val, hD, diagonal_pow, GeneralLinearGroup.coe_scalar,
      scalar_apply, diagonal_apply_eq, Pi.pow_apply] at h2
    exact h2
  set E : GL (Fin d) K := GeneralLinearGroup.scalar (Fin d) (Units.mk0 _ he0) with hE
  set g : GL (Fin d) K := E⁻¹ * M with hg
  have hgG : g ∈ G := G.mul_mem (by rw [hE, ← map_inv]; exact hG.scalar_mem _) hMG
  have hEp : E ^ p = GeneralLinearGroup.scalar (Fin d) u := by
    rw [hE, ← map_pow]
    congr 1
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hep])
  have hgp : g ^ p = 1 := by
    have hc : Commute E⁻¹ M := by
      rw [hE, ← map_inv]
      exact TypeA.PGLTor.scalar_mul_comm _ M
    rw [hg, hc.mul_pow, inv_pow, hEp, hu, inv_mul_cancel]
  obtain ⟨M', hM'U, hM'⟩ := hXU _ hM
  obtain ⟨s, hs⟩ := TypeA.exists_scalar_of_conjAut_eq_one (A := M * M'⁻¹)
    (by rw [map_mul, map_inv, hM', mul_inv_cancel])
  have hMs : (M : Matrix (Fin d) (Fin d) K) = s • (M' : Matrix (Fin d) (Fin d) K) := by
    have h1 : M = (M * M'⁻¹) * M' := by group
    rw [h1, Units.val_mul, hs, scalar_mul_eq_smul]
  have hgM : (g : Matrix (Fin d) (Fin d) K) =
      ((t ⟨0, hd⟩)⁻¹ * s) • (M' : Matrix (Fin d) (Fin d) K) := by
    rw [hg, Units.val_mul, hE, ← map_inv, GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul, hMs,
      smul_smul, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hgU : g ∈ primeFormUnitary h (idGram K d) :=
    mem_primeFormUnitary_of_pow_eq_one h hpq hd hM'U hgM hgp
  have hdiag := hP ⟨g, hgU⟩ ⟨hgG, Subtype.ext (by rw [Subgroup.coe_pow, hgp]; rfl)⟩
  have hPg : ((P⁻¹ * ⟨g, hgU⟩ * P : primeFormUnitary h (idGram K d)) : GL (Fin d) K) =
      (P : GL (Fin d) K)⁻¹ * g * P := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hPg] at hdiag
  have hM' : (P : GL (Fin d) K)⁻¹ * M * P = E * ((P : GL (Fin d) K)⁻¹ * g * P) := by
    rw [hg, show (P : GL (Fin d) K)⁻¹ * (E⁻¹ * M) * P = E⁻¹ * ((P : GL (Fin d) K)⁻¹ * M * P) by
      rw [hE, ← map_inv]
      rw [← mul_assoc, ← TypeA.PGLTor.scalar_mul_comm, mul_assoc, mul_assoc, mul_assoc],
      mul_inv_cancel_left]
  rw [hM', Units.val_mul, hE, GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul]
  exact hdiag.smul _

omit [Finite K] in
theorem ne_two_of_dvd (h : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n + 1) : p ≠ 2 := by
  rintro rfl
  have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by have := h.one_le; omega)
  have h2 : 2 ∣ 1 := (Nat.dvd_add_right h1).mp hpq
  omega

omit [Finite K] in
theorem dvd_card_sub_one' (h : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n + 1) :
    p ∣ Nat.card K - 1 := by
  have h1 : Nat.card K - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [h.card, pow_mul', sq]
    have := Nat.mul_self_sub_mul_self_eq (2 ^ n) 1
    simpa using this
  rw [h1]
  exact Dvd.dvd.mul_right hpq _

theorem ggPGUTorality (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {X : Subgroup (MulAut (projectiveSL d K))} (hX : IsElemAbelian p X)
    (hXU : ∀ x ∈ X, ∃ M ∈ LargeEvenGUSet (Fin d) K (2 ^ n), conjAut d K M = x)
    (hcard : p ^ (d / p + 2) ≤ Nat.card X) :
    ∃ P ∈ primeFormUnitary h (idGram K d), ∀ M : GL (Fin d) K, conjAut d K M ∈ X →
      ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨1, Subgroup.one_mem _, fun M _ i => i.elim0⟩
  have hp2 := ne_two_of_dvd h hpq
  have hpK := dvd_card_sub_one' h hpq
  rcases TypeA.PGLTor.toral_or_card_le hp hp2 hpK (TypeA.isProjElem_comap hd hX) with
    htor | hbound
  · exact exists_unitary_diag_of_isToral h hp hpq hd hX hXU htor
  · exfalso
    have hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
      intro x hx
      obtain ⟨M, -, hM⟩ := hXU x hx
      exact ⟨M, hM⟩
    rw [TypeA.card_comap_eq hd hXI, Fintype.card_fin] at hbound
    have hK1 : 0 < Nat.card K - 1 := by
      have := Finite.one_lt_card (α := K)
      omega
    have hX' : Nat.card X ≤ p ^ (d / p + 1) := Nat.le_of_mul_le_mul_right hbound hK1
    have h1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard.trans hX')
    omega

end Torality

end TableBUD

end CFSG.StandardType
