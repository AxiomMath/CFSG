module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSU
public import CFSG.LieType.Universal.Unitary.Extras.RankOneLast

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

namespace InnerDiagSU

section Roots

@[expose] def twoEpsVec (n : ℕ) (a : Fin (n / 2)) : Fin (n / 2) → ℤ := fun b =>
  if b.val < a.val then 0 else if Even n ∧ b.val + 1 = n / 2 then 1 else 2

theorem toStd_twoEpsVec (n : ℕ) (a : Fin (n / 2)) :
    toStd n (twoEpsVec n a) = 2 • Pi.single a 1 := by
  funext b
  by_cases he : Even n
  · simp only [toStd, he, ite_true, Symplectic.toStd, twoEpsVec, true_and, Pi.smul_apply,
      Pi.single_apply, Fin.ext_iff, nsmul_eq_mul, Nat.cast_ofNat]
    split_ifs <;> omega
  · simp only [toStd, he, ite_false, twoEpsVec, false_and, Pi.smul_apply,
      Pi.single_apply, Fin.ext_iff, nsmul_eq_mul, Nat.cast_ofNat]
    split_ifs <;> omega

theorem toStd_neg' (n : ℕ) (v : Fin (n / 2) → ℤ) : toStd n (-v) = -toStd n v := by
  funext b
  by_cases he : Even n
  · simp only [toStd, he, ite_true, Symplectic.toStd, Pi.neg_apply]
    split_ifs <;> ring
  · simp only [toStd, he, ite_false, Pi.neg_apply]
    split_ifs <;> ring

@[expose] def twoWtRoot (n : ℕ) (i : Fin n) : Fin (n / 2) → ℤ :=
  if h : i.val < n / 2 then twoEpsVec n ⟨i.val, h⟩
  else if h' : n - 1 - i.val < n / 2 then -twoEpsVec n ⟨n - 1 - i.val, h'⟩ else 0

theorem toStd_twoWtRoot {n : ℕ} (i : Fin n) : toStd n (twoWtRoot n i) = 2 • weight n i := by
  unfold twoWtRoot weight
  split_ifs with h h'
  · exact toStd_twoEpsVec n _
  · rw [toStd_neg', toStd_twoEpsVec, smul_neg]
  · funext b
    by_cases he : Even n
    · simp [toStd, he, Symplectic.toStd]
    · simp [toStd, he]

theorem twoWtRoot_mem_roots {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) :
    twoWtRoot n i ∈ roots (isFiniteType_cartan n) (divisible n) :=
  mem_roots_of_weight_sub hi (by rw [toStd_twoWtRoot, weight_rev', sub_neg_eq_add, two_nsmul])

end Roots

section Conj

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem mat_mul_mat_inv (g : SU σ n) : mat σ n g * mat σ n g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem mat_inv_mul_mat (g : SU σ n) : mat σ n g⁻¹ * mat σ n g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem mat_apply_self_ne_zero_of_col {g : SU σ n} {i : Fin n}
    (hcol : ∀ a, a ≠ i → mat σ n g a i = 0) : mat σ n g i i ≠ 0 := by
  intro h0
  have h1 := congrFun (congrFun (mat_inv_mul_mat g) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_zero fun a _ => by
    by_cases ha : a = i
    · rw [ha, h0, mul_zero]
    · rw [hcol a ha, mul_zero], one_apply_eq] at h1
  exact zero_ne_one h1

theorem exists_mat_apply_ne_zero (g : SU σ n) (r : Fin n) : ∃ b, mat σ n g r b ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := congrFun (congrFun (mat_mul_mat_inv g) r) r
  rw [Matrix.mul_apply, Finset.sum_eq_zero fun b _ => by rw [h b, zero_mul], one_apply_eq] at h1
  exact zero_ne_one h1

end Conj

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

theorem one_mem_traceZero : (1 : F) ∈ traceZero (unitaryInvolution F 2 f) := by
  rw [mem_traceZero, map_one]
  exact CharTwo.add_self_eq_zero 1

include hF in
theorem col_row_of_mem_ggTorus {n : ℕ} {g : SU (unitaryInvolution F 2 f) n}
    (hg : g ∈ ggTorus (rootDatum hF n)) {i : Fin n} (hi : i ≠ Fin.rev i) :
    (∀ a, a ≠ i → mat _ n g a i = 0) ∧
      ∀ b, b ≠ Fin.rev i → mat _ n g⁻¹ (Fin.rev i) b = 0 := by
  have hσ := unitaryInvolution_involutive hF
  have hw : 2 • weight n i = toStd n (twoWtRoot n i) := (toStd_twoWtRoot i).symm
  have hN : g ∈ Subgroup.normalizer
      (rootGroup (unitaryInvolution F 2 f) hσ n (twoWtRoot n i) : Set _) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hg
    exact hg _ (twoWtRoot_mem_roots hi)
  have hx : longRootHom (unitaryInvolution F 2 f) hi (Multiplicative.ofAdd ⟨1, one_mem_traceZero⟩) ∈
      rootGroup (unitaryInvolution F 2 f) hσ n (twoWtRoot n i) :=
    longRootHom_mem hσ hi hw _
  have hgx := (Subgroup.mem_normalizer_iff.mp hN _).mp hx
  have hent : ∀ a b, ¬(a = i ∧ b = Fin.rev i) →
      mat _ n g a i * mat _ n g⁻¹ (Fin.rev i) b = 0 := by
    intro a b hab
    have h1 := mat_apply_of_mem_rootGroup hσ hgx (a := a) (b := b)
      (fun h => hab (eq_of_weight_sub_eq_two_smul hi (h.trans hw.symm)))
      (fun h => weight_ne_zero hi (eq_zero_of_weight_sub_eq_nsmul
        (h.trans (by rw [← hw, smul_smul])) (by norm_num)))
    rw [map_mul, map_mul, mat_apply (longRootHom _ hi _), coe_longRootHom, longRootMatrix,
      conj_one_add_apply (mat_mul_mat_inv g), mul_single_mul_apply] at h1
    simpa using h1
  have hcol : ∀ a, a ≠ i → mat _ n g a i = 0 := by
    intro a ha
    obtain ⟨b, hb⟩ := exists_mat_apply_ne_zero g⁻¹ (Fin.rev i)
    exact (mul_eq_zero.mp (hent a b fun h => ha h.1)).resolve_right hb
  refine ⟨hcol, fun b hb => ?_⟩
  exact (mul_eq_zero.mp (hent i b fun h => hb h.2)).resolve_left
    (mat_apply_self_ne_zero_of_col hcol)

include hF in
theorem mat_eq_zero_of_mem_ggTorus {n : ℕ} {g : SU (unitaryInvolution F 2 f) n}
    (hg : g ∈ ggTorus (rootDatum hF n)) {a b : Fin n} (hab : a ≠ b) : mat _ n g a b = 0 := by
  by_cases hb : b = Fin.rev b
  · have ha : a ≠ Fin.rev a := fun ha => hab (Fin.ext (by
      have h1 := congrArg Fin.val ha
      have h2 := congrArg Fin.val hb
      simp only [Fin.val_rev] at h1 h2
      omega))
    obtain ⟨-, hrow⟩ := col_row_of_mem_ggTorus hF (inv_mem hg) (rev_ne_rev_rev ha)
    have h := hrow b (by rw [Fin.rev_rev]; exact hab.symm)
    rwa [inv_inv, Fin.rev_rev] at h
  · exact (col_row_of_mem_ggTorus hF hg hb).1 a hab

include hF in
theorem eq_diagonal_of_mem_ggTorus {n : ℕ} {g : SU (unitaryInvolution F 2 f) n}
    (hg : g ∈ ggTorus (rootDatum hF n)) :
    mat _ n g = diagonal (fun s => mat _ n g s s) ∧
      ∀ s, unitaryInvolution F 2 f (mat _ n g s s) * mat _ n g (Fin.rev s) (Fin.rev s) = 1 := by
  have hd : mat _ n g = diagonal (fun s => mat _ n g s s) := by
    ext a b
    by_cases hab : a = b
    · rw [hab, diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hab, mat_eq_zero_of_mem_ggTorus hF hg hab]
  exact ⟨hd, unitary_of_coe_eq_diagonal hd⟩

include hF in
theorem exists_scalar_of_mem_center {n : ℕ} (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    {z : SU (unitaryInvolution F 2 f) n} (hz : z ∈ Subgroup.center _) :
    ∃ c : F, mat _ n z = Matrix.scalar (Fin n) c := by
  have hZ := (isQuasisimple_statedSU_of_card hF hn hnq).2
  set P := (exists_wittMatrix hF n).choose with hPdef
  have hP := (exists_wittMatrix hF n).choose_spec
  let E : SU (unitaryInvolution F 2 f) n ≃* ↥(StatedSU n (2 ^ f) F) :=
    (conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hF n))
  have hEz : ((E z : ↥(StatedSU n (2 ^ f) F)) : GL (Fin n) F) = P * z * P⁻¹ := rfl
  have h1 : E z ∈ Subgroup.center _ := (mem_center_iff_of_mulEquiv E).mpr hz
  rw [hZ, Subgroup.mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨(c : F), ?_⟩
  have h2 : (P : Matrix (Fin n) (Fin n) F) * mat _ n z * ((P⁻¹ : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) (c : F) := by
    have := congrArg (fun A : GL (Fin n) F => (A : Matrix (Fin n) (Fin n) F)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, hEz, Units.val_mul] at this
    rw [mat_apply, this]
  have hPP : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc mat _ n z = ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((P : Matrix (Fin n) (Fin n) F) * mat _ n z * ((P⁻¹ : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F)) * (P : Matrix (Fin n) (Fin n) F) := by
        simp only [Matrix.mul_assoc, hPP, Matrix.mul_one]
        rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
    _ = Matrix.scalar (Fin n) (c : F) := by
        rw [h2, Matrix.mul_assoc,
          (Matrix.scalar_commute (c : F) (fun r => Commute.all _ r) _).eq, ← Matrix.mul_assoc,
          hPP, Matrix.one_mul]

end Torus

section Diag

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

@[expose] noncomputable def diagJ (d : Fin n → F) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) :
    GL (Fin n) F :=
  ⟨diagonal d, diagonal fun s => (d s)⁻¹,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext s
      exact mul_inv_cancel₀ (ne_zero_of_unitary hd s),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext s
      exact inv_mul_cancel₀ (ne_zero_of_unitary hd s)⟩

theorem coe_diagJ (d : Fin n → F) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) :
    ((diagJ d hd : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d :=
  rfl

theorem coe_diagJ_inv (d : Fin n → F) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) :
    (((diagJ d hd)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun s => (d s)⁻¹ :=
  rfl

theorem conjTr_diagonal (d : Fin n → F) :
    conjTr σ (diagonal d) = diagonal fun s => σ (d s) := by
  rw [conjTr, diagonal_map (map_zero σ), diagonal_transpose]

theorem isJUnitary_diagJ (d : Fin n → F) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) :
    IsJUnitary σ (diagJ d hd) := by
  unfold IsJUnitary
  rw [coe_diagJ, conjTr_diagonal]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  simp only [antidiag, of_apply]
  split_ifs with h
  · rw [h, mul_one]
    exact hd a
  · rw [mul_zero, zero_mul]

theorem mat_conjSU_diagJ (d : Fin n → F) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (x : SU σ n)
    (a b : Fin n) :
    mat σ n (conjSU (diagJ d hd) (isJUnitary_diagJ d hd) x) a b =
      d a * mat σ n x a b * (d b)⁻¹ := by
  rw [mat_apply, coe_conjSU, Units.val_mul, Units.val_mul, coe_diagJ, coe_diagJ_inv,
    mul_diagonal, diagonal_mul, mat_apply]

theorem conjSU_diagJ_eq_self (d : Fin n → F) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    (x : SU σ n) (h : ∀ a b, a ≠ b → mat σ n x a b ≠ 0 → d a = d b) :
    conjSU (diagJ d hd) (isJUnitary_diagJ d hd) x = x := by
  apply mat_injective
  ext a b
  rw [mat_conjSU_diagJ]
  have h0 := ne_zero_of_unitary hd
  by_cases hab : a = b
  · rw [hab]
    field_simp [h0 b]
  · by_cases hx : mat σ n x a b = 0
    · rw [hx, mul_zero, zero_mul]
    · rw [h a b hab hx]
      field_simp [h0 b]

theorem conj_eq_conjSU_diagJ {h : SU σ n} {t : Fin n → F}
    (hh : mat σ n h = diagonal t) (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1) (z : SU σ n) :
    h * z * h⁻¹ = conjSU (diagJ t ht) (isJUnitary_diagJ t ht) z := by
  apply mat_injective
  have hinv : mat σ n h⁻¹ = diagonal fun s => (t s)⁻¹ := by
    have h1 : mat σ n h * mat σ n h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [hh] at h1
    have h3 : diagonal (fun s => (t s)⁻¹ * t s) = (1 : Matrix (Fin n) (Fin n) F) := by
      rw [← diagonal_one]
      congr 1
      funext s
      exact inv_mul_cancel₀ (ne_zero_of_unitary ht s)
    calc mat σ n h⁻¹ = diagonal (fun s => (t s)⁻¹ * t s) * mat σ n h⁻¹ := by
          rw [h3, Matrix.one_mul]
      _ = diagonal (fun s => (t s)⁻¹) * (diagonal t * mat σ n h⁻¹) := by
          rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
      _ = diagonal fun s => (t s)⁻¹ := by rw [h1, Matrix.mul_one]
  rw [map_mul, map_mul, hh, hinv, mat_apply (conjSU _ _ z), coe_conjSU, Units.val_mul,
    Units.val_mul, coe_diagJ, coe_diagJ_inv, mat_apply]

end Diag

end InnerDiagSU

end CFSG.StandardType
