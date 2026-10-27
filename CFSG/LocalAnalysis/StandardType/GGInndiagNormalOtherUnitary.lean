module

public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

namespace InndiagSU

variable {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)

section Transport

theorem largeEvenSUGroup_eq_gramSU :
    LargeEvenSUGroup (Fin d) K (2 ^ n) =
      gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have hset : {g : GL (Fin d) K | (g : Matrix (Fin d) (Fin d) K).det = 1 ∧
      Matrix.transpose ((g : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ n)) *
        (g : Matrix (Fin d) (Fin d) K) = 1} =
      (gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) : Set (GL (Fin d) K)) := by
    ext g
    rw [SetLike.mem_coe, mem_gramSU, Units.val_one, Matrix.mul_one, and_comm]
    rfl
  rw [LargeEvenSUGroup, hset, Subgroup.closure_eq]

theorem det_coe_scalar (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K).det = (c : K) ^ d := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem map_scalars_subgroupOf (hd : 1 ≤ d) :
    ((LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K (2 ^ n))).map
        (MulEquiv.subgroupCongr (largeEvenSUGroup_eq_gramSU (d := d) h)).toMonoidHom =
      normOneScalars h (gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) d := by
  ext x
  constructor
  · rintro ⟨y, ⟨c, hc⟩, rfl⟩
    have hy : ((MulEquiv.subgroupCongr (largeEvenSUGroup_eq_gramSU (d := d) h)).toMonoidHom y :
        GL (Fin d) K) = Matrix.GeneralLinearGroup.scalar (Fin d) c := hc.symm
    have hmem := ((MulEquiv.subgroupCongr (largeEvenSUGroup_eq_gramSU (d := d) h)).toMonoidHom y).2
    rw [hy] at hmem
    refine ⟨c, norm_eq_one_of_scalar_mem_primeFormUnitary h hd 1 ?_, ?_, hy⟩
    · exact ((mem_gramSU_iff_unitary h).mp hmem).1
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← det_coe_scalar, Units.val_one]
      exact hmem.2
  · rintro ⟨c, -, -, hx⟩
    refine ⟨(MulEquiv.subgroupCongr (largeEvenSUGroup_eq_gramSU (d := d) h)).symm x,
      ⟨c, hx.symm⟩, ?_⟩
    exact (MulEquiv.subgroupCongr (largeEvenSUGroup_eq_gramSU (d := d) h)).apply_symm_apply x

@[expose] noncomputable def projEquiv (hd : 1 ≤ d) :
    LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) ≃*
      primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (largeEvenSUGroup_eq_gramSU (d := d) h))
    (map_scalars_subgroupOf h hd)

theorem projEquiv_mk (hd : 1 ≤ d) (g : LargeEvenSUGroup (Fin d) K (2 ^ n)) :
    projEquiv h hd (g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) =
      ((⟨g, largeEvenSUGroup_eq_gramSU (d := d) h ▸ g.2⟩ :
        gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
          primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :=
  rfl

theorem projEquiv_symm_mk (hd : 1 ≤ d)
    (s : gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    (projEquiv h hd).symm (s : primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
      ((⟨s, (largeEvenSUGroup_eq_gramSU (d := d) h).symm ▸ s.2⟩ :
        LargeEvenSUGroup (Fin d) K (2 ^ n)) :
          LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  rw [MulEquiv.symm_apply_eq, projEquiv_mk]

end Transport

section Conj

variable (hd : 1 ≤ d)

theorem scalar_mul_conj (u : Kˣ) (A g : GL (Fin d) K) :
    Matrix.GeneralLinearGroup.scalar (Fin d) u * A * g *
        (Matrix.GeneralLinearGroup.scalar (Fin d) u * A)⁻¹ = A * g * A⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (ι := Fin d) u)
  set s := Matrix.GeneralLinearGroup.scalar (Fin d) u
  rw [_root_.mul_inv_rev]
  calc s * A * g * (A⁻¹ * s⁻¹) = s * (A * g * A⁻¹) * s⁻¹ := by group
    _ = (A * g * A⁻¹) * s * s⁻¹ := by rw [hc (A * g * A⁻¹)]
    _ = A * g * A⁻¹ := by group

theorem congr_eq_primeFormConjHom_of_scalar_mul
    (M : GL (Fin d) K) (u : Kˣ)
    (A : primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (hA : (A : GL (Fin d) K) = Matrix.GeneralLinearGroup.scalar (Fin d) u * M)
    (φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      {M}) :
    MulAut.congr (projEquiv h hd) φ =
      primeFormConjHom h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) A := by
  obtain ⟨M', hM', hφ⟩ := hφ
  rw [Set.mem_singleton_iff] at hM'
  subst M'
  have hconj : ∀ g : GL (Fin d) K, A * g * A⁻¹ = M * g * M⁻¹ := by
    intro g
    change (A : GL (Fin d) K) * g * (A : GL (Fin d) K)⁻¹ = M * g * M⁻¹
    rw [hA, scalar_mul_conj u M g]
  refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun s => ?_
  rw [primeFormConjHom_mk, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    projEquiv_symm_mk]
  have hmem : M * (s : GL (Fin d) K) * M⁻¹ ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
    rw [largeEvenSUGroup_eq_gramSU h, ← hconj s]
    exact conj_mem_gramSU h _ A.2 s.2
  have e1 := hφ ⟨s, (largeEvenSUGroup_eq_gramSU (d := d) h).symm ▸ s.2⟩
    ⟨M * (s : GL (Fin d) K) * M⁻¹, hmem⟩ rfl
  change projEquiv h hd (φ (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))
    ⟨s, (largeEvenSUGroup_eq_gramSU (d := d) h).symm ▸ s.2⟩)) = _
  rw [e1]
  change projEquiv h hd ((⟨M * (s : GL (Fin d) K) * M⁻¹, hmem⟩ :
    LargeEvenSUGroup (Fin d) K (2 ^ n)) : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = _
  rw [projEquiv_mk]
  congr 1
  exact Subtype.ext (hconj s).symm

theorem congr_mem_primeFormD [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n))) :
    MulAut.congr (projEquiv h hd) φ ∈
      primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  obtain ⟨A, ⟨μ, hμ0, hμq, hA⟩, hφ⟩ := hφ
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.one_le
  obtain ⟨l, hl⟩ := TableB.exists_norm_eq hq hK hμ0 hμq
  set A' := Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹ * A with hA'
  have hA2 : Matrix.transpose ((A : Matrix (Fin d) (Fin d) K).map h.bar) *
      (A : Matrix (Fin d) (Fin d) K) = μ • (1 : Matrix (Fin d) (Fin d) K) := hA
  have hA'U : A' ∈ primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, hA', TableB.coe_scalar_mul,
      TableB.transpose_map_smul, Matrix.smul_mul, Matrix.mul_smul, hA2, smul_smul, smul_smul,
      UnitaryFieldData.bar_apply, ← hl]
    have h0 : ((l⁻¹ : Kˣ) : K) ^ 2 ^ n * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ n + 1) = 1 := by
      have hinv : ((l⁻¹ : Kˣ) : K) * (l : K) = 1 := Units.inv_mul l
      calc ((l⁻¹ : Kˣ) : K) ^ 2 ^ n * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ n + 1) =
            (((l⁻¹ : Kˣ) : K) * l) ^ 2 ^ n * (((l⁻¹ : Kˣ) : K) * l) := by ring
        _ = 1 := by rw [hinv, one_pow, one_mul]
    rw [h0, one_smul]
  have hconj : ∀ g : GL (Fin d) K, A' * g * A'⁻¹ = A * g * A⁻¹ := fun g => by
    rw [hA']
    exact scalar_mul_conj l⁻¹ A g
  refine ⟨⟨A', hA'U⟩, ?_⟩
  exact (congr_eq_primeFormConjHom_of_scalar_mul h hd A l⁻¹ ⟨A', hA'U⟩ hA' φ
    ⟨A, by simp, hφ⟩).symm

theorem congr_symm_mem (B : primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    (MulAut.congr (projEquiv h hd)).symm (primeFormConjHom h _ B) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
  refine ⟨B, ⟨1, one_ne_zero, one_pow _, ?_⟩, fun g g' hgg' => ?_⟩
  · have hB := mem_primeFormUnitary.mp B.2
    change Matrix.transpose (((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar) * 1 *
      ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 at hB
    rw [Matrix.mul_one] at hB
    rw [one_smul]
    exact hB
  · rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    change (projEquiv h hd).symm (primeFormConjHom h _ B
      (projEquiv h hd (g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) =
        (g' : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    rw [projEquiv_mk, primeFormConjHom_mk, projEquiv_symm_mk]
    congr 1
    exact Subtype.ext hgg'.symm

end Conj

theorem ggInndiagNormal_unitary [Finite K] (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) :
    GGInndiagNormal (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro α φ hφ
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  have hd1 : 1 ≤ d := by omega
  set E := MulAut.congr (projEquiv h hd1) with hE
  obtain ⟨-, -, -, -, -, -, -, -, hD, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (K := K) (n := d)) hd hq
  have h1 := congr_mem_primeFormD h hd1 hK hφ
  have h2 : E (α * φ * α⁻¹) ∈ primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    rw [map_mul, map_mul, map_inv]
    exact hD.conj_mem _ h1 (E α)
  obtain ⟨B, hB⟩ := h2
  have e : α * φ * α⁻¹ = E.symm (primeFormConjHom h _ B) := by
    rw [hB, MulEquiv.symm_apply_apply]
  rw [e]
  exact subset_ggInndiag (congr_symm_mem h hd1 B)

end InndiagSU

section Labels

theorem recipeUnitary_inndiag {d n : ℕ} (hn : 1 ≤ n) (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2))
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => GGInndiagNormal R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    fun _ _ => InndiagSU.ggInndiagNormal_unitary hn hK hd hq⟩

@[expose] def GGInndiagUnitaryLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)

theorem largeEvenLabelAll_inndiag_unitary {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGInndiagUnitaryLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  intro Q hQ
  rcases h with h | ⟨h, hl3⟩
  · dsimp only at h
    subst h
    obtain ⟨hl2, hl2n⟩ := hl
    refine recipeUnitary_inndiag hn (by omega) (fun ⟨h3, h2⟩ => ?_) hQ
    change l + 1 = 3 at h3
    change 2 ^ n = 2 at h2
    have hn2 : 2 ≤ n := hl2n (by omega)
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · dsimp only at h hl3
    subst h hl3
    have h32 : (3 : ℕ) ≠ 2 := by decide
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [h32, ↓reduceIte] at hQ ⊢
    exact recipeUnitary_inndiag hn (by norm_num) (by omega) hQ

end Labels

end CFSG.StandardType
