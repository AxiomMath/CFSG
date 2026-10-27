module

public import CFSG.LocalAnalysis.StandardType.GGPGUKummerShift
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel

public section

namespace CFSG.StandardType.UnitaryThreeP

open Matrix CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.ClassicalGroups.UnitaryFlag TableBUE

variable {K : Type} [Field K] {d : ℕ}

@[expose] def IsSBlock (S : Finset (Fin d)) (M : Matrix (Fin d) (Fin d) K) : Prop :=
  (∀ i ∈ S, ∀ k ∉ S, M i k = 0) ∧ ∀ i ∉ S, ∀ k ∈ S, M i k = 0

variable {S : Finset (Fin d)}

theorem isSBlock_diagonal (t : Fin d → K) : IsSBlock S (diagonal t) :=
  ⟨fun i hi k hk => diagonal_apply_ne _ fun h => hk (h ▸ hi),
    fun i hi k hk => diagonal_apply_ne _ fun h => hi (h ▸ hk)⟩

theorem blockRes_mul_of_row {M : Matrix (Fin d) (Fin d) K} (hM : ∀ i ∈ S, ∀ k ∉ S, M i k = 0)
    (N : Matrix (Fin d) (Fin d) K) : blockRes S (M * N) = blockRes S M * blockRes S N := by
  ext a b
  simp only [blockRes, Matrix.mul_apply]
  set e := S.equivFin.symm with he
  have hz : ∀ k ∉ S, M (e a) k * N k (e b) = 0 := by
    intro k hk
    rw [hM _ (e a).2 k hk, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) fun k _ hk => hz k hk,
    ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp e fun k : ↥S => M (e a) k * N k (e b)).symm

theorem blockRes_diagonal_of_const {t : Fin d → K} {c : K} (ht : ∀ i ∈ S, t i = c) :
    blockRes S (diagonal t) = c • (1 : Matrix (Fin S.card) (Fin S.card) K) := by
  ext a b
  simp only [blockRes, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [diagonal_apply_eq, ht _ (S.equivFin.symm a).2, if_pos rfl, mul_one]
  · have hne : ((S.equivFin.symm a : ↥S) : Fin d) ≠ S.equivFin.symm b :=
      fun h' => hab (S.equivFin.symm.injective (Subtype.ext h'))
    rw [diagonal_apply_ne _ hne, if_neg hab, mul_zero]

theorem apply_eq_blockRes (M : Matrix (Fin d) (Fin d) K) {i j : Fin d} (hi : i ∈ S) (hj : j ∈ S) :
    M i j = blockRes S M (S.equivFin ⟨i, hi⟩) (S.equivFin ⟨j, hj⟩) := by
  simp [blockRes]

theorem blockExt_row (N : Matrix (Fin S.card) (Fin S.card) K) :
    ∀ i ∈ S, ∀ k ∉ S, blockExt S N i k = 0 := by
  intro i hi k hk
  rw [isBlockOn_blockExt N i k (Or.inr hk), Matrix.one_apply_ne fun h : i = k => hk (h ▸ hi)]

theorem blockExt_mul_eq_mul_blockExt {B : Matrix (Fin d) (Fin d) K} (hB : IsSBlock S B)
    {N₁ N₂ : Matrix (Fin S.card) (Fin S.card) K} (hN : N₁ * blockRes S B = blockRes S B * N₂) :
    blockExt S N₁ * B = B * blockExt S N₂ := by
  ext i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · rw [apply_eq_blockRes (blockExt S N₁ * B) hi hj, apply_eq_blockRes (B * blockExt S N₂) hi hj,
      blockRes_mul_of_row (blockExt_row N₁), blockRes_mul_of_row hB.1, blockRes_blockExt,
      blockRes_blockExt, hN]
  · rw [(isBlockOn_blockExt N₂).mul_apply_right i hj, hB.1 i hi j hj, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ S
    · rw [hB.1 k hk j hj, mul_zero]
    · rw [blockExt_row N₁ i hi k hk, zero_mul]
  · rw [(isBlockOn_blockExt N₁).mul_apply_left hi j, hB.2 i hi j hj, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    by_cases hk : k ∈ S
    · rw [hB.2 i hi k hk, zero_mul]
    · rw [isBlockOn_blockExt N₂ k j (Or.inl hk), Matrix.one_apply_ne fun h : k = j => hk (h ▸ hj),
        mul_zero]
  · rw [(isBlockOn_blockExt N₁).mul_apply_left hi j, (isBlockOn_blockExt N₂).mul_apply_right i hj]

theorem blockExt_smul_one_comm {B : Matrix (Fin d) (Fin d) K} (hB : IsSBlock S B) (c : K) :
    blockExt S (c • (1 : Matrix (Fin S.card) (Fin S.card) K)) * B =
      B * blockExt S (c • (1 : Matrix (Fin S.card) (Fin S.card) K)) :=
  blockExt_mul_eq_mul_blockExt hB (by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one])

@[expose] noncomputable def blockScalar (S : Finset (Fin d)) (ζ : Kˣ) : GL (Fin d) K :=
  Units.map (blockExtHom S) (GeneralLinearGroup.scalar (Fin S.card) ζ)

theorem coe_blockScalar (ζ : Kˣ) :
    ((blockScalar S ζ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blockExt S ((ζ : K) • (1 : Matrix (Fin S.card) (Fin S.card) K)) := by
  change blockExt S _ = _
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem blockScalar_pow (ζ : Kˣ) (k : ℕ) : blockScalar S ζ ^ k = blockScalar S (ζ ^ k) := by
  rw [blockScalar, blockScalar, ← map_pow, ← map_pow]

theorem exists_block_conj [Finite K] {n p : ℕ} (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    {P x : GL (Fin d) K} (hP : P ∈ primeFormUnitary h (idGram K d))
    (hxU : x ∈ primeFormUnitary h (idGram K d)) {b : ℕ} (hxb : x ^ p ^ b = 1) {l : Kˣ}
    (hxp : x ^ p = GeneralLinearGroup.scalar (Fin d) l) (hl : ∀ μ : Kˣ, μ ^ p ≠ l)
    (hxS : IsSBlock S ((P⁻¹ * x * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    ∃ E ∈ unitarySU 2 n K d, E * x * E⁻¹ = (P * blockScalar S ζ * P⁻¹) * x ∧
      ∀ y : GL (Fin d) K, IsSBlock S ((P⁻¹ * y * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) →
        (∃ c : K, blockRes S ((P⁻¹ * y * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          c • (1 : Matrix (Fin S.card) (Fin S.card) K)) → E * y = y * E := by
  classical
  set Y : GL (Fin d) K := P⁻¹ * x * P with hY
  have h1 : blockRes S (Y : Matrix (Fin d) (Fin d) K) *
      blockRes S ((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← blockRes_mul_of_row hxS.1, ← Units.val_mul, mul_inv_cancel, Units.val_one, blockRes_one]
  set X₁ : GL (Fin S.card) K := ⟨blockRes S (Y : Matrix (Fin d) (Fin d) K),
    blockRes S ((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K), h1,
    mul_eq_one_comm.mp h1⟩ with hX₁
  have hX₁c : (X₁ : Matrix (Fin S.card) (Fin S.card) K) = blockRes S (Y : Matrix (Fin d) (Fin d) K) :=
    rfl
  have hpow : ∀ k : ℕ, ((X₁ ^ k : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) =
      blockRes S ((Y ^ k : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Units.val_one, Units.val_one, blockRes_one]
    | succ k ih =>
      rw [pow_succ', pow_succ', Units.val_mul, Units.val_mul, ih, hX₁c,
        blockRes_mul_of_row hxS.1]
  have hYp : Y ^ p = GeneralLinearGroup.scalar (Fin d) l := by
    rw [hY, show P⁻¹ * x * P = P⁻¹ * x * P⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv, hxp,
      ← (TypeA.PGLTor.commute_scalar l P⁻¹).eq, inv_mul_cancel_right]
  have hX₁p : X₁ ^ p = GeneralLinearGroup.scalar (Fin S.card) l := by
    apply Units.ext
    rw [hpow, hYp, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.scalar_apply, blockRes_diagonal_of_const (fun _ _ => rfl),
      Matrix.smul_one_eq_diagonal]
  have hX₁b : X₁ ^ p ^ b = 1 := by
    apply Units.ext
    rw [hpow, hY, show P⁻¹ * x * P = P⁻¹ * x * P⁻¹⁻¹ by rw [inv_inv], conj_pow, hxb, mul_one,
      mul_inv_cancel, Units.val_one, Units.val_one, blockRes_one]
  have hYU : Y ∈ primeFormUnitary h (idGram K d) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hP) hxU) hP
  have hX₁U : X₁ ∈ primeFormUnitary h (idGram K S.card) := by
    have eY : ((Y : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * ((1 : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) * Y = ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := hYU
    rw [Units.val_one, Matrix.mul_one] at eY
    change ((X₁ : Matrix (Fin S.card) (Fin S.card) K).map h.bar)ᵀ *
      ((1 : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) * X₁ =
        ((1 : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K)
    have hrowT : ∀ i ∈ S, ∀ k ∉ S, (((Y : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ) i k = 0 := by
      intro i hi k hk
      rw [Matrix.transpose_apply, Matrix.map_apply, hxS.2 k hk i hi, map_zero]
    rw [Units.val_one, Matrix.mul_one, hX₁c, ← blockRes_map_transpose, ← blockRes_mul_of_row hrowT,
      eY, blockRes_one]
  obtain ⟨E₁, hE₁, hE₁X⟩ := KummerShift.exists_unitarySU_conj_eq_scalar_mul h hp hp2 hpq hζ hX₁U
    hX₁b hX₁p hl
  have hE₁m : (E₁ : Matrix (Fin S.card) (Fin S.card) K) * X₁ =
      X₁ * ((ζ : K) • (E₁ : Matrix (Fin S.card) (Fin S.card) K)) := by
    have e := congrArg (fun z : GL (Fin S.card) K => (z * E₁ : GL (Fin S.card) K)) hE₁X
    simp only [inv_mul_cancel_right] at e
    have e2 := congrArg (fun z : GL (Fin S.card) K => (z : Matrix (Fin S.card) (Fin S.card) K)) e
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e2
    rw [e2, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  set E' : unitarySU 2 n K d := blockExtSU S h ⟨E₁, hE₁⟩ with hE'
  have hE'c : (((E' : unitarySU 2 n K d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blockExt S (E₁ : Matrix (Fin S.card) (Fin S.card) K) := rfl
  have hPN := LineU.primeForm_mem_normalizer h hP
  refine ⟨P * (E' : GL (Fin d) K) * P⁻¹,
    (Subgroup.mem_normalizer_iff.mp hPN ((E' : GL (Fin d) K))).mp E'.2, ?_, ?_⟩
  ·
    have hkey : (E' : GL (Fin d) K) * Y = blockScalar S ζ * Y * (E' : GL (Fin d) K) := by
      have h1 := blockExt_mul_eq_mul_blockExt hxS (N₁ := (E₁ : Matrix (Fin S.card) (Fin S.card) K))
        (N₂ := (ζ : K) • (E₁ : Matrix (Fin S.card) (Fin S.card) K)) (by rw [← hX₁c]; exact hE₁m)
      have h2 := blockExt_smul_one_comm hxS (ζ : K)
      apply Units.ext
      change (((E' : unitarySU 2 n K d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          (Y : Matrix (Fin d) (Fin d) K) =
        ((blockScalar S ζ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          (Y : Matrix (Fin d) (Fin d) K) *
            (((E' : unitarySU 2 n K d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      rw [hE'c, coe_blockScalar, h1, h2, Matrix.mul_assoc, ← blockExt_mul, Matrix.smul_mul,
        Matrix.one_mul]
    calc P * (E' : GL (Fin d) K) * P⁻¹ * x * (P * (E' : GL (Fin d) K) * P⁻¹)⁻¹ =
        P * ((E' : GL (Fin d) K) * Y) * (E' : GL (Fin d) K)⁻¹ * P⁻¹ := by rw [hY]; group
      _ = P * blockScalar S ζ * P⁻¹ * x := by rw [hkey, hY]; group
  · intro y hyS ⟨c, hc⟩
    have hcomm : (E' : GL (Fin d) K) * (P⁻¹ * y * P) = (P⁻¹ * y * P) * (E' : GL (Fin d) K) := by
      apply Units.ext
      change (((E' : unitarySU 2 n K d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((P⁻¹ * y * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((P⁻¹ * y * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          (((E' : unitarySU 2 n K d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      rw [hE'c]
      refine blockExt_mul_eq_mul_blockExt hyS ?_
      rw [hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    calc P * (E' : GL (Fin d) K) * P⁻¹ * y =
        P * ((E' : GL (Fin d) K) * (P⁻¹ * y * P)) * P⁻¹ := by group
      _ = y * (P * (E' : GL (Fin d) K) * P⁻¹) := by rw [hcomm]; group

theorem projConj_mem_inducedSub_of_commute {n p : ℕ} (hcov : LineU.UnitaryCoverAt n d K)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ M : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
      ∀ l : L', TableB.projConj (unitarySU 2 n K d) M (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent p A) (δ : unitarySU 2 n K d) (hδp : δ ^ p = 1)
    (hδc : ∀ M : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
      TableB.projConj (unitarySU 2 n K d) M ∈ TypeA.inducedSub ψ A →
        (M : GL (Fin d) K) * δ = δ * M) :
    TableB.projConj (unitarySU 2 n K d)
      ⟨(δ : GL (Fin d) K), Subgroup.le_normalizer δ.2⟩ ∈ TypeA.inducedSub ψ A := by
  obtain ⟨hperfSU, hcov'⟩ := hcov
  obtain ⟨φ, hφ⟩ := hcov' L' ψ hψ hker hperf
  have hn₀p : φ δ ^ p = 1 := by rw [← map_pow, hδp, map_one]
  have hfix : ∀ a ∈ A, a (φ δ) = φ δ := by
    intro a ha
    obtain ⟨M, hM⟩ := hAI a ha
    have hMA : TableB.projConj (unitarySU 2 n K d) M ∈ TypeA.inducedSub ψ A :=
      TypeA.mem_inducedSub.mpr ⟨a, ha, hM⟩
    have hfun : (MulEquiv.toMonoidHom a).comp φ = φ.comp (LineU.conjNHom (M : GL (Fin d) K) M.2) := by
      apply TypeA.eq_of_inv_mul_mem_center hperfSU
      intro s
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, LineU.coe_conjNHom]
      rw [← hM (φ s), hφ s, LineU.projConj_mk_eq _ M.2 s, ← hφ (LineU.conjN _ M.2 s), inv_mul_cancel]
    have e := congrArg (fun f => f δ) hfun
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, LineU.coe_conjNHom] at e
    rw [e]
    congr 1
    apply Subtype.ext
    rw [LineU.coe_conjN, hδc M hMA, mul_inv_cancel_right]
  refine TypeA.mem_inducedSub.mpr ⟨MulAut.conj (φ δ), hsc (φ δ) hfix hn₀p, fun l => ?_⟩
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (ψ l)
  have hs' : ψ l = LargeEvenProjMk (unitarySU 2 n K d) s := hs.symm
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hφ, hs', LineU.projConj_mk_eq]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
