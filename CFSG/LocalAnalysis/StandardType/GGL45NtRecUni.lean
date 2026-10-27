module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

private theorem ggL45NtRecUni_bar_map {n d : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (M : Matrix (Fin d) (Fin d) K) :
    M.map (· ^ 2 ^ n) = M.map h.bar := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply]

private theorem ggL45NtRecUni_gu_one {n d : ℕ} {K : Type} [Field K] :
    (1 : GL (Fin d) K) ∈ LargeEvenGUSet (Fin d) K (2 ^ n) :=
  ⟨1, one_ne_zero, one_pow _, by simp⟩

private theorem ggL45NtRecUni_gu_mul {n d : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) {A B : GL (Fin d) K}
    (hA : A ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hB : B ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    A * B ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := by
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  obtain ⟨ν, hν0, hνq, hBν⟩ := hB
  rw [ggL45NtRecUni_bar_map h] at hAμ hBν
  refine ⟨μ * ν, mul_ne_zero hμ0 hν0, by rw [mul_pow, hμq, hνq], ?_⟩
  rw [ggL45NtRecUni_bar_map h, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ
    (A : Matrix (Fin d) (Fin d) K) (B : Matrix (Fin d) (Fin d) K)]
  rw [hAμ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hBν, smul_smul]

private theorem ggL45NtRecUni_gu_inv {n d : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) {A : GL (Fin d) K}
    (hA : A ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    A⁻¹ ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := by
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  rw [ggL45NtRecUni_bar_map h] at hAμ
  refine ⟨μ⁻¹, inv_ne_zero hμ0, by rw [inv_pow, hμq], ?_⟩
  rw [ggL45NtRecUni_bar_map h]
  have hAA : (A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
      μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    calc ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
          ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
            ((A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
            rw [hAA, Matrix.mul_one]
      _ = μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
            rw [← Matrix.mul_assoc, hAμ, Matrix.smul_mul, Matrix.one_mul]
  have h2 : (((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      (μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 := by
    rw [← h1, ← Matrix.transpose_mul, ← Matrix.map_mul, hAA,
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one]
  rw [Matrix.mul_smul] at h2
  rw [← h2, smul_smul, inv_mul_cancel₀ hμ0, one_smul]

private theorem ggL45NtRecUni_su_subset_gu {n d : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) :
    (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) ⊆
      LargeEvenGUSet (Fin d) K (2 ^ n) := by
  intro A hA
  unfold LargeEvenSUGroup at hA
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact ⟨1, one_ne_zero, one_pow _, by rw [one_smul]; exact hx.2⟩
  | one => exact ggL45NtRecUni_gu_one
  | mul x y _ _ ihx ihy => exact ggL45NtRecUni_gu_mul h ihx ihy
  | inv x _ ihx => exact ggL45NtRecUni_gu_inv h ihx

private theorem ggL45NtRecUni_pow_d_mem {K : Type} [Field K] [Finite K] {n d : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hN : LargeEvenGUSet (Fin d) K (2 ^ n) ⊆
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)))
    {A : GL (Fin d) K} (hA : A ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) ⟨A, hN hA⟩ ^ d ∈
      Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  classical
  have h := TableBU.unitaryFieldData_of_card hK hn
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  have hAmem : A ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := ⟨μ, hμ0, hμq, hAμ⟩
  have hAμσ : ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) =
      μ • 1 := by
    rw [← ggL45NtRecUni_bar_map h]
    exact hAμ
  set x : Kˣ := Matrix.GeneralLinearGroup.det A with hx
  have hxval : (x : K) = (A : Matrix (Fin d) (Fin d) K).det :=
    Matrix.GeneralLinearGroup.val_det_apply A
  have hxq : (x : K) ^ (2 ^ n) * (x : K) = μ ^ d := by
    have hdet := congrArg Matrix.det hAμσ
    rw [Matrix.det_mul, Matrix.det_transpose] at hdet
    rw [show (A : Matrix (Fin d) (Fin d) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin d) (Fin d) K) from rfl] at hdet
    rw [← RingHom.map_det] at hdet
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, UnitaryFieldData.bar_apply,
      ← hxval] at hdet
    exact hdet
  set B : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) x⁻¹ * A ^ d with hB
  have hcoeb : (B : Matrix (Fin d) (Fin d) K) =
      (x⁻¹ : K) • ((A : Matrix (Fin d) (Fin d) K) ^ d) := by
    rw [hB, TableB.coe_scalar_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  have hBdet : (B : Matrix (Fin d) (Fin d) K).det = 1 := by
    rw [hcoeb, Matrix.det_smul, Matrix.det_pow, Fintype.card_fin, ← hxval, ← mul_pow,
      inv_mul_cancel₀ (Units.ne_zero x), one_pow]
  have hAinv : (A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcomm : Commute ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ
      (A : Matrix (Fin d) (Fin d) K) := by
    show ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) =
      (A : Matrix (Fin d) (Fin d) K) * ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ
    have hM : ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
        μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      calc ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
            ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
              ((A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
              rw [hAinv, Matrix.mul_one]
        _ = (((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K)) *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [Matrix.mul_assoc]
        _ = (μ • 1) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [hAμσ]
        _ = μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
              rw [Matrix.smul_mul, Matrix.one_mul]
    have hAM : (A : Matrix (Fin d) (Fin d) K) * ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
        μ • 1 := by
      calc (A : Matrix (Fin d) (Fin d) K) * ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
            (A : Matrix (Fin d) (Fin d) K) *
              (μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by rw [hM]
        _ = μ • ((A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
              rw [Matrix.mul_smul]
        _ = μ • 1 := by rw [hAinv]
    rw [hAμσ]
    exact hAM.symm
  have hBuniσ : ((B : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (B : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hcoeb, TableB.transpose_map_smul, Matrix.map_pow, Matrix.transpose_pow, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    have hpow : (((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ) ^ d *
        (A : Matrix (Fin d) (Fin d) K) ^ d = μ ^ d • 1 := by
      rw [← hcomm.mul_pow, hAμσ, Matrix.smul_one_eq_diagonal, Matrix.diagonal_pow]
      have hfun : ((fun _ : Fin d => μ) ^ d) = fun _ : Fin d => μ ^ d := by
        funext i
        simp
      rw [hfun, ← Matrix.smul_one_eq_diagonal]
    rw [hpow, smul_smul]
    have hsc : h.bar (x⁻¹ : K) * (x⁻¹ : K) = (μ ^ d)⁻¹ := by
      rw [UnitaryFieldData.bar_apply, show (x⁻¹ : K) = (x : K)⁻¹ from rfl, inv_pow, ← mul_inv_rev,
        mul_comm (x : K) ((x : K) ^ 2 ^ n), ← hxq]
    rw [hsc, inv_mul_cancel₀ (pow_ne_zero d hμ0), one_smul]
  have hBmem : B ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
    unfold LargeEvenSUGroup
    refine Subgroup.subset_closure ⟨hBdet, ?_⟩
    rw [ggL45NtRecUni_bar_map h]
    exact hBuniσ
  have hAeq : (⟨A, hN hAmem⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) ^ d =
      ⟨Matrix.GeneralLinearGroup.scalar (Fin d) x,
        TableB.scalar_mem_normalizer _ ⟨x, rfl⟩⟩ *
        ⟨B, Subgroup.le_normalizer hBmem⟩ := by
    apply Subtype.ext
    show (A : GL (Fin d) K) ^ d = Matrix.GeneralLinearGroup.scalar (Fin d) x * B
    rw [hB, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hinner : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
      (⟨A, hN hAmem⟩ ^ d) ∈
      Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
    rw [hAeq, map_mul, TableB.projConj_of_scalar _ ⟨x, rfl⟩, one_mul,
      TableB.projConj_of_mem _ B hBmem]
    exact ⟨((⟨B, hBmem⟩ : LargeEvenSUGroup (Fin d) K (2 ^ n)) :
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))), rfl⟩
  rw [← map_pow]
  exact hinner

private theorem ggL45NtRecUni_aux
    {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d) :
    GGL45NtRec p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  intro _ _
  have h := TableBU.unitaryFieldData_of_card hK hn
  set H := LargeEvenSUGroup (Fin d) K (2 ^ n) with hH
  have hN : LargeEvenGUSet (Fin d) K (2 ^ n) ⊆ Subgroup.normalizer (H : Set (GL (Fin d) K)) :=
    TableBUE.gu_subset_normalizer h
  have hSUgu : (H : Set (GL (Fin d) K)) ⊆ LargeEvenGUSet (Fin d) K (2 ^ n) :=
    ggL45NtRecUni_su_subset_gu h
  refine ⟨?_, ?_, ?_⟩
  · intro r
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective ((LargeEvenScalars (Fin d) K).subgroupOf H) r
    refine ⟨a, hSUgu a.2, ?_⟩
    intro x y hxy
    rw [MulAut.conj_apply]
    have h1 : (LargeEvenProjMk H a) * (LargeEvenProjMk H x) * (LargeEvenProjMk H a)⁻¹ =
        LargeEvenProjMk H (a * x * a⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [h1]
    congr 1
    exact Subtype.ext hxy.symm
  · intro u hu hup
    obtain ⟨k, hk⟩ := hup
    obtain ⟨A, hA, rfl⟩ := TableB.exists_eq_projConj hN hu
    have hdmem : TableB.projConj H ⟨A, hN hA⟩ ^ d ∈
        (MulAut.conj : LargeEvenProj H →* MulAut (LargeEvenProj H)).range :=
      ggL45NtRecUni_pow_d_mem hK hn hN hA
    have hmem : TableB.projConj H ⟨A, hN hA⟩ ∈
        (MulAut.conj : LargeEvenProj H →* MulAut (LargeEvenProj H)).range := by
      set N := (MulAut.conj : LargeEvenProj H →* MulAut (LargeEvenProj H)).range
      have h1 : (QuotientGroup.mk' N (TableB.projConj H ⟨A, hN hA⟩)) ^ d = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff (N := N) _).mpr hdmem
      have h2 : (QuotientGroup.mk' N (TableB.projConj H ⟨A, hN hA⟩)) ^ (p ^ k) = 1 := by
        rw [← map_pow, hk, map_one]
      have hgcd : Nat.gcd d (p ^ k) = 1 :=
        Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm
      have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
      rw [hgcd, pow_one] at h3
      exact (QuotientGroup.eq_one_iff _).mp h3
    obtain ⟨r, hr⟩ := hmem
    exact ⟨r, hr.symm⟩
  · exact StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd

theorem ggL45NtRecOn_uni :
    GGL45NtRecOn GGL45NtFamUni := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  rcases hS.2 with htag | ⟨htag, hrank⟩
  · subst htag
    have hpd : ¬ p ∣ rank + 1 := hS.1.1
    have hdq : (rank + 1, 2 ^ n) ≠ (3, 2) := by
      intro he
      have h1 : rank = 2 := by
        have := congrArg Prod.fst he
        simpa using this
      have h2 : 2 ^ n = 2 := congrArg Prod.snd he
      have hn2 : 2 ≤ n := hlab.2.2 h1
      have hle : 2 ^ (2 : ℕ) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      rw [h2] at hle
      norm_num at hle
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    exact ⟨K, hf, hfin, hK, hQ',
      ggL45NtRecUni_aux hK hlab.1 (Nat.succ_le_succ hlab.2.1) hdq hp hp2 hpd⟩
  · subst htag
    subst hrank
    have hpd : ¬ p ∣ 4 := by
      intro hdvd
      have h2 : p ∣ 2 ^ 2 := by simpa using hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    exact ⟨K, hf, hfin, hK, hQ',
      ggL45NtRecUni_aux hK hlab.1 (by norm_num : 3 ≤ 4) (by norm_num) hp hp2 hpd⟩

end CFSG.StandardType
