module

public import CFSG.LocalAnalysis.StandardType.GGKD2UnitaryPieces1615
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUComp
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdNode
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9InnerDiag

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom)

private lemma ltrcu2c_entry_zero
    {d n : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 n K) (hdvd : 3 ∣ 2 ^ n + 1)
    {N : GL (Fin d) K}
    (hNnorm : N ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {I : Finset (Fin d)}
    (hconj : ∀ b : ↥(unitarySU 2 n K d), b ∈ TableBUE.blockSU (K := K) (n := n) I →
      (unitarySU 2 n K d).normalizerMonoidHom ⟨N, hNnorm⟩ b ∈
        TableBUE.blockSU (K := K) (n := n) I)
    {i j κ : Fin d} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) (hκ : κ ∉ I) :
    ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) κ i = 0 := by
  classical
  obtain ⟨ζ, hζo, hζq⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one h (p := 3) (by norm_num) hdvd
  have hζne : ζ ≠ 1 := by
    intro h1
    have h31 : (3 : ℕ) = 1 := by
      calc (3 : ℕ) = orderOf ζ := hζo.symm
        _ = orderOf (1 : Kˣ) := by rw [h1]
        _ = 1 := orderOf_one
    omega
  let t : Fin d → Kˣ := Pi.mulSingle i ζ * Pi.mulSingle j ζ⁻¹
  have hti : t i = ζ := by simp [t, hij]
  have htj : t j = ζ⁻¹ := by simp [t, Ne.symm hij]
  have ht_off : ∀ l, l ≠ i → l ≠ j → t l = 1 := by
    intro l hli hlj
    simp [t, hli, hlj]
  have ht_unitary : diagHom d t ∈ unitarySU 2 n K d := by
    refine TableBUE.diagHom_mem_unitarySU h (fun k => ?_) ?_
    · simp only [t, Pi.mul_apply, Pi.mulSingle_apply]
      split_ifs <;> simp [hζq, inv_pow]
    · simp only [t, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
      exact mul_inv_cancel ζ
  let b0 : ↥(unitarySU 2 n K d) := ⟨diagHom d t, ht_unitary⟩
  have hb0B : b0 ∈ TableBUE.blockSU (K := K) (n := n) I := by
    rw [TableBUE.mem_blockSU]
    intro a b hab
    show (((diagHom d t : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) a b =
      (1 : Matrix (Fin d) (Fin d) K) a b
    rw [CFSG.SectionRank.OddCover.coe_diagHom]
    rcases hab with ha | hb
    · by_cases hab' : a = b
      · subst hab'
        rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        have hai : a ≠ i := fun h' => ha (h' ▸ hi)
        have haj : a ≠ j := fun h' => ha (h' ▸ hj)
        rw [ht_off a hai haj, Units.val_one]
      · rw [Matrix.diagonal_apply_ne _ hab', Matrix.one_apply_ne hab']
    · by_cases hab' : a = b
      · subst hab'
        rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        have hbi : a ≠ i := fun h' => hb (h' ▸ hi)
        have hbj : a ≠ j := fun h' => hb (h' ▸ hj)
        rw [ht_off a hbi hbj, Units.val_one]
      · rw [Matrix.diagonal_apply_ne _ hab', Matrix.one_apply_ne hab']
  let g' : ↥(unitarySU 2 n K d) :=
    (unitarySU 2 n K d).normalizerMonoidHom ⟨N, hNnorm⟩ b0
  have hg'B : g' ∈ TableBUE.blockSU (K := K) (n := n) I := hconj b0 hb0B
  have hGmBlock : TableBUE.IsBlockOn I
      (((g' : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) :=
    (TableBUE.mem_blockSU).mp hg'B
  have hg'val : ((g' : GL (Fin d) K)) = N * (b0 : GL (Fin d) K) * N⁻¹ := by
    change (((unitarySU 2 n K d).normalizerMonoidHom
        (⟨N, hNnorm⟩ : Subgroup.normalizer (unitarySU 2 n K d))) b0 : GL (Fin d) K) =
      N * (b0 : GL (Fin d) K) * N⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hmul : ((g' : GL (Fin d) K)) * N = N * (b0 : GL (Fin d) K) := by
    rw [hg'val]
    group
  have hmul_mat : ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((b0 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    have h := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K)) hmul
    simpa only [Units.val_mul] using h
  have hentry : (((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i =
      (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((b0 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i := by
    rw [hmul_mat]
  have hL : (((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i =
      (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i :=
    hGmBlock.mul_apply_left hκ i
  have hR : (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((b0 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i =
      (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i * (ζ : K) := by
    change (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((diagHom d t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i = _
    rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.mul_diagonal, hti]
  have hfin : (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i =
      (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i * (ζ : K) := by
    calc (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i
        = ((((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i) := hL.symm
      _ = ((((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((b0 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i) := hentry
      _ = (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i * (ζ : K) := hR
  have hzeta : (ζ : K) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h1
    exact hζne (Units.ext (by simpa using h1))
  have hzero : (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) κ i * ((ζ : K) - 1) = 0 := by
    rw [mul_sub, mul_one, ← hfin, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_right hzeta

theorem unitaryBlock_entry_zero
    {d n : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K)
    (hn : 2 ≤ n) (hdvd : 3 ∣ 2 ^ n + 1)
    {N : GL (Fin d) K}
    (hNnorm : N ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {I : Finset (Fin d)} (hI : I.card = 2)
    (hconj : ∀ b : ↥(unitarySU 2 n K d), b ∈ TableBUE.blockSU (K := K) (n := n) I →
      (unitarySU 2 n K d).normalizerMonoidHom ⟨N, hNnorm⟩ b ∈
        TableBUE.blockSU (K := K) (n := n) I) :
    ∀ i ∈ I, ∀ k : Fin d, k ∉ I →
      ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k i = 0 := by
  obtain ⟨i₀, i₁, hne, rfl⟩ := Finset.card_eq_two.mp hI
  intro i hi κ hκ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with hmem | hmem
  · rw [hmem]
    exact ltrcu2c_entry_zero (i := i₀) (j := i₁) (κ := κ) h hdvd hNnorm hconj
      (by simp) (by simp) hne hκ
  · rw [hmem]
    exact ltrcu2c_entry_zero (i := i₁) (j := i₀) (κ := κ) h hdvd hNnorm hconj
      (by simp) (by simp) hne.symm hκ

private theorem ltrcu2d_blockRes_mul_of_lowerZero {d : ℕ} {K : Type} [Field K]
    {I : Finset (Fin d)} {M N : Matrix (Fin d) (Fin d) K}
    (hN : ∀ i ∈ I, ∀ k : Fin d, k ∉ I → N k i = 0) :
    TableBUE.blockRes I (M * N) = TableBUE.blockRes I M * TableBUE.blockRes I N := by
  ext a b
  simp only [TableBUE.blockRes, Matrix.mul_apply]
  set e := I.equivFin.symm with he
  have hz : ∀ k ∉ I, M (e a) k * N k (e b) = 0 := by
    intro k hk
    rw [hN (e b) (e b).2 k hk, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ I) fun k _ hk => hz k hk,
    ← Finset.sum_coe_sort I]
  exact (Equiv.sum_comp e fun k : ↥I => M (e a) k * N k (e b)).symm

private theorem ltrcu2d_isBlockDiag_of_isBlockOn {d : ℕ} {K : Type} [Field K]
    {S : Finset (Fin d)} {M : Matrix (Fin d) (Fin d) K} (hM : TableBUE.IsBlockOn S M) :
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.IsBlockDiag S M := by
  intro i j hij
  rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rw [hM i j (Or.inr hj)]
    exact Matrix.one_apply_ne (fun h => hj (h ▸ hi))
  · rw [hM i j (Or.inl hi)]
    exact Matrix.one_apply_ne (fun h => hi (h ▸ hj))

private theorem ltrcu2d_isBlockDiag_of_shape
    {d n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    {N : GL (Fin d) K} (hNgu : N ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    {I : Finset (Fin d)}
    (hshape : ∀ i ∈ I, ∀ k : Fin d, k ∉ I →
      ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k i = 0) :
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.IsBlockDiag I
      ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  classical
  obtain ⟨μ, hμ0, hμq, hAsim⟩ := hNgu
  set A : Matrix (Fin d) (Fin d) K := ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hA
  have hshapeA : ∀ i ∈ I, ∀ k : Fin d, k ∉ I → A k i = 0 := by
    intro i hi k hk
    rw [hA]
    exact hshape i hi k hk
  have hAsimA : Matrix.transpose (A.map h.bar) * A = μ • (1 : Matrix (Fin d) (Fin d) K) := by
    have hmap : (A.map h.bar) = (A.map fun x : K => x ^ 2 ^ n) := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply]
    rw [hmap]
    exact hAsim
  have hPsim : Matrix.transpose ((TableBUE.blockRes I A).map h.bar) * TableBUE.blockRes I A =
      μ • (1 : Matrix (Fin I.card) (Fin I.card) K) := by
    have h1 : TableBUE.blockRes I (Matrix.transpose (A.map h.bar) * A) =
        μ • (1 : Matrix (Fin I.card) (Fin I.card) K) := by
      rw [hAsimA, CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockRes_smul_one]
    rw [ltrcu2d_blockRes_mul_of_lowerZero (I := I) (M := Matrix.transpose (A.map h.bar))
      (N := A) hshapeA, TableBUE.blockRes_map_transpose] at h1
    exact h1
  have hdet : (TableBUE.blockRes I A).det ≠ 0 := by
    intro h0
    have hbar : (Matrix.transpose ((TableBUE.blockRes I A).map h.bar)).det =
        h.bar ((TableBUE.blockRes I A).det) := by
      rw [Matrix.det_transpose]
      have h1 := RingHom.map_det h.bar (TableBUE.blockRes I A)
      rw [show h.bar.mapMatrix (TableBUE.blockRes I A) =
        ((TableBUE.blockRes I A).map h.bar) from rfl] at h1
      exact h1.symm
    have h2 := congrArg Matrix.det hPsim
    rw [Matrix.det_mul, hbar, h0, map_zero, zero_mul, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, mul_one] at h2
    exact (pow_ne_zero (I.card) hμ0) h2.symm
  let Pgl : GL (Fin I.card) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (TableBUE.blockRes I A) hdet
  have hPgl_coe : ((Pgl : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) =
      TableBUE.blockRes I A := Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  let Q : Matrix (Fin I.card) {j : Fin d // j ∉ I} K :=
    fun a j => A (I.equivFin.symm a) j.val
  have hPQ : Matrix.transpose ((TableBUE.blockRes I A).map h.bar) * Q = 0 := by
    ext a j
    have hglob := congrFun (congrFun hAsimA (I.equivFin.symm a)) j.val
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply] at hglob
    rw [if_neg (show ((I.equivFin.symm a : ↥I) : Fin d) ≠ j.val from fun hh =>
      j.2 (hh ▸ (I.equivFin.symm a).2)), smul_zero] at hglob
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, TableBUE.blockRes,
      Matrix.zero_apply, Q]
    rw [← hglob]
    rw [← Finset.sum_subset (Finset.subset_univ I) (fun x _ hx => by
      rw [hshapeA (I.equivFin.symm a) (I.equivFin.symm a).2 x hx, map_zero, zero_mul]),
      ← Finset.sum_coe_sort I]
    exact Equiv.sum_comp (I.equivFin.symm) fun x : ↥I =>
      h.bar (A x (I.equivFin.symm a)) * A x j.val
  have hPinv : TableBUE.blockRes I A *
      ((Pgl⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) = 1 := by
    rw [← hPgl_coe, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPstar : Matrix.transpose ((TableBUE.blockRes I A).map h.bar) =
      μ • ((Pgl⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) := by
    calc Matrix.transpose ((TableBUE.blockRes I A).map h.bar)
        = Matrix.transpose ((TableBUE.blockRes I A).map h.bar) *
            (TableBUE.blockRes I A *
              ((Pgl⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K)) := by
          rw [hPinv, mul_one]
      _ = (Matrix.transpose ((TableBUE.blockRes I A).map h.bar) * TableBUE.blockRes I A) *
            ((Pgl⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) := by
          exact (Matrix.mul_assoc _ _ _).symm
      _ = (μ • (1 : Matrix (Fin I.card) (Fin I.card) K)) *
            ((Pgl⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) := by
          rw [hPsim]
      _ = μ • ((Pgl⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) := by
          rw [Matrix.smul_mul, Matrix.one_mul]
  have hQzero : Q = 0 := by
    have h1 : ((Pgl⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) * Q = 0 := by
      have h2 := hPQ
      rw [hPstar, Matrix.smul_mul] at h2
      rcases smul_eq_zero.mp h2 with hh | hh
      · exact absurd hh hμ0
      · exact hh
    calc Q = (TableBUE.blockRes I A *
            ((Pgl⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K)) * Q := by
          rw [hPinv, Matrix.one_mul]
      _ = TableBUE.blockRes I A *
            (((Pgl⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) * Q) := by
          exact Matrix.mul_assoc _ _ _
      _ = 0 := by rw [h1, Matrix.mul_zero]
  intro i j hij
  rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hh := congrFun (congrFun hQzero (I.equivFin ⟨i, hi⟩)) ⟨j, hj⟩
    simpa [Q, hA] using hh
  · exact hshape j hj i hi

private theorem ltrcu2d_scalar_conj_cancel {k : ℕ} {K : Type} [Field K]
    (z : Kˣ) (h m : GL (Fin k) K) :
    (Matrix.GeneralLinearGroup.scalar (Fin k) z * h) * m *
        (Matrix.GeneralLinearGroup.scalar (Fin k) z * h)⁻¹ = h * m * h⁻¹ := by
  have hz : Matrix.GeneralLinearGroup.scalar (Fin k) z ∈ Subgroup.center (GL (Fin k) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact (commute_scalar z g).eq
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin k) z) (h * m * h⁻¹) :=
    (Subgroup.mem_center_iff.mp hz _).symm
  calc (Matrix.GeneralLinearGroup.scalar (Fin k) z * h) * m *
        (Matrix.GeneralLinearGroup.scalar (Fin k) z * h)⁻¹
      = Matrix.GeneralLinearGroup.scalar (Fin k) z * (h * m * h⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin k) z)⁻¹ := by group
    _ = (h * m * h⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin k) z *
          (Matrix.GeneralLinearGroup.scalar (Fin k) z)⁻¹ := by rw [hcomm.eq]
    _ = h * m * h⁻¹ := by group

theorem unitaryBlock_conj_inner_of_shape
    {d n : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    {N : GL (Fin d) K}
    (hNnorm : N ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hNgu : N ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    {I : Finset (Fin d)} (hI : I.card = 2)
    (hshape : ∀ i ∈ I, ∀ k : Fin d, k ∉ I →
      ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k i = 0)
    (hconj : ∀ b : ↥(unitarySU 2 n K d), b ∈ TableBUE.blockSU (K := K) (n := n) I →
      (unitarySU 2 n K d).normalizerMonoidHom ⟨N, hNnorm⟩ b ∈
        TableBUE.blockSU (K := K) (n := n) I) :
    ∃ s : ↥(unitarySU 2 n K d), s ∈ TableBUE.blockSU (K := K) (n := n) I ∧
      ∀ b : ↥(unitarySU 2 n K d), b ∈ TableBUE.blockSU (K := K) (n := n) I →
        (unitarySU 2 n K d).normalizerMonoidHom ⟨N, hNnorm⟩ b = s * b * s⁻¹ := by
  classical
  obtain ⟨μ, hμ0, hμq, hAsim⟩ := hNgu
  have hAsim' : Matrix.transpose (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar) *
      ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      μ • (1 : Matrix (Fin d) (Fin d) K) := by
    have hmap : (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar) =
        (((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map fun x : K => x ^ 2 ^ n) := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply]
    rw [hmap]
    exact hAsim
  have hAdiag : CFSG.LocalAnalysis.GLTheoremA.T171Sh.IsBlockDiag I
      ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    ltrcu2d_isBlockDiag_of_shape h ⟨μ, hμ0, hμq, hAsim⟩ hshape
  have hPsim : Matrix.transpose ((TableBUE.blockRes I
      ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).map h.bar) *
      TableBUE.blockRes I ((N : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      μ • (1 : Matrix (Fin I.card) (Fin I.card) K) :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockRes_similitude (S := I) h hAdiag hAsim'
  have hk : Nat.Coprime I.card (2 ^ n + 1) := by
    rw [hI]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact Nat.coprime_two_left.mpr ⟨2 ^ m, by rw [pow_succ]; ring⟩
  obtain ⟨z, h', h'mem, hPdecomp⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.exists_scalar_mul_mem_unitarySU_of_similitude
      h hk (ν := Units.mk0 μ hμ0)
      (U := CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockResGL hAdiag) (by simpa using hμq)
      (by simpa only [CFSG.LocalAnalysis.GLTheoremA.T171Sh.coe_blockResGL hAdiag,
        Units.val_mk0] using hPsim)
  let s : ↥(unitarySU 2 n K d) := TableBUE.blockExtSU I h ⟨h', h'mem⟩
  have hsB : s ∈ TableBUE.blockSU (K := K) (n := n) I := by
    rw [← TableBUE.range_blockExtSU (S := I) (h := h)]
    exact ⟨⟨h', h'mem⟩, rfl⟩
  refine ⟨s, hsB, fun b hb => ?_⟩
  have hbOn : TableBUE.IsBlockOn I ((b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    TableBUE.mem_blockSU.mp hb
  have hbDiag : CFSG.LocalAnalysis.GLTheoremA.T171Sh.IsBlockDiag I
      ((b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    ltrcu2d_isBlockDiag_of_isBlockOn hbOn
  let bIgl : GL (Fin I.card) K := CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockResGL hbDiag
  have hbIgl_coe : ((bIgl : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) =
      TableBUE.blockRes I ((b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.coe_blockResGL hbDiag
  have hs_coe : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      TableBUE.blockExt I ((h' : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) :=
    TableBUE.coe_blockExtSU (S := I) (h := h) ⟨h', h'mem⟩
  have hSon : TableBUE.IsBlockOn I ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    TableBUE.mem_blockSU.mp hsB
  have hSdiag : CFSG.LocalAnalysis.GLTheoremA.T171Sh.IsBlockDiag I
      ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    ltrcu2d_isBlockDiag_of_isBlockOn hSon
  have hSgl : CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockResGL hSdiag = h' := by
    apply Units.ext
    rw [CFSG.LocalAnalysis.GLTheoremA.T171Sh.coe_blockResGL, hs_coe,
      TableBUE.blockRes_blockExt]
  apply Subtype.ext
  apply Units.ext
  set Lm : Matrix (Fin d) (Fin d) K :=
    ((((unitarySU 2 n K d).normalizerMonoidHom ⟨N, hNnorm⟩ b : ↥(unitarySU 2 n K d)) :
      GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hLm
  set Rm : Matrix (Fin d) (Fin d) K :=
    ((((s * b * s⁻¹ : ↥(unitarySU 2 n K d))) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) with hRm
  have hLon : TableBUE.IsBlockOn I Lm := by
    rw [hLm]
    exact TableBUE.mem_blockSU.mp (hconj b hb)
  have hRon : TableBUE.IsBlockOn I Rm := by
    rw [hRm]
    exact TableBUE.mem_blockSU.mp ((TableBUE.blockSU (K := K) (n := n) I).mul_mem
      ((TableBUE.blockSU (K := K) (n := n) I).mul_mem hsB hb)
      ((TableBUE.blockSU (K := K) (n := n) I).inv_mem hsB))
  have hLres : TableBUE.blockRes I Lm =
      ((CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockResGL hAdiag * bIgl *
        (CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockResGL hAdiag)⁻¹ : GL (Fin I.card) K) :
        Matrix (Fin I.card) (Fin I.card) K) := by
    rw [hLm, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp only [Units.val_mul]
    rw [CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockRes_conj_eq hAdiag hbOn]
    simp only [Units.val_mul, CFSG.LocalAnalysis.GLTheoremA.T171Sh.coe_blockResGL, bIgl]
  have hRres : TableBUE.blockRes I Rm =
      ((h' * bIgl * h'⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) := by
    rw [hRm]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockRes_conj_eq hSdiag hbOn]
    rw [hSgl, ← hbIgl_coe]
  have hscal : ((CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockResGL hAdiag * bIgl *
      (CFSG.LocalAnalysis.GLTheoremA.T171Sh.blockResGL hAdiag)⁻¹ : GL (Fin I.card) K) :
      Matrix (Fin I.card) (Fin I.card) K) =
      ((h' * bIgl * h'⁻¹ : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K) := by
    rw [hPdecomp]
    exact congrArg (fun g : GL (Fin I.card) K => (g : Matrix (Fin I.card) (Fin I.card) K))
      (ltrcu2d_scalar_conj_cancel z h' bIgl)
  have hbres : TableBUE.blockRes I Lm = TableBUE.blockRes I Rm := by
    rw [hLres, hRres]
    exact hscal
  calc Lm = TableBUE.blockExt I (TableBUE.blockRes I Lm) :=
        (TableBUE.blockExt_blockRes hLon).symm
    _ = TableBUE.blockExt I (TableBUE.blockRes I Rm) := by rw [hbres]
    _ = Rm := TableBUE.blockExt_blockRes hRon

end CFSG.StandardType.KD2Pieces1615

end
