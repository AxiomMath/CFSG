module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Leaves
import CFSG.RankThree.PartTwo.Sec4.Item426A6U43
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.Quasithin.Background.A318PL3Inst
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

open Matrix CFSG.Blueprint

section Linear

variable {L : Type*} [Field L] [CharP L 3]

theorem pair_eig {A : Matrix (Fin 4) (Fin 4) L} (hu : (A.map (frobenius L 3))ᵀ * A = 1)
    {a b : L} {u w : Fin 4 → L} (hAu : A *ᵥ u = a • u) (hAw : A *ᵥ w = b • w) :
    a ^ 3 * b * ((fun i => u i ^ 3) ⬝ᵥ w) = (fun i => u i ^ 3) ⬝ᵥ w := by
  have h1 : A.map (frobenius L 3) *ᵥ (fun i => u i ^ 3) = a ^ 3 • (fun i => u i ^ 3) := by
    funext i
    have := RingHom.map_mulVec (frobenius L 3) A u i
    rw [hAu] at this
    simpa [frobenius_def, mul_pow, Function.comp_def] using this.symm
  calc a ^ 3 * b * ((fun i => u i ^ 3) ⬝ᵥ w)
      = (a ^ 3 • (fun i => u i ^ 3)) ⬝ᵥ (b • w) := by
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
    _ = (A.map (frobenius L 3) *ᵥ (fun i => u i ^ 3)) ⬝ᵥ (A *ᵥ w) := by rw [h1, hAw]
    _ = (fun i => u i ^ 3) ⬝ᵥ w := by
        rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, hu, one_mulVec]

theorem core_five [IsAlgClosed L] {B : Matrix (Fin 4) (Fin 4) L}
    (hu : (B.map (frobenius L 3))ᵀ * B = 1) (h5 : B ^ 5 = 1) (hB1 : B ≠ 1) :
    ∃ v : Fin 4 → L, v ≠ 0 ∧ ∀ A : Matrix (Fin 4) (Fin 4) L, A * B = B * A →
      (A.map (frobenius L 3))ᵀ * A = 1 → A.det = 1 →
      ∃ c : L, A *ᵥ v = c • v ∧ c ^ 20 = 1 ∧ (c ^ 4 = 1 → A = Matrix.scalar (Fin 4) c) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨μ, v, hv, hBv, hμ1⟩ : ∃ μ : L, ∃ v : Fin 4 → L, v ≠ 0 ∧ B *ᵥ v = μ • v ∧ μ ≠ 1 := by
    set Q := B ^ 4 + B ^ 3 + B ^ 2 + B + 1 with hQ
    have hQB : Q * (B - 1) = B ^ 5 - 1 := by rw [hQ]; noncomm_ring
    have hcomm : B * Q = Q * B := by rw [hQ]; noncomm_ring
    obtain ⟨u, hu'⟩ : ∃ u, (B - 1) *ᵥ u ≠ 0 := by
      by_contra hcon
      apply hB1
      have h0 : B - 1 = 0 := Matrix.mulVec_injective (funext fun u => by
        by_contra hne
        exact hcon ⟨u, by simpa using hne⟩)
      exact sub_eq_zero.mp h0
    set W := LinearMap.ker (Matrix.toLin' Q) with hW
    have hinv : ∀ y ∈ W, Matrix.toLin' B y ∈ W := by
      intro y hy
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy ⊢
      rw [Matrix.toLin'_apply, mulVec_mulVec, ← hcomm, ← mulVec_mulVec, hy, mulVec_zero]
    have hmem : (B - 1) *ᵥ u ∈ W := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, mulVec_mulVec, hQB, h5, sub_self, zero_mulVec]
    have hne : W ≠ ⊥ := fun h => hu' (by rw [h] at hmem; exact (Submodule.mem_bot L).mp hmem)
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((Matrix.toLin' B).restrict hinv)
    obtain ⟨y, hy⟩ := hμ.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
    have hBy : B *ᵥ (y : Fin 4 → L) = μ • (y : Fin 4 → L) := by
      have := congrArg Subtype.val hy.1
      simpa [LinearMap.restrict_apply, Matrix.toLin'_apply] using this
    have hy0 : (y : Fin 4 → L) ≠ 0 := fun h => hy.2 (Subtype.ext h)
    refine ⟨μ, y, hy0, hBy, ?_⟩
    rintro rfl
    have hpow : ∀ k : ℕ, B ^ k *ᵥ (y : Fin 4 → L) = (y : Fin 4 → L) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBy, one_smul, ih]
    have hQy : Q *ᵥ (y : Fin 4 → L) = (5 : L) • (y : Fin 4 → L) := by
      have h1 := hpow 1
      rw [pow_one] at h1
      rw [hQ, add_mulVec, add_mulVec, add_mulVec, add_mulVec, hpow, hpow, hpow, h1, one_mulVec,
        show (5 : L) = 1 + 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, add_smul,
        one_smul]
    have hy' := y.2
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hQy] at hy'
    have h5ne : (5 : L) ≠ 0 := by
      intro h
      have h' : ((5 : ℕ) : L) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff L 3] at h'
      norm_num at h'
    exact hy0 ((smul_eq_zero.mp hy').resolve_left h5ne)
  obtain ⟨hμ5, v₂, hv₂, hBv₂⟩ := CFSG.RankThree.PartTwo.Sec4.Item426.exists_eig_sq hu h5 hv hBv
  obtain ⟨-, v₄, hv₄, hBv₄⟩ := CFSG.RankThree.PartTwo.Sec4.Item426.exists_eig_sq hu h5 hv₂ hBv₂
  obtain ⟨-, v₃, hv₃, hBv₃⟩ := CFSG.RankThree.PartTwo.Sec4.Item426.exists_eig_sq hu h5 hv₄ hBv₄
  have hμo : orderOf μ = 5 := orderOf_eq_prime hμ5 hμ1
  have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at hμ5
  set lam : Fin 4 → L := fun i => μ ^ ((i : ℕ) + 1) with hlam_def
  set vec : Fin 4 → (Fin 4 → L) := ![v, v₂, v₃, v₄] with hvec_def
  have hvec : ∀ i, B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · simpa [hvec_def, hlam_def] using hBv
    · simpa [hvec_def, hlam_def] using hBv₂
    · have h8 : ((μ ^ 2) ^ 2) ^ 2 = μ ^ 3 := by
        rw [← pow_mul, ← pow_mul, show 2 * 2 * 2 = 5 + 3 by norm_num, pow_add, hμ5, one_mul]
      simpa [hvec_def, hlam_def, h8] using hBv₃
    · have h4 : (μ ^ 2) ^ 2 = μ ^ 4 := by rw [← pow_mul]
      simpa [hvec_def, hlam_def, h4] using hBv₄
  have hvec0 : ∀ i, vec i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [hvec_def] using hv
    · simpa [hvec_def] using hv₂
    · simpa [hvec_def] using hv₃
    · simpa [hvec_def] using hv₄
  have hlam : Function.Injective lam := by
    intro i j hij
    have hprim : IsPrimitiveRoot μ 5 := hμo ▸ IsPrimitiveRoot.orderOf μ
    have hi := i.2
    have hj := j.2
    have h := hprim.pow_inj (by omega) (by omega)
      (show μ ^ ((i : ℕ) + 1) = μ ^ ((j : ℕ) + 1) from hij)
    exact Fin.ext (by omega)
  have hli : LinearIndependent L vec :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B) lam hlam vec fun i => by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact ⟨hvec i, hvec0 i⟩
  have hcard : Fintype.card (Fin 4) = Module.finrank L (Fin 4 → L) := by simp
  set bs := basisOfLinearIndependentOfCardEqFinrank hli hcard with hbs_def
  have hbs : ∀ i, bs i = vec i := fun i => by simp [hbs_def]
  set σ : Fin 4 → Fin 4 := ![1, 3, 0, 2] with hσ
  have hlamσ : ∀ k, lam k ^ 3 * lam (σ k) = 1 := by
    have h10 : μ ^ 10 = 1 := by rw [show 10 = 5 * 2 by norm_num, pow_mul, hμ5, one_pow]
    have h15 : μ ^ 15 = 1 := by rw [show 15 = 5 * 3 by norm_num, pow_mul, hμ5, one_pow]
    intro k
    fin_cases k <;> simp [hlam_def, hσ, ← pow_mul, ← pow_add, hμ5, h10, h15] <;>
      first | done | (rw [← pow_succ]; exact h10)
  have hlam0 : ∀ k, lam k ≠ 0 := fun k => pow_ne_zero _ hμ0
  have hσ_unique : ∀ k j, lam k ^ 3 * lam j = 1 → j = σ k := by
    intro k j h
    apply hlam
    exact mul_left_cancel₀ (pow_ne_zero 3 (hlam0 k)) (h.trans (hlamσ k).symm)
  have hpair : ∀ k, (fun i => vec k i ^ 3) ⬝ᵥ vec (σ k) ≠ 0 := by
    intro k h0
    have hall : ∀ j, (fun i => vec k i ^ 3) ⬝ᵥ vec j = 0 := by
      intro j
      by_cases hj : j = σ k
      · rw [hj]; exact h0
      · have h := pair_eig hu (hvec k) (hvec j)
        have h' : (lam k ^ 3 * lam j - 1) * ((fun i => vec k i ^ 3) ⬝ᵥ vec j) = 0 := by
          rw [sub_mul, h, one_mul, sub_self]
        exact (mul_eq_zero.mp h').resolve_left
          (sub_ne_zero.mpr fun h1 => hj (hσ_unique k j h1))
    have hzero : ∀ w : Fin 4 → L, (fun i => vec k i ^ 3) ⬝ᵥ w = 0 := by
      intro w
      rw [← bs.sum_repr w, dotProduct_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [dotProduct_smul, hbs, hall j, smul_zero]
    apply hvec0 k
    funext i
    have := hzero (Pi.single i 1)
    rw [dotProduct_single, mul_one] at this
    exact (pow_eq_zero_iff (by norm_num)).mp this
  refine ⟨v, hv, ?_⟩
  intro A hAB hAu hdet
  have hAvec : ∀ k, ∃ c : L, A *ᵥ vec k = c • vec k := by
    intro k
    set x := A *ᵥ vec k with hx
    have hBx : B *ᵥ x = lam k • x := by
      rw [hx, mulVec_mulVec, ← hAB, ← mulVec_mulVec, hvec k, mulVec_smul]
    set c := bs.repr x with hc
    have hxsum : x = ∑ j, c j • vec j := by
      conv_lhs => rw [← bs.sum_repr x]
      simp only [hbs]
      rfl
    have hcoef : ∀ j, j ≠ k → c j = 0 := by
      intro j hjk
      have h1 : B *ᵥ x = ∑ j, (lam j * c j) • bs j := by
        rw [hxsum, mulVec_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mulVec_smul, hvec i, smul_smul, hbs, mul_comm]
      have h2 : lam k • x = ∑ j, (lam k * c j) • bs j := by
        rw [hxsum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, hbs]
      have h3 := congrArg (fun y => bs.repr y j) (h1.symm.trans (hBx.trans h2))
      simp only [bs.repr_sum_self] at h3
      have h4 : (lam j - lam k) * c j = 0 := by rw [sub_mul, h3, sub_self]
      exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr (hlam.ne hjk))
    exact ⟨c k, by rw [hxsum, Finset.sum_eq_single k (fun j _ hjk => by rw [hcoef j hjk,
      zero_smul]) (by simp)]⟩
  choose cf hcf using hAvec
  have hrel : ∀ k, cf k ^ 3 * cf (σ k) = 1 := by
    intro k
    have h := pair_eig hAu (hcf k) (hcf (σ k))
    have h' : (cf k ^ 3 * cf (σ k) - 1) * ((fun i => vec k i ^ 3) ⬝ᵥ vec (σ k)) = 0 := by
      rw [sub_mul, h, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right (hpair k))
  have hdetc : A.det = ∏ k, cf k := by
    have hmat : LinearMap.toMatrix bs bs (Matrix.toLin' A) = Matrix.diagonal cf := by
      ext i j
      rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hbs, hcf j, ← hbs, map_smul,
        bs.repr_self, Matrix.diagonal_apply, Finsupp.smul_apply, Finsupp.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [← LinearMap.det_toLin' A, ← LinearMap.det_toMatrix bs, hmat, Matrix.det_diagonal]
  have hr0 := hrel 0
  have hr1 := hrel 1
  have hr2 := hrel 2
  have hr3 := hrel 3
  simp only [hσ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons] at hr0 hr1 hr2 hr3
  rw [hdet, Fin.prod_univ_four] at hdetc
  set c := cf 0 with hc
  have hc0 : c ≠ 0 := by rintro h; rw [h] at hr0; simp at hr0
  have e1 : cf 1 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hr0
  have e3 : cf 3 = c ^ 9 := by
    rw [e1, inv_pow, ← pow_mul] at hr1
    rw [← mul_inv_cancel_left₀ (pow_ne_zero (3 * 3) hc0) (cf 3), hr1, mul_one]
  have e2 : cf 2 = (c ^ 27)⁻¹ := by
    rw [e3, ← pow_mul] at hr3
    exact eq_inv_of_mul_eq_one_right hr3
  have h20 : c ^ 20 = 1 := by
    rw [e1, e2, e3] at hdetc
    have : c ^ 20 * (c * (c ^ 3)⁻¹ * (c ^ 27)⁻¹ * c ^ 9) = 1 := by
      field_simp
    rw [← hdetc, mul_one] at this
    exact this
  refine ⟨c, by rw [show v = vec 0 from rfl]; exact hcf 0, h20, fun h4 => ?_⟩
  have hc1 : (c ^ 3)⁻¹ = c := by
    rw [inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv₀ hc0, ← pow_succ, h4]
  have hc3 : c ^ 9 = c := by
    rw [show 9 = 4 * 2 + 1 by norm_num, pow_succ, pow_mul, h4, one_pow, one_mul]
  have hc2 : (c ^ 27)⁻¹ = c := by
    rw [show 27 = 4 * 6 + 3 by norm_num, pow_add, pow_mul, h4, one_pow, one_mul, hc1]
  have hall : ∀ k, cf k = c := by
    intro k
    fin_cases k
    · rfl
    · exact e1.trans hc1
    · exact e2.trans hc2
    · exact e3.trans hc3
  have hlin : Matrix.toLin' A = Matrix.toLin' (Matrix.scalar (Fin 4) c) := by
    apply bs.ext
    intro i
    rw [hbs, Matrix.toLin'_apply, Matrix.toLin'_apply, hcf, hall, scalar_apply]
    funext j
    rw [mulVec_diagonal]
    simp [mul_comm]
  exact Matrix.toLin'.injective hlin

end Linear

section U43

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.A318P (projSU_of_statedClassicalModel_gen)
open CFSG.RankThree.PartTwo.Sec4.Item426 (pow_mul_four_eq_one)

theorem eq_of_mk_eq {K : Type*} [Field K] {A C : GL (Fin 4) K} {n : ℕ} (hcop : Nat.Coprime n 4)
    (hA : A ^ n = 1) (hC : C ^ n = 1)
    (hdet : Matrix.GeneralLinearGroup.det A = Matrix.GeneralLinearGroup.det C)
    (h : ProjGenLinGroup.mk A = ProjGenLinGroup.mk C) : A = C := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  set s := Matrix.GeneralLinearGroup.scalar (Fin 4) u with hs
  have hsc : Commute A s := by
    have : s ∈ Subgroup.center (GL (Fin 4) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    exact Subgroup.mem_center_iff.mp this A
  have hun : u ^ n = 1 := by
    have h1 : (A * s) ^ n = A ^ n * s ^ n := hsc.mul_pow n
    rw [hu, hA, hC, one_mul] at h1
    have h4 : Matrix.GeneralLinearGroup.scalar (Fin 4) (u ^ n) = 1 := by rw [map_pow, ← hs, ← h1]
    have h3 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) h4
    exact Units.ext (by simpa [Matrix.diagonal_pow] using h3)
  have hu4 : u ^ 4 = 1 := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det hu
    rw [map_mul, hs, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hdet] at h1
    exact mul_left_cancel (h1.trans (mul_one _).symm)
  have hu1 : u = 1 := by
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hun) (orderOf_dvd_of_pow_eq_one hu4)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  rw [← hu, hs, hu1, map_one, mul_one]

theorem unitary_mapMatrix {K L : Type*} [Field K] [Field L] [CharP K 3] [CharP L 3] [Algebra K L]
    {A : Matrix (Fin 4) (Fin 4) K} (hu : (A.map (frobenius K 3))ᵀ * A = 1) :
    (((algebraMap K L).mapMatrix A).map (frobenius L 3))ᵀ * (algebraMap K L).mapMatrix A = 1 := by
  have h := congrArg (algebraMap K L).mapMatrix hu
  rw [map_one, map_mul] at h
  convert h using 2
  ext i j
  simp [frobenius_def]

theorem eq_scalar_of_mapMatrix {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A : Matrix (Fin 4) (Fin 4) K} {d : L}
    (h : (algebraMap K L).mapMatrix A = Matrix.scalar (Fin 4) d) :
    A = Matrix.scalar (Fin 4) (A 0 0) := by
  have h00 : algebraMap K L (A 0 0) = d := by
    simpa [Matrix.scalar_apply] using congrFun (congrFun h 0) 0
  ext i j
  apply (algebraMap K L).injective
  have := congrFun (congrFun h i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply] at this ⊢
  rw [this]
  split_ifs <;> simp [h00]

theorem card_centralizer_le_five_projSU (x : projSU 4 3 1) (hx : orderOf x = 5) :
    Nat.card (Subgroup.centralizer ({x} : Set (projSU 4 3 1))) ≤ 5 := by
  classical
  set K := GaloisField 3 (2 * 1) with hKdef
  have hU : UnitaryFieldData 3 1 K :=
    ⟨Nat.prime_three, le_rfl, GaloisField.card 3 (2 * 1) (by norm_num)⟩
  have : CharP K 3 := hU.charP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlift : ∀ z : projSU 4 3 1, ∃ Z : GL (Fin 4) K, Z ∈ unitarySU 3 1 K 4 ∧
      ProjGenLinGroup.mk Z = (z : ProjGenLinGroup (Fin 4) K) := fun z =>
    Subgroup.mem_map.mp
      ((SetLike.ext_iff.mp (CFSG.RankThree.PartTwo.Sec4.projSU_eq_map_statedSU 4 3 1) _).mp z.2)
  choose Lf hLfmem hLf using hlift
  have hbar : (⇑hU.bar : K → K) = ⇑(frobenius K 3) :=
    funext fun c => by rw [hU.bar_apply, frobenius_def, pow_one]
  have hdet1 : ∀ Z ∈ unitarySU 3 1 K 4, Matrix.GeneralLinearGroup.det Z = 1 := fun Z hZ =>
    Units.ext (by simpa using ((mem_unitarySU_iff hU).mp hZ).1)
  have hunit : ∀ Z ∈ unitarySU 3 1 K 4,
      ((Z : Matrix (Fin 4) (Fin 4) K).map (frobenius K 3))ᵀ * Z = 1 := fun Z hZ => by
    have h := ((mem_unitarySU_iff hU).mp hZ).2
    rwa [hbar] at h
  set X := Lf x with hXdef
  have hx5 : (x : ProjGenLinGroup (Fin 4) K) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    rw [← Subgroup.coe_pow, h, OneMemClass.coe_one]
  have hx1 : (x : ProjGenLinGroup (Fin 4) K) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    norm_num at hx
  set B := X ^ 16 with hB
  have hBmem : B ∈ unitarySU 3 1 K 4 := pow_mem (hLfmem x) 16
  have hB5 : B ^ 5 = 1 := by
    rw [hB, ← pow_mul, show 16 * 5 = 5 * 4 * 4 by norm_num, pow_mul,
      pow_mul_four_eq_one ((mem_unitarySU_iff hU).mp (hLfmem x)).1 (by rw [hLf, hx5]), one_pow]
  have hBx : ProjGenLinGroup.mk B = (x : ProjGenLinGroup (Fin 4) K) := by
    rw [hB, map_pow, hLf, show 16 = 5 * 3 + 1 by norm_num, pow_succ, pow_mul, hx5, one_pow,
      one_mul]
  have hB1 : B ≠ 1 := fun h => hx1 (by rw [← hBx, h, map_one])
  have hcomm : ∀ y : Subgroup.centralizer ({x} : Set (projSU 4 3 1)),
      Lf y * B = B * Lf y := by
    intro y
    have hyx : (y : projSU 4 3 1) * x = x * y :=
      (Subgroup.mem_centralizer_iff.mp y.2 x (Set.mem_singleton x)).symm
    have h := eq_of_mk_eq (n := 5) (A := Lf y * B * (Lf y)⁻¹) (C := B) (by norm_num)
      (by rw [show Lf y * B * (Lf y)⁻¹ = MulAut.conj (Lf y) B by simp, ← map_pow, hB5, map_one])
      hB5 (by simp [map_mul, map_inv, mul_comm])
      (by
        rw [map_mul, map_mul, map_inv, hLf, hBx, mul_inv_eq_iff_eq_mul]
        exact_mod_cast hyx)
    rwa [mul_inv_eq_iff_eq_mul] at h
  set L := AlgebraicClosure K
  set ι := (algebraMap K L).mapMatrix (m := Fin 4) with hι
  have hιunit : ∀ Z ∈ unitarySU 3 1 K 4,
      ((ι (Z : Matrix (Fin 4) (Fin 4) K)).map (frobenius L 3))ᵀ * ι Z = 1 := fun Z hZ =>
    unitary_mapMatrix (hunit Z hZ)
  have hιdet : ∀ Z ∈ unitarySU 3 1 K 4, (ι (Z : Matrix (Fin 4) (Fin 4) K)).det = 1 := by
    intro Z hZ
    rw [hι, ← RingHom.map_det, ((mem_unitarySU_iff hU).mp hZ).1, map_one]
  have hιinj : Function.Injective ι := Matrix.map_injective (algebraMap K L).injective
  obtain ⟨v, hv, hcore⟩ := core_five (B := ι B) (hιunit B hBmem)
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hB5, Units.val_one, map_one])
    (fun h => hB1 (Units.ext (hιinj (by rw [h, Units.val_one, map_one]))))
  have hιcomm : ∀ Z : GL (Fin 4) K, Z * B = B * Z →
      ι (Z : Matrix (Fin 4) (Fin 4) K) * ι B = ι B * ι Z := fun Z h => by
    rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, h]
  have hc : ∀ y : Subgroup.centralizer ({x} : Set (projSU 4 3 1)),
      ∃ c : L, ι (Lf y : Matrix (Fin 4) (Fin 4) K) *ᵥ v = c • v ∧ c ^ 20 = 1 := fun y => by
    obtain ⟨c, h1, h2, -⟩ := hcore _ (hιcomm _ (hcomm y)) (hιunit _ (hLfmem y))
      (hιdet _ (hLfmem y))
    exact ⟨c, h1, h2⟩
  choose cf hcfv hcf20 using hc
  set R := (Polynomial.nthRoots 5 (1 : L)).toFinset with hR
  have hmemR : ∀ y, cf y ^ 4 ∈ R := fun y => by
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num), ← pow_mul]
    exact hcf20 y
  have hinj : Function.Injective (fun y => (⟨cf y ^ 4, hmemR y⟩ : R)) := by
    intro y y' hyy
    have h4 : cf y ^ 4 = cf y' ^ 4 := congrArg Subtype.val hyy
    set Z := Lf y' * (Lf y)⁻¹ with hZ
    have hZmem : Z ∈ unitarySU 3 1 K 4 := mul_mem (hLfmem y') (inv_mem (hLfmem y))
    have hZcomm : Z * B = B * Z := by
      have hinvc : (Lf y)⁻¹ * B = B * (Lf y)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm y, mul_inv_cancel_right]
      rw [hZ, mul_assoc, hinvc, ← mul_assoc, hcomm y', mul_assoc]
    have hcy0 : cf y ≠ 0 := by
      intro h0
      have := hcf20 y
      rw [h0] at this
      norm_num at this
    have hinvv : ι ((Lf y)⁻¹ : GL (Fin 4) K) *ᵥ v = (cf y)⁻¹ • v := by
      have h1 : ι ((Lf y)⁻¹ : GL (Fin 4) K) *ᵥ (ι (Lf y : Matrix (Fin 4) (Fin 4) K) *ᵥ v) = v := by
        rw [mulVec_mulVec, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
          one_mulVec]
      rw [hcfv, mulVec_smul] at h1
      calc ι ((Lf y)⁻¹ : GL (Fin 4) K) *ᵥ v
          = (cf y)⁻¹ • (cf y • (ι ((Lf y)⁻¹ : GL (Fin 4) K) *ᵥ v)) := by
            rw [smul_smul, inv_mul_cancel₀ hcy0, one_smul]
        _ = (cf y)⁻¹ • v := by rw [h1]
    have hZv : ι (Z : Matrix (Fin 4) (Fin 4) K) *ᵥ v = (cf y' * (cf y)⁻¹) • v := by
      rw [hZ, Units.val_mul, map_mul, ← mulVec_mulVec, hinvv, mulVec_smul, hcfv, smul_smul,
        mul_comm (cf y)⁻¹]
    obtain ⟨d, hd1, -, hd3⟩ := hcore _ (hιcomm _ hZcomm) (hιunit _ hZmem) (hιdet _ hZmem)
    have hdd : d = cf y' * (cf y)⁻¹ := by
      rw [hZv] at hd1
      by_contra hne
      have h' : (cf y' * (cf y)⁻¹ - d) • v = 0 := by rw [sub_smul, hd1, sub_self]
      exact hv ((smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Ne.symm hne)))
    have hd4 : d ^ 4 = 1 := by
      rw [hdd, mul_pow, inv_pow, ← h4, mul_inv_cancel₀ (pow_ne_zero 4 hcy0)]
    have hZs := eq_scalar_of_mapMatrix (hd3 hd4)
    have hZ00 : (Z : Matrix (Fin 4) (Fin 4) K) 0 0 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hZs
      have := (Matrix.GeneralLinearGroup.det Z).ne_zero
      rw [Matrix.GeneralLinearGroup.val_det_apply, hZs, Matrix.det_zero] at this
      exact this rfl
    have hmkZ : ProjGenLinGroup.mk Z = 1 := by
      rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨Units.mk0 _ hZ00, Units.ext ?_⟩
      conv_rhs => rw [hZs]
      rfl
    have hyy' : ((y' : projSU 4 3 1) : ProjGenLinGroup (Fin 4) K) = (y : projSU 4 3 1) := by
      rw [← hLf, ← hLf, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← hZ, hmkZ]
    exact (Subtype.ext (Subtype.ext hyy')).symm
  calc Nat.card (Subgroup.centralizer ({x} : Set (projSU 4 3 1)))
      ≤ Nat.card R := Nat.card_le_card_of_injective _ hinj
    _ = R.card := Nat.card_eq_finsetCard R
    _ ≤ Multiset.card (Polynomial.nthRoots 5 (1 : L)) := Multiset.toFinset_card_le _
    _ ≤ 5 := Polynomial.card_nthRoots 5 1

theorem u43Cent5 : U43Cent5Statement := by
  unfold U43Cent5Statement
  intro S _ _ hS x hx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := projSU_of_statedClassicalModel_gen (hS.statedClassicalModel (by decide))
  have hle : Nat.card (Subgroup.centralizer ({x} : Set S)) ≤ 5 := by
    refine le_trans ?_
      (card_centralizer_le_five_projSU (e x) (by rw [MulEquiv.orderOf_eq]; exact hx))
    refine Nat.card_le_card_of_injective
      (fun y => ⟨e y, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩) ?_
    · rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp y.2]
    · intro a b h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
  have hdvd : 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set S)) := by
    have hxmem : x ∈ Subgroup.centralizer ({x} : Set S) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have := Subgroup.orderOf_dvd_natCard _ hxmem
    rwa [hx] at this
  have hpos : 0 < Nat.card (Subgroup.centralizer ({x} : Set S)) := Nat.card_pos
  have : Nat.card (Subgroup.centralizer ({x} : Set S)) = 5 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk] at hle hpos ⊢
    have : k = 1 := by omega
    rw [this]
  rw [this]

end U43

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

