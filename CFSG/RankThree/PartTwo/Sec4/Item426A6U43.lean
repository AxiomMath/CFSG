module

import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426

open Matrix

section Linear

variable {L : Type*} [Field L] [CharP L 3]

theorem exists_eig_sq {B : Matrix (Fin 4) (Fin 4) L}
    (hu : (B.map (frobenius L 3))ᵀ * B = 1) (h5 : B ^ 5 = 1) {μ : L} {v : Fin 4 → L}
    (hv : v ≠ 0) (hBv : B *ᵥ v = μ • v) : μ ^ 5 = 1 ∧ ∃ w, w ≠ 0 ∧ B *ᵥ w = μ ^ 2 • w := by
  have hpow : ∀ k : ℕ, B ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBv, mulVec_smul, ih, smul_smul, pow_succ']
  have hμ5 : μ ^ 5 = 1 := by
    have h := hpow 5
    rw [h5, one_mulVec] at h
    by_contra hne
    apply hv
    have h' : (μ ^ 5 - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  refine ⟨hμ5, ?_⟩
  set w : Fin 4 → L := fun i => (v i) ^ 3 with hw
  have hw0 : w ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simp only [hw, Pi.zero_apply] at this
    exact (pow_eq_zero_iff (by norm_num)).mp this
  have h1 : B.map (frobenius L 3) *ᵥ w = μ ^ 3 • w := by
    funext i
    have := RingHom.map_mulVec (frobenius L 3) B v i
    rw [hBv] at this
    simpa [frobenius_def, mul_pow, hw, Function.comp_def] using this.symm
  have h2 : w ᵥ* B = μ ^ 2 • w := by
    have h3 : w ᵥ* ((B.map (frobenius L 3))ᵀ * B) = w := by rw [hu, vecMul_one]
    rw [← vecMul_vecMul, vecMul_transpose, h1, smul_vecMul] at h3
    have hμ3 : μ ^ 2 * μ ^ 3 = 1 := by rw [← pow_add]; exact hμ5
    calc w ᵥ* B = (μ ^ 2 * μ ^ 3) • (w ᵥ* B) := by rw [hμ3, one_smul]
      _ = μ ^ 2 • w := by rw [mul_smul, h3]
  have hdet : (B - Matrix.scalar (Fin 4) (μ ^ 2)).det = 0 := by
    rw [← exists_vecMul_eq_zero_iff]
    refine ⟨w, hw0, ?_⟩
    rw [vecMul_sub, h2, scalar_apply]
    funext i
    simp [mul_comm]
  obtain ⟨w', hw', h⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨w', hw', ?_⟩
  rw [sub_mulVec, sub_eq_zero, scalar_apply] at h
  rw [h]
  funext i
  simp [mulVec_diagonal]

theorem eq_one_of_commute_of_unitary [IsAlgClosed L] {A B : Matrix (Fin 4) (Fin 4) L}
    (hu : (B.map (frobenius L 3))ᵀ * B = 1) (h5 : B ^ 5 = 1) (hB1 : B ≠ 1)
    (hAB : A * B = B * A) (hA3 : A ^ 3 = 1) : A = 1 := by
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
  obtain ⟨hμ5, v₂, hv₂, hBv₂⟩ := exists_eig_sq hu h5 hv hBv
  obtain ⟨-, v₄, hv₄, hBv₄⟩ := exists_eig_sq hu h5 hv₂ hBv₂
  obtain ⟨-, v₃, hv₃, hBv₃⟩ := exists_eig_sq hu h5 hv₄ hBv₄
  have hμo : orderOf μ = 5 := orderOf_eq_prime hμ5 hμ1
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
  have hAvec : ∀ k, A *ᵥ vec k = vec k := by
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
    have hx' : x = c k • vec k := by
      rw [hxsum, Finset.sum_eq_single k (fun j _ hjk => by rw [hcoef j hjk, zero_smul])
        (by simp)]
    have hA : ∀ n : ℕ, A ^ n *ᵥ vec k = c k ^ n • vec k := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, ← hx, hx', smul_smul,
          pow_succ]
    have hc3 : c k ^ 3 = 1 := by
      have h := hA 3
      rw [hA3, one_mulVec] at h
      by_contra hne
      have h' : (c k ^ 3 - 1) • vec k = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
      exact hvec0 k ((smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne))
    have hc1 : c k = 1 := by
      have h := sub_pow_char (p := 3) (c k) 1
      rw [hc3, one_pow, sub_self] at h
      exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h)
    rw [hx', hc1, one_smul]
  have hlin : Matrix.toLin' A = Matrix.toLin' (1 : Matrix (Fin 4) (Fin 4) L) := by
    apply bs.ext
    intro i
    rw [hbs, Matrix.toLin'_apply, Matrix.toLin'_apply, hAvec, one_mulVec]
  exact Matrix.toLin'.injective hlin

end Linear

theorem eq_one_of_commute_of_unitary' {F : Type*} [Field F] [CharP F 3]
    {A B : Matrix (Fin 4) (Fin 4) F}
    (hu : (B.map (frobenius F 3))ᵀ * B = 1) (h5 : B ^ 5 = 1) (hB1 : B ≠ 1)
    (hAB : A * B = B * A) (hA3 : A ^ 3 = 1) : A = 1 := by
  set ι := (algebraMap F (AlgebraicClosure F)).mapMatrix (m := Fin 4) with hι
  have hinj : Function.Injective ι := Matrix.map_injective (algebraMap F _).injective
  apply hinj
  rw [map_one]
  apply eq_one_of_commute_of_unitary (B := ι B)
  · have h := congrArg ι hu
    rw [map_one, map_mul] at h
    convert h using 2
    ext i j
    simp [hι, frobenius_def]
  · rw [← map_pow, h5, map_one]
  · intro h
    apply hB1
    apply hinj
    rw [h, map_one]
  · rw [← map_mul, ← map_mul, hAB]
  · rw [← map_pow, hA3, map_one]

section U43

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem pow_mul_four_eq_one {K : Type*} [Field K] {X : GL (Fin 4) K}
    (hdet : (X : Matrix (Fin 4) (Fin 4) K).det = 1) {n : ℕ}
    (hn : ProjGenLinGroup.mk X ^ n = 1) : X ^ (n * 4) = 1 := by
  rw [← map_pow, ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hn
  obtain ⟨u, hu⟩ := hn
  have hX : Matrix.GeneralLinearGroup.det X = 1 := Units.ext (by simpa using hdet)
  have hu4 : u ^ 4 = 1 := by
    have h1 := Matrix.GeneralLinearGroup.det_scalar (n := Fin 4) u
    rw [hu, map_pow, hX, one_pow, Fintype.card_fin] at h1
    exact h1.symm
  rw [pow_mul, ← hu, ← map_pow, hu4, map_one]

theorem u43ThreeCentralizer : ∀ x : projSU 4 3 1, orderOf x = 3 → ¬ 5 ∣ Nat.card (Subgroup.centralizer {x}) := by
  intro x hx h5
  set K := GaloisField 3 (2 * 1) with hKdef
  have hU : UnitaryFieldData 3 1 K :=
    ⟨Nat.prime_three, le_rfl, GaloisField.card 3 (2 * 1) (by norm_num)⟩
  have : CharP K 3 := hU.charP
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite K := hU.finite
  have : Finite (ProjGenLinGroup (Fin 4) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hzx : (z : projSU 4 3 1) * x = x * z :=
    (Subgroup.mem_centralizer_iff.mp z.2 x (Set.mem_singleton x)).symm
  have hz5 : orderOf (z : projSU 4 3 1) = 5 := by rwa [Subgroup.orderOf_coe]
  have hlift : ∀ y : projSU 4 3 1, ∃ Y : GL (Fin 4) K, Y ∈ unitarySU 3 1 K 4 ∧
      ProjGenLinGroup.mk Y = (y : ProjGenLinGroup (Fin 4) K) := by
    intro y
    exact Subgroup.mem_map.mp
      ((SetLike.ext_iff.mp (projSU_eq_map_statedSU 4 3 1) _).mp y.2)
  obtain ⟨X, hX, hXx⟩ := hlift x
  obtain ⟨Z, hZ, hZz⟩ := hlift (z : projSU 4 3 1)
  have hXdet := ((mem_unitarySU_iff hU).mp hX).1
  have hZdet := ((mem_unitarySU_iff hU).mp hZ).1
  have hx3 : (x : ProjGenLinGroup (Fin 4) K) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    rw [← Subgroup.coe_pow, h, OneMemClass.coe_one]
  have hz5' : ((z : projSU 4 3 1) : ProjGenLinGroup (Fin 4) K) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one (z : projSU 4 3 1)
    rw [hz5] at h
    rw [← Subgroup.coe_pow, h, OneMemClass.coe_one]
  have hx1 : (x : ProjGenLinGroup (Fin 4) K) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    norm_num at hx
  have hz1 : ((z : projSU 4 3 1) : ProjGenLinGroup (Fin 4) K) ≠ 1 := by
    intro h
    have : (z : projSU 4 3 1) = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz5
    norm_num at hz5
  set X' := X ^ 4 with hX'
  set Z' := Z ^ 16 with hZ'
  have hX'3 : X' ^ 3 = 1 := by
    rw [hX', ← pow_mul]
    exact pow_mul_four_eq_one hXdet (by rw [hXx, hx3])
  have hZ'5 : Z' ^ 5 = 1 := by
    rw [hZ', ← pow_mul, show 16 * 5 = 5 * 4 * 4 by norm_num, pow_mul,
      pow_mul_four_eq_one hZdet (by rw [hZz, hz5']), one_pow]
  have hX'x : ProjGenLinGroup.mk X' = (x : ProjGenLinGroup (Fin 4) K) := by
    rw [hX', map_pow, hXx, pow_succ, hx3, one_mul]
  have hZ'z : ProjGenLinGroup.mk Z' = ((z : projSU 4 3 1) : ProjGenLinGroup (Fin 4) K) := by
    rw [hZ', map_pow, hZz, show 16 = 5 * 3 + 1 by norm_num, pow_succ, pow_mul, hz5', one_pow,
      one_mul]
  have hX'1 : X' ≠ 1 := fun h => hx1 (by rw [← hX'x, h, map_one])
  have hZ'1 : Z' ≠ 1 := fun h => hz1 (by rw [← hZ'z, h, map_one])
  have hZ'mem : Z' ∈ unitarySU 3 1 K 4 := pow_mem hZ 16
  have hZ'det : Matrix.GeneralLinearGroup.det Z' = 1 :=
    Units.ext (by simpa using ((mem_unitarySU_iff hU).mp hZ'mem).1)
  have hcomm : X' * Z' = Z' * X' := by
    have hmk : ProjGenLinGroup.mk (Z' * X') = ProjGenLinGroup.mk (X' * Z') := by
      rw [map_mul, map_mul, hX'x, hZ'z]
      exact_mod_cast hzx
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hmk
    set s := Matrix.GeneralLinearGroup.scalar (Fin 4) u with hs
    have hsc : ∀ g : GL (Fin 4) K, g * s = s * g := fun g => by
      have : s ∈ Subgroup.center (GL (Fin 4) K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨u, rfl⟩
      exact (Subgroup.mem_center_iff.mp this g)
    have hC : X'⁻¹ * Z' * X' * s = Z' := by
      calc X'⁻¹ * Z' * X' * s = X'⁻¹ * (Z' * X' * s) := by group
        _ = Z' := by rw [hu]; group
    have hu5 : u ^ 5 = 1 := by
      have h1 : (X'⁻¹ * Z' * X' * s) ^ 5 = (X'⁻¹ * Z' * X') ^ 5 * s ^ 5 :=
        Commute.mul_pow (hsc _) 5
      have h2 : (X'⁻¹ * Z' * X') ^ 5 = 1 := by
        rw [show X'⁻¹ * Z' * X' = MulAut.conj X'⁻¹ Z' by simp, ← map_pow,
          hZ'5, map_one]
      rw [hC, hZ'5, h2, one_mul] at h1
      have h4 : Matrix.GeneralLinearGroup.scalar (Fin 4) (u ^ 5) = 1 := by
        rw [map_pow, ← hs, ← h1]
      have h3 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) h4
      exact Units.ext (by simpa [Matrix.diagonal_pow] using h3)
    have hu4 : u ^ 4 = 1 := by
      have h1 := congrArg Matrix.GeneralLinearGroup.det hC
      rw [map_mul, map_mul, map_mul, hZ'det, hs, Matrix.GeneralLinearGroup.det_scalar,
        Fintype.card_fin, map_inv] at h1
      have h2 : Matrix.GeneralLinearGroup.det X'⁻¹ * Matrix.GeneralLinearGroup.det X' = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      calc u ^ 4 = (Matrix.GeneralLinearGroup.det X')⁻¹ * 1 *
            Matrix.GeneralLinearGroup.det X' * u ^ 4 := by group
        _ = 1 := h1
    have hu1 : u = 1 := by
      calc u = u ^ 5 * (u ^ 4)⁻¹ := by group
        _ = 1 := by rw [hu5, hu4, inv_one, one_mul]
    rw [← hu, hs, hu1, map_one]
    exact mul_one _
  have hbar : (⇑hU.bar : K → K) = ⇑(frobenius K 3) :=
    funext fun c => by rw [hU.bar_apply, frobenius_def, pow_one]
  have hZ'u := ((mem_unitarySU_iff hU).mp hZ'mem).2
  rw [hbar] at hZ'u
  have h1 := eq_one_of_commute_of_unitary' (A := (X' : Matrix (Fin 4) (Fin 4) K))
    (B := (Z' : Matrix (Fin 4) (Fin 4) K)) hZ'u
    (by rw [← Units.val_pow_eq_pow_val, hZ'5, Units.val_one])
    (fun h => hZ'1 (Units.ext h)) (by rw [← Units.val_mul, ← Units.val_mul, hcomm])
    (by rw [← Units.val_pow_eq_pow_val, hX'3, Units.val_one])
  exact hX'1 (Units.ext h1)

end U43

end CFSG.RankThree.PartTwo.Sec4.Item426
