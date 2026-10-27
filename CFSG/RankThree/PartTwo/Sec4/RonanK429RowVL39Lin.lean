module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.PGLModelStated

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV

open Matrix

private theorem exists_eig_nine {L : Type*} [Field L] [CharP L 3] {B : Matrix (Fin 3) (Fin 3) L}
    (hB9 : B.map (fun x => x ^ 9) = B) {μ : L} {v : Fin 3 → L} (hv : v ≠ 0)
    (hBv : B *ᵥ v = μ • v) : ∃ w : Fin 3 → L, w ≠ 0 ∧ B *ᵥ w = μ ^ 9 • w := by
  obtain ⟨φ, hφx⟩ : ∃ φ : L →+* L, ∀ x : L, φ x = x ^ 9 :=
    ⟨iterateFrobenius L 3 2, fun x => rfl⟩
  have hBφ : B.map φ = B := by
    have h9 : B.map φ = B.map (fun x => x ^ 9) := by
      ext i j
      simp [hφx]
    rw [h9, hB9]
  refine ⟨fun i => φ (v i), ?_, ?_⟩
  · intro h0
    apply hv
    funext i
    have h := congrFun h0 i
    simp only [Pi.zero_apply] at h
    exact φ.injective (h.trans (map_zero φ).symm)
  · funext i
    have h : φ ((B *ᵥ v) i) = (B.map φ *ᵥ (φ ∘ v)) i := RingHom.map_mulVec φ B v i
    rw [hBv, hBφ, Pi.smul_apply, smul_eq_mul, map_mul, hφx μ] at h
    rw [Pi.smul_apply, smul_eq_mul]
    exact h.symm

private theorem unit_eq_one_of_pow_three_eq_one {K : Type*} [Field K] (hK : Nat.card K = 9)
    {u : Kˣ} (hu : u ^ 3 = 1) : u = 1 := by
  have h3 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu
  have h8 : orderOf u ∣ 8 := by
    have h := orderOf_dvd_natCard u
    rw [Nat.card_units, hK] at h
    simpa using h
  have h1 : orderOf u ∣ 1 := by
    have h := Nat.dvd_gcd h3 h8
    rw [show Nat.gcd 3 8 = 1 by norm_num] at h
    exact h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

private theorem pow_eq_one_of_mk_pow_eq_one {K : Type*} [Field K] (hK : Nat.card K = 9)
    {Y : GL (Fin 3) K} (hdet : (Y : Matrix (Fin 3) (Fin 3) K).det = 1) {n : ℕ}
    (hn : ProjGenLinGroup.mk Y ^ n = 1) : Y ^ n = 1 := by
  rw [← map_pow, ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hn
  obtain ⟨u, hu⟩ := hn
  have hY : Matrix.GeneralLinearGroup.det Y = 1 := Units.ext (by simpa using hdet)
  have hu3 : u ^ 3 = 1 := by
    have h1 := Matrix.GeneralLinearGroup.det_scalar (n := Fin 3) u
    rw [hu, map_pow, hY, one_pow, Fintype.card_fin] at h1
    exact h1.symm
  rw [unit_eq_one_of_pow_three_eq_one hK hu3, map_one] at hu
  exact hu.symm

theorem eq_one_of_commute_of_pow_seven {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L]
    {A B : Matrix (Fin 3) (Fin 3) L} (hB9 : B.map (fun x => x ^ 9) = B) (h7 : B ^ 7 = 1)
    (hB1 : B ≠ 1) (hAB : A * B = B * A) (hA3 : A ^ 3 = 1) : A = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨μ, v, hv, hBv, hμ1⟩ : ∃ μ : L, ∃ v : Fin 3 → L, v ≠ 0 ∧ B *ᵥ v = μ • v ∧ μ ≠ 1 := by
    set Q := B ^ 6 + B ^ 5 + B ^ 4 + B ^ 3 + B ^ 2 + B + 1 with hQ
    have hQB : Q * (B - 1) = B ^ 7 - 1 := by rw [hQ]; noncomm_ring
    have hcomm : B * Q = Q * B := by rw [hQ]; noncomm_ring
    obtain ⟨u, hu'⟩ : ∃ u, (B - 1) *ᵥ u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hB1
      rw [← sub_eq_zero]
      ext i j
      have h := congrFun (hcon (Pi.single j 1)) i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
    set W := LinearMap.ker (Matrix.toLin' Q) with hW
    have hinv : ∀ y ∈ W, Matrix.toLin' B y ∈ W := by
      intro y hy
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy ⊢
      rw [Matrix.toLin'_apply, mulVec_mulVec, ← hcomm, ← mulVec_mulVec, hy, mulVec_zero]
    have hmem : (B - 1) *ᵥ u ∈ W := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, mulVec_mulVec, hQB, h7, sub_self, zero_mulVec]
    have hne : W ≠ ⊥ := fun h => hu' (by rw [h] at hmem; exact (Submodule.mem_bot L).mp hmem)
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((Matrix.toLin' B).restrict hinv)
    obtain ⟨y, hy⟩ := hμ.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
    have hBy : B *ᵥ (y : Fin 3 → L) = μ • (y : Fin 3 → L) := by
      have := congrArg Subtype.val hy.1
      simpa [LinearMap.restrict_apply, Matrix.toLin'_apply] using this
    have hy0 : (y : Fin 3 → L) ≠ 0 := fun h => hy.2 (Subtype.ext h)
    refine ⟨μ, y, hy0, hBy, ?_⟩
    rintro rfl
    have hpow : ∀ k : ℕ, B ^ k *ᵥ (y : Fin 3 → L) = (y : Fin 3 → L) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBy, one_smul, ih]
    have hQy : Q *ᵥ (y : Fin 3 → L) = (7 : L) • (y : Fin 3 → L) := by
      have h1 := hpow 1
      rw [pow_one] at h1
      rw [hQ, add_mulVec, add_mulVec, add_mulVec, add_mulVec, add_mulVec, add_mulVec, hpow, hpow,
        hpow, hpow, hpow, h1, one_mulVec, show (7 : L) = 1 + 1 + 1 + 1 + 1 + 1 + 1 by norm_num,
        add_smul, add_smul, add_smul, add_smul, add_smul, add_smul, one_smul]
    have hy' := y.2
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hQy] at hy'
    have h7ne : (7 : L) ≠ 0 := by
      intro h
      have h' : ((7 : ℕ) : L) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff L 3] at h'
      norm_num at h'
    exact hy0 ((smul_eq_zero.mp hy').resolve_left h7ne)
  have hpowv : ∀ k : ℕ, B ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBv, mulVec_smul, ih, smul_smul, pow_succ']
  have hμ7 : μ ^ 7 = 1 := by
    have h := hpowv 7
    rw [h7, one_mulVec] at h
    by_contra hne
    apply hv
    have h' : (μ ^ 7 - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  have hμo : orderOf μ = 7 := orderOf_eq_prime hμ7 hμ1
  have hprim : IsPrimitiveRoot μ 7 := hμo ▸ IsPrimitiveRoot.orderOf μ
  obtain ⟨v₂, hv₂, hBv₂⟩ := exists_eig_nine hB9 hv hBv
  obtain ⟨v₄, hv₄, hBv₄⟩ := exists_eig_nine hB9 hv₂ hBv₂
  have h9 : μ ^ 9 = μ ^ 2 := by rw [show 9 = 7 + 2 by norm_num, pow_add, hμ7, one_mul]
  have h81 : (μ ^ 9) ^ 9 = μ ^ 4 := by
    rw [← pow_mul, show 9 * 9 = 7 * 11 + 4 by norm_num, pow_add, pow_mul, hμ7, one_pow, one_mul]
  rw [h9] at hBv₂
  rw [h81] at hBv₄
  set lam : Fin 3 → L := fun i => μ ^ (2 ^ (i : ℕ)) with hlam_def
  set vec : Fin 3 → (Fin 3 → L) := ![v, v₂, v₄] with hvec_def
  have hpow7 : ∀ i : Fin 3, 2 ^ (i : ℕ) < 7 := by decide
  have hinj2 : ∀ i j : Fin 3, 2 ^ (i : ℕ) = 2 ^ (j : ℕ) → i = j := by decide
  have hlam : Function.Injective lam := fun i j h =>
    hinj2 i j (hprim.pow_inj (hpow7 i) (hpow7 j) h)
  have hvec : ∀ i, B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · simpa [hvec_def, hlam_def] using hBv
    · simpa [hvec_def, hlam_def] using hBv₂
    · simpa [hvec_def, hlam_def] using hBv₄
  have hvec0 : ∀ i, vec i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [hvec_def] using hv
    · simpa [hvec_def] using hv₂
    · simpa [hvec_def] using hv₄
  have hli : LinearIndependent L vec :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B) lam hlam vec fun i => by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact ⟨hvec i, hvec0 i⟩
  have hcard : Fintype.card (Fin 3) = Module.finrank L (Fin 3 → L) := by simp
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
  have hlin : Matrix.toLin' A = Matrix.toLin' (1 : Matrix (Fin 3) (Fin 3) L) := by
    apply bs.ext
    intro i
    rw [hbs, Matrix.toLin'_apply, Matrix.toLin'_apply, hAvec, one_mulVec]
  exact Matrix.toLin'.injective hlin

theorem eq_one_of_commute_of_pow_seven' {F : Type*} [Field F] [Finite F] [CharP F 3]
    (hF : Nat.card F = 9) {A B : Matrix (Fin 3) (Fin 3) F} (h7 : B ^ 7 = 1) (hB1 : B ≠ 1)
    (hAB : A * B = B * A) (hA3 : A ^ 3 = 1) : A = 1 := by
  have hpow9 : ∀ x : F, x ^ 9 = x := by
    intro x
    letI := Fintype.ofFinite F
    have h := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hF] at h
    exact h
  set ι := (algebraMap F (AlgebraicClosure F)).mapMatrix (m := Fin 3) with hι
  have hinj : Function.Injective ι := Matrix.map_injective (algebraMap F _).injective
  apply hinj
  rw [map_one]
  apply eq_one_of_commute_of_pow_seven (B := ι B)
  · ext i j
    simp only [hι, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [← map_pow, hpow9]
  · rw [← map_pow, h7, map_one]
  · intro h
    apply hB1
    apply hinj
    rw [h, map_one]
  · rw [← map_mul, ← map_mul, hAB]
  · rw [← map_pow, hA3, map_one]

private theorem card_galoisField_three_two : Nat.card (GaloisField 3 2) = 9 := by
  rw [GaloisField.card 3 2 (by norm_num)] <;> norm_num

private theorem not_seven_dvd_card_centralizer_of_card_nine {K : Type} [Field K] [Finite K]
    [CharP K 3] (hK : Nat.card K = 9) (x : CFSG.Assembly.RankThreeEven.projSL 3 K)
    (hx : orderOf x = 3) :
    ¬ 7 ∣ Nat.card (Subgroup.centralizer
      ({x} : Set (CFSG.Assembly.RankThreeEven.projSL 3 K))) := by
  intro h7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hzx : (z : CFSG.Assembly.RankThreeEven.projSL 3 K) * x = x * z :=
    (Subgroup.mem_centralizer_iff.mp z.2 x (Set.mem_singleton x)).symm
  have hz7 : orderOf (z : CFSG.Assembly.RankThreeEven.projSL 3 K) = 7 := by
    rwa [Subgroup.orderOf_coe]
  have hP : CFSG.Assembly.RankThreeEven.projSL 3 K =
      (CFSG.Open.StatedSL 3 K).map (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K) :=
    (CFSG.PGLModel.projImage_statedSL 3 K).symm
  have hlift : ∀ y : CFSG.Assembly.RankThreeEven.projSL 3 K, ∃ Y : GL (Fin 3) K,
      Y ∈ CFSG.Open.StatedSL 3 K ∧ ProjGenLinGroup.mk Y = (y : ProjGenLinGroup (Fin 3) K) := by
    intro y
    have hy : (y : ProjGenLinGroup (Fin 3) K) ∈
        (CFSG.Open.StatedSL 3 K).map (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K) := by
      rw [← hP]
      exact y.2
    exact Subgroup.mem_map.mp hy
  obtain ⟨X, hX, hXx⟩ := hlift x
  obtain ⟨Z, hZ, hZz⟩ := hlift (z : CFSG.Assembly.RankThreeEven.projSL 3 K)
  have hXdet : (X : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL hX
  have hZdet : (Z : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL hZ
  have hx3 : (x : ProjGenLinGroup (Fin 3) K) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    rw [← Subgroup.coe_pow, h, OneMemClass.coe_one]
  have hz7' : ((z : CFSG.Assembly.RankThreeEven.projSL 3 K) : ProjGenLinGroup (Fin 3) K) ^ 7 = 1 := by
    have h := pow_orderOf_eq_one (z : CFSG.Assembly.RankThreeEven.projSL 3 K)
    rw [hz7] at h
    rw [← Subgroup.coe_pow, h, OneMemClass.coe_one]
  have hx1 : (x : ProjGenLinGroup (Fin 3) K) ≠ 1 := by
    intro h
    have h' : x = 1 := Subtype.ext h
    rw [h', orderOf_one] at hx
    norm_num at hx
  have hz1 : ((z : CFSG.Assembly.RankThreeEven.projSL 3 K) : ProjGenLinGroup (Fin 3) K) ≠ 1 := by
    intro h
    have h' : (z : CFSG.Assembly.RankThreeEven.projSL 3 K) = 1 := Subtype.ext h
    rw [h', orderOf_one] at hz7
    norm_num at hz7
  have hX3 : X ^ 3 = 1 := pow_eq_one_of_mk_pow_eq_one (n := 3) hK hXdet (by rw [hXx]; exact hx3)
  have hZ7 : Z ^ 7 = 1 :=
    pow_eq_one_of_mk_pow_eq_one (n := 7) hK hZdet (by rw [hZz]; exact hz7')
  have hX1 : X ≠ 1 := fun h => hx1 (by rw [← hXx, h, map_one])
  have hZ1 : Z ≠ 1 := fun h => hz1 (by rw [← hZz, h, map_one])
  have hcomm : Z * X = X * Z := by
    have hmk : ProjGenLinGroup.mk (Z * X) = ProjGenLinGroup.mk (X * Z) := by
      rw [map_mul, map_mul, hXx, hZz]
      exact_mod_cast hzx
    have hdiv : ProjGenLinGroup.mk (Z * X * (X * Z)⁻¹) = 1 := by
      rw [map_mul, map_inv, hmk, mul_inv_cancel]
    rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hdiv
    obtain ⟨u, hu⟩ := hdiv
    have hXdetU : Matrix.GeneralLinearGroup.det X = 1 := Units.ext (by simpa using hXdet)
    have hZdetU : Matrix.GeneralLinearGroup.det Z = 1 := Units.ext (by simpa using hZdet)
    have hu3 : u ^ 3 = 1 := by
      have h1 := congrArg Matrix.GeneralLinearGroup.det hu
      simp only [map_mul, map_inv, hXdetU, hZdetU, mul_one, one_mul, inv_one] at h1
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
      exact h1
    rw [unit_eq_one_of_pow_three_eq_one hK hu3, map_one] at hu
    exact mul_inv_eq_one.mp hu.symm
  have hZ7M : (Z : Matrix (Fin 3) (Fin 3) K) ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hZ7, Units.val_one]
  have hZ1M : (Z : Matrix (Fin 3) (Fin 3) K) ≠ 1 := fun h => hZ1 (Units.ext h)
  have hX3M : (X : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hX3, Units.val_one]
  have hcommM : (X : Matrix (Fin 3) (Fin 3) K) * (Z : Matrix (Fin 3) (Fin 3) K) =
      (Z : Matrix (Fin 3) (Fin 3) K) * (X : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hcomm]
  have h1 := eq_one_of_commute_of_pow_seven' hK hZ7M hZ1M hcommM hX3M
  exact hX1 (Units.ext h1)

theorem l39_not_seven_dvd_card_centralizer
    (x : CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 2)) (hx : orderOf x = 3) :
    ¬ 7 ∣ Nat.card (Subgroup.centralizer
      ({x} : Set (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 2)))) :=
  not_seven_dvd_card_centralizer_of_card_nine card_galoisField_three_two x hx

end CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV
