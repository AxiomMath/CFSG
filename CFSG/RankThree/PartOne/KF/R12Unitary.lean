module

public import CFSG.RankThree.PartOne.KF.R12Lin
public import CFSG.RankThree.PartOne.KF.R12TwoLift
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KF.ToralQuot

public section

namespace CFSG.RankThree.PartOne.KFU

open Module Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane

section LemmaA

variable {K : Type} [Field K]

noncomputable abbrev toL (x : GL (Fin 5) K) : (Fin 5 → K) →ₗ[K] (Fin 5 → K) :=
  Matrix.toLin' (x : Matrix (Fin 5) (Fin 5) K)

theorem toL_apply (x : GL (Fin 5) K) (v : Fin 5 → K) :
    toL x v = (x : Matrix (Fin 5) (Fin 5) K) *ᵥ v := rfl

theorem toL_injective (x : GL (Fin 5) K) : Function.Injective (toL x) := by
  intro a b h
  have h1 : (x⁻¹ : GL (Fin 5) K).1 *ᵥ ((x : Matrix (Fin 5) (Fin 5) K) *ᵥ a) =
      (x⁻¹ : GL (Fin 5) K).1 *ᵥ ((x : Matrix (Fin 5) (Fin 5) K) *ᵥ b) := by
    rw [toL_apply, toL_apply] at h
    rw [h]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h1
  have h2 : ((x⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rwa [h2, Matrix.one_mulVec, Matrix.one_mulVec] at h1

theorem exists_of_mem_scalars {z : GL (Fin 5) K} (hz : z ∈ StatedScalars (Fin 5) K) :
    ∃ c : K, c ≠ 0 ∧ (z : Matrix (Fin 5) (Fin 5) K) = c • (1 : Matrix (Fin 5) (Fin 5) K) := by
  obtain ⟨c, rfl⟩ := hz
  refine ⟨(c : K), c.ne_zero, ?_⟩
  simp [Matrix.GeneralLinearGroup.scalar]
  exact (Matrix.smul_one_eq_diagonal _).symm

theorem det_smul_one_five (c : K) : (c • (1 : Matrix (Fin 5) (Fin 5) K)).det = c ^ 5 := by
  simp

theorem toL_pow (x : GL (Fin 5) K) (n : ℕ) (v : Fin 5 → K) :
    ((toL x) ^ n) v = ((x ^ n : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, toL_apply, Matrix.mulVec_mulVec, pow_succ',
      Units.val_mul]

theorem det_commutator_five (x y : GL (Fin 5) K) :
    ((x * y * x⁻¹ * y⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det (x * y * x⁻¹ * y⁻¹) = 1 := by
    have h2 := map_commutatorElement (Matrix.GeneralLinearGroup.det (n := Fin 5) (R := K)) x y
    rw [commutatorElement_def] at h2
    rw [h2]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have h3 := congrArg Units.val h1
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h3
  exact h3

variable [Finite K]

theorem abelian_exp_five_of_invariant (h25 : ¬ 25 ∣ Nat.card Kˣ)
    (W : Submodule K (Fin 5 → K)) (hW0 : 0 < finrank K W) (hW5 : finrank K W < 5)
    (B : Subgroup (GL (Fin 5) K))
    (hBW : ∀ x ∈ B, ∀ w ∈ W, (x : Matrix (Fin 5) (Fin 5) K) *ᵥ w ∈ W)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ StatedScalars (Fin 5) K)
    (hBe : ∀ x ∈ B, x ^ 5 ∈ StatedScalars (Fin 5) K)
    (hBd : ∀ x ∈ B, (x : Matrix (Fin 5) (Fin 5) K).det = 1) :
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ ∀ x ∈ B, x ^ 5 = 1 := by
  classical
  have hnp : ∀ c : K, c ^ 5 = 1 → c ^ finrank K W = 1 → c = 1 := by
    intro c h5 hW
    have hcop : Nat.Coprime 5 (finrank K W) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
      intro hd
      have := Nat.le_of_dvd hW0 hd
      omega
    have h1 : c ^ Nat.gcd 5 (finrank K W) = 1 := pow_gcd_eq_one.mpr ⟨h5, hW⟩
    rwa [hcop, pow_one] at h1
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc0, hc⟩ := exists_of_mem_scalars (hBc x hx y hy)
    have hxy : ((x * y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        c • ((y * x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
      have h1 : x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      rw [h1, Units.val_mul, hc, smul_mul_assoc, one_mul]
    have hc5 : c ^ 5 = 1 := by
      have h1 := congrArg Matrix.det hc
      rw [det_smul_one_five, det_commutator_five] at h1
      exact h1.symm
    have hcW : c ^ finrank K W = 1 := by
      refine comm_scalar_pow_finrank W (toL x) (toL y) (hBW x hx) (hBW y hy) (toL_injective x)
        (toL_injective y) c (fun v => ?_)
      rw [toL_apply, toL_apply, toL_apply, toL_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← Units.val_mul, ← Units.val_mul, hxy, Matrix.smul_mulVec]
    have hc1 := hnp c hc5 hcW
    have hcomm : x * y * x⁻¹ * y⁻¹ = 1 := Units.ext (by rw [hc, hc1, one_smul, Units.val_one])
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [hcomm, one_mul]
  · obtain ⟨c, hc0, hc⟩ := exists_of_mem_scalars (hBe x hx)
    have hc5 : c ^ 5 = 1 := by
      have h1 := congrArg Matrix.det hc
      rw [det_smul_one_five, Units.val_pow_eq_pow_val, Matrix.det_pow, hBd x hx, one_pow] at h1
      exact h1.symm
    by_cases hc1 : c = 1
    · apply Units.ext
      rw [hc, hc1, one_smul, Units.val_one]
    · exfalso
      have hprim : IsPrimitiveRoot c 5 := by
        rw [IsPrimitiveRoot.iff_orderOf]
        have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
        exact orderOf_eq_prime hc5 hc1
      refine false_of_pow_five_scalar W hW0 hW5 (toL x) (hBW x hx) c (fun v => ?_)
        (not_pow_five_of_primitive hprim h25)
      rw [toL_pow, hc, Matrix.smul_mulVec, Matrix.one_mulVec]

omit [Finite K] in
theorem exists_scalar_hom (A : Subgroup (GL (Fin 5) K)) (hAe : ∀ a ∈ A, a ^ 5 = 1)
    (g : GL (Fin 5) K) (hgA : ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ StatedScalars (Fin 5) K) :
    ∃ φ : ↥A →* Kˣ, (∀ a : A, ((g * (a : GL (Fin 5) K) * g⁻¹ : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = (φ a : K) • ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) ∧
      ∀ a, (φ a) ^ 5 = 1 := by
  classical
  have hex : ∀ a : A, ∃ c : K, c ≠ 0 ∧ ((g * (a : GL (Fin 5) K) * g⁻¹ : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = c • ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    intro a
    obtain ⟨c, hc0, hc⟩ := exists_of_mem_scalars (hgA a a.2)
    refine ⟨c, hc0, ?_⟩
    have h1 : g * (a : GL (Fin 5) K) * g⁻¹ = (g * (a : GL (Fin 5) K) * g⁻¹ * (a : GL (Fin 5) K)⁻¹) *
        (a : GL (Fin 5) K) := by group
    rw [h1, Units.val_mul, hc, smul_mul_assoc, one_mul]
  choose c hc0 hc using hex
  have hmul : ∀ a b : A, c (a * b) = c a * c b := by
    intro a b
    have h1 : ((g * ((a * b : A) : GL (Fin 5) K) * g⁻¹ : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = (c a * c b) • (((a * b : A) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) := by
      have h2 : g * ((a * b : A) : GL (Fin 5) K) * g⁻¹ =
          (g * (a : GL (Fin 5) K) * g⁻¹) * (g * (b : GL (Fin 5) K) * g⁻¹) := by
        rw [Subgroup.coe_mul]
        group
      rw [h2, Units.val_mul, hc a, hc b, Subgroup.coe_mul, Units.val_mul, smul_mul_assoc,
        mul_smul_comm, smul_smul]
    have h3 := hc (a * b)
    rw [h1] at h3
    have hM : (((a * b : A) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ≠ 0 :=
      ((a * b : A) : GL (Fin 5) K).ne_zero
    exact (smul_left_injective K hM h3).symm
  have hone : c 1 = 1 := by
    have h1 := hc 1
    have h2 : (g * (((1 : A) : GL (Fin 5) K)) * g⁻¹ : GL (Fin 5) K) = 1 := by
      rw [Subgroup.coe_one]
      group
    rw [h2] at h1
    have hM : (((1 : A) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ≠ 0 :=
      ((1 : A) : GL (Fin 5) K).ne_zero
    have h3 : (1 : K) • (((1 : A) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        c 1 • (((1 : A) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
      rw [one_smul, ← h1]
      simp
    exact (smul_left_injective K hM h3).symm
  let φ : ↥A →* Kˣ :=
    { toFun := fun a => Units.mk0 (c a) (hc0 a)
      map_one' := Units.ext hone
      map_mul' := fun a b => Units.ext (hmul a b) }
  refine ⟨φ, fun a => hc a, fun a => ?_⟩
  have : a ^ 5 = 1 := Subtype.ext (hAe a a.2)
  rw [← map_pow, this, map_one]

theorem centralizes_of_scalar_commutators {f : ℕ} (hU : UnitaryFieldData 2 f K)
    (h5 : 5 ∣ 2 ^ f + 1)
    (A : Subgroup (GL (Fin 5) K)) (hAU : A ≤ unitarySU 2 f K 5)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAe : ∀ x ∈ A, x ^ 5 = 1)
    (hAcard : Nat.card A = 125) (hAsc : Nat.card ↥(A ⊓ StatedScalars (Fin 5) K) ≤ 5)
    (g : GL (Fin 5) K) (hgA : ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ StatedScalars (Fin 5) K) :
    ∀ a ∈ A, g * a = a * g := by
  classical
  obtain ⟨φ, hφ, hφ5⟩ := exists_scalar_hom A hAe g hgA
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀, hne⟩ := hcon
  have hφa₀ : φ ⟨a₀, ha₀⟩ ≠ 1 := by
    intro h1
    apply hne
    have h2 := hφ ⟨a₀, ha₀⟩
    rw [h1, Units.val_one, one_smul] at h2
    have h3 : g * a₀ * g⁻¹ = a₀ := Units.ext h2
    calc g * a₀ = (g * a₀ * g⁻¹) * g := by group
      _ = a₀ * g := by rw [h3]
  have hrange : Nat.card φ.range = 5 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hord : orderOf (φ ⟨a₀, ha₀⟩) = 5 := orderOf_eq_prime (hφ5 _) hφa₀
    have hge : 5 ≤ Nat.card φ.range := by
      have h1 : Subgroup.zpowers (φ ⟨a₀, ha₀⟩) ≤ φ.range :=
        (Subgroup.zpowers_le).mpr ⟨⟨a₀, ha₀⟩, rfl⟩
      have h2 := Subgroup.card_le_of_le h1
      rwa [Nat.card_zpowers, hord] at h2
    have hle : Nat.card φ.range ≤ 5 := by
      have h1 : φ.range ≤ rootsOfUnity 5 K := by
        rintro _ ⟨a, rfl⟩
        exact (mem_rootsOfUnity 5 (φ a)).mpr (hφ5 a)
      exact (Subgroup.card_le_of_le h1).trans (card_rootsOfUnity K 5)
    omega
  have hker : Nat.card φ.ker = 25 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hrange, hAcard] at h1
    omega
  obtain ⟨b, hbA, hbφ, hbsc⟩ : ∃ b : GL (Fin 5) K, ∃ hb : b ∈ A, φ ⟨b, hb⟩ = 1 ∧
      b ∉ StatedScalars (Fin 5) K := by
    by_contra hno
    push Not at hno
    have hsub : φ.ker.map A.subtype ≤ A ⊓ StatedScalars (Fin 5) K := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.2, hno x.1 x.2 hx⟩
    have h1 := Subgroup.card_le_of_le hsub
    rw [Subgroup.card_map_of_injective A.subtype_injective, hker] at h1
    omega
  have hle := unitarySU_le_primeFormUnitary (n := 5) hU
  let a' : primeFormUnitary hU (idGram K 5) := ⟨a₀, hle (hAU ha₀)⟩
  let b' : primeFormUnitary hU (idGram K 5) := ⟨b, hle (hAU hbA)⟩
  have hab' : a' * b' = b' * a' := Subtype.ext (hAab a₀ ha₀ b hbA)
  have hScomm : ∀ x ∈ ({a', b'} : Set (primeFormUnitary hU (idGram K 5))),
      ∀ y ∈ ({a', b'} : Set (primeFormUnitary hU (idGram K 5))), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hab'
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hab'.symm
    · rw [Set.mem_singleton_iff] at hx hy
      rw [hx, hy]
  have hSexp : ∀ x ∈ ({a', b'} : Set (primeFormUnitary hU (idGram K 5))), x ^ 5 = 1 := by
    intro x hx
    rcases hx with rfl | hx
    · exact Subtype.ext (hAe a₀ ha₀)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subtype.ext (hAe b hbA)
  obtain ⟨hcl1, hcl2⟩ := closure_comm_exp (p := 5) _ hScomm hSexp
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag hU Nat.prime_five h5
    (Subgroup.closure {a', b'}) hcl1 hcl2
  have hda := hP a' (Subgroup.subset_closure (Set.mem_insert _ _))
  have hdb := hP b' (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  obtain ⟨l, hl⟩ := exists_diagU_of_isDiag hda
  obtain ⟨m, hm⟩ := exists_diagU_of_isDiag hdb
  set Pm : GL (Fin 5) K := (P : GL (Fin 5) K) with hPm
  have hl' : diagU l = Pm⁻¹ * a₀ * Pm := by rw [hl]; rfl
  have hm' : diagU m = Pm⁻¹ * b * Pm := by rw [hm]; rfl
  set ζ' : K := ((φ ⟨a₀, ha₀⟩ : Kˣ) : K) with hζ'
  have hζ'prim : IsPrimitiveRoot ζ' 5 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    rw [hζ', IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf]
    exact orderOf_eq_prime (hφ5 _) hφa₀
  have hga : ((g * a₀ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ζ' • ((a₀ * g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    have h1 := hφ ⟨a₀, ha₀⟩
    have h2 : g * a₀ = (g * a₀ * g⁻¹) * g := by group
    rw [h2, Units.val_mul, h1, smul_mul_assoc, ← Units.val_mul]
  have hgb : ((g * b : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (1 : K) • ((b * g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    have h1 := hφ ⟨b, hbA⟩
    rw [hbφ, Units.val_one, one_smul] at h1
    have h3 : g * b * g⁻¹ = b := Units.ext h1
    have h4 : g * b = b * g := by
      calc g * b = (g * b * g⁻¹) * g := by group
        _ = b * g := by rw [h3]
    rw [h4, one_smul]
  have hconj : ∀ {x y : GL (Fin 5) K} {c : K}
      (h : ((x * y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        c • ((y * x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)),
      (((Pm⁻¹ * x * Pm) * (Pm⁻¹ * y * Pm) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        c • (((Pm⁻¹ * y * Pm) * (Pm⁻¹ * x * Pm) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    intro x y c h
    have e1 : (Pm⁻¹ * x * Pm) * (Pm⁻¹ * y * Pm) = Pm⁻¹ * (x * y) * Pm := by group
    have e2 : (Pm⁻¹ * y * Pm) * (Pm⁻¹ * x * Pm) = Pm⁻¹ * (y * x) * Pm := by group
    rw [e1, e2]
    show ((Pm⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((x * y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * (Pm : Matrix (Fin 5) (Fin 5) K) =
      c • (((Pm⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((y * x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * (Pm : Matrix (Fin 5) (Fin 5) K))
    rw [h, Matrix.mul_smul, Matrix.smul_mul]
  have hfa := hconj hga
  have hfb := hconj hgb
  rw [← hl'] at hfa
  rw [← hm'] at hfb
  have hl0 : ∀ i, (l i : K) ≠ 0 := fun i => (l i).ne_zero
  have hdet : ((Pm⁻¹ * g * Pm : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Pm⁻¹ * g * Pm).isUnit).ne_zero
  have hmconst := heis_const hζ'prim (fun i => (l i : K)) (fun i => (m i : K)) hl0
    ((Pm⁻¹ * g * Pm : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) hdet
    (fun i j => by
      have h1 := congrFun (congrFun hfa i) j
      simp only [Units.val_mul, diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.smul_apply, smul_eq_mul] at h1 ⊢
      rw [h1]
      ring)
    (fun i j => by
      have h1 := congrFun (congrFun hfb i) j
      simp only [Units.val_mul, diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.smul_apply, smul_eq_mul, one_mul] at h1 ⊢
      rw [h1])
  apply hbsc
  have hmeq : diagU m = Matrix.GeneralLinearGroup.scalar (Fin 5) (m 0) := by
    apply Units.ext
    rw [diagU_val]
    have h1 : (fun i => (m i : K)) = fun _ => (m 0 : K) := funext fun i => hmconst i 0
    simp only [Matrix.GeneralLinearGroup.scalar, h1]
    rfl
  have hcent : Matrix.GeneralLinearGroup.scalar (Fin 5) (m 0) ∈ Subgroup.center (GL (Fin 5) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨m 0, rfl⟩
  have hb : b = Matrix.GeneralLinearGroup.scalar (Fin 5) (m 0) := by
    have h1 : b = Pm * (Pm⁻¹ * b * Pm) * Pm⁻¹ := by group
    rw [h1, ← hm', hmeq]
    have h2 := Subgroup.mem_center_iff.mp hcent Pm
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
  rw [hb]
  exact ⟨m 0, rfl⟩

omit [Finite K] in
theorem prod_range_X_sub_C {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    ∏ i ∈ Finset.range 5, (Polynomial.X - Polynomial.C (ζ ^ i)) =
      Polynomial.X ^ 5 - 1 := by
  classical
  rw [Polynomial.X_pow_sub_one_eq_prod (by norm_num) hζ]
  have himg : Polynomial.nthRootsFinset 5 (1 : K) = (Finset.range 5).image (fun i => ζ ^ i) := by
    ext x
    rw [Polynomial.mem_nthRootsFinset (by norm_num), Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := hζ.eq_pow_of_pow_eq_one hx
      exact ⟨i, Finset.mem_range.mpr hi, hix⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [himg, Finset.prod_image]
  intro i hi j hj hij
  exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

omit [Finite K] in
theorem exists_eigenspace_ne_bot {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (a : GL (Fin 5) K)
    (ha : a ^ 5 = 1) : ∃ c : K, LinearMap.ker (toL a - c • LinearMap.id) ≠ ⊥ := by
  classical
  have hN : ∀ v, ((toL a) ^ 5) v = v := fun v => by
    rw [toL_pow, ha, Units.val_one, Matrix.one_mulVec]
  obtain ⟨w, hw⟩ : ∃ w : Fin 5 → K, w ≠ 0 := ⟨Pi.single 0 1, fun h => by
    have := congrFun h 0
    simp at this⟩
  let Q : ℕ → Polynomial K := fun k => ∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (ζ ^ i))
  let u : ℕ → (Fin 5 → K) := fun k => (Polynomial.aeval (toL a) (Q k)) w
  have hu0 : u 0 = w := by simp [u, Q]
  have hu5 : u 5 = 0 := by
    have h1 : Q 5 = Polynomial.X ^ 5 - 1 := prod_range_X_sub_C hζ
    simp only [u, h1, map_sub, map_pow, Polynomial.aeval_X, map_one]
    simp [hN w]
  have hustep : ∀ k, u (k + 1) =
      (toL a - ζ ^ k • (LinearMap.id : (Fin 5 → K) →ₗ[K] (Fin 5 → K))) (u k) := by
    intro k
    have h1 : Q (k + 1) = (Polynomial.X - Polynomial.C (ζ ^ k)) * Q k := by
      simp only [Q, Finset.prod_range_succ]
      ring
    have h2 : Polynomial.aeval (toL a) (Polynomial.X - Polynomial.C (ζ ^ k)) =
        toL a - ζ ^ k • (LinearMap.id : (Fin 5 → K) →ₗ[K] (Fin 5 → K)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Module.algebraMap_end_eq_smul_id]
    simp only [u, h1, map_mul, h2, Module.End.mul_apply]
  have hex : ∃ k, k < 5 ∧ u k ≠ 0 ∧ u (k + 1) = 0 := by
    have hP : ∃ m, u m = 0 := ⟨5, hu5⟩
    have hm₀ : u (Nat.find hP) = 0 := Nat.find_spec hP
    have hm₀pos : Nat.find hP ≠ 0 := by
      intro h
      rw [h, hu0] at hm₀
      exact hw hm₀
    have hm₀le : Nat.find hP ≤ 5 := Nat.find_min' hP hu5
    refine ⟨Nat.find hP - 1, by omega, Nat.find_min hP (by omega), ?_⟩
    rw [Nat.sub_add_cancel (by omega)]
    exact hm₀
  obtain ⟨k, -, hk, hk1⟩ := hex
  refine ⟨ζ ^ k, fun hbot => hk ?_⟩
  have : u k ∈ LinearMap.ker (toL a - ζ ^ k • (LinearMap.id : (Fin 5 → K) →ₗ[K] (Fin 5 → K))) := by
    rw [LinearMap.mem_ker, ← hustep k, hk1]
  rw [hbot] at this
  exact (Submodule.mem_bot K).mp this

omit [Finite K] in
theorem mem_scalars_of_toL_eq (a : GL (Fin 5) K) (c : K) (h : ∀ v, toL a v = c • v) :
    a ∈ StatedScalars (Fin 5) K := by
  have hM : (a : Matrix (Fin 5) (Fin 5) K) = c • (1 : Matrix (Fin 5) (Fin 5) K) := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    have := h v
    rw [toL_apply] at this
    simp [Matrix.toLin'_apply, this]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hM
    exact a.ne_zero hM
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [hM]
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]

theorem card_inf_scalars_le (A : Subgroup (GL (Fin 5) K))
    (hdet : ∀ x ∈ A, (x : Matrix (Fin 5) (Fin 5) K).det = 1) :
    Nat.card ↥(A ⊓ StatedScalars (Fin 5) K) ≤ 5 := by
  have hinj :
      Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 5) : Kˣ →* GL (Fin 5) K) := by
    intro c d h
    have h1 := congrArg (fun z : GL (Fin 5) K => (z : Matrix (Fin 5) (Fin 5) K) 0 0) h
    simpa [Matrix.GeneralLinearGroup.scalar] using Units.ext h1
  have hle : A ⊓ StatedScalars (Fin 5) K ≤
      (rootsOfUnity 5 K).map (Matrix.GeneralLinearGroup.scalar (Fin 5)) := by
    rintro _ ⟨hxA, c, rfl⟩
    refine ⟨c, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_rootsOfUnity]
    have h1 := hdet _ hxA
    have h2 : ((Matrix.GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = (c : K) • (1 : Matrix (Fin 5) (Fin 5) K) := by
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]
    rw [h2, det_smul_one_five] at h1
    exact Units.ext (by simpa using h1)
  have := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective hinj] at this
  exact this.trans (card_rootsOfUnity K 5)

theorem abelian_exp_five_of_contains {f : ℕ} (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h25 : ¬ 25 ∣ Nat.card Kˣ)
    (X A T : Subgroup (GL (Fin 5) K)) (hAX : A ≤ X) (hXU : X ≤ unitarySU 2 f K 5)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ StatedScalars (Fin 5) K)
    (hXe : ∀ x ∈ X, x ^ 5 ∈ StatedScalars (Fin 5) K) (hAcard : Nat.card A = 125)
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hAT : ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T) :
    (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) ∧ ∀ x ∈ X, x ^ 5 = 1 := by
  classical
  have hdet : ∀ x ∈ X, (x : Matrix (Fin 5) (Fin 5) K).det = 1 := fun x hx =>
    ((mem_unitarySU_iff hU).mp (hXU hx)).1
  have hK2 : 2 ∣ Nat.card K := by
    rw [hU.card]
    exact dvd_pow_self 2 (by have := hU.one_le; omega)
  have hWne : fixedSpace T ≠ ⊥ := fixedSpace_ne_bot hK2 (by norm_num) hT2
  have hWtop : fixedSpace T ≠ ⊤ := fixedSpace_ne_top hT
  have hW0 : 0 < finrank K (fixedSpace T) := Submodule.one_le_finrank_iff.mpr hWne
  have hW5 : finrank K (fixedSpace T) < 5 := by
    have := Submodule.finrank_lt hWtop
    simpa using this
  have hAW : ∀ a ∈ A, ∀ w ∈ fixedSpace T, (a : Matrix (Fin 5) (Fin 5) K) *ᵥ w ∈ fixedSpace T :=
    fun a ha w hw => fixedSpace_invariant
      (fun t ht => by simpa using hAT a⁻¹ (A.inv_mem ha) t ht) hw
  obtain ⟨hAab, hAe⟩ := abelian_exp_five_of_invariant h25 (fixedSpace T) hW0 hW5 A hAW
    (fun x hx y hy => hXc x (hAX hx) y (hAX hy)) (fun x hx => hXe x (hAX hx))
    (fun x hx => hdet x (hAX hx))
  have hAsc := card_inf_scalars_le A (fun x hx => hdet x (hAX hx))
  have hcent : ∀ g ∈ X, ∀ a ∈ A, g * a = a * g := fun g hg =>
    centralizes_of_scalar_commutators hU h5 A (hAX.trans hXU) hAab hAe hAcard hAsc g
      (fun a ha => hXc g hg a (hAX ha))
  obtain ⟨a₁, ha₁, ha₁sc⟩ : ∃ a₁ ∈ A, a₁ ∉ StatedScalars (Fin 5) K := by
    by_contra hno
    push Not at hno
    have hle : A ≤ A ⊓ StatedScalars (Fin 5) K := fun x hx => ⟨hx, hno x hx⟩
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨c, hc⟩ := exists_eigenspace_ne_bot hζ a₁ (hAe a₁ ha₁)
  let N : Submodule K (Fin 5 → K) :=
    LinearMap.ker (toL a₁ - c • (LinearMap.id : (Fin 5 → K) →ₗ[K] (Fin 5 → K)))
  have hNne : N ≠ ⊥ := hc
  have hNtop : N ≠ ⊤ := by
    intro htop
    apply ha₁sc
    refine mem_scalars_of_toL_eq a₁ c fun v => ?_
    have hv : v ∈ N := htop ▸ Submodule.mem_top
    have := LinearMap.mem_ker.mp hv
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
    exact sub_eq_zero.mp this
  have hN0 : 0 < finrank K N := Submodule.one_le_finrank_iff.mpr hNne
  have hN5 : finrank K N < 5 := by
    have := Submodule.finrank_lt hNtop
    simpa using this
  have hXN : ∀ x ∈ X, ∀ w ∈ N, (x : Matrix (Fin 5) (Fin 5) K) *ᵥ w ∈ N := by
    intro x hx w hw
    have hw' := LinearMap.mem_ker.mp hw
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hw'
    have hcomm : (a₁ : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K) =
        (x : Matrix (Fin 5) (Fin 5) K) * (a₁ : Matrix (Fin 5) (Fin 5) K) := by
      rw [← Units.val_mul, ← Units.val_mul, (hcent x hx a₁ ha₁).symm]
    change (toL a₁ - c • (LinearMap.id : (Fin 5 → K) →ₗ[K] (Fin 5 → K)))
      ((x : Matrix (Fin 5) (Fin 5) K) *ᵥ w) = 0
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, toL_apply]
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
    have hw'' : (a₁ : Matrix (Fin 5) (Fin 5) K) *ᵥ w = c • w := by
      rw [toL_apply] at hw'
      exact sub_eq_zero.mp hw'
    rw [hw'', Matrix.mulVec_smul, sub_self]
  exact abelian_exp_five_of_invariant h25 N hN0 hN5 X hXN hXc hXe hdet

end LemmaA

section PLevel

variable {f : ℕ} {K : Type} [Field K] [Finite K]

@[expose] def scalarsU (K : Type) [Field K] (f : ℕ) : Subgroup ↥(unitarySU 2 f K 5) :=
  (StatedScalars (Fin 5) K).subgroupOf (unitarySU 2 f K 5)

instance : (scalarsU K f).Normal := by
  unfold scalarsU
  infer_instance

@[expose] def projU (K : Type) [Field K] (f : ℕ) :
    ↥(unitarySU 2 f K 5) →* StatedProj (unitarySU 2 f K 5) :=
  QuotientGroup.mk' (scalarsU K f)

omit [Finite K] in
theorem projU_surjective : Function.Surjective (projU K f) := QuotientGroup.mk'_surjective _

omit [Finite K] in
theorem ker_projU : (projU K f).ker = scalarsU K f := QuotientGroup.ker_mk' _

omit [Finite K] in
theorem scalarsU_le_center : scalarsU K f ≤ Subgroup.center ↥(unitarySU 2 f K 5) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hz' : (z : GL (Fin 5) K) ∈ Subgroup.center (GL (Fin 5) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hz
  exact Subtype.ext (Subgroup.mem_center_iff.mp hz' g)

theorem card_comap_projU (A : Subgroup (StatedProj (unitarySU 2 f K 5))) :
    Nat.card (A.comap (projU K f)) = Nat.card A * Nat.card (scalarsU K f) := by
  have h1 := Subgroup.card_mul_index A
  have h2 := Subgroup.card_mul_index (A.comap (projU K f))
  have h3 := Subgroup.card_ker_mul_card_of_surjective (projU_surjective (K := K) (f := f))
  rw [ker_projU] at h3
  rw [Subgroup.index_comap_of_surjective _ (projU_surjective (K := K) (f := f))] at h2
  have hi : 0 < A.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  apply Nat.eq_of_mul_eq_mul_right hi
  calc Nat.card (A.comap (projU K f)) * A.index = Nat.card ↥(unitarySU 2 f K 5) := h2
    _ = Nat.card (scalarsU K f) * Nat.card (StatedProj (unitarySU 2 f K 5)) := h3.symm
    _ = Nat.card (scalarsU K f) * (Nat.card A * A.index) := by rw [h1]
    _ = Nat.card A * Nat.card (scalarsU K f) * A.index := by ring

theorem card_scalarsU (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) : Nat.card (scalarsU K f) = 5 := by
  have hinj :
      Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 5) : Kˣ →* GL (Fin 5) K) := by
    intro c d h
    have h1 := congrArg (fun z : GL (Fin 5) K => (z : Matrix (Fin 5) (Fin 5) K) 0 0) h
    simpa [Matrix.GeneralLinearGroup.scalar] using Units.ext h1
  have hmap : (scalarsU K f).map (unitarySU 2 f K 5).subtype =
      unitarySU 2 f K 5 ⊓ StatedScalars (Fin 5) K := by
    unfold scalarsU
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hle : Nat.card (scalarsU K f) ≤ 5 := by
    have h1 := card_inf_scalars_le (unitarySU 2 f K 5)
      (fun x hx => ((mem_unitarySU_iff hU).mp hx).1)
    rw [← hmap, Subgroup.card_map_of_injective (unitarySU 2 f K 5).subtype_injective] at h1
    exact h1
  have hge : 5 ≤ Nat.card (scalarsU K f) := by
    have hR : (rootsOfUnity 5 K).map (Matrix.GeneralLinearGroup.scalar (Fin 5)) ≤
        unitarySU 2 f K 5 ⊓ StatedScalars (Fin 5) K := by
      rintro _ ⟨c, hc, rfl⟩
      have hc5 : c ^ 5 = 1 := (mem_rootsOfUnity 5 c).mp hc
      refine ⟨?_, c, rfl⟩
      have h1 : Matrix.GeneralLinearGroup.scalar (Fin 5) c = diagU (fun _ => c) := by
        apply Units.ext
        rw [diagU_val]
        simp [Matrix.GeneralLinearGroup.scalar]
      rw [h1]
      refine torusSU_le_unitarySU hU h5 (mem_torusSU_iff.mpr ⟨fun _ => c, fun _ => hc5, ?_, rfl⟩)
      simp [Finset.prod_const, hc5]
    have h1 := Subgroup.card_le_of_le hR
    rw [Subgroup.card_map_of_injective hinj, ← hmap,
      Subgroup.card_map_of_injective (unitarySU 2 f K 5).subtype_injective] at h1
    have : NeZero 5 := ⟨by norm_num⟩
    have hcard : Nat.card (rootsOfUnity 5 K) = 5 := IsPrimitiveRoot.card_rootsOfUnity hζ
    omega
  omega

omit [Finite K] in
theorem not_dvd_card_units (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (h25 : ¬ 25 ∣ 2 ^ f + 1) : ¬ 25 ∣ Nat.card Kˣ := by
  have hfin := hU.finite
  rw [Nat.card_units, hU.card]
  intro hd
  have h1 : 2 ^ (2 * f) - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : (2 : ℕ) ^ (2 * f) = 2 ^ f * 2 ^ f := by rw [two_mul, pow_add]
    rw [this]
    have h3 := Nat.mul_self_sub_mul_self_eq (2 ^ f) 1
    simpa using h3
  rw [h1] at hd
  have hcop : Nat.Coprime 5 (2 ^ f - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    intro h
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 5 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h5 h
    have : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rw [this] at h2
    omega
  have hcop25 : Nat.Coprime 25 (2 ^ f - 1) := by
    have : (25 : ℕ) = 5 ^ 2 := by norm_num
    rw [this]
    exact Nat.Coprime.pow_left 2 hcop
  exact h25 (hcop25.dvd_of_dvd_mul_right hd)

@[expose] def torusBar (K : Type) [Field K] (f : ℕ) : Subgroup (StatedProj (unitarySU 2 f K 5)) :=
  ((torusSU 5 5 K).subgroupOf (unitarySU 2 f K 5)).map (projU K f)

omit [Finite K] in
theorem toral_conj_of_contains (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (h25 : ¬ 25 ∣ 2 ^ f + 1) (X A S : Subgroup (StatedProj (unitarySU 2 f K 5)))
    (hAX : A ≤ X) (hAcard : Nat.card A = 25) (hXe : ∀ x ∈ X, x ^ 5 = 1)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hAS : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S) :
    ∃ α : MulAut (StatedProj (unitarySU 2 f K 5)), ∀ x ∈ X, α x ∈ torusBar K f := by
  classical
  have hfin := hU.finite
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hU Nat.prime_five h5
  have h25' : ¬ 25 ∣ Nat.card Kˣ := not_dvd_card_units hU h5 h25
  obtain ⟨T, hTne, hT2, hAT⟩ := exists_two_subgroup_lift (projU K f) projU_surjective
    (scalarsU K f) ker_projU scalarsU_le_center S hS hS2 (A.comap (projU K f))
    (fun a ha s hs => hAS _ ha s hs)
  have hinj := (unitarySU 2 f K 5).subtype_injective
  let Xt : Subgroup ↥(unitarySU 2 f K 5) := X.comap (projU K f)
  let At : Subgroup ↥(unitarySU 2 f K 5) := A.comap (projU K f)
  have hXt_mem : ∀ x : ↥(unitarySU 2 f K 5), x ∈ Xt ↔ projU K f x ∈ X := fun x => Iff.rfl
  have hscal : ∀ z : ↥(unitarySU 2 f K 5), projU K f z = 1 →
      (z : GL (Fin 5) K) ∈ StatedScalars (Fin 5) K := fun z hz => by
    have : z ∈ scalarsU K f := by rw [← ker_projU]; exact hz
    exact Subgroup.mem_subgroupOf.mp this
  have hmain := abelian_exp_five_of_contains hU h5 hζ h25' (Xt.map (unitarySU 2 f K 5).subtype)
    (At.map (unitarySU 2 f K 5).subtype) (T.map (unitarySU 2 f K 5).subtype)
    (Subgroup.map_mono (Subgroup.comap_mono hAX)) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have h1 : projU K f (x * y * x⁻¹ * y⁻¹) = 1 := by
        have := hXc _ hx _ hy
        simp only [map_mul, map_inv]
        rw [this]
        group
      simpa using hscal _ h1)
    (by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : projU K f (x ^ 5) = 1 := by rw [map_pow]; exact hXe _ hx
      simpa using hscal _ h1)
    (by
      rw [Subgroup.card_map_of_injective hinj, card_comap_projU, hAcard,
        card_scalarsU hU h5 hζ])
    (fun h => hTne ((Subgroup.map_eq_bot_iff_of_injective _ hinj).mp h)) (hT2.map _)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨t, ht, rfl⟩
      exact ⟨a * t * a⁻¹, hAT a ha t ht, by simp⟩)
  obtain ⟨hab, hexp⟩ := hmain
  have hle := unitarySU_le_primeFormUnitary (n := 5) hU
  let G' : Subgroup (primeFormUnitary hU (idGram K 5)) := Xt.map (Subgroup.inclusion hle)
  have hG'mem : ∀ x ∈ G', ∃ x₀ ∈ Xt, Subgroup.inclusion hle x₀ = x := fun x hx => by
    obtain ⟨x₀, hx₀, hx⟩ := Subgroup.mem_map.mp hx
    exact ⟨x₀, hx₀, hx⟩
  have hGcomm : ∀ x ∈ G', ∀ y ∈ G', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hG'mem y hy
    apply Subtype.ext
    exact hab _ ⟨x₀, hx₀, rfl⟩ _ ⟨y₀, hy₀, rfl⟩
  have hGpow : ∀ x ∈ G', x ^ 5 = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    apply Subtype.ext
    exact hexp _ ⟨x₀, hx₀, rfl⟩
  obtain ⟨Pc, hPc⟩ := exists_unitary_conj_diag hU Nat.prime_five h5 G' hGcomm hGpow
  let α₀ : ↥(unitarySU 2 f K 5) ≃* ↥(unitarySU 2 f K 5) := conjSU hU Pc⁻¹
  have hα₀z : ∀ z ∈ scalarsU K f, α₀ z = z := by
    intro z hz
    apply Subtype.ext
    have hz' : (z : GL (Fin 5) K) ∈ Subgroup.center (GL (Fin 5) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hz
    have h1 := Subgroup.mem_center_iff.mp hz' (Pc : GL (Fin 5) K)⁻¹
    show (Pc⁻¹ : primeFormUnitary hU (idGram K 5)).1 * (z : GL (Fin 5) K) *
      ((Pc⁻¹ : primeFormUnitary hU (idGram K 5)).1)⁻¹ = z
    have h2 : (Pc⁻¹ : primeFormUnitary hU (idGram K 5)).1 = (Pc : GL (Fin 5) K)⁻¹ := rfl
    rw [h2, inv_inv, h1, mul_assoc, inv_mul_cancel, mul_one]
  have hmap : (scalarsU K f).map α₀.toMonoidHom = scalarsU K f := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hα₀z w hw]
      exact hw
    · intro hz
      exact ⟨z, hz, hα₀z z hz⟩
  refine ⟨QuotientGroup.congr (scalarsU K f) (scalarsU K f) α₀ hmap, fun x hx => ?_⟩
  obtain ⟨x₀, rfl⟩ := projU_surjective x
  have hx₀ : x₀ ∈ Xt := hx
  have hdiag := hPc _ (Subgroup.mem_map.mpr ⟨x₀, hx₀, rfl⟩)
  have hco : (((Pc⁻¹ * Subgroup.inclusion hle x₀ * Pc :
      primeFormUnitary hU (idGram K 5)) : GL (Fin 5) K)) = ((α₀ x₀ : ↥(unitarySU 2 f K 5)) :
      GL (Fin 5) K) := rfl
  rw [hco] at hdiag
  obtain ⟨d, hd⟩ := exists_diagU_of_isDiag hdiag
  have hx5 : (x₀ : GL (Fin 5) K) ^ 5 = 1 := by
    have := hexp _ ⟨x₀, hx₀, rfl⟩
    simpa using this
  have hα5 : ((α₀ x₀ : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) ^ 5 = 1 := by
    have : α₀ x₀ ^ 5 = 1 := by
      rw [← map_pow]
      have : x₀ ^ 5 = 1 := Subtype.ext hx5
      rw [this, map_one]
    simpa using congrArg Subtype.val this
  refine ⟨α₀ x₀, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    refine mem_torusSU_iff.mpr ⟨d, fun i => ?_, ?_, hd⟩
    · have h1 : diagU (d ^ 5) = 1 := by rw [← diagU_pow, hd, hα5]
      have h2 : d ^ 5 = 1 := diagU_injective (h1.trans diagU_one.symm)
      exact congrFun h2 i
    · have hdet := ((mem_unitarySU_iff hU).mp (α₀ x₀).2).1
      rw [← hd, det_diagU] at hdet
      exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hdet)
  · exact (QuotientGroup.congr_mk (scalarsU K f) (scalarsU K f) α₀ hmap x₀).symm

end PLevel

end CFSG.RankThree.PartOne.KFU
