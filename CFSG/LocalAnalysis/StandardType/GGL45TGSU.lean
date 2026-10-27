module

public import CFSG.LocalAnalysis.StandardType.GGL45TALinRecipe
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover

public section

namespace CFSG.StandardType.GGL45TG.SU

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

variable {n d : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)

@[expose] def CU (h : UnitaryFieldData 2 n K) (d : ℕ) : Subgroup (GL (Fin d) K) where
  carrier := {x | ∃ μ : K, ((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
    (x : Matrix (Fin d) (Fin d) K) = μ • (1 : Matrix (Fin d) (Fin d) K)}
  mul_mem' := by
    rintro x y ⟨μ, hx⟩ ⟨ν, hy⟩
    refine ⟨μ * ν, ?_⟩
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ, hx, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, hy, smul_smul]
  one_mem' := ⟨1, by
    rw [Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one,
      Matrix.one_mul, one_smul]⟩
  inv_mem' := by
    rintro x ⟨μ, hx⟩
    refine ⟨μ⁻¹, ?_⟩
    have hXY : (x : Matrix (Fin d) (Fin d) K) *
        ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : (((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
        ((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hXY,
        Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one]
    have h3 : μ • ((((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
        ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 := by
      rw [← Matrix.smul_mul, ← hXY]
      congr 1
      calc μ • (((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ
          = (((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
              (μ • (1 : Matrix (Fin d) (Fin d) K)) := by
            rw [Matrix.mul_smul, Matrix.mul_one]
        _ = (((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
              ((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (x : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.mul_assoc, hx]
        _ = (x : Matrix (Fin d) (Fin d) K) := by rw [h1, Matrix.one_mul]
    by_cases hμ : μ = 0
    · rw [hμ, zero_smul] at h3
      have hall : ∀ M : Matrix (Fin d) (Fin d) K, M = 0 := fun M => by
        rw [← Matrix.mul_one M, ← h3, Matrix.mul_zero]
      exact (hall _).trans (hall _).symm
    · rw [← h3, smul_smul, inv_mul_cancel₀ hμ, one_smul]

theorem mem_cu_iff {x : GL (Fin d) K} : x ∈ CU h d ↔ ∃ μ : K,
    ((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (x : Matrix (Fin d) (Fin d) K) =
      μ • (1 : Matrix (Fin d) (Fin d) K) := Iff.rfl

private theorem barT_mul_mul (A B : Matrix (Fin d) (Fin d) K) :
    ((A * B).map h.bar)ᵀ * (A * B) = (B.map h.bar)ᵀ * ((A.map h.bar)ᵀ * A) * B := by
  rw [Matrix.map_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

private theorem smul_barT_inv {x : GL (Fin d) K} {μ : K}
    (hx : ((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (x : Matrix (Fin d) (Fin d) K) =
      μ • (1 : Matrix (Fin d) (Fin d) K)) :
    μ • ((((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 := by
  have hXY : (x : Matrix (Fin d) (Fin d) K) *
      ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      ((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hXY,
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one]
  rw [← Matrix.smul_mul, ← hXY]
  congr 1
  calc μ • (((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ
      = (((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
          (μ • (1 : Matrix (Fin d) (Fin d) K)) := by
        rw [Matrix.mul_smul, Matrix.mul_one]
    _ = (((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
          ((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (x : Matrix (Fin d) (Fin d) K) := by
        rw [Matrix.mul_assoc, hx]
    _ = (x : Matrix (Fin d) (Fin d) K) := by rw [h1, Matrix.one_mul]

private theorem pair_ne (hn : 2 ≤ n) : (d, 2 ^ n) ≠ (3, 2) := by
  intro he
  have h2 : 2 ^ n = 2 := congrArg Prod.snd he
  have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

private theorem not_three_two (hn : 2 ≤ n) : ¬(d = 3 ∧ 2 ^ n = 2) := fun ⟨_, h2⟩ => by
  have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

private theorem glAut_eq_map (σ : K ≃+* K) (g : GL (Fin d) K) :
    glAut σ g = Matrix.GeneralLinearGroup.map σ.toRingHom g :=
  Units.ext rfl

private theorem projMk_eq (hd : 1 ≤ d) (c : LargeEvenSUGroup (Fin d) K (2 ^ n)) :
    InndiagSU.projEquiv h hd (LargeEvenProjMk _ c) =
      ((⟨c, InndiagSU.largeEvenSUGroup_eq_gramSU (d := d) h ▸ c.2⟩ :
        gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
          primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :=
  InndiagSU.projEquiv_mk h hd c

theorem mem_su_iff {g : GL (Fin d) K} : g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) ↔
    ((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (g : Matrix (Fin d) (Fin d) K) = 1 ∧
      (g : Matrix (Fin d) (Fin d) K).det = 1 := by
  rw [InndiagSU.largeEvenSUGroup_eq_gramSU h, mem_gramSU, Units.val_one, Matrix.mul_one]

include h in
theorem commutator_su (hd : 3 ≤ d) (hn : 2 ≤ n) :
    ⁅LargeEvenSUGroup (Fin d) K (2 ^ n), LargeEvenSUGroup (Fin d) K (2 ^ n)⁆ =
      LargeEvenSUGroup (Fin d) K (2 ^ n) := by
  have := h.finite
  have := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Subgroup.isPerfect_iff.mp
    (CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd (F := K) (p := 2) (f := n)
      h.card_eq_sq hd (pair_ne hn))

include h in
theorem mem_scalars_of_commute_su (hd : 3 ≤ d) (c : GL (Fin d) K)
    (hc : ∀ g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n), Commute c g) :
    c ∈ LargeEvenScalars (Fin d) K :=
  TableBUE.mem_scalars_of_commute h
    (Nat.minFac_prime (by have := Nat.one_le_two_pow (n := n); omega)) (Nat.minFac_dvd _)
    fun g hg => (hc g hg).eq

include h in
theorem map_mem_su (σ : K ≃+* K) {g : GL (Fin d) K}
    (hg : g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n)) :
    Matrix.GeneralLinearGroup.map σ.toRingHom g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
  set S : Set (GL (Fin d) K) := {A | (A : Matrix (Fin d) (Fin d) K).det = 1 ∧
    ((A : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ n))ᵀ * (A : Matrix (Fin d) (Fin d) K) = 1}
  have hSU : LargeEvenSUGroup (Fin d) K (2 ^ n) = Subgroup.closure S := rfl
  rw [hSU] at hg ⊢
  have hle : Subgroup.closure S ≤
      (Subgroup.closure S).comap (Matrix.GeneralLinearGroup.map σ.toRingHom) := by
    rw [Subgroup.closure_le]
    rintro x ⟨hdet, hx⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · change ((x : Matrix (Fin d) (Fin d) K).map σ).det = 1
      rw [show (x : Matrix (Fin d) (Fin d) K).map σ =
        (σ : K →+* K).mapMatrix (x : Matrix (Fin d) (Fin d) K) from rfl, ← RingHom.map_det, hdet,
        map_one]
    · change (((x : Matrix (Fin d) (Fin d) K).map σ).map (· ^ 2 ^ n))ᵀ *
        (x : Matrix (Fin d) (Fin d) K).map σ = 1
      have e : (((x : Matrix (Fin d) (Fin d) K).map σ).map (· ^ 2 ^ n))ᵀ *
          (x : Matrix (Fin d) (Fin d) K).map σ =
          ((((x : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ n))ᵀ *
            (x : Matrix (Fin d) (Fin d) K))).map σ := by
        ext i j
        simp [Matrix.mul_apply, map_sum]
      rw [e, hx, Matrix.map_one _ (map_zero σ) (map_one σ)]
  exact hle hg

theorem conj_mem_su {x : GL (Fin d) K} (hx : x ∈ CU h d) {g : GL (Fin d) K}
    (hg : g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n)) :
    x * g * x⁻¹ ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
  obtain ⟨μ, hμ⟩ := hx
  rw [mem_su_iff h] at hg ⊢
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, barT_mul_mul h, barT_mul_mul h, hμ, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, hg.1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    exact smul_barT_inv h hμ
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hg.2, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

theorem scalar_mem_cu (c : Kˣ) : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ CU h d := by
  refine ⟨h.norm c, ?_⟩
  have e := scalar_barTranspose_mul_mul h (1 : Matrix (Fin d) (Fin d) K) (c : K)
  rw [Matrix.mul_one] at e
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  exact e

theorem map_mem_cu (σ : K ≃+* K) {x : GL (Fin d) K} (hx : x ∈ CU h d) :
    Matrix.GeneralLinearGroup.map σ.toRingHom x ∈ CU h d := by
  obtain ⟨μ, hμ⟩ := hx
  refine ⟨σ μ, ?_⟩
  have e : ((((Matrix.GeneralLinearGroup.map σ.toRingHom x : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      ((Matrix.GeneralLinearGroup.map σ.toRingHom x : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K)) =
      ((((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (x : Matrix (Fin d) (Fin d) K))).map σ := by
    ext i j
    simp [Matrix.mul_apply, map_sum, UnitaryFieldData.bar_apply]
  rw [e, hμ]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem guSet_subset_cu : LargeEvenGUSet (Fin d) K (2 ^ n) ⊆ (CU h d : Set (GL (Fin d) K)) := by
  rintro A ⟨μ, -, -, hA⟩
  exact ⟨μ, hA⟩

theorem unitary_of_mem_cu_of_pow [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : (p : ℤ) ∣ 2 ^ n + 1) {x : GL (Fin d) K} (hx : x ∈ CU h d) (hxp : x ^ p = 1) :
    ((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (x : Matrix (Fin d) (Fin d) K) = 1 := by
  obtain ⟨μ, hμ⟩ := hx
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i₀⟩⟩
  · exact Matrix.ext fun i => isEmptyElim i
  have hbar : h.bar μ = μ := by
    have e1 : (((x : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (x : Matrix (Fin d) (Fin d) K))
        i₀ i₀ = μ := by
      rw [hμ]
      simp
    rw [← e1]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
      UnitaryFieldData.bar_bar]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hk : ∀ k : ℕ, (((x ^ k : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      ((x ^ k : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        μ ^ k • (1 : Matrix (Fin d) (Fin d) K) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, pow_zero, one_smul, Units.val_one,
        Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one, Matrix.one_mul]
    | succ k ih =>
      rw [pow_succ x k, Units.val_mul, barT_mul_mul h, ih, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hμ, smul_smul, ← pow_succ]
  have hpow : μ ^ p = 1 := by
    have e := hk p
    rw [hxp, Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
      Matrix.transpose_one, Matrix.one_mul] at e
    have e2 := congrFun (congrFun e i₀) i₀
    simpa using e2.symm
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hpow
    exact zero_ne_one hpow
  have hq : μ ^ (2 ^ n - 1) = 1 := by
    have e : μ ^ (2 ^ n - 1) * μ = 1 * μ := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, one_mul, ← h.bar_apply, hbar]
    exact mul_right_cancel₀ hμ0 e
  have hcop : Nat.Coprime p (2 ^ n - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have h1 : (p : ℤ) ∣ ((2 ^ n - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
    rw [Nat.cast_sub Nat.one_le_two_pow] at h1
    push_cast at h1
    have h2 : (p : ℤ) ∣ 2 := by
      have := dvd_sub hpq h1
      rwa [show ((2 : ℤ) ^ n + 1) - (2 ^ n - 1) = 2 by ring] at this
    have h3 : p ∣ 2 := by exact_mod_cast h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hμ1 : μ = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hpow, hq⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  rw [hμ, hμ1, one_smul]

private theorem exists_cover_of_sections [Finite K] {L : Type} [Group L] [Finite L]
    (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* LargeEvenSUGroup (Fin d) K (2 ^ n)),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : LargeEvenSUGroup (Fin d) K (2 ^ n) →* E, ∀ g, π (s g) = g) :
    ∃ π : LargeEvenSUGroup (Fin d) K (2 ^ n) →* L, Function.Surjective π ∧
      (∀ g ∈ π.ker, (g : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K) ∧
      ∀ g, θ (π g : L ⧸ Subgroup.center L) = LargeEvenProjMk _ g := by
  let ψ : L →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψ : ∀ l, ψ l = θ (l : L ⧸ Subgroup.center L) := fun _ => rfl
  have hψs : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker ≤ Subgroup.center L := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ] at hx
    exact (QuotientGroup.eq_one_iff x).mp (θ.injective (by rw [map_one]; exact hx))
  obtain ⟨φ, hφ⟩ := LineU.exists_hom_of_sections (LargeEvenProjMk _) ψ hψs hψker hsec
  refine ⟨φ, LineU.surjective_of_cover (LargeEvenProjMk _) (QuotientGroup.mk'_surjective _) ψ
    hψker hL φ hφ, fun g hg => ?_, fun g => (hψ _).symm.trans (hφ g)⟩
  have h1 : LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)) g = 1 := by
    rw [← hφ, MonoidHom.mem_ker.mp hg, map_one]
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff g).mp h1)

include h in
theorem exists_cover_unitary
    [Finite K] (hd : 3 ≤ d) (hn : 2 ≤ n) {L : Type} [Group L]
    [Finite L]
    (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :
    ∃ π : LargeEvenSUGroup (Fin d) K (2 ^ n) →* L, Function.Surjective π ∧
      (∀ g ∈ π.ker, (g : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K) ∧
      ∀ g, θ (π g : L ⧸ Subgroup.center L) = LargeEvenProjMk _ g := by
  have := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_cover_of_sections hL θ fun E _ _ π hπ hcen => ?_
  rcases Nat.even_or_odd d with he | ho
  · have hd4 : 4 ≤ d := by
      obtain ⟨r, hr⟩ := he
      omega
    have hq : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central
      (F := K) (p := 2) (f := n) h.card_eq_sq he hd4 hq hπ hcen
  · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
      (F := K) (p := 2) (f := n) h.card_eq_sq (by omega) hd (Nat.not_even_iff_odd.mpr ho)
      (pair_ne hn) hπ hcen

theorem exists_semilin_of_pElt [Finite K] (hd : 3 ≤ d) (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hα : GGL45IsPElt p α) :
    ∃ g ∈ CU h d, ∃ (σ : K ≃+* K) (m : ℕ), σ ^ p ^ m = 1 ∧
      ∀ a b : LargeEvenSUGroup (Fin d) K (2 ^ n),
        (b : GL (Fin d) K) = g * Matrix.GeneralLinearGroup.map σ.toRingHom a * g⁻¹ →
          α (LargeEvenProjMk _ a) = LargeEvenProjMk _ b := by
  obtain ⟨m, hm⟩ := hα
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, hsurj, -, -, -, happ, -, -, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (K := K) (n := d)) hd
      (not_three_two hn)
  set E := MulAut.congr (InndiagSU.projEquiv h hd1) with hE
  obtain ⟨⟨A, σ⟩, hAσ⟩ := hsurj (E α)
  rw [primeFormPsi_apply] at hAσ
  refine ⟨A, ⟨1, ?_⟩, σ, m, ?_, fun a b hab => ?_⟩
  · have hA := mem_primeFormUnitary.mp A.2
    change ((((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).map h.bar)ᵀ * 1 *
      ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 at hA
    rw [Matrix.mul_one] at hA
    rw [one_smul]
    exact hA
  ·
    have e1 := happ A σ
    rw [hAσ] at e1
    have e2 : primeFormFieldFactor h (isPrimeFormGram_one (K := K) (n := d)) hd
        (not_three_two hn) (E (α ^ p ^ m)) = σ ^ p ^ m := by
      rw [map_pow, map_pow, e1]
    rw [hm, map_one, map_one] at e2
    exact e2.symm
  · apply (InndiagSU.projEquiv h hd1).injective
    have e1 : InndiagSU.projEquiv h hd1 (α (LargeEvenProjMk _ a)) =
        E α (InndiagSU.projEquiv h hd1 (LargeEvenProjMk _ a)) := by
      rw [hE, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [e1, ← hAσ, MulAut.mul_apply, projMk_eq h hd1, projMk_eq h hd1]
    change primeFormConjHom h _ A (primeFormFieldAut h _ σ _) = _
    rw [primeFormFieldAut_mk, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (A : GL (Fin d) K) * glAut σ (a : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹ = b
    rw [hab, glAut_eq_map]

include h in
theorem eq_one_of_field_eq_one [Finite K] (hd : 3 ≤ d) (hn : 2 ≤ n) {σ : K ≃+* K}
    (hσ : ∀ a b : LargeEvenSUGroup (Fin d) K (2 ^ n),
      (b : GL (Fin d) K) = Matrix.GeneralLinearGroup.map σ.toRingHom a →
        LargeEvenProjMk _ a = LargeEvenProjMk _ b) : σ = 1 := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, -, -, -, -, happ, -, -, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (K := K) (n := d)) hd
      (not_three_two hn)
  have hf : primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ = 1 := by
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun s => ?_
    rw [MulAut.one_apply]
    change primeFormFieldAut h _ σ
      (s : primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = _
    rw [primeFormFieldAut_mk]
    have hs : (s : GL (Fin d) K) ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) :=
      (InndiagSU.largeEvenSUGroup_eq_gramSU (d := d) h).symm ▸ s.2
    have hs' : glAut σ (s : GL (Fin d) K) ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) :=
      (InndiagSU.largeEvenSUGroup_eq_gramSU (d := d) h).symm ▸
        glAut_mem_gramSU h (isPrimeFormGram_one (K := K) (n := d)) σ s.2
    have e := congrArg (InndiagSU.projEquiv h hd1)
      (hσ ⟨s, hs⟩ ⟨_, hs'⟩ (glAut_eq_map σ (s : GL (Fin d) K)))
    rw [projMk_eq h hd1, projMk_eq h hd1] at e
    exact e.symm
  have e := happ 1 σ
  rw [map_one, one_mul, hf, map_one] at e
  exact e.symm

end CFSG.StandardType.GGL45TG.SU
