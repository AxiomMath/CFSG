module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofL3Aut
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open scoped MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

section Action

variable {G : Type*} [Group G] (L : Subgroup G)

theorem conj_mem_of_mem_normalizer (x : Subgroup.normalizer (L : Set G)) (l : L) :
    (x : G) * l * (x : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp x.2 l).mp l.2

@[expose] noncomputable def barAut :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ CFSG.pCore 2 L) :=
  ({ toFun := fun σ => QuotientGroup.congr (CFSG.pCore 2 L) (CFSG.pCore 2 L) σ
        (CFSG.pCore_map_iso 2 σ)
     map_one' := by
       ext y
       induction y using QuotientGroup.induction_on with
       | H y => rfl
     map_mul' := fun σ τ => by
       ext y
       induction y using QuotientGroup.induction_on with
       | H y => rfl } : MulAut L →* MulAut (L ⧸ CFSG.pCore 2 L)).comp L.normalizerMonoidHom

theorem barAut_mk (x : Subgroup.normalizer (L : Set G)) (l : L) :
    barAut L x (l : L ⧸ CFSG.pCore 2 L) =
      ((⟨(x : G) * l * (x : G)⁻¹, conj_mem_of_mem_normalizer L x l⟩ : L) :
        L ⧸ CFSG.pCore 2 L) :=
  rfl

variable {L} {n : ℕ}
  (φ : L ⧸ CFSG.pCore 2 L ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))

@[expose] noncomputable def psi : L →* projectiveSL 3 (GaloisField 2 n) :=
  ((φ.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _)).toMonoidHom).comp
    (QuotientGroup.mk' _)

@[expose] noncomputable def rho :
    Subgroup.normalizer (L : Set G) →* MulAut (projectiveSL 3 (GaloisField 2 n)) :=
  (MulAut.congr (φ.trans
    (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _))).toMonoidHom.comp (barAut L)

theorem rho_psi (x : Subgroup.normalizer (L : Set G)) (l : L) :
    rho φ x (psi φ l) = psi φ ⟨(x : G) * l * (x : G)⁻¹, conj_mem_of_mem_normalizer L x l⟩ := by
  simp [rho, psi, MulAut.congr_apply, barAut_mk]

theorem psi_surjective : Function.Surjective (psi φ) :=
  (φ.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _)).surjective.comp
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 L))

theorem psi_eq_one_iff (l : L) : psi φ l = 1 ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 L := by
  have h1 : psi φ l = 1 ↔ (l : L ⧸ CFSG.pCore 2 L) = 1 :=
    (φ.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _)).map_eq_one_iff
  rw [h1, QuotientGroup.eq_one_iff, CFSG.Open.pCoreOf, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨l, h, rfl⟩
  · rintro ⟨y, hy, hyl⟩
    exact (Subtype.ext hyl : y = l) ▸ hy

theorem rho_eq_conj (x : Subgroup.normalizer (L : Set G)) (l : L) (hxl : (x : G) = l) :
    rho φ x = MulAut.conj (psi φ l) := by
  ext p
  obtain ⟨m, rfl⟩ := psi_surjective φ p
  rw [rho_psi, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by simp [hxl])

theorem rho_eq_one_iff (x : Subgroup.normalizer (L : Set G)) :
    rho φ x = 1 ↔ ∀ l ∈ L, (x : G) * l * (x : G)⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  constructor
  · intro h l hl
    have h1 := rho_psi φ x ⟨l, hl⟩
    rw [h, MulAut.one_apply, eq_comm, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      psi_eq_one_iff] at h1
    simpa using h1
  · intro h
    ext p
    obtain ⟨m, rfl⟩ := psi_surjective φ p
    rw [rho_psi, MulAut.one_apply, ← mul_inv_eq_one, ← map_inv, ← map_mul, psi_eq_one_iff]
    simpa using h m m.2

theorem exists_lift {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (p : projectiveSL 3 (GaloisField 2 n))
    (hp : p ^ r = 1) : ∃ y : L, psi φ y = p ∧ y ^ r = 1 := by
  obtain ⟨y₁, rfl⟩ := psi_surjective φ p
  have hker : y₁ ^ r ∈ CFSG.pCore 2 L := by
    have h1 : psi φ (y₁ ^ r) = 1 := by rw [map_pow, hp]
    have h2 := (psi_eq_one_iff φ (y₁ ^ r)).mp h1
    rw [CFSG.Open.pCoreOf, Subgroup.mem_map] at h2
    obtain ⟨y, hy, hyl⟩ := h2
    exact (Subtype.ext hyl : y = y₁ ^ r) ▸ hy
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)) ⟨_, hker⟩
  have hm' : (y₁ ^ r) ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hcop : Nat.Coprime (2 ^ m) r :=
    Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  refine ⟨y₁ ^ (2 ^ m * u), ?_, ?_⟩
  · rw [map_pow, ← Nat.mod_add_div (2 ^ m * u) r, hu, pow_add, pow_mul, hp, one_pow, mul_one,
      pow_one]
  · calc (y₁ ^ (2 ^ m * u)) ^ r = ((y₁ ^ r) ^ 2 ^ m) ^ u := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [hm', one_pow]

end Action

section Model

variable {n : ℕ}

private theorem eq_one_of_pow_three_eq_one (hn : Odd n) {c : (GaloisField 2 n)ˣ}
    (hc : c ^ 3 = 1) : c = 1 := by
  have hn0 : n ≠ 0 := by
    obtain ⟨k, rfl⟩ := hn
    omega
  classical
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
      GaloisField.card 2 n hn0]
  have hcop : (Nat.card (GaloisField 2 n)ˣ).Coprime 3 := by
    rw [hcard]
    exact CFSG.RankThree.PartTwo.Sec20.Res7.coprime_two_pow_sub_one_three hn
  exact (powCoprime hcop).injective (by simpa using hc)

theorem proj_injective_of_odd (hn : Odd n) :
    Function.Injective (proj 3 (GaloisField 2 n)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, eq_bot_iff]
  rintro g ⟨c, hc3, hgc⟩
  have hc1 := eq_one_of_pow_three_eq_one hn hc3
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [hgc, hc1]; simp)

theorem center_projectiveSL_eq_bot :
    Subgroup.center (projectiveSL 3 (GaloisField 2 n)) = ⊥ :=
  CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot le_rfl

theorem conjAut_mul_dualAut_proj (A : GL (Fin 3) (GaloisField 2 n))
    (g : SL(3, GaloisField 2 n)) :
    (conjAut 3 (GaloisField 2 n) A * dualAut 3 (GaloisField 2 n)) (proj 3 _ g) =
      proj 3 _ (CatalogueBHigherLinearAction.slConjugation 3 _ A
        (CatalogueBGraphForm.slGraphAut 3 _ g)) := by
  rw [MulAut.mul_apply]
  change conjAut 3 _ A (descendAut 3 _ (CatalogueBGraphForm.slGraphAut 3 _) (proj 3 _ g)) = _
  rw [descendAut_proj, conjAut_proj]

end Model

section Outer

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ}
  (φ : L ⧸ CFSG.pCore 2 L ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))

theorem exists_conj_eq_conjAut (hn : Odd n) (A : GL (Fin 3) (GaloisField 2 n)) :
    ∃ l : L, MulAut.conj (psi φ l) = conjAut 3 (GaloisField 2 n) A := by
  obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.Sec20.Res7.exists_conj_eq_conjAut_of_cube A
    (CFSG.RankThree.PartTwo.Sec20.Res7.exists_cube_galoisField hn)
  obtain ⟨l, rfl⟩ := psi_surjective φ y
  exact ⟨l, hy.symm⟩

theorem rho_eq_conjAut_mul_dualAut (hn : Odd n) (x : Subgroup.normalizer (L : Set G))
    (h2 : ∃ a : ℕ, (rho φ x) ^ 2 ^ a = 1)
    (hout : ∀ l : L, rho φ x ≠ MulAut.conj (psi φ l)) :
    ∃ A : GL (Fin 3) (GaloisField 2 n),
      rho φ x = conjAut 3 (GaloisField 2 n) A * dualAut 3 (GaloisField 2 n) := by
  classical
  obtain ⟨a, ha⟩ := h2
  set F := GaloisField 2 n with hF
  set β : MulAut (projectiveSL 3 F) := rho φ x with hβ
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have hδδ : dualAut 3 F * dualAut 3 F = 1 := htrans.2.2.2.1
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hβeq⟩ := hform β
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hβeq
    obtain ⟨B, hB⟩ :=
      CFSG.RankThree.PartTwo.Sec20.Res7.exists_pow_conjAut_mul_fieldAut A σ (2 ^ a)
    rw [← hβeq, ha] at hB
    obtain ⟨hσ1, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) B (σ ^ 2 ^ a) hB.symm
    have hσ : σ = 1 := CFSG.RankThree.PartTwo.Sec20.Res7.eq_one_of_pow_two_pow_eq_one hn hσ1
    rw [hσ, map_one, mul_one] at hβeq
    obtain ⟨l, hl⟩ := exists_conj_eq_conjAut φ hn A
    exact absurd (hβeq.trans hl.symm) (hout l)
  ·
    rw [pow_one] at hβeq
    have hsq : β ^ 2 = conjAut 3 F (A * GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose A)) * fieldAut 3 F (σ * σ) := by
      rw [← conjAut_mul_fieldAut_mul]
      have h1 : β ^ 2 = conjAut 3 F A * fieldAut 3 F σ * (dualAut 3 F * conjAut 3 F A *
          dualAut 3 F * (dualAut 3 F * fieldAut 3 F σ * dualAut 3 F)) := by
        rw [hβeq, pow_two]
        calc _ = conjAut 3 F A * fieldAut 3 F σ * (dualAut 3 F * conjAut 3 F A *
              fieldAut 3 F σ * dualAut 3 F) := by group
          _ = conjAut 3 F A * fieldAut 3 F σ * (dualAut 3 F * conjAut 3 F A *
              (dualAut 3 F * dualAut 3 F) * fieldAut 3 F σ * dualAut 3 F) := by
            rw [hδδ]
            group
          _ = _ := by group
      rw [h1, htrans.2.2.2.2.1, htrans.2.2.2.2.2.1]
    have hpow : β ^ 2 ^ (a + 1) = 1 := by
      rw [pow_succ, pow_mul, ha, one_pow]
    obtain ⟨B, hB⟩ := CFSG.RankThree.PartTwo.Sec20.Res7.exists_pow_conjAut_mul_fieldAut
      (A * GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.inverseTranspose A))
      (σ * σ) (2 ^ a)
    rw [← hsq, ← pow_mul, ← pow_succ', hpow] at hB
    obtain ⟨hσ1, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) B _ hB.symm
    have hσ : σ = 1 := by
      refine CFSG.RankThree.PartTwo.Sec20.Res7.eq_one_of_pow_two_pow_eq_one hn (a := a + 1) ?_
      rw [pow_succ', pow_mul, pow_two]
      exact hσ1
    exact ⟨A, by rw [hβeq, hσ, map_one, mul_one]⟩

private theorem exists_symm_of_sq_eq_one_aux {F : Type*} [Field F] [Finite F]
    (hcube : ∀ c : Fˣ, c ^ 3 = 1 → c = 1) (A : GL (Fin 3) F)
    (h2 : (conjAut 3 F A * dualAut 3 F) ^ 2 = 1) :
    ∃ B : GL (Fin 3) F, (B : Matrix (Fin 3) (Fin 3) F)ᵀ = B ∧
      conjAut 3 F A * dualAut 3 F = conjAut 3 F B * dualAut 3 F := by
  classical
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have hsq : conjAut 3 F (A * GeneralLinearGroup.inverseTranspose A) * fieldAut 3 F 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← htrans.2.2.2.2.1, ← h2, pow_two]
    group
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ 1 hsq
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F, M = A := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 3) (Fin 3) F, N = ((A⁻¹ : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
  have hMN : M * N = 1 := by
    rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 := congrArg (fun X : GL (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F)) hc
  simp only [GeneralLinearGroup.coe_scalar, Units.val_mul,
    GeneralLinearGroup.coe_inverseTranspose] at h1
  rw [← hM, ← hN] at h1
  have hAT : M = (c : F) • Mᵀ := by
    calc M = M * (M * N)ᵀ := by rw [hMN, transpose_one, mul_one]
      _ = (M * Nᵀ) * Mᵀ := by rw [transpose_mul, ← mul_assoc]
      _ = (c : F) • Mᵀ := by
        rw [← h1, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hdet : M.det = (c : F) ^ 3 * M.det := by
    conv_lhs => rw [hAT]
    rw [Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  have hdet0 : M.det ≠ 0 := by
    rw [hM, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hc3 : (c : F) ^ 3 = 1 :=
    mul_right_cancel₀ hdet0 (hdet.symm.trans (one_mul _).symm)
  have hc1 : c = 1 := hcube c (Units.ext (by rw [Units.val_pow_eq_pow_val, hc3, Units.val_one]))
  rw [hc1, Units.val_one, one_smul] at hAT
  refine ⟨A, ?_, rfl⟩
  rw [← hM]
  exact hAT.symm

theorem exists_symm_of_sq_eq_one (hn : Odd n) (A : GL (Fin 3) (GaloisField 2 n))
    (h2 : (conjAut 3 (GaloisField 2 n) A * dualAut 3 (GaloisField 2 n)) ^ 2 = 1) :
    ∃ B : GL (Fin 3) (GaloisField 2 n), (B : Matrix (Fin 3) (Fin 3) (GaloisField 2 n))ᵀ = B ∧
      conjAut 3 (GaloisField 2 n) A * dualAut 3 (GaloisField 2 n) =
        conjAut 3 (GaloisField 2 n) B * dualAut 3 (GaloisField 2 n) :=
  exists_symm_of_sq_eq_one_aux (fun _ hc => eq_one_of_pow_three_eq_one hn hc) A h2

end Outer

end CFSG.RankThree.PartTwo.Sec3.Sims321
