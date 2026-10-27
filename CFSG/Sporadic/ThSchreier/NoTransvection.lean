
module

public import CFSG.Sporadic.ThSchreier.NoTransvectionBase1

public import CFSG.Sporadic.ThSchreier.AutCore
public meta import CFSG.Sporadic.ThSchreier.Rigidity
public import CFSG.Sporadic.ThSchreier.NoTransvectionInputs
public import Certificates.Certificate2314
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates Equiv Equiv.Perm Matrix

theorem dtCols_eq : posWord8 B1enc B2enc dtWord = dtCols :=
  Certificates.certificate2314

theorem mat8_dtCols : mat8 dtCols = posWord B1 B2 dtWord := by
  rw [← dtCols_eq, mat8_posWord8, mat8_B1enc, mat8_B2enc]


@[expose] def dtPerm : Perm (Fin 9) := Equiv.swap 0 1 * Equiv.swap 2 3

theorem dtWord_perm : posWord aPerm bPerm dtWord = dtPerm := by decide

theorem cycleType_involution_alt9 {σ : Perm (Fin 9)} (hs : sign σ = 1) (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 ∧
      (Multiset.card σ.cycleType = 2 ∨ Multiset.card σ.cycleType = 4) := by
  have htypes : ∀ n ∈ σ.cycleType, n = 2 := pow_prime_eq_one_iff.mp h2
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.2 htypes
  refine ⟨hrep, ?_⟩
  have hsupport := σ.support.card_le_univ
  rw [← sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul] at hsupport
  simp only [Fintype.card_fin] at hsupport
  have hsign := hs
  rw [sign_of_cycleType, hrep] at hsign
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have hne : Multiset.card σ.cycleType ≠ 0 := by
    intro h0
    exact h1 (card_cycleType_eq_zero.mp h0)
  have hev : Even (Multiset.card σ.cycleType) := by
    rcases Nat.even_or_odd (Multiset.card σ.cycleType) with he | ho
    · exact he
    · exfalso
      obtain ⟨k, hk⟩ := ho
      rw [hk] at hsign
      simp [pow_add, pow_mul] at hsign
  obtain ⟨k, hk⟩ := hev
  omega

theorem sign_swap01 : sign (Equiv.swap (0 : Fin 9) 1) = -1 := by decide

theorem exists_even_conj {σ τ : Perm (Fin 9)} (h : IsConj σ τ)
    (hτ : Equiv.swap (0 : Fin 9) 1 * τ * (Equiv.swap (0 : Fin 9) 1)⁻¹ = τ) :
    ∃ π : Perm (Fin 9), sign π = 1 ∧ π * σ * π⁻¹ = τ := by
  obtain ⟨π, hπ⟩ := isConj_iff.1 h
  rcases Int.units_eq_one_or (sign π) with hs | hs
  · exact ⟨π, hs, hπ⟩
  · refine ⟨Equiv.swap 0 1 * π, ?_, ?_⟩
    · rw [Equiv.Perm.sign_mul, sign_swap01, hs]
      rfl
    · rw [← hτ, ← hπ]
      group

theorem involution_conj_alt9 {σ : Perm (Fin 9)} (hs : sign σ = 1) (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) :
    ∃ π : Perm (Fin 9), sign π = 1 ∧ (π * σ * π⁻¹ = aPerm ∨ π * σ * π⁻¹ = dtPerm) := by
  obtain ⟨hrep, hcard⟩ := cycleType_involution_alt9 hs h2 h1
  obtain ⟨hrepA, hcardA⟩ := cycleType_involution_alt9 (σ := aPerm) (by decide) (by decide)
    (by decide)
  obtain ⟨hrepD, hcardD⟩ := cycleType_involution_alt9 (σ := dtPerm) (by decide) (by decide)
    (by decide)
  have hsuppA : aPerm.support.card = 8 := by decide
  have hsuppD : dtPerm.support.card = 4 := by decide
  have hA4 : Multiset.card aPerm.cycleType = 4 := by
    have h := sum_cycleType aPerm
    rw [hrepA, Multiset.sum_replicate, smul_eq_mul, hsuppA] at h
    omega
  have hD2 : Multiset.card dtPerm.cycleType = 2 := by
    have h := sum_cycleType dtPerm
    rw [hrepD, Multiset.sum_replicate, smul_eq_mul, hsuppD] at h
    omega
  rcases hcard with h | h
  · obtain ⟨π, hπ, he⟩ := exists_even_conj (τ := dtPerm)
      (isConj_iff_cycleType_eq.2 (by rw [hrep, hrepD, h, hD2])) (by decide)
    exact ⟨π, hπ, Or.inr he⟩
  · obtain ⟨π, hπ, he⟩ := exists_even_conj (τ := aPerm)
      (isConj_iff_cycleType_eq.2 (by rw [hrep, hrepA, h, hA4])) (by decide)
    exact ⟨π, hπ, Or.inl he⟩

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := ExtraspecialNF.zmod_two_cases c

theorem exists_eq_one_of_ne_zero {ℓ : Fin 8 → ZMod 2} (hℓ : ℓ ≠ 0) : ∃ j, ℓ j = 1 := by
  by_contra h
  apply hℓ
  funext j
  rcases zmod2_cases (ℓ j) with h0 | h1
  · exact h0
  · exact absurd ⟨j, h1⟩ h

theorem fix_kernel_sub {X : Matrix (Fin 8) (Fin 8) (ZMod 2)} {ℓ : Fin 8 → ZMod 2} {j₀ : Fin 8}
    (hj : ℓ j₀ = 1) (h : ∀ v, ℓ ⬝ᵥ v = 0 → X *ᵥ v = v) (v : Fin 8 → ZMod 2) :
    X *ᵥ v - v = (ℓ ⬝ᵥ v) • (X *ᵥ Pi.single j₀ 1 - Pi.single j₀ 1) := by
  set c := ℓ ⬝ᵥ v
  have hk : ℓ ⬝ᵥ (v - c • Pi.single j₀ 1) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_single_one, hj, smul_eq_mul, mul_one, sub_self]
  have hX := h _ hk
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul] at hX
  rw [smul_sub]
  calc X *ᵥ v - v = (X *ᵥ v - c • X *ᵥ Pi.single j₀ 1) + c • X *ᵥ Pi.single j₀ 1 - v := by abel
    _ = (v - c • Pi.single j₀ 1) + c • X *ᵥ Pi.single j₀ 1 - v := by rw [hX]
    _ = c • X *ᵥ Pi.single j₀ 1 - c • Pi.single j₀ 1 := by abel

theorem cols_eq_of_fix_kernel {X : Matrix (Fin 8) (Fin 8) (ZMod 2)} {ℓ : Fin 8 → ZMod 2}
    (hℓ : ℓ ≠ 0) (h : ∀ v, ℓ ⬝ᵥ v = 0 → X *ᵥ v = v) {u w : Fin 8 → ZMod 2}
    (hu : X *ᵥ u - u ≠ 0) (hw : X *ᵥ w - w ≠ 0) : X *ᵥ u - u = X *ᵥ w - w := by
  obtain ⟨j₀, hj⟩ := exists_eq_one_of_ne_zero hℓ
  rw [fix_kernel_sub hj h u] at hu ⊢
  rw [fix_kernel_sub hj h w] at hw ⊢
  rcases zmod2_cases (ℓ ⬝ᵥ u) with h0 | h1
  · exact absurd (by rw [h0, zero_smul]) hu
  rcases zmod2_cases (ℓ ⬝ᵥ w) with h0' | h1'
  · exact absurd (by rw [h0', zero_smul]) hw
  rw [h1, h1']

theorem matrix_ext8 {A B : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h v)

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by revert c; decide

theorem sq_eq_one_of_fix_kernel {X Y : Matrix (Fin 8) (Fin 8) (ZMod 2)} (hXY : X * Y = 1)
    {ℓ : Fin 8 → ZMod 2} (hℓ : ℓ ≠ 0) (h : ∀ v, ℓ ⬝ᵥ v = 0 → X *ᵥ v = v) : X * X = 1 := by
  obtain ⟨j₀, hj⟩ := exists_eq_one_of_ne_zero hℓ
  have hYX : Y * X = 1 := mul_eq_one_comm.1 hXY
  set d := X *ᵥ Pi.single j₀ 1 - Pi.single j₀ 1 with hd
  have hX : ∀ v, X *ᵥ v = v + (ℓ ⬝ᵥ v) • d := fun v => by
    rw [← fix_kernel_sub hj h v]
    abel
  have hd0 : ℓ ⬝ᵥ d = 0 := by
    rcases zmod2_cases (ℓ ⬝ᵥ d) with h0 | h1
    · exact h0
    · exfalso
      have hXd : X *ᵥ d = 0 := by
        rw [hX d, h1, one_smul]
        funext i
        exact zmod2_add_self _
      have hd' : d = 0 := by
        have e := congrArg (fun v => Y *ᵥ v) hXd
        simp only [Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec, Matrix.mulVec_zero] at e
        exact e
      rw [hd', dotProduct_zero] at h1
      exact zero_ne_one h1
  apply matrix_ext8
  intro v
  rw [← Matrix.mulVec_mulVec, hX (X *ᵥ v), hX v, dotProduct_add, dotProduct_smul, hd0,
    smul_eq_mul, mul_zero, add_zero, add_assoc, ← add_smul, zmod2_add_self, zero_smul, add_zero,
    Matrix.one_mulVec]

theorem not_fix_kernel {X : Matrix (Fin 8) (Fin 8) (ZMod 2)} {u w : Fin 8 → ZMod 2}
    (hu : X *ᵥ u - u ≠ 0) (hw : X *ᵥ w - w ≠ 0) (huw : X *ᵥ u - u ≠ X *ᵥ w - w)
    {ℓ : Fin 8 → ZMod 2} (hℓ : ℓ ≠ 0) : ¬ ∀ v, ℓ ⬝ᵥ v = 0 → X *ᵥ v = v :=
  fun h => huw (cols_eq_of_fix_kernel hℓ h hu hw)

theorem B1_cols : B1 *ᵥ Pi.single 0 1 - Pi.single 0 1 ≠ 0 ∧
    B1 *ᵥ Pi.single 2 1 - Pi.single 2 1 ≠ 0 ∧
    B1 *ᵥ Pi.single 0 1 - Pi.single 0 1 ≠ B1 *ᵥ Pi.single 2 1 - Pi.single 2 1 := by
  rw [← mat8_B1enc]
  decide

theorem D_cols : mat8 dtCols *ᵥ Pi.single 0 1 - Pi.single 0 1 ≠ 0 ∧
    mat8 dtCols *ᵥ Pi.single 1 1 - Pi.single 1 1 ≠ 0 ∧
    mat8 dtCols *ᵥ Pi.single 0 1 - Pi.single 0 1 ≠
      mat8 dtCols *ᵥ Pi.single 1 1 - Pi.single 1 1 := by
  decide

theorem fix_kernel_conj {T P Pi : Matrix (Fin 8) (Fin 8) (ZMod 2)} (hP : P * Pi = 1)
    {ℓ : Fin 8 → ZMod 2} (hℓ : ℓ ≠ 0) (h : ∀ v, ℓ ⬝ᵥ v = 0 → T *ᵥ v = v) :
    ℓ ᵥ* Pi ≠ 0 ∧ ∀ w, (ℓ ᵥ* Pi) ⬝ᵥ w = 0 → (P * T * Pi) *ᵥ w = w := by
  have hPiP : Pi * P = 1 := mul_eq_one_comm.1 hP
  refine ⟨fun h0 => hℓ ?_, fun w hw => ?_⟩
  · have e := congrArg (fun u => u ᵥ* P) h0
    simp only [Matrix.vecMul_vecMul, hPiP, Matrix.vecMul_one, Matrix.zero_vecMul] at e
    exact e
  · rw [← Matrix.dotProduct_mulVec] at hw
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h _ hw, Matrix.mulVec_mulVec, hP,
      Matrix.one_mulVec]

namespace AutCore.Data

variable {G : Type*} [Group G] (D : Data G)

theorem ρ_mul_inv (m : G) : D.ρ m * D.ρ m⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]

theorem rho_eq_one_of_fix (m : G) {ℓ : Fin 8 → ZMod 2} (hℓ : ℓ ≠ 0)
    (h : ∀ v, ℓ ⬝ᵥ v = 0 → D.ρ m *ᵥ v = v) : D.ρ m = 1 := by
  by_contra hne
  have hsq : D.ρ m * D.ρ m = 1 := sq_eq_one_of_fix_kernel (D.ρ_mul_inv m) hℓ h
  have hm2 : m * m ∈ D.Q := (D.ρQ _).1 (by rw [map_mul, hsq])
  have hmQ : m ∉ D.Q := fun hm => hne ((D.ρQ m).2 hm)
  have hσs : sign (D.κPerm m) = 1 :=
    Equiv.Perm.mem_alternatingGroup.1 (D.κ (QuotientGroup.mk m)).2
  have hσ2 : D.κPerm m ^ 2 = 1 := by
    rw [sq, ← map_mul, κPerm_apply]
    have e : (QuotientGroup.mk (m * m) : G ⧸ D.Q) = 1 := (QuotientGroup.eq_one_iff _).2 hm2
    rw [e, map_one]
    rfl
  have hσ1 : D.κPerm m ≠ 1 := by
    intro e
    apply hmQ
    have e' : D.κ (QuotientGroup.mk m) = 1 := Subtype.ext (by rw [← κPerm_apply, e]; rfl)
    rw [map_eq_one_iff _ D.κ.injective, QuotientGroup.eq_one_iff] at e'
    exact e'
  obtain ⟨π, hπ, hτ⟩ := involution_conj_alt9 hσs hσ2 hσ1
  obtain ⟨n, hn⟩ := D.exists_κ_eq ⟨π, Equiv.Perm.mem_alternatingGroup.2 hπ⟩
  have hκ : D.κPerm (n * m * n⁻¹) = π * D.κPerm m * π⁻¹ := by
    rw [map_mul, map_mul, map_inv, D.κPerm_apply n, hn]
  have hρ : D.ρ (n * m * n⁻¹) = D.ρ n * D.ρ m * D.ρ n⁻¹ := by rw [map_mul, map_mul]
  obtain ⟨hℓ', hfix⟩ := fix_kernel_conj (D.ρ_mul_inv n) hℓ h
  rw [← hρ] at hfix
  rcases hτ with hτ | hτ
  · have hx : D.ρ (n * m * n⁻¹) = B1 := by
      rw [D.ρ_eq_of_κ_eq (n := D.x) (Subtype.ext (by rw [← κPerm_apply, hκ, hτ, D.κx])), D.ρx]
    rw [hx] at hfix
    exact not_fix_kernel B1_cols.1 B1_cols.2.1 B1_cols.2.2 hℓ' hfix
  · have hw : D.ρ (n * m * n⁻¹) = mat8 dtCols := by
      rw [D.ρ_eq_of_κ_eq (n := posWord D.x D.y dtWord)
        (Subtype.ext (by rw [← κPerm_apply, hκ, hτ, D.κ_posWord, dtWord_perm])), map_posWord,
        D.ρx, D.ρy, mat8_dtCols]
    rw [hw] at hfix
    exact not_fix_kernel D_cols.1 D_cols.2.1 D_cols.2.2 hℓ' hfix

end AutCore.Data

end CFSG.Sporadic.ThSchreier
