module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel

public section

namespace CFSG.StandardType.LineU

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {n d : ℕ}

theorem exists_not_mem_two {d : ℕ} (hd : 3 ≤ d) (i j : Fin d) : ∃ k : Fin d, k ≠ i ∧ k ≠ j := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {i, j} := by
    intro x _
    by_cases hx : x = i
    · simp [hx]
    · simp [h x hx]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ({i, j} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
  omega

theorem exists_not_mem_three {d : ℕ} (hd : 4 ≤ d) (i j m : Fin d) :
    ∃ x : Fin d, x ≠ i ∧ x ≠ j ∧ x ≠ m := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {i, j, m} := by
    intro x _
    by_cases hx : x = i
    · simp [hx]
    · by_cases hy : x = j
      · simp [hy]
      · simp [h x hx hy]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ({i, j, m} : Finset (Fin d)).card ≤ 3 := Finset.card_le_three
  omega

theorem diag_ne_zero_of_eq {D : GL (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (k : Fin d) : t k ≠ 0 := by
  intro hk
  have h1 := D.isUnit.map (Matrix.detMonoidHom (n := Fin d) (R := K))
  rw [Matrix.coe_detMonoidHom, hD, det_diagonal, Finset.prod_eq_zero (Finset.mem_univ k) hk] at h1
  exact not_isUnit_zero h1

theorem coe_inv_diag {D : GL (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) :
    ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun k => (t k)⁻¹) := by
  rw [Matrix.coe_units_inv, hD]
  apply Matrix.inv_eq_left_inv
  rw [diagonal_mul_diagonal]
  have h1 : (fun k => (t k)⁻¹ * t k) = fun _ => (1 : K) :=
    funext fun k => inv_mul_cancel₀ (diag_ne_zero_of_eq hD k)
  rw [h1]
  exact Matrix.diagonal_one

@[expose] def conjN (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (s : ↥(unitarySU 2 n K d)) : ↥(unitarySU 2 n K d) :=
  ⟨D * s * D⁻¹, (Subgroup.mem_normalizer_iff.mp hD (s : GL (Fin d) K)).mp s.2⟩

theorem coe_conjN (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (s : ↥(unitarySU 2 n K d)) :
    ((conjN D hD s : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = D * s * D⁻¹ :=
  rfl

@[expose] def ActsDiagU {L' : Type} [Group L'] (φ : ↥(unitarySU 2 n K d) →* L') (a : MulAut L')
    (t : Fin d → K) : Prop :=
  ∃ (D : GL (Fin d) K) (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
    (D : Matrix (Fin d) (Fin d) K) = diagonal t ∧
      ∀ s : ↥(unitarySU 2 n K d), a (φ s) = φ (conjN D hD s)

theorem actsDiagU_one {L' : Type} [Group L'] (φ : ↥(unitarySU 2 n K d) →* L') :
    ActsDiagU φ 1 (fun _ => (1 : K)) := by
  have hD : (1 : GL (Fin d) K) ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.one_mem _
  refine ⟨1, hD, ?_, fun s => ?_⟩
  · rw [Units.val_one, ← Matrix.diagonal_one]
  · have e : conjN 1 hD s = s := Subtype.ext (by rw [coe_conjN]; simp)
    rw [e, MulAut.one_apply]

theorem ActsDiagU.ne_zero {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} {a : MulAut L'}
    {t : Fin d → K} (ha : ActsDiagU φ a t) (k : Fin d) : t k ≠ 0 := by
  obtain ⟨D, -, hDt, -⟩ := ha
  exact diag_ne_zero_of_eq hDt k

theorem ActsDiagU.pow {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} {a : MulAut L'}
    {t : Fin d → K} (ha : ActsDiagU φ a t) (m : ℕ) : ActsDiagU φ (a ^ m) (fun k => t k ^ m) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  have claim : ∀ j : ℕ, ∀ (s s' : ↥(unitarySU 2 n K d)),
      (s' : GL (Fin d) K) = D ^ j * s * (D ^ j)⁻¹ → (a ^ j) (φ s) = φ s' := by
    intro j
    induction j with
    | zero =>
      intro s s' hs
      have e : s' = s := Subtype.ext (by rw [hs]; simp)
      rw [e, pow_zero, MulAut.one_apply]
    | succ j ih =>
      intro s s' hs
      rw [pow_succ, MulAut.mul_apply, hact s]
      refine ih _ s' ?_
      rw [hs, coe_conjN, pow_succ]
      group
  refine ⟨D ^ m, pow_mem hD m, ?_, fun s => claim m s _ rfl⟩
  rw [Units.val_pow_eq_pow_val, hDt, diagonal_pow]
  rfl

theorem coe_permGL_matrix (σ : Equiv.Perm (Fin d)) :
    ((CFSG.RankThree.Classical.permGL σ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      σ⁻¹.permMatrix K := by
  rw [CFSG.RankThree.Classical.permGL, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply]

theorem coe_permGL_inv_matrix (σ : Equiv.Perm (Fin d)) :
    (((CFSG.RankThree.Classical.permGL σ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      σ.permMatrix K := by
  rw [← map_inv CFSG.RankThree.Classical.permGL σ, coe_permGL_matrix, inv_inv]

theorem permMatrix_conj_diag (σ : Equiv.Perm (Fin d)) (t : Fin d → K) :
    σ⁻¹.permMatrix K * diagonal t * σ.permMatrix K = diagonal (fun k => t (σ⁻¹ k)) := by
  have h := CFSG.StandardType.TypeANbrDvd.permMatrix_mul_diagonal_mul_inv σ⁻¹ t
  rw [inv_inv] at h
  exact h

theorem permGL_mem_unitarySU (hK : UnitaryFieldData 2 n K) (σ : Equiv.Perm (Fin d)) :
    CFSG.RankThree.Classical.permGL σ ∈ unitarySU 2 n K d := by
  have hc : CharP K 2 := hK.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [mem_unitarySU_iff hK]
  refine ⟨?_, CFSG.RankThree.Classical2.permGL_unitary hK σ⟩
  rw [coe_permGL_matrix, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simp [h]
    linear_combination -h2

@[expose] noncomputable def permSU (hK : UnitaryFieldData 2 n K) (σ : Equiv.Perm (Fin d)) :
    ↥(unitarySU 2 n K d) :=
  ⟨CFSG.RankThree.Classical.permGL σ, permGL_mem_unitarySU hK σ⟩

theorem coe_permSU (hK : UnitaryFieldData 2 n K) (σ : Equiv.Perm (Fin d)) :
    ((permSU hK σ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
      CFSG.RankThree.Classical.permGL σ :=
  rfl

theorem ActsDiagU.ratio_eq {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {a : MulAut L'} {t u : Fin d → K} (ha : ActsDiagU φ a t) (hb : ActsDiagU φ a u) (i j : Fin d) :
    t i * (t j)⁻¹ = u i * (u j)⁻¹ := by
  by_cases hij : i = j
  · subst hij
    rw [mul_inv_cancel₀ (ha.ne_zero i), mul_inv_cancel₀ (hb.ne_zero i)]
  have htne : ∀ k, t k ≠ 0 := fun k => ha.ne_zero k
  have hune : ∀ k, u k ≠ 0 := fun k => hb.ne_zero k
  obtain ⟨D, hD, hDt, hact⟩ := ha
  obtain ⟨E, hE, hEt, hbct⟩ := hb
  obtain ⟨k, hki, hkj⟩ := exists_not_mem_two hd i j
  set σ : Equiv.Perm (Fin d) := Equiv.swap i j with hσ
  set X : ↥(unitarySU 2 n K d) :=
    conjN D hD (permSU hK σ) * (conjN E hE (permSU hK σ))⁻¹ with hXdef
  have hXφ : φ X = 1 := by
    rw [hXdef, map_mul, map_inv, ← hact (permSU hK σ), ← hbct (permSU hK σ), mul_inv_cancel]
  obtain ⟨c, hc⟩ := hφker X hXφ
  set F : GL (Fin d) K := D⁻¹ * E with hFdef
  have hF : (F : Matrix (Fin d) (Fin d) K) = diagonal (fun k => (t k)⁻¹ * u k) := by
    rw [hFdef, Units.val_mul, coe_inv_diag hDt, hEt, diagonal_mul_diagonal]
  have hX' : ((X : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
      D * (CFSG.RankThree.Classical.permGL σ * F *
        (CFSG.RankThree.Classical.permGL σ)⁻¹) * E⁻¹ := by
    rw [hXdef, hFdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjN, coe_permSU]
    group
  have hXm : (((X : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun m => t m * ((t (σ⁻¹ m))⁻¹ * u (σ⁻¹ m)) * (u m)⁻¹) := by
    rw [hX']
    simp only [Units.val_mul]
    rw [hDt, coe_permGL_matrix, hF, coe_permGL_inv_matrix, coe_inv_diag hEt,
      permMatrix_conj_diag σ, diagonal_mul_diagonal, diagonal_mul_diagonal]
  have hf : (fun m => t m * ((t (σ⁻¹ m))⁻¹ * u (σ⁻¹ m)) * (u m)⁻¹) = fun _ => c :=
    Matrix.diagonal_injective (hXm.symm.trans hc)
  have hk := congrFun hf k
  have hi := congrFun hf i
  rw [hσ, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hki hkj] at hk
  rw [hσ, Equiv.swap_inv, Equiv.swap_apply_left] at hi
  have hk1 : t k * ((t k)⁻¹ * u k) * (u k)⁻¹ = 1 := by
    field_simp [htne k, hune k]
  have hc1 : c = 1 := by rw [← hk, hk1]
  rw [hc1] at hi
  field_simp [htne i, htne j, hune i, hune j] at hi ⊢
  linear_combination hi

theorem ActsDiagU.ratio_pow {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) {p : ℕ} (hap : a ^ p = 1)
    (i j : Fin d) : (t i * (t j)⁻¹) ^ p = 1 := by
  have h1 : ActsDiagU φ 1 (fun k => t k ^ p) := by
    rw [← hap]
    exact ha.pow p
  have h2 := ActsDiagU.ratio_eq hK hd hφker h1 (actsDiagU_one φ) i j
  simp only [inv_one, mul_one] at h2
  rw [mul_pow, inv_pow]
  exact h2

theorem ActsDiagU.eq_one_of_const {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hφs : Function.Surjective φ) {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t)
    (i0 : Fin d) (hc : ∀ i j, t i = t j) : a = 1 := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  have hconst : (D : Matrix (Fin d) (Fin d) K) = (t i0) • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hDt]
    have ht : t = fun _ => t i0 := funext fun i => hc i i0
    rw [ht]
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  have hcomm : ∀ s : ↥(unitarySU 2 n K d), conjN D hD s = s := by
    intro s
    apply Subtype.ext
    rw [coe_conjN]
    have hDs : (D : GL (Fin d) K) * s = s * D := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hconst]
      simp [Matrix.smul_mul, Matrix.mul_smul]
    rw [hDs, mul_assoc, mul_inv_cancel, mul_one]
  ext l
  obtain ⟨s, rfl⟩ := hφs l
  rw [hact s, hcomm s, MulAut.one_apply]

theorem ActsDiagU.fix_of_diagonal {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) (X : ↥(unitarySU 2 n K d))
    {v : Fin d → K} (hXv : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) :
    a (φ X) = φ X := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  rw [hact X]
  congr 1
  apply Subtype.ext
  rw [coe_conjN]
  have hcomm : (D : GL (Fin d) K) * (X : GL (Fin d) K) = (X : GL (Fin d) K) * D := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [hDt, hXv, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem ActsDiagU.conj_perm {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t)
    (σ : Equiv.Perm (Fin d)) :
    ActsDiagU φ (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹)
      (fun k => t (σ⁻¹ k)) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  set P : ↥(unitarySU 2 n K d) := permSU hK σ with hP
  have hPN : (P : GL (Fin d) K) ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.le_normalizer P.2
  refine ⟨(P : GL (Fin d) K) * D * (P : GL (Fin d) K)⁻¹,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hPN hD) (Subgroup.inv_mem _ hPN), ?_, fun s => ?_⟩
  · rw [Units.val_mul, Units.val_mul, hP, coe_permSU, hDt, coe_permGL_matrix,
      coe_permGL_inv_matrix, permMatrix_conj_diag σ t]
  · have hPinvN : ((P : GL (Fin d) K)⁻¹) ∈
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := Subgroup.inv_mem _ hPN
    have hs₀ : φ (conjN ((P : GL (Fin d) K)⁻¹) hPinvN s) = (φ P)⁻¹ * φ s * φ P := by
      have e : conjN ((P : GL (Fin d) K)⁻¹) hPinvN s = P⁻¹ * s * P := by
        apply Subtype.ext
        simp only [coe_conjN, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [e, map_mul, map_mul, map_inv]
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply,
      ← hs₀, hact, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [coe_conjN, Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem weyl_X_diag {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t)
    (σ : Equiv.Perm (Fin d)) :
    ∃ X : ↥(unitarySU 2 n K d), φ (permSU hK σ) * (a (φ (permSU hK σ)))⁻¹ = φ X ∧
      ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (fun k => t (σ⁻¹ k) * (t k)⁻¹) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  set P : ↥(unitarySU 2 n K d) := permSU hK σ with hP
  refine ⟨P * (conjN D hD P)⁻¹, ?_, ?_⟩
  · rw [hact P, map_mul, map_inv]
  · have hXG : ((P * (conjN D hD P)⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
        (P : GL (Fin d) K) * D * (P : GL (Fin d) K)⁻¹ * D⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjN]
      group
    rw [hXG, hP, coe_permSU]
    simp only [Units.val_mul]
    rw [hDt, coe_permGL_matrix, coe_permGL_inv_matrix, coe_inv_diag hDt,
      permMatrix_conj_diag σ t, diagonal_mul_diagonal]

theorem weyl_W_prop {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {p : ℕ} {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) :
    ∀ n' ∈ {x : L' | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hK σ)}, ∀ a ∈ A,
      (n' * (a n')⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n' * (a n')⁻¹) = n' * (a n')⁻¹ := by
  rintro _ ⟨σ, rfl⟩ a ha
  obtain ⟨t, ht⟩ := hdiag a ha
  obtain ⟨X, hXeq, hXm⟩ := weyl_X_diag hK ht σ
  rw [hXeq]
  refine ⟨?_, fun a' ha' => ?_⟩
  · rw [← map_pow]
    have hXp : X ^ p = 1 := by
      apply Subtype.ext
      apply Units.ext
      have hent : ((fun k => t (σ⁻¹ k) * (t k)⁻¹) ^ p : Fin d → K) = fun _ => (1 : K) :=
        funext fun k => (Pi.pow_apply _ _ k).trans (ht.ratio_pow hK hd hφker (hAp a ha) (σ⁻¹ k) k)
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
      rw [hXm, diagonal_pow, hent, Matrix.diagonal_one]
    rw [hXp, map_one]
  · obtain ⟨t', ht'⟩ := hdiag a' ha'
    exact ht'.fix_of_diagonal X hXm

theorem const_of_swap_pow {d p : ℕ} {K : Type} [Field K] (hd : 4 ≤ d) (hp : p.Prime)
    (t : Fin d → K) (ht : ∀ a, t a ≠ 0) (hpow : ∀ a b, (t a * (t b)⁻¹) ^ p = 1)
    (hsw : ∀ i j : Fin d, i ≠ j → ∃ k : ℕ,
      ∀ a b, t (Equiv.swap i j a) * (t (Equiv.swap i j b))⁻¹ = (t a * (t b)⁻¹) ^ k) :
    ∀ a b, t a = t b := by
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI : Fact p.Prime := ⟨hp⟩
  have key : ∀ x : K, x ^ p = 1 → x ≠ 1 → ∀ k : ℕ, x ^ (k + 1) = 1 →
      ∀ y : K, y ^ p = 1 → y ^ k = y⁻¹ := by
    intro x hxp hx1 k hxk y hyp
    have hdvd : p ∣ k + 1 := by
      rw [← orderOf_eq_prime hxp hx1]
      exact orderOf_dvd_of_pow_eq_one hxk
    obtain ⟨m, hm⟩ := hdvd
    have hy : y ^ (k + 1) = 1 := by rw [hm, pow_mul, hyp, one_pow]
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hp0] at hyp
      exact zero_ne_one hyp
    rw [pow_succ] at hy
    exact (mul_eq_one_iff_eq_inv₀ hy0).mp hy
  have key2 : ∀ (x : K) (k : ℕ), x ≠ 0 → x = (x⁻¹) ^ k → x ^ (k + 1) = 1 := by
    intro x k hx0 h
    calc x ^ (k + 1) = x ^ k * x := pow_succ x k
      _ = x ^ k * (x⁻¹) ^ k := by rw [← h]
      _ = (x * x⁻¹) ^ k := by rw [mul_pow]
      _ = 1 := by rw [mul_inv_cancel₀ hx0, one_pow]
  intro a0 b0
  by_contra hab
  have hx0' : t a0 * (t b0)⁻¹ ≠ 1 := fun h => hab ((mul_inv_eq_one₀ (ht b0)).mp h)
  have hij : a0 ≠ b0 := fun h => hab (congrArg t h)
  obtain ⟨x, hx⟩ : ∃ x, x = t a0 * (t b0)⁻¹ := ⟨_, rfl⟩
  have hxinv : t b0 * (t a0)⁻¹ = x⁻¹ := by rw [hx, _root_.mul_inv_rev, inv_inv]
  have hxp : x ^ p = 1 := by rw [hx]; exact hpow a0 b0
  have hx1 : x ≠ 1 := by rw [hx]; exact hx0'
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow hp0] at hxp
    exact zero_ne_one hxp
  obtain ⟨k1, hk1⟩ := hsw a0 b0 hij
  have hr1 : x = (x⁻¹) ^ k1 := by
    have h := hk1 b0 a0
    rw [Equiv.swap_apply_right, Equiv.swap_apply_left, hxinv, ← hx] at h
    exact h
  have hk1' : x ^ (k1 + 1) = 1 := key2 x k1 hx0 hr1
  have hinv1 : ∀ y : K, y ^ p = 1 → y ^ k1 = y⁻¹ := key x hxp hx1 k1 hk1'
  have claim : ∀ m : Fin d, m ≠ a0 → m ≠ b0 → ∃ k2 : ℕ,
      (∀ y : K, y ^ p = 1 → y ^ k2 = y⁻¹) ∧
      (∀ a b, t (Equiv.swap a0 m a) * (t (Equiv.swap a0 m b))⁻¹ = (t a * (t b)⁻¹) ^ k2) ∧
      t m * (t a0)⁻¹ = x := by
    intro m hma hmb
    obtain ⟨u, hu⟩ : ∃ u, u = t m * (t a0)⁻¹ := ⟨_, rfl⟩
    have hup : u ^ p = 1 := by rw [hu]; exact hpow m a0
    have hE1 : t m * (t b0)⁻¹ = u⁻¹ := by
      have h := hk1 m a0
      rw [Equiv.swap_apply_of_ne_of_ne hma hmb, Equiv.swap_apply_left] at h
      rw [h, ← hu, hinv1 u hup]
    have hu1 : u ≠ 1 := by
      intro h1
      have h2 : t m * (t a0)⁻¹ = 1 := by rw [← hu, h1]
      have hm1 : t m = t a0 := (mul_inv_eq_one₀ (ht a0)).mp h2
      rw [h1, inv_one] at hE1
      have hm2 : t m = t b0 := (mul_inv_eq_one₀ (ht b0)).mp hE1
      exact hab (hm1.symm.trans hm2)
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, zero_pow hp0] at hup
      exact zero_ne_one hup
    obtain ⟨k2, hk2⟩ := hsw a0 m (Ne.symm hma)
    have hA := hk2 a0 m
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right, ← hu] at hA
    have hinvu : t a0 * (t m)⁻¹ = u⁻¹ := by rw [hu, _root_.mul_inv_rev, inv_inv]
    rw [hinvu] at hA
    have hk2' : u ^ (k2 + 1) = 1 := key2 u k2 hu0 hA
    have hinv2 : ∀ y : K, y ^ p = 1 → y ^ k2 = y⁻¹ := key u hup hu1 k2 hk2'
    have hB := hk2 b0 m
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) (Ne.symm hmb), Equiv.swap_apply_right,
      hxinv] at hB
    have hwu : t b0 * (t m)⁻¹ = u := by
      rw [show t b0 * (t m)⁻¹ = (t m * (t b0)⁻¹)⁻¹ by rw [_root_.mul_inv_rev, inv_inv],
        hE1, inv_inv]
    rw [hwu, hinv2 u hup] at hB
    have hux : x = u := inv_inj.mp hB
    exact ⟨k2, hinv2, hk2, by rw [← hu, hux]⟩
  obtain ⟨m, hma, hmb⟩ := exists_not_mem_two (by omega) a0 b0
  obtain ⟨m', hm'a, hm'b, hm'm⟩ := exists_not_mem_three hd a0 b0 m
  obtain ⟨k2, hinv2, hrel, hm⟩ := claim m hma hmb
  obtain ⟨-, -, -, hm'⟩ := claim m' hm'a hm'b
  have hR := hrel m' a0
  rw [Equiv.swap_apply_of_ne_of_ne hm'a hm'm, Equiv.swap_apply_left, hm', hinv2 x hxp] at hR
  have hcoc : t m * (t m')⁻¹ = 1 := by
    have e : t m * (t m')⁻¹ = (t m * (t a0)⁻¹) * (t m' * (t a0)⁻¹)⁻¹ := by
      field_simp [ht a0, ht m']
    rw [e, hm, hm', mul_inv_cancel₀ hx0]
  have hm'm' : t m' * (t m)⁻¹ = 1 := by
    rw [show t m' * (t m)⁻¹ = (t m * (t m')⁻¹)⁻¹ by rw [_root_.mul_inv_rev, inv_inv], hcoc, inv_one]
  rw [hm'm'] at hR
  exact hx1 (inv_eq_one.mp hR.symm)

theorem moved_of_diag {L' : Type} [Group L'] [Finite (MulAut L')]
    {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) (hd : 4 ≤ d) (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {p : ℕ} (hp : p.Prime) {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    {Λ : Subgroup (MulAut L')} (hΛA : Λ ≤ A) (hΛp : Nat.card Λ = p) :
    ∃ σ : Equiv.Perm (Fin d), ∃ e ∈ Λ,
      MulAut.conj (φ (permSU hK σ)) * e * (MulAut.conj (φ (permSU hK σ)))⁻¹ ∉ Λ := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨e, heΛ, he1⟩ : ∃ e ∈ Λ, e ≠ 1 := by
    by_contra hc
    push Not at hc
    have hbot : Λ = ⊥ := (Subgroup.eq_bot_iff_forall Λ).mpr hc
    rw [hbot, Subgroup.card_bot] at hΛp
    exact hp.one_lt.ne hΛp
  have heA : e ∈ A := hΛA heΛ
  have hep : e ^ p = 1 := hAp e heA
  have hord : orderOf e = p := orderOf_eq_prime hep he1
  have hzp : Subgroup.zpowers e = Λ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr heΛ)
      (by rw [hΛp, Nat.card_zpowers, hord])
  have hfin : IsOfFinOrder e := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hep⟩
  obtain ⟨t, ht⟩ := hdiag e heA
  have hd3 : 3 ≤ d := by omega
  have hsw : ∀ i j : Fin d, i ≠ j → ∃ k : ℕ,
      ∀ a b, t (Equiv.swap i j a) * (t (Equiv.swap i j b))⁻¹ = (t a * (t b)⁻¹) ^ k := by
    intro i j _hij
    have hmem := hcon (Equiv.swap i j) e heΛ
    have hmem' : MulAut.conj (φ (permSU hK (Equiv.swap i j))) * e *
        (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹ ∈ Submonoid.powers e :=
      hfin.mem_powers_iff_mem_zpowers.mpr (by rw [hzp]; exact hmem)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hmem'
    refine ⟨k, fun a b => ?_⟩
    have h1 := ActsDiagU.conj_perm hK ht (Equiv.swap i j)
    have h2 := ActsDiagU.pow ht k
    rw [← hk] at h1
    simp only [Equiv.swap_inv] at h1
    have h3 := ActsDiagU.ratio_eq hK hd3 hφker h1 h2 a b
    have h4 : (t a * (t b)⁻¹) ^ k = t a ^ k * (t b ^ k)⁻¹ := by rw [mul_pow, inv_pow]
    exact h3.trans h4.symm
  have hconst := const_of_swap_pow hd hp t (fun x => ht.ne_zero x)
    (fun a b => ht.ratio_pow hK hd3 hφker hep a b) hsw
  exact he1 (ActsDiagU.eq_one_of_const hφs ht ⟨0, by omega⟩ (fun i j => hconst i j))

end CFSG.StandardType.LineU
