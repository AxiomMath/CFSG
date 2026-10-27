module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofSmallTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherLinTwo
import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Four

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Res423Two
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open Matrix
open scoped MatrixGroups

@[expose] def K417DatumU54 : Prop :=
  ∀ D : Subgroup (projSU 5 2 2), Res417Three.IsDatum417 (projSU 5 2 2) D →
    Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 4)

@[expose] def K417DatumSp62 : Prop :=
  ∀ D : Subgroup (projSp 3 (GaloisField 2 1)),
    Res417Three.IsDatum417 (projSp 3 (GaloisField 2 1)) D → Nat.card D = 27 ∧
      Nonempty (autIn ⊤ D ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))

@[expose] def aM : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def aMi : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def bM : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

@[expose] def bMi : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]

@[expose] def rM : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1]

@[expose] def rMi : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 0, 1]

@[expose] def sM : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem inv_spec : aM * aMi = 1 ∧ aMi * aM = 1 ∧ bM * bMi = 1 ∧ bMi * bM = 1 ∧
    rM * rMi = 1 ∧ rMi * rM = 1 ∧ sM * sM = 1 := by
  decide +kernel

@[expose] def a5 : GL (Fin 5) (ZMod 2) := ⟨aM, aMi, inv_spec.1, inv_spec.2.1⟩

@[expose] def b5 : GL (Fin 5) (ZMod 2) := ⟨bM, bMi, inv_spec.2.2.1, inv_spec.2.2.2.1⟩

@[expose] def r5 : GL (Fin 5) (ZMod 2) := ⟨rM, rMi, inv_spec.2.2.2.2.1, inv_spec.2.2.2.2.2.1⟩

@[expose] def s5 : GL (Fin 5) (ZMod 2) := ⟨sM, sM, inv_spec.2.2.2.2.2.2, inv_spec.2.2.2.2.2.2⟩

@[expose] def vec5 (v : Fin 2 → ZMod 3) : GL (Fin 5) (ZMod 2) := a5 ^ (v 0).val * b5 ^ (v 1).val

@[expose] def t5 : Fin 4 → GL (Fin 5) (ZMod 2) := ![a5, a5 ^ 2, b5, b5 ^ 2]

@[expose] def w5 (k : Fin 4) (l : Fin 2) : GL (Fin 5) (ZMod 2) := r5 ^ (k : ℕ) * s5 ^ (l : ℕ)

@[expose] def sqIdx : Fin 4 → Fin 4 := ![1, 0, 3, 2]

@[expose] def img1 (k : Fin 4) (l : Fin 2) : Fin 4 :=
  ![![0, 1], ![2, 3], ![1, 0], ![3, 2]] k l

@[expose] def img2 (k : Fin 4) (_l : Fin 2) : Fin 4 := ![2, 1, 3, 0] k

theorem vec5_spec : (∀ v w : Fin 2 → ZMod 3, vec5 (v + w) = vec5 v * vec5 w) ∧
    (∀ v : Fin 2 → ZMod 3, vec5 v = 1 → v = 0) ∧ vec5 ![1, 0] = a5 ∧ vec5 ![0, 1] = b5 := by
  decide +kernel

theorem trace_cases : ∀ v : Fin 2 → ZMod 3, ((vec5 v : GL (Fin 5) (ZMod 2)) :
    Matrix (Fin 5) (Fin 5) (ZMod 2)).trace = 0 → ∃ i : Fin 4, vec5 v = t5 i := by
  decide +kernel

theorem rs5_spec : r5 * a5 * r5⁻¹ = b5 ∧ r5 * b5 * r5⁻¹ = a5⁻¹ ∧ s5 * a5 * s5⁻¹ = a5⁻¹ ∧
    s5 * b5 * s5⁻¹ = b5 ∧ r5 ^ 4 = 1 ∧ s5 ^ 2 = 1 ∧
    (a5 : Matrix (Fin 5) (Fin 5) (ZMod 2)).trace = 0 ∧
    (b5 : Matrix (Fin 5) (Fin 5) (ZMod 2)).trace = 0 ∧ b5 ≠ a5 ∧ b5 ≠ a5 ^ 2 ∧
    (∀ i : Fin 4, t5 (sqIdx i) = t5 i ^ 2) ∧ Function.Injective t5 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro i j hij
  revert i j
  decide +kernel

theorem srs5_spec : (s5 * r5 * s5⁻¹) * a5 * (s5 * r5 * s5⁻¹)⁻¹ = r5⁻¹ * a5 * (r5⁻¹)⁻¹ ∧
    (s5 * r5 * s5⁻¹) * b5 * (s5 * r5 * s5⁻¹)⁻¹ = r5⁻¹ * b5 * (r5⁻¹)⁻¹ ∧
    r5 ^ 2 * a5 * (r5 ^ 2)⁻¹ ≠ a5 ∧
    ∀ k : Fin 4, ¬ (r5 ^ (k : ℕ) * a5 * (r5 ^ (k : ℕ))⁻¹ = s5 * a5 * s5⁻¹ ∧
      r5 ^ (k : ℕ) * b5 * (r5 ^ (k : ℕ))⁻¹ = s5 * b5 * s5⁻¹) := by
  decide +kernel

theorem words_spec : ∀ (k : Fin 4) (l : Fin 2),
    w5 k l * a5 * (w5 k l)⁻¹ = t5 (img1 k l) ∧ w5 k l * b5 * (w5 k l)⁻¹ = t5 (img2 k l) := by
  decide +kernel

theorem img_cover : ∀ i j : Fin 4, j ≠ i → j ≠ sqIdx i →
    ∃ k : Fin 4, ∃ l : Fin 2, img1 k l = i ∧ img2 k l = j := by
  decide

@[expose] noncomputable def vecHom5 : Multiplicative (Fin 2 → ZMod 3) →* GL (Fin 5) (ZMod 2) where
  toFun v := vec5 (Multiplicative.toAdd v)
  map_one' := by simp [vec5]
  map_mul' u v := vec5_spec.1 _ _

@[expose] def E9 : Subgroup (GL (Fin 5) (ZMod 2)) := Subgroup.zpowers a5 ⊔ Subgroup.zpowers b5

theorem E9_eq_range : E9 = vecHom5.range := by
  apply le_antisymm
  · refine sup_le (Subgroup.zpowers_le.mpr ⟨Multiplicative.ofAdd ![1, 0], vec5_spec.2.2.1⟩)
      (Subgroup.zpowers_le.mpr ⟨Multiplicative.ofAdd ![0, 1], vec5_spec.2.2.2⟩)
  · rintro _ ⟨v, rfl⟩
    exact mul_mem (pow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) _)
      (pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)

theorem card_E9 : Nat.card E9 = 9 := by
  have hinj : Function.Injective vecHom5 := by
    rw [injective_iff_map_eq_one]
    intro v hv
    exact Multiplicative.toAdd.injective (vec5_spec.2.1 _ hv)
  rw [E9_eq_range, Item434AltPerm.card_range_of_injective _ hinj]
  norm_num

theorem factorization_card_GL5 : (Nat.card (GL (Fin 5) (ZMod 2))).factorization 3 = 2 := by
  rw [Matrix.card_GL_field, ZMod.card]
  have h : (∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ))) = 3 ^ 2 * 1111040 := by decide
  rw [h]
  exact Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)

theorem mem_normalizer_E9 {g : GL (Fin 5) (ZMod 2)} (h1 : g * a5 * g⁻¹ ∈ E9)
    (h2 : g * b5 * g⁻¹ ∈ E9) : g ∈ Subgroup.normalizer (E9 : Set (GL (Fin 5) (ZMod 2))) := by
  have hle : E9 ≤ E9.comap (MulAut.conj g).toMonoidHom := by
    refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    · exact h1
    · exact h2
  exact Subgroup.mem_normalizer_fintype fun x hx => hle hx

theorem a5_mem : a5 ∈ E9 := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem b5_mem : b5 ∈ E9 := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

@[expose] def rN5 : Subgroup.normalizer (E9 : Set (GL (Fin 5) (ZMod 2))) :=
  ⟨r5, mem_normalizer_E9 (by rw [rs5_spec.1]; exact b5_mem)
    (by rw [rs5_spec.2.1]; exact inv_mem a5_mem)⟩

@[expose] def sN5 : Subgroup.normalizer (E9 : Set (GL (Fin 5) (ZMod 2))) :=
  ⟨s5, mem_normalizer_E9 (by rw [rs5_spec.2.2.1]; exact inv_mem a5_mem)
    (by rw [rs5_spec.2.2.2.1]; exact b5_mem)⟩

@[expose] noncomputable def rho5 : MulAut E9 := E9.normalizerMonoidHom rN5

@[expose] noncomputable def sigma5 : MulAut E9 := E9.normalizerMonoidHom sN5

@[expose] def aE : E9 := ⟨a5, a5_mem⟩

@[expose] def bE : E9 := ⟨b5, b5_mem⟩

theorem nmh5_eq (h₁ h₂ : Subgroup.normalizer (E9 : Set (GL (Fin 5) (ZMod 2))))
    (ha : (h₁ : GL (Fin 5) (ZMod 2)) * a5 * (h₁ : GL (Fin 5) (ZMod 2))⁻¹ =
      (h₂ : GL (Fin 5) (ZMod 2)) * a5 * (h₂ : GL (Fin 5) (ZMod 2))⁻¹)
    (hb : (h₁ : GL (Fin 5) (ZMod 2)) * b5 * (h₁ : GL (Fin 5) (ZMod 2))⁻¹ =
      (h₂ : GL (Fin 5) (ZMod 2)) * b5 * (h₂ : GL (Fin 5) (ZMod 2))⁻¹) :
    E9.normalizerMonoidHom h₁ = E9.normalizerMonoidHom h₂ := by
  set x : GL (Fin 5) (ZMod 2) := (h₁ : GL (Fin 5) (ZMod 2)) with hx'
  set y : GL (Fin 5) (ZMod 2) := (h₂ : GL (Fin 5) (ZMod 2)) with hy'
  have hk : ∀ z : GL (Fin 5) (ZMod 2), x * z * x⁻¹ = y * z * y⁻¹ ↔
      z * (y⁻¹ * x) = (y⁻¹ * x) * z := by
    intro z
    constructor
    · intro h
      calc z * (y⁻¹ * x) = y⁻¹ * (y * z * y⁻¹) * x := by group
        _ = y⁻¹ * (x * z * x⁻¹) * x := by rw [h]
        _ = (y⁻¹ * x) * z := by group
    · intro h
      calc x * z * x⁻¹ = y * ((y⁻¹ * x) * z) * x⁻¹ := by group
        _ = y * (z * (y⁻¹ * x)) * x⁻¹ := by rw [h]
        _ = y * z * y⁻¹ := by group
  have hle : E9 ≤ Subgroup.centralizer ({y⁻¹ * x} : Set (GL (Fin 5) (ZMod 2))) := by
    refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · exact (hk _).mp ha
    · exact (hk _).mp hb
  refine MulEquiv.ext fun z => Subtype.ext ?_
  exact (hk _).mpr (Subgroup.mem_centralizer_singleton_iff.mp (hle z.2))

theorem rho5_mem : rho5 ∈ autIn ⊤ E9 :=
  mem_autIn_iff.mpr ⟨_, rN5.2, Subgroup.mem_top _, rfl⟩

theorem sigma5_mem : sigma5 ∈ autIn ⊤ E9 :=
  mem_autIn_iff.mpr ⟨_, sN5.2, Subgroup.mem_top _, rfl⟩

theorem coe_w5 (k : Fin 4) (l : Fin 2) :
    ((rN5 ^ (k : ℕ) * sN5 ^ (l : ℕ) : Subgroup.normalizer (E9 : Set (GL (Fin 5) (ZMod 2)))) :
      GL (Fin 5) (ZMod 2)) = w5 k l := by
  simp [w5, rN5, sN5]

theorem mem_autIn_E9 {φ : MulAut E9} (hφ : φ ∈ autIn ⊤ E9) :
    ∃ k : Fin 4, ∃ l : Fin 2, φ = rho5 ^ (k : ℕ) * sigma5 ^ (l : ℕ) := by
  obtain ⟨g, hN, -, rfl⟩ := mem_autIn_iff.mp hφ
  have himg : ∀ c ∈ E9, (c : Matrix (Fin 5) (Fin 5) (ZMod 2)).trace = 0 →
      ∃ i : Fin 4, g * c * g⁻¹ = t5 i := by
    intro c hc htr
    have hmem : g * c * g⁻¹ ∈ E9 := (Subgroup.mem_normalizer_iff.mp hN c).mp hc
    rw [E9_eq_range] at hmem
    obtain ⟨v, hv⟩ := hmem
    change vec5 (Multiplicative.toAdd v) = g * c * g⁻¹ at hv
    have htr' : ((vec5 (Multiplicative.toAdd v) : GL (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)).trace = 0 := by
      rw [hv, Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      exact htr
    obtain ⟨i, hi⟩ := trace_cases _ htr'
    exact ⟨i, hv ▸ hi⟩
  obtain ⟨hr1, hr2, hs1, hs2, -, -, hta, htb, hba, hba2, hsq, ht5inj⟩ := rs5_spec
  obtain ⟨i, hi⟩ := himg a5 a5_mem hta
  obtain ⟨j, hj⟩ := himg b5 b5_mem htb
  have hji : j ≠ i := by
    rintro rfl
    apply hba
    have h1 : g * b5 * g⁻¹ = g * a5 * g⁻¹ := by rw [hi, hj]
    simpa using h1
  have hji2 : j ≠ sqIdx i := by
    rintro rfl
    apply hba2
    have h1 : g * b5 * g⁻¹ = g * a5 ^ 2 * g⁻¹ := by
      rw [hj, hsq, ← hi, conj_pow]
    simpa using h1
  obtain ⟨k, l, hk1, hk2⟩ := img_cover i j hji hji2
  refine ⟨k, l, ?_⟩
  rw [rho5, sigma5, ← map_pow, ← map_pow, ← map_mul]
  obtain ⟨hw1, hw2⟩ := words_spec k l
  refine nmh5_eq _ _ ?_ ?_
  · rw [coe_w5, hw1, hk1]
    exact hi
  · rw [coe_w5, hw2, hk2]
    exact hj

theorem nmh5_apply (h : Subgroup.normalizer (E9 : Set (GL (Fin 5) (ZMod 2)))) (x : E9) :
    ((E9.normalizerMonoidHom h x : E9) : GL (Fin 5) (ZMod 2)) =
      (h : GL (Fin 5) (ZMod 2)) * (x : GL (Fin 5) (ZMod 2)) * (h : GL (Fin 5) (ZMod 2))⁻¹ :=
  rfl

theorem rho5_pow_four : rho5 ^ 4 = 1 := by
  have h : rN5 ^ 4 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact rs5_spec.2.2.2.2.1)
  rw [rho5, ← map_pow, h, map_one]

theorem rho5_sq_ne_one : rho5 ^ 2 ≠ 1 := by
  intro h
  have h1 := congrArg (fun φ : MulAut E9 => ((φ aE : E9) : GL (Fin 5) (ZMod 2))) h
  simp only [MulAut.one_apply] at h1
  rw [rho5, ← map_pow, nmh5_apply] at h1
  exact srs5_spec.2.2.1 (by simpa [rN5, aE] using h1)

theorem orderOf_rho5 : orderOf rho5 = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : rho5 ^ 2 ^ (1 + 1) = 1 := rho5_pow_four
  have h2 : ¬ rho5 ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact rho5_sq_ne_one
  exact orderOf_eq_prime_pow h2 h4

theorem sigma5_sq : sigma5 ^ 2 = 1 := by
  have h : sN5 ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact rs5_spec.2.2.2.2.2.1)
  rw [sigma5, ← map_pow, h, map_one]

theorem sigma5_rho5 : sigma5 * rho5 * sigma5⁻¹ = rho5⁻¹ := by
  rw [rho5, sigma5, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
  refine nmh5_eq _ _ ?_ ?_
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact srs5_spec.1
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact srs5_spec.2.1

theorem sigma5_not_mem : sigma5 ∉ Subgroup.zpowers rho5 := by
  classical
  intro h
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_rho5] at h
  obtain ⟨k, hk, hks⟩ := Finset.mem_image.mp h
  have hk4 : k < 4 := Finset.mem_range.mp hk
  have h1 := congrArg (fun φ : MulAut E9 => ((φ aE : E9) : GL (Fin 5) (ZMod 2))) hks
  have h2 := congrArg (fun φ : MulAut E9 => ((φ bE : E9) : GL (Fin 5) (ZMod 2))) hks
  rw [rho5, sigma5, ← map_pow, nmh5_apply, nmh5_apply] at h1 h2
  rw [Subgroup.coe_pow] at h1 h2
  exact srs5_spec.2.2.2 ⟨k, hk4⟩ ⟨h1, h2⟩

theorem nonempty_autIn_E9 : Nonempty (autIn ⊤ E9 ≃* DihedralGroup 4) := by
  set ρ' : autIn ⊤ E9 := ⟨rho5, rho5_mem⟩
  set σ' : autIn ⊤ E9 := ⟨sigma5, sigma5_mem⟩
  have hgen : (⊤ : Subgroup (autIn ⊤ E9)) = Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ' := by
    refine (eq_top_iff.mpr fun x _ => ?_).symm
    obtain ⟨k, l, hkl⟩ := mem_autIn_E9 x.2
    have hx : x = ρ' ^ (k : ℕ) * σ' ^ (l : ℕ) := Subtype.ext (by simpa [ρ', σ'] using hkl)
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers _)) _) (Subgroup.pow_mem _ (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers _)) _)
  have hσ2 : σ' ^ 2 = 1 := Subtype.ext (by simpa [σ'] using sigma5_sq)
  have hrel : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := Subtype.ext (by simpa [σ', ρ'] using sigma5_rho5)
  have hσρ : σ' ∉ Subgroup.zpowers ρ' := by
    intro h
    apply sigma5_not_mem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa [ρ', σ'] using congrArg Subtype.val hn⟩
  have hord : orderOf ρ' = 4 := by
    rw [← orderOf_rho5]
    exact Subgroup.orderOf_mk rho5 rho5_mem
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ' σ' hgen hσ2 hrel hσρ
  rw [hord] at e
  exact ⟨e⟩

@[expose] noncomputable def gl5ToSL : GL (Fin 5) (ZMod 2) →* SL(5, GaloisField 2 1) :=
  (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) (GaloisField 2 1))).comp
    (CFSG.QuasithinUnique.Setup.Family.slEquivGL 5).symm.toMonoidHom

theorem gl5ToSL_injective : Function.Injective gl5ToSL := by
  intro x y h
  have hmap : Function.Injective (Matrix.SpecialLinearGroup.map
      (ZMod.castHom (dvd_refl 2) (GaloisField 2 1)) :
        SL(5, ZMod 2) →* SL(5, GaloisField 2 1)) := by
    intro u v huv
    apply Subtype.ext
    have h' := congrArg (fun m : SL(5, GaloisField 2 1) =>
      (m : Matrix (Fin 5) (Fin 5) (GaloisField 2 1))) huv
    exact Matrix.map_injective (ZMod.castHom (dvd_refl 2) (GaloisField 2 1)).injective h'
  rw [gl5ToSL, MonoidHom.coe_comp] at h
  exact (CFSG.QuasithinUnique.Setup.Family.slEquivGL 5).symm.injective (hmap h)

theorem card_SL5_gf2 : Nat.card SL(5, GaloisField 2 1) = Nat.card (GL (Fin 5) (ZMod 2)) := by
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  rw [Matrix.card_SL_field, Matrix.card_GL_field, ← Nat.card_eq_fintype_card,
    GaloisField.card 2 1 one_ne_zero, ZMod.card]
  decide

@[expose] noncomputable def gl5EquivProjSL : GL (Fin 5) (ZMod 2) ≃* projSL 5 (GaloisField 2 1) :=
  (MulEquiv.ofBijective gl5ToSL (gl5ToSL_injective.bijective_of_nat_card_le card_SL5_gf2.le)).trans
    (Item434SmallTwoOther.slEquivProjSL (by norm_num))

theorem k417DatumL52_holds :
    ∀ D : Subgroup (projSL 5 (GaloisField 2 1)),
      Res417Three.IsDatum417 (projSL 5 (GaloisField 2 1)) D →
        Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 4) := by
  intro D hD
  obtain ⟨hDe, -, F, hFD, hF9, -⟩ := hD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (projSL 5 (GaloisField 2 1)) := Finite.of_equiv _ gl5EquivProjSL.toEquiv
  set ψ := gl5EquivProjSL.symm with hψ
  set D' := D.map ψ.toMonoidHom with hD'
  have hcard : Nat.card D' = Nat.card D := Subgroup.card_map_of_injective ψ.injective
  have hD3 : IsPGroup 3 D := fun x => ⟨1, Subtype.ext (by simpa using hDe.2 x x.2)⟩
  have hDp : IsPGroup 3 D' := hD3.map ψ.toMonoidHom
  have hle := Item434AltPerm.card_le_of_isPGroup hDp
  rw [factorization_card_GL5, hcard] at hle
  have hge : 9 ≤ Nat.card D := hF9.trans (Subgroup.card_le_of_le hFD)
  have hD9 : Nat.card D = 9 := by
    have : Nat.card D ≤ 9 := by simpa using hle
    omega
  refine ⟨hD9, ?_⟩
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_card_nine factorization_card_GL5
    (hcard.trans hD9) card_E9
  have f1 := Sporadic.autInTopCongr ψ D
  have f2 := Sporadic.autInTopCongr (MulAut.conj g) D'
  rw [show D'.map (MulAut.conj g : GL (Fin 5) (ZMod 2) ≃* GL (Fin 5) (ZMod 2)).toMonoidHom = E9
    from hg] at f2
  obtain ⟨e⟩ := nonempty_autIn_E9
  exact ⟨f1.trans (f2.trans e)⟩

theorem k417DatumSmallTwo_of (hU : K417DatumU54) (hS : K417DatumSp62) :
    Res417Three.K417DatumSmallTwo :=
  ⟨k417DatumL52_holds, hU, hS⟩

end CFSG.RankThree.PartTwo.Sec4.Res417Four
