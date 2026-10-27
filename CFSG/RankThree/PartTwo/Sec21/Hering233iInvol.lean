module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG
open CFSG.Assembly (IsElemAbelian)
open scoped Matrix

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]

@[expose] def gMat (N₁ N₂ : Matrix ι ι R) (s t : R) : Matrix ι ι R := 1 + s • N₁ + t • N₂

structure NilPair (N₁ N₂ : Matrix ι ι R) : Prop where
  h11 : N₁ * N₁ = 0
  h12 : N₁ * N₂ = 0
  h21 : N₂ * N₁ = 0
  h22 : N₂ * N₂ = 0

theorem gMat_mul {N₁ N₂ : Matrix ι ι R} (h : NilPair N₁ N₂) (s t s' t' : R) :
    gMat N₁ N₂ s t * gMat N₁ N₂ s' t' = gMat N₁ N₂ (s + s') (t + t') := by
  simp only [gMat, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, h.h11, h.h12, h.h21, h.h22, smul_zero, add_zero, add_smul]
  abel

theorem gMat_zero_zero (N₁ N₂ : Matrix ι ι R) : gMat N₁ N₂ 0 0 = 1 := by
  simp [gMat]

theorem add_self_eq_zero_of_two (h2 : (2 : R) = 0) (x : R) : x + x = 0 := by
  rw [← two_mul, h2, zero_mul]

theorem gMat_sq {N₁ N₂ : Matrix ι ι R} (h : NilPair N₁ N₂) (h2 : (2 : R) = 0) (s t : R) :
    gMat N₁ N₂ s t * gMat N₁ N₂ s t = 1 := by
  rw [gMat_mul h, add_self_eq_zero_of_two h2 s, add_self_eq_zero_of_two h2 t, gMat_zero_zero]

@[expose] def gUnit {N₁ N₂ : Matrix ι ι R} (h : NilPair N₁ N₂) (h2 : (2 : R) = 0) (s t : R) :
    (Matrix ι ι R)ˣ :=
  ⟨gMat N₁ N₂ s t, gMat N₁ N₂ s t, gMat_sq h h2 s t, gMat_sq h h2 s t⟩

@[expose] noncomputable def gHom {N₁ N₂ : Matrix ι ι R} (P₁ P₂ : AddSubgroup R)
    (h : NilPair N₁ N₂) (h2 : (2 : R) = 0) : Multiplicative (P₁ × P₂) →* (Matrix ι ι R)ˣ where
  toFun x := gUnit h h2 ((Multiplicative.toAdd x).1 : R) ((Multiplicative.toAdd x).2 : R)
  map_one' := Units.ext (by
    change gMat N₁ N₂ (((0 : P₁ × P₂).1 : P₁) : R) (((0 : P₁ × P₂).2 : P₂) : R) = 1
    exact gMat_zero_zero N₁ N₂)
  map_mul' x y := Units.ext (by
    change gMat N₁ N₂ (((Multiplicative.toAdd x + Multiplicative.toAdd y).1 : P₁) : R)
      (((Multiplicative.toAdd x + Multiplicative.toAdd y).2 : P₂) : R) = _
    exact (gMat_mul h _ _ _ _).symm)

theorem gHom_injective {N₁ N₂ : Matrix ι ι R} (P₁ P₂ : AddSubgroup R) (h : NilPair N₁ N₂)
    (h2 : (2 : R) = 0) (hind : ∀ s t : R, s • N₁ + t • N₂ = 0 → s = 0 ∧ t = 0) :
    Function.Injective (gHom P₁ P₂ h h2) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : gMat N₁ N₂ ((Multiplicative.toAdd x).1 : R) ((Multiplicative.toAdd x).2 : R) = 1 :=
    congrArg Units.val hx
  have h3 : ((Multiplicative.toAdd x).1 : R) • N₁ + ((Multiplicative.toAdd x).2 : R) • N₂ = 0 := by
    have : (1 : Matrix ι ι R) + (((Multiplicative.toAdd x).1 : R) • N₁ +
        ((Multiplicative.toAdd x).2 : R) • N₂) = 1 + 0 := by
      rw [add_zero, ← add_assoc]
      exact h1
    exact add_left_cancel this
  obtain ⟨h4, h5⟩ := hind _ _ h3
  apply Multiplicative.toAdd.injective
  exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)

theorem exists_E16_gfam [Finite R] {N₁ N₂ : Matrix ι ι R} (P₁ P₂ : AddSubgroup R)
    (hP : 16 ≤ Nat.card P₁ * Nat.card P₂)
    (h : NilPair N₁ N₂) (h2 : (2 : R) = 0)
    (hind : ∀ s t : R, s • N₁ + t • N₂ = 0 → s = 0 ∧ t = 0) :
    ∃ E : Subgroup (Matrix ι ι R)ˣ, IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4 ∧
      ∀ g ∈ E, ∃ s ∈ P₁, ∃ t ∈ P₂, (g : Matrix ι ι R) = gMat N₁ N₂ s t := by
  set ψ := gHom P₁ P₂ h h2 with hψ
  have hinj : Function.Injective ψ := gHom_injective P₁ P₂ h h2 hind
  have hsq : ∀ x : Multiplicative (P₁ × P₂), x ^ 2 = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, two_nsmul, toAdd_one]
    exact Prod.ext (Subtype.ext (add_self_eq_zero_of_two h2 _))
      (Subtype.ext (add_self_eq_zero_of_two h2 _))
  haveI : Finite P₁ := inferInstance
  haveI : Finite P₂ := inferInstance
  haveI : Finite (Multiplicative (P₁ × P₂)) := inferInstanceAs (Finite (P₁ × P₂))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Multiplicative (P₁ × P₂)) := fun x => ⟨1, by simpa using hsq x⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hcard : Nat.card (Multiplicative (P₁ × P₂)) = Nat.card P₁ * Nat.card P₂ := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (P₁ × P₂) ≃ P₁ × P₂),
      Nat.card_prod]
  have h16 : 2 ^ 4 ∣ Nat.card (Multiplicative (P₁ × P₂)) := by
    have hle : 2 ^ 4 ≤ 2 ^ n := by
      rw [← hn, hcard]
      exact hP
    have : 4 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    rw [hn]
    exact pow_dvd_pow 2 this
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 h16
  refine ⟨K₀.map ψ, ?_, ?_, ?_⟩
  · have hK₀e : IsElemAbelian 2 K₀ :=
      ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun x hx => by
        have := hsq x
        exact congrArg Subtype.val (Subtype.ext this : (⟨x, hx⟩ : K₀) ^ 2 = 1)⟩
    exact CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map hK₀e _
  · rw [Subgroup.card_map_of_injective hinj, hK₀]
  · rintro g ⟨x, -, rfl⟩
    exact ⟨_, (Multiplicative.toAdd x).1.2, _, (Multiplicative.toAdd x).2.2, rfl⟩

theorem det_eq_one_of_mul_self [IsDomain R] {A : Matrix ι ι R} (hA : A * A = 1)
    (h2 : (2 : R) = 0) : A.det = 1 := by
  have h1 : A.det * A.det = 1 := by rw [← Matrix.det_mul, hA, Matrix.det_one]
  have h3 : (A.det - 1) * (A.det - 1) = 0 := by
    linear_combination h1 + (1 - A.det) * h2
  have := mul_self_eq_zero.mp h3
  exact sub_eq_zero.mp this

theorem gMat_symp {N₁ N₂ J : Matrix ι ι R} (h : NilPair N₁ N₂) (h2 : (2 : R) = 0)
    (hJ : Jᵀ = J) (hJ1 : (J * N₁)ᵀ = J * N₁) (hJ2 : (J * N₂)ᵀ = J * N₂) (s t : R) :
    (gMat N₁ N₂ s t)ᵀ * J * gMat N₁ N₂ s t = J := by
  have e1 : ∀ N : Matrix ι ι R, (J * N)ᵀ = J * N → Nᵀ * J = J * N := by
    intro N hN
    calc Nᵀ * J = Nᵀ * Jᵀ := by rw [hJ]
      _ = (J * N)ᵀ := (Matrix.transpose_mul J N).symm
      _ = J * N := hN
  set M : Matrix ι ι R := s • N₁ + t • N₂ with hM
  have hMJ : Mᵀ * J = J * M := by
    rw [hM, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.add_mul,
      Matrix.smul_mul, Matrix.smul_mul, e1 N₁ hJ1, e1 N₂ hJ2, Matrix.mul_add, Matrix.mul_smul,
      Matrix.mul_smul]
  have hMM : M * M = 0 := by
    rw [hM]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.h11, h.h12,
      h.h21, h.h22, smul_zero, add_zero]
  have hg : gMat N₁ N₂ s t = 1 + M := by
    rw [gMat, hM, add_assoc]
  have e2 : J * M + J * M = 0 := by
    have : J * M + J * M = (2 : R) • (J * M) := by rw [two_smul]
    rw [this, h2, zero_smul]
  have step1 : (1 + Mᵀ) * J = J + J * M := by
    rw [Matrix.add_mul, Matrix.one_mul, hMJ]
  rw [hg, Matrix.transpose_add, Matrix.transpose_one, step1, Matrix.mul_add, Matrix.mul_one,
    Matrix.add_mul, mul_assoc J M M, hMM, Matrix.mul_zero, add_zero, add_assoc, e2, add_zero]

theorem gMat_map {N₁ N₂ : Matrix ι ι R} (φ : R →+* R) (hf₁ : N₁.map φ = N₁)
    (hf₂ : N₂.map φ = N₂) {s t : R} (hs : φ s = s) (ht : φ t = t) :
    (gMat N₁ N₂ s t).map φ = gMat N₁ N₂ s t := by
  ext i j
  have e1 := congrFun₂ hf₁ i j
  have e2 := congrFun₂ hf₂ i j
  simp only [Matrix.map_apply] at e1 e2
  have e3 : φ ((1 : Matrix ι ι R) i j) = (1 : Matrix ι ι R) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp only [gMat, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
    map_mul, e1, e2, e3, hs, ht]

theorem gMat_unitary {N₁ N₂ : Matrix ι ι R} (φ : R →+* R) (h : NilPair N₁ N₂)
    (h2 : (2 : R) = 0) (hs₁ : N₁ᵀ = N₁) (hs₂ : N₂ᵀ = N₂) (hf₁ : N₁.map φ = N₁)
    (hf₂ : N₂.map φ = N₂) {s t : R} (hs : φ s = s) (ht : φ t = t) :
    ((gMat N₁ N₂ s t).map φ)ᵀ * gMat N₁ N₂ s t = 1 := by
  rw [gMat_map φ hf₁ hf₂ hs ht]
  have : (gMat N₁ N₂ s t)ᵀ = gMat N₁ N₂ s t := by
    simp only [gMat, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hs₁,
      hs₂]
  rw [this]
  exact gMat_sq h h2 s t

end Generic

end CFSG.RankThree.PartTwo.Sec21.Hering233i
