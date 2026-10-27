module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.SectionRank.OddCover

namespace SUTorus

variable {K : Type} [Field K] {f n : ℕ}

theorem not_dvd_two_pow_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) :
    ¬ p ∣ 2 ^ f - 1 := by
  intro h
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : p ∣ 2 ^ f + 1 - (2 ^ f - 1) := Nat.dvd_sub hpq h
  rw [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem pow_add_one_eq_one_of_pow (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) {l c : Kˣ} (hl : l ^ p = c)
    (hc : c ^ (2 ^ f + 1) = 1) : l ^ (2 ^ f + 1) = 1 := by
  have : Finite K := h.finite
  set μ := l ^ (2 ^ f + 1) with hμ
  have h1 : μ ^ p = 1 := by rw [hμ, ← pow_mul, mul_comm, pow_mul, hl, hc]
  have h2 : μ ^ (2 ^ f - 1) = 1 := by
    have hcard : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
      rw [Nat.card_units, h.card_eq_sq, sq]
      have := Nat.mul_self_sub_mul_self_eq (2 ^ f) 1
      simpa using this
    rw [hμ, ← pow_mul, ← hcard, pow_card_eq_one']
  have hcop : Nat.gcd p (2 ^ f - 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_two_pow_sub_one hp hp2 hpq)
  have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rwa [hcop, pow_one] at this

variable (h : UnitaryFieldData 2 f K)

theorem scalar_mem_primeFormUnitary_iff [NeZero n] (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram K n) ↔
      h.bar (c : K) * c = 1 := by
  rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  constructor
  · intro h1
    have := congrFun (Matrix.diagonal_injective h1) 0
    simpa using this
  · intro h1
    congr 1
    funext _
    exact h1

theorem mem_normalizer_of_mem_primeFormUnitary {Q : GL (Fin n) K}
    (hQ : Q ∈ primeFormUnitary h (idGram K n)) :
    Q ∈ Subgroup.normalizer ((unitarySU 2 f K n : Set (GL (Fin n) K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact ((TableBUE.conjSU h Q hQ).symm ⟨u, hu⟩).2
  · intro hu
    have h1 := ((TableBUE.conjSU h Q hQ) ⟨Q * u * Q⁻¹, hu⟩).2
    rwa [TableBUE.coe_conjSU, show Q⁻¹ * (Q * u * Q⁻¹) * Q = u by group] at h1

omit h in
theorem mul_comm_of_isToral {Ĝ : Subgroup (GL (Fin n) K)} (hT : TypeA.PGLTor.IsToral Ĝ)
    {x y : GL (Fin n) K} (hx : x ∈ Ĝ) (hy : y ∈ Ĝ) : x * y = y * x := by
  obtain ⟨A₀, hA₀⟩ := hT
  obtain ⟨σ, hσ⟩ := TableBUE.exists_diagHom_of_isDiag (g := A₀ * x * A₀⁻¹) (by
    intro i j hij
    rw [Units.val_mul, Units.val_mul]
    exact hA₀ x hx i j hij)
  obtain ⟨τ, hτ⟩ := TableBUE.exists_diagHom_of_isDiag (g := A₀ * y * A₀⁻¹) (by
    intro i j hij
    rw [Units.val_mul, Units.val_mul]
    exact hA₀ y hy i j hij)
  have hc : (A₀ * x * A₀⁻¹) * (A₀ * y * A₀⁻¹) = (A₀ * y * A₀⁻¹) * (A₀ * x * A₀⁻¹) := by
    rw [hσ, hτ, ← map_mul, mul_comm, map_mul]
  have h1 : A₀ * (x * y) * A₀⁻¹ = A₀ * (y * x) * A₀⁻¹ := by
    calc A₀ * (x * y) * A₀⁻¹ = (A₀ * x * A₀⁻¹) * (A₀ * y * A₀⁻¹) := by group
      _ = (A₀ * y * A₀⁻¹) * (A₀ * x * A₀⁻¹) := hc
      _ = A₀ * (y * x) * A₀⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h1)

theorem exists_unitary_frame [NeZero n] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ f + 1) {Ĝ : Subgroup (GL (Fin n) K)} (hĜ : TypeA.PGLTor.IsProjElem p Ĝ)
    (hT : TypeA.PGLTor.IsToral Ĝ) :
    ∃ Q ∈ primeFormUnitary h (idGram K n), ∀ B ∈ Ĝ, B ∈ primeFormUnitary h (idGram K n) →
      ∃ d : Fin n → Kˣ, Q⁻¹ * B * Q = diagHom n d := by
  have hcomm : ∀ x ∈ Ĝ, ∀ y ∈ Ĝ, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isToral hT hx hy
  let G' : Subgroup (primeFormUnitary h (idGram K n)) :=
    { carrier := {x | (x : GL (Fin n) K) ∈ Ĝ ∧ x ^ p = 1}
      one_mem' := ⟨Ĝ.one_mem, one_pow p⟩
      mul_mem' := fun {x y} hx hy => ⟨Ĝ.mul_mem hx.1 hy.1, by
        have hxy : Commute x y := Subtype.ext (hcomm _ hx.1 _ hy.1)
        rw [hxy.mul_pow, hx.2, hy.2, one_mul]⟩
      inv_mem' := fun {x} hx => ⟨Ĝ.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  obtain ⟨Q, hQ⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h hp hpq G'
    (fun x hx y hy => Subtype.ext (hcomm _ hx.1 _ hy.1)) (fun x hx => hx.2)
  refine ⟨Q, Q.2, fun B hB hBU => ?_⟩
  obtain ⟨A₀, hA₀⟩ := hT
  obtain ⟨σ, hσ⟩ := TableBUE.exists_diagHom_of_isDiag (g := A₀ * B * A₀⁻¹) (by
    intro i j hij
    rw [Units.val_mul, Units.val_mul]
    exact hA₀ B hB i j hij)
  obtain ⟨c, hc⟩ := hĜ.pow_scalar B hB
  set l := σ 0 with hl
  have hlp : l ^ p = c := by
    have h1 : (A₀ * B * A₀⁻¹) ^ p = A₀ * B ^ p * A₀⁻¹ := conj_pow
    rw [hσ, ← map_pow, hc, ← TypeA.PGLTor.scalar_mul_comm, mul_inv_cancel_right] at h1
    have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) 0 0) h1
    simp only [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Pi.pow_apply, Units.val_pow_eq_pow_val] at h2
    exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h2)
  have hcU : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram K n) := by
    rw [← hc]
    exact (primeFormUnitary h (idGram K n)).pow_mem hBU p
  have hcq : c ^ (2 ^ f + 1) = 1 := by
    have h1 := (scalar_mem_primeFormUnitary_iff h c).mp hcU
    rw [UnitaryFieldData.bar_apply] at h1
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, pow_succ, h1, Units.val_one])
  have hlq := pow_add_one_eq_one_of_pow h hp hp2 hpq hlp hcq
  have hlU : Matrix.GeneralLinearGroup.scalar (Fin n) l⁻¹ ∈ primeFormUnitary h (idGram K n) := by
    rw [scalar_mem_primeFormUnitary_iff, UnitaryFieldData.bar_apply, ← pow_succ,
      ← Units.val_pow_eq_pow_val, inv_pow, hlq, inv_one, Units.val_one]
  set B' := Matrix.GeneralLinearGroup.scalar (Fin n) l⁻¹ * B with hB'
  have hB'U : B' ∈ primeFormUnitary h (idGram K n) :=
    (primeFormUnitary h (idGram K n)).mul_mem hlU hBU
  have hB'Ĝ : B' ∈ Ĝ := Ĝ.mul_mem (hĜ.scalar_mem _) hB
  have hB'p : B' ^ p = 1 := by
    rw [hB', (TypeA.PGLTor.commute_scalar l⁻¹ B).mul_pow, ← map_pow, hc, ← map_mul, inv_pow,
      hlp, inv_mul_cancel, map_one]
  have hdiag := hQ ⟨B', hB'U⟩ ⟨hB'Ĝ, Subtype.ext (by
    rw [SubmonoidClass.coe_pow]
    exact hB'p)⟩
  have hBeq : (Q : GL (Fin n) K)⁻¹ * B * Q =
      Matrix.GeneralLinearGroup.scalar (Fin n) l * ((Q : GL (Fin n) K)⁻¹ * B' * Q) := by
    rw [hB']
    calc (Q : GL (Fin n) K)⁻¹ * B * Q = (Q : GL (Fin n) K)⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin n) l *
            Matrix.GeneralLinearGroup.scalar (Fin n) l⁻¹) * B * Q := by
          rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) l * ((Q : GL (Fin n) K)⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin n) l⁻¹ * B) * Q) := by
          rw [← mul_assoc ((Q : GL (Fin n) K)⁻¹), ← TypeA.PGLTor.scalar_mul_comm l]
          group
  refine TableBUE.exists_diagHom_of_isDiag ?_
  intro i j hij
  rw [hBeq, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_mul]
  have h3 := hdiag hij
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
  rw [h3, mul_zero]

theorem coe_conjSU_symm (Q : GL (Fin n) K) (hQ : Q ∈ primeFormUnitary h (idGram K n))
    (x : ↥(unitarySU 2 f K n)) :
    (((TableBUE.conjSU h Q hQ).symm x : ↥(unitarySU 2 f K n)) : GL (Fin n) K) = Q * x * Q⁻¹ :=
  rfl

variable {G : Type*} [Group G]

theorem range_comp_conjSU_symm (ψ : ↥(unitarySU 2 f K n) →* G) (Q : GL (Fin n) K)
    (hQ : Q ∈ primeFormUnitary h (idGram K n)) :
    (ψ.comp (TableBUE.conjSU h Q hQ).symm.toMonoidHom).range = ψ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (TableBUE.conjSU h Q hQ).symm.surjective,
    ← MonoidHom.range_eq_map]

theorem ker_comp_conjSU_symm_le {ψ : ↥(unitarySU 2 f K n) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) (Q : GL (Fin n) K)
    (hQ : Q ∈ primeFormUnitary h (idGram K n)) :
    (ψ.comp (TableBUE.conjSU h Q hQ).symm.toMonoidHom).ker ≤
      Subgroup.center ↥(unitarySU 2 f K n) := by
  intro u hu
  have hz : (TableBUE.conjSU h Q hQ).symm u ∈ Subgroup.center _ := hker hu
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro v
  have h1 := hz ((TableBUE.conjSU h Q hQ).symm v)
  rw [← map_mul, ← map_mul] at h1
  exact (TableBUE.conjSU h Q hQ).symm.injective h1

theorem mem_suPairs_frame {ψ : ↥(unitarySU 2 f K n) →* G} {Q : GL (Fin n) K}
    (hQ : Q ∈ primeFormUnitary h (idGram K n)) {e : G} {B : GL (Fin n) K}
    (hB : (e, B) ∈ suPairs ψ) :
    (e, Q⁻¹ * B * Q) ∈ suPairs (ψ.comp (TableBUE.conjSU h Q hQ).symm.toMonoidHom) := by
  have hQN := mem_normalizer_of_mem_primeFormUnitary h hQ
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hQN) hB.1) hQN,
    fun u v hv => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  refine hB.2 _ _ ?_
  rw [coe_conjSU_symm, coe_conjSU_symm, hv]
  group

end SUTorus

end CFSG.StandardType
