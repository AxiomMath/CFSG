module

public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
public import CFSG.Sporadic.Bridge.J3Surj
public import Certificates.Certificate8095
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native
open CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover.Native
open CFSG.RankThree.PartOne.CentralCoverThree
open scoped commutatorElement

namespace SporadicTwoCover

section Datum

variable {X : Type*} [Group X]

structure E16Datum (a₁ a₂ a₃ a₄ n : X) : Prop where
  ne_one : a₁ ≠ 1
  sq : a₁ ^ 2 = 1
  comm₁₂ : Commute a₁ a₂
  comm₁₃ : Commute a₁ a₃
  comm₁₄ : Commute a₁ a₄
  conj₁ : n * a₁ * n⁻¹ = a₂
  conj₂ : n * a₂ * n⁻¹ = a₃
  conj₃ : n * a₃ * n⁻¹ = a₄
  conj₄ : n * a₄ * n⁻¹ = a₁ * a₂

@[expose] def e16Prod (a₁ a₂ a₃ a₄ : X) (v : Fin 4 → Fin 2) : X :=
  a₁ ^ (v 0 : ℕ) * a₂ ^ (v 1 : ℕ) * a₃ ^ (v 2 : ℕ) * a₄ ^ (v 3 : ℕ)

@[expose] def e16Shift (v : Fin 4 → Fin 2) : Fin 4 → Fin 2 := ![v 3, v 0 + v 3, v 1, v 2]

theorem exists_iterate_e16Shift :
    ∀ v : Fin 4 → Fin 2, v ≠ 0 → ∃ k : Fin 15, e16Shift^[k] ![1, 0, 0, 0] = v := by
  decide

namespace E16Datum

variable {a₁ a₂ a₃ a₄ n : X} (h : E16Datum a₁ a₂ a₃ a₄ n)
include h

theorem sq₂ : a₂ ^ 2 = 1 := by
  rw [← h.conj₁, conj_pow, h.sq, mul_one, mul_inv_cancel]

theorem sq₃ : a₃ ^ 2 = 1 := by
  rw [← h.conj₂, conj_pow, h.sq₂, mul_one, mul_inv_cancel]

theorem sq₄ : a₄ ^ 2 = 1 := by
  rw [← h.conj₃, conj_pow, h.sq₃, mul_one, mul_inv_cancel]

theorem comm₂₃ : Commute a₂ a₃ := by
  have := h.comm₁₂.map (MulAut.conj n)
  simpa only [MulAut.conj_apply, h.conj₁, h.conj₂] using this

theorem comm₂₄ : Commute a₂ a₄ := by
  have := h.comm₁₃.map (MulAut.conj n)
  simpa only [MulAut.conj_apply, h.conj₁, h.conj₃] using this

theorem comm₃₄ : Commute a₃ a₄ := by
  have := h.comm₂₃.map (MulAut.conj n)
  simpa only [MulAut.conj_apply, h.conj₂, h.conj₃] using this

theorem conj_e16Prod (v : Fin 4 → Fin 2) :
    n * e16Prod a₁ a₂ a₃ a₄ v * n⁻¹ = e16Prod a₁ a₂ a₃ a₄ (e16Shift v) := by
  have e : ∀ x y : X, n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := fun x y => by group
  have ep : ∀ (x : X) (k : ℕ), n * x ^ k * n⁻¹ = (n * x * n⁻¹) ^ k := fun x k =>
    (conj_pow ..).symm
  have hlhs : n * e16Prod a₁ a₂ a₃ a₄ v * n⁻¹ = a₂ ^ (v 0 : ℕ) * a₃ ^ (v 1 : ℕ) *
      a₄ ^ (v 2 : ℕ) * (a₁ ^ (v 3 : ℕ) * a₂ ^ (v 3 : ℕ)) := by
    rw [e16Prod, e, e, e, ep, ep, ep, ep, h.conj₁, h.conj₂, h.conj₃, h.conj₄,
      h.comm₁₂.mul_pow]
  have hrhs : e16Prod a₁ a₂ a₃ a₄ (e16Shift v) = a₁ ^ (v 3 : ℕ) *
      (a₂ ^ (v 0 : ℕ) * a₂ ^ (v 3 : ℕ)) * a₃ ^ (v 1 : ℕ) * a₄ ^ (v 2 : ℕ) := by
    change a₁ ^ (v 3 : ℕ) * a₂ ^ ((v 0 + v 3 : Fin 2) : ℕ) * a₃ ^ (v 1 : ℕ) * a₄ ^ (v 2 : ℕ) = _
    rw [Fin.val_add, ← pow_eq_pow_mod _ h.sq₂, pow_add]
  have c1 : Commute (a₂ ^ (v 0 : ℕ) * a₃ ^ (v 1 : ℕ) * a₄ ^ (v 2 : ℕ)) (a₁ ^ (v 3 : ℕ)) :=
    ((h.comm₁₂.symm.pow_pow _ _).mul_left (h.comm₁₃.symm.pow_pow _ _)).mul_left
      (h.comm₁₄.symm.pow_pow _ _)
  have c2 : Commute (a₃ ^ (v 1 : ℕ) * a₄ ^ (v 2 : ℕ)) (a₂ ^ (v 3 : ℕ)) :=
    (h.comm₂₃.symm.pow_pow _ _).mul_left (h.comm₂₄.symm.pow_pow _ _)
  rw [hlhs, hrhs, ← mul_assoc, c1.eq]
  calc a₁ ^ (v 3 : ℕ) * (a₂ ^ (v 0 : ℕ) * a₃ ^ (v 1 : ℕ) * a₄ ^ (v 2 : ℕ)) * a₂ ^ (v 3 : ℕ)
      = a₁ ^ (v 3 : ℕ) * a₂ ^ (v 0 : ℕ) * ((a₃ ^ (v 1 : ℕ) * a₄ ^ (v 2 : ℕ)) * a₂ ^ (v 3 : ℕ)) := by
        simp only [mul_assoc]
    _ = a₁ ^ (v 3 : ℕ) * a₂ ^ (v 0 : ℕ) * (a₂ ^ (v 3 : ℕ) * (a₃ ^ (v 1 : ℕ) * a₄ ^ (v 2 : ℕ))) := by
        rw [c2.eq]
    _ = a₁ ^ (v 3 : ℕ) * (a₂ ^ (v 0 : ℕ) * a₂ ^ (v 3 : ℕ)) * a₃ ^ (v 1 : ℕ) * a₄ ^ (v 2 : ℕ) := by
        simp only [mul_assoc]

theorem conj_pow_eq (k : ℕ) :
    n ^ k * a₁ * (n ^ k)⁻¹ = e16Prod a₁ a₂ a₃ a₄ (e16Shift^[k] ![1, 0, 0, 0]) := by
  induction k with
  | zero => simp [e16Prod]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← h.conj_e16Prod, ← ih, pow_succ', mul_inv_rev]
    group

theorem prod_ne_one (v : Fin 4 → Fin 2) (hv : v ≠ 0) : e16Prod a₁ a₂ a₃ a₄ v ≠ 1 := by
  obtain ⟨k, hk⟩ := exists_iterate_e16Shift v hv
  rw [← hk, ← h.conj_pow_eq]
  exact fun e => h.ne_one (conj_eq_one_iff.mp e)

end E16Datum

end Datum

section Lift

variable {X J : Type*} [Group X] [Group J] {φ : J →* X} {a₁ a₂ a₃ a₄ n : X}

theorem E16Datum.exists_lift (h : E16Datum a₁ a₂ a₃ a₄ n) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) :
    ∃ b₁ b₂ b₃ b₄ : J, φ b₁ = a₁ ∧ φ b₂ = a₂ ∧ φ b₃ = a₃ ∧ φ b₄ = a₄ ∧ b₁ ^ 2 = 1 ∧
      b₂ ^ 2 = 1 ∧ b₃ ^ 2 = 1 ∧ b₄ ^ 2 = 1 ∧ Commute b₁ b₂ ∧ Commute b₁ b₃ ∧
      Commute b₁ b₄ ∧ Commute b₂ b₃ ∧ Commute b₂ b₄ ∧ Commute b₃ b₄ := by
  obtain ⟨b₁, hb₁⟩ := hφ a₁
  obtain ⟨m, hm⟩ := hφ n
  obtain ⟨b₂, hb₂def⟩ : ∃ b₂, b₂ = m * b₁ * m⁻¹ := ⟨_, rfl⟩
  obtain ⟨b₃, hb₃def⟩ : ∃ b₃, b₃ = m * b₂ * m⁻¹ := ⟨_, rfl⟩
  obtain ⟨b₄, hb₄def⟩ : ∃ b₄, b₄ = m * b₃ * m⁻¹ := ⟨_, rfl⟩
  have hb₂ : φ b₂ = a₂ := by rw [hb₂def, map_mul, map_mul, map_inv, hm, hb₁, h.conj₁]
  have hb₃ : φ b₃ = a₃ := by rw [hb₃def, map_mul, map_mul, map_inv, hm, hb₂, h.conj₂]
  have hb₄ : φ b₄ = a₄ := by rw [hb₄def, map_mul, map_mul, map_inv, hm, hb₃, h.conj₃]
  obtain ⟨k, hkdef⟩ : ∃ k, k = (b₁ * b₂)⁻¹ * (m * b₄ * m⁻¹) := ⟨_, rfl⟩
  have hk : φ k = 1 := by
    rw [hkdef, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, hm, hb₁, hb₂, hb₄,
      h.conj₄, inv_mul_cancel]
  have Zk : k ∈ Subgroup.center J := hker hk
  have hmb₄ : m * b₄ * m⁻¹ = b₁ * b₂ * k := by rw [hkdef, mul_inv_cancel_left]
  have hZ : ∀ {x y : J}, Commute (φ x) (φ y) → ⁅x, y⁆ ∈ Subgroup.center J := fun hxy =>
    commutator_mem_center_of_commute hker hxy
  have Z12 : ⁅b₁, b₂⁆ ∈ Subgroup.center J := hZ (by rw [hb₁, hb₂]; exact h.comm₁₂)
  have Z13 : ⁅b₁, b₃⁆ ∈ Subgroup.center J := hZ (by rw [hb₁, hb₃]; exact h.comm₁₃)
  have Z14 : ⁅b₁, b₄⁆ ∈ Subgroup.center J := hZ (by rw [hb₁, hb₄]; exact h.comm₁₄)
  have Z23 : ⁅b₂, b₃⁆ ∈ Subgroup.center J := hZ (by rw [hb₂, hb₃]; exact h.comm₂₃)
  have Z24 : ⁅b₂, b₄⁆ ∈ Subgroup.center J := hZ (by rw [hb₂, hb₄]; exact h.comm₂₄)
  have Z34 : ⁅b₃, b₄⁆ ∈ Subgroup.center J := hZ (by rw [hb₃, hb₄]; exact h.comm₃₄)
  have Z32 : ⁅b₃, b₂⁆ ∈ Subgroup.center J := hZ (by rw [hb₂, hb₃]; exact h.comm₂₃.symm)
  have Z42 : ⁅b₄, b₂⁆ ∈ Subgroup.center J := hZ (by rw [hb₂, hb₄]; exact h.comm₂₄.symm)
  have Z22 : ⁅b₂, b₂⁆ ∈ Subgroup.center J := by
    rw [commutatorElement_self]; exact Subgroup.one_mem _
  have hconj : ∀ x y : J, ⁅x, y⁆ ∈ Subgroup.center J → ⁅m * x * m⁻¹, m * y * m⁻¹⁆ = ⁅x, y⁆ :=
    fun x y hxy => by
      rw [← conjugate_commutatorElement, Subgroup.mem_center_iff.mp hxy m, mul_inv_cancel_right]
  have E1 : ⁅b₂, b₃⁆ = ⁅b₁, b₂⁆ := by
    have := hconj b₁ b₂ Z12
    rwa [← hb₂def, ← hb₃def] at this
  have E2 : ⁅b₃, b₄⁆ = ⁅b₂, b₃⁆ := by
    have := hconj b₂ b₃ Z23
    rwa [← hb₃def, ← hb₄def] at this
  have E3 : ⁅b₂, b₄⁆ = ⁅b₁, b₃⁆ := by
    have := hconj b₁ b₃ Z13
    rwa [← hb₂def, ← hb₄def] at this
  have F1 : ⁅b₂, b₁ * b₂ * k⁆ = ⁅b₁, b₄⁆ := by
    have := hconj b₁ b₄ Z14
    rwa [← hb₂def, hmb₄] at this
  have F2 : ⁅b₃, b₁ * b₂ * k⁆ = ⁅b₂, b₄⁆ := by
    have := hconj b₂ b₄ Z24
    rwa [← hb₃def, hmb₄] at this
  have F3 : ⁅b₄, b₁ * b₂ * k⁆ = ⁅b₃, b₄⁆ := by
    have := hconj b₃ b₄ Z34
    rwa [← hb₄def, hmb₄] at this
  rw [commutator_mul_central_right Zk, commutator_mul_right_of_central Z22,
    commutatorElement_self, mul_one, ← commutatorElement_inv] at F1
  rw [commutator_mul_central_right Zk, commutator_mul_right_of_central Z32,
    ← commutatorElement_inv, ← commutatorElement_inv b₂ b₃, E3, E1] at F2
  rw [commutator_mul_central_right Zk, commutator_mul_right_of_central Z42,
    ← commutatorElement_inv, ← commutatorElement_inv b₂ b₄, E3, E2, E1] at F3
  set Z := Subgroup.center J
  set α : Z := ⟨_, Z12⟩
  set β : Z := ⟨_, Z13⟩
  set γ : Z := ⟨_, Z14⟩
  have G1 : α⁻¹ = γ := Subtype.ext F1
  have G2 : β⁻¹ * α⁻¹ = β := Subtype.ext F2
  have G3 : γ⁻¹ * β⁻¹ = α := Subtype.ext F3
  have hβ : β = 1 := by
    rw [← G1, inv_inv] at G3
    have : α * β⁻¹ = α * 1 := by rw [G3, mul_one]
    exact inv_eq_one.mp (mul_left_cancel this)
  have hα : α = 1 := by
    rw [hβ, inv_one, one_mul] at G2
    exact inv_eq_one.mp G2
  have hγ : γ = 1 := by rw [← G1, hα, inv_one]
  have c12 : ⁅b₁, b₂⁆ = 1 := congrArg Subtype.val hα
  have c13 : ⁅b₁, b₃⁆ = 1 := congrArg Subtype.val hβ
  have c14 : ⁅b₁, b₄⁆ = 1 := congrArg Subtype.val hγ
  have h12 : Commute b₁ b₂ := commutatorElement_eq_one_iff_commute.mp c12
  have h13 : Commute b₁ b₃ := commutatorElement_eq_one_iff_commute.mp c13
  have h14 : Commute b₁ b₄ := commutatorElement_eq_one_iff_commute.mp c14
  have h23 : Commute b₂ b₃ := commutatorElement_eq_one_iff_commute.mp (E1.trans c12)
  have h24 : Commute b₂ b₄ := commutatorElement_eq_one_iff_commute.mp (E3.trans c13)
  have h34 : Commute b₃ b₄ := commutatorElement_eq_one_iff_commute.mp ((E2.trans E1).trans c12)
  have Zs₁ : b₁ ^ 2 ∈ Z := hker (by rw [MonoidHom.mem_ker, map_pow, hb₁, h.sq])
  have hsq : ∀ {x : J}, x ^ 2 ∈ Z → (m * x * m⁻¹) ^ 2 = x ^ 2 := fun hx => by
    rw [conj_pow, Subgroup.mem_center_iff.mp hx m, mul_inv_cancel_right]
  have s₂ : b₂ ^ 2 = b₁ ^ 2 := by rw [hb₂def]; exact hsq Zs₁
  have s₃ : b₃ ^ 2 = b₁ ^ 2 := by rw [hb₃def, hsq (by rw [s₂]; exact Zs₁), s₂]
  have s₄ : b₄ ^ 2 = b₁ ^ 2 := by rw [hb₄def, hsq (by rw [s₃]; exact Zs₁), s₃]
  have hkc : ∀ x : J, Commute x k := fun x => Subgroup.mem_center_iff.mp Zk x
  have key : b₁ ^ 2 * k ^ 2 = 1 := by
    have e₁ : (m * b₄ * m⁻¹) ^ 2 = b₁ ^ 2 := by rw [hsq (by rw [s₄]; exact Zs₁), s₄]
    rw [hmb₄, (hkc _).mul_pow, h12.mul_pow, s₂] at e₁
    set S : Z := ⟨_, Zs₁⟩
    set K : Z := ⟨_, Zk⟩
    have e₂ : S * S * K ^ 2 = S := Subtype.ext e₁
    have e₃ : S * K ^ 2 = 1 := by
      have : S * (S * K ^ 2) = S * 1 := by rw [← mul_assoc, e₂, mul_one]
      exact mul_left_cancel this
    exact congrArg Subtype.val e₃
  have hinv : ∀ {x : J}, x ^ 2 = b₁ ^ 2 → (x * k) ^ 2 = 1 := fun {x} hx => by
    rw [(hkc x).mul_pow, hx, key]
  refine ⟨b₁ * k, b₂ * k, b₃ * k, b₄ * k, ?_, ?_, ?_, ?_, hinv rfl, hinv s₂, hinv s₃, hinv s₄,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, hk, mul_one, hb₁]
  · rw [map_mul, hk, mul_one, hb₂]
  · rw [map_mul, hk, mul_one, hb₃]
  · rw [map_mul, hk, mul_one, hb₄]
  · exact (h12.mul_right (hkc b₁)).mul_left ((hkc b₂).symm.mul_right (Commute.refl k))
  · exact (h13.mul_right (hkc b₁)).mul_left ((hkc b₃).symm.mul_right (Commute.refl k))
  · exact (h14.mul_right (hkc b₁)).mul_left ((hkc b₄).symm.mul_right (Commute.refl k))
  · exact (h23.mul_right (hkc b₂)).mul_left ((hkc b₃).symm.mul_right (Commute.refl k))
  · exact (h24.mul_right (hkc b₂)).mul_left ((hkc b₄).symm.mul_right (Commute.refl k))
  · exact (h34.mul_right (hkc b₃)).mul_left ((hkc b₄).symm.mul_right (Commute.refl k))

theorem E16Datum.five_le_pRank [Finite J] (h : E16Datum a₁ a₂ a₃ a₄ n)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center J) {z : J} (hz : φ z = 1)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) : 5 ≤ CFSG.pRank 2 J := by
  obtain ⟨b₁, b₂, b₃, b₄, hb₁, hb₂, hb₃, hb₄, s₁, s₂, s₃, s₄, c₁₂, c₁₃, c₁₄, c₂₃, c₂₄, c₃₄⟩ :=
    h.exists_lift hφ hker
  have hzc : ∀ x : J, Commute x z := fun x => Subgroup.mem_center_iff.mp (hker hz) x
  refine le_pRank_two_of_independent ![b₁, b₂, b₃, b₄, z] ?_ ?_ ?_
  · intro i
    fin_cases i <;> simpa
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four] <;>
      first
        | exact Commute.refl _ | exact c₁₂ | exact c₁₂.symm | exact c₁₃ | exact c₁₃.symm
        | exact c₁₄ | exact c₁₄.symm | exact c₂₃ | exact c₂₃.symm | exact c₂₄ | exact c₂₄.symm
        | exact c₃₄ | exact c₃₄.symm | exact hzc _ | exact (hzc _).symm
  · intro v hv hprod
    have hform : (List.ofFn fun i => (![b₁, b₂, b₃, b₄, z] : Fin 5 → J) i ^ (v i : ℕ)).prod =
        b₁ ^ (v 0 : ℕ) * (b₂ ^ (v 1 : ℕ) * (b₃ ^ (v 2 : ℕ) * (b₄ ^ (v 3 : ℕ) *
          z ^ (v 4 : ℕ)))) := by
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
      rfl
    rw [hform] at hprod
    have himg := congrArg φ hprod
    simp only [map_mul, map_pow, map_one, hb₁, hb₂, hb₃, hb₄, hz, one_pow, mul_one] at himg
    by_cases h0 : (![v 0, v 1, v 2, v 3] : Fin 4 → Fin 2) = 0
    · have h0' : ∀ i : Fin 4, (![v 0, v 1, v 2, v 3] : Fin 4 → Fin 2) i = 0 := fun i => by
        rw [h0]; rfl
      have e0 : v 0 = 0 := h0' 0
      have e1 : v 1 = 0 := h0' 1
      have e2 : v 2 = 0 := h0' 2
      have e3 : v 3 = 0 := h0' 3
      have h4 : v 4 ≠ 0 := by
        intro h4
        apply hv
        funext i
        fin_cases i
        exacts [e0, e1, e2, e3, h4]
      have h4' : v 4 = 1 := by
        revert h4; generalize v 4 = w; revert w; decide
      rw [e0, e1, e2, e3, h4'] at hprod
      simp only [Fin.isValue, Fin.val_zero, pow_zero, Fin.val_one, pow_one, one_mul] at hprod
      exact hz1 hprod
    · refine h.prod_ne_one _ h0 ?_
      change a₁ ^ (v 0 : ℕ) * a₂ ^ (v 1 : ℕ) * a₃ ^ (v 2 : ℕ) * a₄ ^ (v 3 : ℕ) = 1
      simpa only [mul_assoc] using himg

end Lift

theorem noRankThreeTwoCover_of_e16Datum {X : Type} [Group X] {a₁ a₂ a₃ a₄ n : X}
    (h : E16Datum a₁ a₂ a₃ a₄ n) :
    NoRankThreeTwoCover X := by
  intro J _ _ ⟨_, hZ2, hZnt, ⟨e⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : J →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center J := fun x hx => by
    rw [MonoidHom.mem_ker] at hx
    have hx' : (QuotientGroup.mk' (Subgroup.center J)) x = 1 :=
      e.injective (by rw [map_one]; exact hx)
    exact (QuotientGroup.eq_one_iff x).mp hx'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (two_dvd_card_center hZ2 hZnt)
  have hz2 : (z : J) ^ 2 = 1 := by
    rw [← Subgroup.orderOf_coe] at hz
    rw [← hz]
    exact pow_orderOf_eq_one _
  have hz1 : (z : J) ≠ 1 := by
    intro e1
    rw [← Subgroup.orderOf_coe, e1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzk : ψ z = 1 := by
    change e (QuotientGroup.mk (z : J)) = 1
    rw [(QuotientGroup.eq_one_iff (z : J)).mpr z.2, map_one]
  have := h.five_le_pRank hψ hker hzk hz1 hz2
  omega

section Native

theorem e16Datum_of_check {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
    [Inhabited M] [Inhabited V] (D : E8Data) (h : e16Check O D = true) :
    ∃ a₁ a₂ a₃ a₄ n : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      E16Datum a₁ a₂ a₃ a₄ n := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold e16Check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hprog⟩, hrx⟩, hrh⟩, hoh⟩, hX2⟩, hHo⟩, hXt⟩, hc12⟩, hc13⟩, hc14⟩,
    hconj⟩ := h
  set R := O.regsOf D.seedA D.seedB D.nregs D.prog
  obtain ⟨wX, mX⟩ := Sp.regsOf_ok hprog hrx
  obtain ⟨wH, mH⟩ := Sp.regsOf_ok hprog hrh
  have eX := Sp.pow_eq_one_of_check wX hX2
  have eH := Sp.pow_eq_one_of_check wH hHo
  let x := unitOf S mX two_ne_zero eX
  let g := unitOf S mH hoh.ne' eH
  have fx : valHom S x = Sp.toMat R[D.rx]! := valHom_unitOf S _ _ _
  have fg : valHom S g = Sp.toMat R[D.rh]! := valHom_unitOf S _ _ _
  have hg : g ^ D.oh = 1 := unitOf_pow S mH _ eH
  set H' := O.pow R[D.rh]! (D.oh - 1)
  have wH' : Sp.WF H' := (Sp.pow_spec wH _).1
  have fgi : valHom S g⁻¹ = Sp.toMat H' := by
    rw [valHom_inv_of_pow S hoh.ne' hg, fg, (Sp.pow_spec wH _).2]
  set X₂ := O.mul (O.mul R[D.rh]! R[D.rx]!) H'
  set X₃ := O.mul (O.mul R[D.rh]! X₂) H'
  set X₄ := O.mul (O.mul R[D.rh]! X₃) H'
  have wX₂ : Sp.WF X₂ := Sp.mul_wf (Sp.mul_wf wH wX) wH'
  have wX₃ : Sp.WF X₃ := Sp.mul_wf (Sp.mul_wf wH wX₂) wH'
  have wX₄ : Sp.WF X₄ := Sp.mul_wf (Sp.mul_wf wH wX₃) wH'
  have f₂ : valHom S (g * x * g⁻¹) = Sp.toMat X₂ := by
    rw [map_mul, map_mul, fg, fx, fgi, Sp.toMat_mul (Sp.mul_wf wH wX) wH', Sp.toMat_mul wH wX]
  have f₃ : valHom S (g * (g * x * g⁻¹) * g⁻¹) = Sp.toMat X₃ := by
    rw [map_mul, map_mul, fg, f₂, fgi, Sp.toMat_mul (Sp.mul_wf wH wX₂) wH', Sp.toMat_mul wH wX₂]
  have f₄ : valHom S (g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹) = Sp.toMat X₄ := by
    rw [map_mul, map_mul, fg, f₃, fgi, Sp.toMat_mul (Sp.mul_wf wH wX₃) wH', Sp.toMat_mul wH wX₃]
  have hcomm : ∀ {y : S ˣ} {Y : M}, Sp.WF Y → valHom S y = Sp.toMat Y →
      O.eq (O.mul R[D.rx]! Y) (O.mul Y R[D.rx]!) = true → x * y = y * x := by
    intro y Y wY fy hc
    apply valHom_injective S
    rw [map_mul (valHom S) x, map_mul (valHom S) y x, fx, fy, ← Sp.toMat_mul wX wY,
      ← Sp.toMat_mul wY wX]
    exact Sp.toMat_eq (Sp.mul_wf wX wY) (Sp.mul_wf wY wX) hc
  refine ⟨x, g * x * g⁻¹, g * (g * x * g⁻¹) * g⁻¹, g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹, g,
    ⟨?_, unitOf_pow S mX _ eX, hcomm wX₂ f₂ hc12, hcomm wX₃ f₃ hc13, hcomm wX₄ f₄ hc14, rfl,
      rfl, rfl, ?_⟩⟩
  · intro h1
    apply Sp.toVec_ne hXt
    rw [Sp.toVec_vmul (Sp.unit_wf _) wX, ← fx, h1, map_one, Matrix.vecMul_one]
  · rw [mul_inv_eq_iff_eq_mul]
    apply valHom_injective S
    rw [map_mul (valHom S) g, map_mul (valHom S) _ g, map_mul (valHom S) x, fg, f₄, fx, f₂]
    have := Sp.toMat_of_conjOK wH wX₄ (Sp.mul_wf wX wX₂) hconj
    rwa [Sp.toMat_mul wX wX₂] at this

theorem j3_e16_check : e16Check (ops2 80) j3E16Data = true :=
  Certificates.certificate8095

theorem j3_e16Datum :
    ∃ a₁ a₂ a₃ a₄ n : NativeSporadic.J3, E16Datum a₁ a₂ a₃ a₄ n :=
  e16Datum_of_check (spec2 80) j3E16Data j3_e16_check

end Native

end SporadicTwoCover

open SporadicTwoCover

theorem noRankThreeTwoCover_j3 :
    NoRankThreeTwoCover (Spor .J3) := by
  obtain ⟨a₁, a₂, a₃, a₄, n, h⟩ := j3_e16Datum
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have h₀ : NoRankThreeTwoCover NativeSporadic.J3 := noRankThreeTwoCover_of_e16Datum h
  have e' : NativeSporadic.J3 ≃* Spor .J3 := e
  exact noRankThreeTwoCover_of_mulEquiv (X := NativeSporadic.J3) (Y := Spor .J3) e' h₀

end CFSG.RankThree.PartTwo.Sec4.Census
