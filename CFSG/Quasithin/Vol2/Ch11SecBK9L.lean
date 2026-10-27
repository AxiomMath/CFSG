module

public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.Quasithin.Vol2.Ch11SecBK9J

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix QuadraticMap
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply quadMinus quadMinus_apply)

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem pow_four_eq (hK : Nat.card K = 4) (a : K) : a ^ 4 = a := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card a
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem tr_sq (hK : Nat.card K = 4) (a : K) : tr (a ^ 2) = tr a := by
  unfold tr
  rw [← pow_mul, show 2 * 2 = 4 by norm_num, pow_four_eq hK]
  ring

theorem eq_zero_or_one_of_tr {s : K} (h : tr s = 0) : s = 0 ∨ s = 1 := by
  unfold tr at h
  have h' : s * (1 + s) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · right
    have := eq_neg_of_add_eq_zero_right h1
    rwa [CharTwo.neg_eq] at this

theorem tr_qOf (hK : Nat.card K = 4) (e a : Fin 2 ⊕ Fin 2 → K) :
    tr (qOf e a) = tr (quadPlus 2 K (e + a)) + tr (quadPlus 2 K e) := by
  have h := isSpForm_quadPlus (K := K) e a
  simp only [polar] at h
  rw [qOf_apply, show quadPlus 2 K (e + a) = quadPlus 2 K e + quadPlus 2 K a + spB K e a by
    linear_combination h, tr_add, tr_add, tr_add, tr_sq hK]
  have h2 : tr (quadPlus 2 K e) + tr (quadPlus 2 K e) = 0 := CharTwo.add_self_eq_zero _
  linear_combination -h2

theorem exists_orbit_trv (hK : Nat.card K = 4) {e a : Fin 2 ⊕ Fin 2 → K}
    (ha : tr (qOf e a) = 0) : ∃ γ : ↥(StatedSp 2 K), mat 2 K γ *ᵥ e + bm hK γ = e + a := by
  obtain ⟨ω, hω, -⟩ := exists_omega hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have key : ∀ t : K, mat 2 K (K7.trv a t) *ᵥ e + bm hK (K7.trv a t) =
      e + (t * qOf e a ^ 2 + t ^ 2) • a := fun t => by
    rw [K7.trv_mulVec, bm_trv, add_assoc, ← add_smul, qOf_apply, CharTwo.add_sq,
      ← pow_mul, show 2 * 2 = 4 by norm_num, pow_four_eq hK, K7.bil_comm]
    congr 2
    ring
  rcases eq_zero_or_one_of_tr ha with h0 | h1
  · refine ⟨K7.trv a 1, ?_⟩
    rw [key, h0]
    simp
  · refine ⟨K7.trv a ω, ?_⟩
    rw [key, h1, one_pow, mul_one, hω, show ω + (ω + 1) = 1 by linear_combination ω * h2,
      one_smul]

theorem qOf_act (hK : Nat.card K = 4) (γ : ↥(StatedSp 2 K)) (e x : Fin 2 ⊕ Fin 2 → K) :
    qOf (mat 2 K γ *ᵥ e + bm hK γ) (mat 2 K γ *ᵥ x) = qOf e x := by
  rw [← qOf_comp hK γ e]
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, linEquiv_apply]
  rw [KGNat.mat_inv_mulVec]

@[expose] noncomputable def qOfIso (hK : Nat.card K = 4) (γ : ↥(StatedSp 2 K))
    (e : Fin 2 ⊕ Fin 2 → K) : (qOf e).IsometryEquiv (qOf (mat 2 K γ *ᵥ e + bm hK γ)) where
  toLinearEquiv := linEquiv γ
  map_app' x := qOf_act hK γ e x

@[expose] def eMinus (ω : K) : Fin 2 ⊕ Fin 2 → K := KGNat.vec4 1 0 ω 0

@[expose] def minusIdx : (Fin 1 ⊕ Fin 1 ⊕ Fin 2) ≃ (Fin 2 ⊕ Fin 2) where
  toFun := Sum.elim (fun _ => .inl 1) (Sum.elim (fun _ => .inr 1) ![.inr 0, .inl 0])
  invFun := Sum.elim ![.inr (.inr 1), .inl 0] ![.inr (.inr 0), .inr (.inl 0)]
  left_inv := by decide
  right_inv := by decide

theorem qOf_eMinus_apply {ω : K} (hω : ω ^ 2 = ω + 1) (x : Fin 2 ⊕ Fin 2 → K) :
    qOf (eMinus ω) x = x (.inl 1) * x (.inr 1) + x (.inr 0) ^ 2 + 1 * x (.inr 0) * x (.inl 0) +
      (ω + 1) * x (.inl 0) ^ 2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [qOf_apply, quadPlus_apply, KGNat.toBilin'_spJ_apply]
  simp only [Fin.sum_univ_two, eMinus, KGNat.vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  linear_combination (x (.inl 0) ^ 2) * hω + (-(ω * x (.inr 0) * x (.inl 0))) * h2

theorem quadMinus_minusIdx {ω : K} (x : Fin 2 ⊕ Fin 2 → K) :
    quadMinus 2 K 1 (ω + 1) (LinearEquiv.funCongrLeft K K minusIdx x) =
      x (.inl 1) * x (.inr 1) + x (.inr 0) ^ 2 + 1 * x (.inr 0) * x (.inl 0) +
        (ω + 1) * x (.inl 0) ^ 2 := by
  rw [quadMinus_apply]
  have : Unique (Fin (2 - 1)) := inferInstanceAs (Unique (Fin 1))
  rw [Fintype.sum_unique]
  rfl

@[expose] noncomputable def qOfMinusIso {ω : K} (hω : ω ^ 2 = ω + 1) :
    (qOf (eMinus ω)).IsometryEquiv (quadMinus 2 K 1 (ω + 1)) where
  toLinearEquiv := LinearEquiv.funCongrLeft K K minusIdx
  map_app' x := by
    rw [qOf_eMinus_apply hω]
    exact quadMinus_minusIdx x

theorem irreducible_minus (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 = ω + 1) :
    ∀ s : K, s ^ 2 + 1 * s + (ω + 1) ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_add] at hω
    exact zero_ne_one hω
  have hω1 : ω + 1 ≠ 0 := by
    intro h
    have : ω = 1 := by
      have := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at this
    rw [this, one_pow, CharTwo.add_self_eq_zero] at hω
    exact one_ne_zero hω
  intro s hs
  have e : s ^ 2 + 1 * s + (ω + 1) = tr s + (ω + 1) := by
    unfold tr
    ring
  rw [e] at hs
  rcases tr_eq_zero_or_one hK s with h | h <;> rw [h] at hs
  · rw [zero_add] at hs
    exact hω1 hs
  · apply hω0
    linear_combination hs - h2

theorem not_isPlusType_qOf_eMinus (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 = ω + 1) :
    ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (qOf (eMinus ω)) := fun h =>
  CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := 2) (by norm_num)
    (irreducible_minus hK hω)
    ((CFSG.GroupTheory.WeirSylow.isPlusType_congr (qOfMinusIso hω)).mp h)

theorem quadPlus_eMinus {ω : K} : quadPlus 2 K (eMinus ω) = ω := by
  rw [quadPlus_apply]
  simp [Fin.sum_univ_two, eMinus, KGNat.vec4]

theorem exists_orbit_of_tr (hK : Nat.card K = 4) {e e' : Fin 2 ⊕ Fin 2 → K}
    (h : tr (quadPlus 2 K e') = tr (quadPlus 2 K e)) :
    ∃ γ : ↥(StatedSp 2 K), mat 2 K γ *ᵥ e + bm hK γ = e' := by
  have ha : tr (qOf e (e' - e)) = 0 := by
    rw [tr_qOf hK, add_sub_cancel, h, CharTwo.add_self_eq_zero]
  obtain ⟨γ, hγ⟩ := exists_orbit_trv hK ha
  exact ⟨γ, by rw [hγ, add_sub_cancel]⟩

theorem isPlusType_qOf_iff (hK : Nat.card K = 4) (e : Fin 2 ⊕ Fin 2 → K) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (qOf e) ↔ tr (quadPlus 2 K e) = 0 := by
  obtain ⟨ω, hω, -⟩ := exists_omega hK
  rcases tr_eq_zero_or_one hK (quadPlus 2 K e) with h | h
  · refine iff_of_true ?_ h
    obtain ⟨γ, hγ⟩ := exists_orbit_of_tr hK (e := 0) (e' := e)
      (by rw [h, QuadraticMap.map_zero, tr_zero])
    rw [← hγ]
    refine (CFSG.GroupTheory.WeirSylow.isPlusType_congr (qOfIso hK γ 0)).mp ?_
    rw [qOf_zero]
    exact CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 2
  · refine iff_of_false (fun hp => ?_) (by rw [h]; exact one_ne_zero)
    obtain ⟨γ, hγ⟩ := exists_orbit_of_tr hK (e := e) (e' := eMinus ω)
      (by rw [quadPlus_eMinus, tr_omega hω, h])
    apply not_isPlusType_qOf_eMinus hK hω
    rw [← hγ]
    exact (CFSG.GroupTheory.WeirSylow.isPlusType_congr (qOfIso hK γ e)).mp hp

theorem exists_orbit_iff (hK : Nat.card K = 4) (e e' : Fin 2 ⊕ Fin 2 → K) :
    (∃ γ : ↥(StatedSp 2 K), mat 2 K γ *ᵥ e + bm hK γ = e') ↔
      tr (quadPlus 2 K e') = tr (quadPlus 2 K e) := by
  refine ⟨fun ⟨γ, hγ⟩ => ?_, exists_orbit_of_tr hK⟩
  have hiff := CFSG.GroupTheory.WeirSylow.isPlusType_congr (qOfIso hK γ e)
  rw [hγ, isPlusType_qOf_iff hK, isPlusType_qOf_iff hK] at hiff
  rcases tr_eq_zero_or_one hK (quadPlus 2 K e) with h | h <;>
    rcases tr_eq_zero_or_one hK (quadPlus 2 K e') with h' | h' <;> rw [h, h'] at hiff ⊢
  · exact absurd (hiff.mp rfl) one_ne_zero
  · exact absurd (hiff.mpr rfl) one_ne_zero

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
