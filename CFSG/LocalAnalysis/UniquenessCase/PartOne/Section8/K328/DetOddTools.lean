module

import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedSLPerfect
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Leaves
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)

open Matrix
open CFSG.Open
open scoped Finset

open scoped commutatorElement

private theorem k328de8_charP_two_of_card_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  have _ : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, ⟨m, hp, hcard⟩⟩ := FiniteField.card' K
  have hpn : p ^ (m : ℕ) = 2 ^ n := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
  have hdiv : p ∣ 2 ^ n := by rw [← hpn]; exact dvd_pow_self p m.ne_zero
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdiv)
  rw [hp2] at hchar
  exact hchar

private theorem k328de8_pullback {Y M : Type} [Group Y] [Group M] (e : Y ≃* M)
    (A' : Subgroup M) (hcomm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a)
    (hsq : ∀ a ∈ A', a ^ 2 = 1) :
    ∃ A : Subgroup Y, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧
      Nat.card A = Nat.card A' := by
  refine ⟨A'.map e.symm.toMonoidHom, ?_, ?_, Subgroup.card_map_of_injective e.symm.injective⟩
  · rintro a ha b hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul, hcomm a' ha' b' hb']
  · rintro a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    rw [← map_pow, hsq a' ha', map_one]


private abbrev k328de8_E02 {K : Type} [Field K] [CharP K 2]  : Matrix (Fin 3) (Fin 3) K := Matrix.single 0 2 (1:K)
private abbrev k328de8_E12 {K : Type} [Field K] [CharP K 2]  : Matrix (Fin 3) (Fin 3) K := Matrix.single 1 2 (1:K)

private def k328de8_tm {K : Type} [Field K] [CharP K 2]  (a : K) (b : ZMod 2) : Matrix (Fin 3) (Fin 3) K :=
  1 + a • k328de8_E02 + (ZMod.cast (R := K) b) • k328de8_E12

private theorem k328de8_tm_det {K : Type} [Field K] [CharP K 2]  (a : K) (b : ZMod 2) : (k328de8_tm a b).det = 1 := by
  rw [k328de8_tm, Matrix.det_fin_three]
  simp [k328de8_E02, k328de8_E12, Matrix.single]

private theorem k328de8_tm_mul {K : Type} [Field K] [CharP K 2]  (a a' : K) (b b' : ZMod 2) :
    k328de8_tm a b * k328de8_tm a' b' = k328de8_tm (a + a') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328de8_tm, k328de8_E02, k328de8_E12, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.add_apply, Matrix.one_apply, Matrix.single] <;>
    ring

private theorem k328de8_tm_zero {K : Type} [Field K] [CharP K 2]  : (k328de8_tm (K := K) 0 0 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328de8_tm, k328de8_E02, k328de8_E12, Matrix.add_apply, Matrix.single,
      ZMod.cast_zero]

private def k328de8_TM {K : Type} [Field K] [CharP K 2]  (a : K) (b : ZMod 2) : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero (k328de8_tm a b) (by rw [k328de8_tm_det]; exact one_ne_zero)

private theorem k328de8_TM_mul {K : Type} [Field K] [CharP K 2]  (a a' : K) (b b' : ZMod 2) :
    k328de8_TM a b * k328de8_TM a' b' = k328de8_TM (a + a') (b + b') := by
  apply GeneralLinearGroup.ext
  intro i j
  simp only [k328de8_TM, Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, k328de8_tm_mul]

private theorem k328de8_TM_one {K : Type} [Field K] [CharP K 2]  : k328de8_TM (K := K) 0 0 = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  simp only [k328de8_TM, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, k328de8_tm_zero]
  rfl

private theorem k328de8_TM_injective {K : Type} [Field K] [CharP K 2]  : Function.Injective (fun p : K × ZMod 2 => k328de8_TM p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hm : k328de8_tm a b = k328de8_tm c d := by
    simpa [k328de8_TM, Matrix.GeneralLinearGroup.val_mkOfDetNeZero] using
      congr_arg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h
  have h02 : a = c := by
    have := congr_fun (congr_fun hm 0) 2
    simpa [k328de8_tm, k328de8_E02, k328de8_E12, Matrix.single, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply] using this
  have h12 : (ZMod.cast (R := K) b) = (ZMod.cast (R := K) d) := by
    have := congr_fun (congr_fun hm 1) 2
    simpa [k328de8_tm, k328de8_E02, k328de8_E12, Matrix.single, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply] using this
  have hbd : b = d := (ZMod.castHom_injective (R := K)) (by simpa using h12)
  exact Prod.ext h02 hbd

private theorem k328de8_TM_sq {K : Type} [Field K] [CharP K 2]  (a : K) (b : ZMod 2) : k328de8_TM a b * k328de8_TM a b = 1 := by
  rw [k328de8_TM_mul]
  have h1 : a + a = 0 := by rw [← two_mul, CharTwo.two_eq_zero, zero_mul]
  have h2 : b + b = (0 : ZMod 2) := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [h1, h2, k328de8_TM_one]

private theorem k328de8_TM_mem {K : Type} [Field K] [CharP K 2]  (a : K) (b : ZMod 2) : k328de8_TM a b ∈ StatedSL 3 K :=
  Subgroup.subset_closure (show (k328de8_TM a b : Matrix (Fin 3) (Fin 3) K).det = 1 from by
    change (k328de8_tm a b).det = 1
    exact k328de8_tm_det a b)

private def k328de8_AH {K : Type} [Field K] [CharP K 2]  : Subgroup (GL (Fin 3) K) where
  carrier := Set.range fun p : K × ZMod 2 => k328de8_TM p.1 p.2
  one_mem' := ⟨(0, 0), k328de8_TM_one⟩
  mul_mem' := by
    rintro x y ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨(p.1 + q.1, p.2 + q.2), (k328de8_TM_mul p.1 q.1 p.2 q.2).symm⟩
  inv_mem' := by
    rintro x ⟨p, rfl⟩
    exact ⟨p, (mul_eq_one_iff_inv_eq.mp (k328de8_TM_sq p.1 p.2)).symm⟩

private theorem k328de8_AH_card {K : Type} [Field K] [CharP K 2]  (hK : Nat.card K = 4) :
    Nat.card (k328de8_AH : Subgroup (GL (Fin 3) K)) = 8 := by
  have hbij : Function.Bijective (fun p : K × ZMod 2 =>
      (⟨k328de8_TM p.1 p.2, ⟨p, rfl⟩⟩ : (k328de8_AH : Subgroup (GL (Fin 3) K)))) := by
    constructor
    · intro p q h
      exact k328de8_TM_injective (Subtype.ext_iff.mp h)
    · rintro ⟨x, hx⟩
      obtain ⟨p, rfl⟩ := hx
      exact ⟨p, rfl⟩
  have h1 : Nat.card (K × ZMod 2) = Nat.card (k328de8_AH : Subgroup (GL (Fin 3) K)) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [← h1, Nat.card_prod, Nat.card_zmod, hK]

private theorem k328de8_AH_comm {K : Type} [Field K] [CharP K 2]  : ∀ a ∈ (k328de8_AH : Subgroup (GL (Fin 3) K)),
    ∀ b ∈ (k328de8_AH : Subgroup (GL (Fin 3) K)), a * b = b * a := by
  rintro a ⟨p, rfl⟩ b ⟨q, rfl⟩
  rw [k328de8_TM_mul, k328de8_TM_mul, add_comm p.1 q.1, add_comm p.2 q.2]

private theorem k328de8_AH_sq {K : Type} [Field K] [CharP K 2]  : ∀ a ∈ (k328de8_AH : Subgroup (GL (Fin 3) K)), a ^ 2 = 1 := by
  rintro a ⟨p, rfl⟩
  rw [sq, k328de8_TM_sq]

private theorem k328de8_TM_scalar_zero {K : Type} [Field K] [CharP K 2]  {a : K} {b : ZMod 2} (h : k328de8_TM a b ∈ StatedScalars (Fin 3) K) :
    a = 0 ∧ b = 0 := by
  rw [StatedScalars] at h
  obtain ⟨u, hu⟩ := h
  constructor
  · have h02 := congr_fun (congr_fun (congr_arg
        (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) hu) 0) 2
    simpa [k328de8_TM, GeneralLinearGroup.coe_scalar, Matrix.scalar,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero, k328de8_tm, k328de8_E02, k328de8_E12, Matrix.single,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h02.symm
  · have h12 := congr_fun (congr_fun (congr_arg
        (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) hu) 1) 2
    have h12' : (ZMod.cast (R := K) b) = 0 := by
      simpa [k328de8_TM, GeneralLinearGroup.coe_scalar, Matrix.scalar,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero, k328de8_tm, k328de8_E02, k328de8_E12, Matrix.single,
        Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h12.symm
    exact (ZMod.castHom_injective (R := K)) (by simpa using h12')

private theorem k328de8_AH_disjoint {K : Type} [Field K] [CharP K 2]  : (k328de8_AH : Subgroup (GL (Fin 3) K)) ⊓ StatedScalars (Fin 3) K = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxAH, hxS⟩
  obtain ⟨p, rfl⟩ := hxAH
  change k328de8_TM p.1 p.2 ∈ (⊥ : Subgroup (GL (Fin 3) K))
  rw [Subgroup.mem_bot]
  obtain ⟨ha, hb⟩ := k328de8_TM_scalar_zero hxS
  rw [ha, hb, k328de8_TM_one]

private theorem k328de8_PSL_exists {K : Type} [Field K] [CharP K 2]  (hK : Nat.card K = 4) :
    ∃ A : Subgroup (StatedProj (StatedSL 3 K)),
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ Nat.card A = 8 := by
  let H := StatedSL 3 K
  let S : Subgroup (GL (Fin 3) K) := StatedScalars (Fin 3) K
  have hAHle : (k328de8_AH : Subgroup (GL (Fin 3) K)) ≤ H := by
    rintro x ⟨p, rfl⟩
    exact k328de8_TM_mem p.1 p.2
  let AHH : Subgroup H := (k328de8_AH : Subgroup (GL (Fin 3) K)).subgroupOf H
  let N : Subgroup H := S.subgroupOf H
  let q : H →* StatedProj H := QuotientGroup.mk' N
  let Abar : Subgroup (StatedProj H) := AHH.map q
  have hdisj : AHH ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hxAH : (x : GL (Fin 3) K) ∈ (k328de8_AH : Subgroup (GL (Fin 3) K)) := hx1
    have hxS : (x : GL (Fin 3) K) ∈ S := hx2
    have h1 : (x : GL (Fin 3) K) ∈ (k328de8_AH : Subgroup (GL (Fin 3) K)) ⊓ S := ⟨hxAH, hxS⟩
    rw [k328de8_AH_disjoint] at h1
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  have hcardAHH : Nat.card AHH = 8 := by
    rw [show Nat.card AHH = Nat.card (k328de8_AH : Subgroup (GL (Fin 3) K)) from
      card_subgroupOf_of_le hAHle]
    exact k328de8_AH_card hK
  have hbot : N.subgroupOf AHH = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxN : (x : H) ∈ N := hx
    have h1 : (x : H) ∈ AHH ⊓ N := ⟨x.2, hxN⟩
    rw [hdisj] at h1
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  have hNrel : N.relIndex AHH = Nat.card AHH := by
    change (N.subgroupOf AHH).index = Nat.card AHH
    rw [hbot, Subgroup.index_bot]
  have hmap := Subgroup.relIndex_ker (K := AHH) q
  rw [QuotientGroup.ker_mk'] at hmap
  have hcardmap : Nat.card Abar = Nat.card AHH := by
    change Nat.card (AHH.map q) = Nat.card AHH
    rw [← hmap]
    exact hNrel
  have hcardAbar : Nat.card Abar = 8 := hcardmap.trans hcardAHH
  refine ⟨Abar, ?_, ?_, hcardAbar⟩
  · intro a ha b hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact k328de8_AH_comm _ (show (x : GL (Fin 3) K) ∈ (k328de8_AH : Subgroup (GL (Fin 3) K)) from hx)
      _ (show (y : GL (Fin 3) K) ∈ (k328de8_AH : Subgroup (GL (Fin 3) K)) from hy)
  · intro a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [← map_pow, ← map_one q]
    congr 1
    apply Subtype.ext
    change (x : GL (Fin 3) K) ^ 2 = 1
    exact k328de8_AH_sq _ (show (x : GL (Fin 3) K) ∈ (k328de8_AH : Subgroup (GL (Fin 3) K)) from hx)


private theorem k328de8_card_fixed8 {K : Type} [Field K] [CharP K 2]  (hK : Nat.card K = 64) : Nat.card {c : K // c ^ 8 = c} = 8 := by
  classical
  have _ : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hcard63 : Nat.card Kˣ = 63 := by
    rw [Nat.card_units, hK]
  have h7 : Nat.card {u : Kˣ // u ^ 7 = 1} = 7 := by
    have _ : Fintype Kˣ := Fintype.ofFinite Kˣ
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hsum := sum_card_orderOf_eq_card_pow_eq_one (G := Kˣ) (n := 7) (by norm_num)
    rw [← hsum]
    have h7dvd : 7 ∣ Fintype.card Kˣ := by rw [← Nat.card_eq_fintype_card, hcard63]; norm_num
    have h1 : #{x : Kˣ | orderOf x = 1} = 1 := by
      have hset : (Finset.filter (fun x : Kˣ => orderOf x = 1) Finset.univ) = {1} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [orderOf_eq_one_iff]
      rw [hset]
      simp
    have h2 : #{x : Kˣ | orderOf x = 7} = 6 := by
      rw [IsCyclic.card_orderOf_eq_totient (α := Kˣ) (d := 7) h7dvd]
      decide
    rw [show Nat.divisors 7 = {1, 7} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton, h1, h2]
  let z : {c : K // c ^ 8 = c} := ⟨0, by simp⟩
  let f : {c : K // c ^ 8 = c} → Option {u : Kˣ // u ^ 7 = 1} := fun c =>
    if hc : (c : K) = 0 then none
    else some ⟨Units.mk0 (c : K) hc, by
      rw [Units.ext_iff]
      show ((Units.mk0 (c : K) hc : Kˣ) : K) ^ 7 = 1
      rw [Units.val_mk0]
      have h8 : (c : K) ^ 8 = c := c.2
      let x : K := c.1
      have hx8 : x ^ 8 = x := c.2
      have h : x ^ 7 * x = x := by
        rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_add, pow_one] at hx8
        simpa using hx8
      have h7 : x ^ 7 = 1 := mul_right_cancel₀ hc (by simpa using h)
      simpa [x] using h7⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c1 c2 h
      by_cases h1 : (c1 : K) = 0 <;> by_cases h2 : (c2 : K) = 0
      · exact Subtype.ext (by rw [h1, h2])
      · simp only [f, dif_pos h1, dif_neg h2] at h
        exact absurd h (by simp)
      · simp only [f, dif_neg h1, dif_pos h2] at h
        exact absurd h (by simp)
      · simp only [f, dif_neg h1, dif_neg h2, Option.some.injEq] at h
        have hv : (c1 : K) = (c2 : K) := by
          have hh := congrArg (fun x : {u : Kˣ // u ^ 7 = 1} => (x.1 : K)) h
          simpa [Units.val_mk0] using hh
        exact Subtype.ext hv
    · rintro o
      cases o with
      | none => exact ⟨z, by simp [f, z]⟩
      | some u =>
        have h7u : ((u : Kˣ) : K) ^ 7 = 1 := by
          rw [← Units.val_pow_eq_pow_val, u.2, Units.val_one]
        have h8u : ((u : Kˣ) : K) ^ 8 = (u : Kˣ) := by
          rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_add, pow_one, h7u, one_mul]
        let c₀ : {c : K // c ^ 8 = c} := ⟨(u : Kˣ), h8u⟩
        have hne : (c₀ : K) ≠ 0 := u.1.ne_zero
        refine ⟨c₀, ?_⟩
        simp only [f, dif_neg hne]
        congr 1
        exact Subtype.ext (Units.ext (by rw [Units.val_mk0]))
  have hcard : Nat.card {c : K // c ^ 8 = c} =
      Nat.card (Option {u : Kˣ // u ^ 7 = 1}) :=
    Nat.card_congr (Equiv.ofBijective f hf)
  rw [hcard, Finite.card_option, h7]


private def k328de8_pv {K : Type} [Field K] [CharP K 2]  : Fin 3 → K := ![1, 1, 0]

private def k328de8_pN {K : Type} [Field K] [CharP K 2]  : Matrix (Fin 3) (Fin 3) K := fun i j => k328de8_pv i * k328de8_pv j

private def k328de8_ptm {K : Type} [Field K] [CharP K 2]  (c : K) : Matrix (Fin 3) (Fin 3) K := 1 + c • k328de8_pN

private theorem k328de8_h8add {K : Type} [Field K] [CharP K 2]  (x y : K) : (x + y) ^ 8 = x ^ 8 + y ^ 8 := by
  have h := add_pow_char_pow (R := K) (p := 2) (n := 3) x y
  simpa using h

private theorem k328de8_ptm_det {K : Type} [Field K] [CharP K 2]  (c : K) : (k328de8_ptm c).det = 1 := by
  rw [k328de8_ptm, Matrix.det_fin_three]
  simp only [k328de8_pN, k328de8_pv, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  ring_nf
  simp [CharTwo.add_self_eq_zero]

private theorem k328de8_pN_sq {K : Type} [Field K] [CharP K 2]  : (k328de8_pN : Matrix (Fin 3) (Fin 3) K) * k328de8_pN = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328de8_pN, k328de8_pv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.zero_apply,
      CharTwo.add_self_eq_zero]

private theorem k328de8_ptm_mul {K : Type} [Field K] [CharP K 2]  (c d : K) : k328de8_ptm c * k328de8_ptm d = k328de8_ptm (c + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328de8_ptm, k328de8_pN, k328de8_pv, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  all_goals ring_nf
  all_goals rw [CharTwo.two_eq_zero, mul_zero, add_zero]

private theorem k328de8_ptm_zero {K : Type} [Field K] [CharP K 2]  : k328de8_ptm (K := K) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328de8_ptm, Matrix.add_apply]

private theorem k328de8_ptm_transpose {K : Type} [Field K] [CharP K 2]  (c : K) : (k328de8_ptm c)ᵀ = k328de8_ptm c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328de8_ptm, k328de8_pN, k328de8_pv, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
      mul_comm]

private theorem k328de8_ptm_map8 {K : Type} [Field K] [CharP K 2]  (c : K) : (k328de8_ptm c).map (· ^ 8) = k328de8_ptm (c ^ 8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328de8_ptm, k328de8_pN, k328de8_pv, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      k328de8_h8add]

private theorem k328de8_ptm_sq {K : Type} [Field K] [CharP K 2]  (c : K) : k328de8_ptm c * k328de8_ptm c = 1 := by
  have h : c + c = 0 := CharTwo.add_self_eq_zero c
  calc k328de8_ptm c * k328de8_ptm c = k328de8_ptm (c + c) := k328de8_ptm_mul c c
    _ = k328de8_ptm 0 := by rw [h]
    _ = 1 := k328de8_ptm_zero

private theorem k328de8_ptm_unitary {K : Type} [Field K] [CharP K 2]  {c : K} (hc : c ^ 8 = c) :
    ((k328de8_ptm c).map (· ^ 8))ᵀ * k328de8_ptm c = 1 := by
  rw [k328de8_ptm_map8, hc, k328de8_ptm_transpose, k328de8_ptm_sq]

private def k328de8_pT {K : Type} [Field K] [CharP K 2]  (c : K) : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero (k328de8_ptm c) (by rw [k328de8_ptm_det]; exact one_ne_zero)

private theorem k328de8_pT_mul {K : Type} [Field K] [CharP K 2]  (c d : K) : k328de8_pT c * k328de8_pT d = k328de8_pT (c + d) := by
  apply GeneralLinearGroup.ext
  intro i j
  simp only [k328de8_pT, Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, k328de8_ptm_mul]

private theorem k328de8_pT_zero {K : Type} [Field K] [CharP K 2]  : k328de8_pT (K := K) 0 = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  simp only [k328de8_pT, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, k328de8_ptm_zero]
  rfl

private theorem k328de8_pT_sq {K : Type} [Field K] [CharP K 2]  (c : K) : k328de8_pT c * k328de8_pT c = 1 := by
  have h : c + c = 0 := CharTwo.add_self_eq_zero c
  calc k328de8_pT c * k328de8_pT c = k328de8_pT (c + c) := k328de8_pT_mul c c
    _ = k328de8_pT 0 := by rw [h]
    _ = 1 := k328de8_pT_zero

private theorem k328de8_pT_mem {K : Type} [Field K] [CharP K 2]  {c : K} (hc : c ^ 8 = c) : k328de8_pT c ∈ StatedSU 3 8 K := by
  apply Subgroup.subset_closure
  change (k328de8_ptm c).det = 1 ∧ ((k328de8_ptm c).map (· ^ 8))ᵀ * k328de8_ptm c = 1
  exact ⟨k328de8_ptm_det c, k328de8_ptm_unitary hc⟩

private theorem k328de8_pT_injective {K : Type} [Field K] [CharP K 2]  : Function.Injective (fun c : {c : K // c ^ 8 = c} => k328de8_pT c.1) := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ h
  have hm : k328de8_ptm c = k328de8_ptm d := by
    simpa [k328de8_pT, Matrix.GeneralLinearGroup.val_mkOfDetNeZero] using
      congr_arg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h
  have h01 : c = d := by
    have := congr_fun (congr_fun hm 0) 1
    simpa [k328de8_ptm, k328de8_pN, k328de8_pv, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using this
  exact Subtype.ext h01

private def k328de8_PH {K : Type} [Field K] [CharP K 2]  : Subgroup (GL (Fin 3) K) where
  carrier := Set.range fun c : {c : K // c ^ 8 = c} => k328de8_pT c.1
  one_mem' := ⟨⟨0, by simp⟩, k328de8_pT_zero⟩
  mul_mem' := by
    rintro x y ⟨c, rfl⟩ ⟨d, rfl⟩
    refine ⟨⟨c.1 + d.1, ?_⟩, (k328de8_pT_mul c.1 d.1).symm⟩
    rw [k328de8_h8add, c.2, d.2]
  inv_mem' := by
    rintro x ⟨c, rfl⟩
    exact ⟨c, (mul_eq_one_iff_inv_eq.mp (k328de8_pT_sq c.1)).symm⟩

private theorem k328de8_PH_card {K : Type} [Field K] [CharP K 2]  (hK : Nat.card K = 64) :
    Nat.card (k328de8_PH : Subgroup (GL (Fin 3) K)) = 8 := by
  have hbij : Function.Bijective (fun c : {c : K // c ^ 8 = c} =>
      (⟨k328de8_pT c.1, ⟨c, rfl⟩⟩ : (k328de8_PH : Subgroup (GL (Fin 3) K)))) := by
    constructor
    · intro p q h
      exact k328de8_pT_injective (Subtype.ext_iff.mp h)
    · rintro ⟨x, hx⟩
      obtain ⟨p, rfl⟩ := hx
      exact ⟨p, rfl⟩
  have h1 : Nat.card {c : K // c ^ 8 = c} =
      Nat.card (k328de8_PH : Subgroup (GL (Fin 3) K)) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [← h1]
  exact k328de8_card_fixed8 hK

private theorem k328de8_PH_comm {K : Type} [Field K] [CharP K 2]  : ∀ a ∈ (k328de8_PH : Subgroup (GL (Fin 3) K)),
    ∀ b ∈ (k328de8_PH : Subgroup (GL (Fin 3) K)), a * b = b * a := by
  rintro a ⟨p, rfl⟩ b ⟨q, rfl⟩
  rw [k328de8_pT_mul, k328de8_pT_mul, add_comm p.1 q.1]

private theorem k328de8_PH_sq {K : Type} [Field K] [CharP K 2]  : ∀ a ∈ (k328de8_PH : Subgroup (GL (Fin 3) K)), a ^ 2 = 1 := by
  rintro a ⟨p, rfl⟩
  rw [sq, k328de8_pT_sq]

private theorem k328de8_pT_scalar_zero {K : Type} [Field K] [CharP K 2]  {c : K} (_hc : c ^ 8 = c)
    (h : k328de8_pT c ∈ StatedScalars (Fin 3) K) : c = 0 := by
  rw [StatedScalars] at h
  obtain ⟨u, hu⟩ := h
  have h01 := congr_fun (congr_fun (congr_arg
        (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) hu) 0) 1
  simpa [k328de8_pT, GeneralLinearGroup.coe_scalar, Matrix.scalar,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, k328de8_ptm, k328de8_pN, k328de8_pv, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply] using h01.symm

private theorem k328de8_PH_disjoint {K : Type} [Field K] [CharP K 2]  : (k328de8_PH : Subgroup (GL (Fin 3) K)) ⊓ StatedScalars (Fin 3) K = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxH, hxS⟩
  obtain ⟨⟨c, hc⟩, rfl⟩ := hxH
  have hc0 : c = 0 := k328de8_pT_scalar_zero hc hxS
  subst c
  change k328de8_pT (0 : K) ∈ (⊥ : Subgroup (GL (Fin 3) K))
  rw [Subgroup.mem_bot, k328de8_pT_zero]


private theorem k328de8_PSU_exists {K : Type} [Field K] [CharP K 2]  (hK : Nat.card K = 64) :
    ∃ A : Subgroup (StatedProj (StatedSU 3 8 K)),
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ Nat.card A = 8 := by
  let H := StatedSU 3 8 K
  let S : Subgroup (GL (Fin 3) K) := StatedScalars (Fin 3) K
  have hHle : (k328de8_PH : Subgroup (GL (Fin 3) K)) ≤ H := by
    rintro x ⟨c, rfl⟩
    exact k328de8_pT_mem c.2
  let AHH : Subgroup H := (k328de8_PH : Subgroup (GL (Fin 3) K)).subgroupOf H
  let N : Subgroup H := S.subgroupOf H
  let q : H →* StatedProj H := QuotientGroup.mk' N
  let Abar : Subgroup (StatedProj H) := AHH.map q
  have hdisj : AHH ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hxH : (x : GL (Fin 3) K) ∈ (k328de8_PH : Subgroup (GL (Fin 3) K)) := hx1
    have hxS : (x : GL (Fin 3) K) ∈ S := hx2
    have h1 : (x : GL (Fin 3) K) ∈ (k328de8_PH : Subgroup (GL (Fin 3) K)) ⊓ S := ⟨hxH, hxS⟩
    rw [k328de8_PH_disjoint] at h1
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  have hcardAHH : Nat.card AHH = 8 := by
    rw [show Nat.card AHH = Nat.card (k328de8_PH : Subgroup (GL (Fin 3) K)) from
      card_subgroupOf_of_le hHle]
    exact k328de8_PH_card hK
  have hbot : N.subgroupOf AHH = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxN : (x : H) ∈ N := hx
    have h1 : (x : H) ∈ AHH ⊓ N := ⟨x.2, hxN⟩
    rw [hdisj] at h1
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  have hNrel : N.relIndex AHH = Nat.card AHH := by
    change (N.subgroupOf AHH).index = Nat.card AHH
    rw [hbot, Subgroup.index_bot]
  have hmap := Subgroup.relIndex_ker (K := AHH) q
  rw [QuotientGroup.ker_mk'] at hmap
  have hcardmap : Nat.card Abar = Nat.card AHH := by
    change Nat.card (AHH.map q) = Nat.card AHH
    rw [← hmap]
    exact hNrel
  have hcardAbar : Nat.card Abar = 8 := hcardmap.trans hcardAHH
  refine ⟨Abar, ?_, ?_, hcardAbar⟩
  · intro a ha b hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact k328de8_PH_comm _ (show (x : GL (Fin 3) K) ∈ (k328de8_PH : Subgroup (GL (Fin 3) K)) from hx)
      _ (show (y : GL (Fin 3) K) ∈ (k328de8_PH : Subgroup (GL (Fin 3) K)) from hy)
  · intro a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [← map_pow, ← map_one q]
    congr 1
    apply Subtype.ext
    change (x : GL (Fin 3) K) ^ 2 = 1
    exact k328de8_PH_sq _ (show (x : GL (Fin 3) K) ∈ (k328de8_PH : Subgroup (GL (Fin 3) K)) from hx)


private theorem k328dr_neg_one_ne_one' {E : Type*} [Field E] (h2 : (2 : E) ≠ 0) : (-1 : E) ≠ 1 := by
  intro h
  apply h2
  calc (2 : E) = 1 + 1 := by norm_num
    _ = -1 + 1 := by rw [h]
    _ = 0 := neg_add_cancel 1

private theorem k328dr_eigenspace_isCompl {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    (h2 : (2 : E) ≠ 0) (f : Module.End E V) (hf : f * f = 1) :
    IsCompl (f.eigenspace 1) (f.eigenspace (-1)) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Module.End.mem_eigenspace_iff] at hx1 hx2
    rw [one_smul] at hx1; rw [neg_one_smul] at hx2
    have hxe : x = -x := hx1.symm.trans hx2
    have h2x : (2 : E) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hxe]
      exact neg_add_cancel x
    rcases smul_eq_zero.mp h2x with h | h
    · exact absurd h h2
    · exact h
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hff : f (f x) = x := by
      have h : (f * f) x = (1 : Module.End E V) x :=
        congrArg (fun g : Module.End E V => g x) hf
      simpa [Module.End.mul_apply] using h
    refine Submodule.mem_sup.mpr ⟨(2 : E)⁻¹ • (x + f x), ?_, (2 : E)⁻¹ • (x - f x), ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      rw [map_smul, map_add, hff, one_smul]
      rw [add_comm]
    · rw [Module.End.mem_eigenspace_iff]
      rw [map_smul, map_sub, hff]
      rw [smul_comm, neg_one_smul, neg_sub]
    · rw [← smul_add]
      have hsum : (x + f x) + (x - f x) = (2 : E) • x := by
        rw [two_smul]; abel
      rw [hsum, smul_smul, inv_mul_cancel₀ h2, one_smul]

private theorem k328dr_det_eq_mul_det_of_isCompl {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {W₁ W₂ : Submodule E V} (h : IsCompl W₁ W₂)
    (f : Module.End E V) (h₁ : W₁ ≤ W₁.comap f) (h₂ : W₂ ≤ W₂.comap f) :
    f.det = (f.restrict h₁).det * (f.restrict h₂).det := by
  let e : (↥W₁ × ↥W₂) ≃ₗ[E] V := W₁.prodEquivOfIsCompl W₂ h
  have hconj : (e.symm : V →ₗ[E] (↥W₁ × ↥W₂)) ∘ₗ f ∘ₗ (e : (↥W₁ × ↥W₂) →ₗ[E] V) =
      LinearMap.prodMap (f.restrict h₁) (f.restrict h₂) := by
    apply LinearMap.ext
    rintro ⟨x₁, x₂⟩
    have he : (e : (↥W₁ × ↥W₂) →ₗ[E] V) (x₁, x₂) = (x₁ : V) + (x₂ : V) :=
      Submodule.coe_prodEquivOfIsCompl' W₁ W₂ h (x₁, x₂)
    have hsymm : e.symm ((f.restrict h₁ x₁ : V) + (f.restrict h₂ x₂ : V)) =
        (f.restrict h₁ x₁, f.restrict h₂ x₂) := by
      rw [← Submodule.coe_prodEquivOfIsCompl' W₁ W₂ h (f.restrict h₁ x₁, f.restrict h₂ x₂),
        LinearEquiv.symm_apply_apply]
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
    change e.symm (f ((x₁ : V) + (x₂ : V))) = (f.restrict h₁ x₁, f.restrict h₂ x₂)
    rw [map_add]
    change e.symm ((f.restrict h₁ x₁ : V) + (f.restrict h₂ x₂ : V)) = _
    rw [hsymm]
  calc f.det = ((e.symm : V →ₗ[E] (↥W₁ × ↥W₂)) ∘ₗ f ∘ₗ (e : (↥W₁ × ↥W₂) →ₗ[E] V)).det :=
        (LinearMap.det_conj f e.symm).symm
    _ = (LinearMap.prodMap (f.restrict h₁) (f.restrict h₂)).det := by rw [hconj]
    _ = (f.restrict h₁).det * (f.restrict h₂).det := LinearMap.det_prodMap _ _

private theorem k328dr_det_eq_neg_one_pow {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (h2 : (2 : E) ≠ 0) (f : Module.End E V) (hf : f * f = 1) :
    f.det = (-1) ^ Module.finrank E (↥(f.eigenspace (-1))) := by
  have hc := k328dr_eigenspace_isCompl h2 f hf
  have h₁ : f.eigenspace 1 ≤ (f.eigenspace 1).comap f := by
    intro x hx
    have hx' : f x = x := by simpa using Module.End.mem_eigenspace_iff.mp hx
    rw [Submodule.mem_comap, hx']
    exact hx
  have h₂ : f.eigenspace (-1) ≤ (f.eigenspace (-1)).comap f := by
    intro x hx
    have hx' : f x = -x := by
      simpa [neg_one_smul] using Module.End.mem_eigenspace_iff.mp hx
    rw [Submodule.mem_comap, hx', Module.End.mem_eigenspace_iff, map_neg, hx']
    simp
  rw [k328dr_det_eq_mul_det_of_isCompl hc f h₁ h₂]
  have hr₁ : (f.restrict h₁ : ↥(f.eigenspace 1) →ₗ[E] ↥(f.eigenspace 1)) = 1 := by
    ext x
    change f (x : V) = (x : V)
    simpa using Module.End.mem_eigenspace_iff.mp x.2
  have hr₂ : (f.restrict h₂ : ↥(f.eigenspace (-1)) →ₗ[E] ↥(f.eigenspace (-1))) = -1 := by
    ext x
    change f (x : V) = -(x : V)
    simpa [neg_one_smul] using Module.End.mem_eigenspace_iff.mp x.2
  have hd₂ : (-1 : Module.End E ↥(f.eigenspace (-1))) =
      (-1 : E) • (1 : Module.End E ↥(f.eigenspace (-1))) := by
    ext x
    simp
  rw [hr₁, hr₂, hd₂, LinearMap.det_smul]
  simp




private theorem k328dr_mapsTo_eigenspace_of_comm {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    {f g : Module.End E V} (h : Commute f g) (μ : E) :
    ∀ x ∈ f.eigenspace μ, g x ∈ f.eigenspace μ := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hc : f (g x) = g (f x) := by
    have hh := congrArg (fun k : Module.End E V => k x) h.eq
    simpa [Module.End.mul_apply] using hh
  rw [hc, hx, map_smul]

private theorem k328dr_finrank_add_finrank_eigenspaces {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (h2 : (2 : E) ≠ 0) (f : Module.End E V) (hf : f * f = 1) :
    Module.finrank E (↥(f.eigenspace 1)) + Module.finrank E (↥(f.eigenspace (-1))) =
      Module.finrank E V := by
  have hcompl := k328dr_eigenspace_isCompl h2 f hf
  have he := (f.eigenspace 1).prodEquivOfIsCompl (f.eigenspace (-1)) hcompl
  rw [← he.finrank_eq, Module.finrank_prod]

private theorem k328dr_finrank_eigenspace_one_eq_one {E : Type*} [Field E] (h2 : (2 : E) ≠ 0)
    (f : Module.End E (Fin 3 → E)) (hf : f * f = 1) (hdet : f.det = 1) (hf1 : f ≠ 1) :
    Module.finrank E (↥(f.eigenspace 1)) = 1 := by
  have hcompl := k328dr_eigenspace_isCompl h2 f hf
  have h₁ : f.eigenspace 1 ≤ (f.eigenspace 1).comap f := by
    intro x hx
    have hx' : f x = x := by simpa using Module.End.mem_eigenspace_iff.mp hx
    rw [Submodule.mem_comap, hx']
    exact hx
  have h₂ : f.eigenspace (-1) ≤ (f.eigenspace (-1)).comap f := by
    intro x hx
    have hx' : f x = -x := by
      simpa [neg_one_smul] using Module.End.mem_eigenspace_iff.mp hx
    rw [Submodule.mem_comap, hx', Module.End.mem_eigenspace_iff, map_neg, hx']
    simp
  have hsum := k328dr_finrank_add_finrank_eigenspaces (V := Fin 3 → E) h2 f hf
  have hV : Module.finrank E (Fin 3 → E) = 3 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hdetmul := k328dr_det_eq_mul_det_of_isCompl hcompl f h₁ h₂
  have hr₁ : (f.restrict h₁ : ↥(f.eigenspace 1) →ₗ[E] ↥(f.eigenspace 1)) = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa using Module.End.mem_eigenspace_iff.mp x.2
  have hr₂ : (f.restrict h₂ : ↥(f.eigenspace (-1)) →ₗ[E] ↥(f.eigenspace (-1))) = -1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa [neg_one_smul] using Module.End.mem_eigenspace_iff.mp x.2
  have hd₂ : (-1 : Module.End E ↥(f.eigenspace (-1))) =
      (-1 : E) • (1 : Module.End E ↥(f.eigenspace (-1))) := by
    ext x
    simp
  have hpar : (-1 : E) ^ Module.finrank E (↥(f.eigenspace (-1))) = 1 := by
    have h := hdetmul
    rw [hr₁, hr₂, hd₂, LinearMap.det_smul, hdet] at h
    simpa using h.symm
  have heven : Even (Module.finrank E (↥(f.eigenspace (-1)))) :=
    (neg_one_pow_eq_one_iff_even (k328dr_neg_one_ne_one' h2)).mp hpar
  have hne : f.eigenspace 1 ≠ ⊤ := by
    intro htop
    apply hf1
    apply LinearMap.ext
    intro x
    have hx : x ∈ f.eigenspace 1 := by rw [htop]; exact Submodule.mem_top
    simpa using Module.End.mem_eigenspace_iff.mp hx
  have hfw₁ne : Module.finrank E (↥(f.eigenspace 1)) ≠ 3 := by
    intro h3
    exact hne (Submodule.eq_top_of_finrank_eq (S := f.eigenspace 1) (by rw [h3, hV]))
  rcases heven with ⟨m, hm⟩
  have hle : Module.finrank E (↥(f.eigenspace 1)) ≤ 3 := by omega
  omega

private theorem k328dr_eq_one_or_neg_one_of_involution_finrank_two {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h2 : (2 : E) ≠ 0) (g : Module.End E W) (hg : g * g = 1)
    (hdet : g.det = 1) (hfin : Module.finrank E W = 2) :
    g = 1 ∨ g = -1 := by
  have hcompl := k328dr_eigenspace_isCompl h2 g hg
  have h₁ : g.eigenspace 1 ≤ (g.eigenspace 1).comap g := by
    intro x hx
    have hx' : g x = x := by simpa using Module.End.mem_eigenspace_iff.mp hx
    rw [Submodule.mem_comap, hx']
    exact hx
  have h₂ : g.eigenspace (-1) ≤ (g.eigenspace (-1)).comap g := by
    intro x hx
    have hx' : g x = -x := by
      simpa [neg_one_smul] using Module.End.mem_eigenspace_iff.mp hx
    rw [Submodule.mem_comap, hx', Module.End.mem_eigenspace_iff, map_neg, hx']
    simp
  have hsum := k328dr_finrank_add_finrank_eigenspaces h2 g hg
  have hdetmul := k328dr_det_eq_mul_det_of_isCompl hcompl g h₁ h₂
  have hr₁ : (g.restrict h₁ : ↥(g.eigenspace 1) →ₗ[E] ↥(g.eigenspace 1)) = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa using Module.End.mem_eigenspace_iff.mp x.2
  have hr₂ : (g.restrict h₂ : ↥(g.eigenspace (-1)) →ₗ[E] ↥(g.eigenspace (-1))) = -1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa [neg_one_smul] using Module.End.mem_eigenspace_iff.mp x.2
  have hd₂ : (-1 : Module.End E ↥(g.eigenspace (-1))) =
      (-1 : E) • (1 : Module.End E ↥(g.eigenspace (-1))) := by
    ext x
    simp
  have hpar : (-1 : E) ^ Module.finrank E (↥(g.eigenspace (-1))) = 1 := by
    have h := hdetmul
    rw [hr₁, hr₂, hd₂, LinearMap.det_smul, hdet] at h
    simpa using h.symm
  have heven : Even (Module.finrank E (↥(g.eigenspace (-1)))) :=
    (neg_one_pow_eq_one_iff_even (k328dr_neg_one_ne_one' h2)).mp hpar
  rcases heven with ⟨m, hm⟩
  have hcases : Module.finrank E (↥(g.eigenspace (-1))) = 0 ∨
      Module.finrank E (↥(g.eigenspace (-1))) = 2 := by omega
  rcases hcases with h0 | h2'
  · left
    have h1 : Module.finrank E (↥(g.eigenspace 1)) = 2 := by omega
    have htop : g.eigenspace 1 = ⊤ := Submodule.eq_top_of_finrank_eq (S := g.eigenspace 1) (by rw [h1, hfin])
    apply LinearMap.ext
    intro x
    have hx : x ∈ g.eigenspace 1 := by rw [htop]; exact Submodule.mem_top
    simpa using Module.End.mem_eigenspace_iff.mp hx
  · right
    have htop : g.eigenspace (-1) = ⊤ := Submodule.eq_top_of_finrank_eq (S := g.eigenspace (-1)) (by rw [h2', hfin])
    apply LinearMap.ext
    intro x
    have hx : x ∈ g.eigenspace (-1) := by rw [htop]; exact Submodule.mem_top
    have := Module.End.mem_eigenspace_iff.mp hx
    simpa [neg_one_smul] using this





private theorem k328dr_apply_apply_eq_of_mul_self {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    (f : Module.End E V) (hf : f * f = 1) (x : V) : f (f x) = x := by
  have := congrArg (fun T : Module.End E V => T x) hf
  simpa [Module.End.mul_apply] using this

private theorem k328dr_exists_generator_finrank_one {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    {P : Submodule E V} (hP : Module.finrank E ↥P = 1) :
    ∃ v : ↥P, v ≠ 0 ∧ ∀ w : ↥P, ∃ c : E, c • v = w :=
  (finrank_eq_one_iff').mp hP

private theorem k328dr_eq_smul_one_of_generator {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    {P : Submodule E V} (T : Module.End E ↥P) {v : ↥P}
    (hv : ∀ w : ↥P, ∃ c : E, c • v = w) {c : E} (h : T v = c • v) : T = c • 1 := by
  ext w
  obtain ⟨d, rfl⟩ := hv w
  simp only [map_smul, h, LinearMap.smul_apply, Module.End.one_apply]

private theorem k328dr_eq_of_commute_involution_same_eigenspace {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (h2 : (2 : E) ≠ 0) (f g : Module.End E V)
    (hf : f * f = 1) (hg : g * g = 1) (hcomm : f * g = g * f)
    (hfg : f.eigenspace 1 = g.eigenspace 1) : f = g := by
  have hmem : ∀ x : V, (f - g) x ∈ f.eigenspace 1 := by
    intro x
    have h1 : f x + x ∈ f.eigenspace 1 := by
      rw [Module.End.mem_eigenspace_iff, map_add, k328dr_apply_apply_eq_of_mul_self f hf x, one_smul]
      abel
    have h2' : g x + x ∈ f.eigenspace 1 := by
      rw [hfg, Module.End.mem_eigenspace_iff, map_add, k328dr_apply_apply_eq_of_mul_self g hg x, one_smul]
      abel
    have hx : (f - g) x = (f x + x) - (g x + x) := by
      simp only [LinearMap.sub_apply]; abel
    rw [hx]
    exact Submodule.sub_mem _ h1 h2'
  have hf1 : ∀ y ∈ f.eigenspace 1, f y = y := by
    intro y hy
    simpa using Module.End.mem_eigenspace_iff.mp hy
  have hg1 : ∀ y ∈ f.eigenspace 1, g y = y := by
    intro y hy
    have hy' : y ∈ g.eigenspace 1 := by rw [← hfg]; exact hy
    simpa using Module.End.mem_eigenspace_iff.mp hy'
  have hA : f * (f - g) = f - g := by
    ext x
    rw [Module.End.mul_apply]
    exact hf1 _ (hmem x)
  have hB : g * (f - g) = f - g := by
    ext x
    rw [Module.End.mul_apply]
    exact hg1 _ (hmem x)
  have hA' : f * (f - g) = 1 - f * g := by rw [mul_sub, hf]
  have hB' : g * (f - g) = f * g - 1 := by rw [mul_sub, hcomm, hg]
  rw [hA'] at hA
  rw [hB'] at hB
  have heq : f - g = -(f - g) := by
    calc f - g = 1 - f * g := hA.symm
      _ = -(f * g - 1) := by abel
      _ = -(f - g) := by rw [hB]
  have h2s : (2 : E) • (f - g) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [heq]
    exact neg_add_cancel (f - g)
  have hz : f - g = 0 := by
    rcases smul_eq_zero.mp h2s with h | h
    · exact absurd h h2
    · exact h
  exact sub_eq_zero.mp hz

private theorem k328dr_involution_add_eq_neg_one {E : Type*} [Field E] (h2 : (2 : E) ≠ 0) (f g : Module.End E (Fin 3 → E))
    (hf : f * f = 1) (hg : g * g = 1) (hcomm : f * g = g * f)
    (hfd : f.det = 1) (hgd : g.det = 1) (hf1 : f ≠ 1) (hg1 : g ≠ 1) (hne : f ≠ g) :
    f + g + f * g = -1 := by
  have hPf : Module.finrank E ↥(f.eigenspace 1) = 1 :=
    k328dr_finrank_eigenspace_one_eq_one h2 f hf hfd hf1
  have hPg : Module.finrank E ↥(g.eigenspace 1) = 1 :=
    k328dr_finrank_eigenspace_one_eq_one h2 g hg hgd hg1
  obtain ⟨v, hv0, hv⟩ := k328dr_exists_generator_finrank_one (E := E) hPf
  have hpres : ∀ x ∈ f.eigenspace 1, g x ∈ f.eigenspace 1 := by
    intro x hx
    have hcomm' : f (g x) = g (f x) := by
      have hh := congrArg (fun T : Module.End E (Fin 3 → E) => T x) hcomm
      simpa [Module.End.mul_apply] using hh
    have hx' : f x = x := by simpa using Module.End.mem_eigenspace_iff.mp hx
    rw [Module.End.mem_eigenspace_iff, hcomm', hx', one_smul]
  obtain ⟨c, hc⟩ : ∃ c : E, c • (v : Fin 3 → E) = g (v : Fin 3 → E) := by
    obtain ⟨c, hc⟩ := hv ⟨g (v : Fin 3 → E), hpres v v.2⟩
    exact ⟨c, congrArg (fun z : ↥(f.eigenspace 1) => (z : Fin 3 → E)) hc⟩
  have hgc : ∀ x ∈ f.eigenspace 1, g x = c • x := by
    intro x hx
    obtain ⟨d, hd⟩ := hv ⟨x, hx⟩
    have hd' : d • (v : Fin 3 → E) = x := congrArg (fun z : ↥(f.eigenspace 1) => (z : Fin 3 → E)) hd
    rw [← hd', map_smul, ← hc, smul_smul, smul_smul, mul_comm]
  have hc2 : c ^ 2 = 1 := by
    have h1 : (c ^ 2 : E) • (v : Fin 3 → E) = (v : Fin 3 → E) := by
      have h := k328dr_apply_apply_eq_of_mul_self g hg (v : Fin 3 → E)
      rw [← hc, map_smul, ← hc, smul_smul, ← pow_two] at h
      exact h
    have h2' : (c ^ 2 - 1 : E) • (v : Fin 3 → E) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    have h4 : c ^ 2 - 1 = 0 := by
      rcases smul_eq_zero.mp h2' with h | h
      · exact h
      · exact absurd (Subtype.ext h) hv0
    exact sub_eq_zero.mp h4
  have hc_neg : c = -1 := by
    rcases sq_eq_one_iff.mp hc2 with h1 | h1
    · exfalso
      have hgle : f.eigenspace 1 ≤ g.eigenspace 1 := by
        intro y hy
        have hy' : g y = y := by rw [hgc y hy, h1, one_smul]
        rw [Module.End.mem_eigenspace_iff, hy', one_smul]
      have heq : f.eigenspace 1 = g.eigenspace 1 :=
        Submodule.eq_of_le_of_finrank_eq hgle (by rw [hPf, hPg])
      exact hne (k328dr_eq_of_commute_involution_same_eigenspace h2 f g hf hg hcomm heq)
    · exact h1
  have hgneg : ∀ x ∈ f.eigenspace 1, g x = -x := by
    intro x hx
    rw [hgc x hx, hc_neg, neg_one_smul]
  have hpres' : ∀ x ∈ g.eigenspace 1, f x ∈ g.eigenspace 1 := by
    intro x hx
    have hcomm' : g (f x) = f (g x) := by
      have hh := congrArg (fun T : Module.End E (Fin 3 → E) => T x) hcomm
      have hh' : f (g x) = g (f x) := by simpa [Module.End.mul_apply] using hh
      exact hh'.symm
    have hx' : g x = x := by simpa using Module.End.mem_eigenspace_iff.mp hx
    rw [Module.End.mem_eigenspace_iff, hcomm', hx', one_smul]
  obtain ⟨w, hw0, hw⟩ := k328dr_exists_generator_finrank_one (E := E) hPg
  obtain ⟨d, hd⟩ : ∃ d : E, d • (w : Fin 3 → E) = f (w : Fin 3 → E) := by
    obtain ⟨d, hd⟩ := hw ⟨f (w : Fin 3 → E), hpres' w w.2⟩
    exact ⟨d, congrArg (fun z : ↥(g.eigenspace 1) => (z : Fin 3 → E)) hd⟩
  have hfd' : ∀ x ∈ g.eigenspace 1, f x = d • x := by
    intro x hx
    obtain ⟨e, he⟩ := hw ⟨x, hx⟩
    have he' : e • (w : Fin 3 → E) = x := congrArg (fun z : ↥(g.eigenspace 1) => (z : Fin 3 → E)) he
    rw [← he', map_smul, ← hd, smul_smul, smul_smul, mul_comm]
  have hd2 : d ^ 2 = 1 := by
    have h1 : (d ^ 2 : E) • (w : Fin 3 → E) = (w : Fin 3 → E) := by
      have h := k328dr_apply_apply_eq_of_mul_self f hf (w : Fin 3 → E)
      rw [← hd, map_smul, ← hd, smul_smul, ← pow_two] at h
      exact h
    have h2' : (d ^ 2 - 1 : E) • (w : Fin 3 → E) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    have h4 : d ^ 2 - 1 = 0 := by
      rcases smul_eq_zero.mp h2' with h | h
      · exact h
      · exact absurd (Subtype.ext h) hw0
    exact sub_eq_zero.mp h4
  have hd_neg : d = -1 := by
    rcases sq_eq_one_iff.mp hd2 with h1 | h1
    · exfalso
      have hgle : g.eigenspace 1 ≤ f.eigenspace 1 := by
        intro y hy
        have hy' : f y = y := by rw [hfd' y hy, h1, one_smul]
        rw [Module.End.mem_eigenspace_iff, hy', one_smul]
      have heq : f.eigenspace 1 = g.eigenspace 1 :=
        (Submodule.eq_of_le_of_finrank_eq hgle (by rw [hPg, hPf])).symm
      exact hne (k328dr_eq_of_commute_involution_same_eigenspace h2 f g hf hg hcomm heq)
    · exact h1
  have hfneg : ∀ x ∈ g.eigenspace 1, f x = -x := by
    intro x hx
    rw [hfd' x hx, hd_neg, neg_one_smul]
  have hprod : (f + 1) * (g + 1) = 0 := by
    apply LinearMap.ext
    intro x
    have hx : (g + 1) x ∈ g.eigenspace 1 := by
      rw [Module.End.mem_eigenspace_iff, LinearMap.add_apply, Module.End.one_apply, map_add,
        k328dr_apply_apply_eq_of_mul_self g hg x, one_smul]
      abel
    have hf' := hfneg ((g + 1) x) hx
    change (f + 1) ((g + 1) x) = 0
    rw [LinearMap.add_apply, Module.End.one_apply, hf', neg_add_cancel]
  have hexp : (f + 1) * (g + 1) = f * g + f + g + 1 := by noncomm_ring
  rw [hexp] at hprod
  have hsum : f * g + f + g = -1 := by
    have h := congrArg (fun x : Module.End E (Fin 3 → E) => x - 1) hprod
    simpa using h
  rw [show f + g + f * g = f * g + f + g by abel]
  exact hsum






private def k328dr_natRep {E : Type*} [Field E] (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E)) :
    ↥Y →* Module.End E (Fin 3 → E) where
  toFun y := Matrix.toLin' ((y : ↥Y) : Matrix (Fin 3) (Fin 3) E)
  map_one' := by
    simp only [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
    rfl
  map_mul' := by
    intro y z
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul,
      Module.End.mul_eq_comp]

private theorem k328dr_natRep_injective {E : Type*} [Field E] (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E)) :
    Function.Injective (k328dr_natRep Y) := by
  intro y z h
  apply Subtype.ext
  apply Subtype.ext
  exact Matrix.toLin'.injective h

private theorem k328dr_commute_natRep {E : Type*} [Field E] (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E))
    {c : ↥Y} (hc : c ∈ Subgroup.center ↥Y) (y : ↥Y) :
    Commute (k328dr_natRep Y c) (k328dr_natRep Y y) := by
  rw [commute_iff_eq]
  have h : c * y = y * c := (Subgroup.mem_center_iff.mp hc y).symm
  have := congrArg (k328dr_natRep Y) h
  simpa [map_mul] using this

private theorem k328dr_pres_of_comm {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    {f g : Module.End E V} (h : Commute f g) (μ : E) :
    f.eigenspace μ ≤ (f.eigenspace μ).comap g :=
  fun x hx => k328dr_mapsTo_eigenspace_of_comm h μ x hx

private theorem k328dr_apply_eq_neg_of_involution {E : Type*} [Field E] (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E))
    (h2 : (2 : E) ≠ 0) (hperf : ⁅Y, Y⁆ = Y) (c : ↥Y)
    (hc : c ∈ Subgroup.center ↥Y) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (x : ↥Y) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∀ w ∈ (k328dr_natRep Y c).eigenspace (-1), k328dr_natRep Y x w = -w := by
  set fc := k328dr_natRep Y c with hfc
  set fx := k328dr_natRep Y x with hfx
  have hcx : Commute fc fx := k328dr_commute_natRep Y hc x
  have hfc2 : fc * fc = 1 := by
    rw [hfc, ← map_mul, ← pow_two, hc2, map_one]
  have hfx2 : fx * fx = 1 := by
    rw [hfx, ← map_mul, ← pow_two, hx2, map_one]
  have hdetc : fc.det = 1 := by
    rw [hfc]
    change LinearMap.det (Matrix.toLin' ((c : ↥Y) : Matrix (Fin 3) (Fin 3) E)) = 1
    rw [LinearMap.det_toLin']
    exact (c : Matrix.SpecialLinearGroup (Fin 3) E).2
  have hdetx : fx.det = 1 := by
    rw [hfx]
    change LinearMap.det (Matrix.toLin' ((x : ↥Y) : Matrix (Fin 3) (Fin 3) E)) = 1
    rw [LinearMap.det_toLin']
    exact (x : Matrix.SpecialLinearGroup (Fin 3) E).2
  have hfc1 : fc ≠ 1 := by
    intro h
    apply hc1
    exact k328dr_natRep_injective Y (by rw [← hfc, h, map_one])
  have hcompl := k328dr_eigenspace_isCompl h2 fc hfc2
  set Wp := fc.eigenspace 1 with hWpdef
  set Wm := fc.eigenspace (-1) with hWmdef
  have hWp : Module.finrank E ↥Wp = 1 :=
    k328dr_finrank_eigenspace_one_eq_one h2 fc hfc2 hdetc hfc1
  have hWm : Module.finrank E ↥Wm = 2 := by
    have hsum := k328dr_finrank_add_finrank_eigenspaces (V := Fin 3 → E) h2 fc hfc2
    have hV : Module.finrank E (Fin 3 → E) = 3 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [hV, ← hWpdef, ← hWmdef] at hsum
    omega
  obtain ⟨v, hv0, hv⟩ := k328dr_exists_generator_finrank_one (E := E) hWp
  have hpresC : ∀ y : ↥Y, Wp ≤ Wp.comap (k328dr_natRep Y y) := fun y =>
    k328dr_pres_of_comm (k328dr_commute_natRep Y hc y) 1
  let α : ↥Y → E := fun y =>
    Classical.choose (hv ⟨k328dr_natRep Y y (v : Fin 3 → E), hpresC y v.2⟩)
  have hα : ∀ y : ↥Y, α y • (v : Fin 3 → E) = k328dr_natRep Y y (v : Fin 3 → E) := fun y =>
    congrArg (fun z : ↥Wp => (z : Fin 3 → E))
      (Classical.choose_spec (hv ⟨k328dr_natRep Y y (v : Fin 3 → E), hpresC y v.2⟩))
  have hα_mul : ∀ y z : ↥Y, α (y * z) = α y * α z := by
    intro y z
    have h1 : α (y * z) • (v : Fin 3 → E) = k328dr_natRep Y y (k328dr_natRep Y z (v : Fin 3 → E)) := by
      rw [hα (y * z), map_mul, Module.End.mul_apply]
    rw [← hα z, map_smul, ← hα y, smul_smul] at h1
    have h2 : (α (y * z) - α z * α y) • (v : Fin 3 → E) = 0 := by rw [sub_smul, h1, sub_self]
    have h3 : α (y * z) - α z * α y = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd (Subtype.ext h) hv0
    rw [sub_eq_zero] at h3
    rw [h3, mul_comm]
  have hα_one : α 1 = 1 := by
    have h1 : α 1 • (v : Fin 3 → E) = (v : Fin 3 → E) := by
      rw [hα 1, map_one, Module.End.one_apply]
    have h2 : (α 1 - 1) • (v : Fin 3 → E) = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    have h3 : α 1 - 1 = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd (Subtype.ext h) hv0
    exact sub_eq_zero.mp h3
  have hα_ne : ∀ y : ↥Y, α y ≠ 0 := by
    intro y hy
    have h := hα_mul y y⁻¹
    rw [mul_inv_cancel, hα_one] at h
    rw [hy, zero_mul] at h
    exact one_ne_zero h
  let Φ : ↥Y →* Eˣ :=
    { toFun := fun y => Units.mk0 (α y) (hα_ne y)
      map_one' := Units.ext (by simp [hα_one])
      map_mul' := fun y z => Units.ext (by simp [hα_mul y z]) }
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hle : (⊤ : Subgroup ↥Y) ≤ Φ.ker := by
    rw [← Group.IsPerfect.commutator_eq_top]
    exact Abelianization.commutator_subset_ker Φ
  have hker : Φ.ker = ⊤ := top_le_iff.mp hle
  have hα_one' : ∀ y : ↥Y, α y = 1 := by
    intro y
    have hmem : y ∈ Φ.ker := by rw [hker]; trivial
    have h1 : Φ y = 1 := MonoidHom.mem_ker.mp hmem
    have := congrArg (fun u : Eˣ => (u : E)) h1
    simpa [Φ] using this
  have hpresx_p : Wp ≤ Wp.comap fx := k328dr_pres_of_comm hcx 1
  have hpresx_m : Wm ≤ Wm.comap fx := k328dr_pres_of_comm hcx (-1)
  have hdetWp : LinearMap.det (fx.restrict hpresx_p) = 1 := by
    have heq : (fx.restrict hpresx_p : Module.End E ↥Wp) = α x • 1 :=
      k328dr_eq_smul_one_of_generator _ hv (Subtype.ext (hα x).symm)
    rw [heq, LinearMap.det_smul, hWp, pow_one, hα_one' x]
    simp
  have hdetWm : LinearMap.det (LinearMap.restrict fx (p := Wm) (q := Wm) hpresx_m) = 1 := by
    have h := k328dr_det_eq_mul_det_of_isCompl hcompl fx hpresx_p hpresx_m
    rw [hdetx, hdetWp, one_mul] at h
    exact h.symm
  have hff : ∀ w, fx (fx w) = w := fun w => by
    have := congrArg (fun T : Module.End E (Fin 3 → E) => T w) hfx2
    simpa [Module.End.mul_apply] using this
  have hresq : (LinearMap.restrict fx (p := Wm) (q := Wm) hpresx_m) *
      (LinearMap.restrict fx (p := Wm) (q := Wm) hpresx_m) = 1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change fx (fx (w : Fin 3 → E)) = (w : Fin 3 → E)
    rw [hff]
  have hresWp : (LinearMap.restrict fx (p := Wp) (q := Wp) hpresx_p : Module.End E ↥Wp) = 1 := by
    have heq : (LinearMap.restrict fx (p := Wp) (q := Wp) hpresx_p : Module.End E ↥Wp) =
        α x • 1 := k328dr_eq_smul_one_of_generator _ hv (Subtype.ext (hα x).symm)
    rw [heq, hα_one' x, one_smul]
  have hneg : (LinearMap.restrict fx (p := Wm) (q := Wm) hpresx_m) = -1 := by
    rcases k328dr_eq_one_or_neg_one_of_involution_finrank_two h2
      (LinearMap.restrict fx (p := Wm) (q := Wm) hpresx_m) hresq hdetWm hWm with h1 | h1
    · exfalso
      have hfx1 : fx = 1 := by
        apply LinearMap.ext
        intro w
        have hw : w ∈ Wp ⊔ Wm := by
          rw [hcompl.sup_eq_top]
          trivial
        rcases Submodule.mem_sup.mp hw with ⟨p, hp, q, hq, rfl⟩
        rw [map_add]
        have hp' : fx p = p := by
          have : (LinearMap.restrict fx (p := Wp) (q := Wp) hpresx_p) ⟨p, hp⟩ = ⟨p, hp⟩ := by
            rw [hresWp]; rfl
          simpa using congrArg (fun z : ↥Wp => (z : Fin 3 → E)) this
        have hq' : fx q = q := by
          have : (LinearMap.restrict fx (p := Wm) (q := Wm) hpresx_m) ⟨q, hq⟩ = ⟨q, hq⟩ := by
            rw [h1]; rfl
          simpa using congrArg (fun z : ↥Wm => (z : Fin 3 → E)) this
        rw [hp', hq', Module.End.one_apply]
      exact hx1 (k328dr_natRep_injective Y (by rw [← hfx, hfx1, map_one]))
    · exact h1
  intro w hw
  have hthis := congrArg (fun T : Module.End E ↥Wm => T ⟨w, hw⟩) hneg
  simpa using congrArg (fun z : ↥Wm => (z : Fin 3 → E)) hthis

private theorem k328dr_eq_of_commute_involutions {E : Type*} [Field E] (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E))
    (h2 : (2 : E) ≠ 0) (hperf : ⁅Y, Y⁆ = Y) (c : ↥Y)
    (hc : c ∈ Subgroup.center ↥Y) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (x y : ↥Y) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x * y = y * x) : x = y := by
  have hxneg := k328dr_apply_eq_neg_of_involution Y h2 hperf c hc hc2 hc1 x hx2 hx1
  have hyneg := k328dr_apply_eq_neg_of_involution Y h2 hperf c hc hc2 hc1 y hy2 hy1
  have hxy2 : (x * y) ^ 2 = 1 := by
    calc (x * y) ^ 2 = (x * y) * (x * y) := by rw [pow_two]
      _ = x * (y * x) * y := by noncomm_ring
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by noncomm_ring
      _ = 1 := by rw [← pow_two, ← pow_two, hx2, hy2, one_mul]
  by_contra hne
  have hxy_ne_one : x * y ≠ 1 := by
    intro hxy1
    apply hne
    have hx : x = (x * y) * y := by rw [mul_assoc, ← pow_two, hy2, mul_one]
    rw [hxy1, one_mul] at hx
    exact hx
  have hxyneg := k328dr_apply_eq_neg_of_involution Y h2 hperf c hc hc2 hc1 (x * y) hxy2 hxy_ne_one
  have hfc2 : k328dr_natRep Y c * k328dr_natRep Y c = 1 := by rw [← map_mul, ← pow_two, hc2, map_one]
  have hdetc : (k328dr_natRep Y c).det = 1 := by
    change LinearMap.det (Matrix.toLin' ((c : ↥Y) : Matrix (Fin 3) (Fin 3) E)) = 1
    rw [LinearMap.det_toLin']
    exact (c : Matrix.SpecialLinearGroup (Fin 3) E).2
  have hfc1 : k328dr_natRep Y c ≠ 1 := by
    intro h
    apply hc1
    exact k328dr_natRep_injective Y (by rw [h, map_one])
  have hWp : Module.finrank E ↥((k328dr_natRep Y c).eigenspace 1) = 1 :=
    k328dr_finrank_eigenspace_one_eq_one h2 _ hfc2 hdetc hfc1
  have hWm : Module.finrank E ↥((k328dr_natRep Y c).eigenspace (-1)) = 2 := by
    have hsum := k328dr_finrank_add_finrank_eigenspaces (V := Fin 3 → E) h2 _ hfc2
    have hV : Module.finrank E (Fin 3 → E) = 3 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [hV, hWp] at hsum
    omega
  have hWmne : (k328dr_natRep Y c).eigenspace (-1) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hWm
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWmne
  have hxyw : k328dr_natRep Y (x * y) w = w := by
    rw [map_mul, Module.End.mul_apply, hyneg w hw, map_neg, hxneg w hw, neg_neg]
  have hwneg : w = -w := by
    calc w = k328dr_natRep Y (x * y) w := hxyw.symm
      _ = -w := hxyneg w hw
  have h2w : (2 : E) • w = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hwneg]
    exact neg_add_cancel w
  rcases smul_eq_zero.mp h2w with h | h
  · exact absurd h h2
  · exact absurd h hw0






private abbrev k328dr_toEnd {E : Type*} [Field E] (t : Matrix.SpecialLinearGroup (Fin 3) E) : Module.End E (Fin 3 → E) :=
  Matrix.toLin' (t : Matrix (Fin 3) (Fin 3) E)

private theorem k328dr_toEnd_injective {E : Type*} [Field E] : Function.Injective (k328dr_toEnd (E := E)) := by
  intro a b h
  exact Subtype.ext (Matrix.toLin'.injective h)

private theorem k328dr_toEnd_mul {E : Type*} [Field E] (a b : Matrix.SpecialLinearGroup (Fin 3) E) :
    k328dr_toEnd (a * b) = k328dr_toEnd a * k328dr_toEnd b := by
  simp only [k328dr_toEnd, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

private theorem k328dr_toEnd_one {E : Type*} [Field E] : k328dr_toEnd (1 : Matrix.SpecialLinearGroup (Fin 3) E) = 1 := by
  simp only [k328dr_toEnd, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
  rfl

private theorem k328dr_toEnd_pow_two {E : Type*} [Field E] (a : Matrix.SpecialLinearGroup (Fin 3) E) :
    k328dr_toEnd (a ^ 2) = k328dr_toEnd a * k328dr_toEnd a := by
  rw [pow_two, k328dr_toEnd_mul]

private theorem k328dr_toEnd_det {E : Type*} [Field E] (a : Matrix.SpecialLinearGroup (Fin 3) E) : (k328dr_toEnd a).det = 1 := by
  rw [k328dr_toEnd, LinearMap.det_toLin']
  exact a.2

private theorem k328dr_smul_one_mul {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    (c : E) (f : Module.End E V) : ((c • (1 : Module.End E V)) * f) = c • f := by
  rw [Module.End.mul_eq_comp, LinearMap.smul_comp]
  congr 1

private theorem k328dr_nsmul_one_mul {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
    (n : ℕ) (f : Module.End E V) : ((n • (1 : Module.End E V)) * f) = n • f := by
  induction n with
  | zero => simp
  | succ k ih => rw [succ_nsmul, add_mul, ih, one_mul, succ_nsmul]

private theorem k328dr_false_of_three_involutions {E : Type*} [Field E] {f g h : Matrix.SpecialLinearGroup (Fin 3) E}
    (h2 : (2 : E) ≠ 0)
    (hf2 : f ^ 2 = 1) (hg2 : g ^ 2 = 1) (hh2 : h ^ 2 = 1)
    (hf1 : f ≠ 1) (hg1 : g ≠ 1) (hh1 : h ≠ 1)
    (hfg : f * g = g * f) (hfh : f * h = h * f) (hgh : g * h = h * g)
    (hfgne : f ≠ g) (hhf : h ≠ f) (hhg : h ≠ g) (hhfg : h ≠ f * g) : False := by
  let F : Module.End E (Fin 3 → E) := k328dr_toEnd f
  let G : Module.End E (Fin 3 → E) := k328dr_toEnd g
  let H : Module.End E (Fin 3 → E) := k328dr_toEnd h
  have hF : F = k328dr_toEnd f := rfl
  have hG : G = k328dr_toEnd g := rfl
  have hH : H = k328dr_toEnd h := rfl
  have hF2 : F * F = 1 := by
    rw [hF, ← k328dr_toEnd_pow_two, hf2, k328dr_toEnd_one]
  have hG2 : G * G = 1 := by
    rw [hG, ← k328dr_toEnd_pow_two, hg2, k328dr_toEnd_one]
  have hH2 : H * H = 1 := by
    rw [hH, ← k328dr_toEnd_pow_two, hh2, k328dr_toEnd_one]
  have hFdet : F.det = 1 := k328dr_toEnd_det f
  have hGdet : G.det = 1 := k328dr_toEnd_det g
  have hHdet : H.det = 1 := k328dr_toEnd_det h
  have hF1 : F ≠ 1 := by
    intro hh
    apply hf1
    apply k328dr_toEnd_injective
    rw [hF] at hh
    rw [hh, k328dr_toEnd_one]
  have hG1 : G ≠ 1 := by
    intro hh
    apply hg1
    apply k328dr_toEnd_injective
    rw [hG] at hh
    rw [hh, k328dr_toEnd_one]
  have hH1 : H ≠ 1 := by
    intro hh
    apply hh1
    apply k328dr_toEnd_injective
    rw [hH] at hh
    rw [hh, k328dr_toEnd_one]
  have hFG : F * G = G * F := by
    rw [hF, hG, ← k328dr_toEnd_mul, ← k328dr_toEnd_mul, hfg]
  have hFH : F * H = H * F := by
    rw [hF, hH, ← k328dr_toEnd_mul, ← k328dr_toEnd_mul, hfh]
  have hGH : G * H = H * G := by
    rw [hG, hH, ← k328dr_toEnd_mul, ← k328dr_toEnd_mul, hgh]
  have hFGne' : F ≠ G := by
    intro hh
    apply hfgne
    apply k328dr_toEnd_injective
    rw [hF, hG] at hh
    exact hh
  have hFHne' : F ≠ H := by
    intro hh
    apply hhf
    apply k328dr_toEnd_injective
    rw [hF, hH] at hh
    exact hh.symm
  have hGHne' : G ≠ H := by
    intro hh
    apply hhg
    apply k328dr_toEnd_injective
    rw [hG, hH] at hh
    exact hh.symm
  have hFG2 : (F * G) * (F * G) = 1 := by
    calc (F * G) * (F * G) = F * (G * F) * G := by noncomm_ring
      _ = F * (F * G) * G := by rw [← hFG]
      _ = (F * F) * (G * G) := by noncomm_ring
      _ = 1 := by rw [hF2, hG2, one_mul]
  have hFGdet : (F * G).det = 1 := by rw [map_mul, hFdet, hGdet, one_mul]
  have hFGne1 : F * G ≠ 1 := by
    intro hh
    apply hFGne'
    have hx : F = (F * G) * G := by rw [mul_assoc, hG2, mul_one]
    rw [hh, one_mul] at hx
    exact hx
  have hFGneH : F * G ≠ H := by
    intro hh
    apply hhfg
    apply Subtype.ext
    apply Matrix.toLin'.injective
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]
    exact hh.symm
  have hFGH : (F * G) * H = H * (F * G) := by
    calc (F * G) * H = F * (G * H) := by noncomm_ring
      _ = F * (H * G) := by rw [hGH]
      _ = (F * H) * G := by noncomm_ring
      _ = (H * F) * G := by rw [hFH]
      _ = H * (F * G) := by noncomm_ring
  have hFGid : F + G + F * G = -1 := k328dr_involution_add_eq_neg_one h2 F G hF2 hG2 hFG hFdet hGdet hF1 hG1 hFGne'
  have hFHid : F + H + F * H = -1 := k328dr_involution_add_eq_neg_one h2 F H hF2 hH2 hFH hFdet hHdet hF1 hH1 hFHne'
  have hGHid : G + H + G * H = -1 := k328dr_involution_add_eq_neg_one h2 G H hG2 hH2 hGH hGdet hHdet hG1 hH1 hGHne'
  have hD_id : (F * G) + H + (F * G) * H = -1 :=
    k328dr_involution_add_eq_neg_one h2 (F * G) H hFG2 hH2 hFGH hFGdet hHdet hFGne1 hH1 hFGneH
  have hA : (1 + F) * (1 + H) = 0 := by
    have hexp : (1 + F) * (1 + H) = 1 + (F + H + F * H) := by noncomm_ring
    rw [hexp, hFHid]; abel
  have hB : (1 + G) * (1 + H) = 0 := by
    have hexp : (1 + G) * (1 + H) = 1 + (G + H + G * H) := by noncomm_ring
    rw [hexp, hGHid]; abel
  have hD : (1 + F * G) * (1 + H) = 0 := by
    have hexp : (1 + F * G) * (1 + H) = 1 + ((F * G) + H + (F * G) * H) := by noncomm_ring
    rw [hexp, hD_id]; abel
  have hABD : (1 + F) + (1 + G) + (1 + F * G) = 2 • (1 : Module.End E (Fin 3 → E)) := by
    have h3 : (1 + F) + (1 + G) + (1 + F * G) =
        (3 : ℕ) • (1 : Module.End E (Fin 3 → E)) + (F + G + F * G) := by abel
    rw [h3, hFGid]
    rw [show (3 : ℕ) • (1 : Module.End E (Fin 3 → E)) + (-1) = 2 • 1 from by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, add_smul, one_smul]; abel]
  have hmul : ((1 + F) + (1 + G) + (1 + F * G)) * (1 + H) = 0 := by
    rw [add_mul, add_mul, hA, hB, hD]; abel
  have h2C : (2 : E) • ((1 : Module.End E (Fin 3 → E)) + H) = 0 := by
    have h := hmul
    rw [hABD, k328dr_nsmul_one_mul] at h
    simpa [two_nsmul, two_smul] using h
  have hC : (1 : Module.End E (Fin 3 → E)) + H = 0 := by
    rcases smul_eq_zero.mp h2C with h | h
    · exact absurd h h2
    · exact h
  have hHneg : H = -1 := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hC
  have hdetneg : (LinearMap.det (-1 : Module.End E (Fin 3 → E))) = -1 := by
    have he : (-1 : Module.End E (Fin 3 → E)) = (-1 : E) • (1 : Module.End E (Fin 3 → E)) := by
      ext x; simp
    rw [he, LinearMap.det_smul, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    norm_num
  rw [hHneg, hdetneg] at hHdet
  exact k328dr_neg_one_ne_one' h2 hHdet

private theorem k328dr_false_of_elemAbelian_card_eight {E : Type*} [Field E] {T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E)}
    [hFT : Fintype ↥T] (h2 : (2 : E) ≠ 0) (hsq : ∀ t ∈ T, t ^ 2 = 1)
    (hcomm : ∀ t ∈ T, ∀ s ∈ T, t * s = s * t) (hcard : Nat.card T = 8) : False := by
  classical
  have hcard' : Fintype.card ↥T = 8 := by rwa [Nat.card_eq_fintype_card] at hcard
  obtain ⟨f, -, hf1⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({(1 : ↥T)} : Finset ↥T)) (t := Finset.univ)
    (by rw [Finset.card_singleton, Finset.card_univ, hcard']; norm_num)
  simp only [Finset.mem_singleton] at hf1
  have hgcard : ({(1 : ↥T), f} : Finset ↥T).card < Fintype.card ↥T := by
    have h := Finset.card_insert_le (1 : ↥T) ({f} : Finset ↥T)
    rw [Finset.card_singleton] at h
    rw [hcard']
    omega
  obtain ⟨g, -, hg'⟩ := Finset.exists_mem_notMem_of_card_lt_card hgcard
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hg'
  have hhcard : ({(1 : ↥T), f, g, f * g} : Finset ↥T).card < Fintype.card ↥T := by
    have h1 := Finset.card_insert_le (1 : ↥T) ({f, g, f * g} : Finset ↥T)
    have h2 := Finset.card_insert_le f ({g, f * g} : Finset ↥T)
    have h3 := Finset.card_insert_le g ({(f * g)} : Finset ↥T)
    rw [Finset.card_singleton] at h3
    rw [hcard']
    omega
  obtain ⟨hh, -, hhh'⟩ := Finset.exists_mem_notMem_of_card_lt_card hhcard
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or,
    not_or, not_or] at hhh'
  have hf2 : ((f : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) ^ 2 = 1 := hsq f f.2
  have hg2 : ((g : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) ^ 2 = 1 := hsq g g.2
  have hh2 : ((hh : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) ^ 2 = 1 := hsq hh hh.2
  have hf1' : ((f : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) ≠ 1 := by
    intro hq; exact hf1 (Subtype.ext hq)
  have hg1' : ((g : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) ≠ 1 := by
    intro hq; exact hg'.1 (Subtype.ext hq)
  have hh1' : ((hh : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) ≠ 1 := by
    intro hq; exact hhh'.1 (Subtype.ext hq)
  have hfg' : ((f : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) *
      ((g : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) =
      ((g : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) *
      ((f : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) := hcomm f f.2 g g.2
  have hfh' : ((f : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) *
      ((hh : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) =
      ((hh : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) *
      ((f : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) := hcomm f f.2 hh hh.2
  have hgh' : ((g : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) *
      ((hh : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) =
      ((hh : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) *
      ((g : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) := hcomm g g.2 hh hh.2
  have hfgne' : ((f : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) ≠
      ((g : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) := by
    intro hq; exact hg'.2 (Subtype.ext hq.symm)
  have hhf' : ((hh : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) ≠
      ((f : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) := by
    intro hq; exact hhh'.2.1 (Subtype.ext hq)
  have hhg' : ((hh : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) ≠
      ((g : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) := by
    intro hq; exact hhh'.2.2.1 (Subtype.ext hq)
  have hhfg' : ((hh : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) ≠
      ((f : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) *
      ((g : ↥T) : Matrix.SpecialLinearGroup (Fin 3) E) := by
    intro hq
    apply hhh'.2.2.2
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hq
  exact k328dr_false_of_three_involutions h2 hf2 hg2 hh2 hf1' hg1' hh1' hfg' hfh' hgh' hfgne' hhf' hhg' hhfg'




theorem k328det_e8OfPos :
    ∀ (Y : Type) [Group Y] [Finite Y], (LieModel Y .PSL 3 2 2 ∨ LieModel Y .PSU 3 2 3) →
      ∃ A : Subgroup Y, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧
        Nat.card A = 8 := by
  intro Y _ _ h
  rcases h with h | h
  · obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
      h.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
    let _ : Field K := hfield
    let _ : Finite K := hfinite
    have h4 : Nat.card K = 4 := by rw [hK]; norm_num
    have _ : CharP K 2 := k328de8_charP_two_of_card_pow (K := K) (n := 2) (by simpa using h4)
    obtain ⟨A', hcomm', hsq', hcard'⟩ := k328de8_PSL_exists (K := K) h4
    obtain ⟨A, hcomm, hsq, hcard⟩ := k328de8_pullback e A' hcomm' hsq'
    exact ⟨A, hcomm, hsq, hcard.trans hcard'⟩
  · obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
      h.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
    let _ : Field K := hfield
    let _ : Finite K := hfinite
    have h64 : Nat.card K = 64 := by rw [hK]; norm_num
    have _ : CharP K 2 := k328de8_charP_two_of_card_pow (K := K) (n := 6) (by simpa using h64)
    obtain ⟨A', hcomm', hsq', hcard'⟩ := k328de8_PSU_exists (K := K) h64
    obtain ⟨A, hcomm, hsq, hcard⟩ := k328de8_pullback e A' hcomm' hsq'
    exact ⟨A, hcomm, hsq, hcard.trans hcard'⟩

private theorem k328dr_isCyclic_of_unique_involution {H : Type} [CommGroup H] [Finite H]
    (h2g : IsPGroup 2 H) (c : H) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (huniq : ∀ x : H, x ^ 2 = 1 → x = 1 ∨ x = c) : IsCyclic H := by
  classical
  have hFintypeH : Fintype H := Fintype.ofFinite H
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (Monoid.ExponentExists.of_finite (G := H))
  have hmax : ∀ x : H, orderOf x ≤ orderOf g := fun x => by
    rw [hg]; exact Monoid.orderOf_le_exponent Monoid.ExponentExists.of_finite x
  by_cases htop : Subgroup.zpowers g = ⊤
  · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, htop⟩
  · exfalso
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2) (G := H)).mp h2g g
    have hcorder : orderOf c = 2 := orderOf_eq_prime hc2 hc1
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, pow_zero] at hk
        have := hmax c
        rw [hk, hcorder] at this
        omega
      · exact hkpos
    let N : Subgroup H := Subgroup.zpowers g
    have hNtop : N ≠ ⊤ := fun h => htop h
    have hQ2 : IsPGroup 2 (H ⧸ N) := IsPGroup.to_quotient h2g N
    have hnt : Nontrivial (H ⧸ N) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      apply hNtop
      rw [eq_top_iff]
      intro y _
      have hy : (QuotientGroup.mk' N) y = 1 := Subsingleton.elim _ _
      rw [QuotientGroup.mk'_apply] at hy
      exact (QuotientGroup.eq_one_iff (N := N) y).mp hy
    obtain ⟨n, hnpos, hncard⟩ := (IsPGroup.nontrivial_iff_card (p := 2) hQ2).mp hnt
    have h2dvd : 2 ∣ Nat.card (H ⧸ N) := by
      rw [hncard]; exact dvd_pow_self 2 hnpos.ne'
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (N := N) q
    have hq2 : q ^ 2 = 1 := by rw [← hq]; exact pow_orderOf_eq_one q
    have hq1 : q ≠ 1 := by
      intro h; rw [h, orderOf_one] at hq; exact absurd hq (by norm_num)
    have hxN : x ∉ N := by
      intro hmem
      have h1 : (QuotientGroup.mk' N) x = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff (N := N) x).mpr hmem
      rw [hx] at h1
      exact hq1 h1
    have hx2 : x ^ 2 ∈ N := by
      have h1 : ((QuotientGroup.mk' N) x) ^ 2 = 1 := by rw [hx, hq2]
      have h2 : (QuotientGroup.mk' N) (x ^ 2) = 1 := by simpa [map_pow] using h1
      rw [QuotientGroup.mk'_apply] at h2
      exact (QuotientGroup.eq_one_iff (N := N) (x ^ 2)).mp h2
    have hx2' : x ^ 2 ∈ (Finset.range (orderOf g)).image (g ^ ·) :=
      mem_zpowers_iff_mem_range_orderOf.mp hx2
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx2'
    have hginv2 : (g ^ 2 ^ (k - 1)) ^ 2 = 1 := by
      rw [← pow_mul, show 2 ^ (k - 1) * 2 = 2 ^ k by
        rw [← pow_succ, Nat.sub_add_cancel hkpos]]
      rw [← hk]
      exact pow_orderOf_eq_one g
    have hginv1 : g ^ 2 ^ (k - 1) ≠ 1 := by
      intro h
      have hdvd : orderOf g ∣ 2 ^ (k - 1) := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hk] at hdvd
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (by positivity)) hdvd
      rw [Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)] at hle
      omega
    have hginvmem : g ^ 2 ^ (k - 1) ∈ N := N.pow_mem (Subgroup.mem_zpowers g) _
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' j
    ·
      have hy2 : (x * (g ^ m)⁻¹) ^ 2 = 1 := by
        rw [mul_pow, ← hj, hm]
        group
      have hyN : x * (g ^ m)⁻¹ ∉ N := by
        intro hmem
        apply hxN
        have h2 : x = (x * (g ^ m)⁻¹) * g ^ m := by group
        rw [h2]
        exact N.mul_mem hmem (N.pow_mem (Subgroup.mem_zpowers g) m)
      have hy1 : x * (g ^ m)⁻¹ ≠ 1 := by
        intro h; exact hyN (by rw [h]; exact N.one_mem)
      have hyc : x * (g ^ m)⁻¹ = c := (huniq _ hy2).resolve_left hy1
      have hcN : c ∉ N := by rw [← hyc]; exact hyN
      have hceq : g ^ 2 ^ (k - 1) = c := (huniq _ hginv2).resolve_left hginv1
      exact hcN (hceq ▸ hginvmem)
    ·
      have hy2 : (x * (g ^ m)⁻¹) ^ 2 = g := by
        rw [mul_pow, ← hj, hm, pow_succ]
        group
      have hyord : orderOf (x * (g ^ m)⁻¹) = 2 ^ (k + 1) := by
        apply orderOf_eq_prime_pow
        · intro h
          have h1 : (x * (g ^ m)⁻¹) ^ 2 ^ k = g ^ 2 ^ (k - 1) := by
            rw [show 2 ^ k = 2 * 2 ^ (k - 1) by
              rw [← pow_succ', Nat.sub_add_cancel hkpos], pow_mul, hy2]
          rw [h1] at h
          exact hginv1 h
        · rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ'], pow_mul, hy2, ← hk]
          exact pow_orderOf_eq_one g
      have := hmax (x * (g ^ m)⁻¹)
      rw [hyord, hk] at this
      rw [pow_succ] at this
      have hpos : 0 < 2 ^ k := by positivity
      omega

private theorem k328dr_closure_pair_comm {G : Type} [Group G] {a b : G} (hab : a * b = b * a) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set G),
      ∀ y ∈ Subgroup.closure ({a, b} : Set G), x * y = y * x := by
  intro x hx y hy
  induction hx, hy using Subgroup.closure_induction₂ with
  | mem p q hp hq =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [hab]
  | one_left q hq => simp
  | one_right q hq => simp
  | mul_left p q z hp hq hz hpz hqz =>
      calc (p * q) * z = p * (q * z) := by group
        _ = p * (z * q) := by rw [hqz]
        _ = (p * z) * q := by group
        _ = (z * p) * q := by rw [hpz]
        _ = z * (p * q) := by group
  | mul_right y z x hy hz hx hxy hxz =>
      calc x * (y * z) = (x * y) * z := by group
        _ = (y * x) * z := by rw [hxy]
        _ = y * (x * z) := by group
        _ = y * (z * x) := by rw [hxz]
        _ = (y * z) * x := by group
  | inv_left p q hp hq hpq =>
      calc p⁻¹ * q = p⁻¹ * (q * p) * p⁻¹ := by group
        _ = p⁻¹ * (p * q) * p⁻¹ := by rw [hpq]
        _ = q * p⁻¹ := by group
  | inv_right p q hp hq hpq =>
      calc p * q⁻¹ = q⁻¹ * (q * p) * q⁻¹ := by group
        _ = q⁻¹ * (p * q) * q⁻¹ := by rw [hpq]
        _ = q⁻¹ * p := by group

private theorem k328dr_finite_of_lieModel (W : Type) [Group W]
    (hW : LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3) : Finite W := by
  rcases hW with h | h
  · obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
      h.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
    let hFieldK : Field K := hfield
    let hFiniteK : Finite K := hfinite
    exact Finite.of_equiv (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) e.toEquiv.symm
  · obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
      h.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
    let hFieldK : Field K := hfield
    let hFiniteK : Finite K := hfinite
    exact Finite.of_equiv (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ 3) K)) e.toEquiv.symm

private theorem k328dr_isCyclic_map_quotient {G : Type*} [Group G] (H : Subgroup G)
    (hH : IsCyclic ↥H) (N : Subgroup G) [N.Normal] :
    IsCyclic ↥(H.map (QuotientGroup.mk' N)) := by
  let f : ↥H →* ↥(H.map (QuotientGroup.mk' N)) :=
    { toFun := fun x => ⟨QuotientGroup.mk' N x, Subgroup.mem_map_of_mem _ x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  exact isCyclic_of_surjective f (by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)

private theorem k328dr_eq_of_involutions_of_isCyclic {K : Type*} [Group K] [Finite K]
    [IsCyclic K] (u v : K) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u = v := by
  classical
  have heq : Subgroup.zpowers u = Subgroup.zpowers v := by
    apply IsCyclic.subgroup_eq_iff_card_eq.mpr
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hu2 hu1, orderOf_eq_prime hv2 hv1]
  have hmem : u ∈ Subgroup.zpowers v := heq ▸ Subgroup.mem_zpowers u
  have hrange := (mem_zpowers_iff_mem_range_orderOf (x := v) (y := u)).mp hmem
  rw [orderOf_eq_prime hv2 hv1, Finset.mem_image] at hrange
  obtain ⟨j, hjrange, hj⟩ := hrange
  rw [Finset.mem_range] at hjrange
  interval_cases j
  · rw [pow_zero] at hj
    exact absurd hj.symm hu1
  · rw [pow_one] at hj
    exact hj.symm

private theorem k328dr_false_of_cyclic_quotient {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (H : Subgroup G) (hH : IsCyclic ↥H) (t s : G) (ht : t ∈ H)
    (hs : s ∈ H) (ht2 : t ^ 2 ∈ N) (hs2 : s ^ 2 ∈ N) (htN : t ∉ N) (hsN : s ∉ N)
    (hts : s * t⁻¹ ∉ N) : False := by
  have : IsCyclic ↥(H.map (QuotientGroup.mk' N)) := k328dr_isCyclic_map_quotient H hH N
  have htbar2 : (QuotientGroup.mk' N t) ^ 2 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (N := N) (t ^ 2)).mpr ht2
  have htbar1 : QuotientGroup.mk' N t ≠ 1 := by
    intro h
    apply htN
    rw [QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff (N := N) t).mp h
  have hsbar2 : (QuotientGroup.mk' N s) ^ 2 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (N := N) (s ^ 2)).mpr hs2
  have hsbar1 : QuotientGroup.mk' N s ≠ 1 := by
    intro h
    apply hsN
    rw [QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff (N := N) s).mp h
  have hne : QuotientGroup.mk' N t ≠ QuotientGroup.mk' N s := by
    intro h
    apply hts
    have h1 : QuotientGroup.mk' N (s * t⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h, mul_inv_cancel]
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff (N := N) (s * t⁻¹)).mp h1
  have key := k328dr_eq_of_involutions_of_isCyclic
    (⟨QuotientGroup.mk' N t, Subgroup.mem_map_of_mem _ ht⟩ :
      ↥(H.map (QuotientGroup.mk' N)))
    ⟨QuotientGroup.mk' N s, Subgroup.mem_map_of_mem _ hs⟩
    (Subtype.ext htbar2) (Subtype.ext hsbar2) (fun h => htbar1 (congrArg Subtype.val h))
    (fun h => hsbar1 (congrArg Subtype.val h))
  exact hne (congrArg Subtype.val key)

private theorem k328dr_exists_cyclic_closure {G : Type} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (C : Subgroup G) (hC : C ≤ Subgroup.center G) (c : G) (hcC : c ∈ C) (hc2 : c ^ 2 = 1)
    (hc1 : c ≠ 1) (huniq : ∀ x : G, x ^ 2 = 1 → x = 1 ∨ x = c) (t s : G)
    (hts : s * t = t * s) : ∃ H : Subgroup G, t ∈ H ∧ s ∈ H ∧ IsCyclic ↥H := by
  let H : Subgroup G := Subgroup.closure (({t, s} : Set G) ∪ (C : Set G))
  have hcH : c ∈ H := Subgroup.subset_closure (Or.inr hcC)
  have htH : t ∈ H := Subgroup.subset_closure (Or.inl (by simp))
  have hsH : s ∈ H := Subgroup.subset_closure (Or.inl (by simp))
  have hHcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
    intro x hx y hy
    induction hx, hy using Subgroup.closure_induction₂ with
    | mem p q hp hq =>
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
        rcases hp with hp | hp
        · rcases hp with hp | hp
          · rw [hp]
            rcases hq with hq | hq
            · rcases hq with hq | hq
              · rw [hq]
              · rw [hq]; exact hts.symm
            · exact Subgroup.mem_center_iff.mp (hC hq) t
          · rw [hp]
            rcases hq with hq | hq
            · rcases hq with hq | hq
              · rw [hq]; exact hts
              · rw [hq]
            · exact Subgroup.mem_center_iff.mp (hC hq) s
        · rcases hq with hq | hq
          · rcases hq with hq | hq
            · rw [hq]; exact (Subgroup.mem_center_iff.mp (hC hp) t).symm
            · rw [hq]; exact (Subgroup.mem_center_iff.mp (hC hp) s).symm
          · exact (Subgroup.mem_center_iff.mp (hC hp) q).symm
    | one_left q hq => simp
    | one_right q hq => simp
    | mul_left p q z hp hq hz hpz hqz =>
        calc (p * q) * z = p * (q * z) := by group
          _ = p * (z * q) := by rw [hqz]
          _ = (p * z) * q := by group
          _ = (z * p) * q := by rw [hpz]
          _ = z * (p * q) := by group
    | mul_right y z x hy hz hx hxy hxz =>
        calc x * (y * z) = (x * y) * z := by group
          _ = (y * x) * z := by rw [hxy]
          _ = y * (x * z) := by group
          _ = y * (z * x) := by rw [hxz]
          _ = (y * z) * x := by group
    | inv_left p q hp hq hpq =>
        calc p⁻¹ * q = p⁻¹ * (q * p) * p⁻¹ := by group
          _ = p⁻¹ * (p * q) * p⁻¹ := by rw [hpq]
          _ = q * p⁻¹ := by group
    | inv_right p q hp hq hpq =>
        calc p * q⁻¹ = q⁻¹ * (q * p) * q⁻¹ := by group
          _ = q⁻¹ * (p * q) * q⁻¹ := by rw [hpq]
          _ = q⁻¹ * p := by group
  have hH2 : IsPGroup 2 H := hG.to_subgroup H
  have hHuniq : ∀ x : ↥H, x ^ 2 = 1 → x = 1 ∨ x = ⟨c, hcH⟩ := by
    rintro ⟨x, hxH⟩ hx2
    rcases huniq x (congrArg Subtype.val hx2) with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  have hcH2 : (⟨c, hcH⟩ : ↥H) ^ 2 = 1 := by
    apply Subtype.ext; show c ^ 2 = 1; exact hc2
  have hcH1 : (⟨c, hcH⟩ : ↥H) ≠ 1 := by
    intro h; exact hc1 (congrArg Subtype.val h)
  exact ⟨H, htH, hsH,
    @k328dr_isCyclic_of_unique_involution ↥H
      { (inferInstance : Group ↥H) with
        mul_comm := fun a b => Subtype.ext (hHcomm a a.2 b b.2) } _
      hH2 ⟨c, hcH⟩ hcH2 hcH1 hHuniq⟩

private theorem k328dr_exists_commuting_outside {G : Type*} [Group G] [Finite G] (C : Subgroup G)
    (hC : C ≤ Subgroup.center G) (hindex : Nat.card (G ⧸ C) = 8) (t c : G) (hcC : c ∈ C)
    (hcomm : ∀ x : G, ⁅t, x⁆ = 1 ∨ ⁅t, x⁆ = c) :
    ∃ s : G, s ∉ C ∧ s * t⁻¹ ∉ C ∧ s * t = t * s := by
  classical
  have hcomm_mem : ∀ x : G, ⁅t, x⁆ ∈ C := by
    intro x
    rcases hcomm x with h | h
    · rw [h]; exact C.one_mem
    · rw [h]; exact hcC
  let ψ : G →* ↥C :=
    { toFun := fun x => ⟨⁅t, x⁆, hcomm_mem x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change ⁅t, x * y⁆ = ⁅t, x⁆ * ⁅t, y⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hx : x * ⁅t, y⁆ * x⁻¹ = ⁅t, y⁆ := by
          have hz : ⁅t, y⁆ ∈ Subgroup.center G := hC (hcomm_mem y)
          rw [Subgroup.mem_center_iff.mp hz x, mul_assoc, mul_inv_cancel, mul_one]
        calc ⁅t, x⁆ * x * ⁅t, y⁆ * x⁻¹
            = ⁅t, x⁆ * (x * ⁅t, y⁆ * x⁻¹) := by group
          _ = ⁅t, x⁆ * ⁅t, y⁆ := by rw [hx] }
  have hψrange : ∀ y ∈ ψ.range, y = 1 ∨ y = (⟨c, hcC⟩ : ↥C) := by
    intro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rcases hcomm x with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  have hψrange_card : Nat.card ψ.range ≤ 2 := by
    have hFintypeRange : Fintype ↥(ψ.range) := Fintype.ofFinite _
    have hinj : Function.Injective
        (fun y : ↥(ψ.range) => if (y : ↥C) = 1 then (0 : Fin 2) else 1) := by
      intro a b hab
      have ha := hψrange a a.2
      have hb := hψrange b b.2
      by_cases ha1 : (a : ↥C) = 1
      · have hindb : (if (b : ↥C) = 1 then (0 : Fin 2) else 1) = 0 := by
          simpa [ha1] using hab.symm
        have hb1 : (b : ↥C) = 1 := by
          by_contra hbne
          rw [if_neg hbne] at hindb
          exact absurd hindb (by decide)
        exact Subtype.ext (ha1.trans hb1.symm)
      · have hindb : (if (b : ↥C) = 1 then (0 : Fin 2) else 1) = 1 := by
          simpa [ha1] using hab.symm
        have hbne : (b : ↥C) ≠ 1 := by
          intro hb1; rw [if_pos hb1] at hindb; exact absurd hindb (by decide)
        have ha' : (a : ↥C) = ⟨c, hcC⟩ := ha.resolve_left ha1
        have hb' : (b : ↥C) = ⟨c, hcC⟩ := hb.resolve_left hbne
        exact Subtype.ext (ha'.trans hb'.symm)
    calc Nat.card ↥(ψ.range) ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
  have hcardG : Nat.card G = Nat.card ↥C * 8 := by
    rw [← Subgroup.card_mul_index (H := C), Subgroup.index_eq_card, hindex]
  have hkerG : Nat.card ψ.ker * Nat.card ψ.range = Nat.card G :=
    Subgroup.card_ker_mul_card_range ψ
  have hker_ge : 4 * Nat.card ↥C ≤ Nat.card ψ.ker := by
    have h1 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card ↥C * 8 := by
      rw [hkerG, hcardG]
    have hpos : 0 < Nat.card ψ.range := Nat.card_pos
    rcases (show Nat.card ψ.range = 1 ∨ Nat.card ψ.range = 2 by omega) with h | h <;>
      rw [h] at h1 <;> omega
  have hFintypeC : Fintype ↥C := Fintype.ofFinite _
  have hFintypeKer : Fintype ↥(ψ.ker) := Fintype.ofFinite _
  let FC : Finset G := Finset.univ.image C.subtype
  let FCt : Finset G := FC.image (· * t)
  let FK : Finset G := Finset.univ.image (ψ.ker).subtype
  have hFCcard : FC.card = Nat.card ↥C := by
    change (Finset.univ.image C.subtype).card = Nat.card ↥C
    rw [Finset.card_image_of_injective (f := ⇑C.subtype) (s := Finset.univ)
        (Subgroup.subtype_injective C), Finset.card_univ, Nat.card_eq_fintype_card]
  have hFCtcard : FCt.card = Nat.card ↥C := by
    change (FC.image (· * t)).card = Nat.card ↥C
    rw [Finset.card_image_of_injective _ (mul_left_injective t), hFCcard]
  have hFKcard : FK.card = Nat.card ↥(ψ.ker) := by
    change (Finset.univ.image (ψ.ker).subtype).card = Nat.card ↥(ψ.ker)
    rw [Finset.card_image_of_injective (f := ⇑(ψ.ker).subtype) (s := Finset.univ)
        (Subgroup.subtype_injective (ψ.ker)), Finset.card_univ, Nat.card_eq_fintype_card]
  have hunion_lt : (FC ∪ FCt).card < FK.card := by
    have h1 : (FC ∪ FCt).card ≤ FC.card + FCt.card := Finset.card_union_le _ _
    rw [hFCcard, hFCtcard] at h1
    rw [hFKcard]
    have hCpos : 0 < Nat.card ↥C := Nat.card_pos
    omega
  obtain ⟨s, hsK, hsnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hunion_lt
  have hsψ : s ∈ ψ.ker := by
    rcases Finset.mem_image.mp hsK with ⟨k, -, rfl⟩
    exact k.2
  have hsC : s ∉ C := by
    intro hmem
    apply hsnot
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨s, hmem⟩, Finset.mem_univ _, rfl⟩)
  have hst : s * t⁻¹ ∉ C := by
    intro hmem
    apply hsnot
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_image.mpr ⟨s * t⁻¹,
      Finset.mem_image.mpr ⟨⟨s * t⁻¹, hmem⟩, Finset.mem_univ _, rfl⟩, by group⟩
  refine ⟨s, hsC, hst, ?_⟩
  have h1 : ψ s = 1 := (MonoidHom.mem_ker).mp hsψ
  have h2 : ⁅t, s⁆ = 1 := by
    have := congrArg Subtype.val h1
    simpa [ψ] using this
  exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

private theorem k328dr_false_of_unique_involution_cover {G : Type} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (C : Subgroup G) (hC : C ≤ Subgroup.center G)
    (hindex : Nat.card (G ⧸ C) = 8) (hsq : ∀ x : G, x ^ 2 ∈ C) (hcomm : ∀ x y : G, ⁅x, y⁆ ∈ C)
    (c : G) (hcC : c ∈ C) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (huniq : ∀ x : G, x ^ 2 = 1 → x = 1 ∨ x = c) : False := by
  classical
  have : C.Normal := Subgroup.normal_of_le_center hC
  have hFintypeQ : Fintype (G ⧸ C) := Fintype.ofFinite _
  have hcardQ : Fintype.card (G ⧸ C) = 8 := by
    rw [← Nat.card_eq_fintype_card]; exact hindex
  obtain ⟨q₁, -, hq₁⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({(1 : G ⧸ C)} : Finset _)) (t := Finset.univ)
    (by rw [Finset.card_singleton, Finset.card_univ, hcardQ]; norm_num)
  simp only [Finset.mem_singleton] at hq₁
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (N := C) q₁
  have htC : t ∉ C := by
    intro hmem
    apply hq₁
    rw [← ht, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (N := C) t).mpr hmem
  have hcomm_c : ∀ x : G, ⁅t, x⁆ = 1 ∨ ⁅t, x⁆ = c := by
    intro x
    apply huniq
    have hz : ⁅t, x⁆ ∈ Subgroup.center G := hC (hcomm t x)
    rw [Commute.commutatorElement_pow_left (Subgroup.mem_center_iff.mp hz t) 2,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hC (hsq t)) x).symm
  obtain ⟨s, hsC, hst, hts⟩ := k328dr_exists_commuting_outside C hC hindex t c hcC hcomm_c
  obtain ⟨H, htH, hsH, hHcyc⟩ := k328dr_exists_cyclic_closure hG C hC c hcC hc2 hc1 huniq t s hts
  exact k328dr_false_of_cyclic_quotient C H hHcyc t s htH hsH (hsq t) (hsq s) htC hsC hst

private theorem k328dr_central_ext_false {E : Type} [Field E] [Finite E] (h2 : (2 : E) ≠ 0)
    (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E)) (hperf : ⁅Y, Y⁆ = Y)
    (W : Type) [Group W] (φ : ↥Y →* W) (hsurj : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center ↥Y)
    (hW : CFSG.Blueprint.LieModel W .PSL 3 2 2 ∨ CFSG.Blueprint.LieModel W .PSU 3 2 3) : False := by
  classical
  have hFiniteW : Finite W := k328dr_finite_of_lieModel W hW
  obtain ⟨A, hAcomm, hAsq, hAcard⟩ := k328det_e8OfPos W hW
  let B : Subgroup ↥Y := A.comap φ
  let φB : ↥B →* A :=
    { toFun := fun b => ⟨φ b, b.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφBsurj : Function.Surjective φB := by
    intro a
    obtain ⟨y, hy⟩ := hsurj a
    have hyB : y ∈ B := by
      rw [Subgroup.mem_comap, hy]
      exact a.2
    exact ⟨⟨y, hyB⟩, Subtype.ext hy⟩
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)
  obtain ⟨T, -⟩ : ∃ T : Sylow 2 ↥B, (⊥ : Subgroup ↥B) ≤ T :=
    IsPGroup.exists_le_sylow (p := 2) (P := (⊥ : Subgroup ↥B)) IsPGroup.of_bot
  let TB : Subgroup ↥B := T
  let φT : ↥TB →* A := φB.comp TB.subtype
  let C2 : Subgroup ↥TB := φT.ker
  let θ : ↥TB →* ↥Y := B.subtype.comp TB.subtype
  have hTBmap : TB.map φB = ⊤ := by
    have htop : IsPGroup 2 (⊤ : Subgroup A) := IsPGroup.to_subgroup hA2 ⊤
    have hle : (⊤ : Subgroup A) ≤ (T.mapSurjective hφBsurj : Subgroup A) :=
      IsPGroup.le_sylow_of_normal (N := ⊤) htop (T.mapSurjective hφBsurj)
    have hcoe : (T.mapSurjective hφBsurj : Subgroup A) = TB.map φB :=
      Sylow.coe_mapSurjective (f := φB) hφBsurj T
    rw [hcoe] at hle
    exact top_le_iff.mp hle
  have hφTsurj : Function.Surjective φT := by
    intro a
    have ha : a ∈ TB.map φB := by rw [hTBmap]; exact Subgroup.mem_top a
    rw [Subgroup.mem_map] at ha
    obtain ⟨b, hb, hba⟩ := ha
    exact ⟨⟨b, hb⟩, Subtype.ext (congrArg Subtype.val hba)⟩
  have hcardTQ : Nat.card (↥TB ⧸ C2) = 8 := by
    rw [show Nat.card (↥TB ⧸ C2) = Nat.card A from
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (φ := φT) hφTsurj).toEquiv, hAcard]
  have hC2leC : ∀ t : ↥TB, t ∈ C2 → θ t ∈ φ.ker := by
    intro t ht
    have h1 : φT t = 1 := (MonoidHom.mem_ker).mp ht
    have h2 : φ (θ t) = 1 := by
      have h3 : φB (t : ↥B) = 1 := by simpa [φT] using h1
      have := congrArg Subtype.val h3
      simpa [φB, θ] using this
    exact (MonoidHom.mem_ker).mpr h2
  by_cases hC2bot : C2 = ⊥
  ·
    have hcardTB : Nat.card ↥TB = 8 := by
      rw [← Subgroup.index_bot, Subgroup.index_eq_card, ← hC2bot]
      exact hcardTQ
    have hsqTB : ∀ t : ↥TB, t ^ 2 = 1 := by
      intro t
      have h1 : (φT t) ^ 2 = 1 := by
        apply Subtype.ext
        exact hAsq (φT t) (φT t).2
      have h2 : t ^ 2 ∈ C2 := by
        rw [MonoidHom.mem_ker]
        simpa [map_pow] using h1
      rw [hC2bot, Subgroup.mem_bot] at h2
      exact h2
    have hcommTB : ∀ t s : ↥TB, t * s = s * t := by
      intro t s
      have h1 : φT (t * s) = φT (s * t) := by
        rw [map_mul, map_mul]
        apply Subtype.ext
        exact hAcomm (φT t) (φT t).2 (φT s) (φT s).2
      have h2 : t * s * (s * t)⁻¹ ∈ C2 := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
      rw [hC2bot, Subgroup.mem_bot] at h2
      exact mul_inv_eq_one.mp h2
    let θ' : ↥TB →* Matrix.SpecialLinearGroup (Fin 3) E := Y.subtype.comp θ
    have hθ'inj : Function.Injective θ' := by
      intro a b hab
      exact Subtype.coe_injective (Subtype.coe_injective (Subtype.coe_injective hab))
    let T' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E) := (⊤ : Subgroup ↥TB).map θ'
    have hcardT' : Nat.card T' = 8 := by
      rw [show Nat.card T' = Nat.card (⊤ : Subgroup ↥TB) from
        Subgroup.card_map_of_injective hθ'inj, Subgroup.card_top, hcardTB]
    have hsqT' : ∀ t ∈ T', t ^ 2 = 1 := by
      intro t ht
      rw [Subgroup.mem_map] at ht
      obtain ⟨a, -, rfl⟩ := ht
      rw [← map_pow, hsqTB a, map_one]
    have hcommT' : ∀ t ∈ T', ∀ s ∈ T', t * s = s * t := by
      intro t ht s hs
      rw [Subgroup.mem_map] at ht hs
      obtain ⟨a, -, rfl⟩ := ht
      obtain ⟨b, -, rfl⟩ := hs
      rw [← map_mul, ← map_mul, hcommTB a b]
    exact k328dr_false_of_elemAbelian_card_eight (hFT := Fintype.ofFinite ↥T') h2 hsqT' hcommT' hcardT'
  ·
    have hC2ne : C2 ≠ ⊥ := hC2bot
    have hC2nt : Nontrivial ↥C2 := (Subgroup.nontrivial_iff_ne_bot C2).mpr hC2ne
    have hC2p : IsPGroup 2 C2 :=
      IsPGroup.of_injective (p := 2) (hG := T.isPGroup') C2.subtype Subtype.coe_injective
    obtain ⟨n₂, hn₂pos, hn₂card⟩ :=
      (IsPGroup.nontrivial_iff_card (p := 2) hC2p).mp hC2nt
    have hFintypeC2 : Fintype ↥C2 := Fintype.ofFinite ↥C2
    have h2dvdC2 : 2 ∣ Nat.card ↥C2 := by rw [hn₂card]; exact dvd_pow_self 2 hn₂pos.ne'
    obtain ⟨c₀, hc₀order⟩ := exists_prime_orderOf_dvd_card' 2 h2dvdC2
    let c : ↥TB := (c₀ : ↥C2)
    have hcC2 : c ∈ C2 := c₀.2
    have hcorder : orderOf c = 2 := by rw [Subgroup.orderOf_coe]; exact hc₀order
    have hc2 : c ^ 2 = 1 := by rw [← hcorder]; exact pow_orderOf_eq_one c
    have hc1 : c ≠ 1 := by
      intro h; rw [h, orderOf_one] at hcorder; exact absurd hcorder (by norm_num)
    have hθinj : Function.Injective θ := by
      intro a b hab; exact Subtype.coe_injective (Subtype.coe_injective hab)
    have hθcC : θ c ∈ φ.ker := hC2leC c hcC2
    have hθc_center : θ c ∈ Subgroup.center ↥Y := hker hθcC
    have hθc2 : (θ c) ^ 2 = 1 := by rw [← map_pow, hc2, map_one]
    have hθc1 : θ c ≠ 1 := fun h => hc1 (hθinj (h.trans (map_one θ).symm))
    have huniqY : ∀ x : ↥Y, x ^ 2 = 1 → x = 1 ∨ x = θ c := by
      intro x hx2
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (k328dr_eq_of_commute_involutions Y h2 hperf (θ c) hθc_center hθc2 hθc1
          x (θ c) hx2 hθc2 hx1 hθc1 (Subgroup.mem_center_iff.mp hθc_center x))
    have hC2center : C2 ≤ Subgroup.center ↥TB := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro y
      apply hθinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp (hker (hC2leC z hz)) (θ y)
    have hsqTB : ∀ x : ↥TB, x ^ 2 ∈ C2 := by
      intro x
      rw [MonoidHom.mem_ker]
      have h1 : (φT x) ^ 2 = 1 := by apply Subtype.ext; exact hAsq (φT x) (φT x).2
      simpa [map_pow] using h1
    have hcommTB : ∀ x y : ↥TB, ⁅x, y⁆ ∈ C2 := by
      intro x y
      rw [MonoidHom.mem_ker, map_commutatorElement]
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      apply Subtype.ext
      exact hAcomm (φT x) (φT x).2 (φT y) (φT y).2
    have huniqTB : ∀ x : ↥TB, x ^ 2 = 1 → x = 1 ∨ x = c := by
      intro x hx2
      have hx2Y : (θ x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
      rcases huniqY (θ x) hx2Y with h | h
      · left; exact hθinj (h.trans (map_one θ).symm)
      · right; exact hθinj h
    exact k328dr_false_of_unique_involution_cover T.isPGroup' C2 hC2center hcardTQ hsqTB hcommTB
      c hcC2 hc2 hc1 huniqTB



private theorem k328dr_W_isPerfect {W : Type} [Group W]
    (hW : LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3) : Group.IsPerfect W := by
  have h3 : (3 : ℕ) ≠ 0 := by norm_num
  rcases hW with h | h
  · obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero h3
    let hFieldK : Field K := hfield
    have hPerfSL : Group.IsPerfect (StatedSL 3 K) :=
      CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K
    have hPerfPSL : Group.IsPerfect (StatedProj (StatedSL 3 K)) :=
      Group.IsPerfect.ofSurjective
        (f := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)))
        (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero h3
    let hFieldK : Field K := hfield
    have hPerfSU : Group.IsPerfect (StatedSU 3 8 K) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (n := 3) (p := 2) (f := 3) hK
        (by norm_num) (by norm_num)
    have hPerfPSU : Group.IsPerfect (StatedProj (StatedSU 3 8 K)) :=
      Group.IsPerfect.ofSurjective
        (f := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 8 K)))
        (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem k328det_sl3NoCentralExt : ∀ (E : Type) [Field E] [Finite E], ringChar E ≠ 2 →
      ∀ (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E)) (W : Type) [Group W] (φ : ↥Y →* W),
        Function.Surjective φ → φ.ker ≤ Subgroup.center ↥Y →
          ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3) := by
  intro E _ _ hchar Y W _ φ hsurj hker hW
  have h2 : (2 : E) ≠ 0 := Ring.two_ne_zero hchar
  classical
  have hFintypeY : Fintype ↥Y := Fintype.ofFinite ↥Y
  let 𝒮 : Finset (Subgroup ↥Y) := Finset.univ.filter (fun H => H.map φ = ⊤)
  have hne : 𝒮.Nonempty := ⟨⊤, by
    simp only [𝒮, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective φ hsurj⟩
  obtain ⟨Y₀, hY₀mem, hY₀min⟩ :=
    Finset.exists_min_image 𝒮 (fun H : Subgroup ↥Y => Nat.card H) hne
  have hY₀surj : Y₀.map φ = ⊤ := (Finset.mem_filter.mp hY₀mem).2
  have hcommle : ⁅Y₀, Y₀⁆ ≤ Y₀ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Y₀.mul_mem (Y₀.mul_mem (Y₀.mul_mem ha hb) (Y₀.inv_mem ha)) (Y₀.inv_mem hb)
  have hY₀perf : ⁅Y₀, Y₀⁆ = Y₀ := by
    have hWperf := k328dr_W_isPerfect hW
    have hder : (⁅Y₀, Y₀⁆ : Subgroup ↥Y).map φ = ⊤ := by
      rw [Subgroup.map_commutator, hY₀surj]
      exact Group.IsPerfect.commutator_eq_top
    have hmem : ⁅Y₀, Y₀⁆ ∈ 𝒮 := by
      simp only [𝒮, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hder
    have h1 : Nat.card Y₀ ≤ Nat.card (⁅Y₀, Y₀⁆ : Subgroup ↥Y) := hY₀min _ hmem
    exact Subgroup.eq_of_le_of_card_ge hcommle h1
  let Y₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E) := Y₀.map Y.subtype
  have hY₁perf : ⁅Y₁, Y₁⁆ = Y₁ := by
    rw [show Y₁ = Y₀.map Y.subtype from rfl, ← Subgroup.map_commutator, hY₀perf]
  let e : ↥Y₀ ≃* ↥Y₁ :=
    Subgroup.equivMapOfInjective Y₀ Y.subtype (Subgroup.subtype_injective Y)
  let φ₁ : ↥Y₁ →* W := (φ.comp Y₀.subtype).comp e.symm.toMonoidHom
  have hφ₁surj : Function.Surjective φ₁ := by
    intro w
    obtain ⟨x, hx, hxw⟩ :=
      Subgroup.mem_map.mp (show w ∈ Y₀.map φ by rw [hY₀surj]; exact Subgroup.mem_top w)
    refine ⟨e ⟨x, hx⟩, ?_⟩
    show φ (Y₀.subtype (e.symm (e ⟨x, hx⟩))) = w
    rw [MulEquiv.symm_apply_apply]
    simpa using hxw
  have hφ₁ker : φ₁.ker ≤ Subgroup.center ↥Y₁ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro z
    have hx' : Y₀.subtype (e.symm x) ∈ φ.ker := by
      rw [MonoidHom.mem_ker] at hx ⊢
      exact hx
    have hxcen : Y₀.subtype (e.symm x) ∈ Subgroup.center ↥Y := hker hx'
    have h1 : e.symm x * e.symm z = e.symm z * e.symm x := by
      apply Subgroup.subtype_injective Y₀
      simpa only [map_mul] using
        (Subgroup.mem_center_iff.mp hxcen (Y₀.subtype (e.symm z))).symm
    have hcomm2 : e.symm (z * x) = e.symm (x * z) := by
      rw [map_mul, map_mul, ← h1]
    exact e.symm.injective hcomm2
  exact k328dr_central_ext_false h2 Y₁ hY₁perf W φ₁ hφ₁surj hφ₁ker hW


private theorem k328deig_mapsTo {E : Type} [Field E] {n : ℕ}
    (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E))
    {z : Matrix.SpecialLinearGroup (Fin n) E} (_hz : z ∈ Y)
    (hzcomm : ∀ y ∈ Y, Commute z y) (μ : E) (y : ↥Y) :
    ∀ v ∈ Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ,
      (Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E) :
        (Fin n → E) →ₗ[E] (Fin n → E)) v ∈
      Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ := by
  intro v hv
  have hTz : (Matrix.SpecialLinearGroup.toLin' z :
      (Fin n → E) →ₗ[E] (Fin n → E)) = Matrix.toLin' (z : Matrix (Fin n) (Fin n) E) :=
    Matrix.SpecialLinearGroup.toLin'_to_linearMap z
  rw [← hTz] at hv ⊢
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hc : (Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E) :
        (Fin n → E) →ₗ[E] (Fin n → E)) *
        (Matrix.SpecialLinearGroup.toLin' z : (Fin n → E) →ₗ[E] (Fin n → E)) =
      (Matrix.SpecialLinearGroup.toLin' z : (Fin n → E) →ₗ[E] (Fin n → E)) *
        (Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E) :
          (Fin n → E) →ₗ[E] (Fin n → E)) := by
    rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul]
    congr 1
    rw [← map_mul, ← map_mul, (hzcomm (y : Matrix.SpecialLinearGroup (Fin n) E) y.2).eq]
  calc
    (Matrix.SpecialLinearGroup.toLin' z : (Fin n → E) →ₗ[E] (Fin n → E))
        ((Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E) :
          (Fin n → E) →ₗ[E] (Fin n → E)) v)
        = ((Matrix.SpecialLinearGroup.toLin' z : (Fin n → E) →ₗ[E] (Fin n → E)) *
            (Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E) :
              (Fin n → E) →ₗ[E] (Fin n → E))) v := by
          rw [Module.End.mul_eq_comp]; rfl
    _ = ((Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E) :
              (Fin n → E) →ₗ[E] (Fin n → E)) *
            (Matrix.SpecialLinearGroup.toLin' z : (Fin n → E) →ₗ[E] (Fin n → E))) v := by rw [hc]
    _ = (Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E) :
          (Fin n → E) →ₗ[E] (Fin n → E))
          ((Matrix.SpecialLinearGroup.toLin' z : (Fin n → E) →ₗ[E] (Fin n → E)) v) := by
          rw [Module.End.mul_eq_comp]; rfl
    _ = (Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E) :
          (Fin n → E) →ₗ[E] (Fin n → E)) (μ • v) := by rw [hv]
    _ = μ • ((Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E) :
          (Fin n → E) →ₗ[E] (Fin n → E)) v) := by rw [map_smul]

private theorem k328deig_map_eq {E : Type} [Field E] {n : ℕ}
    (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E))
    {z : Matrix.SpecialLinearGroup (Fin n) E} (hz : z ∈ Y)
    (hzcomm : ∀ y ∈ Y, Commute z y) (μ : E) (y : ↥Y) :
    (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ).map
        (Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E) :
          (Fin n → E) →ₗ[E] (Fin n → E)) =
      Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro v hv
    exact k328deig_mapsTo Y hz hzcomm μ y v hv
  · intro v hv
    rw [Submodule.mem_map_equiv]
    rw [show (Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E)).symm =
        Matrix.SpecialLinearGroup.toLin' (y⁻¹ : ↥Y) from by
      change (Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E))⁻¹ =
        Matrix.SpecialLinearGroup.toLin' (y⁻¹ : ↥Y)
      exact inv_eq_of_mul_eq_one_right (by simp)]
    exact k328deig_mapsTo Y hz hzcomm μ y⁻¹ v hv

private noncomputable def k328deig_rho {E : Type} [Field E] {n : ℕ}
    (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E))
    {z : Matrix.SpecialLinearGroup (Fin n) E} (hz : z ∈ Y)
    (hzcomm : ∀ y ∈ Y, Commute z y) (μ : E) :
    ↥Y →* (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ ≃ₗ[E]
      Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ) where
  toFun y := (Matrix.SpecialLinearGroup.toLin' (y : Matrix.SpecialLinearGroup (Fin n) E)).ofSubmodules
    _ _ (k328deig_map_eq Y hz hzcomm μ y)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    simp only [LinearEquiv.ofSubmodules_apply]
    rw [show ((1 : ↥Y) : Matrix.SpecialLinearGroup (Fin n) E) = 1 from rfl, map_one]
    rfl
  map_mul' := by
    intro a b
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    simp only [LinearEquiv.ofSubmodules_apply, LinearEquiv.mul_apply]
    rw [Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply]

private theorem k328deig_pow_apply {E : Type} [CommRing E] {V : Type} [AddCommGroup V]
    [Module E V] {f : V →ₗ[E] V} {μ : E} {v : V} (hv : f v = μ • v) (k : ℕ) :
    (f ^ k) v = (μ ^ k) • v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, hv, map_smul, ih, smul_smul,
        ← pow_succ']

private theorem k328deig_rho_z {E : Type} [Field E] {n : ℕ}
    (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E))
    {z : Matrix.SpecialLinearGroup (Fin n) E} (hz : z ∈ Y)
    (hzcomm : ∀ y ∈ Y, Commute z y) (μ : E) :
    (k328deig_rho Y hz hzcomm μ ⟨z, hz⟩).toLinearMap = μ • 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show (Matrix.SpecialLinearGroup.toLin' z) (v : ↥(Module.End.eigenspace
      (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ)) = μ • (v : Fin n → E)
  rw [Matrix.SpecialLinearGroup.toLin'_apply]
  exact Module.End.mem_eigenspace_iff.mp v.2

private theorem k328deig_det_rho {E : Type} [Field E] {n : ℕ}
    (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)) (hYY : ⁅Y, Y⁆ = Y)
    {z : Matrix.SpecialLinearGroup (Fin n) E} (hz : z ∈ Y)
    (hzcomm : ∀ y ∈ Y, Commute z y) (μ : E) (y : ↥Y) :
    (k328deig_rho Y hz hzcomm μ y).det = 1 := by
  have hperf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hYY
  let D : ↥Y →* Eˣ := (LinearEquiv.det).comp (k328deig_rho Y hz hzcomm μ)
  have hker : D.ker = ⊤ := by
    rw [eq_top_iff, ← Group.isPerfect_def.mp hperf]
    exact Abelianization.commutator_subset_ker D
  have hy : y ∈ D.ker := by rw [hker]; trivial
  have h := MonoidHom.mem_ker.mp hy
  simpa [D] using h

private theorem k328deig_finrank_eq_three {E : Type} [Field E] {n : ℕ}
    (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)) (hYY : ⁅Y, Y⁆ = Y)
    {z : Matrix.SpecialLinearGroup (Fin n) E} (hz : z ∈ Y)
    (hzcomm : ∀ y ∈ Y, Commute z y) (hzord : orderOf z = 3)
    (μ : E) (hμ : μ ≠ 1)
    (hVne : Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ ≠ ⊥)
    (hVle : Module.finrank E
      (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ) ≤ 4) :
    Module.finrank E
      (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ) = 3 := by
  let V : Submodule E (Fin n → E) :=
    Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ
  have hVne' : V ≠ ⊥ := hVne
  have hVle' : Module.finrank E V ≤ 4 := hVle
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzord] at this
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne'
  have hzμ : Matrix.toLin' (z : Matrix (Fin n) (Fin n) E) v = μ • v :=
    Module.End.mem_eigenspace_iff.mp hvmem
  have hTz3 : (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) ^ 3 = 1 := by
    have hz3m : (z : Matrix (Fin n) (Fin n) E) ^ 3 = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hz3, Matrix.SpecialLinearGroup.coe_one]
    rw [← Matrix.toLin'_pow, hz3m, Matrix.toLin'_one, Module.End.one_eq_id]
  have hμ3 : μ ^ 3 = 1 := by
    have hp : v = (μ ^ 3) • v := by
      have h := k328deig_pow_apply hzμ 3
      rw [hTz3] at h
      simpa using h
    have hzero : (μ ^ 3 - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hp, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hvne
  have hdet1 : LinearMap.det ((k328deig_rho Y hz hzcomm μ ⟨z, hz⟩ : V →ₗ[E] V)) = 1 := by
    rw [← LinearEquiv.coe_det, k328deig_det_rho Y hYY hz hzcomm μ ⟨z, hz⟩]
    rfl
  have hρz : (k328deig_rho Y hz hzcomm μ ⟨z, hz⟩ : V →ₗ[E] V) = μ • 1 := by
    rw [k328deig_rho_z]
  have hdetμ : LinearMap.det (μ • (1 : V →ₗ[E] V)) = μ ^ Module.finrank E V := by
    rw [LinearMap.det_smul]
    simp
  have hμm : μ ^ Module.finrank E V = 1 := by
    rw [← hdetμ, ← hρz, hdet1]
  have hordμ : orderOf μ = 3 := orderOf_eq_prime hμ3 hμ
  have h3m : 3 ∣ Module.finrank E V := by
    rw [← hordμ]
    exact orderOf_dvd_iff_pow_eq_one.mpr hμm
  have h1 : 1 ≤ Module.finrank E V := by
    have : Module.Finite E V :=
      Module.Finite.of_injective V.subtype Subtype.val_injective
    have : Nontrivial V := (Submodule.nontrivial_iff_ne_bot).mpr hVne'
    exact Module.finrank_pos
  change Module.finrank E V = 3
  interval_cases Module.finrank E V <;> simp_all

private theorem k328deig_ker_le_of_simple
    {G H W : Type} [Group G] [Group H] [Group W] [IsSimpleGroup W]
    (ρ : G →* H) (hG : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤)
    (φ : G →* W) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker ≤ Subgroup.center G) {z : G} (hρz : ρ z ≠ 1) :
    ρ.ker ≤ φ.ker := by
  have : (ρ.ker.map φ).Normal := (MonoidHom.normal_ker ρ).map φ hφsurj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map φ) with hbot | htop
  · intro k hk
    rw [MonoidHom.mem_ker]
    have hmem : φ k ∈ ρ.ker.map φ := Subgroup.mem_map_of_mem φ hk
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  · exfalso
    have hsup : ρ.ker ⊔ φ.ker = (⊤ : Subgroup G) := by
      apply le_antisymm le_top
      intro y _
      have hy' : φ y ∈ ρ.ker.map φ := by rw [htop]; trivial
      rw [Subgroup.mem_map] at hy'
      obtain ⟨k, hk, hky⟩ := hy'
      have hk'y : k⁻¹ * y ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hky, inv_mul_cancel]
      have hyk : y = k * (k⁻¹ * y) := by group
      rw [hyk]
      exact (ρ.ker ⊔ φ.ker).mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hk'y)
    have hcomm_le : ⁅ρ.ker ⊔ φ.ker, ρ.ker ⊔ φ.ker⁆ ≤ ρ.ker := by
      have hBA : ⁅φ.ker, ρ.ker⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hφker.trans (Subgroup.center_le_centralizer (ρ.ker : Set G))
      have hAB : ⁅ρ.ker, φ.ker⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hBA
      have hBB : ⁅φ.ker, φ.ker⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hφker.trans (Subgroup.center_le_centralizer (φ.ker : Set G))
      have hAA : ⁅ρ.ker, ρ.ker⁆ ≤ ρ.ker := Subgroup.commutator_le_of_le le_rfl le_rfl
      calc ⁅ρ.ker ⊔ φ.ker, ρ.ker ⊔ φ.ker⁆
          = ⁅ρ.ker ⊔ φ.ker, ρ.ker⁆ ⊔ ⁅ρ.ker ⊔ φ.ker, φ.ker⁆ :=
            Subgroup.commutator_sup_left _ _ _
        _ = (⁅ρ.ker, ρ.ker⁆ ⊔ ⁅φ.ker, ρ.ker⁆) ⊔
              (⁅ρ.ker, φ.ker⁆ ⊔ ⁅φ.ker, φ.ker⁆) := by
            rw [Subgroup.commutator_sup_right, Subgroup.commutator_sup_right]
        _ ≤ ρ.ker := by
            rw [hBA, hAB, hBB]
            exact sup_le (sup_le hAA bot_le) (sup_le bot_le bot_le)
    have htop_le : (⊤ : Subgroup G) ≤ ρ.ker := by
      rw [← hG, Subgroup.commutator_def, ← hsup]
      exact hcomm_le
    exact hρz (MonoidHom.mem_ker.mp (htop_le (Subgroup.mem_top z)))

theorem k328det_oddEigenblock :
    ∀ (E : Type) [Field E] [Finite E], ringChar E ≠ 2 → ∀ (n : ℕ)
      (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 → ∀ μ : E, μ ≠ 1 →
        Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ ≠ ⊥ →
        Module.finrank E
            (Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ) ≤ 4 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3) := by
  intro E _ _ hE n Y hYY z hz hzcomm hzord μ hμ hVne hVle W _ φ hφsurj hφker hLie
  have : IsSimpleGroup W := by
    rcases hLie with h | h
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  let V : Submodule E (Fin n → E) :=
    Module.End.eigenspace (Matrix.toLin' (z : Matrix (Fin n) (Fin n) E)) μ
  have hVne' : V ≠ ⊥ := hVne
  have hVdim : Module.finrank E V = 3 :=
    k328deig_finrank_eq_three Y hYY hz hzcomm hzord μ hμ hVne hVle
  have : Module.Finite E V := Module.Finite.of_injective V.subtype Subtype.val_injective
  let b : Module.Basis (Fin 3) E V := Module.finBasisOfFinrankEq E V hVdim
  let ρ : ↥Y →* (V ≃ₗ[E] V) := k328deig_rho Y hz hzcomm μ
  have hρz_ne : ρ ⟨z, hz⟩ ≠ 1 := by
    intro h
    have h' : (ρ ⟨z, hz⟩).toLinearMap = 1 := by rw [h]; rfl
    rw [show (ρ ⟨z, hz⟩).toLinearMap = μ • (1 : V →ₗ[E] V) from
      k328deig_rho_z Y hz hzcomm μ] at h'
    obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne'
    have hv : (μ • (1 : V →ₗ[E] V)) ⟨v, hvmem⟩ = ⟨v, hvmem⟩ := by
      have := congrArg (fun f : V →ₗ[E] V => f ⟨v, hvmem⟩) h'
      simpa using this
    have hv' : μ • (⟨v, hvmem⟩ : V) = ⟨v, hvmem⟩ := by simpa using hv
    have hco : μ • v = v := by
      have := congrArg (fun w : V => (w : Fin n → E)) hv'
      simpa using this
    have hzero : (μ - 1) • v = 0 := by rw [sub_smul, one_smul, hco, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact hμ (sub_eq_zero.mp h)
    · exact hvne h
  have hker_le : ρ.ker ≤ φ.ker :=
    k328deig_ker_le_of_simple ρ (Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hYY)) φ hφsurj
      hφker hρz_ne
  let σ : ↥Y →* Matrix (Fin 3) (Fin 3) E :=
    { toFun := fun y => LinearMap.toMatrixAlgEquiv b ((ρ y).toLinearMap)
      map_one' := by
        rw [map_one, LinearEquiv.coe_toLinearMap_one]
        exact map_one (LinearMap.toMatrixAlgEquiv b)
      map_mul' := by
        intro a c
        rw [map_mul, LinearEquiv.coe_toLinearMap_mul]
        exact map_mul (LinearMap.toMatrixAlgEquiv b) _ _ }
  have hσdet : ∀ y : ↥Y, (σ y).det = 1 := by
    intro y
    have h1 : Matrix.det (LinearMap.toMatrixAlgEquiv b ((ρ y).toLinearMap)) =
        LinearMap.det ((ρ y).toLinearMap) :=
      LinearMap.det_toMatrix b ((ρ y).toLinearMap)
    change Matrix.det (LinearMap.toMatrixAlgEquiv b ((ρ y).toLinearMap)) = 1
    rw [h1, ← LinearEquiv.coe_det, k328deig_det_rho Y hYY hz hzcomm μ y]
    rfl
  let σ' : ↥Y →* Matrix.SpecialLinearGroup (Fin 3) E :=
    { toFun := fun y => ⟨σ y, hσdet y⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun a c => Subtype.ext (map_mul σ a c) }
  have hσ'ker : σ'.ker = ρ.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have hσy : σ y = 1 := Subtype.ext_iff.mp h
      have h3 : LinearMap.toMatrixAlgEquiv b ((ρ y).toLinearMap) = 1 := hσy
      have h2 : (ρ y).toLinearMap = 1 := (LinearMap.toMatrixAlgEquiv b).map_eq_one_iff.mp h3
      exact LinearEquiv.toLinearMap_injective h2
    · intro h
      apply Subtype.ext
      show LinearMap.toMatrixAlgEquiv b ((ρ y).toLinearMap) = 1
      rw [h, LinearEquiv.coe_toLinearMap_one]
      exact map_one (LinearMap.toMatrixAlgEquiv b)
  let r : ↥Y →* ↥(σ'.range) := MonoidHom.rangeRestrict σ'
  have hr : Function.Surjective r := MonoidHom.rangeRestrict_surjective σ'
  have hle : r.ker ≤ φ.ker := by
    rw [MonoidHom.ker_rangeRestrict, hσ'ker]
    exact hker_le
  let φ' : ↥(σ'.range) →* W := r.liftOfSurjective hr ⟨φ, hle⟩
  have hφ'comp : ∀ y, φ' (r y) = φ y := by
    intro y
    simp only [φ', MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply]
  have hφ'surj : Function.Surjective φ' := by
    intro w
    obtain ⟨y, hy⟩ := hφsurj w
    exact ⟨r y, by rw [hφ'comp y, hy]⟩
  have hφ'ker : φ'.ker ≤ Subgroup.center ↥(σ'.range) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    obtain ⟨y, rfl⟩ := hr x
    intro x₂
    obtain ⟨y₂, rfl⟩ := hr x₂
    have hy : y ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have h := hφ'comp y
      rw [MonoidHom.mem_ker] at hx
      rw [hx] at h
      exact h.symm
    have hyc : y ∈ Subgroup.center ↥Y := hφker hy
    calc r y₂ * r y = r (y₂ * y) := by rw [map_mul]
      _ = r (y * y₂) := by rw [Subgroup.mem_center_iff.mp hyc y₂]
      _ = r y * r y₂ := by rw [map_mul]
  exact k328det_sl3NoCentralExt E hE σ'.range W φ' hφ'surj hφ'ker hLie

private theorem k328dch3_sub_pow_three {A : Type} [Ring A] (h3 : (3 : A) = 0) (a : A)
    (ha : a ^ 3 = 1) : (a - 1) ^ 3 = 0 := by
  have h : (a - 1) ^ 3 = a ^ 3 - 1 := by
    calc (a - 1) ^ 3 = a ^ 3 - 3 * a ^ 2 + 3 * a - 1 := by noncomm_ring
      _ = a ^ 3 - 1 := by rw [h3]; noncomm_ring
  rw [h, ha, sub_self]

private theorem k328dch3_pow_three_of_sq {A : Type} [Ring A] (h3 : (3 : A) = 0) (a : A)
    (ha : (a - 1) ^ 2 = 0) : a ^ 3 = 1 := by
  have h : (a - 1) ^ 3 = a ^ 3 - 1 := by
    calc (a - 1) ^ 3 = a ^ 3 - 3 * a ^ 2 + 3 * a - 1 := by noncomm_ring
      _ = a ^ 3 - 1 := by rw [h3]; noncomm_ring
  have h0 : (a - 1) ^ 3 = 0 := by rw [pow_succ, ha, zero_mul]
  rw [h] at h0
  exact sub_eq_zero.mp h0

private def k328dch3_finEquiv (d : ℕ) (hd : d ≤ 3) : Fin d ⊕ Fin (3 - d) ≃ Fin 3 :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hd))

private theorem k328dch3_block_det {E : Type} [Field E] {d : ℕ} (hd : d ≤ 3)
    (A : Matrix.SpecialLinearGroup (Fin d) E) :
    (Matrix.reindex (k328dch3_finEquiv d hd) (k328dch3_finEquiv d hd)
      (Matrix.fromBlocks (A : Matrix (Fin d) (Fin d) E) 0 0 1)).det = 1 := by
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, A.2, Matrix.det_one, mul_one]

private theorem k328dch3_reindex_mul {E : Type} [Field E] {d : ℕ} (hd : d ≤ 3)
    (X Y : Matrix (Fin d ⊕ Fin (3 - d)) (Fin d ⊕ Fin (3 - d)) E) :
    Matrix.reindex (k328dch3_finEquiv d hd) (k328dch3_finEquiv d hd) (X * Y) =
      Matrix.reindex (k328dch3_finEquiv d hd) (k328dch3_finEquiv d hd) X *
        Matrix.reindex (k328dch3_finEquiv d hd) (k328dch3_finEquiv d hd) Y :=
  map_mul (Matrix.reindexRingEquiv E (k328dch3_finEquiv d hd)) X Y

private def k328dch3_blockEmb (E : Type) [Field E] (d : ℕ) (hd : d ≤ 3) :
    Matrix.SpecialLinearGroup (Fin d) E →* Matrix.SpecialLinearGroup (Fin 3) E where
  toFun A := ⟨Matrix.reindex (k328dch3_finEquiv d hd) (k328dch3_finEquiv d hd)
      (Matrix.fromBlocks (A : Matrix (Fin d) (Fin d) E) 0 0 1), k328dch3_block_det hd A⟩
  map_one' := by
    apply Subtype.ext
    show Matrix.reindex (k328dch3_finEquiv d hd) (k328dch3_finEquiv d hd)
      (Matrix.fromBlocks (((1 : Matrix.SpecialLinearGroup (Fin d) E)) : Matrix (Fin d) (Fin d) E) 0 0 1) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.fromBlocks_one]
    exact map_one (Matrix.reindexRingEquiv E (k328dch3_finEquiv d hd))
  map_mul' A B := by
    apply Subtype.ext
    show Matrix.reindex (k328dch3_finEquiv d hd) (k328dch3_finEquiv d hd)
        (Matrix.fromBlocks ((A * B : Matrix.SpecialLinearGroup (Fin d) E) : Matrix (Fin d) (Fin d) E) 0 0 1) =
      Matrix.reindex (k328dch3_finEquiv d hd) (k328dch3_finEquiv d hd)
          (Matrix.fromBlocks (A : Matrix (Fin d) (Fin d) E) 0 0 1) *
        Matrix.reindex (k328dch3_finEquiv d hd) (k328dch3_finEquiv d hd)
          (Matrix.fromBlocks (B : Matrix (Fin d) (Fin d) E) 0 0 1)
    rw [Matrix.SpecialLinearGroup.coe_mul, ← k328dch3_reindex_mul hd]
    congr 1
    rw [Matrix.fromBlocks_multiply]
    simp

private theorem k328dch3_blockEmb_injective (E : Type) [Field E] (d : ℕ) (hd : d ≤ 3) :
    Function.Injective (k328dch3_blockEmb E d hd) := by
  intro A B h
  have h' : Matrix.reindexRingEquiv E (k328dch3_finEquiv d hd)
      (Matrix.fromBlocks (A : Matrix (Fin d) (Fin d) E) 0 0 1) =
      Matrix.reindexRingEquiv E (k328dch3_finEquiv d hd)
        (Matrix.fromBlocks (B : Matrix (Fin d) (Fin d) E) 0 0 1) :=
    congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) E => (x : Matrix (Fin 3) (Fin 3) E)) h
  have h2 : Matrix.fromBlocks (A : Matrix (Fin d) (Fin d) E) 0 0 1 =
      Matrix.fromBlocks (B : Matrix (Fin d) (Fin d) E) 0 0 1 :=
    (Matrix.reindexRingEquiv E (k328dch3_finEquiv d hd)).injective h'
  exact Subtype.ext (Matrix.fromBlocks_inj.mp h2).1

private noncomputable def k328dch3_actOn {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    {Y : Type} [Group Y] (σ : Y →* LinearMap.GeneralLinearGroup E V)
    (W : Submodule E V) (hW : ∀ y, W.map (σ y).toLinearEquiv.toLinearMap = W) :
    Y →* LinearMap.GeneralLinearGroup E W where
  toFun y := LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((σ y).toLinearEquiv.ofSubmodules W W (hW y))
  map_one' := by
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv E W).injective
    ext w
    simp [LinearMap.GeneralLinearGroup.ofLinearEquiv]
  map_mul' y y' := by
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv E W).injective
    ext w
    simp only [LinearMap.GeneralLinearGroup.ofLinearEquiv, map_mul,
      LinearMap.GeneralLinearGroup.toLinearEquiv_mul, LinearEquiv.mul_apply]
    rfl

private theorem k328dch3_sl3_reduction
    (E : Type) [Field E] [Finite E] (hchar2 : ringChar E ≠ 2)
    (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (W : Submodule E V) (hd : Module.finrank E W ≤ 3)
    (Y : Type) [Group Y] [Finite Y] (ρ : Y →* LinearMap.GeneralLinearGroup E W)
    (hperf : Group.IsPerfect Y)
    (Wg : Type) [Group Wg] (φ : Y →* Wg)
    (hφsurj : Function.Surjective φ)
    (hker : ρ.ker ≤ φ.ker) (hφker : φ.ker ≤ Subgroup.center Y)
    (hSL3 : ∀ (E : Type) [Field E] [Finite E], ringChar E ≠ 2 →
      ∀ (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E)) (W : Type) [Group W]
        (φ : ↥Y →* W), Function.Surjective φ → φ.ker ≤ Subgroup.center ↥Y →
        ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3)) :
    ¬ (LieModel Wg .PSL 3 2 2 ∨ LieModel Wg .PSU 3 2 3) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let d := Module.finrank E W
  let b := Module.finBasis E W
  let ρ₁ : Y →* Matrix.GeneralLinearGroup (Fin d) E :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ
  have hdet : ∀ y, ((ρ₁ y : Matrix (Fin d) (Fin d) E)).det = 1 := by
    intro y
    let δ : Y →* Eˣ := (Matrix.GeneralLinearGroup.det).comp ρ₁
    have : Group.IsPerfect δ.range := Group.IsPerfect.range δ
    have : IsMulCommutative δ.range := inferInstance
    have : Subsingleton δ.range := inferInstance
    have hδ : δ y = 1 := congrArg Subtype.val
      (Subsingleton.elim (⟨δ y, ⟨y, rfl⟩⟩ : δ.range) 1)
    exact congrArg (fun u : Eˣ => (u : E)) hδ
  let ρ₂ : Y →* Matrix.SpecialLinearGroup (Fin d) E :=
    { toFun := fun y => ⟨(ρ₁ y : Matrix (Fin d) (Fin d) E), hdet y⟩
      map_one' := by
        apply Subtype.ext
        show ((ρ₁ 1 : Matrix.GeneralLinearGroup (Fin d) E) : Matrix (Fin d) (Fin d) E) = 1
        rw [map_one]
        rfl
      map_mul' := by
        intro y y'
        apply Subtype.ext
        show ((ρ₁ (y * y') : Matrix.GeneralLinearGroup (Fin d) E) : Matrix (Fin d) (Fin d) E) =
          ((ρ₁ y : Matrix.GeneralLinearGroup (Fin d) E) : Matrix (Fin d) (Fin d) E) *
            ((ρ₁ y' : Matrix.GeneralLinearGroup (Fin d) E) : Matrix (Fin d) (Fin d) E)
        rw [map_mul, Units.val_mul] }
  let ρ₃ : Y →* Matrix.SpecialLinearGroup (Fin 3) E := (k328dch3_blockEmb E d hd).comp ρ₂
  let Y' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E) := ρ₃.range
  have hker3 : ρ₃.ker ≤ φ.ker := by
    intro y hy
    have hy1 : ρ₃ y = 1 := MonoidHom.mem_ker.mp hy
    have hρ₂ : ρ₂ y = 1 := by
      apply k328dch3_blockEmb_injective E d hd
      rw [map_one]
      exact hy1
    have hρ₁ : ρ₁ y = 1 := Units.ext (congrArg Subtype.val hρ₂)
    have hρ : ρ y = 1 := by
      have h2 : (Matrix.GeneralLinearGroup.toLin' b) (ρ₁ y) = 1 := by
        simpa using congrArg (Matrix.GeneralLinearGroup.toLin' b) hρ₁
      have h3 : (Matrix.GeneralLinearGroup.toLin' b) (ρ₁ y) = ρ y :=
        MulEquiv.apply_symm_apply (Matrix.GeneralLinearGroup.toLin' b) (ρ y)
      rwa [h3] at h2
    exact hker (MonoidHom.mem_ker.mpr hρ)
  let ψ : Y' →* Wg :=
    (QuotientGroup.lift ρ₃.ker φ hker3).comp
      (QuotientGroup.quotientKerEquivRange ρ₃).symm.toMonoidHom
  have hψf : ∀ y, ψ (ρ₃.rangeRestrict y) = φ y := by
    intro y
    show QuotientGroup.lift ρ₃.ker φ hker3
        ((QuotientGroup.quotientKerEquivRange ρ₃).symm (ρ₃.rangeRestrict y)) = φ y
    have h1 : (QuotientGroup.quotientKerEquivRange ρ₃).symm (ρ₃.rangeRestrict y) =
        QuotientGroup.mk y := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [h1, QuotientGroup.lift_mk]
  have hψsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨y, hy⟩ := hφsurj w
    exact ⟨ρ₃.rangeRestrict y, by rw [hψf y, hy]⟩
  have hψker : ψ.ker ≤ Subgroup.center Y' := by
    intro g hg
    obtain ⟨y, hy⟩ := g.2
    have hgy : g = ρ₃.rangeRestrict y := Subtype.ext hy.symm
    have hφy : φ y = 1 := by
      have := MonoidHom.mem_ker.mp hg
      rw [hgy, hψf y] at this
      exact this
    have hycent : y ∈ Subgroup.center Y := hφker (MonoidHom.mem_ker.mpr hφy)
    rw [Subgroup.mem_center_iff]
    intro g'
    obtain ⟨y', hy'⟩ := g'.2
    have hg'y' : g' = ρ₃.rangeRestrict y' := Subtype.ext hy'.symm
    have hcomm : y * y' = y' * y := (Subgroup.mem_center_iff.mp hycent y').symm
    rw [hgy, hg'y', ← map_mul, ← map_mul, hcomm]
  exact hSL3 E hchar2 Y' Wg ψ hψsurj hψker

private theorem k328dch3_kernel_eq_top_of_not_le_ker
    {Y : Type} [Group Y] [Group.IsPerfect Y]
    {W : Type} [Group W] [IsSimpleGroup W]
    (N : Subgroup Y) [N.Normal] (φ : Y →* W) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Y) (h : ¬ N ≤ φ.ker) : N = ⊤ := by
  have hmap : N.map φ = ⊤ := by
    have hnorm : (N.map φ).Normal := Subgroup.Normal.map (inferInstance : N.Normal) φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map φ) with hbot | htop
    · exfalso
      exact h fun n hn => by
        have : φ n ∈ N.map φ := ⟨n, hn, rfl⟩
        rw [hbot] at this
        exact Subgroup.mem_bot.mp this
    · exact htop
  have hle : ⁅(⊤ : Subgroup Y), ⊤⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro g _ h' _
    have hgk : ∃ k ∈ N, φ k = φ g := by
      have : φ g ∈ N.map φ := by rw [hmap]; trivial
      obtain ⟨k, hk, hkφ⟩ := this
      exact ⟨k, hk, hkφ⟩
    obtain ⟨k, hk, hkφ⟩ := hgk
    have hh'k : ∃ k' ∈ N, φ k' = φ h' := by
      have : φ h' ∈ N.map φ := by rw [hmap]; trivial
      obtain ⟨k', hk', hk'φ⟩ := this
      exact ⟨k', hk', hk'φ⟩
    obtain ⟨k', hk', hk'φ⟩ := hh'k
    have hc_ker : k⁻¹ * g ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkφ]
      simp
    have hc'_ker : k'⁻¹ * h' ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hk'φ]
      simp
    have hc_comm : ∀ a : Y, Commute (k⁻¹ * g) a :=
      fun a => ((Subgroup.mem_center_iff.mp (hcen hc_ker)) a).symm
    have hc'_comm : ∀ a : Y, Commute (k'⁻¹ * h') a :=
      fun a => ((Subgroup.mem_center_iff.mp (hcen hc'_ker)) a).symm
    have h1 : ⁅k⁻¹ * g, k' * (k'⁻¹ * h')⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr (hc_comm _)
    have h2 : ⁅k, k'⁻¹ * h'⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr (hc'_comm k).symm
    have hg : g = k * (k⁻¹ * g) := by group
    have hh'' : h' = k' * (k'⁻¹ * h') := by group
    rw [hg, hh'', commutatorElement_mul_left_eq_conj_mul, h1,
      commutatorElement_mul_right_eq_mul_conj, h2]
    have heq : k * 1 * k⁻¹ * (⁅k, k'⁆ * k' * 1 * k'⁻¹) = ⁅k, k'⁆ := by group
    rw [heq]
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hk hk') (N.inv_mem hk)) (N.inv_mem hk')
  exact le_antisymm le_top (by rw [← Group.IsPerfect.commutator_eq_top (G := Y)]; exact hle)

private theorem k328dch3_core
    (hSL3 : ∀ (E : Type) [Field E] [Finite E], ringChar E ≠ 2 →
      ∀ (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E)) (W : Type) [Group W]
        (φ : ↥Y →* W), Function.Surjective φ → φ.ker ≤ Subgroup.center ↥Y →
        ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3)) :
    ∀ (E : Type) [Field E] [Finite E], ringChar E = 3 → ∀ (n : ℕ), n ≤ 4 →
      ∀ (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3) := by
  intro E _ _ hchar n hn Y hY z hz hzcent hzord W _ φ hφsurj hφker hLie
  have hcharP : CharP E 3 := hchar ▸ (inferInstance : CharP E (ringChar E))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar2 : ringChar E ≠ 2 := by omega
  have hz_ne_one : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    omega
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzord] at this
  let Mz : Matrix (Fin n) (Fin n) E :=
    ((z : Matrix.SpecialLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E)
  let f : Module.End E (Fin n → E) := Matrix.toLin' (Mz - 1)
  let K : Submodule E (Fin n → E) := LinearMap.ker f
  let K' : Submodule E (Fin n → E) := LinearMap.range f
  have hMz3 : Mz ^ 3 = 1 := by
    rw [show Mz = ((z : Matrix.SpecialLinearGroup (Fin n) E) :
        Matrix (Fin n) (Fin n) E) from rfl,
      ← Matrix.SpecialLinearGroup.coe_pow, hz3, Matrix.SpecialLinearGroup.coe_one]
  have h3mat : (3 : Matrix (Fin n) (Fin n) E) = 0 := by
    ext i j
    refine (Matrix.natCast_apply (n := Fin n) (i := i) (j := j) (d := 3)).trans ?_
    by_cases h : i = j
    · rw [if_pos h]; exact CharP.cast_eq_zero E 3
    · rw [if_neg h]; simp
  have hf3 : f ^ 3 = 0 := by
    rw [show f = Matrix.toLin' (Mz - 1) from rfl, ← Matrix.toLin'_pow,
      k328dch3_sub_pow_three h3mat Mz hMz3, map_zero]
  have hf_ne : f ≠ 0 := by
    intro hf
    have hM : Mz - 1 = 0 := Matrix.toLin'.injective (by
      show f = Matrix.toLin' 0
      rw [hf, map_zero])
    have hM1 : Mz = 1 := sub_eq_zero.mp hM
    have hz1 : z = 1 := Subtype.ext hM1
    exact hz_ne_one hz1
  have hK_ne_top : K ≠ ⊤ := by
    intro htop
    have hf0 : f = 0 := by
      apply LinearMap.ext
      intro v
      have hv : v ∈ K := by rw [htop]; trivial
      exact hv
    exact hf_ne hf0
  have hK_ne_bot : K ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hbot
    have hf0 : f = 0 := by
      apply LinearMap.ext
      intro v
      have hx : f (f (f v)) = f 0 := by
        have h := congrFun (congrArg
          (fun g : Module.End E (Fin n → E) => (g : (Fin n → E) → (Fin n → E))) hf3) v
        simpa [pow_succ, Module.End.mul_apply] using h
      have h2 : f (f v) = 0 := hinj hx
      exact hinj (h2.trans (map_zero f).symm)
    exact hf_ne hf0
  have hK_le : Module.finrank E K ≤ 3 := by
    have hlt : Module.finrank E K < Module.finrank E (Fin n → E) :=
      Submodule.finrank_lt hK_ne_top
    rw [Module.finrank_fin_fun E] at hlt
    omega
  have hK'_le : Module.finrank E K' ≤ 3 := by
    have hrn : Module.finrank E K' + Module.finrank E K = n :=
      (LinearMap.finrank_range_add_finrank_ker f).trans (Module.finrank_fin_fun E)
    have hKpos : 1 ≤ Module.finrank E K := Submodule.one_le_finrank_iff.mpr hK_ne_bot
    omega
  let σ : ↥Y →* LinearMap.GeneralLinearGroup E (Fin n → E) :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).toMonoidHom.comp
      (Matrix.SpecialLinearGroup.toGL.comp (Subgroup.subtype Y))
  have hσinj : Function.Injective σ := by
    intro y₁ y₂ h
    have h1 := (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).injective h
    have h2 := Matrix.SpecialLinearGroup.toGL_injective h1
    exact Subtype.ext h2
  have hσ : ∀ y : ↥Y, (σ y).toLinearEquiv.toLinearMap =
      Matrix.toLin' (((y : ↥Y) : Matrix.SpecialLinearGroup (Fin n) E) :
        Matrix (Fin n) (Fin n) E) := by
    intro y
    rfl
  have hyM : ∀ y : ↥Y,
      ((y : ↥Y) : Matrix (Fin n) (Fin n) E) * Mz =
        Mz * ((y : ↥Y) : Matrix (Fin n) (Fin n) E) := by
    intro y
    have hc : ((y : ↥Y) : Matrix.SpecialLinearGroup (Fin n) E) * z =
        z * ((y : ↥Y) : Matrix.SpecialLinearGroup (Fin n) E) := (hzcent y y.2).symm
    have hc' := congrArg (fun a : Matrix.SpecialLinearGroup (Fin n) E =>
      (a : Matrix (Fin n) (Fin n) E)) hc
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at hc'
  have hf_comm : ∀ y : ↥Y, ∀ w : Fin n → E,
      f ((σ y).toLinearEquiv w) = (σ y).toLinearEquiv (f w) := by
    intro y w
    have hsub : ((y : ↥Y) : Matrix (Fin n) (Fin n) E) * (Mz - 1) =
        (Mz - 1) * ((y : ↥Y) : Matrix (Fin n) (Fin n) E) := by
      rw [mul_sub, sub_mul, hyM y, mul_one, one_mul]
    change Matrix.toLin' (Mz - 1) ((σ y).toLinearEquiv.toLinearMap w) =
      (σ y).toLinearEquiv.toLinearMap (Matrix.toLin' (Mz - 1) w)
    rw [hσ y, ← Matrix.toLin'_mul_apply, ← Matrix.toLin'_mul_apply, hsub]
  have hKinv : ∀ y : ↥Y, K.map (σ y).toLinearEquiv.toLinearMap = K := by
    intro y
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      show f ((σ y).toLinearEquiv w) = 0
      rw [hf_comm y w, hw, map_zero]
    · intro w hw
      refine ⟨(σ y).toLinearEquiv.symm w, ?_, (σ y).toLinearEquiv.apply_symm_apply w⟩
      show f ((σ y).toLinearEquiv.symm w) = 0
      have h1 : (σ y).toLinearEquiv (f ((σ y).toLinearEquiv.symm w)) = 0 := by
        rw [← hf_comm y ((σ y).toLinearEquiv.symm w), LinearEquiv.apply_symm_apply, hw]
      exact (σ y).toLinearEquiv.injective (by rw [h1, map_zero])
  have hK'inv : ∀ y : ↥Y, K'.map (σ y).toLinearEquiv.toLinearMap = K' := by
    intro y
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨u, hu⟩ := hw
      refine ⟨(σ y).toLinearEquiv u, ?_⟩
      rw [← hu]
      exact hf_comm y u
    · intro w hw
      obtain ⟨u, hu⟩ := hw
      refine ⟨(σ y).toLinearEquiv.symm w, ?_, (σ y).toLinearEquiv.apply_symm_apply w⟩
      refine ⟨(σ y).toLinearEquiv.symm u, ?_⟩
      apply (σ y).toLinearEquiv.injective
      rw [← hf_comm y ((σ y).toLinearEquiv.symm u), LinearEquiv.apply_symm_apply, hu,
        LinearEquiv.apply_symm_apply]
  let ρK : ↥Y →* LinearMap.GeneralLinearGroup E K := k328dch3_actOn σ K hKinv
  let ρK' : ↥Y →* LinearMap.GeneralLinearGroup E K' := k328dch3_actOn σ K' hK'inv
  have hperf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  have hperfI : Group.IsPerfect ↥Y := hperf
  have hsimple : IsSimpleGroup W := by
    rcases hLie with hL | hL
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  have hsimpleI : IsSimpleGroup W := hsimple
  have hgood : ρK.ker ≤ φ.ker ∨ ρK'.ker ≤ φ.ker := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hbadK, hbadK'⟩ := hcon
    have hKtop : ρK.ker = ⊤ := k328dch3_kernel_eq_top_of_not_le_ker ρK.ker φ hφsurj hφker hbadK
    have hK'top : ρK'.ker = ⊤ :=
      k328dch3_kernel_eq_top_of_not_le_ker ρK'.ker φ hφsurj hφker hbadK'
    let τ : ↥Y →* Module.End E (Fin n → E) :=
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := E) (M := (Fin n → E))).comp
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).toMonoidHom.comp σ)
    have hτinj : Function.Injective τ := by
      intro y₁ y₂ h
      have h1 : (σ y₁).toLinearEquiv = (σ y₂).toLinearEquiv := by
        apply LinearEquiv.ext
        intro v
        have := congrFun (congrArg (fun e : Module.End E (Fin n → E) =>
          (e : (Fin n → E) → (Fin n → E))) h) v
        simpa [τ] using this
      exact hσinj ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).injective h1)
    have hexp : ∀ y : ↥Y, y ^ 3 = 1 := by
      intro y
      have hofinjK : Function.Injective
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (R := E) (M := K)) :=
        (LinearMap.GeneralLinearGroup.generalLinearEquiv E K).symm.injective
      have hof1K : LinearMap.GeneralLinearGroup.ofLinearEquiv (1 : K ≃ₗ[E] K) = 1 :=
        map_one (LinearMap.GeneralLinearGroup.generalLinearEquiv E K).symm
      have hKfix : ∀ v ∈ K, (τ y - 1) v = 0 := by
        intro v hv
        have h1 : ρK y = 1 := by rw [← MonoidHom.mem_ker, hKtop]; trivial
        have h2 : (σ y).toLinearEquiv.ofSubmodules K K (hKinv y) = 1 := by
          apply hofinjK
          rw [show (LinearMap.GeneralLinearGroup.ofLinearEquiv
            ((σ y).toLinearEquiv.ofSubmodules K K (hKinv y))) = ρK y from rfl, h1, hof1K]
        have h3 : (σ y).toLinearEquiv v = v := by
          have hw := congrArg (fun e : K ≃ₗ[E] K => (e ⟨v, hv⟩ : Fin n → E)) h2
          simpa [LinearEquiv.ofSubmodules_apply] using hw
        change (σ y).toLinearEquiv v - v = 0
        rw [h3, sub_self]
      have hofinjK' : Function.Injective
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (R := E) (M := K')) :=
        (LinearMap.GeneralLinearGroup.generalLinearEquiv E K').symm.injective
      have hof1K' : LinearMap.GeneralLinearGroup.ofLinearEquiv (1 : K' ≃ₗ[E] K') = 1 :=
        map_one (LinearMap.GeneralLinearGroup.generalLinearEquiv E K').symm
      have hK'fix : ∀ v ∈ K', (τ y - 1) v = 0 := by
        intro v hv
        have h1 : ρK' y = 1 := by rw [← MonoidHom.mem_ker, hK'top]; trivial
        have h2 : (σ y).toLinearEquiv.ofSubmodules K' K' (hK'inv y) = 1 := by
          apply hofinjK'
          rw [show (LinearMap.GeneralLinearGroup.ofLinearEquiv
            ((σ y).toLinearEquiv.ofSubmodules K' K' (hK'inv y))) = ρK' y from rfl, h1, hof1K']
        have h3 : (σ y).toLinearEquiv v = v := by
          have hw := congrArg (fun e : K' ≃ₗ[E] K' => (e ⟨v, hv⟩ : Fin n → E)) h2
          simpa [LinearEquiv.ofSubmodules_apply] using hw
        change (σ y).toLinearEquiv v - v = 0
        rw [h3, sub_self]
      have h3end : (3 : Module.End E (Fin n → E)) = 0 := by
        apply LinearMap.ext
        intro v
        show (3 : Module.End E (Fin n → E)) v = 0
        change 3 • v = 0
        rw [← Nat.cast_smul_eq_nsmul E 3 v, CharP.cast_eq_zero, zero_smul]
      have hNy2 : (τ y - 1) ^ 2 = 0 := by
        apply LinearMap.ext
        intro v
        show (τ y - 1) ((τ y - 1) v) = 0
        apply hKfix
        show f ((τ y - 1) v) = 0
        have hcommN : f ((τ y - 1) v) = (τ y - 1) (f v) := by
          change f ((σ y).toLinearEquiv v - v) = (σ y).toLinearEquiv (f v) - f v
          rw [map_sub, hf_comm y v]
        rw [hcommN, hK'fix (f v) ⟨v, rfl⟩]
      have hcube : (τ y) ^ 3 = 1 := k328dch3_pow_three_of_sq h3end (τ y) hNy2
      have h1 : τ (y ^ 3) = 1 := by rw [map_pow, hcube]
      exact hτinj (by rw [h1, map_one])
    have hP : IsPGroup 3 ↥Y := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro y
      exact ⟨1, by simpa using hexp y⟩
    have : Group.IsNilpotent ↥Y := IsPGroup.isNilpotent hP
    have : Group.IsSolvable ↥Y := inferInstance
    have : Nontrivial ↥Y := by
      obtain ⟨a, b, hab⟩ := exists_pair_ne W
      obtain ⟨a', ha'⟩ := hφsurj a
      obtain ⟨b', hb'⟩ := hφsurj b
      exact ⟨a', b', fun h => hab (by rw [← ha', ← hb', h])⟩
    exact Group.IsPerfect.not_isSolvable ↥Y inferInstance
  rcases hgood with hgoodK | hgoodK'
  · exact (k328dch3_sl3_reduction E hchar2 (Fin n → E) K hK_le ↥Y ρK hperf W φ hφsurj
      hgoodK hφker hSL3) hLie
  · exact (k328dch3_sl3_reduction E hchar2 (Fin n → E) K' hK'_le ↥Y ρK' hperf W φ hφsurj
      hgoodK' hφker hSL3) hLie

theorem k328det_charThreeBlock :
    ∀ (E : Type) [Field E] [Finite E], ringChar E = 3 → ∀ (n : ℕ), n ≤ 4 →
      ∀ (Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)), ⁅Y, Y⁆ = Y →
      ∀ z ∈ Y, (∀ y ∈ Y, Commute z y) → orderOf z = 3 →
        ∀ (W : Type) [Group W] (φ : ↥Y →* W), Function.Surjective φ →
          φ.ker ≤ Subgroup.center ↥Y → ¬ (LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3) :=
  k328dch3_core k328det_sl3NoCentralExt

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
