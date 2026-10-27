module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainBasic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import CFSG.LocalAnalysis.StandardType.FS81.N7MainMatK

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

structure N7MatHyp (Xg : Subgroup (GL (Fin 8) (ZMod 3))) : Prop where
  norm : ∀ A ∈ Xg, (∀ i : Fin 8, i ≠ 0 → (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) i 0 = 0) →
    (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ evenAll0 7
  sub : ∀ M ∈ evenAll0 7, ∃ A ∈ Xg, (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) = M
  perm : ∀ σ : Equiv.Perm (Fin 8), ∃ A ∈ Xg, (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) = spMat σ 1

@[expose] def OrbE0 (Xg : Subgroup (GL (Fin 8) (ZMod 3))) (v : Fin 8 → ZMod 3) : Prop :=
  ∃ A ∈ Xg, (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = v

section Orbit

variable {Xg : Subgroup (GL (Fin 8) (ZMod 3))}

theorem inv_mulVec_mulVec (A : GL (Fin 8) (ZMod 3)) (z : Fin 8 → ZMod 3) :
    ((A⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      ((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem conj_mulVec (A B : GL (Fin 8) (ZMod 3)) (z : Fin 8 → ZMod 3) :
    ((A⁻¹ * B * A : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z =
      ((A⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
        ((B : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ ((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mul_assoc]

theorem orbE0_mulVec {v : Fin 8 → ZMod 3} (hv : OrbE0 Xg v) {B : GL (Fin 8) (ZMod 3)}
    (hB : B ∈ Xg) : OrbE0 Xg ((B : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) := by
  obtain ⟨A, hA, rfl⟩ := hv
  exact ⟨B * A, Xg.mul_mem hB hA, by rw [Units.val_mul, ← Matrix.mulVec_mulVec]⟩

theorem orbE0_mulVec_iff {v : Fin 8 → ZMod 3} {B : GL (Fin 8) (ZMod 3)} (hB : B ∈ Xg) :
    OrbE0 Xg ((B : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) ↔ OrbE0 Xg v := by
  refine ⟨fun hv => ?_, fun hv => orbE0_mulVec hv hB⟩
  have := orbE0_mulVec hv (Xg.inv_mem hB)
  rwa [inv_mulVec_mulVec] at this

theorem orbE0_e0 : OrbE0 Xg (Pi.single 0 1) := ⟨1, Xg.one_mem, by rw [Units.val_one, Matrix.one_mulVec]⟩

end Orbit

namespace N7MatHyp

variable {Xg : Subgroup (GL (Fin 8) (ZMod 3))} (h : N7MatHyp Xg)
include h

theorem mem_fk {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (hp : ∏ i, s i = 1) : ∃ A ∈ Xg, (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) = spMat σ s := by
  obtain ⟨P, hP, hPe⟩ := h.perm σ
  obtain ⟨D, hD, hDe⟩ := h.sub (spMat 1 s) ⟨1, s, hs, ⟨rfl, hp⟩, rfl⟩
  refine ⟨P * D, Xg.mul_mem hP hD, ?_⟩
  rw [Units.val_mul, hPe, hDe, spMat_mul, mul_one]
  congr 1
  funext j
  simp

theorem orbE0_iff_repW {v : Fin 8 → ZMod 3} (hv : wt v ≤ 7) :
    OrbE0 Xg v ↔ OrbE0 Xg (repW (wt v)) := by
  obtain ⟨σ, s, hs, hp, he⟩ := exists_spMat_mulVec_eq_repW v hv
  obtain ⟨P, hP, hPe⟩ := h.mem_fk hs hp
  rw [← he, ← hPe, orbE0_mulVec_iff hP]

theorem orbE0_iff_rep8 {v : Fin 8 → ZMod 3} (hv : wt v = 8) :
    OrbE0 Xg v ↔ OrbE0 Xg (rep8 (∏ i, v i)) := by
  obtain ⟨σ, s, hs, hp, he⟩ := exists_spMat_mulVec_eq_rep8 v hv
  obtain ⟨P, hP, hPe⟩ := h.mem_fk hs hp
  rw [← he, ← hPe, orbE0_mulVec_iff hP]

theorem conj_spMat {A₀ B : GL (Fin 8) (ZMod 3)} (hA₀ : A₀ ∈ Xg) (hB : B ∈ Xg) {c : ZMod 3}
    (hBv : (B : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      Pi.single 0 1) = c • ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1)) :
    ∃ σ s, IsSign s ∧ σ 0 = 0 ∧ s 0 = c ∧ ∏ i, s i = 1 ∧
      ((A₀⁻¹ * B * A₀ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) = spMat σ s := by
  have hC : A₀⁻¹ * B * A₀ ∈ Xg := Xg.mul_mem (Xg.mul_mem (Xg.inv_mem hA₀) hB) hA₀
  have hCe : ((A₀⁻¹ * B * A₀ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      Pi.single 0 1 = c • Pi.single 0 1 := by
    rw [conj_mulVec, hBv, Matrix.mulVec_smul, inv_mulVec_mulVec]
  have hcol : ∀ i : Fin 8, i ≠ 0 →
      ((A₀⁻¹ * B * A₀ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) i 0 = 0 := by
    intro i hi
    have e := congrFun hCe i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_eq_of_ne hi,
      smul_zero] at e
  obtain ⟨σ, s, hs, ⟨hσ0, hp⟩, hCs⟩ := h.norm _ hC hcol
  refine ⟨σ, s, hs, hσ0, ?_, hp, hCs⟩
  have hσ0' : σ.symm 0 = 0 := by rw [Equiv.symm_apply_eq, hσ0]
  have e := congrFun hCe 0
  rw [hCs] at e
  simp only [spMat_mulVec] at e
  rw [hσ0', Pi.smul_apply, Pi.single_eq_same, mul_one, smul_eq_mul, mul_one] at e
  exact e

theorem false_of_reflection {v : Fin 8 → ZMod 3} (hv : OrbE0 Xg v) {ρ : GL (Fin 8) (ZMod 3)}
    (hρ : ρ ∈ Xg) (hρv : (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = -v)
    (hρl : ∀ z, ∃ c : ZMod 3, (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z - z = c • v) : False := by
  obtain ⟨A₀, hA₀, rfl⟩ := hv
  obtain ⟨σ, s, hs, -, hs0, hp, hR⟩ := h.conj_spMat hA₀ hρ (c := -1)
    (by rw [hρv]; funext i; simp)
  have hk : ∀ k : Fin 8, k ≠ 0 → s k = 1 := by
    intro k hk0
    obtain ⟨c, hc⟩ := hρl ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single k 1)
    have e : spMat σ s *ᵥ Pi.single k 1 - Pi.single k 1 = c • Pi.single 0 1 := by
      rw [← hR, conj_mulVec]
      have := congrArg (fun z => ((A₀⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) hc
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, inv_mulVec_mulVec] at this
      exact this
    have e' := congrFun e k
    simp only [Pi.sub_apply, spMat_mulVec] at e'
    rw [Pi.smul_apply, Pi.single_eq_of_ne hk0, smul_zero, Pi.single_eq_same] at e'
    by_cases hσk : σ.symm k = k
    · rw [hσk, Pi.single_eq_same, mul_one, sub_eq_zero] at e'
      exact e'
    · rw [Pi.single_eq_of_ne hσk, mul_zero, zero_sub] at e'
      exact absurd e' (by decide)
  have hprod : ∏ i, s i = -1 := by
    rw [Fin.prod_univ_succ, hs0, Finset.prod_eq_one (fun i _ => hk i.succ (Fin.succ_ne_zero i)),
      mul_one]
  rw [hp] at hprod
  exact absurd hprod (by decide)

theorem false_of_order_fifteen {v : Fin 8 → ZMod 3} (hv : OrbE0 Xg v) {B : GL (Fin 8) (ZMod 3)}
    (hB : B ∈ Xg) (hfix : (B : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = v) (h15 : B ^ 15 = 1)
    (h5 : B ^ 5 ≠ 1) (h3 : B ^ 3 ≠ 1) : False := by
  obtain ⟨A₀, hA₀, rfl⟩ := hv
  obtain ⟨σ, s, hs, hσ0, -, -, hC⟩ := h.conj_spMat hA₀ hB (c := 1) (by rw [hfix, one_smul])
  have hpow : ∀ n : ℕ, spMat σ s ^ n =
      ((A₀⁻¹ * B ^ n * A₀ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) := by
    intro n
    have e : (A₀⁻¹ * B * A₀) ^ n = A₀⁻¹ * B ^ n * A₀ := by
      have := conj_pow (i := n) (a := A₀⁻¹) (b := B)
      rwa [inv_inv] at this
    rw [← hC, ← Units.val_pow_eq_pow_val, e]
  have hne : ∀ n : ℕ, B ^ n ≠ 1 → spMat σ s ^ n ≠ 1 := by
    intro n hn e
    apply hn
    rw [hpow] at e
    have e' : A₀⁻¹ * B ^ n * A₀ = 1 := Units.ext (by rw [e, Units.val_one])
    calc B ^ n = A₀ * (A₀⁻¹ * B ^ n * A₀) * A₀⁻¹ := by group
      _ = 1 := by rw [e', mul_one, mul_inv_cancel]
  obtain ⟨h15', h5', h3'⟩ := perm_pow_of_spMat_pow hs
    (by rw [hpow, h15, mul_one, inv_mul_cancel, Units.val_one]) (hne 5 h5) (hne 3 h3)
  exact false_of_perm_order_fifteen σ hσ0 h15' h5' h3'

end N7MatHyp

@[expose] def cyc3 (a b c : Fin 8) : Equiv.Perm (Fin 8) := Equiv.swap a b * Equiv.swap b c

@[expose] def cyc5 (a b c d e : Fin 8) : Equiv.Perm (Fin 8) :=
  Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d e

@[expose] def pi35 : Equiv.Perm (Fin 8) := cyc3 0 1 2 * cyc5 3 4 5 6 7

@[expose] def pi53 : Equiv.Perm (Fin 8) := cyc5 0 1 2 3 4 * cyc3 5 6 7

theorem pi35_pow : pi35 ^ 15 = 1 ∧ pi35 ^ 5 ≠ 1 ∧ pi35 ^ 3 ≠ 1 := by decide +kernel

theorem pi53_pow : pi53 ^ 15 = 1 ∧ pi53 ^ 5 ≠ 1 ∧ pi53 ^ 3 ≠ 1 := by decide +kernel

@[expose] def sign53 : Fin 8 → ZMod 3 := fun j => rep8 (-1) (pi53 j) * rep8 (-1) j

theorem pow_eq_one_iff_of_spMat_one {B : GL (Fin 8) (ZMod 3)} {π : Equiv.Perm (Fin 8)}
    (hB : (B : Matrix (Fin 8) (Fin 8) (ZMod 3)) = spMat π 1) (n : ℕ) : B ^ n = 1 ↔ π ^ n = 1 := by
  constructor
  · intro e
    have := congrArg Units.val e
    rw [Units.val_pow_eq_pow_val, hB, spMat_one_pow, Units.val_one] at this
    exact perm_eq_one_of_spMat_eq_one this
  · intro e
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hB, spMat_one_pow, e, Units.val_one]
    exact spMat_one

theorem pow_eq_one_iff_of_spMat_sign53 {B : GL (Fin 8) (ZMod 3)}
    (hB : (B : Matrix (Fin 8) (Fin 8) (ZMod 3)) = spMat pi53 sign53) (n : ℕ) :
    B ^ n = 1 ↔ pi53 ^ n = 1 := by
  have ht : IsSign (rep8 (-1)) := by unfold IsSign; decide
  have hD := spMat_one_mul_self ht
  have hconj : spMat pi53 sign53 = spMat 1 (rep8 (-1)) * spMat pi53 1 * spMat 1 (rep8 (-1)) := by
    rw [spMat_mul, spMat_mul]
    exact congrArg₂ spMat (by rw [one_mul, mul_one]) (funext fun j => by simp [sign53])
  have hBn : ((B ^ n : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      spMat 1 (rep8 (-1)) * spMat (pi53 ^ n) 1 * spMat 1 (rep8 (-1)) := by
    rw [Units.val_pow_eq_pow_val, hB, hconj, pow_conj_of_mul_self hD, spMat_one_pow]
  constructor
  · intro e
    have e' := congrArg Units.val e
    rw [hBn, Units.val_one] at e'
    have hP : spMat (pi53 ^ n) 1 = spMat 1 (rep8 (-1)) * (spMat 1 (rep8 (-1)) *
        spMat (pi53 ^ n) 1 * spMat 1 (rep8 (-1))) * spMat 1 (rep8 (-1)) := by
      calc spMat (pi53 ^ n) 1 = (spMat 1 (rep8 (-1)) * spMat 1 (rep8 (-1))) * spMat (pi53 ^ n) 1 *
            (spMat 1 (rep8 (-1)) * spMat 1 (rep8 (-1))) := by
            rw [hD, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e', Matrix.mul_one, hD] at hP
    exact perm_eq_one_of_spMat_eq_one hP
  · intro e
    apply Units.ext
    rw [hBn, e, Units.val_one, show spMat (1 : Equiv.Perm (Fin 8)) (1 : Fin 8 → ZMod 3) = 1 from
      spMat_one, Matrix.mul_one]
    exact hD

namespace N7MatHyp

variable {Xg : Subgroup (GL (Fin 8) (ZMod 3))} (h : N7MatHyp Xg)
include h

theorem not_orbE0_repW_two : ¬ OrbE0 Xg (repW 2) := by
  intro hv
  obtain ⟨ρ, hρ, hρe⟩ := h.mem_fk (σ := Equiv.swap 0 1)
    (s := fun j => if j = 0 ∨ j = 1 then (-1 : ZMod 3) else 1) (by unfold IsSign; decide) (by decide)
  refine h.false_of_reflection hv hρ ?_ fun z => ⟨-(z 0 + z 1), ?_⟩
  · rw [hρe, spMat_mulVec]
    decide
  · rw [hρe, spMat_mulVec]
    funext i
    fin_cases i <;> simp [repW, Equiv.swap_apply_def] <;> ring

theorem not_orbE0_repW_three : ¬ OrbE0 Xg (repW 3) := by
  intro hv
  obtain ⟨B, hB, hBe⟩ := h.perm pi35
  obtain ⟨h15, h5, h3⟩ := pi35_pow
  refine h.false_of_order_fifteen hv hB ?_ ((pow_eq_one_iff_of_spMat_one hBe 15).mpr h15)
    (fun e => h5 ((pow_eq_one_iff_of_spMat_one hBe 5).mp e))
    (fun e => h3 ((pow_eq_one_iff_of_spMat_one hBe 3).mp e))
  rw [hBe, spMat_mulVec]
  decide

theorem not_orbE0_repW_five : ¬ OrbE0 Xg (repW 5) := by
  intro hv
  obtain ⟨B, hB, hBe⟩ := h.perm pi53
  obtain ⟨h15, h5, h3⟩ := pi53_pow
  refine h.false_of_order_fifteen hv hB ?_ ((pow_eq_one_iff_of_spMat_one hBe 15).mpr h15)
    (fun e => h5 ((pow_eq_one_iff_of_spMat_one hBe 5).mp e))
    (fun e => h3 ((pow_eq_one_iff_of_spMat_one hBe 3).mp e))
  rw [hBe, spMat_mulVec]
  decide

theorem not_orbE0_rep8_one : ¬ OrbE0 Xg (rep8 1) := by
  intro hv
  obtain ⟨B, hB, hBe⟩ := h.perm pi53
  obtain ⟨h15, h5, h3⟩ := pi53_pow
  refine h.false_of_order_fifteen hv hB ?_ ((pow_eq_one_iff_of_spMat_one hBe 15).mpr h15)
    (fun e => h5 ((pow_eq_one_iff_of_spMat_one hBe 5).mp e))
    (fun e => h3 ((pow_eq_one_iff_of_spMat_one hBe 3).mp e))
  rw [hBe, spMat_mulVec]
  decide

theorem not_orbE0_rep8_neg_one : ¬ OrbE0 Xg (rep8 (-1)) := by
  intro hv
  obtain ⟨B, hB, hBe⟩ := h.mem_fk (σ := pi53) (s := sign53) (by unfold IsSign; decide) (by decide)
  obtain ⟨h15, h5, h3⟩ := pi53_pow
  refine h.false_of_order_fifteen hv hB ?_ ((pow_eq_one_iff_of_spMat_sign53 hBe 15).mpr h15)
    (fun e => h5 ((pow_eq_one_iff_of_spMat_sign53 hBe 5).mp e))
    (fun e => h3 ((pow_eq_one_iff_of_spMat_sign53 hBe 3).mp e))
  rw [hBe, spMat_mulVec]
  decide

end N7MatHyp

theorem card_perm_fix_zero : Nat.card {σ : Equiv.Perm (Fin 8) // σ 0 = 0} = 5040 := by
  have e1 : {σ : Equiv.Perm (Fin 8) // σ 0 = 0} ≃
      {f : Equiv.Perm (Fin 8) // ∀ a, ¬ (a ≠ 0) → f a = a} :=
    Equiv.subtypeEquivRight fun f => ⟨fun h a ha => by
      rw [not_not] at ha
      subst ha
      exact h, fun h => h 0 (by simp)⟩
  rw [Nat.card_congr (e1.trans (Equiv.Perm.subtypeEquivSubtypePerm
    (fun a : Fin 8 => a ≠ 0)).symm), Nat.card_perm]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_subtype_eq]
  rfl

theorem card_signs_fix_zero :
    Nat.card {s : Fin 8 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i, s i = 1} = 64 := by
  have e : {s : Fin 8 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i, s i = 1} =
      {s : Fin 8 → ZMod 3 // (∀ i, s i = 1 ∨ s i = -1) ∧ s 0 = 1 ∧ ∏ i, s i = 1} := rfl
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem sign_eq_of_spMat_eq {σ τ : Equiv.Perm (Fin 8)} {s t : Fin 8 → ZMod 3} (hs : IsSign s)
    (h : spMat σ s = spMat τ t) : s = t := by
  have hστ := perm_eq_of_spMat_eq hs h
  subst hστ
  funext j
  have e := congrFun (congrFun h (σ j)) j
  rwa [spMat_apply, spMat_apply, if_pos rfl, if_pos rfl] at e

namespace N7MatHyp

variable {Xg : Subgroup (GL (Fin 8) (ZMod 3))} (h : N7MatHyp Xg)
include h

theorem card_stab :
    Nat.card ↥(MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 8 → ZMod 3)) = 322560 := by
  classical
  have hsm : ∀ (A : ↥Xg) (v : Fin 8 → ZMod 3),
      A • v = ((A : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v := fun A v => by
    rw [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec]
  have hex : ∀ q : {σ : Equiv.Perm (Fin 8) // σ 0 = 0} ×
      {s : Fin 8 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i, s i = 1},
      ∃ A ∈ Xg, (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) = spMat q.1.1 q.2.1 :=
    fun q => h.mem_fk q.2.2.1 q.2.2.2.2
  have hfix : ∀ q : {σ : Equiv.Perm (Fin 8) // σ 0 = 0} ×
      {s : Fin 8 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i, s i = 1},
      spMat q.1.1 q.2.1 *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rintro ⟨⟨σ, hσ⟩, ⟨s, -, hs0, -⟩⟩
    have hσ' : σ.symm 0 = 0 := by rw [Equiv.symm_apply_eq, hσ]
    rw [spMat_mulVec]
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [hσ', hs0]
    · have : σ.symm i ≠ 0 := fun h' => hi (by rw [← Equiv.apply_symm_apply σ i, h', hσ])
      simp [Pi.single_eq_of_ne this, Pi.single_eq_of_ne hi]
  let Φ : {σ : Equiv.Perm (Fin 8) // σ 0 = 0} ×
      {s : Fin 8 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i, s i = 1} →
      ↥(MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 8 → ZMod 3)) := fun q =>
    ⟨⟨(hex q).choose, (hex q).choose_spec.1⟩, by
      rw [MulAction.mem_stabilizer_iff, hsm]
      show ((hex q).choose : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ _ = _
      rw [(hex q).choose_spec.2]
      exact hfix q⟩
  have hΦ : ∀ q, (((Φ q : ↥Xg) : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      spMat q.1.1 q.2.1 := fun q => (hex q).choose_spec.2
  have hbij : Function.Bijective Φ := by
    constructor
    · intro q q' hq
      have e := congrArg (fun A : ↥(MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 8 → ZMod 3)) =>
        (((A : ↥Xg) : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))) hq
      simp only [hΦ] at e
      obtain ⟨⟨σ, hσ⟩, ⟨s, hs, hs'⟩⟩ := q
      obtain ⟨⟨σ', hσ''⟩, ⟨s', hs'', hs'''⟩⟩ := q'
      have h1 := perm_eq_of_spMat_eq hs e
      have h2 := sign_eq_of_spMat_eq hs e
      subst h1
      subst h2
      rfl
    · rintro ⟨⟨A, hA⟩, hAs⟩
      rw [MulAction.mem_stabilizer_iff, hsm] at hAs
      obtain ⟨σ, s, hs, hσ0, hs0, hp, hAe⟩ := h.conj_spMat (A₀ := 1) Xg.one_mem hA (c := 1)
        (by rw [Units.val_one, Matrix.one_mulVec, hAs, one_smul])
      refine ⟨(⟨σ, hσ0⟩, ⟨s, hs, hs0, hp⟩), ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      rw [hΦ]
      rw [inv_one, one_mul, mul_one] at hAe
      exact hAe.symm
  rw [← Nat.card_congr (Equiv.ofBijective Φ hbij), Nat.card_prod, card_perm_fix_zero,
    card_signs_fix_zero]

theorem card_eq_orbit :
    Nat.card Xg = {v : Fin 8 → ZMod 3 | OrbE0 Xg v}.ncard * 322560 := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 8 → ZMod 3))
  rw [MulAction.index_stabilizer, h.card_stab] at h1
  have h2 : MulAction.orbit ↥Xg (Pi.single 0 1 : Fin 8 → ZMod 3) = {v | OrbE0 Xg v} := by
    ext v
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq, OrbE0, Subgroup.smul_def,
      Units.smul_def, Matrix.smul_eq_mulVec]
    constructor
    · rintro ⟨⟨A, hA⟩, rfl⟩
      exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨⟨A, hA⟩, rfl⟩
  rw [h2] at h1
  rw [← h1, mul_comm]

end N7MatHyp

theorem conj'_mulVec (A B : GL (Fin 8) (ZMod 3)) (z : Fin 8 → ZMod 3) :
    ((A * B * A⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z =
      (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ ((B : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
        (((A⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mul_assoc]

theorem mulVec_inv_mulVec (A : GL (Fin 8) (ZMod 3)) (z : Fin 8 → ZMod 3) :
    (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      (((A⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem wt_single (k : Fin 8) : wt (Pi.single k (1 : ZMod 3)) = 1 := by
  unfold wt
  rw [Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext i
  by_cases hi : i = k
  · subst hi
    simp
  · simp [hi, Pi.single_eq_of_ne hi]

theorem sum_mul_single (w : Fin 8 → ZMod 3) (k : Fin 8) :
    ∑ j, w j * (Pi.single k (1 : ZMod 3) : Fin 8 → ZMod 3) j = w k := by
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one]

theorem zmod3_refl_coeff {S a : ZMod 3} (ha : a ≠ 0) (h : -a = a + S * a) : S = 1 := by
  revert S a
  decide

theorem zmod3_neg_of_one_add {w a : ZMod 3} (ha : a ≠ 0) (h : 1 + w * a = 0) : w = -a := by
  revert w a
  decide

namespace N7MatHyp

variable {Xg : Subgroup (GL (Fin 8) (ZMod 3))} (h : N7MatHyp Xg)
include h

theorem wt_two_of_reflection (hO : ∀ v, OrbE0 Xg v ↔ (wt v = 1 ∨ wt v = 7))
    {ρ : GL (Fin 8) (ZMod 3)} (hρ : ρ ∈ Xg) {u : Fin 8 → ZMod 3} (hu : u ≠ 0)
    (hρu : (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u = -u)
    (hρl : ∀ z, ∃ c : ZMod 3, (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z - z = c • u) :
    wt u = 2 := by
  have hu17 : ¬ (wt u = 1 ∨ wt u = 7) := fun hw =>
    h.false_of_reflection ((hO u).mpr hw) hρ hρu hρl
  have hpres : ∀ z, (wt z = 1 ∨ wt z = 7) →
      (wt ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) = 1 ∨
        wt ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) = 7) :=
    fun z hz => (hO _).mp (orbE0_mulVec ((hO z).mpr hz) hρ)
  obtain ⟨m, hm⟩ : ∃ m, u m ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu (funext hc)
  obtain ⟨w, hw⟩ : ∃ w : Fin 8 → ZMod 3, ∀ z,
      (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z = z + (∑ j, w j * z j) • u := by
    refine ⟨fun j => u m * ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) m j, fun z => ?_⟩
    obtain ⟨c, hc⟩ := hρl z
    have e2 : ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z - z) m =
        ∑ j, ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) m j * z j := by
      rw [show (ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z - z =
        ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) *ᵥ z by rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
      rfl
    have hcm : ∑ j, u m * ((ρ : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) m j * z j = c := by
      simp only [mul_assoc]
      rw [← Finset.mul_sum, ← e2, hc, Pi.smul_apply, smul_eq_mul, mul_comm c, ← mul_assoc,
        mul_self_of_ne_zero hm, one_mul]
    rw [hcm, ← hc, add_sub_cancel]
  have hwu : ∑ j, w j * u j = 1 := by
    have em := congrFun (hw u) m
    rw [hρu] at em
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at em
    exact zmod3_refl_coeff hm em
  obtain ⟨k, hwk, huk⟩ : ∃ k, w k ≠ 0 ∧ u k ≠ 0 := by
    by_contra hc
    push Not at hc
    have : ∑ j, w j * u j = 0 := Finset.sum_eq_zero fun j _ => by
      by_cases hj : w j = 0
      · rw [hj, zero_mul]
      · rw [hc j hj, mul_zero]
    rw [hwu] at this
    exact one_ne_zero this
  have hek := hpres (Pi.single k 1) (Or.inl (wt_single k))
  rw [hw, sum_mul_single, wt_single_add_smul huk hwk] at hek
  have hw28 : wt u = 2 ∨ wt u = 8 := by
    have hle : wt u ≤ 8 := by
      unfold wt
      exact (Finset.card_le_univ _).trans (by simp)
    split_ifs at hek <;> omega
  rcases hw28 with h2 | h8
  · exact h2
  exfalso
  have hall := (wt_eq_iff_forall_ne_zero u).mp h8
  have hwp : ∀ p, w p ≠ 0 := by
    intro p hp
    have hz7 : wt (u - u p • Pi.single p 1) = 7 := by
      have hz : (u - u p • Pi.single p 1) = Function.update u p 0 := by
        funext i
        by_cases hi : i = p
        · subst hi
          simp
        · simp [hi, Pi.single_eq_of_ne hi]
      rw [hz]
      unfold wt
      have : (Finset.univ.filter fun i => Function.update u p 0 i ≠ 0) = Finset.univ.erase p := by
        ext i
        by_cases hi : i = p
        · subst hi
          simp
        · simp [hi, hall i]
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hρz := hpres _ (Or.inr hz7)
    rw [hw] at hρz
    have hs : ∑ j, w j * (u - u p • Pi.single p 1 : Fin 8 → ZMod 3) j = 1 := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
      rw [hwu]
      have : ∑ j, w j * (u p * (Pi.single p (1 : ZMod 3) : Fin 8 → ZMod 3) j) = 0 := by
        simp only [mul_left_comm (w _), ← Finset.mul_sum, sum_mul_single, hp, mul_zero]
      rw [this, sub_zero]
    rw [hs, one_smul] at hρz
    have h8' : wt (u - u p • Pi.single p 1 + u) = 8 := by
      refine (wt_eq_iff_forall_ne_zero _).mpr fun i => ?_
      by_cases hi : i = p
      · subst hi
        simpa using hall i
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.single_eq_of_ne hi, mul_zero, sub_zero]
        have := hall i
        revert this
        generalize u i = a
        revert a
        decide
    omega
  have hwp' : ∀ p, w p = -u p := by
    intro p
    have hρe := hpres (Pi.single p 1) (Or.inl (wt_single p))
    rw [hw, sum_mul_single, wt_single_add_smul (hall p) (hwp p), h8] at hρe
    by_cases hc : 1 + w p * u p = 0
    · exact zmod3_neg_of_one_add (hall p) hc
    · rw [if_neg hc] at hρe
      omega
  have hz7 : wt (fun j : Fin 8 => if j = 0 then 0 else if (j : ℕ) ≤ 3 then -u j else u j) = 7 := by
    unfold wt
    have : (Finset.univ.filter fun i : Fin 8 =>
        (if i = 0 then 0 else if (i : ℕ) ≤ 3 then -u i else u i) ≠ 0) = Finset.univ.erase 0 := by
      ext i
      by_cases hi : i = 0
      · subst hi
        simp
      · by_cases h3 : (i : ℕ) ≤ 3 <;> simp [hi, h3, hall i]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hρz := hpres _ (Or.inr hz7)
  rw [hw] at hρz
  have hs : ∑ j, w j * (if j = 0 then 0 else if (j : ℕ) ≤ 3 then -u j else u j) = -1 := by
    have hpt : ∀ j : Fin 8, w j * (if j = 0 then 0 else if (j : ℕ) ≤ 3 then -u j else u j) =
        if j = 0 then 0 else if (j : ℕ) ≤ 3 then 1 else -1 := by
      intro j
      rw [hwp' j]
      by_cases hj : j = 0
      · simp [hj]
      · by_cases h3 : (j : ℕ) ≤ 3
        · simp only [hj, h3, if_false, if_true, neg_mul_neg, mul_self_of_ne_zero (hall j)]
        · simp only [hj, h3, if_false, neg_mul, mul_self_of_ne_zero (hall j)]
    rw [Finset.sum_congr rfl (fun j _ => hpt j)]
    decide
  rw [hs] at hρz
  have h4 : wt ((fun j : Fin 8 => if j = 0 then 0 else if (j : ℕ) ≤ 3 then -u j else u j) +
      (-1 : ZMod 3) • u) = 4 := by
    unfold wt
    have : (Finset.univ.filter fun i : Fin 8 =>
        ((fun j : Fin 8 => if j = 0 then 0 else if (j : ℕ) ≤ 3 then -u j else u j) +
          (-1 : ZMod 3) • u) i ≠ 0) = Finset.univ.filter fun i : Fin 8 => (i : ℕ) ≤ 3 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      have hui := hall i
      by_cases hi : i = 0
      · subst hi
        simp only [if_true]
        constructor
        · intro _
          decide
        · intro _
          revert hui
          generalize u 0 = a
          revert a
          decide
      · by_cases h3 : (i : ℕ) ≤ 3
        · simp only [hi, h3, if_false, if_true, iff_true]
          revert hui
          generalize u i = a
          revert a
          decide
        · simp only [hi, h3, if_false, iff_false, not_not]
          ring
    rw [this]
    decide
  omega

theorem false_of_orbit_one_seven (hO : ∀ v, OrbE0 Xg v ↔ (wt v = 1 ∨ wt v = 7)) : False := by
  obtain ⟨A₀, hA₀, hA₀e⟩ := (hO (repW 7)).mpr (Or.inr (by decide))
  have key : ∀ r : GL (Fin 8) (ZMod 3), r ∈ Xg → ∀ d : Fin 8 → ZMod 3, d ≠ 0 →
      (r : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ d = -d →
      (∀ z, ∃ c : ZMod 3, (r : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z - z = c • d) →
      wt ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ d) = 2 := by
    intro r hr d hd hrd hrl
    refine h.wt_two_of_reflection hO (ρ := A₀ * r * A₀⁻¹)
      (Xg.mul_mem (Xg.mul_mem hA₀ hr) (Xg.inv_mem hA₀)) ?_ ?_ ?_
    · intro h0
      apply hd
      rw [← inv_mulVec_mulVec A₀ d, h0, Matrix.mulVec_zero]
    · rw [conj'_mulVec, inv_mulVec_mulVec, hrd, Matrix.mulVec_neg]
    · intro z
      obtain ⟨c, hc⟩ := hrl (((A₀⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z)
      refine ⟨c, ?_⟩
      rw [conj'_mulVec]
      calc (A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ ((r : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
            (((A₀⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z)) - z =
          (A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ ((r : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
            (((A₀⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) -
            ((A₀⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ z) := by
            rw [Matrix.mulVec_sub, mulVec_inv_mulVec]
        _ = c • ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ d) := by
            rw [hc, Matrix.mulVec_smul]
  obtain ⟨rp, hrp, hrpe⟩ := h.mem_fk (σ := Equiv.swap 0 1)
    (s := fun j => if j = 0 ∨ j = 1 then (-1 : ZMod 3) else 1) (by unfold IsSign; decide)
    (by decide)
  obtain ⟨rm, hrm, hrme⟩ := h.perm (Equiv.swap 0 1)
  have ha := key rp hrp (Pi.single 0 1 + Pi.single 1 1) (by decide)
    (by rw [hrpe, spMat_mulVec]; decide) (fun z => ⟨-(z 0 + z 1), by
      rw [hrpe, spMat_mulVec]
      funext i
      fin_cases i <;> simp [Equiv.swap_apply_def] <;> ring⟩)
  have hb := key rm hrm (Pi.single 0 1 - Pi.single 1 1) (by decide)
    (by rw [hrme, spMat_mulVec]; decide) (fun z => ⟨z 1 - z 0, by
      rw [hrme, spMat_mulVec]
      funext i
      fin_cases i <;> simp [Equiv.swap_apply_def] <;> ring⟩)
  have hsum : (A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ (Pi.single 0 1 + Pi.single 1 1) +
      (A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ (Pi.single 0 1 - Pi.single 1 1) =
      (2 : ZMod 3) • repW 7 := by
    rw [← Matrix.mulVec_add, show (Pi.single 0 1 + Pi.single 1 1 + (Pi.single 0 1 - Pi.single 1 1) :
      Fin 8 → ZMod 3) = (2 : ZMod 3) • Pi.single 0 1 by decide, Matrix.mulVec_smul, hA₀e]
  have hle := wt_add_le ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ (Pi.single 0 1 + Pi.single 1 1))
    ((A₀ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ (Pi.single 0 1 - Pi.single 1 1))
  rw [hsum, wt_smul (by decide), ha, hb] at hle
  have h7 : wt (repW 7) = 7 := by decide
  omega

end N7MatHyp

theorem card_wt_1 : (Finset.univ.filter fun v : Fin 8 → ZMod 3 => wt v = 1).card = 16 :=
  card_wt_one

theorem card_wt_14 :
    (Finset.univ.filter fun v : Fin 8 → ZMod 3 => wt v = 1 ∨ wt v = 4).card = 1136 :=
  (N7WtK.card_filter_wt (fun k => k = 1 ∨ k = 4) (fun k => Nat.beq k 1 || Nat.beq k 4)
    (fun k => by simp)).trans (by decide +kernel)

theorem card_wt_16 :
    (Finset.univ.filter fun v : Fin 8 → ZMod 3 => wt v = 1 ∨ wt v = 6).card = 1808 :=
  (N7WtK.card_filter_wt (fun k => k = 1 ∨ k = 6) (fun k => Nat.beq k 1 || Nat.beq k 6)
    (fun k => by simp)).trans (by decide +kernel)

theorem card_wt_146 :
    (Finset.univ.filter fun v : Fin 8 → ZMod 3 => wt v = 1 ∨ wt v = 4 ∨ wt v = 6).card = 2928 :=
  (N7WtK.card_filter_wt (fun k => k = 1 ∨ k = 4 ∨ k = 6)
    (fun k => Nat.beq k 1 || (Nat.beq k 4 || Nat.beq k 6)) (fun k => by simp)).trans
    (by decide +kernel)

theorem card_wt_147 :
    (Finset.univ.filter fun v : Fin 8 → ZMod 3 => wt v = 1 ∨ wt v = 4 ∨ wt v = 7).card = 2160 :=
  (N7WtK.card_filter_wt (fun k => k = 1 ∨ k = 4 ∨ k = 7)
    (fun k => Nat.beq k 1 || (Nat.beq k 4 || Nat.beq k 7)) (fun k => by simp)).trans
    (by decide +kernel)

theorem card_wt_167 :
    (Finset.univ.filter fun v : Fin 8 → ZMod 3 => wt v = 1 ∨ wt v = 6 ∨ wt v = 7).card = 2832 :=
  (N7WtK.card_filter_wt (fun k => k = 1 ∨ k = 6 ∨ k = 7)
    (fun k => Nat.beq k 1 || (Nat.beq k 6 || Nat.beq k 7)) (fun k => by simp)).trans
    (by decide +kernel)

theorem card_wt_1467 :
    (Finset.univ.filter fun v : Fin 8 → ZMod 3 =>
      wt v = 1 ∨ wt v = 4 ∨ wt v = 6 ∨ wt v = 7).card = 3952 :=
  (N7WtK.card_filter_wt (fun k => k = 1 ∨ k = 4 ∨ k = 6 ∨ k = 7)
    (fun k => Nat.beq k 1 || (Nat.beq k 4 || (Nat.beq k 6 || Nat.beq k 7)))
    (fun k => by simp)).trans (by decide +kernel)

theorem ncard_of_card {p : (Fin 8 → ZMod 3) → Prop} [DecidablePred p] {n : ℕ}
    (h : (Finset.univ.filter p).card = n) : {v : Fin 8 → ZMod 3 | p v}.ncard = n := by
  rw [← h, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

theorem orbit_evenAll0_seven (Xg : Subgroup (GL (Fin 8) (ZMod 3))) (h : N7MatHyp Xg)
    (hcard : 2 ^ 8 * Nat.factorial 8 < Nat.card Xg) :
    Nat.card Xg = 696729600 ∧
      ∀ v : Fin 8 → ZMod 3, OrbE0 Xg v ↔ (wt v = 1 ∨ wt v = 4 ∨ wt v = 7) := by
  classical
  have h1 : OrbE0 Xg (repW 1) := by
    rw [show repW 1 = Pi.single 0 1 by decide]
    exact orbE0_e0
  have h0 : ¬ OrbE0 Xg (repW 0) := by
    rintro ⟨A, -, hA⟩
    have : (Pi.single 0 1 : Fin 8 → ZMod 3) = 0 := by
      rw [← inv_mulVec_mulVec A (Pi.single 0 1), hA, show repW 0 = 0 by decide,
        Matrix.mulVec_zero]
    exact absurd (congrFun this 0) (by decide)
  have hw : ∀ v : Fin 8 → ZMod 3, OrbE0 Xg v ↔ (wt v = 1 ∨ (wt v = 4 ∧ OrbE0 Xg (repW 4)) ∨
      (wt v = 6 ∧ OrbE0 Xg (repW 6)) ∨ (wt v = 7 ∧ OrbE0 Xg (repW 7))) := by
    intro v
    have hle : wt v ≤ 8 := by
      unfold wt
      exact (Finset.card_le_univ _).trans (by simp)
    by_cases h8 : wt v = 8
    · rw [h.orbE0_iff_rep8 h8, h8]
      have hall := (wt_eq_iff_forall_ne_zero v).mp h8
      have hp : ∏ i, v i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hall i
      rcases eq_one_or_of_ne_zero hp with hp | hp <;> rw [hp]
      · simp [h.not_orbE0_rep8_one]
      · simp [h.not_orbE0_rep8_neg_one]
    · have hle7 : wt v ≤ 7 := by omega
      rw [h.orbE0_iff_repW hle7]
      interval_cases hv : wt v
      · simp [h0]
      · simp [h1]
      · simp [h.not_orbE0_repW_two]
      · simp [h.not_orbE0_repW_three]
      · simp
      · simp [h.not_orbE0_repW_five]
      · simp
      · simp
  have hX := h.card_eq_orbit
  have hset : {v : Fin 8 → ZMod 3 | OrbE0 Xg v} = {v | wt v = 1 ∨ (wt v = 4 ∧ OrbE0 Xg (repW 4)) ∨
      (wt v = 6 ∧ OrbE0 Xg (repW 6)) ∨ (wt v = 7 ∧ OrbE0 Xg (repW 7))} := Set.ext hw
  have hdvd : Nat.card Xg ∣ ∏ i : Fin 8, (3 ^ 8 - 3 ^ (i : ℕ)) := by
    have := Subgroup.card_subgroup_dvd_card Xg
    rwa [Matrix.card_GL_field, ZMod.card] at this
  by_cases r4 : OrbE0 Xg (repW 4) <;> by_cases r6 : OrbE0 Xg (repW 6) <;>
    by_cases r7 : OrbE0 Xg (repW 7) <;>
    simp only [r4, r6, r7, and_true, and_false, or_false, false_or] at hset hw <;>
    rw [hset] at hX
  · rw [ncard_of_card card_wt_1467] at hX
    rw [hX] at hdvd
    exact absurd hdvd (by decide)
  · rw [ncard_of_card card_wt_146] at hX
    rw [hX] at hdvd
    exact absurd hdvd (by decide)
  · rw [ncard_of_card card_wt_147] at hX
    exact ⟨hX, hw⟩
  · rw [ncard_of_card card_wt_14] at hX
    rw [hX] at hdvd
    exact absurd hdvd (by decide)
  · rw [ncard_of_card card_wt_167] at hX
    rw [hX] at hdvd
    exact absurd hdvd (by decide)
  · rw [ncard_of_card card_wt_16] at hX
    rw [hX] at hdvd
    exact absurd hdvd (by decide)
  · exact (h.false_of_orbit_one_seven hw).elim
  · rw [ncard_of_card card_wt_1] at hX
    rw [hX] at hcard
    exact absurd hcard (by decide)

end CFSG.StandardType.FrameRoute.FS81

end
