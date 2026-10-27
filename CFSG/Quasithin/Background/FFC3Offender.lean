module

public import CFSG.Quasithin.Background.FFC3Para
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.Quasithin

namespace FFC

open Matrix

variable {m : ℕ}

@[expose] def mkVec (α : ZMod 2) (x : Fin m → ZMod 2) (β : ZMod 2) (k : Fin (m + 2)) : ZMod 2 :=
  Fin.cases α (fun j : Fin (m + 1) => Fin.lastCases β (fun i : Fin m => x i) j) k

theorem mkVec_zero (α : ZMod 2) (x : Fin m → ZMod 2) (β : ZMod 2) : mkVec α x β 0 = α := by
  simp [mkVec]

theorem mkVec_mid (α : ZMod 2) (x : Fin m → ZMod 2) (β : ZMod 2) (j : Fin m) :
    mkVec α x β (midIdx j) = x j := by
  simp [mkVec, midIdx]

theorem mkVec_last (α : ZMod 2) (x : Fin m → ZMod 2) (β : ZMod 2) :
    mkVec α x β (Fin.last (m + 1)) = β := by
  simp [mkVec, cases_last']

theorem mkVec_dot (α : ZMod 2) (x : Fin m → ZMod 2) (β : ZMod 2) (v : Fin (m + 2) → ZMod 2) :
    mkVec α x β ⬝ᵥ v = α * v 0 + ∑ j, x j * v (midIdx j) + β * v (Fin.last (m + 1)) := by
  rw [dotProduct, sum_split3]
  simp [mkVec_zero, mkVec_mid, mkVec_last]

theorem mkVec_inj {α α' β β' : ZMod 2} {x x' : Fin m → ZMod 2}
    (h : mkVec α x β = mkVec α' x' β') : α = α' ∧ x = x' ∧ β = β' := by
  refine ⟨?_, funext fun j => ?_, ?_⟩
  · simpa [mkVec_zero] using congrFun h 0
  · simpa [mkVec_mid] using congrFun h (midIdx j)
  · simpa [mkVec_last] using congrFun h (Fin.last (m + 1))

section REntries

variable {g : GL (Fin (m + 2)) (ZMod 2)}

@[expose] def xr (g : GL (Fin (m + 2)) (ZMod 2)) (j : Fin m) : ZMod 2 :=
  (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) 0 (midIdx j)

@[expose] def yr (g : GL (Fin (m + 2)) (ZMod 2)) (i : Fin m) : ZMod 2 :=
  (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) (midIdx i) (Fin.last (m + 1))

@[expose] def cr (g : GL (Fin (m + 2)) (ZMod 2)) : ZMod 2 :=
  (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) 0 (Fin.last (m + 1))

theorem R_zero_zero (hg : g ∈ Rgrp m) : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) 0 0 = 1 := by
  simp [Pgrp_col0 (mem_Rgrp.1 hg).1 0]

theorem R_mid_zero (hg : g ∈ Rgrp m) (i : Fin m) :
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) (midIdx i) 0 = 0 := by
  simp [Pgrp_col0 (mem_Rgrp.1 hg).1 (midIdx i), midIdx_ne_zero]

theorem R_last_zero (hg : g ∈ Rgrp m) :
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) (Fin.last (m + 1)) 0 = 0 := by
  simp [Pgrp_rowLast (mem_Rgrp.1 hg).1 0]

theorem R_last_mid (hg : g ∈ Rgrp m) (j : Fin m) :
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) (Fin.last (m + 1)) (midIdx j) = 0 := by
  simp [Pgrp_rowLast (mem_Rgrp.1 hg).1 (midIdx j), midIdx_ne_last]

theorem R_last_last (hg : g ∈ Rgrp m) :
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) (Fin.last (m + 1)) (Fin.last (m + 1)) = 1 := by
  simp [Pgrp_rowLast (mem_Rgrp.1 hg).1 (Fin.last (m + 1))]

theorem R_mid_mid (hg : g ∈ Rgrp m) (i j : Fin m) :
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) (midIdx i) (midIdx j) = if i = j then 1 else 0 := by
  have h := congrFun (congrFun (mem_Rgrp.1 hg).2 i) j
  simpa [midBlock, Matrix.one_apply] using h

theorem R_ext {g h : GL (Fin (m + 2)) (ZMod 2)} (hg : g ∈ Rgrp m) (hh : h ∈ Rgrp m)
    (hx : xr g = xr h) (hy : yr g = yr h) (hc : cr g = cr h) : g = h := by
  apply Units.ext
  ext a b
  rcases fin_cases3 a with rfl | ⟨i, rfl⟩ | rfl <;> rcases fin_cases3 b with rfl | ⟨j, rfl⟩ | rfl
  · rw [R_zero_zero hg, R_zero_zero hh]
  · exact congrFun hx j
  · exact hc
  · rw [R_mid_zero hg, R_mid_zero hh]
  · rw [R_mid_mid hg, R_mid_mid hh]
  · exact congrFun hy i
  · rw [R_last_zero hg, R_last_zero hh]
  · rw [R_last_mid hg, R_last_mid hh]
  · rw [R_last_last hg, R_last_last hh]

theorem R_mulVec_zero (hg : g ∈ Rgrp m) (v : Fin (m + 2) → ZMod 2) :
    ((g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec v) 0 =
      v 0 + ∑ j, xr g j * v (midIdx j) + cr g * v (Fin.last (m + 1)) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_split3, R_zero_zero hg, one_mul]
  rfl

theorem R_mulVec_mid (hg : g ∈ Rgrp m) (v : Fin (m + 2) → ZMod 2) (i : Fin m) :
    ((g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec v) (midIdx i) =
      v (midIdx i) + yr g i * v (Fin.last (m + 1)) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_split3, R_mid_zero hg]
  simp [R_mid_mid hg, yr]

theorem R_tmulVec_mid (hg : g ∈ Rgrp m) (w : Fin (m + 2) → ZMod 2) (j : Fin m) :
    (((g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec w) (midIdx j) =
      w (midIdx j) + xr g j * w 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [sum_split3]
  simp [R_mid_mid hg, R_last_mid hg, xr]
  ring

theorem R_tmulVec_last (hg : g ∈ Rgrp m) (w : Fin (m + 2) → ZMod 2) :
    (((g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec w) (Fin.last (m + 1)) =
      w (Fin.last (m + 1)) + cr g * w 0 + ∑ i, yr g i * w (midIdx i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [sum_split3, R_last_last hg]
  simp only [one_mul]
  unfold cr yr
  ring

end REntries

@[expose] def fixNat (A : Subgroup (GL (Fin (m + 2)) (ZMod 2))) : Set (Fin (m + 2) → ZMod 2) :=
  {v | ∀ a ∈ A, (a : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec v = v}

@[expose] def fixDual (A : Subgroup (GL (Fin (m + 2)) (ZMod 2))) : Set (Fin (m + 2) → ZMod 2) :=
  {w | ∀ a ∈ A, ((a : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec w = w}

section Offender

variable {A : Subgroup (GL (Fin (m + 2)) (ZMod 2))}

theorem fixNat_dot (hA : A ≤ Rgrp m) {v : Fin (m + 2) → ZMod 2} (hv : v ∈ fixNat A)
    {a : GL (Fin (m + 2)) (ZMod 2)} (ha : a ∈ A) :
    (∑ j, xr a j * v (midIdx j)) + cr a * v (Fin.last (m + 1)) = 0 := by
  have h := congrFun (hv a ha) 0
  rw [R_mulVec_zero (hA ha)] at h
  have h2 : v 0 + ((∑ j, xr a j * v (midIdx j)) + cr a * v (Fin.last (m + 1))) = v 0 + 0 := by
    rw [add_zero, ← add_assoc]
    exact h
  exact add_left_cancel h2

theorem fixNat_mid (hA : A ≤ Rgrp m) {v : Fin (m + 2) → ZMod 2} (hv : v ∈ fixNat A)
    {a : GL (Fin (m + 2)) (ZMod 2)} (ha : a ∈ A) (i : Fin m) :
    yr a i * v (Fin.last (m + 1)) = 0 := by
  have h := congrFun (hv a ha) (midIdx i)
  rw [R_mulVec_mid (hA ha)] at h
  have h2 : v (midIdx i) + yr a i * v (Fin.last (m + 1)) = v (midIdx i) + 0 := by
    rw [add_zero]
    exact h
  exact add_left_cancel h2

theorem fixDual_x (hA : A ≤ Rgrp m) {w : Fin (m + 2) → ZMod 2} (hw : w ∈ fixDual A)
    {a : GL (Fin (m + 2)) (ZMod 2)} (ha : a ∈ A) (j : Fin m) :
    xr a j * w 0 = 0 := by
  have h := congrFun (hw a ha) (midIdx j)
  rw [R_tmulVec_mid (hA ha)] at h
  have h2 : w (midIdx j) + xr a j * w 0 = w (midIdx j) + 0 := by
    rw [add_zero]
    exact h
  exact add_left_cancel h2

theorem fixDual_dot (hA : A ≤ Rgrp m) {w : Fin (m + 2) → ZMod 2} (hw : w ∈ fixDual A)
    {a : GL (Fin (m + 2)) (ZMod 2)} (ha : a ∈ A) :
    cr a * w 0 + ∑ i, yr a i * w (midIdx i) = 0 := by
  have h := congrFun (hw a ha) (Fin.last (m + 1))
  rw [R_tmulVec_last (hA ha)] at h
  have h2 : w (Fin.last (m + 1)) + (cr a * w 0 + ∑ i, yr a i * w (midIdx i)) =
      w (Fin.last (m + 1)) + 0 := by
    rw [add_zero, ← add_assoc]
    exact h
  exact add_left_cancel h2

theorem zmod2_eq_one_of_ne_zero {z : ZMod 2} (h : z ≠ 0) : z = 1 := by
  revert z
  decide

theorem fixNat_last_eq_zero (hA : A ≤ Rgrp m) {a : GL (Fin (m + 2)) (ZMod 2)} (ha : a ∈ A)
    (hy : yr a ≠ 0) {v : Fin (m + 2) → ZMod 2} (hv : v ∈ fixNat A) : v (Fin.last (m + 1)) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, yr a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy (funext hcon)
  have := fixNat_mid hA hv ha i
  rwa [zmod2_eq_one_of_ne_zero hi, one_mul] at this

theorem fixDual_zero_eq_zero (hA : A ≤ Rgrp m) {a : GL (Fin (m + 2)) (ZMod 2)} (ha : a ∈ A)
    (hx : xr a ≠ 0) {w : Fin (m + 2) → ZMod 2} (hw : w ∈ fixDual A) : w 0 = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, xr a j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  have := fixDual_x hA hw ha j
  rwa [zmod2_eq_one_of_ne_zero hj, one_mul] at this

end Offender

theorem card_mul_card_le_pow_field {K : Type*} [Field K] [Fintype K] {k : ℕ} {S : Type*} [Finite S]
    (ι : S → (Fin k → K)) (hι : Function.Injective ι) (C : Set (Fin k → K))
    (hC : ∀ s, ∀ v ∈ C, ι s ⬝ᵥ v = 0) :
    Nat.card S * Nat.card C ≤ Fintype.card K ^ k := by
  classical
  let Φ : Subspace K (Module.Dual K (Fin k → K)) :=
    Submodule.span K (Set.range fun s => dotProductEquiv K (Fin k) (ι s))
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  have hCsub : C ⊆ (Φ.dualCoannihilator : Set (Fin k → K)) := by
    intro v hv
    rw [SetLike.mem_coe, Submodule.mem_dualCoannihilator]
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      simpa [dotProductEquiv] using hC s v hv
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have h1 : Nat.card C ≤ Nat.card Φ.dualCoannihilator := Nat.card_mono (Set.toFinite _) hCsub
  have hinj : Function.Injective (fun s : S => (⟨dotProductEquiv K (Fin k) (ι s),
      Submodule.subset_span ⟨s, rfl⟩⟩ : Φ)) := by
    intro s t hst
    have := congrArg Subtype.val hst
    exact hι ((dotProductEquiv K (Fin k)).injective this)
  have : Finite Φ := Module.finite_of_finite K
  have h2 : Nat.card S ≤ Nat.card Φ := Nat.card_le_card_of_injective _ hinj
  have hΦ : Nat.card Φ = Fintype.card K ^ Module.finrank K Φ := by
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
  have hΦo : Nat.card Φ.dualCoannihilator =
      Fintype.card K ^ Module.finrank K Φ.dualCoannihilator := by
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
  calc Nat.card S * Nat.card C ≤ Nat.card Φ * Nat.card Φ.dualCoannihilator := Nat.mul_le_mul h2 h1
    _ = Fintype.card K ^ k := by rw [hΦ, hΦo, ← pow_add, hdim]

theorem card_mul_card_le_two_pow {k : ℕ} {S : Type*} [Finite S] (ι : S → (Fin k → ZMod 2))
    (hι : Function.Injective ι) (C : Set (Fin k → ZMod 2)) (hC : ∀ s, ∀ v ∈ C, ι s ⬝ᵥ v = 0) :
    Nat.card S * Nat.card C ≤ 2 ^ k := by
  have := card_mul_card_le_pow_field (K := ZMod 2) ι hι C hC
  simpa [ZMod.card] using this

section OffenderCases

variable {A : Subgroup (GL (Fin (m + 2)) (ZMod 2))}

theorem xr_one : xr (1 : GL (Fin (m + 2)) (ZMod 2)) = 0 := by
  funext j
  simp [xr, (midIdx_ne_zero j).symm]

theorem yr_one : yr (1 : GL (Fin (m + 2)) (ZMod 2)) = 0 := by
  funext i
  simp [yr, midIdx_ne_last i]

theorem cr_one : cr (1 : GL (Fin (m + 2)) (ZMod 2)) = 0 := by
  simp [cr]

theorem one_mem_Rgrp : (1 : GL (Fin (m + 2)) (ZMod 2)) ∈ Rgrp m := Subgroup.one_mem _

theorem R_eq_one_of_params {g : GL (Fin (m + 2)) (ZMod 2)} (hg : g ∈ Rgrp m) (hx : xr g = 0)
    (hy : yr g = 0) (hc : cr g = 0) : g = 1 :=
  R_ext hg one_mem_Rgrp (hx.trans xr_one.symm) (hy.trans yr_one.symm) (hc.trans cr_one.symm)

theorem offender_case_I (hA : A ≤ Rgrp m) {a₁ a₂ : GL (Fin (m + 2)) (ZMod 2)} (h₁ : a₁ ∈ A)
    (h₂ : a₂ ∈ A) (hx : xr a₁ ≠ 0) (hy : yr a₂ ≠ 0) :
    2 * (Nat.card A * Nat.card (fixNat A) * Nat.card (fixDual A)) ≤ 2 ^ (m + 2) * 2 ^ (m + 2) := by
  classical
  let X : Set (Fin m → ZMod 2) := Set.range fun a : A => xr a.1
  let Y : Set (Fin m → ZMod 2) := Set.range fun a : A => yr a.1
  have hN : Nat.card X * 2 * Nat.card (fixNat A) ≤ 2 ^ (m + 2) := by
    have := card_mul_card_le_two_pow (S := ↥X × ZMod 2) (fun p => mkVec 0 p.1.1 p.2) ?_
      (fixNat A) ?_
    · rwa [Nat.card_prod, Nat.card_zmod] at this
    · intro p q h
      obtain ⟨-, h2, h3⟩ := mkVec_inj h
      exact Prod.ext (Subtype.ext h2) h3
    · rintro ⟨⟨x, a, rfl⟩, ε⟩ v hv
      have hl := fixNat_last_eq_zero hA h₂ hy hv
      have hd := fixNat_dot hA hv a.2
      rw [hl, mul_zero, add_zero] at hd
      simp only [mkVec_dot, zero_mul, hl, mul_zero, add_zero, hd]
  have hD : Nat.card Y * 2 * Nat.card (fixDual A) ≤ 2 ^ (m + 2) := by
    have := card_mul_card_le_two_pow (S := ↥Y × ZMod 2) (fun p => mkVec p.2 p.1.1 0) ?_
      (fixDual A) ?_
    · rwa [Nat.card_prod, Nat.card_zmod] at this
    · intro p q h
      obtain ⟨h1, h2, -⟩ := mkVec_inj h
      exact Prod.ext (Subtype.ext h2) h1
    · rintro ⟨⟨y, a, rfl⟩, ε⟩ w hw
      have hz := fixDual_zero_eq_zero hA h₁ hx hw
      have hd := fixDual_dot hA hw a.2
      rw [hz, mul_zero, zero_add] at hd
      simp only [mkVec_dot, hz, mul_zero, hd, zero_mul, add_zero]
  have hAle : Nat.card A ≤ Nat.card X * Nat.card Y * 2 := by
    have hinj : Function.Injective (fun a : A => ((⟨xr a.1, a, rfl⟩ : X), (⟨yr a.1, a, rfl⟩ : Y),
        cr a.1)) := by
      intro a b h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      exact Subtype.ext (R_ext (hA a.2) (hA b.2) (congrArg Subtype.val h1)
        (congrArg Subtype.val h2) h3)
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod, Nat.card_prod, Nat.card_zmod, ← mul_assoc] at this
  calc 2 * (Nat.card A * Nat.card (fixNat A) * Nat.card (fixDual A))
      ≤ 2 * (Nat.card X * Nat.card Y * 2 * Nat.card (fixNat A) * Nat.card (fixDual A)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul hAle le_rfl) le_rfl)
    _ = (Nat.card X * 2 * Nat.card (fixNat A)) * (Nat.card Y * 2 * Nat.card (fixDual A)) := by ring
    _ ≤ 2 ^ (m + 2) * 2 ^ (m + 2) := Nat.mul_le_mul hN hD

theorem offender_case_II (hA : A ≤ Rgrp m) (hy : ∀ a ∈ A, yr a = 0) (hA1 : A ≠ ⊥) :
    2 * (Nat.card A * Nat.card (fixNat A) * Nat.card (fixDual A)) ≤ 2 ^ (m + 2) * 2 ^ (m + 2) := by
  classical
  have hN : Nat.card A * Nat.card (fixNat A) ≤ 2 ^ (m + 2) := by
    refine card_mul_card_le_two_pow (S := A) (fun a => mkVec 0 (xr a.1) (cr a.1)) ?_ (fixNat A) ?_
    · intro a b h
      obtain ⟨-, h2, h3⟩ := mkVec_inj h
      exact Subtype.ext (R_ext (hA a.2) (hA b.2) h2 ((hy _ a.2).trans (hy _ b.2).symm) h3)
    · intro a v hv
      have hd := fixNat_dot hA hv a.2
      simp only [mkVec_dot, zero_mul, zero_add]
      exact hd
  have hw0 : ∀ w ∈ fixDual A, w 0 = 0 := by
    obtain ⟨a₀, ha₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
    intro w hw
    have hne : ¬ (xr a₀.1 = 0 ∧ cr a₀.1 = 0) := by
      rintro ⟨h1, h2⟩
      exact ha₀ (Subtype.ext (R_eq_one_of_params (hA a₀.2) h1 (hy _ a₀.2) h2))
    by_cases hx : xr a₀.1 = 0
    · have hc : cr a₀.1 ≠ 0 := fun h => hne ⟨hx, h⟩
      have hd := fixDual_dot hA hw a₀.2
      rw [hy _ a₀.2] at hd
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at hd
      rwa [zmod2_eq_one_of_ne_zero hc, one_mul] at hd
    · exact fixDual_zero_eq_zero hA a₀.2 hx hw
  have hD : 2 * Nat.card (fixDual A) ≤ 2 ^ (m + 2) := by
    have := card_mul_card_le_two_pow (S := ZMod 2) (fun ε => mkVec ε (0 : Fin m → ZMod 2) 0) ?_
      (fixDual A) ?_
    · rwa [Nat.card_zmod] at this
    · intro ε ε' h
      exact (mkVec_inj h).1
    · intro ε w hw
      simp only [mkVec_dot, hw0 w hw, mul_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  calc 2 * (Nat.card A * Nat.card (fixNat A) * Nat.card (fixDual A))
      = (Nat.card A * Nat.card (fixNat A)) * (2 * Nat.card (fixDual A)) := by ring
    _ ≤ 2 ^ (m + 2) * 2 ^ (m + 2) := Nat.mul_le_mul hN hD

theorem offender_case_III (hA : A ≤ Rgrp m) (hx : ∀ a ∈ A, xr a = 0) (hA1 : A ≠ ⊥) :
    2 * (Nat.card A * Nat.card (fixNat A) * Nat.card (fixDual A)) ≤ 2 ^ (m + 2) * 2 ^ (m + 2) := by
  classical
  have hD : Nat.card A * Nat.card (fixDual A) ≤ 2 ^ (m + 2) := by
    refine card_mul_card_le_two_pow (S := A) (fun a => mkVec (cr a.1) (yr a.1) 0) ?_ (fixDual A) ?_
    · intro a b h
      obtain ⟨h1, h2, -⟩ := mkVec_inj h
      exact Subtype.ext (R_ext (hA a.2) (hA b.2) ((hx _ a.2).trans (hx _ b.2).symm) h2 h1)
    · intro a w hw
      have hd := fixDual_dot hA hw a.2
      simp only [mkVec_dot, zero_mul, add_zero]
      exact hd
  have hv0 : ∀ v ∈ fixNat A, v (Fin.last (m + 1)) = 0 := by
    obtain ⟨a₀, ha₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
    intro v hv
    have hne : ¬ (yr a₀.1 = 0 ∧ cr a₀.1 = 0) := by
      rintro ⟨h1, h2⟩
      exact ha₀ (Subtype.ext (R_eq_one_of_params (hA a₀.2) (hx _ a₀.2) h1 h2))
    by_cases hy : yr a₀.1 = 0
    · have hc : cr a₀.1 ≠ 0 := fun h => hne ⟨hy, h⟩
      have hd := fixNat_dot hA hv a₀.2
      rw [hx _ a₀.2] at hd
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at hd
      rwa [zmod2_eq_one_of_ne_zero hc, one_mul] at hd
    · exact fixNat_last_eq_zero hA a₀.2 hy hv
  have hN : 2 * Nat.card (fixNat A) ≤ 2 ^ (m + 2) := by
    have := card_mul_card_le_two_pow (S := ZMod 2) (fun ε => mkVec 0 (0 : Fin m → ZMod 2) ε) ?_
      (fixNat A) ?_
    · rwa [Nat.card_zmod] at this
    · intro ε ε' h
      exact (mkVec_inj h).2.2
    · intro ε v hv
      simp only [mkVec_dot, hv0 v hv, mul_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        add_zero]
  calc 2 * (Nat.card A * Nat.card (fixNat A) * Nat.card (fixDual A))
      = (2 * Nat.card (fixNat A)) * (Nat.card A * Nat.card (fixDual A)) := by ring
    _ ≤ 2 ^ (m + 2) * 2 ^ (m + 2) := Nat.mul_le_mul hN hD

theorem model_offender (hA : A ≤ Rgrp m) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card (fixNat A) * Nat.card (fixDual A) < 2 ^ (m + 2) * 2 ^ (m + 2) := by
  have h2 : 2 * (Nat.card A * Nat.card (fixNat A) * Nat.card (fixDual A)) ≤
      2 ^ (m + 2) * 2 ^ (m + 2) := by
    by_cases hI : (∃ a ∈ A, xr a ≠ 0) ∧ (∃ a ∈ A, yr a ≠ 0)
    · obtain ⟨⟨a₁, h₁, hx⟩, ⟨a₂, h₂, hy⟩⟩ := hI
      exact offender_case_I hA h₁ h₂ hx hy
    · rw [not_and_or] at hI
      rcases hI with h | h
      · push Not at h
        exact offender_case_III hA h hA1
      · push Not at h
        exact offender_case_II hA h hA1
  have hpos : 0 < 2 ^ (m + 2) * 2 ^ (m + 2) := by positivity
  omega

end OffenderCases

end FFC

end CFSG.Quasithin
