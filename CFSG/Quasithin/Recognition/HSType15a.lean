module

public import CFSG.Quasithin.Recognition.HSTypeS6
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Std.Tactic.BVDecide.Normalize.Prop
import CFSG.Quasithin.Recognition.HSType15aPack

public section

namespace CFSG.Quasithin.HSType

open CFSG.Permutation.FinPack CFSG.Quasithin.HSType.Pack15a

@[expose] def hsJ (v : SpV) : SpV := ![v 3, v 2, v 1 + v 2, v 0 + v 3]

@[expose] def lamS : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {σ | ∀ v, actS6 σ (hsJ v) = hsJ (actS6 σ v)}
  mul_mem' {σ τ} hσ hτ := by
    simp only [Set.mem_ofPred_eq] at hσ hτ ⊢
    intro v
    rw [actS6_mul, actS6_mul, hτ, hσ]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, actS6_one, implies_true]
  inv_mem' {σ} hσ := by
    simp only [Set.mem_ofPred_eq] at hσ ⊢
    intro v
    have h1 : ∀ w, actS6 σ (actS6 σ⁻¹ w) = w := fun w => by
      rw [← actS6_mul, mul_inv_cancel, actS6_one]
    have hinj : Function.Injective (actS6 σ) := fun a b hab => by
      have := congrArg (actS6 σ⁻¹) hab
      rwa [← actS6_mul, ← actS6_mul, inv_mul_cancel, actS6_one, actS6_one] at this
    apply hinj
    rw [h1, hσ, h1]

theorem hsJ_add (v w : SpV) : hsJ (v + w) = hsJ v + hsJ w := by
  funext k
  fin_cases k <;> simp [hsJ] <;> ring

theorem hsJ_smul (c : ZMod 2) (v : SpV) : hsJ (c • v) = c • hsJ v := by
  funext k
  fin_cases k <;> simp [hsJ] <;> ring

theorem mem_lamS_iff_basis (σ : Equiv.Perm (Fin 6)) :
    (∀ v, actS6 σ (hsJ v) = hsJ (actS6 σ v)) ↔
      ∀ k : Fin 4, actS6 σ (hsJ (spE k)) = hsJ (actS6 σ (spE k)) := by
  refine ⟨fun h k => h _, fun h v => ?_⟩
  have hv : v = v 0 • spE 0 + v 1 • spE 1 + v 2 • spE 2 + v 3 • spE 3 := by
    funext k
    fin_cases k <;> simp [spE]
  rw [hv]
  simp only [hsJ_add, hsJ_smul, actS6_add, actS6_smul, h]

instance : DecidablePred (· ∈ lamS) := fun σ =>
  decidable_of_iff (∀ k : Fin 4, actS6 σ (hsJ (spE k)) = hsJ (actS6 σ (spE k)))
    (mem_lamS_iff_basis σ).symm

private theorem vK_hsJ : ∀ v : SpV, vK (hsJ v) = rd hjT (vK v) := by decide +kernel

private theorem vK_lits : vK 0 = 0 ∧ vK (spE 0) = 1 ∧ vK (spE 1) = 2 ∧ vK (spE 2) = 4 ∧
    vK (spE 3) = 8 ∧ vK (spE 0 + spE 3) = 9 ∧ vK (hsJ (spE 0)) = 8 ∧ vK (hsJ (spE 1)) = 4 ∧
    vK (hsJ (spE 2)) = 6 ∧ vK (hsJ (spE 3)) = 9 := by
  decide

private theorem forall_fin_four {P : Fin 4 → Prop} : (∀ k, P k) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 :=
  ⟨fun h => ⟨h 0, h 1, h 2, h 3⟩, fun ⟨a, b, c, d⟩ k => by fin_cases k <;> assumption⟩

private theorem mem_lamS_K (σ : Equiv.Perm (Fin 6)) : σ ∈ lamS ↔ lamQ (enc σ) = true := by
  obtain ⟨-, l1, l2, l4, l8, -, j0, j1, j2, j3⟩ := vK_lits
  change (∀ v, actS6 σ (hsJ v) = hsJ (actS6 σ v)) ↔ _
  rw [mem_lamS_iff_basis, forall_fin_four]
  simp only [eq_iff_vK, vK_actS6]
  simp only [j0, j1, j2, j3]
  simp only [vK_hsJ, vK_actS6, l1, l2, l4, l8]
  rw [lamQ, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, and_assoc, and_assoc]

@[expose] def InV2m (v : SpV) : Prop := v 1 = 0 ∧ v 2 = 0

instance : DecidablePred InV2m := fun v => inferInstanceAs (Decidable (v 1 = 0 ∧ v 2 = 0))

theorem InV2m_zero : InV2m 0 := ⟨rfl, rfl⟩

theorem InV2m_add {v w : SpV} (hv : InV2m v) (hw : InV2m w) : InV2m (v + w) := by
  refine ⟨?_, ?_⟩
  · rw [Pi.add_apply, hv.1, hw.1, add_zero]
  · rw [Pi.add_apply, hv.2, hw.2, add_zero]

theorem InV2m_spE0 : InV2m (spE 0) := by decide

theorem InV2m_spE3 : InV2m (spE 3) := by decide

theorem spForm_spE0_of_InV2m : ∀ v : SpV, InV2m v → spForm (spE 0) v = 0 := by decide

theorem InV2m_cases : ∀ v : SpV, InV2m v → v = 0 ∨ v = spE 0 ∨ v = spE 3 ∨ v = spE 0 + spE 3 := by
  decide

@[expose] def InC0m (v : SpV) : Prop := v 0 = 0 ∧ v 3 = 0

instance : DecidablePred InC0m := fun v => inferInstanceAs (Decidable (v 0 = 0 ∧ v 3 = 0))

theorem InC0m_zero : InC0m 0 := ⟨rfl, rfl⟩

theorem InC0m_add {v w : SpV} (hv : InC0m v) (hw : InC0m w) : InC0m (v + w) := by
  refine ⟨?_, ?_⟩
  · rw [Pi.add_apply, hv.1, hw.1, add_zero]
  · rw [Pi.add_apply, hv.2, hw.2, add_zero]

theorem eq_zero_of_InC0m_InV2m : ∀ v : SpV, InC0m v → InV2m v → v = 0 := by decide

private theorem forall_InV2m_iff (P : SpV → Prop) :
    (∀ v, InV2m v → P v) ↔ P 0 ∧ P (spE 0) ∧ P (spE 3) ∧ P (spE 0 + spE 3) :=
  ⟨fun h => ⟨h _ InV2m_zero, h _ InV2m_spE0, h _ InV2m_spE3, h _ (InV2m_add InV2m_spE0 InV2m_spE3)⟩,
    fun ⟨h0, h1, h2, h3⟩ v hv => by rcases InV2m_cases v hv with rfl | rfl | rfl | rfl <;> assumption⟩

private theorem InV2m_iff_vK : ∀ v : SpV, InV2m v ↔ Nat.beq (Nat.land (vK v) 6) 0 = true := by
  decide +kernel

private theorem stab_iff (σ : Equiv.Perm (Fin 6)) :
    (∀ v, InV2m v → InV2m (actS6 σ v)) ↔ stabQ (enc σ) = true := by
  obtain ⟨l0, l1, -, -, l8, l9, -⟩ := vK_lits
  refine (forall_InV2m_iff fun v => InV2m (actS6 σ v)).trans ?_
  simp only [InV2m_iff_vK, vK_actS6, l0, l1, l8, l9]
  rw [stabQ, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, and_assoc, and_assoc]

private theorem fix_iff (σ : Equiv.Perm (Fin 6)) :
    (∀ v, InV2m v → actS6 σ v = v) ↔ fixQ (enc σ) = true := by
  obtain ⟨l0, l1, -, -, l8, l9, -⟩ := vK_lits
  refine (forall_InV2m_iff fun v => actS6 σ v = v).trans ?_
  simp only [eq_iff_vK, vK_actS6, l0, l1, l8, l9]
  rw [fixQ, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, and_assoc, and_assoc]

@[expose] def stabS : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {σ | ∀ v, InV2m v → InV2m (actS6 σ v)}
  mul_mem' {σ τ} hσ hτ := by
    simp only [Set.mem_ofPred_eq] at hσ hτ ⊢
    intro v hv
    rw [actS6_mul]
    exact hσ _ (hτ v hv)
  one_mem' := by
    simp only [Set.mem_ofPred_eq, actS6_one, imp_self, implies_true]
  inv_mem' {σ} hσ := by
    simp only [Set.mem_ofPred_eq] at hσ ⊢
    have key : ∀ σ : Equiv.Perm (Fin 6), (∀ v, InV2m v → InV2m (actS6 σ v)) →
        ∀ v, InV2m v → InV2m (actS6 σ⁻¹ v) := by
      intro σ h
      rw [stab_iff] at h ⊢
      have hw := walkK_sound stabQ_inv σ
      simp only [h, Bool.not_true, Bool.false_or] at hw
      rwa [enc_inv_invCK six_le]
    exact key σ hσ

instance : DecidablePred (· ∈ stabS) := fun σ =>
  decidable_of_iff (∀ v, InV2m v → InV2m (actS6 σ v)) Iff.rfl

@[expose] def fixS : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {σ | ∀ v, InV2m v → actS6 σ v = v}
  mul_mem' {σ τ} hσ hτ := by
    simp only [Set.mem_ofPred_eq] at hσ hτ ⊢
    intro v hv
    rw [actS6_mul, hτ v hv, hσ v hv]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, actS6_one, implies_true]
  inv_mem' {σ} hσ := by
    simp only [Set.mem_ofPred_eq] at hσ ⊢
    intro v hv
    calc actS6 σ⁻¹ v = actS6 σ⁻¹ (actS6 σ v) := by rw [hσ v hv]
      _ = v := by rw [← actS6_mul, inv_mul_cancel, actS6_one]

instance : DecidablePred (· ∈ fixS) := fun σ =>
  decidable_of_iff (∀ v, InV2m v → actS6 σ v = v) Iff.rfl

abbrev lam0 : Subgroup (Equiv.Perm (Fin 6)) := lamS ⊓ stabS

abbrev kleinS : Subgroup (Equiv.Perm (Fin 6)) := lamS ⊓ fixS

instance : DecidablePred (· ∈ lam0) := fun σ =>
  decidable_of_iff (σ ∈ stabS ∧ σ ∈ lamS) (and_comm.trans Subgroup.mem_inf.symm)

instance : DecidablePred (· ∈ kleinS) := fun σ =>
  decidable_of_iff (σ ∈ fixS ∧ σ ∈ lamS) (and_comm.trans Subgroup.mem_inf.symm)

theorem fixS_le_stabS : fixS ≤ stabS := fun σ hσ v hv => by
  have h1 : actS6 σ v = v := hσ v hv
  rw [h1]
  exact hv

theorem kleinS_le_lam0 : kleinS ≤ lam0 := inf_le_inf_left _ fixS_le_stabS

private theorem mem_lam0_K (σ : Equiv.Perm (Fin 6)) :
    σ ∈ lam0 ↔ (stabQ (enc σ) && lamQ (enc σ)) = true := by
  change σ ∈ lamS ⊓ stabS ↔ _
  rw [Subgroup.mem_inf, mem_lamS_K, Bool.and_eq_true, and_comm]
  exact Iff.and (stab_iff σ) Iff.rfl

private theorem mem_kleinS_K (σ : Equiv.Perm (Fin 6)) :
    σ ∈ kleinS ↔ (fixQ (enc σ) && lamQ (enc σ)) = true := by
  change σ ∈ lamS ⊓ fixS ↔ _
  rw [Subgroup.mem_inf, mem_lamS_K, Bool.and_eq_true, and_comm]
  exact Iff.and (fix_iff σ) Iff.rfl

theorem card_lamS : Nat.card lamS = 60 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (card_filter_of_iff _ lamQ mem_lamS_K).trans lamQ_cnt

theorem card_stabS : Nat.card stabS = 48 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (card_filter_of_iff _ stabQ stab_iff).trans stabQ_cnt

theorem card_lam0 : Nat.card lam0 = 12 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (card_filter_of_iff _ (fun c => stabQ c && lamQ c) mem_lam0_K).trans lam0Q_cnt

theorem card_kleinS : Nat.card kleinS = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (card_filter_of_iff _ (fun c => fixQ c && lamQ c) mem_kleinS_K).trans kleinQ_cnt

theorem card_fixS : Nat.card fixS = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (card_filter_of_iff _ fixQ fix_iff).trans fixQ_cnt

@[expose] def αS : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 4 5

@[expose] def βS : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 3 5 * Equiv.swap 5 4

@[expose] def σS0 : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 3 * Equiv.swap 3 5

theorem αS_mem : αS ∈ lamS := by decide

theorem βS_mem : βS ∈ lamS := by decide

theorem σS0_mem : σS0 ∈ lam0 := by decide

theorem αS_mul_self : αS * αS = 1 := by decide

theorem βS_pow_three : βS ^ 3 = 1 := by decide

theorem αS_βS_pow_five : (αS * βS) ^ 5 = 1 := by decide

@[expose] def evalAB : List Bool → Equiv.Perm (Fin 6)
  | [] => 1
  | b :: w => (if b then βS else αS) * evalAB w

theorem evalAB_mem (w : List Bool) : evalAB w ∈ Subgroup.closure {αS, βS} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons b w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    cases b
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def abWords : List (List Bool) :=
  [[], [false], [true], [true, false], [false, true], [true, true], [false, true, false],
    [true, true, false], [true, false, true], [false, true, true], [true, false, true, false],
    [false, true, true, false], [false, true, false, true], [true, true, false, true],
    [true, false, true, true], [false, true, false, true, false], [true, true, false, true, false],
    [true, false, true, true, false], [true, false, true, false, true],
    [false, true, true, false, true], [false, true, false, true, true],
    [true, true, false, true, true], [true, false, true, false, true, false],
    [false, true, true, false, true, false], [false, true, false, true, true, false],
    [true, true, false, true, true, false], [true, true, false, true, false, true],
    [true, false, true, true, false, true], [true, false, true, false, true, true],
    [true, true, false, true, false, true, false], [true, false, true, true, false, true, false],
    [true, false, true, false, true, true, false], [false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true], [true, true, false, true, true, false, true],
    [true, true, false, true, false, true, true],
    [false, true, true, false, true, false, true, false],
    [false, true, false, true, true, false, true, false],
    [true, true, false, true, true, false, true, false],
    [true, true, false, true, false, true, true, false],
    [true, false, true, true, false, true, false, true],
    [true, false, true, false, true, true, false, true],
    [false, true, true, false, true, false, true, true],
    [true, false, true, true, false, true, false, true, false],
    [true, false, true, false, true, true, false, true, false],
    [false, true, true, false, true, false, true, true, false],
    [false, true, false, true, true, false, true, false, true],
    [true, true, false, true, true, false, true, false, true],
    [true, true, false, true, false, true, true, false, true],
    [true, false, true, true, false, true, false, true, true],
    [false, true, false, true, true, false, true, false, true, false],
    [true, true, false, true, true, false, true, false, true, false],
    [true, true, false, true, false, true, true, false, true, false],
    [true, false, true, true, false, true, false, true, true, false],
    [false, true, true, false, true, false, true, true, false, true],
    [false, true, false, true, true, false, true, false, true, true],
    [false, true, true, false, true, false, true, true, false, true, false],
    [false, true, false, true, true, false, true, false, true, true, false],
    [true, false, true, true, false, true, false, true, true, false, true],
    [true, false, true, true, false, true, false, true, true, false, true, false]]

private theorem enc_αS' : enc αS = alphaC := by decide +kernel

private theorem enc_βS' : enc βS = betaC := by decide +kernel

private theorem enc_evalAB (w : List Bool) : enc (evalAB w) = evalABK w := by
  induction w with
  | nil => exact enc_one_six
  | cons b w ih =>
    rw [evalAB, enc_mul six_le, ih]
    cases b
    · rw [if_neg Bool.false_ne_true, enc_αS']
      rfl
    · rw [if_pos rfl, enc_βS']
      rfl

private theorem abWords_codes : (abWords.map evalABK == wordC) = true := by decide +kernel

theorem exists_abWord : ∀ σ : Equiv.Perm (Fin 6), σ ∈ lamS → ∃ w ∈ abWords, evalAB w = σ := by
  intro σ hσ
  have hw := walkK_sound word_walk σ
  simp only [(mem_lamS_K σ).1 hσ, Bool.not_true, Bool.false_or] at hw
  have hm := memK_iff.1 hw
  rw [← beq_iff_eq.1 abWords_codes, List.mem_map] at hm
  obtain ⟨w, hw', he⟩ := hm
  exact ⟨w, hw', enc_inj six_le ((enc_evalAB w).trans he)⟩

theorem closure_αS_βS : Subgroup.closure {αS, βS} = lamS := by
  refine le_antisymm ?_ fun σ hσ => ?_
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact αS_mem
    · exact βS_mem
  · obtain ⟨w, -, rfl⟩ := exists_abWord σ hσ
    exact evalAB_mem w

theorem eq_zero_of_actS6_βS : ∀ v : SpV, actS6 βS v = v → v = 0 := by decide

theorem exists_add_actS6_σS0 : ∀ u : SpV, ∃ w : SpV, w + actS6 σS0 w = u := by decide

theorem exists_mem_V2m_of_σS0 : ∀ v : SpV, ¬ InV2m v → ∀ w : SpV, ∃ e₁ e₂ : ZMod 2,
    InV2m (w + e₁ • v + e₂ • actS6 σS0 v) := by
  decide

theorem exists_stabS_map (a b : SpV) (h : InV2m a ∧ InV2m b ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) :
    ∃ σ : Equiv.Perm (Fin 6), σ ∈ stabS ∧ actS6 σ (spE 0) = a ∧ actS6 σ (spE 3) = b := by
  obtain ⟨ha, hb, ha0, hb0, hab⟩ := h
  rcases InV2m_cases a ha with rfl | rfl | rfl | rfl <;>
    rcases InV2m_cases b hb with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl ha0
      | exact absurd rfl hb0
      | exact absurd rfl hab
      | exact ⟨1, by decide, by decide, by decide⟩
      | exact ⟨Equiv.swap 2 4 * Equiv.swap 3 5, by decide, by decide, by decide⟩
      | exact ⟨Equiv.swap 0 4 * Equiv.swap 1 5, by decide, by decide, by decide⟩
      | exact ⟨Equiv.swap 0 4 * Equiv.swap 4 2 * Equiv.swap 1 5 * Equiv.swap 5 3, by decide,
          by decide, by decide⟩
      | exact ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide, by decide, by decide⟩
      | exact ⟨Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 3 * Equiv.swap 3 5, by decide,
          by decide, by decide⟩

theorem mem_kleinS_of_lam0 : ∀ σ : Equiv.Perm (Fin 6), σ ∈ lam0 → σ * σ = 1 → σ ∈ kleinS := by
  intro σ h1 h2
  have hw := walkK_sound klein_walk σ
  simp only [(mem_lam0_K σ).1 h1, (sq_iff σ).2 h2, Bool.not_true, Bool.false_or] at hw
  exact (mem_kleinS_K σ).2 hw

theorem σS0_pow_three : σS0 ^ 3 = 1 := by decide

theorem mem_lamS_of_pow_three : ∀ σ : Equiv.Perm (Fin 6), σ ∈ stabS → σ ^ 3 = 1 → σ ∈ lamS := by
  intro σ h1 h2
  have hw := walkK_sound pow3_walk σ
  simp only [(stab_iff σ).1 h1, (cube_iff σ).2 h2, Bool.not_true, Bool.false_or] at hw
  exact (mem_lamS_K σ).2 hw

private theorem enc_σS0_inv' : enc σS0⁻¹ = sigmaInvC := by
  rw [enc_inv_invCK six_le]
  decide +kernel

theorem pow_three_or_of_mem_lam0 : ∀ ρ : Equiv.Perm (Fin 6), ρ ∈ lam0 →
    ρ ^ 3 = 1 ∨ (σS0⁻¹ * ρ) ^ 3 = 1 := by
  intro ρ h
  have hw := walkK_sound pow3or_walk ρ
  simp only [(mem_lam0_K ρ).1 h, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hw
  rcases hw with h3 | h3
  · exact Or.inl ((cube_iff ρ).1 h3)
  · rw [← enc_σS0_inv', ← enc_mul six_le] at h3
    exact Or.inr ((cube_iff _).1 h3)

end CFSG.Quasithin.HSType
