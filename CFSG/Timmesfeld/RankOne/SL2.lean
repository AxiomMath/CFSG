module

public import CFSG.Timmesfeld.RankOne.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Timmesfeld.RankOne

variable (K : Type*) [Field K]

@[expose] def upperElt (t : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lowerElt (t : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

theorem upperElt_mul (s t : K) : upperElt K s * upperElt K t = upperElt K (s + t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [upperElt, add_comm]

theorem lowerElt_mul (s t : K) : lowerElt K s * lowerElt K t = lowerElt K (s + t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [lowerElt]

theorem upperElt_zero : upperElt K 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperElt]

theorem lowerElt_zero : lowerElt K 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerElt]

theorem upperElt_injective : Function.Injective (upperElt K) := by
  intro s t hst
  have := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) hst
  simpa [upperElt] using this

theorem lowerElt_injective : Function.Injective (lowerElt K) := by
  intro s t hst
  have := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 0) hst
  simpa [lowerElt] using this

theorem mem_upperUnipotent_iff {g : Matrix.SpecialLinearGroup (Fin 2) K} :
    g ∈ upperUnipotent K ↔ ∃ t : K, g = upperElt K t := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨t, ht⟩ := hx
      exact ⟨t, Subtype.ext ht⟩
    | one => exact ⟨0, (upperElt_zero K).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hy
      exact ⟨s + t, upperElt_mul K s t⟩
    | inv x _ hx =>
      obtain ⟨s, rfl⟩ := hx
      refine ⟨-s, ?_⟩
      rw [inv_eq_iff_mul_eq_one, upperElt_mul, add_neg_cancel, upperElt_zero]
  · rintro ⟨t, rfl⟩
    exact Subgroup.subset_closure ⟨t, rfl⟩

theorem mem_lowerUnipotent_iff {g : Matrix.SpecialLinearGroup (Fin 2) K} :
    g ∈ lowerUnipotent K ↔ ∃ t : K, g = lowerElt K t := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨t, ht⟩ := hx
      exact ⟨t, Subtype.ext ht⟩
    | one => exact ⟨0, (lowerElt_zero K).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hy
      exact ⟨s + t, lowerElt_mul K s t⟩
    | inv x _ hx =>
      obtain ⟨s, rfl⟩ := hx
      refine ⟨-s, ?_⟩
      rw [inv_eq_iff_mul_eq_one, lowerElt_mul, add_neg_cancel, lowerElt_zero]
  · rintro ⟨t, rfl⟩
    exact Subgroup.subset_closure ⟨t, rfl⟩

theorem card_upperUnipotent : Nat.card (upperUnipotent K) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun t : K => (⟨upperElt K t, (mem_upperUnipotent_iff K).2 ⟨t, rfl⟩⟩ : upperUnipotent K))
    ⟨fun s t hst => upperElt_injective K (congrArg Subtype.val hst), ?_⟩)).symm
  rintro ⟨g, hg⟩
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff K).1 hg
  exact ⟨t, rfl⟩

theorem card_lowerUnipotent : Nat.card (lowerUnipotent K) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun t : K => (⟨lowerElt K t, (mem_lowerUnipotent_iff K).2 ⟨t, rfl⟩⟩ : lowerUnipotent K))
    ⟨fun s t hst => lowerElt_injective K (congrArg Subtype.val hst), ?_⟩)).symm
  rintro ⟨g, hg⟩
  obtain ⟨t, rfl⟩ := (mem_lowerUnipotent_iff K).1 hg
  exact ⟨t, rfl⟩

theorem upperUnipotent_ne_lowerUnipotent : upperUnipotent K ≠ lowerUnipotent K := by
  intro heq
  have h1 : lowerElt K 1 ∈ upperUnipotent K := heq ▸ (mem_lowerUnipotent_iff K).2 ⟨1, rfl⟩
  obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff K).1 h1
  have := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 0) ht
  simp [lowerElt, upperElt] at this

theorem center_SL2_eq_bot [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr1 : r = 1 := by
    rw [Fintype.card_fin, pow_two] at hr
    rcases mul_self_eq_one_iff.1 hr with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  ext i j
  rw [← hrA, hr1]
  simp [Matrix.one_apply]

noncomputable def psl2EquivSL2 [CharP K 2] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientMulEquivOfEq (center_SL2_eq_bot K)).trans QuotientGroup.quotientBot

theorem card_psl2_four :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) = 60 := by
  let _ : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  rw [Nat.card_congr (psl2EquivSL2 (GaloisField 2 2)).toEquiv, Matrix.card_SL_field,
    Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]
  simp [Fin.prod_univ_two]

theorem isCyclic_sylow_psl2 {n : ℕ} (hn : 2 ≤ n) (r : ℕ) [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (R : Sylow r (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))) :
    IsCyclic R := by
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hcop : r.Coprime (Nat.card (GaloisField 2 n)) := by
    rw [hcard]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hr.out Nat.prime_two).2 hr2)
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  ·
    obtain rfl : n = 2 := by omega
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 R.isPGroup'
    have hdvd : r ^ k ∣ 60 := by
      rw [← hk, ← card_psl2_four]
      exact Subgroup.card_subgroup_dvd_card _
    rcases k with _ | _ | k
    · rw [pow_zero] at hk
      have : Subsingleton R := by rw [← Finite.card_le_one_iff_subsingleton, hk]
      infer_instance
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
    · exfalso
      have h2 : r ^ 2 ∣ 60 := (pow_dvd_pow r (by omega)).trans hdvd
      have hle : r ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) h2
      have hr8 : r < 8 := by nlinarith
      have hr' : r.Prime := hr.out
      interval_cases r <;> revert hr' hr2 h2 <;> norm_num
  · exact CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card
      (GaloisField 2 n) (p := 2) (f := n) hcard (by
        rw [hcard]
        calc 7 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3)
      r hr2 hcop R

end CFSG.Timmesfeld.RankOne
