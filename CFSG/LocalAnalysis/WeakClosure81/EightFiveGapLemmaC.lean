module

public import CFSG.Permutation.SymmetricCoxeter
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Permutation.SymmetricCoxeter Equiv Subgroup

section LemmaC

variable {Y : Type} [Group Y] [Finite Y] {n : ℕ} (ψ : Y →* Perm (Fin (n + 1)))

private theorem eq_one_of_sq_eq_one_of_odd_card {Z : Type} [Group Z] [Finite Z]
    (hodd : Odd (Nat.card Z)) {z : Z} (hz : z * z = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : z ^ Nat.card Z = 1 := pow_card_eq_one'
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hz
  rw [hk, pow_succ, pow_mul, hz2, one_pow, one_mul] at h1
  exact h1

theorem exists_involution_lift (hodd : Odd (Nat.card ψ.ker)) {σ : Perm (Fin (n + 1))}
    (hσ : σ * σ = 1) {a : Y} (ha : ψ a = σ) : ∃ s : Y, s * s = 1 ∧ ψ s = σ := by
  have haa : a * a ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, ha, hσ]
  have h1 : (⟨a * a, haa⟩ : ψ.ker) ^ Nat.card ψ.ker = 1 := pow_card_eq_one'
  have h2 : (a * a) ^ Nat.card ψ.ker = 1 := congrArg Subtype.val h1
  refine ⟨a ^ Nat.card ψ.ker, ?_, ?_⟩
  · rw [← pow_add, ← two_mul, pow_mul, pow_two, h2]
  · obtain ⟨k, hk⟩ := hodd
    have hσ2 : σ ^ 2 = 1 := by rw [pow_two]; exact hσ
    rw [map_pow, ha, hk, pow_succ, pow_mul, hσ2, one_pow, one_mul]

theorem pow_eq_one_of_mem_ker (hker : ψ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card ψ.ker))
    {s t : Y} (hs : s * s = 1) (ht : t * t = 1) {k : ℕ} (hk : (s * t) ^ k ∈ ψ.ker) :
    (s * t) ^ k = 1 := by
  have hc : s * (s * t) ^ k * s⁻¹ = ((s * t) ^ k)⁻¹ := by
    have hst : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
      have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
      rw [hs', mul_inv_rev, hs', inv_eq_of_mul_eq_one_right ht]
      calc s * (s * t) * s = (s * s) * t * s := by group
        _ = t * s := by rw [hs, one_mul]
    rw [← inv_pow, ← hst, ← conj_pow]
  have hz : (s * t) ^ k = ((s * t) ^ k)⁻¹ := by
    rw [← hc]
    exact ((Subgroup.mem_center_iff.1 (hker hk)) s).symm ▸ by simp
  have hzz : (⟨(s * t) ^ k, hk⟩ : ψ.ker) * ⟨(s * t) ^ k, hk⟩ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, OneMemClass.coe_one]
    nth_rewrite 1 [hz]
    exact inv_mul_cancel _
  exact congrArg Subtype.val (eq_one_of_sq_eq_one_of_odd_card hodd hzz)

private theorem braid_iff_pow_three {s t : Y} (hs : s * s = 1) (ht : t * t = 1) :
    s * t * s = t * s * t ↔ (s * t) ^ 3 = 1 := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hss : ∀ b : Y, s * (s * b) = b := fun b => by rw [← mul_assoc, hs, one_mul]
  have htt : ∀ b : Y, t * (t * b) = b := fun b => by rw [← mul_assoc, ht, one_mul]
  have e1 : (s * t) ^ 3 = (s * t * s) * (t * s * t) := by simp [pow_succ, mul_assoc]
  constructor
  · intro h
    rw [e1, h]
    simp only [mul_assoc, hss, htt, ht]
  · intro h
    rw [e1] at h
    calc s * t * s = (t * s * t)⁻¹ := eq_inv_of_mul_eq_one_left h
      _ = t * s * t := by simp only [mul_inv_rev, hs', ht', mul_assoc]

private theorem comm_iff_pow_two {s t : Y} (hs : s * s = 1) (ht : t * t = 1) :
    s * t = t * s ↔ (s * t) ^ 2 = 1 := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hss : ∀ b : Y, s * (s * b) = b := fun b => by rw [← mul_assoc, hs, one_mul]
  have htt : ∀ b : Y, t * (t * b) = b := fun b => by rw [← mul_assoc, ht, one_mul]
  have e1 : (s * t) ^ 2 = s * t * (s * t) := by rw [pow_two]
  constructor
  · intro h
    rw [e1]
    calc s * t * (s * t) = s * t * (t * s) := by rw [← h]
      _ = s * (t * t) * s := by simp only [mul_assoc]
      _ = 1 := by rw [ht, mul_one, hs]
  · intro h
    rw [e1] at h
    calc s * t = (s * t)⁻¹ := eq_inv_of_mul_eq_one_left h
      _ = t * s := by simp only [mul_inv_rev, hs', ht']

theorem exists_isCoxeterA_lift (hker : ψ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card ψ.ker))
    (hψ : Function.Surjective ψ) :
    ∃ x : ℕ → Y, IsCoxeterA n x ∧ ∀ i, i < n → ψ (x i) = adjSwap n i := by
  have hlift : ∀ i : ℕ, ∃ s : Y, i < n → s * s = 1 ∧ ψ s = adjSwap n i := by
    intro i
    by_cases hi : i < n
    · obtain ⟨a, ha⟩ := hψ (adjSwap n i)
      obtain ⟨s, hs, hψs⟩ :=
        exists_involution_lift ψ hodd ((isCoxeterA_adjSwap n).sq i hi) ha
      exact ⟨s, fun _ => ⟨hs, hψs⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose x hx using hlift
  refine ⟨x, ⟨fun i hi => (hx i hi).1, ?_, ?_⟩, fun i hi => (hx i hi).2⟩
  · intro i hi
    have hs : x i * x i = 1 := (hx i (by omega)).1
    have ht : x (i + 1) * x (i + 1) = 1 := (hx (i + 1) hi).1
    have hmem : (x i * x (i + 1)) ^ 3 ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, map_mul, (hx i (by omega)).2, (hx (i + 1) hi).2]
      exact (braid_iff_pow_three ((isCoxeterA_adjSwap n).sq i (by omega))
        ((isCoxeterA_adjSwap n).sq (i + 1) hi)).1 ((isCoxeterA_adjSwap n).braid i hi)
    exact (braid_iff_pow_three hs ht).2
      (pow_eq_one_of_mem_ker ψ hker hodd hs ht hmem)
  · intro i j hij hj
    have hs : x i * x i = 1 := (hx i (by omega)).1
    have ht : x j * x j = 1 := (hx j hj).1
    have hmem : (x i * x j) ^ 2 ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, map_mul, (hx i (by omega)).2, (hx j hj).2]
      exact (comm_iff_pow_two ((isCoxeterA_adjSwap n).sq i (by omega))
        ((isCoxeterA_adjSwap n).sq j hj)).1 ((isCoxeterA_adjSwap n).comm i j hij hj)
    exact (comm_iff_pow_two hs ht).2
      (pow_eq_one_of_mem_ker ψ hker hodd hs ht hmem)

theorem exists_section_of_central_odd (hker : ψ.ker ≤ Subgroup.center Y)
    (hodd : Odd (Nat.card ψ.ker)) (hψ : Function.Surjective ψ) :
    ∃ θ : Perm (Fin (n + 1)) →* Y, ∀ σ, ψ (θ σ) = σ := by
  obtain ⟨x, hx, hxψ⟩ := exists_isCoxeterA_lift ψ hker hodd hψ
  obtain ⟨θ, hθ⟩ := exists_hom_perm n x hx
  refine ⟨θ, fun σ => ?_⟩
  have h : ψ.comp θ = MonoidHom.id _ := by
    refine MonoidHom.eq_of_eqOn_dense (closure_adjSwap n) ?_
    rintro _ ⟨i, hi, rfl⟩
    simp [hθ i hi, hxψ i hi]
  exact DFunLike.congr_fun h σ

theorem ker_eq_bot_of_closure_involutions (hker : ψ.ker ≤ Subgroup.center Y)
    (hodd : Odd (Nat.card ψ.ker)) (hψ : Function.Surjective ψ)
    (hgen : Subgroup.closure {y : Y | y * y = 1} = ⊤) : ψ.ker = ⊥ := by
  obtain ⟨θ, hθ⟩ := exists_section_of_central_odd ψ hker hodd hψ
  have hinv : ∀ y : Y, y * y = 1 → y ∈ θ.range := by
    intro y hy
    have hσ : ψ y * ψ y = 1 := by rw [← map_mul, hy, map_one]
    have hθσ : θ (ψ y) * θ (ψ y) = 1 := by rw [← map_mul, hσ, map_one]
    have hzmem : y * (θ (ψ y))⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθ]
      simp
    have hc := Subgroup.mem_center_iff.1 (hker hzmem) (θ (ψ y))
    have hzz : (⟨y * (θ (ψ y))⁻¹, hzmem⟩ : ψ.ker) * ⟨y * (θ (ψ y))⁻¹, hzmem⟩ = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, OneMemClass.coe_one]
      have hθ' : (θ (ψ y))⁻¹ = θ (ψ y) := inv_eq_of_mul_eq_one_right hθσ
      rw [hθ'] at hc ⊢
      calc y * θ (ψ y) * (y * θ (ψ y)) = y * (θ (ψ y) * (y * θ (ψ y))) := by rw [mul_assoc]
        _ = y * (y * θ (ψ y) * θ (ψ y)) := by rw [hc]
        _ = 1 := by rw [mul_assoc, hθσ, mul_one, hy]
    have hz1 := congrArg Subtype.val (eq_one_of_sq_eq_one_of_odd_card hodd hzz)
    have : y = θ (ψ y) := by
      have h2 : y * (θ (ψ y))⁻¹ = 1 := hz1
      exact mul_inv_eq_one.1 h2
    exact ⟨ψ y, this.symm⟩
  have htop : θ.range = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    exact fun y hy => hinv y hy
  refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
  obtain ⟨τ, rfl⟩ : y ∈ θ.range := by rw [htop]; exact Subgroup.mem_top y
  have h1 : τ = 1 := by
    rw [← hθ τ]
    exact hy
  rw [h1, map_one]

end LemmaC

end CFSG.LocalAnalysis.WeakClosure81

end
