module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.S126P31

open Equiv

private theorem card_mulAut_alt5_abs3 :
    Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))), Nat.card_perm, Nat.card_fin]
  rfl

private theorem ker_conjNormal_eq_centralizer_abs3 {Y : Type*} [Group Y] (K : Subgroup Y)
    [K.Normal] :
    (MulAut.conjNormal (H := K)).ker = Subgroup.centralizer (K : Set Y) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hfix : MulAut.conjNormal x ⟨k, hk⟩ = ⟨k, hk⟩ := by
      have hfix' := congrArg (fun e : MulAut K => e ⟨k, hk⟩) hx
      rw [MulAut.one_apply] at hfix'
      exact hfix'
    have hconj : x * k * x⁻¹ = k :=
      (MulAut.conjNormal_apply x ⟨k, hk⟩).symm.trans (congrArg Subtype.val hfix)
    calc
      k * x = (x * k * x⁻¹) * x := by rw [hconj]
      _ = x * k := by simp [mul_assoc]
  · intro hx
    ext k
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hx' : (k : Y) * x = x * (k : Y) :=
      (Subgroup.mem_centralizer_iff.mp hx) (k : Y) k.2
    calc
      x * (k : Y) * x⁻¹ = ((k : Y) * x) * x⁻¹ := by rw [hx']
      _ = (k : Y) := by simp [mul_assoc]

theorem card_le_mul_centralizer_alt5 {Y : Type*} [Group Y] [Finite Y]
    (K : Subgroup Y) [K.Normal] (e : ↥K ≃* alternatingGroup (Fin 5)) :
    Nat.card Y ≤ 120 * Nat.card (Subgroup.centralizer (K : Set Y)) := by
  have hMA : Nat.card (MulAut K) = 120 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_alt5_abs3]
  haveI : Finite (MulAut K) := Nat.finite_of_card_ne_zero (by rw [hMA]; norm_num)
  have hrange : Nat.card (MulAut.conjNormal (H := K)).range ≤ 120 := by
    rw [← hMA]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hcard : Nat.card Y = Nat.card (MulAut.conjNormal (H := K)).ker *
      Nat.card (MulAut.conjNormal (H := K)).range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [ker_conjNormal_eq_centralizer_abs3 K] at hcard
  calc Nat.card Y = Nat.card (Subgroup.centralizer (K : Set Y)) *
        Nat.card (MulAut.conjNormal (H := K)).range := hcard
    _ ≤ Nat.card (Subgroup.centralizer (K : Set Y)) * 120 := Nat.mul_le_mul le_rfl hrange
    _ = 120 * Nat.card (Subgroup.centralizer (K : Set Y)) := Nat.mul_comm _ _

private theorem pow_thirty_alt5_abs3 : ∀ a : ↥(alternatingGroup (Fin 5)), a ^ 30 = 1 := by
  decide +kernel

theorem sq_eq_one_of_isPGroup_alt5 {Q : Type*} [Group Q] {X S : Subgroup Q}
    (e : ↥X ≃* alternatingGroup (Fin 5)) (hSX : S ≤ X) (hS : IsPGroup 2 S) :
    ∀ x ∈ S, x ^ 2 = 1 := by
  intro x hx
  obtain ⟨k, hk⟩ := hS ⟨x, hx⟩
  have hxk : (⟨x, hSX hx⟩ : ↥X) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  obtain ⟨j, -, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hxk)
  have h30 : (⟨x, hSX hx⟩ : ↥X) ^ 30 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact pow_thirty_alt5_abs3 _
  have hdvd : orderOf (⟨x, hSX hx⟩ : ↥X) ∣ 2 := by
    have h30' : orderOf (⟨x, hSX hx⟩ : ↥X) ∣ 30 := orderOf_dvd_of_pow_eq_one h30
    rw [hord] at h30' ⊢
    have hlt : j < 5 := by
      by_contra hcon
      have h32 : 32 ≤ 2 ^ j :=
        le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 5 ≤ j by omega))
      have hle : 2 ^ j ≤ 30 := Nat.le_of_dvd (by norm_num) h30'
      omega
    interval_cases j <;> first | decide | (revert h30'; decide)
  have h2 : (⟨x, hSX hx⟩ : ↥X) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd
  simpa using congrArg Subtype.val h2

theorem isPGroup_of_ker_range {A B : Type*} [Group A] [Group B] (f : A →* B) {p : ℕ}
    (hk : IsPGroup p f.ker) (hr : IsPGroup p f.range) : IsPGroup p A := by
  intro g
  obtain ⟨k, hk1⟩ := hr ⟨f g, MonoidHom.mem_range.2 ⟨g, rfl⟩⟩
  have hfk : g ^ p ^ k ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    simpa using congrArg Subtype.val hk1
  obtain ⟨j, hj⟩ := hk ⟨g ^ p ^ k, hfk⟩
  refine ⟨k + j, ?_⟩
  have h : (g ^ p ^ k) ^ p ^ j = 1 := by
    simpa using congrArg Subtype.val hj
  rw [pow_add, pow_mul]
  exact h

end CFSG.Quasithin.H13.S126P31
