module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

public section

namespace CFSG

theorem commute_conj_of_apply_eq {G : Type*} [Group G] {β : MulAut G} {y : G} (h : β y = y) :
    Commute β (MulAut.conj y) := by
  rw [commute_iff_eq]
  ext r
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h]

theorem mulAut_conj_mul_inv {G : Type*} [Group G] (φ : MulAut G) (g : G) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem inv_mulAut_conj_mul {G : Type*} [Group G] (β : MulAut G) (ρ : G) :
    β⁻¹ * MulAut.conj ρ * β = MulAut.conj (β⁻¹ ρ) := by
  simpa using mulAut_conj_mul_inv β⁻¹ ρ

theorem mulAut_conj_ker {G : Type*} [Group G] :
    (MulAut.conj : G →* MulAut G).ker = Subgroup.center G := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hg x
    have h := congrArg (fun f : MulAut G => f x) hg
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * g = (g * x * g⁻¹) * g := by rw [h]
      _ = g * x := by group
  · intro hg
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← hg x]
    group

theorem mulAut_conj_injective {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, mulAut_conj_ker, hZ]

theorem range_conj_normal {G : Type*} [Group G] :
    (MulAut.conj : G →* MulAut G).range.Normal :=
  Subgroup.Normal.mk fun n hn φ => by
    obtain ⟨g, rfl⟩ := hn
    exact ⟨φ g, (mulAut_conj_mul_inv φ g).symm⟩

private theorem exists_mem_range_mul_pow {G : Type*} [Group G] {u f : MulAut G}
    (hu : u ∈ (MulAut.conj : G →* MulAut G).range) (j : ℕ) :
    ∃ d ∈ (MulAut.conj : G →* MulAut G).range, (u * f) ^ j = d * f ^ j := by
  let N := (MulAut.conj : G →* MulAut G).range
  have hN : N.Normal := range_conj_normal
  let q : MulAut G →* MulAut G ⧸ N := QuotientGroup.mk' N
  have huq : q u = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hu
  have hq : q ((u * f) ^ j) = q (f ^ j) := by
    rw [map_pow, map_mul, huq, one_mul, map_pow]
  refine ⟨(u * f) ^ j * (f ^ j)⁻¹, ?_, by group⟩
  change (u * f) ^ j * (f ^ j)⁻¹ ∈ N
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hq, mul_inv_cancel]

theorem exists_eq_conj_mul_pow_of_eq_mul {G : Type*} [Group G] {p n k : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) {a u f : MulAut G} (hu : u ∈ (MulAut.conj : G →* MulAut G).range)
    (ha : a ^ p ^ k = 1) (haeq : a = u * f) :
    ∃ (ρ : G) (j e : ℕ), n ∣ p ^ e * j ∧ a = MulAut.conj ρ * f ^ j := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have ha1 : a = 1 := by simpa using ha
    exact ⟨1, 0, 0, by simp, by rw [ha1]; simp⟩
  obtain ⟨e, n', hn'p, hn_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcop : Nat.Coprime n' (p ^ k) :=
    (hp.coprime_iff_not_dvd.mpr hn'p).symm.pow_right k
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (Nat.one_lt_pow hk0.ne' hp.one_lt)
  have haa : a = a ^ (n' * c) := by
    rw [pow_eq_pow_mod (n' * c) ha, hc, pow_one]
  obtain ⟨d, hd, hdf⟩ := exists_mem_range_mul_pow hu (n' * c)
  obtain ⟨ρ, hρ⟩ := hd
  refine ⟨ρ, n' * c, e, ?_, ?_⟩
  · rw [hn_eq]
    exact mul_dvd_mul_left _ (dvd_mul_right _ _)
  · rw [haa, haeq, hdf, ← hρ]

end CFSG

end
