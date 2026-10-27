module

public import CFSG.Quasithin.Background.F7TwoInvAltGen
public import CFSG.Quasithin.Background.F7TwoInvDefs

public section

namespace CFSG.Quasithin.F7Two

open Equiv Equiv.Perm

theorem isPGroup_zpowers_iff {G : Type*} [Group G] {p : ℕ} {g : G} :
    IsPGroup p ↥(Subgroup.zpowers g) ↔ ∃ k : ℕ, g ^ p ^ k = 1 := by
  refine ⟨fun hp => ?_, fun ⟨k, hk⟩ ⟨x, hx⟩ => ?_⟩
  · obtain ⟨k, hk⟩ := hp ⟨g, Subgroup.mem_zpowers g⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

theorem not_isPGroup_two_zpowers_of_pow_three {G : Type*} [Group G] {g : G} (h3 : g ^ 3 = 1)
    (h1 : g ≠ 1) : ¬ IsPGroup 2 ↥(Subgroup.zpowers g) := by
  rw [isPGroup_zpowers_iff]
  rintro ⟨k, hk⟩
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact h1 (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
    (orderOf_dvd_of_pow_eq_one hk)))

variable {α : Type*} [DecidableEq α]

section triCycle

variable {σ : Perm α} {a b d : α}

theorem triCycle_conj (σ : Perm α) (a b d : α) :
    σ * triCycle a b d * σ⁻¹ = triCycle (σ a) (σ b) (σ d) := by
  calc σ * (swap a b * swap b d) * σ⁻¹
      = (σ * swap a b * σ⁻¹) * (σ * swap b d * σ⁻¹) := by group
    _ = triCycle (σ a) (σ b) (σ d) := by rw [← swap_apply_apply, ← swap_apply_apply]; rfl

theorem triCycle_flip_mul (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    triCycle b a d * triCycle a b d = 1 := by
  ext x
  by_cases hxa : x = a
  · subst hxa
    rw [Perm.mul_apply, triCycle_apply_left hab had, triCycle_apply_left hab.symm hbd]
    rfl
  by_cases hxb : x = b
  · subst hxb
    rw [Perm.mul_apply, triCycle_apply_mid hbd had, triCycle_apply_right]
    rfl
  by_cases hxd : x = d
  · subst hxd
    rw [Perm.mul_apply, triCycle_apply_right, triCycle_apply_mid had hbd]
    rfl
  rw [Perm.mul_apply, triCycle_apply_of_ne hxa hxb hxd, triCycle_apply_of_ne hxb hxa hxd]
  rfl

theorem triCycle_pow_three [Fintype α] (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    triCycle a b d ^ 3 = 1 := by
  have h := pow_orderOf_eq_one (triCycle a b d)
  rwa [(triCycle_isThreeCycle hab hbd had).orderOf] at h

theorem triCycle_mem_invXi_fixed [Fintype α] (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d)
    (h1 : σ a = b) (h2 : σ b = a) (h3 : σ d = d) :
    triCycle a b d ∈ invXi (alternatingGroup α) σ := by
  refine ⟨triCycle_mem_alternatingGroup hab hbd had, ?_⟩
  have hc3 := triCycle_pow_three hab hbd had
  have hinv : σ * triCycle a b d * σ⁻¹ = (triCycle a b d)⁻¹ := by
    rw [triCycle_conj, h1, h2, h3, eq_inv_iff_mul_eq_one]
    exact triCycle_flip_mul hab hbd had
  have hg : σ * triCycle a b d * σ⁻¹ * (triCycle a b d)⁻¹ = triCycle a b d := by
    rw [hinv]
    calc (triCycle a b d)⁻¹ * (triCycle a b d)⁻¹
        = (triCycle a b d)⁻¹ * (triCycle a b d)⁻¹ * triCycle a b d ^ 3 := by rw [hc3, mul_one]
      _ = triCycle a b d := by group
  rw [hg]
  refine not_isPGroup_two_zpowers_of_pow_three hc3 fun h => hab ?_
  have := triCycle_apply_left hab had
  rwa [h, Perm.one_apply] at this

theorem triCycle_mem_invXi_disjoint [Fintype α] (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d)
    (hσ : ∀ x y, (x = a ∨ x = b ∨ x = d) → (y = a ∨ y = b ∨ y = d) → σ x ≠ y) :
    triCycle a b d ∈ invXi (alternatingGroup α) σ := by
  refine ⟨triCycle_mem_alternatingGroup hab hbd had, ?_⟩
  have hc3 := triCycle_pow_three hab hbd had
  have ha : a = a ∨ a = b ∨ a = d := Or.inl rfl
  have hb : b = a ∨ b = b ∨ b = d := Or.inr (Or.inl rfl)
  have hd : d = a ∨ d = b ∨ d = d := Or.inr (Or.inr rfl)
  have hdisj : Disjoint (σ * triCycle a b d * σ⁻¹) (triCycle a b d)⁻¹ := by
    refine Disjoint.inv_right fun x => ?_
    rw [triCycle_conj]
    by_cases hx : x = a ∨ x = b ∨ x = d
    · exact Or.inl (triCycle_apply_of_ne (hσ a x ha hx).symm (hσ b x hb hx).symm
        (hσ d x hd hx).symm)
    · push Not at hx
      exact Or.inr (triCycle_apply_of_ne hx.1 hx.2.1 hx.2.2)
  have hg3 : (σ * triCycle a b d * σ⁻¹ * (triCycle a b d)⁻¹) ^ 3 = 1 := by
    rw [hdisj.commute.mul_pow, conj_pow, hc3, inv_pow, hc3]
    simp
  refine not_isPGroup_two_zpowers_of_pow_three hg3 fun h => ?_
  have hca : (triCycle a b d)⁻¹ a = d := Perm.inv_eq_iff_eq.2 triCycle_apply_right.symm
  have hga : (σ * triCycle a b d * σ⁻¹ * (triCycle a b d)⁻¹) a = d := by
    rw [Perm.mul_apply, hca, triCycle_conj]
    exact triCycle_apply_of_ne (hσ a d ha hd).symm (hσ b d hb hd).symm (hσ d d hd hd).symm
  rw [h, Perm.one_apply] at hga
  exact had hga

end triCycle

end CFSG.Quasithin.F7Two
