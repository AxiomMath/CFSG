module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.Background.Harris.R1.PermSeven

variable {α : Type} [Fintype α] [DecidableEq α]

lemma fixed_card_modEq {β : Type} [Fintype β] [DecidableEq β] {f : Equiv.Perm β} {p n : ℕ}
    [Fact p.Prime] (h : f ^ p ^ n = 1) :
    Fintype.card β ≡ Fintype.card {z // f z = z} [MOD p] := by
  have h1 : ⇑(f ^ p ^ n) = ⇑(1 : Equiv.Perm β) := congrArg _ h
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_one] at h1
  have h' : (show Function.End β from ⇑f) ^ p ^ n = 1 := h1
  have := Equiv.Perm.card_fixedPoints_modEq h'
  have e : Fintype.card {z // f z = z} = Fintype.card (Function.fixedPoints ⇑f) :=
    Fintype.card_congr (Equiv.refl _)
  rw [e]; exact this

lemma pow_apply_of_apply_eq {c : Equiv.Perm α} {x : α} (h : c x = x) (k : ℕ) :
    (c ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, h, ih]

lemma apply_eq_of_pow_apply_eq {c : Equiv.Perm α} (hc7 : c ^ 7 = 1) {x : α} {d : ℕ}
    (hd0 : 0 < d) (hd7 : d < 7) (hdx : (c ^ d) x = x) : c x = x := by
  have hmod : d ^ 6 % 7 = 1 := by
    interval_cases d <;> norm_num
  have h2 := pow_apply_of_apply_eq hdx (d ^ 5)
  rw [← pow_mul] at h2
  have e : d * d ^ 5 = d ^ 6 := by ring
  rw [e] at h2
  have hdiv : d ^ 6 = 7 * (d ^ 6 / 7) + 1 := by
    generalize d ^ 6 = N at hmod ⊢
    omega
  rw [hdiv, pow_add, pow_mul, hc7, one_pow, pow_one, one_mul] at h2
  exact h2

lemma pow_apply_inj {c : Equiv.Perm α} (hc7 : c ^ 7 = 1) {x : α} (hx : ¬ c x = x) {a b : ℕ}
    (ha : a < 7) (hb : b < 7) (hab : (c ^ a) x = (c ^ b) x) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hsplit : c ^ b = c ^ a * c ^ (b - a) := by
      rw [← pow_add]; congr 1; omega
    have h1 : (c ^ a) x = (c ^ a) ((c ^ (b - a)) x) := by
      rw [hab, hsplit, Equiv.Perm.mul_apply]
    have h2 : (c ^ (b - a)) x = x := ((c ^ a).injective h1).symm
    exact hx (apply_eq_of_pow_apply_eq hc7 (by omega) (by omega) h2)
  · have hsplit : c ^ a = c ^ b * c ^ (a - b) := by
      rw [← pow_add]; congr 1; omega
    have h1 : (c ^ b) x = (c ^ b) ((c ^ (a - b)) x) := by
      rw [← hab, hsplit, Equiv.Perm.mul_apply]
    have h2 : (c ^ (a - b)) x = x := ((c ^ b).injective h1).symm
    exact hx (apply_eq_of_pow_apply_eq hc7 (by omega) (by omega) h2)

lemma orbit_cover {c : Equiv.Perm α} (hc7 : c ^ 7 = 1) {x : α} (hx : ¬ c x = x)
    (hS : Fintype.card {z // ¬ c z = z} = 7) : ∀ z, ¬ c z = z → ∃ j : ℕ, (c ^ j) x = z := by
  have hcardS : (Finset.univ.filter (fun z => ¬ c z = z)).card = 7 := by
    rw [← Fintype.card_subtype]; exact hS
  have hcardO : (Finset.univ.image (fun j : Fin 7 => (c ^ (j : ℕ)) x)).card = 7 := by
    rw [Finset.card_image_of_injective _ (fun i j hij => Fin.ext
      (pow_apply_inj hc7 hx i.isLt j.isLt hij))]
    simp
  have hsub : Finset.univ.image (fun j : Fin 7 => (c ^ (j : ℕ)) x)
      ⊆ Finset.univ.filter (fun z => ¬ c z = z) := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨j, rfl⟩ := hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    have h1 : (c ^ (j : ℕ)) (c x) = (c ^ (j : ℕ)) x := by
      have := congrArg (fun g : Equiv.Perm α => g x) (((Commute.refl c).pow_right (j : ℕ)).eq)
      simp only [Equiv.Perm.mul_apply] at this
      rw [← this]; exact h
    exact hx ((c ^ (j : ℕ)).injective h1)
  have hfin : Finset.univ.image (fun j : Fin 7 => (c ^ (j : ℕ)) x)
      = Finset.univ.filter (fun z => ¬ c z = z) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardO, hcardS])
  intro z hz
  have hmem : z ∈ Finset.univ.image (fun j : Fin 7 => (c ^ (j : ℕ)) x) := by
    rw [hfin]; simp [hz]
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
  exact ⟨(j : ℕ), hj⟩

theorem eq_one_of_commute_seven_card (hα : Fintype.card α = 9) {c y : Equiv.Perm α}
    (hc : orderOf c = 7) {pt : α} (hcpt : c pt = pt) (hy : IsPGroup 2 (Subgroup.zpowers y))
    (hyc : y * c = c * y) (hypt : y pt = pt) : y = 1 := by
  have hc7 : c ^ 7 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hcne : c ≠ 1 := by
    intro h; rw [h, orderOf_one] at hc; norm_num at hc
  obtain ⟨x0, hx0⟩ : ∃ x, ¬ c x = x := by
    by_contra h
    push_neg at h
    exact hcne (Equiv.ext h)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Fintype.card α ≡ Fintype.card {z // c z = z} [MOD 7] :=
    fixed_card_modEq (p := 7) (n := 1) (by rw [pow_one]; exact hc7)
  have hFlt : Fintype.card {z // c z = z} < 9 := by
    rw [← hα]; exact Fintype.card_subtype_lt (p := fun z => c z = z) (x := x0) hx0
  have hFpos : 0 < Fintype.card {z // c z = z} := Fintype.card_pos_iff.mpr ⟨⟨pt, hcpt⟩⟩
  have hFix2 : Fintype.card {z // c z = z} = 2 := by
    unfold Nat.ModEq at hF; rw [hα] at hF; omega
  have hS : Fintype.card {z // ¬ c z = z} = 7 := by
    have := Fintype.card_subtype_compl (fun z => c z = z)
    rw [hα, hFix2] at this; omega
  obtain ⟨k, hk⟩ := hy ⟨y, Subgroup.mem_zpowers y⟩
  have hyk : y ^ 2 ^ k = 1 := by
    have h2 := congrArg Subtype.val hk
    simpa using h2
  have hcy : ∀ z, c (y z) = y (c z) := fun z => by
    have := congrArg (fun g : Equiv.Perm α => g z) hyc
    simp only [Equiv.Perm.mul_apply] at this
    exact this.symm
  have hf : ∀ z, ¬ c (y z) = y z ↔ ¬ c z = z := fun z => by
    rw [hcy]; exact y.injective.ne_iff
  have key : ∀ (n : ℕ) (z : {z // ¬ c z = z}),
      (((y.subtypePerm (p := fun z => ¬ c z = z) hf) ^ n) z : α) = (y ^ n) (z : α) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih,
        Equiv.Perm.subtypePerm_apply]
  have hysk : (y.subtypePerm (p := fun z => ¬ c z = z) hf) ^ 2 ^ k = 1 := by
    refine Equiv.ext fun z => Subtype.ext ?_
    rw [key, hyk]; simp
  have hodd := fixed_card_modEq (p := 2) (n := k) hysk
  have hFixY : 0 < Fintype.card {z // (y.subtypePerm (p := fun z => ¬ c z = z) hf) z = z} := by
    unfold Nat.ModEq at hodd; omega
  obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.mp hFixY
  have hxm : ¬ c w.1 = w.1 := w.2
  have hxy : y w.1 = w.1 := by
    have := congrArg Subtype.val hw
    simpa [Equiv.Perm.subtypePerm_apply] using this
  have hyz : ∀ j : ℕ, y ((c ^ j) w.1) = (c ^ j) w.1 := fun j => by
    have h := congrArg (fun g : Equiv.Perm α => g w.1) (((show Commute y c from hyc).pow_right j).eq)
    simp only [Equiv.Perm.mul_apply] at h
    rw [hxy] at h
    exact h
  have hmoved : ∀ z, ¬ c z = z → y z = z := by
    intro z hz
    obtain ⟨j, rfl⟩ := orbit_cover hc7 hxm hS z hz
    exact hyz j
  have hfix : ∀ z, c z = z → y z = z := by
    intro z hz
    by_contra hne
    have hyz' : c (y z) = y z := by rw [hcy, hz]
    by_cases hzp : z = pt
    · subst hzp; exact hne hypt
    · have hyp : y z ≠ pt := fun h => hzp (y.injective (h.trans hypt.symm))
      have h3 : 2 < Fintype.card {w // c w = w} :=
        Fintype.two_lt_card_iff.mpr ⟨⟨z, hz⟩, ⟨pt, hcpt⟩, ⟨y z, hyz'⟩,
          fun h => hzp (congrArg Subtype.val h),
          fun h => hne (congrArg Subtype.val h).symm,
          fun h => hyp (congrArg Subtype.val h).symm⟩
      omega
  refine Equiv.ext fun z => ?_
  show y z = z
  by_cases h : c z = z
  · exact hfix z h
  · exact hmoved z h

theorem eq_one_of_commute_seven_pow {α : Type} [Fintype α] (hα : Fintype.card α = 9)
    {c y : Equiv.Perm α} (hc : orderOf c = 7) {pt : α} (hcpt : c pt = pt) {n : ℕ}
    (hy : y ^ 2 ^ n = 1) (hyc : y * c = c * y) (hypt : y pt = pt) : y = 1 := by
  classical
  have hgrp : IsPGroup 2 (Subgroup.zpowers y) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hm, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hy, one_zpow]
  exact eq_one_of_commute_seven_card hα hc hcpt hgrp hyc hypt

end CFSG.Quasithin.Background.Harris.R1.PermSeven

end
