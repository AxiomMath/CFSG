module

public import CFSG.LocalAnalysis.StandardType.GGResIClassify
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsBasic

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Shape

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

def ggEvenRefl (h : V) (α : Module.Dual (ZMod p) V) : V →ₗ[ZMod p] V :=
  LinearMap.id - α.smulRight h

theorem ggEvenRefl_apply (h : V) (α : Module.Dual (ZMod p) V) (v : V) :
    ggEvenRefl h α v = v - α v • h := by
  simp [ggEvenRefl, LinearMap.smulRight_apply]

theorem ggEvenRefl_involutive (_hp2 : p ≠ 2) {h : V} {α : Module.Dual (ZMod p) V}
    (hα : α h = 2) (v : V) : ggEvenRefl h α (ggEvenRefl h α v) = v := by
  simp only [ggEvenRefl_apply]
  rw [map_sub, map_smul, hα]
  rw [show α v - α v • 2 = -(α v) by rw [smul_eq_mul]; ring]
  rw [neg_smul]
  abel

theorem ggEvenRefl_self {h : V} {α : Module.Dual (ZMod p) V} (hα : α h = 2) :
    ggEvenRefl h α h = -h := by
  rw [ggEvenRefl_apply, hα, two_smul]
  abel

theorem ne_zero_of_pairing (hp2 : p ≠ 2) {h : V} {α : Module.Dual (ZMod p) V}
    (hα : α h = 2) : h ≠ 0 := by
  rintro rfl
  rw [map_zero] at hα
  exact zmod_two_ne_zero hp2 hα.symm

theorem basis_ne_zero {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V) (a : Fin k) :
    b a ≠ 0 := by
  intro h0
  have h1 := b.repr_self_apply a a
  rw [h0, map_zero] at h1
  simp at h1

theorem repr_sub_self_eq {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V)
    (r : V →ₗ[ZMod p] V) (σ : Equiv.Perm (Fin k)) (c : Fin k → ZMod p)
    (hform : ∀ a, r (b a) = c a • b (σ a)) (x : Fin k) :
    b.repr (r (b x) - b x) x = c x * (if σ x = x then 1 else 0) - 1 := by
  rw [hform x]
  simp [Finsupp.single_apply]

theorem repr_sum_smul {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V)
    (f : Fin k → ZMod p) (x : Fin k) :
    b.repr (∑ a, f a • b a) x = f x := by
  rw [map_sum]
  rw [Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single x]
  · rw [map_smul, Finsupp.smul_apply, b.repr_self_apply, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro y _ hyx
    rw [map_smul, Finsupp.smul_apply, b.repr_self_apply, ite_eq_right hyx, smul_zero]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

theorem perm_apply_apply {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V)
    {r : V →ₗ[ZMod p] V} (hr : ∀ v, r (r v) = v) {σ : Equiv.Perm (Fin k)}
    {c : Fin k → ZMod p} (hform : ∀ a, r (b a) = c a • b (σ a)) : ∀ a, σ (σ a) = a := by
  intro a
  have h := hr (b a)
  rw [hform a, map_smul, hform (σ a), smul_smul] at h
  by_contra hne
  have hc : (c a * c (σ a)) * (if σ (σ a) = a then 1 else 0) = 1 := by
    have h' := congrArg (fun v => b.repr v a) h
    rw [map_smul, Finsupp.smul_apply, b.repr_self_apply, smul_eq_mul, b.repr_self_apply,
      ite_eq_left rfl] at h'
    exact h'
  rw [ite_eq_right hne, mul_zero] at hc
  exact zero_ne_one hc

theorem perm_c_eq {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V)
    {r : V →ₗ[ZMod p] V} (hr : ∀ v, r (r v) = v) {σ : Equiv.Perm (Fin k)}
    {c : Fin k → ZMod p} (hc : ∀ a, c a = 1 ∨ c a = -1)
    (hform : ∀ a, r (b a) = c a • b (σ a)) : ∀ a, c (σ a) = c a := by
  intro a
  have h := hr (b a)
  rw [hform a, map_smul, hform (σ a), smul_smul, perm_apply_apply b hr hform a] at h
  have hc' : c a * c (σ a) = 1 := by
    have h' := congrArg (fun v => b.repr v a) h
    simpa [b.repr_self_apply] using h'
  have hca : c a ≠ 0 := by
    rcases hc a with h1 | h1
    · rw [h1]; exact one_ne_zero
    · rw [h1]; exact neg_ne_zero.mpr one_ne_zero
  have hs : c a * c a = 1 := by
    rcases hc a with h1 | h1 <;> rw [h1] <;> ring
  exact mul_left_cancel₀ hca (hc'.trans hs.symm)

theorem at_most_one_neg (hp2 : p ≠ 2) {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V)
    {r : V →ₗ[ZMod p] V} {c : Fin k → ZMod p} (hform : ∀ a, r (b a) = c a • b a)
    {h : V} {α : Module.Dual (ZMod p) V} (happly : ∀ v, r v = v - α v • h)
    {a a' : Fin k} (ha : c a = -1) (ha' : c a' = -1) (hne : a ≠ a') : False := by
  have hsplit : ∀ x, c x = -1 → -b x = b x - α (b x) • h := by
    intro x hx
    rw [← happly, hform x, hx, neg_one_smul]
  have h2 : ∀ x, c x = -1 → α (b x) • h = b x + b x := by
    intro x hx
    have h1 := hsplit x hx
    have h4 : b x + b x - α (b x) • h = 0 := by
      rw [add_sub_assoc, ← h1, add_neg_cancel]
    exact (sub_eq_zero.mp h4).symm
  have hαne : ∀ x, c x = -1 → α (b x) ≠ 0 := by
    intro x hx h0
    have h1 := hsplit x hx
    rw [h0, zero_smul, sub_zero] at h1
    have h2' : (2 : ZMod p) • b x = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h1.symm]
      rw [add_neg_cancel]
    rcases smul_eq_zero.mp h2' with h3 | h3
    · exact zmod_two_ne_zero hp2 h3
    · exact basis_ne_zero b x h3
  have hh : ∀ x, c x = -1 → h = ((α (b x))⁻¹ * 2) • b x := by
    intro x hx
    have h3 := congrArg (fun v => (α (b x))⁻¹ • v) (h2 x hx)
    rw [smul_add, smul_smul, inv_mul_cancel₀ (hαne x hx), one_smul, ← add_smul] at h3
    rwa [show (α (b x))⁻¹ + (α (b x))⁻¹ = (α (b x))⁻¹ * 2 by ring] at h3
  have heq : ((α (b a))⁻¹ * 2) • b a = ((α (b a'))⁻¹ * 2) • b a' :=
    (hh a ha).symm.trans (hh a' ha')
  have hcontr := congrArg (fun v => b.repr v a) heq
  rw [map_smul, Finsupp.smul_apply, b.repr_self_apply, ite_eq_left rfl, smul_eq_mul, mul_one,
    map_smul, Finsupp.smul_apply, b.repr_self_apply, ite_eq_right (Ne.symm hne),
    smul_zero] at hcontr
  exact (mul_ne_zero (inv_ne_zero (hαne a ha)) (zmod_two_ne_zero hp2)) hcontr

theorem exists_neg_coeff {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V)
    {r : V →ₗ[ZMod p] V} {c : Fin k → ZMod p} (hform : ∀ a, r (b a) = c a • b a) {h : V}
    (hrh : r h = -h) (hne : h ≠ 0) : ∃ a, c a = -1 := by
  classical
  have hsum : h = ∑ a, b.repr h a • b a := (b.sum_repr h).symm
  have hneg : -h = ∑ a, (b.repr h a * c a) • b a := by
    conv_lhs => rw [← hrh, hsum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hform a, smul_smul]
  have hcoef : ∀ x, b.repr h x * c x = -(b.repr h x) := by
    intro x
    have h1 : b.repr (-h) x = b.repr h x * c x := by
      rw [hneg, repr_sum_smul]
    rw [map_neg, Finsupp.neg_apply] at h1
    exact h1.symm
  have hex : ∃ x, b.repr h x ≠ 0 := by
    by_contra h'
    push Not at h'
    apply hne
    rw [hsum]
    simp [h']
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, ?_⟩
  have hcx := hcoef x
  exact mul_left_cancel₀ hx (hcx.trans (by ring))

theorem perm_ne_one (hp2 : p ≠ 2) {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V)
    {r : V →ₗ[ZMod p] V} {σ : Equiv.Perm (Fin k)} {c : Fin k → ZMod p}
    (hc : ∀ a, c a = 1 ∨ c a = -1) (hprod : ∏ a, c a = 1)
    (hform : ∀ a, r (b a) = c a • b (σ a)) {h : V} {α : Module.Dual (ZMod p) V}
    (happly : ∀ v, r v = v - α v • h) (hrh : r h = -h) (hne : h ≠ 0) :
    ∃ a, σ a ≠ a := by
  by_contra h
  push Not at h
  have hform' : ∀ a, r (b a) = c a • b a := fun a => by simpa [h a] using hform a
  obtain ⟨x, hx⟩ := exists_neg_coeff b hform' hrh hne
  have hother : ∀ a, a ≠ x → c a = 1 := by
    intro a hax
    rcases hc a with h1 | h1
    · exact h1
    · exact (at_most_one_neg hp2 b hform' happly h1 hx hax).elim
  have hsplit := Finset.mul_prod_erase Finset.univ c (Finset.mem_univ x)
  rw [hprod] at hsplit
  rw [hx, Finset.prod_eq_one (fun a ha => hother a (Finset.ne_of_mem_erase ha)),
    mul_one] at hsplit
  exact (zmod_two_ne_zero hp2) (by linear_combination -hsplit)

theorem perm_shape {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V)
    {r : V →ₗ[ZMod p] V} {σ : Equiv.Perm (Fin k)} {c : Fin k → ZMod p}
    (hform : ∀ a, r (b a) = c a • b (σ a)) {h : V} {α : Module.Dual (ZMod p) V}
    (happly : ∀ v, r v = v - α v • h) (hr : ∀ v, r (r v) = v)
    (hc : ∀ a, c a = 1 ∨ c a = -1) {a d : Fin k} (had : a ≠ d) (hσa : σ a = d) :
    (∀ x, x ≠ a → x ≠ d → σ x = x ∧ c x = 1) ∧
      h = (α (b a))⁻¹ • (b a - c a • b d) ∧
      α (b d) = α (b a) * (-(c a)) := by
  have hσ2 : ∀ y, σ (σ y) = y := perm_apply_apply b hr hform
  have hσd : σ d = a := by rw [← hσa]; exact hσ2 a
  have hcd : c d = c a := by
    have h' := perm_c_eq b hr hc hform a
    rwa [hσa] at h'
  have hαa : α (b a) ≠ 0 := by
    intro h0
    have h1 : c a • b d = b a := by
      have h' := hform a
      rw [hσa, happly, h0, zero_smul, sub_zero] at h'
      exact h'.symm
    have h2 := congrArg (fun v => b.repr v d) h1
    rw [map_smul, Finsupp.smul_apply, b.repr_self_apply, ite_eq_left rfl, smul_eq_mul, mul_one,
      b.repr_self_apply, ite_eq_right had] at h2
    rcases hc a with h3 | h3 <;> rw [h3] at h2 <;> simp at h2
  have hseq : h = (α (b a))⁻¹ • (b a - c a • b d) := by
    have h1 : c a • b d = b a - α (b a) • h := by
      rw [← hσa, ← hform a, happly]
    have h2 : α (b a) • h = b a - c a • b d := by rw [h1]; abel
    have h3 := congrArg (fun v => (α (b a))⁻¹ • v) h2
    simpa [smul_smul, inv_mul_cancel₀ hαa] using h3
  have hαd : α (b d) = α (b a) * (-(c a)) := by
    have h1 : c a • b a = b d - α (b d) • h := by
      rw [← hcd, ← hσd, ← hform d, happly]
    have h2 : α (b d) • h = b d - c a • b a := by rw [h1]; abel
    have h3 : (α (b d) * (α (b a))⁻¹) • (b a - c a • b d) = b d - c a • b a := by
      rw [← h2, hseq, smul_smul]
    have hwa : b.repr (b a - c a • b d) a = 1 := by
      simp [map_sub, map_smul, had]
    have h4 : α (b d) * (α (b a))⁻¹ = -(c a) := by
      have h4' := congrArg (fun v => b.repr v a) h3
      simpa [map_sub, map_smul, b.repr_self_apply, had, hwa] using h4'
    calc α (b d) = (α (b d) * (α (b a))⁻¹) * (α (b a)) := by
          rw [mul_assoc, inv_mul_cancel₀ hαa, mul_one]
      _ = (-(c a)) * (α (b a)) := by rw [h4]
      _ = α (b a) * (-(c a)) := by ring
  refine ⟨?_, hseq, hαd⟩
  intro x hxa hxd
  have hw : b.repr (b a - c a • b d) x = 0 := by
    simp [map_sub, map_smul, Ne.symm hxa, Ne.symm hxd]
  have hhx : b.repr h x = 0 := by
    rw [hseq, map_smul, Finsupp.smul_apply, hw, smul_zero]
  have hx0 : b.repr (r (b x) - b x) x = 0 := by
    have h1 : r (b x) - b x = -(α (b x)) • h := by rw [happly, neg_smul]; abel
    rw [h1, map_smul, Finsupp.smul_apply, hhx, smul_zero]
  have hx1 := repr_sub_self_eq b r σ c hform x
  rw [hx1] at hx0
  by_cases hσx : σ x = x
  · rw [hσx, ite_eq_left rfl] at hx0
    have hcx : c x = 1 := by
      have := sub_eq_zero.mp hx0
      simpa using this
    exact ⟨hσx, hcx⟩
  · rw [ite_eq_right hσx] at hx0
    simp only [mul_zero, zero_sub] at hx0
    exact absurd hx0 (neg_ne_zero.mpr one_ne_zero)

theorem exists_dRoot_shape (hp2 : p ≠ 2) {k : ℕ}
    (b : Module.Basis (Fin k) (ZMod p) V) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hrD : ∀ i, ∃ (σ : Equiv.Perm (Fin k)) (c : Fin k → ZMod p),
      (∀ a, c a = 1 ∨ c a = -1) ∧ ∏ a, c a = 1 ∧
        ∀ a, b a - α i (b a) • h i = c a • b (σ a)) (i : Λ) :
    ∃ (ρ : Fin k → ℤ) (lam : ZMod p), lam ≠ 0 ∧ ρ ∈ ggDRootSet k ∧
      h i = lam • ∑ a, ((ρ a : ℤ) : ZMod p) • b a ∧
      (∀ v, α i v = lam⁻¹ * ∑ a, ((ρ a : ℤ) : ZMod p) * b.repr v a) := by
  classical
  obtain ⟨σ, c, hc, hprod, hform0⟩ := hrD i
  let r : V →ₗ[ZMod p] V := ggEvenRefl (h i) (α i)
  have happly : ∀ v, r v = v - α i v • h i := fun v => ggEvenRefl_apply _ _ _
  have hii : α i (h i) = 2 := by
    have h' := hpair i i
    rwa [hC.1 i, Int.cast_ofNat] at h'
  have hne : h i ≠ 0 := ne_zero_of_pairing hp2 hii
  have hr2 : ∀ v, r (r v) = v := ggEvenRefl_involutive hp2 hii
  have hrneg : r (h i) = -h i := ggEvenRefl_self hii
  have hform : ∀ a, r (b a) = c a • b (σ a) := by
    intro a
    rw [happly]
    exact hform0 a
  obtain ⟨a, ha⟩ := perm_ne_one hp2 b hc hprod hform happly hrneg hne
  let d : Fin k := σ a
  have hd : d = σ a := rfl
  have had : a ≠ d := by
    intro h'
    exact ha (by rw [← hd]; exact h'.symm)
  obtain ⟨hfix, hseq, hαd⟩ := perm_shape b hform happly hr2 hc had hd.symm
  let εZ : ℤ := if c a = 1 then 1 else -1
  have hεZcast : ((εZ : ℤ) : ZMod p) = c a := by
    rw [show εZ = if c a = 1 then (1 : ℤ) else -1 from rfl]
    split_ifs with h1
    · rw [h1]; norm_num
    · have h2 : c a = -1 := by
        rcases hc a with h3 | h3
        · exact absurd h3 h1
        · exact h3
      rw [h2]; norm_num
  have hεZpm : εZ = 1 ∨ εZ = -1 := by
    rw [show εZ = if c a = 1 then (1 : ℤ) else -1 from rfl]
    split_ifs <;> simp
  let ρ : Fin k → ℤ := Pi.single a 1 + Pi.single d (-εZ)
  have hαane : α i (b a) ≠ 0 := by
    intro h0
    have hEq : h i = 0 := by rw [hseq, h0]; simp
    exact hne hEq
  have hlamne : (α i (b a))⁻¹ ≠ 0 := inv_ne_zero hαane
  have hρa : ((ρ a : ℤ) : ZMod p) = 1 := by
    simp [ρ, had]
  have hρd : ((ρ d : ℤ) : ZMod p) = -c a := by
    have h' : ρ d = -εZ := by simp [ρ, Ne.symm had]
    rw [h', Int.cast_neg, hεZcast]
  have hρx : ∀ x, x ≠ a → x ≠ d → ((ρ x : ℤ) : ZMod p) = 0 := by
    intro x hxa hxd
    have h' : ρ x = 0 := by simp [ρ, hxa, hxd]
    rw [h']; norm_num
  have hsum : ∑ x, ((ρ x : ℤ) : ZMod p) • b x = b a - c a • b d := by
    rw [← b.sum_repr (b a - c a • b d)]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    by_cases hxa : x = a
    · subst hxa
      simp [hρa, map_sub, map_smul, had]
    · by_cases hxd : x = d
      · subst hxd
        simp [hρd, map_sub, map_smul, had]
      · simp [hρx x hxa hxd, map_sub, map_smul, Ne.symm hxa, Ne.symm hxd]
  have hαbasis : ∀ x, α i (b x) = ((α i (b a))⁻¹)⁻¹ * ((ρ x : ℤ) : ZMod p) := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      rw [hρa, mul_one, inv_inv]
    · by_cases hxd : x = d
      · subst hxd
        rw [hρd, hαd, inv_inv]
      · obtain ⟨hσx, hcx⟩ := hfix x hxa hxd
        have hrx : r (b x) = b x := by rw [hform x, hσx, hcx, one_smul]
        have h0 : α i (b x) • h i = 0 := by
          have h' := hrx
          rw [happly] at h'
          exact sub_eq_self.mp h'
        have hαx : α i (b x) = 0 := by
          rcases smul_eq_zero.mp h0 with h' | h'
          · exact h'
          · exact absurd h' hne
        rw [hαx, hρx x hxa hxd, mul_zero]
  refine ⟨ρ, (α i (b a))⁻¹, hlamne, ?_, ?_, ?_⟩
  · refine ⟨a, d, 1, -εZ, had, Or.inl rfl, ?_, rfl⟩
    rcases hεZpm with h' | h' <;> rw [h'] <;> norm_num
  · rw [hsum, hseq]
  · intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_eq_mul, hαbasis x]
    ring

end Shape

theorem three_le_of_prime_ne_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : 3 ≤ p := by
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hlt : 2 < p := lt_of_le_of_ne h2 (Ne.symm hp2)
  omega

theorem neg_one_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by
    have h' : (1 : ZMod p) + (-1) = 0 := by ring
    rw [h] at h'
    rw [show (2 : ZMod p) = 1 + 1 by norm_num]
    exact h'
  exact zmod_two_ne_zero hp2 h2

theorem intCast_ne_zero_of_neg_small {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a : ℤ}
    (h1 : -2 ≤ a) (h2 : a < 0) : (a : ZMod p) ≠ 0 := by
  intro h
  have hdvd : (p : ℤ) ∣ a := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h
  have hp3 : (3 : ℤ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp2
  have habs : |a| < p := by
    rw [abs_lt]
    constructor <;> omega
  have hzero := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

theorem ggDRootSet_neg_mem {k : ℕ} {γ : Fin k → ℤ} (h : γ ∈ ggDRootSet k) :
    -γ ∈ ggDRootSet k := by
  obtain ⟨a, b, s, t, hab, hs, ht, rfl⟩ := h
  refine ⟨a, b, -s, -t, hab, ?_, ?_, ?_⟩
  · rcases hs with rfl | rfl <;> norm_num
  · rcases ht with rfl | rfl <;> norm_num
  · funext x
    simp only [Pi.neg_apply, Pi.add_apply, Pi.single_apply]
    split_ifs <;> ring

theorem ggDDot_bounds {k : ℕ} {γ δ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (hδ : δ ∈ ggDRootSet k) : -2 ≤ ggDDot γ δ ∧ ggDDot γ δ ≤ 2 := by
  obtain ⟨a, b, hab, ha, hb⟩ := ggDRootSet_exists_pair hγ
  rw [ggDRootSet_dot_eq hγ hab ha hb]
  have hsa : γ a = 1 ∨ γ a = -1 := ggDRootSet_sign hγ ha
  have hsb : γ b = 1 ∨ γ b = -1 := ggDRootSet_sign hγ hb
  have hda : δ a = 0 ∨ δ a = 1 ∨ δ a = -1 := ggDRootSet_apply hδ a
  have hdb : δ b = 0 ∨ δ b = 1 ∨ δ b = -1 := ggDRootSet_apply hδ b
  rcases hsa with hsa | hsa <;> rcases hsb with hsb | hsb <;>
    rcases hda with hda | hda | hda <;> rcases hdb with hdb | hdb | hdb <;>
    rw [hsa, hsb, hda, hdb] <;> norm_num

theorem ggDDot_self_eq_zero {k : ℕ} {u : Fin k → ℤ} (h : ggDDot u u = 0) : u = 0 := by
  funext x
  have hsum : ∑ y, u y * u y = 0 := h
  have hterm : ∀ y ∈ Finset.univ, u y * u y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => mul_self_nonneg (u y))).mp hsum
  exact mul_self_eq_zero.mp (hterm x (Finset.mem_univ x))

theorem ggDDot_eq_two_of_mem {k : ℕ} {γ δ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (hδ : δ ∈ ggDRootSet k) (h : ggDDot γ δ = 2) : δ = γ := by
  have h1 : ggDDot (γ - δ) (γ - δ) = 0 := by
    rw [ggDDot_eq_dotProduct, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_comm δ γ, ← ggDDot_eq_dotProduct, ← ggDDot_eq_dotProduct,
      ← ggDDot_eq_dotProduct, h, ggDDot_self_of_mem hγ, ggDDot_self_of_mem hδ]
    norm_num
  have hsub : γ - δ = 0 := ggDDot_self_eq_zero h1
  exact (sub_eq_zero.mp hsub).symm

theorem ggDDot_eq_neg_two_of_mem {k : ℕ} {γ δ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (hδ : δ ∈ ggDRootSet k) (h : ggDDot γ δ = -2) : δ = -γ := by
  have h2 : ggDDot γ (-δ) = 2 := by
    rw [ggDDot_eq_dotProduct] at h ⊢
    rw [dotProduct_neg, h]
    ring
  have h3 := ggDDot_eq_two_of_mem hγ (ggDRootSet_neg_mem hδ) h2
  have := congrArg (fun v : Fin k → ℤ => -v) h3
  simpa using this

theorem not_label_four_six {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : ℤ} (hG0 : G ≠ 0)
    (h1 : -2 ≤ G) (h2 : G ≤ 2) (hG : ((G : ZMod p)) ^ 2 = 2 ∨ ((G : ZMod p)) ^ 2 = 3) :
    False := by
  have hcases : G = -2 ∨ G = -1 ∨ G = 1 ∨ G = 2 := by omega
  have hp3 : 3 ≤ p := three_le_of_prime_ne_two hp2
  have h12 : (1 : ZMod p) ≠ 2 := by
    intro h
    have h' : (1 : ZMod p) = 0 := by
      have h2 : (2 : ZMod p) - 1 = 0 := by rw [h]; ring
      rw [show (2 : ZMod p) - 1 = 1 by ring] at h2
      exact h2
    exact one_ne_zero h'
  have h13 : (1 : ZMod p) ≠ 3 := by
    intro h
    have h' : (2 : ZMod p) = 0 := by
      have h2 : (3 : ZMod p) - 1 = 0 := by rw [← h]; ring
      rw [show (3 : ZMod p) - 1 = 2 by ring] at h2
      exact h2
    exact zmod_two_ne_zero hp2 h'
  have h42 : (4 : ZMod p) ≠ 2 := by
    intro h
    have h' : (2 : ZMod p) = 0 := by
      have h2 : (4 : ZMod p) - 2 = 0 := by rw [h]; ring
      rw [show (4 : ZMod p) - 2 = 2 by ring] at h2
      exact h2
    exact zmod_two_ne_zero hp2 h'
  have h43 : (4 : ZMod p) ≠ 3 := by
    intro h
    have h' : (1 : ZMod p) = 0 := by
      have h2 : (4 : ZMod p) - 3 = 0 := by rw [h]; ring
      rw [show (4 : ZMod p) - 3 = 1 by ring] at h2
      exact h2
    exact one_ne_zero h'
  have hsq : ((G : ZMod p)) ^ 2 = 1 ∨ ((G : ZMod p)) ^ 2 = 4 := by
    rcases hcases with rfl | rfl | rfl | rfl
    · right; rw [← Int.cast_pow]; norm_num
    · left; rw [← Int.cast_pow]; norm_num
    · left; rw [← Int.cast_pow]; norm_num
    · right; rw [← Int.cast_pow]; norm_num
  rcases hG with h | h <;> rcases hsq with hq | hq <;> rw [hq] at h
  · exact h12 h
  · exact h42 h
  · exact h13 h
  · exact h43 h

theorem int_eq_of_zero_or_neg_one {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (ha : a = 0 ∨ a = -1) (hb : b = 0 ∨ b = -1) (h : (a : ZMod p) = (b : ZMod p)) :
    a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exfalso
    have hcast : (((-1 : ℤ) : ZMod p)) = (-1 : ZMod p) := by push_cast; ring
    rw [hcast] at h
    have h' : (-1 : ZMod p) = ((0 : ℤ) : ZMod p) := h.symm
    rw [Int.cast_zero] at h'
    exact (neg_ne_zero.mpr one_ne_zero) h'
  · exfalso
    have hcast : (((-1 : ℤ) : ZMod p)) = (-1 : ZMod p) := by push_cast; ring
    rw [hcast] at h
    have h' : (-1 : ZMod p) = ((0 : ℤ) : ZMod p) := h
    rw [Int.cast_zero] at h'
    exact (neg_ne_zero.mpr one_ne_zero) h'
  · rfl

theorem int_eq_of_bounds_cast_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b : ℤ}
    (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hb : b = 0 ∨ b = -1) (h : (a : ZMod p) = (b : ZMod p)) :
    a = b := by
  have hp3 : (3 : ℤ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp2
  rcases hb with rfl | rfl
  · have hdvd : (p : ℤ) ∣ a := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [Int.cast_zero] at h
      exact h
    have hz := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
    omega
  · have hdvd : (p : ℤ) ∣ a + 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hcast : ((a + 1 : ℤ) : ZMod p) = (a : ZMod p) + 1 := by
        rw [Int.cast_add, Int.cast_one]
      rw [hcast, h]
      have hneg : (((-1 : ℤ) : ZMod p)) = (-1 : ZMod p) := by push_cast; ring
      rw [hneg]
      ring
    have hz := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
    omega

theorem reflTransGen_forward {α : Type} {r : α → α → Prop} {P : α → Prop} {a b : α}
    (ha : P a) (hclosed : ∀ u v, P u → r u v → P v)
    (h : Relation.ReflTransGen r a b) : P b := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hclosed _ _ ih hbc

theorem zmod3_mul_eq {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {u : ZMod p} {s : ℤ}
    (hs : s = 1 ∨ s = -1) (h : (-1 : ZMod p) = u * ((2 : ZMod p) * (s : ZMod p))) :
    u = (s : ZMod p) := by
  subst hp3
  rcases hs with rfl | rfl
  · have h' : u = 1 := by
      have h2 : (2 : ZMod 3) * 2 = 1 := by decide +revert
      have h4 : (-1 : ZMod 3) * 2 = 1 := by decide +revert
      have hu : u * 2 = -1 := by simpa using h.symm
      calc u = u * 1 := (mul_one u).symm
        _ = u * ((2 : ZMod 3) * 2) := by rw [h2]
        _ = (u * 2) * 2 := by ring
        _ = (-1 : ZMod 3) * 2 := by rw [hu]
        _ = 1 := h4
    exact h'
  · have h' : u = -1 := by
      have h2 : (2 : ZMod 3) * (-1) = 1 := by decide +revert
      have hu : u * ((2 : ZMod 3) * (-1)) = -1 := h.symm
      calc u = u * 1 := (mul_one u).symm
        _ = u * ((2 : ZMod 3) * (-1)) := by rw [h2]
        _ = -1 := hu
    have hcast : (((-1 : ℤ) : ZMod 3)) = (-1 : ZMod 3) := by push_cast; ring
    rw [hcast]
    exact h'

theorem ggEdge_pm_two_false {p : ℕ} [Fact p.Prime] {k : ℕ} {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M C) (rho : Λ → Fin k → ℤ) (lam : Λ → ZMod p)
    (hlamne : ∀ i, lam i ≠ 0) (hmem : ∀ i, rho i ∈ ggDRootSet k)
    (hcongr : ∀ i j, (C i j : ZMod p) =
      (lam i)⁻¹ * lam j * (ggDDot (rho i) (rho j) : ZMod p))
    (hlabel : ∀ i j, i ≠ j → (C i j = 0 ∧ M i j = 2) ∨ (C i j = -1 ∧ M i j = 3))
    (hp3 : p = 3) (hΛ : 3 ≤ Fintype.card Λ) {i j : Λ} (hij : i ≠ j) (hMij : M i j = 3)
    (hG : ggDDot (rho i) (rho j) = 2 ∨ ggDDot (rho i) (rho j) = -2) : False := by
  have hCij : C i j = -1 := by
    rcases hlabel i j hij with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact absurd h2 (by rw [hMij]; norm_num)
    · exact h1
  have hCji : C j i = -1 := by
    rcases hlabel j i hij.symm with ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [M.symmetric j i] at h2
      rw [hMij] at h2
      norm_num at h2
    · exact h1
  let s : ℤ := if ggDDot (rho i) (rho j) = 2 then 1 else -1
  have hs1 : ggDDot (rho i) (rho j) = 2 → s = 1 := by
    intro h
    rw [show s = if ggDDot (rho i) (rho j) = 2 then (1 : ℤ) else -1 from rfl]
    exact ite_eq_left h
  have hs2 : ggDDot (rho i) (rho j) ≠ 2 → s = -1 := by
    intro h
    rw [show s = if ggDDot (rho i) (rho j) = 2 then (1 : ℤ) else -1 from rfl]
    exact ite_eq_right h
  have hsval : s = 1 ∨ s = -1 := by
    rcases hG with h | h
    · exact Or.inl (hs1 h)
    · exact Or.inr (hs2 (by rw [h]; norm_num))
  have hrhoj : rho j = s • rho i := by
    rcases hG with h | h
    · rw [hs1 h]
      have h2 := ggDDot_eq_two_of_mem (hmem i) (hmem j) h
      rw [h2, one_smul]
    · rw [hs2 (by rw [h]; norm_num)]
      have h2 := ggDDot_eq_neg_two_of_mem (hmem i) (hmem j) h
      rw [h2, neg_one_smul]
  have hG2s : ggDDot (rho i) (rho j) = 2 * s := by
    rcases hG with h | h
    · rw [hs1 h, h]; norm_num
    · rw [hs2 (by rw [h]; norm_num), h]; norm_num
  have hu : (lam i)⁻¹ * lam j = s := by
    have hc := hcongr i j
    rw [hCij, hG2s] at hc
    push_cast at hc
    exact zmod3_mul_eq hp3 hsval hc
  have hlamj : lam j = s * lam i := by
    have h := congrArg (fun x => x * lam i) hu
    rw [mul_assoc, mul_comm (lam j) (lam i), ← mul_assoc, inv_mul_cancel₀ (hlamne i),
      one_mul] at h
    exact h
  have hs2' : (s : ZMod p) * (s : ZMod p) = 1 := by
    rcases hsval with h | h <;> rw [h] <;> ring
  have hsame : ∀ l, l ≠ i → l ≠ j → C l i = C l j := by
    intro l hli hlj
    have hGli : (ggDDot (rho l) (rho j) : ZMod p)
        = (s : ZMod p) * (ggDDot (rho l) (rho i) : ZMod p) := by
      have h1 : ggDDot (rho l) (rho j) = s * ggDDot (rho l) (rho i) := by
        rw [hrhoj]
        simp only [ggDDot, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      rw [h1]
      push_cast
      ring
    have hcast : (C l i : ZMod p) = (C l j : ZMod p) := by
      have h1 : (lam l)⁻¹ * lam j = (s : ZMod p) * ((lam l)⁻¹ * lam i) := by
        rw [hlamj]
        ring
      rw [hcongr l i, hcongr l j, h1, hGli]
      rw [show ((s : ZMod p) * ((lam l)⁻¹ * lam i)) *
          ((s : ZMod p) * (ggDDot (rho l) (rho i) : ZMod p)) =
          (lam l)⁻¹ * lam i * (ggDDot (rho l) (rho i) : ZMod p) * ((s : ZMod p) * s) by ring]
      rw [hs2']
      ring
    have hCi : C l i = 0 ∨ C l i = -1 := by
      rcases hlabel l i hli with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    have hCj : C l j = 0 ∨ C l j = -1 := by
      rcases hlabel l j hlj with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    exact int_eq_of_zero_or_neg_one hCi hCj hcast
  have hCneg_symm : ∀ u v, u ≠ v → C u v = -1 → C v u = -1 := by
    intro u v huv h
    have hMuv : M u v = 3 := by
      rcases hlabel u v huv with ⟨h0, -⟩ | ⟨-, h3⟩
      · exact absurd h0 (by rw [h]; norm_num)
      · exact h3
    rcases hlabel v u huv.symm with ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [M.symmetric v u] at h2
      rw [hMuv] at h2
      norm_num at h2
    · exact h1
  have htri : ∀ l, l ≠ i → l ≠ j → C l i ≠ 0 → False := by
    intro l hli hlj hCne
    have hCli : C l i = -1 := by
      rcases hlabel l i hli with ⟨h0, -⟩ | ⟨h1, -⟩
      · exact absurd h0 hCne
      · exact h1
    have hClj : C l j = -1 := by rw [← hsame l hli hlj, hCli]
    have hCil : C i l = -1 := hCneg_symm l i hli hCli
    have hCjl : C j l = -1 := hCneg_symm l j hlj hClj
    have hfin : TauCeti.IsFiniteType C := isFiniteType_of_ggIsWeylMatrixFixed hM hC
    have hdeg : ∀ v ∈ (insert i (insert j (insert l ∅)) : Finset Λ),
        2 ≤ ((insert i (insert j (insert l ∅)) : Finset Λ).filter
          (fun u => u ≠ v ∧ C v u ≠ 0)).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hv
      rcases hv with hvi | hvj | hvl
      · rw [hvi]
        have hsub : ({j, l} : Finset Λ) ⊆ (insert i (insert j (insert l ∅)) : Finset Λ).filter
            (fun u => u ≠ i ∧ C i u ≠ 0) := by
          intro u hu
          simp [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with huj | hul
          · rw [huj]
            exact ⟨by simp, hij.symm, by rw [hCij]; norm_num⟩
          · rw [hul]
            exact ⟨by simp, hli, by rw [hCil]; norm_num⟩
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair (Ne.symm hlj)] at this
      · rw [hvj]
        have hsub : ({i, l} : Finset Λ) ⊆ (insert i (insert j (insert l ∅)) : Finset Λ).filter
            (fun u => u ≠ j ∧ C j u ≠ 0) := by
          intro u hu
          simp [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with hui | hul
          · rw [hui]
            exact ⟨by simp, hij, by rw [hCji]; norm_num⟩
          · rw [hul]
            exact ⟨by simp, hlj, by rw [hCjl]; norm_num⟩
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair (Ne.symm hli)] at this
      · rw [hvl]
        have hsub : ({i, j} : Finset Λ) ⊆ (insert i (insert j (insert l ∅)) : Finset Λ).filter
            (fun u => u ≠ l ∧ C l u ≠ 0) := by
          intro u hu
          simp [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with hui | huj
          · rw [hui]
            exact ⟨by simp, Ne.symm hli, by rw [hCli]; norm_num⟩
          · rw [huj]
            exact ⟨by simp, Ne.symm hlj, by rw [hClj]; norm_num⟩
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair hij] at this
    exact ggResI_no_cycle hfin {i, j, l} ⟨i, by simp⟩ hdeg
  have hnoNbr : ∀ l, l ≠ i → l ≠ j → C l i = 0 := by
    intro l hli hlj
    by_contra hne
    exact htri l hli hlj hne
  have hconn : ∀ x, x = i ∨ x = j := by
    have hclosed : ∀ u v, (u = i ∨ u = j) → (u ≠ v ∧ M.M u v ≠ 2) → (v = i ∨ v = j) := by
      intro u v hu huv
      obtain ⟨huvne, hMuv⟩ := huv
      rcases hu with hui | huj
      · rw [hui] at huvne hMuv
        right
        by_contra hv
        have hvi : v ≠ i := fun h => huvne h.symm
        have h0 : C v i = 0 := hnoNbr v hvi hv
        have hM2 : M v i = 2 := by
          rcases hlabel v i hvi with ⟨-, h2⟩ | ⟨h1, -⟩
          · exact h2
          · exact absurd h0 (by rw [h1]; norm_num)
        rw [M.symmetric v i] at hM2
        exact hMuv hM2
      · rw [huj] at huvne hMuv
        left
        by_contra hv
        have hvj : v ≠ j := fun h => huvne h.symm
        have h0 : C v i = 0 := hnoNbr v hv hvj
        have h0' : C v j = 0 := by rw [← hsame v hv hvj]; exact h0
        have hM2 : M v j = 2 := by
          rcases hlabel v j hvj with ⟨-, h2⟩ | ⟨h1, -⟩
          · exact h2
          · exact absurd h0' (by rw [h1]; norm_num)
        rw [M.symmetric v j] at hM2
        exact hMuv hM2
    intro x
    exact reflTransGen_forward (a := i) (b := x) (P := fun z => z = i ∨ z = j)
      (Or.inl rfl) hclosed (ggRC_weyl_connected hM i x)
  obtain ⟨l, hli, hlj⟩ : ∃ l, l ≠ i ∧ l ≠ j := by
    by_contra h
    push Not at h
    have hmem : ∀ x, x = i ∨ x = j := by
      intro x
      by_cases hx : x = i
      · exact Or.inl hx
      · exact Or.inr (h x hx)
    have hsurj : Function.Surjective (fun t : Fin 2 => if t = 0 then i else j) := by
      intro x
      rcases hmem x with hx | hx
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simp [hx]⟩
    have hcard := Fintype.card_le_of_surjective _ hsurj
    simp at hcard
    omega
  rcases hconn l with h | h
  · exact hli h
  · exact hlj h

theorem exists_dRoots_of_evenSignedRefl {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hrD : ∀ i, ∃ (σ : Equiv.Perm (Fin k)) (c : Fin k → ZMod p), (∀ a, c a = 1 ∨ c a = -1) ∧
      ∏ a, c a = 1 ∧ ∀ a, b a - α i (b a) • h i = c a • b (σ a))
    (hΛ : 3 ≤ Fintype.card Λ) :
    ∃ (l : ZMod p) (ρ : Λ → Fin k → ℤ), l ≠ 0 ∧ (∀ i, ρ i ∈ ggDRootSet k) ∧
      (∀ i j, ggDDot (ρ i) (ρ j) = C i j) ∧
      (∀ i, h i = l • ∑ a, ((ρ i a : ℤ) : ZMod p) • b a) ∧
      (∀ i v, α i v = l⁻¹ * ∑ a, ((ρ i a : ℤ) : ZMod p) * b.repr v a) := by
  classical
  choose rho lam hdata using exists_dRoot_shape hp2 b hC h α hpair hrD
  have hlamne : ∀ i, lam i ≠ 0 := fun i => (hdata i).1
  have hmem : ∀ i, rho i ∈ ggDRootSet k := fun i => (hdata i).2.1
  have hh : ∀ i, h i = lam i • ∑ a, ((rho i a : ℤ) : ZMod p) • b a :=
    fun i => (hdata i).2.2.1
  have halpha : ∀ i v, α i v = (lam i)⁻¹ * ∑ a, ((rho i a : ℤ) : ZMod p) * b.repr v a :=
    fun i v => (hdata i).2.2.2 v
  set G : Λ → Λ → ℤ := fun i j => ggDDot (rho i) (rho j) with hGdef
  have hGmem : ∀ i j, -2 ≤ G i j ∧ G i j ≤ 2 := by
    intro i j
    rw [hGdef]
    exact ggDDot_bounds (hmem i) (hmem j)
  have hGdiag : ∀ i, G i i = 2 := by
    intro i
    rw [hGdef]
    exact ggDDot_self_of_mem (hmem i)
  have hcongr : ∀ i j, (C i j : ZMod p) = (lam i)⁻¹ * lam j * (G i j : ZMod p) := by
    intro i j
    have hcoord : ∀ a : Fin k, ∑ c, ((rho i c : ℤ) : ZMod p) * b.repr (b a) c
        = ((rho i a : ℤ) : ZMod p) := by
      intro a
      rw [Finset.sum_eq_single a]
      · rw [b.repr_self_apply, ite_eq_left rfl, mul_one]
      · intro c _ hca
        rw [b.repr_self_apply, ite_eq_right (fun h => hca h.symm), mul_zero]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    have hsumα : α i (∑ a, ((rho j a : ℤ) : ZMod p) • b a)
        = (lam i)⁻¹ * ∑ a, ((rho i a : ℤ) : ZMod p) * ((rho j a : ℤ) : ZMod p) := by
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, smul_eq_mul, halpha i (b a), hcoord a]
      ring
    have hGcast : (G i j : ZMod p)
        = ∑ a, ((rho i a : ℤ) : ZMod p) * ((rho j a : ℤ) : ZMod p) := by
      rw [hGdef]
      simp only [ggDDot, Int.cast_sum, Int.cast_mul]
    calc (C i j : ZMod p) = α i (h j) := (hpair i j).symm
      _ = α i (lam j • ∑ a, ((rho j a : ℤ) : ZMod p) • b a) := by rw [hh j]
      _ = lam j * α i (∑ a, ((rho j a : ℤ) : ZMod p) • b a) := by rw [map_smul, smul_eq_mul]
      _ = lam j * ((lam i)⁻¹ * ∑ a, ((rho i a : ℤ) : ZMod p) *
            ((rho j a : ℤ) : ZMod p)) := by rw [hsumα]
      _ = lam j * ((lam i)⁻¹ * (G i j : ZMod p)) := by rw [hGcast]
      _ = (lam i)⁻¹ * lam j * (G i j : ZMod p) := by ring
  have hprod : ∀ i j, (C i j : ZMod p) * (C j i : ZMod p) = (G i j : ZMod p) ^ 2 := by
    intro i j
    rw [hcongr i j, hcongr j i]
    have hGsym : G j i = G i j := by rw [hGdef]; exact ggDDot_comm _ _
    rw [hGsym]
    have hi : lam i ≠ 0 := hlamne i
    have hj : lam j ≠ 0 := hlamne j
    calc (lam i)⁻¹ * lam j * (G i j : ZMod p) * ((lam j)⁻¹ * lam i * (G i j : ZMod p))
        = ((lam i)⁻¹ * lam i) * (lam j * (lam j)⁻¹) * (G i j : ZMod p) ^ 2 := by ring
      _ = 1 * 1 * (G i j : ZMod p) ^ 2 := by rw [inv_mul_cancel₀ hi, mul_inv_cancel₀ hj]
      _ = (G i j : ZMod p) ^ 2 := by ring
  have hlabel : ∀ i j, i ≠ j → (C i j = 0 ∧ M i j = 2) ∨ (C i j = -1 ∧ M i j = 3) := by
    intro i j hij
    rcases hC.2 i j hij with ⟨hM2, h0, -⟩ | ⟨hM3, h1, -⟩ |
      ⟨hM4, hprod4, hlt4, -⟩ | ⟨hM6, hprod6, hlt6, -⟩
    · exact Or.inl ⟨h0, hM2⟩
    · exact Or.inr ⟨h1, hM3⟩
    · exfalso
      have hsq : (G i j : ZMod p) ^ 2 = 2 := by
        rw [← hprod i j, ← Int.cast_mul, hprod4]
        norm_num
      have hG0 : G i j ≠ 0 := by
        intro h0
        have hpm := ggCartanPair_mem hC hij
        simp only [ggCartanPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
          or_false] at hpm
        have hcij : (C i j : ZMod p) ≠ 0 := by
          rcases hpm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
            ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2] at hprod4; norm_num at hprod4
          · rw [h1, h2] at hprod4; norm_num at hprod4
          · rw [h1]; exact intCast_ne_zero_of_neg_small hp2 (by norm_num) (by norm_num)
          · rw [h1]; exact intCast_ne_zero_of_neg_small hp2 (by norm_num) (by norm_num)
          · rw [h1, h2] at hprod4; norm_num at hprod4
          · rw [h1, h2] at hprod4; norm_num at hprod4
        have : (C i j : ZMod p) = 0 := by rw [hcongr i j, h0]; ring
        exact hcij this
      exact not_label_four_six hp2 hG0 (hGmem i j).1 (hGmem i j).2 (Or.inl hsq)
    · exfalso
      have hsq : (G i j : ZMod p) ^ 2 = 3 := by
        rw [← hprod i j, ← Int.cast_mul, hprod6]
        norm_num
      have hG0 : G i j ≠ 0 := by
        intro h0
        have hpm := ggCartanPair_mem hC hij
        simp only [ggCartanPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
          or_false] at hpm
        have hone : C i j = -1 ∨ C j i = -1 := by
          rcases hpm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
            ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2] at hprod6; norm_num at hprod6
          · rw [h1, h2] at hprod6; norm_num at hprod6
          · rw [h1, h2] at hprod6; norm_num at hprod6
          · rw [h1, h2] at hprod6; norm_num at hprod6
          · exact Or.inl h1
          · exact Or.inr h2
        have hcij0 : (C i j : ZMod p) = 0 := by rw [hcongr i j, h0]; ring
        have hGsym : G j i = G i j := by rw [hGdef]; exact ggDDot_comm _ _
        have hcji0 : (C j i : ZMod p) = 0 := by rw [hcongr j i, hGsym, h0]; ring
        rcases hone with h1 | h1
        · rw [h1] at hcij0
          have hcast : (((-1 : ℤ) : ZMod p)) = (-1 : ZMod p) := by push_cast; ring
          rw [hcast] at hcij0
          exact (neg_ne_zero.mpr one_ne_zero) hcij0
        · rw [h1] at hcji0
          have hcast : (((-1 : ℤ) : ZMod p)) = (-1 : ZMod p) := by push_cast; ring
          rw [hcast] at hcji0
          exact (neg_ne_zero.mpr one_ne_zero) hcji0
      exact not_label_four_six hp2 hG0 (hGmem i j).1 (hGmem i j).2 (Or.inr hsq)
  have hne : Nonempty Λ := Fintype.card_pos_iff.mp (by omega)
  set i0 : Λ := Classical.choice hne with hi0def
  set l : ZMod p := lam i0 with hldef
  have hlne : l ≠ 0 := hlamne i0
  set t : Λ → ZMod p := fun i => lam i * l⁻¹ with htdef
  have hedge_lam : ∀ u v, u ≠ v → M.M u v ≠ 2 →
      lam v = -(G u v : ZMod p) * lam u ∧ ((G u v : ZMod p)) ^ 2 = 1 := by
    intro u v huv hMuv
    have hCuv : C u v = -1 := by
      rcases hlabel u v huv with ⟨h0, hM2⟩ | ⟨h1, hM3⟩
      · exact absurd hM2 hMuv
      · exact h1
    have hCvu : C v u = -1 := by
      rcases hlabel v u huv.symm with ⟨h0, hM2⟩ | ⟨h1, hM3⟩
      · rw [M.symmetric v u] at hM2
        exact absurd hM2 hMuv
      · exact h1
    have hsq : (G u v : ZMod p) ^ 2 = 1 := by
      have h' := hprod u v
      rw [hCuv, hCvu] at h'
      simpa using h'.symm
    constructor
    · have hc := hcongr u v
      rw [hCuv] at hc
      have h1 : -(1 : ZMod p) * lam u * (G u v : ZMod p) = lam v := by
        calc -(1 : ZMod p) * lam u * (G u v : ZMod p)
            = ((lam u)⁻¹ * lam v * (G u v : ZMod p)) * lam u * (G u v : ZMod p) := by
                rw [← hc]
                push_cast
                ring
          _ = lam v * ((lam u)⁻¹ * lam u) *
                ((G u v : ZMod p) * (G u v : ZMod p)) := by ring
          _ = lam v := by
              rw [inv_mul_cancel₀ (hlamne u),
                show (G u v : ZMod p) * (G u v : ZMod p) = (G u v : ZMod p) ^ 2 by ring,
                hsq]
              ring
      calc lam v = -(1 : ZMod p) * lam u * (G u v : ZMod p) := h1.symm
        _ = -(G u v : ZMod p) * lam u := by ring
    · exact hsq
  have ht : ∀ i, t i = 1 ∨ t i = -1 := by
    have hclosed : ∀ u v, (t u = 1 ∨ t u = -1) → (u ≠ v ∧ M.M u v ≠ 2) →
        (t v = 1 ∨ t v = -1) := by
      intro u v hu huv
      obtain ⟨huvne, hMuv⟩ := huv
      obtain ⟨hlam, hsq⟩ := hedge_lam u v huvne hMuv
      have htv : t v = -(G u v : ZMod p) * t u := by
        change lam v * l⁻¹ = -(G u v : ZMod p) * (lam u * l⁻¹)
        rw [hlam]
        ring
      have hx : (-(G u v : ZMod p)) = 1 ∨ (-(G u v : ZMod p)) = -1 := by
        have hx2 : (-(G u v : ZMod p)) ^ 2 = 1 := by
          rw [neg_sq, hsq]
        exact sq_eq_one_iff.mp hx2
      rw [htv]
      rcases hu with hu | hu <;> rcases hx with hx | hx <;> rw [hu, hx] <;> norm_num
    intro i
    have h0 : t i0 = 1 ∨ t i0 = -1 := by
      left
      change lam i0 * l⁻¹ = 1
      rw [← hldef]
      exact mul_inv_cancel₀ hlne
    exact reflTransGen_forward (a := i0) (b := i) (P := fun z => t z = 1 ∨ t z = -1)
      h0 hclosed (ggRC_weyl_connected hM i0 i)
  set tZ : Λ → ℤ := fun i => if t i = 1 then 1 else -1 with htZdef
  have htZcast : ∀ i, ((tZ i : ℤ) : ZMod p) = t i := by
    intro i
    show (((if t i = 1 then (1 : ℤ) else -1) : ℤ) : ZMod p) = t i
    rcases ht i with h | h
    · rw [h, ite_eq_left rfl]
      norm_num
    · have hne : t i ≠ 1 := by rw [h]; exact neg_one_ne_one hp2
      rw [ite_eq_right hne, h]
      push_cast
      ring
  have htZpm : ∀ i, tZ i = 1 ∨ tZ i = -1 := by
    intro i
    show (if t i = 1 then (1 : ℤ) else -1) = 1 ∨ (if t i = 1 then (1 : ℤ) else -1) = -1
    split_ifs with h
    · left; rfl
    · right; rfl
  set rho' : Λ → Fin k → ℤ := fun i a => tZ i * rho i a with hrhodef
  have hmem' : ∀ i, rho' i ∈ ggDRootSet k := by
    intro i
    rcases htZpm i with h | h
    · have h' : rho' i = rho i := by
        funext a; change tZ i * rho i a = rho i a; rw [h]; ring
      rw [h']; exact hmem i
    · have h' : rho' i = -rho i := by
        funext a; change tZ i * rho i a = -rho i a; rw [h]; ring
      rw [h']; exact ggDRootSet_neg_mem (hmem i)
  have hti : ∀ i, t i * t i = 1 := by
    intro i
    rcases ht i with h | h <;> rw [h] <;> ring
  have htinv : ∀ i, (t i)⁻¹ = t i := by
    intro i
    rcases ht i with h | h <;> rw [h] <;> norm_num
  have hlam_i : ∀ i, lam i = t i * l := by
    intro i
    change lam i = lam i * l⁻¹ * l
    rw [mul_assoc, inv_mul_cancel₀ hlne, mul_one]
  have hsum' : ∀ i, ∑ a, ((rho' i a : ℤ) : ZMod p) • b a
      = t i • ∑ a, ((rho i a : ℤ) : ZMod p) • b a := by
    intro i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show ((rho' i a : ℤ) : ZMod p) = t i * ((rho i a : ℤ) : ZMod p) by
      change ((tZ i * rho i a : ℤ) : ZMod p) = t i * ((rho i a : ℤ) : ZMod p)
      rw [Int.cast_mul, htZcast i]]
    rw [mul_smul]
  have hh' : ∀ i, h i = l • ∑ a, ((rho' i a : ℤ) : ZMod p) • b a := by
    intro i
    rw [hh i, hsum' i, hlam_i i, mul_comm (t i) l, mul_smul]
  have hsumα' : ∀ i v, ∑ a, ((rho' i a : ℤ) : ZMod p) * b.repr v a
      = t i * ∑ a, ((rho i a : ℤ) : ZMod p) * b.repr v a := by
    intro i v
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show ((rho' i a : ℤ) : ZMod p) = t i * ((rho i a : ℤ) : ZMod p) by
      change ((tZ i * rho i a : ℤ) : ZMod p) = t i * ((rho i a : ℤ) : ZMod p)
      rw [Int.cast_mul, htZcast i]]
    ring
  have hlam_inv : ∀ i, (lam i)⁻¹ = t i * l⁻¹ := by
    intro i
    rw [hlam_i i, mul_inv_rev, htinv i, mul_comm]
  have hα' : ∀ i v, α i v = l⁻¹ * ∑ a, ((rho' i a : ℤ) : ZMod p) * b.repr v a := by
    intro i v
    rw [halpha i v, hsumα' i v, hlam_inv i]
    ring
  have hGram : ∀ i j, ggDDot (rho' i) (rho' j) = C i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [show ggDDot (rho' i) (rho' i) = 2 from ggDDot_self_of_mem (hmem' i), hC.1 i]
    · have hG' : ggDDot (rho' i) (rho' j) = tZ i * tZ j * G i j := by
        rw [hGdef]
        show (∑ a, (tZ i * rho i a) * (tZ j * rho j a))
            = tZ i * tZ j * ∑ a, rho i a * rho j a
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      have hcast : ((ggDDot (rho' i) (rho' j) : ℤ) : ZMod p) = (C i j : ZMod p) := by
        have hcast1 : ((tZ i * tZ j * G i j : ℤ) : ZMod p)
            = t i * t j * (G i j : ZMod p) := by
          rw [Int.cast_mul, Int.cast_mul, htZcast i, htZcast j]
        rw [hG', hcast1, hcongr i j, hlam_i i, hlam_i j, mul_inv_rev]
        rw [show (l⁻¹ * (t i)⁻¹) * (t j * l) * (G i j : ZMod p)
            = (t i)⁻¹ * t j * (l⁻¹ * l) * (G i j : ZMod p) by ring]
        rw [inv_mul_cancel₀ hlne, htinv i]
        ring
      rcases hlabel i j hij with ⟨hC0, hM2⟩ | ⟨hC1, hM3⟩
      · have hG0 : G i j = 0 := by
          have hc := hcongr i j
          rw [hC0, Int.cast_zero] at hc
          have h0 : (lam i)⁻¹ * lam j * (G i j : ZMod p) = 0 := hc.symm
          rcases mul_eq_zero.mp h0 with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 (inv_ne_zero (hlamne i))
            · exact absurd h2 (hlamne j)
          · have hdvd : (p : ℤ) ∣ G i j := by
              rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
              exact h1
            have hb := hGmem i j
            have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp2
            have habs : |G i j| < p := by
              obtain ⟨hb1, hb2⟩ := hGmem i j
              rw [abs_lt]
              constructor <;> omega
            exact Int.eq_zero_of_abs_lt_dvd hdvd habs
        rw [hG', hG0, hC0]
        ring
      · have hnotpm2 : ¬ (G i j = 2 ∨ G i j = -2) := by
          intro hGij
          by_cases hp3eq : p = 3
          · exact ggEdge_pm_two_false hM hC rho lam hlamne hmem hcongr hlabel hp3eq hΛ hij
              hM3 hGij
          · have h41 : (4 : ZMod p) ≠ 1 := by
              intro h41v
              have h3 : (3 : ZMod p) = 0 := by
                have h2 : (4 : ZMod p) - 1 = 0 := by rw [h41v]; ring
                rw [show (4 : ZMod p) - 1 = 3 by ring] at h2
                exact h2
              have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
              have hp2le : 2 ≤ p := (Fact.out : p.Prime).two_le
              rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
              · exact absurd h1 (by omega)
              · exact hp3eq h1
            have hCji : C j i = -1 := by
              rcases hlabel j i (Ne.symm hij) with ⟨-, h2⟩ | ⟨h1, -⟩
              · rw [M.symmetric j i] at h2
                rw [hM3] at h2
                norm_num at h2
              · exact h1
            have hsq1 : (G i j : ZMod p) ^ 2 = 1 := by
              have h' := hprod i j
              rw [hC1, hCji] at h'
              simpa using h'.symm
            rcases hGij with hg | hg
            · have h4 : (((4 : ℤ) : ZMod p)) = 1 := by
                rw [← hsq1, hg]
                rw [show (((2 : ℤ) : ZMod p)) ^ 2 = ((4 : ℤ) : ZMod p) by
                  rw [← Int.cast_pow]; norm_num]
              exact h41 (by simpa using h4)
            · have h4 : (((4 : ℤ) : ZMod p)) = 1 := by
                rw [← hsq1, hg]
                rw [show (((-2 : ℤ) : ZMod p)) ^ 2 = ((4 : ℤ) : ZMod p) by
                  rw [← Int.cast_pow]; norm_num]
              exact h41 (by simpa using h4)
        have htsgn : tZ i * tZ j = 1 ∨ tZ i * tZ j = -1 := by
          rcases htZpm i with hi | hi <;> rcases htZpm j with hj | hj <;>
            rw [hi, hj] <;> norm_num
        have htsq : ∀ x : ℤ, x = 1 ∨ x = -1 → x * x = 1 := by
          intro x hx; rcases hx with rfl | rfl <;> norm_num
        have hzi : tZ i * tZ i = 1 := htsq (tZ i) (htZpm i)
        have hzj : tZ j * tZ j = 1 := htsq (tZ j) (htZpm j)
        have hG'ne2 : ggDDot (rho' i) (rho' j) ≠ 2 := by
          intro h2
          apply hnotpm2
          have hEq : tZ i * tZ j * G i j = 2 := hG'.symm.trans h2
          have h2' := congrArg (fun x : ℤ => x * (tZ i * tZ j)) hEq
          rw [show (tZ i * tZ j * G i j) * (tZ i * tZ j)
              = G i j * ((tZ i * tZ i) * (tZ j * tZ j)) by ring, hzi, hzj, mul_one,
            mul_one] at h2'
          have hg : G i j = 2 ∨ G i j = -2 := by
            rcases htsgn with hs | hs <;> rw [h2', hs] <;> norm_num
          exact hg
        have hG'ne2' : ggDDot (rho' i) (rho' j) ≠ -2 := by
          intro h2
          apply hnotpm2
          have hEq : tZ i * tZ j * G i j = -2 := hG'.symm.trans h2
          have h2' := congrArg (fun x : ℤ => x * (tZ i * tZ j)) hEq
          rw [show (tZ i * tZ j * G i j) * (tZ i * tZ j)
              = G i j * ((tZ i * tZ i) * (tZ j * tZ j)) by ring, hzi, hzj, mul_one,
            mul_one] at h2'
          have hg : G i j = 2 ∨ G i j = -2 := by
            rcases htsgn with hs | hs <;> rw [h2', hs] <;> norm_num
          exact hg
        have hb := ggDDot_bounds (hmem' i) (hmem' j)
        have hGle : -1 ≤ ggDDot (rho' i) (rho' j) ∧ ggDDot (rho' i) (rho' j) ≤ 1 := by
          constructor
          · by_contra hlt
            push Not at hlt
            have : ggDDot (rho' i) (rho' j) = -2 := by omega
            exact hG'ne2' this
          · by_contra hlt
            push Not at hlt
            have : ggDDot (rho' i) (rho' j) = 2 := by omega
            exact hG'ne2 this
        exact int_eq_of_bounds_cast_eq hp2 hGle.1 hGle.2 (Or.inr hC1) hcast
  exact ⟨l, rho', hlne, hmem', hGram, hh', hα'⟩

end CFSG.StandardType

end
