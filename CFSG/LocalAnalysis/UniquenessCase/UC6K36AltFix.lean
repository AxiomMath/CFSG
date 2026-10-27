module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Alt36

open Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem eq_one_of_mem_of_pow_prime_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup G} (hR : IsPGroup 2 R) {w : G} (hw : w ∈ R) (hwp : w ^ p = 1) : w = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨w, hw⟩
  have hk' : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime p (2 ^ k) := ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k
  have h := pow_gcd_eq_one.mpr ⟨hwp, hk'⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

theorem commute_of_mul_mul_inv_mul_inv_eq_one {G : Type*} [Group G] {a b : G} (h : a * b * a⁻¹ * b⁻¹ = 1) :
    Commute a b :=
  mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)

theorem apply_eq_self_of_commute_isCycle {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c r : Perm Ω} (hc : c.IsCycle)
    (hcp : c ^ p = 1) {k : ℕ} (hr : r ^ 2 ^ k = 1) (hrc : Commute r c) {x : Ω} (hx : x ∈ c.support) :
    r x = x := by
  have hx' : c x ≠ x := mem_support.mp hx
  have hrx : c (r x) ≠ r x := mem_support.mp ((mem_support_iff_of_commute hrc x).mpr hx)
  obtain ⟨i, -, hi⟩ := (hc.sameCycle hx' hrx).exists_pow_eq'
  have key : ∀ n : ℕ, (r ^ n) x = (c ^ (i * n)) x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, ih, ← Perm.mul_apply, (hrc.pow_right (i * n)).eq, Perm.mul_apply, ← hi,
        ← Perm.mul_apply, ← pow_add, mul_add, mul_one]
  have h1 : c ^ (i * 2 ^ k) = 1 := (hc.pow_eq_one_iff' hx').mpr (by rw [← key, hr, Perm.one_apply])
  haveI := Fact.mk hp
  have hord : orderOf c = p := orderOf_eq_prime hcp hc.ne_one
  have hcop : Nat.Coprime p (2 ^ k) := ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k
  have h2 : p ∣ i := hcop.dvd_of_dvd_mul_right (by rw [← hord]; exact orderOf_dvd_of_pow_eq_one h1)
  have h3 : c ^ i = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hord]; exact h2)
  rw [← hi, h3, Perm.one_apply]

theorem fix_of_normalized {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : Perm Ω} (hσ : σ ^ p = 1)
    {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R) (hRσ : ∀ r ∈ R, r * σ = σ * r)
    (hRn : ∀ k ∈ alternatingGroup Ω, k * σ = σ * k → ∀ r ∈ R, k * r * k⁻¹ ∈ R)
    {r : Perm Ω} (hr : r ∈ R) {x : Ω} (hx : x ∈ σ.support) : r x = x := by
  have hσx : σ x ≠ x := mem_support.mp hx
  have hc : (σ.cycleOf x).IsCycle := isCycle_cycleOf σ hσx
  have hcF : σ.cycleOf x ∈ σ.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.mpr hx
  have hcp : σ.cycleOf x ^ p = 1 :=
    (hc.pow_eq_one_iff' (x := x) (by rwa [cycleOf_apply_self])).mpr
      (by rw [cycleOf_pow_apply_self, hσ, Perm.one_apply])
  haveI := Fact.mk hp
  have hsign : sign (σ.cycleOf x) = 1 := by
    rw [hc.sign, ← hc.orderOf, orderOf_eq_prime hcp hc.ne_one, Odd.neg_one_pow (hp.odd_of_ne_two hp2), neg_neg]
  have hw : r * σ.cycleOf x * r⁻¹ * (σ.cycleOf x)⁻¹ ∈ R := by
    have h := R.mul_mem hr (hRn _ (mem_alternatingGroup.mpr hsign) (self_mem_cycle_factors_commute hcF).eq r⁻¹
      (R.inv_mem hr))
    simpa only [mul_assoc] using h
  have hc'F : r * σ.cycleOf x * r⁻¹ ∈ σ.cycleFactorsFinset := by
    have h := (mem_cycleFactorsFinset_conj σ r (σ.cycleOf x)).mpr hcF
    rwa [hRσ r hr, mul_inv_cancel_right] at h
  have hwp : (r * σ.cycleOf x * r⁻¹ * (σ.cycleOf x)⁻¹) ^ p = 1 := by
    rw [(cycleFactorsFinset_mem_commute' σ hc'F hcF).inv_right.mul_pow, conj_pow, hcp, inv_pow, hcp]
    simp
  have hrc : Commute r (σ.cycleOf x) :=
    commute_of_mul_mul_inv_mul_inv_eq_one (eq_one_of_mem_of_pow_prime_eq_one hp hp2 hR hw hwp)
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact apply_eq_self_of_commute_isCycle hp hp2 hc hcp hk' hrc
    (mem_support_cycleOf_iff.mpr ⟨SameCycle.refl _ _, hx⟩)

theorem card_compl_support_of_normalized {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : Perm Ω} (hσ : σ ^ p = 1)
    {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R) (hRσ : ∀ r ∈ R, r * σ = σ * r)
    (hRn : ∀ k ∈ alternatingGroup Ω, k * σ = σ * k → ∀ r ∈ R, k * r * k⁻¹ ∈ R) (hR1 : R ≠ ⊥) :
    σ.supportᶜ.card = 2 ∨ σ.supportᶜ.card = 4 := by
  set F := σ.supportᶜ
  have hsupp : ∀ r ∈ R, r.support ⊆ F := fun r hr y hy =>
    Finset.mem_compl.mpr fun hyσ => mem_support.mp hy (fix_of_normalized hp hp2 hσ hR hRσ hRn hr hyσ)
  have hnorm : ∀ g : Perm Ω, sign g = 1 → g.support ⊆ F → ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg hgF =>
    hRn g (mem_alternatingGroup.mpr hg) (disjoint_iff_disjoint_support.mpr
      (Finset.disjoint_of_subset_left hgF disjoint_compl_left)).commute.eq
  obtain ⟨r, hr, hr1⟩ := R.bot_or_exists_ne_one.resolve_left hR1
  obtain ⟨a, ha⟩ : ∃ a, r a ≠ a := by
    by_contra! h
    exact hr1 (Perm.ext h)
  obtain ⟨b, hb⟩ : ∃ b, r a = b := ⟨_, rfl⟩
  have hba : b ≠ a := by rw [← hb]; exact ha
  have haF : a ∈ F := hsupp r hr (mem_support.mpr ha)
  have hbF : b ∈ F := by rw [← hb]; exact hsupp r hr (apply_mem_support.mpr (mem_support.mpr ha))
  have hab : ({a, b} : Finset Ω).card = 2 := Finset.card_pair hba.symm
  have hm2 : 2 ≤ F.card := by
    rw [← hab]
    exact Finset.card_le_card (Finset.insert_subset haF (Finset.singleton_subset_iff.mpr hbF))
  by_contra hcon
  have hm : F.card = 3 ∨ 5 ≤ F.card := by omega
  obtain ⟨e, heF, he⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a, b}) (t := F) (by omega)
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at he
  obtain ⟨hea, heb⟩ := he
  have hg3 : IsThreeCycle (swap a b * swap a e) := isThreeCycle_swap_mul_swap_same hba.symm (Ne.symm hea)
    (Ne.symm heb)
  have hg3p : (swap a b * swap a e) ^ 3 = 1 := by
    rw [← hg3.orderOf]
    exact pow_orderOf_eq_one _
  have hgF : (swap a b * swap a e).support ⊆ F := by
    intro y hy
    have hy' := Finset.mem_of_subset (support_mul_le _ _) hy
    rw [Finset.sup_eq_union, Finset.mem_union, support_swap hba.symm, support_swap (Ne.symm hea)] at hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with (rfl | rfl) | (rfl | rfl) <;> assumption
  have hag : a ∈ (swap a b * swap a e).support := by
    rw [mem_support, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hea heb]
    exact hea
  let φ : alternatingGroup F →* Perm Ω := (alternatingGroup Ω).subtype.comp (alternatingGroup.ofSubtype F)
  have hφs : ∀ k₀, sign (φ k₀) = 1 := fun k₀ => mem_alternatingGroup.mp (alternatingGroup.ofSubtype F k₀).2
  have hφF : ∀ k₀, (φ k₀).support ⊆ F := fun k₀ =>
    (alternatingGroup.mem_range_ofSubtype_iff F _).mp ⟨k₀, rfl⟩
  have hφ : ∀ w : Perm Ω, sign w = 1 → w.support ⊆ F → ∃ k₀, φ k₀ = w := fun w hw hwF => by
    obtain ⟨k₀, hk₀⟩ := MonoidHom.mem_range.mp
      ((alternatingGroup.mem_range_ofSubtype_iff F ⟨w, mem_alternatingGroup.mpr hw⟩).mpr hwF)
    exact ⟨k₀, congrArg Subtype.val hk₀⟩
  let N : Subgroup (alternatingGroup F) := R.comap φ
  haveI : N.Normal := ⟨fun n hn g => by
    show φ (g * n * g⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact hnorm (φ g) (hφs g) (hφF g) (φ n) hn⟩
  haveI : IsSimpleGroup (alternatingGroup F) := by
    rcases hm with hm3 | hm5
    · haveI : Nontrivial F := ⟨⟨⟨a, haF⟩, ⟨b, hbF⟩, fun h => hba (congrArg Subtype.val h).symm⟩⟩
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isSimpleGroup_of_prime_card (p := 3)
        (by rw [nat_card_alternatingGroup, Nat.card_eq_finsetCard, hm3]; decide)
    · exact alternatingGroup.isSimpleGroup (by rwa [Nat.card_eq_finsetCard])
  have hNbot : N = ⊥ := by
    refine (Subgroup.Normal.eq_bot_or_eq_top N).resolve_right fun hNt => ?_
    obtain ⟨k₀, hk₀⟩ := hφ _ hg3.sign hgF
    have hgR : swap a b * swap a e ∈ R := by
      rw [← hk₀]
      have h : k₀ ∈ N := by rw [hNt]; exact Subgroup.mem_top k₀
      exact h
    exact hg3.ne_one (eq_one_of_mem_of_pow_prime_eq_one Nat.prime_three (by norm_num) hR hgR hg3p)
  have hP : ∀ w ∈ R, sign w = 1 → w = 1 := fun w hw hws => by
    obtain ⟨k₀, hk₀⟩ := hφ w hws (hsupp w hw)
    have hk₀N : k₀ ∈ N := show φ k₀ ∈ R by rw [hk₀]; exact hw
    rw [hNbot, Subgroup.mem_bot] at hk₀N
    rw [← hk₀, hk₀N, map_one]
  have hcomm : ∀ g : Perm Ω, sign g = 1 → g.support ⊆ F → Commute r g := fun g hg hgF' => by
    refine commute_of_mul_mul_inv_mul_inv_eq_one (hP _ ?_ (by simp [hg]))
    simpa only [mul_assoc] using R.mul_mem hr (hnorm g hg hgF' r⁻¹ (R.inv_mem hr))
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact ha (apply_eq_self_of_commute_isCycle Nat.prime_three (by norm_num) hg3.isCycle hg3p hk'
    (hcomm _ hg3.sign hgF) hag)

end CFSG.LocalAnalysis.UniquenessCase.UCK.Alt36
