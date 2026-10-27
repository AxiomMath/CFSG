module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.GeomSum

public section

namespace CFSG.StandardType

namespace NbrLang

section Normalizer

variable {G : Type*} [Group G]

theorem pow_mul_mul_inv_pow_mem {H : Subgroup G} {w : G} (h : ∀ b ∈ H, w * b * w⁻¹ ∈ H)
    (n : ℕ) {b : G} (hb : b ∈ H) : w ^ n * b * (w ^ n)⁻¹ ∈ H := by
  induction n with
  | zero => simpa using hb
  | succ n ih =>
    have h1 := h _ ih
    rw [pow_succ', mul_inv_rev]
    simpa only [mul_assoc] using h1

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {w : G}
    (h : ∀ b ∈ H, w * b * w⁻¹ ∈ H) : w ∈ Subgroup.normalizer (H : Set G) := by
  have hinv : w⁻¹ = w ^ (Nat.card G - 1) := by
    have h1 : w ^ Nat.card G = 1 := pow_card_eq_one'
    have h2 : 1 ≤ Nat.card G := Nat.card_pos
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel h2, h1]
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨h b, fun hb => ?_⟩
  have h3 := pow_mul_mul_inv_pow_mem h (Nat.card G - 1) hb
  rw [← hinv, inv_inv] at h3
  simpa [mul_assoc] using h3

theorem mem_normalizer_of_conj_mem_centralizer [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {w : G}
    (hw : ∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) :
    w ∈ Subgroup.normalizer (Bs : Set G) := by
  refine mem_normalizer_of_conj_mem fun b hb => hSC _ (hw b hb) ?_
  rw [conj_pow, hexp b hb, mul_one, mul_inv_cancel]

end Normalizer

section Abstract

variable {A : Type*} [CommGroup A]

theorem pow_apply_eq_self {β : MulAut A} {e : A} (he : β e = e) (i : ℕ) : (β ^ i) e = e := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pow_succ, MulAut.mul_apply, he, ih]

theorem prod_pow_apply_comp {β : MulAut A} {p : ℕ} (hβp : β ^ p = 1) (s : A) :
    ∏ i ∈ Finset.range p, (β ^ i) (β s) = ∏ i ∈ Finset.range p, (β ^ i) s := by
  have h1 := Finset.prod_range_succ' (fun i => (β ^ i) s) p
  have h2 := Finset.prod_range_succ (fun i => (β ^ i) s) p
  simp only [pow_zero, MulAut.one_apply, hβp] at h1 h2
  have h3 : ∏ i ∈ Finset.range p, (β ^ i) (β s) = ∏ i ∈ Finset.range p, (β ^ (i + 1)) s := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_succ, MulAut.mul_apply]
  rw [h3]
  exact mul_right_cancel (h1.symm.trans h2)

theorem apply_prod_pow_apply {β : MulAut A} {p : ℕ} (hβp : β ^ p = 1) (s : A) :
    β (∏ i ∈ Finset.range p, (β ^ i) s) = ∏ i ∈ Finset.range p, (β ^ i) s := by
  conv_rhs => rw [← prod_pow_apply_comp hβp s]
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  change (β * β ^ i) s = (β ^ i * β) s
  rw [← pow_succ', ← pow_succ]

theorem exists_mul_inv_eq_of_norm [Finite A] {p : ℕ} {β : MulAut A} (hβp : β ^ p = 1)
    (hnorm : ∀ t : A, β t = t → ∃ s : A, ∏ i ∈ Finset.range p, (β ^ i) s = t)
    {e : A} (he : β e = e) (hep : e ^ p = 1) : ∃ k : A, k * (β k)⁻¹ = e := by
  let N : A →* A := ∏ i ∈ Finset.range p, (β ^ i).toMonoidHom
  have hN : ∀ s, N s = ∏ i ∈ Finset.range p, (β ^ i) s := fun s => by
    simp [N]
  let f : A →* A :=
    { toFun := fun t => t * (β t)⁻¹
      map_one' := by simp
      map_mul' := fun a c => by
        simp only [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hf : ∀ t, f t = t * (β t)⁻¹ := fun _ => rfl
  have hker : f.ker = N.range := by
    ext t
    rw [MonoidHom.mem_ker, hf, mul_inv_eq_one, MonoidHom.mem_range]
    constructor
    · intro ht
      obtain ⟨s, hs⟩ := hnorm t ht.symm
      exact ⟨s, (hN s).trans hs⟩
    · rintro ⟨s, rfl⟩
      rw [hN]
      exact (apply_prod_pow_apply hβp s).symm
  have hle : f.range ≤ N.ker := by
    rintro _ ⟨t, rfl⟩
    rw [MonoidHom.mem_ker, hf, map_mul, map_inv, hN, hN, prod_pow_apply_comp hβp, mul_inv_cancel]
  have hcard : Nat.card N.ker ≤ Nat.card f.range := by
    have h1 := Subgroup.card_ker_mul_card_range f
    have h2 := Subgroup.card_ker_mul_card_range N
    rw [hker] at h1
    have hpos : 0 < Nat.card N.range := Nat.card_pos
    have h3 : Nat.card N.range * Nat.card f.range = Nat.card N.range * Nat.card N.ker := by
      rw [h1, ← h2, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left hpos h3).ge
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have heN : e ∈ N.ker := by
    rw [MonoidHom.mem_ker, hN, Finset.prod_congr rfl fun i _ => pow_apply_eq_self he i,
      Finset.prod_const, Finset.card_range, hep]
  rw [← heq] at heN
  obtain ⟨k, hk⟩ := heN
  exact ⟨k, hk⟩

end Abstract

section Cyclic

variable {A : Type*} [CommGroup A]

theorem pow_apply_eq_pow {β : MulAut A} {r : ℕ} (hβ : ∀ t, β t = t ^ r) (i : ℕ) (s : A) :
    (β ^ i) s = s ^ (r ^ i) := by
  induction i generalizing s with
  | zero => simp
  | succ i ih => rw [pow_succ, MulAut.mul_apply, hβ, ih, ← pow_mul, ← pow_succ']

theorem norm_surjective_of_isCyclic [Finite A] [IsCyclic A] {r p : ℕ}
    (hcard : Nat.card A = r ^ p - 1) {β : MulAut A} (hβ : ∀ t, β t = t ^ r) :
    ∀ t : A, β t = t → ∃ s : A, ∏ i ∈ Finset.range p, (β ^ i) s = t := by
  have hN : ∀ s : A, ∏ i ∈ Finset.range p, (β ^ i) s = s ^ ∑ i ∈ Finset.range p, r ^ i :=
    fun s => by
      simp_rw [pow_apply_eq_pow hβ]
      exact Finset.prod_pow_eq_pow_sum _ _ _
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hr : 2 ≤ r := by
    by_contra h
    have h' : r ≤ 1 := by omega
    have h1 : r ^ p ≤ 1 := pow_le_one₀ (Nat.zero_le r) h'
    omega
  have hσ : (∑ i ∈ Finset.range p, r ^ i) * (r - 1) = Nat.card A := by
    rw [hcard]
    exact geom_sum_mul_of_one_le (by omega) p
  intro t ht
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have hog : orderOf g = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, g ^ j = t := by
    have h1 : t ∈ Submonoid.powers g := by
      rw [mem_powers_iff_mem_zpowers]
      exact hg t
    exact h1
  have htr : (g ^ j) ^ (r - 1) = 1 := by
    have h1 : (g ^ j) ^ (r - 1) * g ^ j = 1 * g ^ j := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r), ← hβ, ht]
    exact mul_right_cancel h1
  have hdvd : (∑ i ∈ Finset.range p, r ^ i) ∣ j := by
    have h1 : orderOf g ∣ j * (r - 1) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact htr)
    rw [hog, ← hσ] at h1
    exact Nat.dvd_of_mul_dvd_mul_right (by omega) h1
  obtain ⟨c, rfl⟩ := hdvd
  exact ⟨g ^ c, by rw [hN, ← pow_mul, mul_comm]⟩


theorem prod_range_zpow (s : A) (f : ℕ → ℤ) (n : ℕ) :
    ∏ i ∈ Finset.range n, s ^ f i = s ^ ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, Finset.sum_range_succ, zpow_add, ih]

theorem pow_apply_eq_zpow {β : MulAut A} {r : ℤ} (hβ : ∀ t, β t = t ^ r) (i : ℕ) (s : A) :
    (β ^ i) s = s ^ (r ^ i) := by
  induction i generalizing s with
  | zero => simp
  | succ i ih => rw [pow_succ, MulAut.mul_apply, hβ, ih, ← zpow_mul, ← pow_succ']

theorem norm_surjective_of_isCyclic_zpow [Finite A] [IsCyclic A] {r : ℤ} {p : ℕ}
    (hcard : (Nat.card A : ℤ) = |r ^ p - 1|) {β : MulAut A} (hβ : ∀ t, β t = t ^ r) :
    ∀ t : A, β t = t → ∃ s : A, ∏ i ∈ Finset.range p, (β ^ i) s = t := by
  have hN : ∀ s : A, ∏ i ∈ Finset.range p, (β ^ i) s = s ^ ∑ i ∈ Finset.range p, r ^ i :=
    fun s => by
      simp_rw [pow_apply_eq_zpow hβ]
      exact prod_range_zpow s _ p
  have hσ : (∑ i ∈ Finset.range p, r ^ i) * (r - 1) = r ^ p - 1 := geom_sum_mul r p
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hr : r - 1 ≠ 0 := by
    intro h
    have h1 : r = 1 := by omega
    rw [h1, one_pow, sub_self, abs_zero] at hcard
    omega
  intro t ht
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have hog : orderOf g = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg t)
  have htr : (g ^ j) ^ (r - 1) = 1 := by
    have h1 := hβ (g ^ j)
    rw [ht] at h1
    rw [zpow_sub_one, ← h1, mul_inv_cancel]
  have hdvd : (∑ i ∈ Finset.range p, r ^ i) ∣ j := by
    rw [← zpow_mul] at htr
    have h1 : (orderOf g : ℤ) ∣ j * (r - 1) := orderOf_dvd_iff_zpow_eq_one.mpr htr
    rw [hog, hcard, ← hσ, abs_dvd] at h1
    exact (mul_dvd_mul_iff_right hr).mp h1
  obtain ⟨c, rfl⟩ := hdvd
  exact ⟨g ^ c, by rw [hN, ← zpow_mul, mul_comm]⟩

end Cyclic

section Group

open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem exists_conj_eq_mul_of_norm [Finite G] {p : ℕ} {T : Subgroup G}
    (hT : ∀ a ∈ T, ∀ c ∈ T, a * c = c * a) {b : G}
    (hb : b ∈ Subgroup.normalizer (T : Set G)) (hbp : b ^ p = 1)
    (hnorm : ∀ t ∈ T, b * t * b⁻¹ = t → ∃ s ∈ T,
      t = ((List.range p).map fun i => b ^ i * s * (b ^ i)⁻¹).prod)
    {e : G} (heT : e ∈ T) (heb : b * e * b⁻¹ = e) (hep : e ^ p = 1) :
    ∃ k ∈ T, k * b * k⁻¹ = e * b := by
  have : IsMulCommutative T := ⟨⟨fun a c => Subtype.ext (hT a a.2 c c.2)⟩⟩
  set β : MulAut T := T.normalizerMonoidHom ⟨b, hb⟩ with hβdef
  have hβval : ∀ (i : ℕ) (t : T), (((β ^ i) t : T) : G) = b ^ i * t * (b ^ i)⁻¹ := by
    intro i t
    rw [hβdef, ← map_pow]
    rfl
  have hβp : β ^ p = 1 := by
    have h1 : (⟨b, hb⟩ : Subgroup.normalizer (T : Set G)) ^ p = 1 := Subtype.ext hbp
    rw [hβdef, ← map_pow, h1, map_one]
  have hcoe : ∀ (s : T) (n : ℕ), ((∏ i ∈ Finset.range n, (β ^ i) s : T) : G) =
      ((List.range n).map fun i => b ^ i * (s : G) * (b ^ i)⁻¹).prod := by
    intro s n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, Subgroup.coe_mul, ih, hβval, List.range_succ, List.map_append,
        List.prod_append]
      simp
  have hnorm' : ∀ t : T, β t = t → ∃ s : T, ∏ i ∈ Finset.range p, (β ^ i) s = t := by
    intro t ht
    have h1 : b * (t : G) * b⁻¹ = t := by
      have h2 := hβval 1 t
      rw [pow_one, pow_one, ht] at h2
      exact h2.symm
    obtain ⟨s, hs, hst⟩ := hnorm t t.2 h1
    exact ⟨⟨s, hs⟩, Subtype.ext ((hcoe _ p).trans hst.symm)⟩
  have he : β ⟨e, heT⟩ = ⟨e, heT⟩ := by
    apply Subtype.ext
    have h1 := hβval 1 ⟨e, heT⟩
    rw [pow_one, pow_one] at h1
    exact h1.trans heb
  have hep' : (⟨e, heT⟩ : T) ^ p = 1 := Subtype.ext (by simpa using hep)
  obtain ⟨k, hk⟩ := exists_mul_inv_eq_of_norm hβp hnorm' he hep'
  refine ⟨k, k.2, ?_⟩
  have h1 : (k : G) * ((β k : T) : G)⁻¹ = e := congrArg Subtype.val hk
  have h2 := hβval 1 k
  rw [pow_one, pow_one] at h2
  rw [h2] at h1
  calc (k : G) * b * (k : G)⁻¹ = (k : G) * (b * k * b⁻¹)⁻¹ * b := by group
    _ = e * b := by rw [h1]

end Group

end NbrLang

end CFSG.StandardType

end
