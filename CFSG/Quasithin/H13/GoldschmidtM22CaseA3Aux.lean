module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj

public section

namespace CFSG.Quasithin.H13.GM22.CaseA3

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem perm_fin_five_pow_four_of_commute :
    ∀ w δ : Equiv.Perm (Fin 5), w * w = 1 → w ≠ 1 → Equiv.Perm.sign w = 1 →
      δ * w = w * δ → δ ^ 4 = 1 := by
  decide +kernel

theorem perm_fin_five_eq_one_of_commute {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {w δ : Equiv.Perm (Fin 5)} (hw : w * w = 1) (hw1 : w ≠ 1) (hs : Equiv.Perm.sign w = 1)
    (hc : δ * w = w * δ) (hδ : δ ^ p = 1) : δ = 1 := by
  have h4 := perm_fin_five_pow_four_of_commute w δ hw hw1 hs hc
  have hcop : Nat.Coprime 4 p := by
    have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    simpa using h2.pow_left 2
  have := pow_gcd_eq_one.mpr ⟨h4, hδ⟩
  rwa [hcop, pow_one] at this

theorem eq_two_of_prime_eq_two_pow {p k : ℕ} (hp : p.Prime) (h : p = 2 ^ k) : p = 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at h
    exact absurd (h ▸ hp) Nat.not_prime_one
  · have h2 : 2 ∣ p := h ▸ dvd_pow_self 2 hk.ne'
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm

theorem orderOf_ne_prime_of_isPGroup {T : Subgroup G} (hT : IsPGroup 2 T) {x : G}
    (hx : x ∈ T) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : orderOf x ≠ p := by
  intro h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk, h] at hk
  exact hp2 (eq_two_of_prime_eq_two_pow hp hk)

theorem isPGroup_sup_two [Finite G] {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) : IsPGroup 2 ↥(A ⊔ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
  rw [inf_eq_left.mpr le_sup_right, A4.relIndex_sup_eq_of_le_normalizer' hAB] at h1
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  have h3 : B.relIndex A ∣ 2 ^ a := ha ▸ Dvd.intro _ h2
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  exact IsPGroup.of_card (n := c + b) (by rw [← h1, hc, hb, pow_add])

theorem exists_fixed_of_prime_order {d : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : orderOf d = p) {S : Set G} (hfin : S.Finite) (hcard : S.ncard = 4)
    (hS : ∀ v ∈ S, d * v * d⁻¹ ∈ S) : ∃ v ∈ S, d * v * d⁻¹ = v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype ↥S := hfin.fintype
  let f : ↥S → ↥S := fun v => ⟨d * v * d⁻¹, hS v v.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f] at this
    exact Subtype.ext (by simpa using this)
  let σ : Equiv.Perm ↥S := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hσpow : ∀ (k : ℕ) (v : ↥S), (((σ ^ k) v : ↥S) : G) = d ^ k * v * (d ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', Equiv.Perm.mul_apply]
      have h1 : ((σ ((σ ^ k) v) : ↥S) : G) = d * ((σ ^ k) v : ↥S) * d⁻¹ := rfl
      rw [h1, ih v, pow_succ']
      group
  have hσ : σ ^ p ^ 1 = 1 := by
    ext v
    rw [pow_one]
    refine congrArg Subtype.val ?_
    apply Subtype.ext
    rw [hσpow, ← hd, pow_orderOf_eq_one]
    simp
  have hnot : ¬ p ∣ Fintype.card ↥S := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hcard]
    intro h4
    have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime hnot hσ
  refine ⟨a, a.2, ?_⟩
  have := congrArg Subtype.val ha
  rwa [show ((σ a : ↥S) : G) = d * a * d⁻¹ from rfl] at this

theorem exists_odd_prime_order_pow [Finite G] {x : G} (h : ∀ k : ℕ, orderOf x ≠ 2 ^ k) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ orderOf (x ^ (orderOf x / p)) = p := by
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm1 : m ≠ 1 := fun h1 => h k (by rw [hkm, h1, mul_one])
  refine ⟨m.minFac, Nat.minFac_prime hm1, ?_, orderOf_pow_orderOf_div hn ?_⟩
  · intro h2
    have : 2 ∣ m := h2 ▸ Nat.minFac_dvd m
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr this)
  · rw [hkm]
    exact Dvd.dvd.mul_left (Nat.minFac_dvd m) _

theorem mem_normalizer_of_conj_le [Finite G] {A : Subgroup G} {g : G}
    (h : ∀ x ∈ A, g⁻¹ * x * g ∈ A) : g ∈ Subgroup.normalizer (A : Set G) := by
  have hle : A ≤ conjSubgroup A g⁻¹ := fun x hx => mem_conjSubgroup_iff.mpr (by simpa using h x hx)
  have heq := Subgroup.eq_of_le_of_card_ge hle (CFSG.QuasithinUnique.C5.card_conjSubgroup A g⁻¹).le
  have : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp heq.symm
  simpa using (Subgroup.normalizer (A : Set G)).inv_mem this

theorem mem_normalizer_inf_centralizer {V W : Subgroup G} {d : G}
    (hV : d ∈ Subgroup.normalizer (V : Set G)) (hW : d ∈ Subgroup.normalizer (W : Set G)) :
    d ∈ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer] at hV hW ⊢
  rw [CFSG.QuasithinUnique.C5.conjSubgroup_inf, CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
    hV, hW]

theorem mul_mem_of_relIndex_eq_two {A B : Subgroup G} (h2 : A.relIndex B = 2) {x y : G}
    (hx : x ∈ B) (hy : y ∈ B) (hxA : x ∉ A) (hyA : y ∉ A) : x * y ∈ A := by
  have := (Subgroup.mul_mem_iff_of_index_two (H := A.subgroupOf B) h2
    (a := (⟨x, hx⟩ : ↥B)) (b := ⟨y, hy⟩)).2 (by
      simp only [Subgroup.mem_subgroupOf]
      exact iff_of_false hxA hyA)
  simpa [Subgroup.mem_subgroupOf] using this

end CFSG.Quasithin.H13.GM22.CaseA3
