module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeFrobenius
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeAlgebraCyclic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldAlgebra

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

open CFSG.Open in
theorem field_prime_fixed_structure {G : Type*} [Group G] [Finite G] {Q X : Subgroup G} {e : ℕ}
    (hQ : IsElemAbelian 2 Q) (hQcard : Nat.card Q = 2 ^ e) (he : 1 ≤ e)
    (hXQ : ∀ x ∈ X, ∀ v ∈ Q, x⁻¹ * v * x ∈ Q) (hXcyclic : IsCyclic X)
    (hXcard : Nat.card X = Nat.card Q - 1)
    (hXregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b)
    {p : ℕ} (hp : p.Prime) {y : G} (hy : orderOf y = p)
    (hyQ : ∀ v ∈ Q, y⁻¹ * v * y ∈ Q) (hyX : ∀ x ∈ X, y⁻¹ * x * y ∈ X)
    (hXy : ¬ X ≤ Subgroup.centralizer ({y} : Set G)) :
    let E := Q ⊓ Subgroup.centralizer ({y} : Set G)
    let X₀ := X ⊓ Subgroup.centralizer ({y} : Set G)
    p ∣ e ∧ Nat.card E = 2 ^ (e / p) ∧ IsCyclic X₀ ∧ Nat.card X₀ = 2 ^ (e / p) - 1 ∧
      (∀ a ∈ (E : Set G) \ {1}, ∀ b ∈ (E : Set G) \ {1}, ∃! x : X₀, (x : G)⁻¹ * a * x = b) ∧
      (∀ c ∈ X, (y * c) ^ p = 1 → ∃ x ∈ X, x⁻¹ * (y * c) * x = y) := by
  intro E X₀
  obtain ⟨j, hj⟩ := exists_two_pow_conj_eq hQ hQcard he hXQ hXcyclic hXregular hyQ hyX
  have hn : Nat.card X = 2 ^ e - 1 := by rw [hXcard, hQcard]
  have hyp : y ^ p = 1 := hy ▸ pow_orderOf_eq_one y
  have hXord : ∀ x ∈ X, x ^ (2 ^ e - 1) = 1 := fun x hx => by
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : X))
    rw [hn] at h
    simpa using congrArg Subtype.val h
  have hjm : ∀ m, ∀ x ∈ X, (y ^ m)⁻¹ * x * y ^ m = x ^ (2 ^ (j * m)) := by
    intro m
    induction m with
    | zero => intro x _; simp
    | succ m ih =>
      intro x hx
      calc (y ^ (m + 1))⁻¹ * x * y ^ (m + 1) = y⁻¹ * ((y ^ m)⁻¹ * x * y ^ m) * y := by group
        _ = (y⁻¹ * x * y) ^ (2 ^ (j * m)) := by rw [ih x hx, inv_mul_pow_mul]
        _ = x ^ (2 ^ (j * (m + 1))) := by
          rw [hj x hx, ← pow_mul, ← pow_add, mul_add, mul_one, add_comm]
  obtain ⟨ξ, hξ⟩ := IsCyclic.exists_generator (α := X)
  have hξord : orderOf (ξ : G) = 2 ^ e - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hξ, hn]
  have hejp : e ∣ j * p := by
    have h := hjm p ξ ξ.2
    rw [hyp, inv_one, one_mul, mul_one, eq_comm, pow_two_pow_eq_self_iff] at h
    rw [← two_pow_sub_one_dvd_iff, ← hξord]
    exact orderOf_dvd_of_pow_eq_one h
  have hej : ¬ e ∣ j := by
    intro hdvd
    apply hXy
    intro x hx
    apply mem_centralizer_of_conj_eq
    rw [hj x hx, pow_two_pow_eq_self_iff]
    obtain ⟨r, hr⟩ := two_pow_sub_one_dvd_iff.mpr hdvd
    rw [hr, pow_mul, hXord x hx, one_pow]
  obtain ⟨hpe, hgcd⟩ := prime_dvd_and_gcd_eq hp (by omega) hejp hej
  set f := e / p
  have hef : e = f * p := (Nat.div_mul_cancel hpe).symm
  have hfpos : 0 < f := Nat.div_pos (Nat.le_of_dvd (by omega) hpe) hp.pos
  obtain ⟨s, hs⟩ : f ∣ j := hgcd ▸ Nat.gcd_dvd_left j e
  have hsp : s.Coprime p := by
    have h := hgcd
    rw [hs, hef, Nat.gcd_mul_left] at h
    exact Nat.eq_of_mul_eq_mul_left hfpos (h.trans (mul_one f).symm)
  have hgcd' : Nat.gcd (Nat.card X) (2 ^ j - 1) = 2 ^ f - 1 := by
    rw [hn, Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_comm, hgcd]
  have hcent : ∀ x ∈ X, x ∈ Subgroup.centralizer ({y} : Set G) ↔ x ^ (2 ^ j - 1) = 1 := by
    intro x hx
    rw [← pow_two_pow_eq_self_iff, ← hj x hx]
    exact ⟨conj_eq_of_mem_centralizer, mem_centralizer_of_conj_eq⟩
  have hX₀card : Nat.card X₀ = 2 ^ f - 1 := by
    rw [← hgcd', ← card_pow_eq_one_eq_gcd (A := X)]
    exact Nat.card_congr
      { toFun := fun x => ⟨⟨x, x.2.1⟩, Subtype.ext ((hcent x x.2.1).mp x.2.2)⟩
        invFun := fun x => ⟨x.1, x.1.2, (hcent x.1 x.1.2).mpr (congrArg Subtype.val x.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hpowS : ∀ c ∈ X, ∀ m,
      (y * c) ^ m = y ^ m * c ^ (∑ k ∈ Finset.range m, 2 ^ (j * k)) := by
    intro c hc m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsum : ∑ k ∈ Finset.range (m + 1), 2 ^ (j * k) =
          (∑ k ∈ Finset.range m, 2 ^ (j * k)) * 2 ^ j + 1 := by
        rw [Finset.sum_range_succ', Finset.sum_mul]
        simp only [mul_add, mul_one, pow_add, mul_zero, pow_zero]
      have hcS := hj _ (X.pow_mem hc (∑ k ∈ Finset.range m, 2 ^ (j * k)))
      calc (y * c) ^ (m + 1) = y ^ m * y *
            (y⁻¹ * c ^ (∑ k ∈ Finset.range m, 2 ^ (j * k)) * y) * c := by
            rw [pow_succ, ih]
            group
        _ = y ^ (m + 1) * c ^ (∑ k ∈ Finset.range (m + 1), 2 ^ (j * k)) := by
            rw [hcS, hsum, pow_succ c, pow_mul, pow_succ y]
            simp only [mul_assoc]
  have hnorm : ∀ c ∈ X, (y * c) ^ p = c ^ (∑ k ∈ Finset.range p, 2 ^ (f * k)) := by
    intro c hc
    rw [hpowS c hc p, hyp, one_mul, pow_eq_pow_iff_modEq]
    refine Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one (hXord c hc)) ?_
    rw [hs, hef]
    exact sum_two_pow_mul_modEq hp.one_lt hsp
  have hH90 : ∀ c ∈ X, (y * c) ^ p = 1 → ∃ x ∈ X, x⁻¹ * (y * c) * x = y := by
    intro c hc hcp
    rw [hnorm c hc] at hcp
    have hM := sum_two_pow_mul_sub_one f p
    obtain ⟨⟨x, hxX⟩, hx⟩ := exists_pow_eq_of_pow_eq_one (A := X) (c := ⟨c, hc⟩)
      (by rw [hn, hef, ← hM, mul_comm]) hgcd' (Subtype.ext (by simpa using hcp))
    refine ⟨x, hxX, ?_⟩
    have hx' : x ^ (2 ^ j - 1) = c := by simpa using congrArg Subtype.val hx
    have h1 : y⁻¹ * x * y = c * x := by
      rw [hj x hxX, ← hx', pow_sub_one_mul (pow_ne_zero j two_ne_zero)]
    calc x⁻¹ * (y * c) * x = x⁻¹ * y * (c * x) := by group
      _ = x⁻¹ * y * (y⁻¹ * x * y) := by rw [h1]
      _ = y := by group
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hQcard]
    exact Nat.one_lt_two_pow (by omega))
  obtain ⟨⟨v₀, hv₀Q⟩, hv₀1⟩ := exists_ne (1 : Q)
  have hv₀ : v₀ ∈ (Q : Set G) \ {1} := ⟨hv₀Q, fun h => hv₀1 (Subtype.ext h)⟩
  obtain ⟨d, hd, -⟩ := hXregular v₀ hv₀ _ ⟨hyQ v₀ hv₀Q, conj_ne_one hv₀.2⟩
  have hc : (d : G)⁻¹ ∈ X := X.inv_mem d.2
  have hcv : (y * (d : G)⁻¹)⁻¹ * v₀ * (y * (d : G)⁻¹) = v₀ := by
    calc (y * (d : G)⁻¹)⁻¹ * v₀ * (y * (d : G)⁻¹) = d * (y⁻¹ * v₀ * y) * (d : G)⁻¹ := by group
      _ = v₀ := by rw [← hd]; group
  have hcomm : Commute v₀ (y * (d : G)⁻¹) := by
    calc v₀ * (y * (d : G)⁻¹) = (y * (d : G)⁻¹) * ((y * (d : G)⁻¹)⁻¹ * v₀ * (y * (d : G)⁻¹)) := by
          group
      _ = (y * (d : G)⁻¹) * v₀ := by rw [hcv]
  have hpX : (y * (d : G)⁻¹) ^ p ∈ X := by
    rw [hnorm _ hc]
    exact X.pow_mem hc _
  have hp1 : (y * (d : G)⁻¹) ^ p = 1 := by
    obtain ⟨z, -, hz⟩ := hXregular v₀ hv₀ v₀ hv₀
    have e1 := hz ⟨_, hpX⟩ (by
      change ((y * (d : G)⁻¹) ^ p)⁻¹ * v₀ * (y * (d : G)⁻¹) ^ p = v₀
      rw [mul_assoc, (hcomm.pow_right p).eq, inv_mul_cancel_left])
    have e2 := hz 1 (by simp)
    exact congrArg Subtype.val (e1.trans e2.symm)
  obtain ⟨x, hxX, hx⟩ := hH90 _ hc hp1
  have hwE : x⁻¹ * v₀ * x ∈ (E : Set G) \ {1} := by
    refine ⟨⟨hXQ x hxX v₀ hv₀Q, mem_centralizer_of_conj_eq ?_⟩, conj_ne_one hv₀.2⟩
    calc y⁻¹ * (x⁻¹ * v₀ * x) * y = (x⁻¹ * (y * (d : G)⁻¹) * x)⁻¹ * (x⁻¹ * v₀ * x) *
          (x⁻¹ * (y * (d : G)⁻¹) * x) := by rw [hx]
      _ = x⁻¹ * ((y * (d : G)⁻¹)⁻¹ * v₀ * (y * (d : G)⁻¹)) * x := by group
      _ = x⁻¹ * v₀ * x := by rw [hcv]
  have hreg := regular_restrict (Q := Q) hyX hXregular
  have hSE : ∀ x ∈ X₀, ∀ a ∈ (E : Set G) \ {1}, x⁻¹ * a * x ∈ (E : Set G) \ {1} := by
    intro x hx a ha
    refine ⟨⟨hXQ x hx.1 a ha.1.1, ?_⟩, conj_ne_one ha.2⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx.2) ha.1.2) hx.2
  have hE : Nat.card X₀ = Nat.card E - 1 := by
    rw [card_eq_of_regular hSE hreg hwE, card_diff_one]
  have hEcard : Nat.card E = 2 ^ f := by
    have hpos : 0 < Nat.card E := Nat.card_pos
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  exact ⟨hpe, hEcard, Subgroup.isCyclic_of_le inf_le_left, hX₀card, hreg, hH90⟩

theorem field_prime_parameter_bounds {p e : ℕ} (hp : p.Prime) (hpe : p ∣ e) (he : 1 ≤ e)
    (hpq : p ∣ 2 ^ e - 1) : p ≠ 2 ∧ p ∣ 2 ^ (e / p) - 1 ∧ 4 ≤ 2 ^ (e / p) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (odd_two_pow_sub_one he)) (even_iff_two_dvd.mpr hpq)
  obtain ⟨f, rfl⟩ := hpe
  rw [Nat.mul_div_cancel_left f hp.pos]
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at he
    · exact h
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ 2 ^ f - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero] at hpq ⊢
    push_cast at hpq ⊢
    rwa [pow_mul, ZMod.pow_card] at hpq
  refine ⟨hp2, hdvd, ?_⟩
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := Nat.le_of_dvd (by omega) hdvd
  omega

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
