module

public import CFSG.Quasithin.Recognition.CertSzZero

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped Pointwise

namespace F112T

theorem exists_normal_five {X : Type} [Group X] [Finite X] (hcard : Nat.card X = 20) :
    ∃ N : Subgroup X, N.Normal ∧ Nat.card N = 5 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 X) := inferInstance
  have hPcard : Nat.card (P : Subgroup X) = 5 := by
    rw [P.card_eq_multiplicity, hcard]
    have : (20 : ℕ).factorization 5 = 1 := by
      have h20 : (20 : ℕ) = 5 * 4 := by norm_num
      rw [h20, Nat.factorization_mul (by norm_num) (by norm_num)]
      have h4 : (4 : ℕ).factorization 5 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)
      simp [h4, Nat.Prime.factorization_self Nat.prime_five]
    rw [this]
    norm_num
  have hidx : (P : Subgroup X).index = 4 := by
    have := (P : Subgroup X).card_mul_index
    rw [hPcard, hcard] at this
    omega
  have hn5 : Nat.card (Sylow 5 X) = 1 := by
    have h1 := card_sylow_modEq_one 5 X
    have h2 := P.card_dvd_index
    rw [hidx] at h2
    have hle : Nat.card (Sylow 5 X) ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    have hpos : 0 < Nat.card (Sylow 5 X) := Nat.card_pos
    unfold Nat.ModEq at h1
    interval_cases h : Nat.card (Sylow 5 X) <;> simp_all
  have hsub : Subsingleton (Sylow 5 X) := by
    have : Nat.card (Sylow 5 X) ≤ 1 := hn5.le
    exact (Finite.card_le_one_iff_subsingleton).mp (by simpa [Nat.card_eq_fintype_card] using this)
  exact ⟨P, Sylow.normal_of_subsingleton P, hPcard⟩

theorem cent_or_inv_of_order_five {X : Type} [Group X] {N : Subgroup X} [N.Normal] (hN : Nat.card N = 5)
    (a : X) (ha : a * a = 1) :
    (∀ n ∈ N, a * n * a⁻¹ = n) ∨ (∀ n ∈ N, a * n * a⁻¹ = n⁻¹) := by
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcyc : IsCyclic N := isCyclic_of_prime_card hN
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = 5 := by
    have h1 := Nat.card_zpowers g
    have h2 : Subgroup.zpowers g = ⊤ := Subgroup.eq_top_iff' _ |>.mpr hg
    rw [h2, Subgroup.card_top, hN] at h1
    exact h1.symm
  set n₀ : X := (g : X) with hn₀
  have hn₀ord : orderOf n₀ = 5 := by rw [hn₀, Subgroup.orderOf_coe, hord]
  have hn₀N : n₀ ∈ N := g.2
  have hσN : a * n₀ * a⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n₀ hn₀N a
  obtain ⟨k, hk⟩ := hg ⟨a * n₀ * a⁻¹, hσN⟩
  have hk' : n₀ ^ k = a * n₀ * a⁻¹ := by
    have := congrArg Subtype.val hk
    simpa [hn₀] using this
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hsq : n₀ ^ (k * k) = n₀ := by
    have e1 : a * (a * n₀ * a⁻¹) * a⁻¹ = n₀ := by
      calc a * (a * n₀ * a⁻¹) * a⁻¹ = (a * a) * n₀ * (a⁻¹ * a⁻¹) := by group
        _ = n₀ := by rw [ha, ← mul_inv_rev, ha, inv_one]; simp
    calc n₀ ^ (k * k) = (n₀ ^ k) ^ k := zpow_mul _ _ _
      _ = (a * n₀ * a⁻¹) ^ k := by rw [← hk']
      _ = a * n₀ ^ k * a⁻¹ := conj_zpow
      _ = a * (a * n₀ * a⁻¹) * a⁻¹ := by rw [hk']
      _ = n₀ := e1
  have hdvd : (5 : ℤ) ∣ k * k - 1 := by
    have h1 : n₀ ^ (k * k - 1) = 1 := by
      rw [zpow_sub, zpow_one, hsq, mul_inv_cancel]
    have := (orderOf_dvd_iff_zpow_eq_one (x := n₀) (i := k * k - 1)).mpr h1
    rwa [hn₀ord] at this
  have hmod : k % 5 = 1 ∨ k % 5 = 4 := by
    have h1 : (k * k) % 5 = 1 := by omega
    have h2 : (k % 5) * (k % 5) % 5 = 1 := by rw [← Int.mul_emod]; exact h1
    have h3 : 0 ≤ k % 5 := Int.emod_nonneg _ (by norm_num)
    have h4 : k % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
    generalize k % 5 = r at *
    interval_cases r <;> simp_all
  have hpow5 : n₀ ^ (5 : ℤ) = 1 := by
    have := pow_orderOf_eq_one n₀
    rw [hn₀ord] at this
    exact_mod_cast this
  have hkmod : n₀ ^ k = n₀ ^ (k % 5) := by
    have := zpow_mod_orderOf n₀ k
    rw [hn₀ord] at this
    exact_mod_cast this.symm
  have hmem : ∀ n ∈ N, ∃ m : ℤ, n₀ ^ m = n := by
    intro n hn
    obtain ⟨m, hm⟩ := hg ⟨n, hn⟩
    exact ⟨m, by simpa [hn₀] using congrArg Subtype.val hm⟩
  rcases hmod with h1 | h4
  · left
    intro n hn
    obtain ⟨m, rfl⟩ := hmem n hn
    have hc : a * n₀ * a⁻¹ = n₀ := by rw [← hk', hkmod, h1, zpow_one]
    calc a * n₀ ^ m * a⁻¹ = (a * n₀ * a⁻¹) ^ m := conj_zpow.symm
      _ = n₀ ^ m := by rw [hc]
  · right
    intro n hn
    obtain ⟨m, rfl⟩ := hmem n hn
    have hc : a * n₀ * a⁻¹ = n₀⁻¹ := by
      rw [← hk', hkmod, h4]
      have : n₀ ^ (4 : ℤ) * n₀ = 1 := by
        rw [← zpow_add_one, show (4 : ℤ) + 1 = 5 by norm_num, hpow5]
      exact (eq_inv_of_mul_eq_one_left this)
    calc a * n₀ ^ m * a⁻¹ = (a * n₀ * a⁻¹) ^ m := conj_zpow.symm
      _ = (n₀ ^ m)⁻¹ := by rw [hc, inv_zpow]

theorem card_le_two_of_order_twenty {X : Type} [Group X] [Finite X] (hcard : Nat.card X = 20)
    (hO : CFSG.Open.pCore 2 X = ⊥) (E : Subgroup X) (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by
    simp only [pow_one, Subgroup.coe_one, sq]
    exact hE g g.2)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hdvd : Nat.card E ∣ 20 := hcard ▸ Subgroup.card_subgroup_dvd_card E
  have hEc : Nat.card E = 4 := by
    rw [hn] at hdvd hlt ⊢
    have h20 : 2 ^ n ≤ 20 := Nat.le_of_dvd (by norm_num) hdvd
    have hn5 : n < 5 := by
      by_contra h
      push Not at h
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h
      omega
    interval_cases n <;> simp_all
  obtain ⟨N, hNn, hN⟩ := exists_normal_five hcard
  have hdisj : Disjoint N E :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hN, hEc]; norm_num)
  have hcomp : N.IsComplement' E :=
    Subgroup.isComplement'_iff_card_mul_and_disjoint.mpr ⟨by rw [hN, hEc, hcard], hdisj⟩
  have hcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := by
    intro e he f hf
    have h1 := hE (e * f) (E.mul_mem he hf)
    have h2 := inv_eq_of_mul_eq_one_right (hE e he)
    have h3 := inv_eq_of_mul_eq_one_right (hE f hf)
    calc e * f = (e * f)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = f⁻¹ * e⁻¹ := mul_inv_rev _ _
      _ = f * e := by rw [h2, h3]
  have hne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEc
    omega
  obtain ⟨e', he1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have he : (e' : X) ∈ E := e'.2
  have he1 : (e' : X) ≠ 1 := fun h => he1' (Subtype.ext h)
  have hf : ∃ f ∈ E, f ≠ 1 ∧ f ≠ (e' : X) := by
    by_contra hcon
    push Not at hcon
    have hsub : (E : Set X) ⊆ {1, (e' : X)} := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hcon x hx hx1)
    have h1 : Nat.card E ≤ 2 := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({1, (e' : X)} : Set X).ncard ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
      have h3 : Nat.card E = (E : Set X).ncard := Nat.card_coe_set_eq (E : Set X)
      rw [h3]
      exact le_trans this h2
    omega
  obtain ⟨f, hfE, hf1, hfe⟩ := hf
  have hw : ∃ w ∈ E, w ≠ 1 ∧ ∀ n ∈ N, w * n = n * w := by
    rcases cent_or_inv_of_order_five hN (e' : X) (hE _ he) with hce | hie
    · refine ⟨(e' : X), he, he1, fun n hn => ?_⟩
      have := hce n hn
      calc (e' : X) * n = ((e' : X) * n * (e' : X)⁻¹) * e' := by group
        _ = n * e' := by rw [this]
    rcases cent_or_inv_of_order_five hN f (hE f hfE) with hcf | hif
    · refine ⟨f, hfE, hf1, fun n hn => ?_⟩
      have := hcf n hn
      calc f * n = (f * n * f⁻¹) * f := by group
        _ = n * f := by rw [this]
    · refine ⟨(e' : X) * f, E.mul_mem he hfE, ?_, fun n hn => ?_⟩
      · intro h
        apply hfe
        have h2 := inv_eq_of_mul_eq_one_right h
        have h3 := inv_eq_of_mul_eq_one_right (hE _ he)
        exact h2.symm.trans h3
      · have hn' : n⁻¹ ∈ N := N.inv_mem hn
        have hfn : f * n * f⁻¹ = n⁻¹ := hif n hn
        have hen : (e' : X) * n⁻¹ * (e' : X)⁻¹ = (n⁻¹)⁻¹ := hie n⁻¹ hn'
        have h5 : ((e' : X) * f) * n * ((e' : X) * f)⁻¹ = n := by
          calc ((e' : X) * f) * n * ((e' : X) * f)⁻¹
              = e' * (f * n * f⁻¹) * (e' : X)⁻¹ := by group
            _ = e' * n⁻¹ * (e' : X)⁻¹ := by rw [hfn]
            _ = (n⁻¹)⁻¹ := hen
            _ = n := inv_inv n
        calc ((e' : X) * f) * n = (((e' : X) * f) * n * ((e' : X) * f)⁻¹) * ((e' : X) * f) := by group
          _ = n * ((e' : X) * f) := by rw [h5]
  obtain ⟨w, hwE, hw1, hwN⟩ := hw
  have hwc : ∀ x : X, w * x = x * w := by
    intro x
    have hx : x ∈ ((N : Set X) * (E : Set X)) := by rw [hcomp.mul_eq]; trivial
    obtain ⟨n, hn, e₀, he₀, rfl⟩ := Set.mem_mul.mp hx
    calc w * (n * e₀) = (w * n) * e₀ := by group
      _ = (n * w) * e₀ := by rw [hwN n hn]
      _ = n * (w * e₀) := by group
      _ = n * (e₀ * w) := by rw [hcomm w hwE e₀ he₀]
      _ = (n * e₀) * w := by group
  have hKn : (Subgroup.zpowers w).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute w g := hwc g
    have h1 : g * w ^ k = w ^ k * g := ((Commute.zpow_left hc k).eq).symm
    have : g * w ^ k * g⁻¹ = w ^ k := by rw [h1]; group
    rw [show g * w ^ k * g⁻¹ = w ^ k from this]
    exact Subgroup.zpow_mem_zpowers w k
  have hKE : Subgroup.zpowers w ≤ E := (Subgroup.zpowers_le).mpr hwE
  have hKp : IsPGroup 2 (Subgroup.zpowers w) := fun g => ⟨1, Subtype.ext (by
    simp only [pow_one, Subgroup.coe_one, sq]
    exact hE g (hKE g.2))⟩
  have hle : Subgroup.zpowers w ≤ CFSG.Open.pCore 2 X := le_pCore 2 hKn hKp
  rw [hO] at hle
  exact hw1 (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers w)))

@[expose] def ElemAbSmall (X : Type*) [Group X] : Prop :=
  ∀ E : Subgroup X, (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2

theorem ElemAbSmall.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : ElemAbSmall Y) :
    ElemAbSmall X := by
  intro E hE
  have h1 := h (E.map e.toMonoidHom) (by
    rintro _ ⟨x, hx, rfl⟩
    show e x * e x = 1
    rw [← map_mul, hE x hx, map_one])
  rwa [← Nat.card_congr (Subgroup.equivMapOfInjective E e.toMonoidHom e.injective).toEquiv] at h1

theorem ElemAbSmall.of_sz {X : Type*} [Group X] (e : X ≃* ↥(Sz 0)) : ElemAbSmall X := by
  have hfin : Finite ↥(Sz 0) := Nat.finite_of_card_ne_zero (by rw [card_sz_zero_eq_twenty]; norm_num)
  exact ElemAbSmall.of_mulEquiv e (fun E hE =>
    card_le_two_of_order_twenty card_sz_zero_eq_twenty pCore_two_sz_zero_eq_bot E hE)

end F112T

end CFSG.Quasithin
