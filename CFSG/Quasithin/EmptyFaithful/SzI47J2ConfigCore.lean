module

public import CFSG.Quasithin.EmptyFaithful.SzI47J2ConfigAut
public import CFSG.Quasithin.EmptyFaithful.SzI47J2ConfigAct

public section

namespace CFSG.Quasithin.SzI47J2C

theorem conj_mem_closure_oddOrder {G : Type*} [Group G] {X : Subgroup G} {g : G}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {m : G}
    (hm : m ∈ Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, Odd k ∧ x ^ k = 1}) :
    g * m * g⁻¹ ∈ Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, Odd k ∧ x ^ k = 1} := by
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨hxX, k, hk, hxk⟩ := hx
    refine Subgroup.subset_closure ⟨hg x hxX, k, hk, ?_⟩
    rw [conj_pow, hxk]
    group
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem le_closure_oddOrder {G : Type*} [Group G] {X M : Subgroup G} (hMX : M ≤ X)
    (e : ↥M ≃* alternatingGroup (Fin 5)) :
    M ≤ Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, Odd k ∧ x ^ k = 1} := by
  have : Finite ↥M := Finite.of_equiv _ e.symm.toEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimp : IsSimpleGroup ↥M := e.isSimpleGroup_congr.mpr inferInstance
  set K : Subgroup ↥M :=
    (Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, Odd k ∧ x ^ k = 1}).subgroupOf M with hK
  have hKn : K.Normal := ⟨fun n hn g => by
    rw [hK, Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_closure_oddOrder (fun x hx => X.mul_mem (X.mul_mem (hMX g.2) hx)
      (X.inv_mem (hMX g.2))) hn⟩
  have h60 : 3 ∣ Nat.card ↥M := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h60
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxK : x ∈ K := by
    rw [hK, Subgroup.mem_subgroupOf]
    refine Subgroup.subset_closure ⟨hMX x.2, 3, by decide, ?_⟩
    have := congrArg Subtype.val hx3
    simpa using this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · exfalso
    rw [h, Subgroup.mem_bot] at hxK
    rw [hxK, orderOf_one] at hx
    omega
  · intro m hm
    have : (⟨m, hm⟩ : ↥M) ∈ K := by rw [h]; exact Subgroup.mem_top _
    rwa [hK, Subgroup.mem_subgroupOf] at this

theorem mem_of_forall_commute {G : Type*} [Group G] {X M R : Subgroup G} (hMX : M ≤ X)
    (e : ↥M ≃* alternatingGroup (Fin 5)) (hcomm : ∀ r ∈ R, ∀ m ∈ M, r * m = m * r)
    (hXeq : ∀ g ∈ X, ∃ m ∈ M, ∃ r ∈ R, g = m * r) {g : G} (hg : g ∈ X)
    (hcen : ∀ x ∈ X, g * x = x * g) : g ∈ R := by
  obtain ⟨m, hm, r', hr', rfl⟩ := hXeq g hg
  have hmcen : ∀ m' ∈ M, m * m' = m' * m := by
    intro m' hm'
    have h1 := hcen m' (hMX hm')
    have h2 := hcomm r' hr' m' hm'
    have : m * m' * r' = m' * m * r' := by
      calc m * m' * r' = m * (m' * r') := by rw [mul_assoc]
        _ = m * (r' * m') := by rw [h2]
        _ = m * r' * m' := by rw [mul_assoc]
        _ = m' * (m * r') := h1
        _ = m' * m * r' := by rw [mul_assoc]
    exact mul_right_cancel this
  have hm1 : m = 1 := by
    have hc : e ⟨m, hm⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨⟨m', hm'⟩, rfl⟩ := e.surjective a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hmcen m' hm').symm
    rw [alternatingGroup.center_eq_bot (by simp)] at hc
    exact congrArg Subtype.val (e.injective ((Subgroup.mem_bot.mp hc).trans (map_one e).symm))
  rw [hm1, one_mul]
  exact hr'

theorem exists_centralizer_normalizer_of_klein_complement {G : Type*} [Group G] [Finite G]
    {M R X : Subgroup G} {t : G} (hXt : ∀ g : G, g ∈ X ↔ g * t = t * g) (hMX : M ≤ X)
    (e : ↥M ≃* alternatingGroup (Fin 5)) (hcomm : ∀ r ∈ R, ∀ m ∈ M, r * m = m * r)
    (hRcomm : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r)
    (hXeq : ∀ g ∈ X, ∃ m ∈ M, ∃ r ∈ R, g = m * r) (htR : t ∈ R) (ht1 : t ≠ 1)
    (hcard : Nat.card R = 4) (hconj : ∀ r ∈ R, r ≠ 1 → ∃ g : G, g * t * g⁻¹ = r)
    (hodd : ∀ f ∈ X, ∀ n : ℕ, Odd n → f ^ n = 1 → f ∈ M) :
    ∃ y : G, y ∈ Subgroup.centralizer (M : Set G) ∧ y ∈ Subgroup.normalizer (R : Set G) ∧
      y ∉ Subgroup.centralizer (R : Set G) := by
  have htX : t ∈ X := (hXt t).mpr rfl
  have hRX : ∀ r ∈ R, ∀ x ∈ X, r * x = x * r := by
    intro r hr x hx
    obtain ⟨m, hm, r', hr', rfl⟩ := hXeq x hx
    calc r * (m * r') = (r * m) * r' := by rw [mul_assoc]
      _ = (m * r) * r' := by rw [hcomm r hr m hm]
      _ = m * (r * r') := by rw [mul_assoc]
      _ = m * (r' * r) := by rw [hRcomm r hr r' hr']
      _ = m * r' * r := by rw [mul_assoc]
  have hnorm : ∀ r ∈ R, r ≠ 1 → ∃ g ∈ Subgroup.normalizer (R : Set G), g * t * g⁻¹ = r := by
    intro r hr hr1
    obtain ⟨g, hg⟩ := hconj r hr hr1
    refine ⟨g, ?_, hg⟩
    have hX' : ∀ x ∈ X, g⁻¹ * x * g ∈ X := by
      intro x hx
      rw [hXt]
      calc g⁻¹ * x * g * t = g⁻¹ * x * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * (x * r) * g := by rw [hg]; group
        _ = g⁻¹ * (r * x) * g := by rw [hRX r hr x hx]
        _ = (g⁻¹ * r * g) * (g⁻¹ * x * g) := by group
        _ = t * (g⁻¹ * x * g) := by rw [← hg]; group
    have hρ : ∀ ρ ∈ R, g * ρ * g⁻¹ ∈ R := by
      intro ρ hρ
      have hcX : ∀ x ∈ X, g * ρ * g⁻¹ * x = x * (g * ρ * g⁻¹) := by
        intro x hx
        calc g * ρ * g⁻¹ * x = g * (ρ * (g⁻¹ * x * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * x * g) * ρ) * g⁻¹ := by rw [hRX ρ hρ _ (hX' x hx)]
          _ = x * (g * ρ * g⁻¹) := by group
      exact mem_of_forall_commute hMX e hcomm hXeq ((hXt _).mpr (hcX t htX)) hcX
    have : Finite ↥(R : Set G) := inferInstance
    exact Subgroup.mem_normalizer_fintype fun n hn => hρ n hn
  obtain ⟨y₀, hy₀N, n, hn, hy₀n, hy₀t⟩ :=
    exists_odd_pow_eq_one_normalizer_not_comm htR ht1 hcard hnorm
  have hy₀X : ∀ x ∈ X, y₀ * x * y₀⁻¹ ∈ X := by
    intro x hx
    rw [hXt]
    have ht' : y₀⁻¹ * t * y₀ ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy₀N) t).mp htR
      simpa using this
    calc y₀ * x * y₀⁻¹ * t = y₀ * (x * (y₀⁻¹ * t * y₀)) * y₀⁻¹ := by group
      _ = y₀ * ((y₀⁻¹ * t * y₀) * x) * y₀⁻¹ := by rw [hRX _ ht' x hx]
      _ = t * (y₀ * x * y₀⁻¹) := by group
  have hy₀M : ∀ m ∈ M, y₀ * m * y₀⁻¹ ∈ M := by
    intro m hm
    have hOM : Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, Odd k ∧ x ^ k = 1} ≤ M :=
      (Subgroup.closure_le M).mpr fun x ⟨hx, k, hk, hxk⟩ => hodd x hx k hk hxk
    exact hOM (conj_mem_closure_oddOrder hy₀X (le_closure_oddOrder hMX e hm))
  obtain ⟨m₀, hm₀, hinner⟩ := exists_inner_of_odd_pow_eq_one e hy₀M hn hy₀n
  refine ⟨m₀⁻¹ * y₀, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro m hm
    calc m * (m₀⁻¹ * y₀) = m₀⁻¹ * (m₀ * m * m₀⁻¹) * y₀ := by group
      _ = m₀⁻¹ * (y₀ * m * y₀⁻¹) * y₀ := by rw [hinner m hm]
      _ = m₀⁻¹ * y₀ * m := by group
  · have hm₀N : m₀⁻¹ ∈ Subgroup.normalizer (R : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact hcomm r hr m₀⁻¹ (Subgroup.inv_mem _ hm₀)
    exact Subgroup.mul_mem _ hm₀N hy₀N
  · intro h
    have h1 := (Subgroup.mem_centralizer_iff.mp h) t htR
    have h2 := hcomm t htR m₀ hm₀
    have h3 : m₀⁻¹ * t = t * m₀⁻¹ := by
      calc m₀⁻¹ * t = m₀⁻¹ * (t * m₀) * m₀⁻¹ := by group
        _ = m₀⁻¹ * (m₀ * t) * m₀⁻¹ := by rw [h2]
        _ = t * m₀⁻¹ := by group
    have h4 : t * y₀ = y₀ * t := by
      apply mul_left_cancel (a := m₀⁻¹)
      calc m₀⁻¹ * (t * y₀) = (m₀⁻¹ * t) * y₀ := by group
        _ = (t * m₀⁻¹) * y₀ := by rw [h3]
        _ = t * (m₀⁻¹ * y₀) := by group
        _ = m₀⁻¹ * y₀ * t := h1
        _ = m₀⁻¹ * (y₀ * t) := by group
    apply hy₀t
    calc y₀ * t * y₀⁻¹ = t * y₀ * y₀⁻¹ := by rw [h4]
      _ = t := by group

end CFSG.Quasithin.SzI47J2C
