module

public import CFSG.Quasithin.Background.A3Structure318Star

public section

namespace CFSG.Quasithin.H13.Lem8

theorem nonempty_mulEquiv_starImage {H : Type} [Group H] [Finite H] (L : Subgroup H) [L.Normal]
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∣ 3)
    (h3 : ∃ g : ↥L ⧸ CFSG.pCore 2 ↥L, orderOf g = 3) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(starImage 3 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π' : H →* PStar 3 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 H)
  have hker : CFSG.pCore 2 ↥L ≤ (π'.subgroupMap L).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have h1 : (x : H) ∈ CFSG.pCore 2 H := A318.map_pCore_le_pCore L ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 (A318.pCore_two_le_pPrimeCore (by norm_num) h1)
  let ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(starImage 3 L) :=
    QuotientGroup.lift _ (π'.subgroupMap L) hker
  have hψs : Function.Surjective ψ :=
    QuotientGroup.lift_surjective_of_surjective _ _ (π'.subgroupMap_surjective L) hker
  have hcop : ∀ k ∈ ψ.ker, Nat.Coprime 3 (orderOf k) := by
    intro k hk
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective k
    have hl : (l : H) ∈ CFSG.pPrimeCore 3 H :=
      (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val (MonoidHom.mem_ker.mp hk))
    have h1 : orderOf (⟨l, hl⟩ : CFSG.pPrimeCore 3 H) ∣ Nat.card (CFSG.pPrimeCore 3 H) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at h1
    have h2 : orderOf (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L) ∣ orderOf l :=
      orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) l
    exact Nat.Coprime.coprime_dvd_right (h2.trans h1) CFSG.pPrimeCore_coprime_card
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ ψ.normal_ker with h | h
    · exfalso
      obtain ⟨g, hg⟩ := h3
      have := hcop g (h ▸ Subgroup.mem_top g)
      rw [hg] at this
      norm_num at this
    · rw [eq_bot_iff]
      intro k hk
      have hkz : orderOf (⟨k, h hk⟩ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∣
          Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hkz
      have h1 : orderOf k = 1 := Nat.Coprime.eq_one_of_dvd (hcop k hk).symm (hkz.trans hZ)
      rw [Subgroup.mem_bot]
      exact orderOf_eq_one_iff.mp h1
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hψs⟩⟩

theorem exists_orderOf_eq_three_of_two_le_pRank {Q : Type} [Group Q] [Finite Q]
    (h : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q)) : ∃ g : Q, orderOf g = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup Q)
  have h3 : 3 ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨x, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem eq_closure_image_of_subgroupOf_eq {G : Type*} [Group G] {M L : Subgroup G} (hLM : L ≤ M)
    {S : Set ↥M} (h : L.subgroupOf M = Subgroup.closure S) :
    L = Subgroup.closure (M.subtype '' S) := by
  rw [← MonoidHom.map_closure, ← h, Subgroup.map_subgroupOf_eq_of_le hLM]

theorem image_pElements_three {G : Type*} [Group G] (M : Subgroup G) :
    M.subtype '' {x : ↥M | x ∈ (⊤ : Subgroup ↥M) ∧ ∃ k : ℕ, orderOf x = 3 ^ k} =
      {x : G | x ∈ M ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} := by
  ext x
  constructor
  · rintro ⟨y, ⟨-, k, hk⟩, rfl⟩
    refine ⟨y.2, k, ?_⟩
    have h := pow_orderOf_eq_one y
    rw [hk] at h
    simpa using congrArg Subtype.val h
  · rintro ⟨hx, k, hk⟩
    refine ⟨⟨x, hx⟩, ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
    rw [Subgroup.orderOf_mk]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
    exact ⟨j, hj⟩

theorem image_orderThree {G : Type*} [Group G] (M : Subgroup G) :
    M.subtype '' {x : ↥M | x ∈ (⊤ : Subgroup ↥M) ∧ orderOf x = 3} =
      {x : G | x ∈ M ∧ orderOf x = 3} := by
  ext x
  constructor
  · rintro ⟨y, ⟨-, hy⟩, rfl⟩
    exact ⟨y.2, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]; exact hy⟩
  · rintro ⟨hx, hx3⟩
    exact ⟨⟨x, hx⟩, ⟨Subgroup.mem_top _, by rw [Subgroup.orderOf_mk]; exact hx3⟩, rfl⟩

end CFSG.Quasithin.H13.Lem8
