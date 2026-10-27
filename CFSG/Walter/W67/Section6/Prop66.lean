module

public import CFSG.Walter.W67.Section6.Lemma61
public import CFSG.Walter.W67.Section6.Core62A

public section

namespace CFSG.Walter.W67

namespace Sec6

variable {G : Type} [Group G] [Finite G] (s : Std G)

theorem isCyclic_of_le_L
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts)
    (hcyc : ∀ (L : Type) [Group L] [Finite L] (hL : JRGroup L), hL.q ≠ 5 →
      ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ 3 → ∀ P : Sylow p L, IsCyclic (P : Subgroup L))
    {r : ℕ} [Fact r.Prime] (hrσ : r ∈ s.fr.σ) {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥)
    {P₁ : Subgroup G} (hP₁L : P₁ ≤ s.L X)
    (hP₁c : Nat.card P₁ = r ^ (Nat.card (s.L X)).factorization r) : IsCyclic P₁ := by
  obtain ⟨-, -, -, hL, -, -, -, -⟩ := exists_jrGroup s hXE hX
  have hrE : r ∣ Nat.card s.fr.E := ((mem_sigma_iff s).mp hrσ).2
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr s.fr.odd_card_E) (even_iff_two_dvd.mpr hrE)
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact not_three_dvd_card_E s h41 h56 hJ hR hrE
  have e := Subgroup.subgroupOfEquivOfLe hP₁L
  have hQc : Nat.card (P₁.subgroupOf (s.L X)) = r ^ (Nat.card (s.L X)).factorization r := by
    rw [← hP₁c]
    exact Nat.card_congr e.toEquiv
  set T : Sylow r (s.L X) := Sylow.ofCard _ hQc with hTdef
  have hTQ : (T : Subgroup (s.L X)) = P₁.subgroupOf (s.L X) := Sylow.coe_ofCard _ _
  have hT : IsCyclic (T : Subgroup (s.L X)) := by
    by_cases h5 : hL.q = 5
    · obtain ⟨-, -, ⟨hJE1, -, -⟩, -, -⟩ := hJ _ hL h5
      rcases hJE1 r hr2 T with h | h
      · have : Subsingleton (T : Subgroup (s.L X)) := (Nat.card_eq_one_iff_unique.mp h).1
        infer_instance
      · exact isCyclic_of_prime_card h
    · exact hcyc _ hL h5 r hr2 hr3 T
  rw [hTQ] at hT
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

omit [Finite G] in
theorem omega1_eq_zpowers [Finite G] {r : ℕ} [Fact r.Prime] {P₀ : Subgroup G} (hc : IsCyclic P₀)
    {x₀ : G} (hx₀ : x₀ ∈ P₀) (hxo : orderOf x₀ = r) : omega1 r P₀ = Subgroup.zpowers x₀ := by
  apply le_antisymm
  · rw [omega1, Subgroup.closure_le]
    rintro a ⟨ha, har⟩
    rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp (orderOf_dvd_of_pow_eq_one har) with h1 | h1
    · rw [orderOf_eq_one_iff.mp h1]
      exact Subgroup.one_mem _
    · rw [SetLike.mem_coe, zpowers_eq_of_cyclic hc hx₀ ha (by rw [h1, hxo])]
      exact Subgroup.mem_zpowers a
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure ⟨hx₀, by rw [← hxo, pow_orderOf_eq_one]⟩

theorem exists_omega1
    {r : ℕ} [Fact r.Prime] (hrσ : r ∈ s.fr.σ) {P₀ : Subgroup G}
    (hP₀E : P₀ ≤ s.fr.E) (hP₀c : Nat.card P₀ = r ^ (Nat.card s.fr.E).factorization r) :
    ∃ x₀ ∈ P₀, orderOf x₀ = r ∧ omega1 r P₀ = Subgroup.zpowers x₀ := by
  have hrp : r.Prime := Fact.out
  have hrE : r ∣ Nat.card s.fr.E := ((mem_sigma_iff s).mp hrσ).2
  have hrP : r ∣ Nat.card P₀ := by
    rw [hP₀c]
    exact dvd_pow_self r (hrp.factorization_pos_of_dvd Nat.card_pos.ne' hrE).ne'
  obtain ⟨⟨x₀, hx₀⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := P₀) r hrP
  rw [Subgroup.orderOf_mk] at hxo
  have hc : IsCyclic P₀ := by
    have e := Subgroup.subgroupOfEquivOfLe hP₀E
    have : IsCyclic (P₀.subgroupOf s.fr.E) := by
      have := isCyclic_E s
      infer_instance
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  exact ⟨x₀, hx₀, hxo, omega1_eq_zpowers hc hx₀ hxo⟩

end Sec6

open Sec6

theorem prop_6_6_of
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (h62 : S_lemma_6_2)
    (h65 : S_lemma_6_5) : S_prop_6_6 := by
  intro G _ _ s hJ hR hcyc
  have h1 : 1 < Nat.card s.fr.E := (Subgroup.one_lt_card_iff_ne_bot _).mpr s.E_ne_bot
  set r := (Nat.card s.fr.E).minFac with hr
  have hrp : r.Prime := Nat.minFac_prime h1.ne'
  have : Fact r.Prime := ⟨hrp⟩
  have hrσ : r ∈ s.fr.σ := (mem_sigma_iff s).mpr ⟨hrp, Nat.minFac_dvd _⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow r s.fr.E))
  set P₀ := (Q₀ : Subgroup s.fr.E).map s.fr.E.subtype with hP₀
  have hP₀E : P₀ ≤ s.fr.E := Subgroup.map_subtype_le _
  have hP₀c : Nat.card P₀ = r ^ (Nat.card s.fr.E).factorization r := by
    rw [hP₀, Subgroup.card_map_of_injective s.fr.E.subtype_injective, Sylow.card_eq_multiplicity]
  have hP₀r : IsPGroup r P₀ := IsPGroup.of_card hP₀c
  have hP₀f : (Nat.card P₀).factorization r = (Nat.card s.fr.E).factorization r := by
    rw [hP₀c, hrp.factorization_pow, Finsupp.single_eq_same]
  obtain ⟨x₀, hx₀, hxo, hX⟩ := exists_omega1 s hrσ hP₀E hP₀c
  have hXE : omega1 r P₀ ≤ s.fr.E := by
    rw [hX, Subgroup.zpowers_le]
    exact hP₀E hx₀
  have hX1 : omega1 r P₀ ≠ ⊥ := by
    rw [hX]
    intro h
    have := Nat.card_zpowers x₀
    rw [h, Subgroup.card_bot, hxo] at this
    exact hrp.one_lt.ne this
  have hns := h65 G s hJ hR hrσ P₀ hP₀E hP₀r hP₀f
  obtain ⟨P₀', P₁, hP₀'E, hP₀'c, hP₁L, hP₁c, -, -, hPE, hPL, hPJ, hPcard⟩ :=
    exists_P s h41 h56 hJ hR hrσ hXE hX1 hns
  have hP₀' : P₀' = P₀ := eq_of_le_cyclic (isCyclic_E s) hP₀'E hP₀E (by rw [hP₀'c, hP₀c])
  rw [hP₀'] at hPE hPL hPJ hPcard
  have hPN : P₀ ⊔ P₁ ≤ Subgroup.normalizer ((omega1 r P₀ : Subgroup G) : Set G) := by
    rw [normalizer_eq s hXE hX1]
    exact sup_le (hP₀E.trans le_sup_right) (hP₁L.trans le_sup_left)
  apply h62 G s hJ hR hrσ P₀ hP₀E hP₀r hP₀f hns (P₀ ⊔ P₁) hPN (IsPGroup.of_card hPcard)
    (by rw [hPcard, hrp.factorization_pow, Finsupp.single_eq_same]) hPE hPJ
  rw [hPL]
  exact isCyclic_of_le_L s h41 h56 hJ hR hcyc hrσ hXE hX1 hP₁L hP₁c

end CFSG.Walter.W67
