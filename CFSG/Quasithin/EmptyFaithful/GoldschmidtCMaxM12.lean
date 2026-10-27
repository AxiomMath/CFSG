module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxMBound
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxM12Lat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M12Pairs

namespace GoldCMax

theorem eq_of_mem_zpowers_orderOf_two {G : Type*} [Group G] {z x : G} (hz : orderOf z = 2)
    (hx : x ∈ Subgroup.zpowers z) (hx1 : x ≠ 1) : x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h := zpow_mod_orderOf z k
  rw [hz, Nat.cast_ofNat] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at h
    exact absurd h.symm hx1
  · rw [h1, zpow_one] at h
    exact h.symm

theorem normalizer_zpowers_le_centralizer {G : Type*} [Group G] {z : G} (hz : orderOf z = 2) :
    Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({z} : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg
  have hzA : g * z * g⁻¹ ∈ Subgroup.zpowers z := (hg z).mp (Subgroup.mem_zpowers z)
  have hne : g * z * g⁻¹ ≠ 1 := by
    intro h
    have : z = 1 := by simpa using h
    rw [this, orderOf_one] at hz
    omega
  have h := eq_of_mem_zpowers_orderOf_two hz hzA hne
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h]

theorem m12_sylow_data :
    ∃ (S₀ : Subgroup X12) (z : X12), IsPGroup 2 ↥S₀ ∧ ¬ 2 ∣ S₀.index ∧ orderOf z = 2 ∧
      centerOf S₀ = Subgroup.zpowers z ∧
      Nat.card (Subgroup.centralizer ({z} : Set X12)) = 192 := by
  obtain ⟨hlen, hnd, h1, hmul, hpow⟩ := s0_facts
  obtain ⟨hA1len, -⟩ := a_facts
  obtain ⟨hK1len, hK1nd, hK1n, hK1c⟩ := k1_facts
  obtain ⟨-, hQ1nd, hQ1K, hQ11, hQ1mul, hQ1norm, hQ1pow, hQ1cent, hQ1A3, hQ1r⟩ := q1_facts
  obtain ⟨S₀, hS₀⟩ := subgroupOfList_exists S0X h1 hmul
  have hS₀card : Nat.card ↥S₀ = 64 := by rw [card_of_list hnd hS₀, hlen]
  have hS₀2 : IsPGroup 2 S₀ := fun g => ⟨6, Subtype.ext (hpow _ ((hS₀ _).1 g.2))⟩
  have hXcard : Nat.card X12 = 95040 := CFSG.Sporadic.Schreier.m12_card
  have hS₀i : ¬ 2 ∣ S₀.index := by
    have h := Subgroup.card_mul_index S₀
    rw [hS₀card, hXcard] at h
    have : S₀.index = 1485 := by omega
    rw [this]
    omega
  have hA₁ : ∀ y, y ∈ canonZ S₀ ↔ y ∈ A1X := by
    intro y
    simp only [mem_canonZ, hS₀, A1X, List.mem_filter, List.all_eq_true, beq_iff_eq]
  have hAcard : Nat.card ↥(canonZ S₀) = 2 :=
    (card_of_list (hnd.filter _) hA₁).trans hA1len
  obtain ⟨-, hcard₁, -⟩ := side_data (canonZ S₀) A1X hA₁ K1X hK1nd hK1n hK1c Q1X hQ1nd hQ1K hQ11
    hQ1mul hQ1norm hQ1pow hQ1cent hQ1A3 hQ1r
  have hnt : Nontrivial ↥(canonZ S₀) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥(canonZ S₀))
  set z : X12 := (a : X12) with hzdef
  have hz1 : z ≠ 1 := fun h => ha (Subtype.ext h)
  have hz2 : orderOf z = 2 := by
    have hd : orderOf z ∣ 2 := by
      rw [show orderOf z = orderOf a from Subgroup.orderOf_coe a, ← hAcard]
      exact orderOf_dvd_natCard a
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hcen : canonZ S₀ = Subgroup.zpowers z := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a.2) ?_
    rw [hAcard, Nat.card_zpowers, hz2]
  refine ⟨S₀, z, hS₀2, hS₀i, hz2, hcen, ?_⟩
  have hle : Subgroup.centralizer ({z} : Set X12) ≤
      Subgroup.normalizer ((canonZ S₀ : Subgroup X12) : Set X12) := by
    rw [hcen, ← centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  have hge : Subgroup.normalizer ((canonZ S₀ : Subgroup X12) : Set X12) ≤
      Subgroup.centralizer ({z} : Set X12) := by
    rw [hcen]
    exact normalizer_zpowers_le_centralizer hz2
  rw [le_antisymm hle hge, hcard₁, hK1len]

end GoldCMax

open GoldCMax in
theorem centMaxProp_m12 :
    CentMaxProp X12 := by
  obtain ⟨S₀, z, hS₀2, hS₀i, hz2, hcen, hcard⟩ := m12_sylow_data
  have hSC : S₀ ≤ Subgroup.centralizer ({z} : Set X12) := by
    intro s hs
    have hz : z ∈ centerOf S₀ := hcen ▸ Subgroup.mem_zpowers z
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hz.2 s hs
  have hne : Subgroup.centralizer ({z} : Set X12) ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, CFSG.Sporadic.Schreier.m12_card] at hcard
    omega
  refine centMaxProp_of_data hS₀2 hS₀i hz2 hcen ?_
  exact isMaxSubgroupIn_of_overgroup_bound (B := 192) hne hcard.ge fun Y hY =>
    m12_overgroup_bound hS₀2 hS₀i (hSC.trans hY)

theorem centMax_m12
    (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q)
    (hP2 : IsPGroup 2 ↥P) (hPi : ¬ 2 ∣ P.index) (hQ : IsSporadic .M12 Q) (W : Subgroup Q)
    (hW : W ≤ centerOf P) (hW0 : W ≠ ⊥) :
    IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q)) := by
  obtain ⟨e⟩ := hQ
  exact (centMaxProp_m12.of_mulEquiv e.symm) P hP2 hPi W hW hW0

end CFSG.Quasithin
