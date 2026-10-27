module

public import CFSG.GroupTheory.SolvableHallNodes

public section

namespace CFSG.Quasithin.H13.L319

open scoped Pointwise

private abbrev G6Hall.pi3 : Set Nat.Primes := {p | p.val ≠ 3}

private abbrev G6Hall.pi5 : Set Nat.Primes := {p | p.val ≠ 2 ∧ p.val ≠ 3}

private lemma G6Hall.mem_pi3 {p : Nat.Primes} : p ∈ G6Hall.pi3 ↔ p.val ≠ 3 := Iff.rfl

private lemma G6Hall.mem_pi5 {p : Nat.Primes} : p ∈ G6Hall.pi5 ↔ p.val ≠ 2 ∧ p.val ≠ 3 :=
  Iff.rfl

private lemma G6Hall.isPiSubgroup_pi3 {S : Type*} [Group S] [Finite S] {T : Subgroup S}
    (hT2 : IsPGroup 2 T) : CFSG.IsPiSubgroup G6Hall.pi3 T := by
  intro p hp
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT2
  rw [hn] at hp
  have hp2 : p.val = 2 :=
    (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).1 (p.2.dvd_of_dvd_pow hp)
  exact G6Hall.mem_pi3.mpr (by rw [hp2]; norm_num)

private lemma G6Hall.coprime_six_of_pi5 {n : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p ≠ 2 ∧ p ≠ 3) : Nat.Coprime n 6 := by
  have h2 : Nat.Coprime n 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact fun hd => (h 2 Nat.prime_two hd).1 rfl
  have h3 : Nat.Coprime n 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact fun hd => (h 3 Nat.prime_three hd).2 rfl
  exact Nat.Coprime.mul_right h2 h3

private lemma G6Hall.card_mul_card_and_coprime {S : Type*} [Group S] [Finite S]
    {E : Subgroup S} (hE : CFSG.IsHallSubgroup G6Hall.pi3 E)
    {T : Subgroup S} (hT2 : IsPGroup 2 T) (hTodd : ¬ 2 ∣ T.index) (hTE : T ≤ E)
    {F₀ : Subgroup E} (hF₀ : CFSG.IsHallSubgroup G6Hall.pi5 F₀) :
    Nat.card F₀ * Nat.card (T.subgroupOf E) = Nat.card E ∧
      Nat.Coprime (Nat.card F₀) (Nat.card (T.subgroupOf E)) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT2
  have hcardT' : Nat.card (T.subgroupOf E) = 2 ^ n :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTE).toEquiv).trans hn
  have hTodd' : ¬ 2 ∣ (T.subgroupOf E).index := fun h => by
    have hrel : (T.subgroupOf E).index ∣ T.index :=
      Subgroup.relIndex_dvd_index_of_le (H := T) (K := E) hTE
    exact hTodd (h.trans hrel)
  have hf2 : ¬ 2 ∣ Nat.card F₀ := fun h =>
    (G6Hall.mem_pi5.mp (hF₀.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h)).1 rfl
  have hcop_tf : Nat.Coprime (Nat.card (T.subgroupOf E)) (Nat.card F₀) := by
    rw [hcardT']
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hf2)
  have hfa : Nat.card F₀ * F₀.index = Nat.card E := Subgroup.card_mul_index F₀
  have htb : Nat.card (T.subgroupOf E) * (T.subgroupOf E).index = Nat.card E :=
    Subgroup.card_mul_index (T.subgroupOf E)
  have hab : Nat.Coprime F₀.index (T.subgroupOf E).index := by
    refine Nat.coprime_of_dvd ?_
    intro q hq hqa hqb
    have hqE : q ∣ Nat.card E := by
      rw [← hfa]
      exact Dvd.dvd.mul_left hqa _
    have h3 : q ≠ 3 := G6Hall.mem_pi3.mp (hE.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqE)
    have h5 : ¬ (q ≠ 2 ∧ q ≠ 3) := fun h =>
      hF₀.p_in_pi_of_p_dvd_index ⟨q, hq⟩ hqa (G6Hall.mem_pi5.mpr h)
    have hq2 : q = 2 := by
      by_contra hne
      exact h5 ⟨hne, h3⟩
    subst hq2
    exact hTodd' hqb
  have hat : F₀.index = Nat.card (T.subgroupOf E) := by
    apply Nat.dvd_antisymm
    · have h1 : F₀.index ∣ Nat.card (T.subgroupOf E) * (T.subgroupOf E).index := by
        rw [htb, ← hfa]
        exact dvd_mul_left _ _
      exact hab.dvd_of_dvd_mul_right h1
    · have h2 : Nat.card (T.subgroupOf E) ∣ Nat.card F₀ * F₀.index := by
        rw [hfa, ← htb]
        exact dvd_mul_right _ _
      exact hcop_tf.dvd_of_dvd_mul_left h2
  refine ⟨?_, hcop_tf.symm⟩
  rw [← hat]
  exact hfa

private lemma G6Hall.isHall_map_of_hall {S : Type*} [Group S] [Finite S] {E : Subgroup S}
    (hE : CFSG.IsHallSubgroup G6Hall.pi3 E) {F₀ : Subgroup E}
    (hF₀ : CFSG.IsHallSubgroup G6Hall.pi5 F₀) :
    CFSG.IsHallSubgroup G6Hall.pi5 (F₀.map E.subtype) := by
  refine CFSG.isHallSubgroup_of G6Hall.pi5 (F₀.map E.subtype) ?_ ?_
  · intro p hp
    have hcard : Nat.card (F₀.map E.subtype) = Nat.card F₀ :=
      Subgroup.card_map_of_injective E.subtype_injective
    rw [hcard] at hp
    exact hF₀.p_in_pi_of_p_dvd_card p hp
  · intro p hp hdvd
    rw [Subgroup.index_map_subtype F₀] at hdvd
    rcases (Nat.Prime.dvd_mul p.2).1 hdvd with h1 | h2
    · exact hF₀.p_in_pi_of_p_dvd_index p h1 hp
    · exact hE.p_in_pi_of_p_dvd_index p h2 (G6Hall.mem_pi3.mpr (G6Hall.mem_pi5.mp hp).2)

theorem exists_permutable_hall_ge5 {S : Type*} [Group S] [Finite S] (hS : Group.IsSolvable S)
    {T : Subgroup S} (hT2 : IsPGroup 2 T) (hTodd : ¬ 2 ∣ T.index) :
    ∃ F : Subgroup S, (∀ x ∈ F, Nat.Coprime (orderOf x) 6) ∧
      ((F ⊔ T : Subgroup S) : Set S) = (F : Set S) * (T : Set S) ∧
      ∀ y : S, Nat.Coprime (orderOf y) 6 → ∃ s : S, s * y * s⁻¹ ∈ F := by
  obtain ⟨E, hE, hTE⟩ := CFSG.SolvableHall.solvable_hall_containment hS G6Hall.pi3 T
    (G6Hall.isPiSubgroup_pi3 hT2)
  obtain ⟨F₀, hF₀⟩ := CFSG.SolvableHall.solvable_hall_existence
    (inferInstance : Group.IsSolvable ↥E) G6Hall.pi5
  obtain ⟨hcard, hcop⟩ := G6Hall.card_mul_card_and_coprime hE hT2 hTodd hTE hF₀
  have hcompl : Subgroup.IsComplement' F₀ (T.subgroupOf E) :=
    Subgroup.isComplement'_of_coprime hcard hcop
  have hF : CFSG.IsHallSubgroup G6Hall.pi5 (F₀.map E.subtype) :=
    G6Hall.isHall_map_of_hall hE hF₀
  refine ⟨F₀.map E.subtype, ?_, ?_, ?_⟩
  ·
    intro x hx
    apply G6Hall.coprime_six_of_pi5
    intro p hp hpx
    exact G6Hall.mem_pi5.mp
      (hF.p_in_pi_of_p_dvd_card ⟨p, hp⟩ (hpx.trans (Subgroup.orderOf_dvd_natCard _ hx)))
  ·
    ext x
    constructor
    · intro hx
      have hx' : x ∈ F₀.map E.subtype ⊔ T := hx
      have hxE : x ∈ E := (sup_le (Subgroup.map_subtype_le F₀) hTE) hx'
      obtain ⟨⟨⟨f, hf⟩, ⟨t, ht⟩⟩, hft⟩ :=
        (Subgroup.IsComplement.existsUnique hcompl ⟨x, hxE⟩).exists
      have hft' : f * t = ⟨x, hxE⟩ := hft
      have hx'' : (f : S) * (t : S) = x := congrArg Subtype.val hft'
      have ht' : t ∈ T.subgroupOf E := ht
      refine Set.mem_mul.mpr ⟨(f : S), ?_, (t : S), ?_, hx''⟩
      · exact Subgroup.mem_map.mpr ⟨f, hf, rfl⟩
      · exact Subgroup.mem_subgroupOf.mp ht'
    · rintro ⟨f, hf, t, ht, rfl⟩
      exact Subgroup.mul_mem_sup hf ht
  ·
    intro y hy
    have hcopy : ∀ d : ℕ, d ∣ orderOf y → d ∣ 6 → d = 1 :=
      fun d h1 h2 => Nat.eq_one_of_dvd_coprimes hy h1 h2
    have hyπ : CFSG.IsPiSubgroup G6Hall.pi5 (Subgroup.zpowers y) := by
      intro p hp
      rw [Nat.card_zpowers] at hp
      refine G6Hall.mem_pi5.mpr ⟨fun h2 => ?_, fun h3 => ?_⟩
      · have h6 : p.val ∣ 6 := by rw [h2]; norm_num
        have h1 := hcopy _ hp h6
        rw [h2] at h1
        exact absurd h1 (by norm_num)
      · have h6 : p.val ∣ 6 := by rw [h3]; norm_num
        have h1 := hcopy _ hp h6
        rw [h3] at h1
        exact absurd h1 (by norm_num)
    obtain ⟨F₁, hF₁, hyF₁⟩ :=
      CFSG.SolvableHall.solvable_hall_containment hS G6Hall.pi5 (Subgroup.zpowers y) hyπ
    obtain ⟨g, hg⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hS hF hF₁
    have hy' : y ∈ (F₀.map E.subtype).map (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      exact hyF₁ (Subgroup.mem_zpowers y)
    obtain ⟨f, hf, hfy⟩ := Subgroup.mem_map.mp hy'
    have hfy' : g * f * g⁻¹ = y := hfy
    refine ⟨g⁻¹, ?_⟩
    have hconj : g⁻¹ * y * g⁻¹⁻¹ = f := by
      rw [← hfy']
      group
    rw [hconj]
    exact hf

end CFSG.Quasithin.H13.L319
