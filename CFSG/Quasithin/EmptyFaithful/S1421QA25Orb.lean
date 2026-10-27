module

public import CFSG.Quasithin.EmptyFaithful.S1421QA25Stab
public import CFSG.Quasithin.Vol2.Ch1EightFourNum

public section

namespace CFSG.Quasithin

open MulAction CFSG.QuasithinUnique CFSG.Quasithin.Ch1Four

namespace QA25

section Orb

variable {G Ω : Type} [Group G] [MulAction G Ω]

theorem mem_fixingSubgroup_pair {p q : Ω} {a : G} :
    a ∈ fixingSubgroup G ({p, q} : Set Ω) ↔ a • p = p ∧ a • q = q := by
  rw [mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact ⟨h p (by simp), h q (by simp)⟩
  · rintro ⟨hp, hq⟩ y hy
    rcases hy with rfl | hy
    · exact hp
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hq

theorem mem_fixingSubgroup_four {p q c d : Ω} {a : G} :
    a ∈ fixingSubgroup G ({p, q, c, d} : Set Ω) ↔
      a • p = p ∧ a • q = q ∧ a • c = c ∧ a • d = d := by
  rw [mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact ⟨h p (by simp), h q (by simp), h c (by simp), h d (by simp)⟩
  · rintro ⟨hp, hq, hc, hd⟩ y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> assumption

theorem injective_vec4 {a b c d : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]

theorem exists_smul_eq_four (h4 : IsMultiplyPretransitive G Ω 4) {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Ω}
    (hx : Function.Injective ![x₀, x₁, x₂, x₃]) (hy : Function.Injective ![y₀, y₁, y₂, y₃]) :
    ∃ g : G, g • x₀ = y₀ ∧ g • x₁ = y₁ ∧ g • x₂ = y₂ ∧ g • x₃ = y₃ := by
  have : IsPretransitive G (Fin 4 ↪ Ω) := h4
  obtain ⟨g, hg⟩ := exists_smul_eq G (⟨_, hx⟩ : Fin 4 ↪ Ω) (⟨_, hy⟩ : Fin 4 ↪ Ω)
  have h0 := congrArg (fun f : Fin 4 ↪ Ω => f 0) hg
  have h1 := congrArg (fun f : Fin 4 ↪ Ω => f 1) hg
  have h2 := congrArg (fun f : Fin 4 ↪ Ω => f 2) hg
  have h3 := congrArg (fun f : Fin 4 ↪ Ω => f 3) hg
  exact ⟨g, h0, h1, h2, h3⟩

theorem card_fix_pair [Finite G] [Finite Ω] (h4 : IsMultiplyPretransitive G Ω 4)
    (hΩ : Nat.card Ω = 23) (hG : Nat.card G = 10200960) {p q : Ω} (hpq : p ≠ q) :
    Nat.card (fixingSubgroup G ({p, q} : Set Ω)) = 20160 := by
  have h2 : IsMultiplyPretransitive G Ω ({p, q} : Set Ω).ncard := by
    rw [Set.ncard_pair hpq]
    exact isMultiplyPretransitive_of_le (m := 2) (n := 4) (by norm_num) (by rw [hΩ]; norm_num)
  have hidx := IsMultiplyPretransitive.index_of_fixingSubgroup_eq ({p, q} : Set Ω) h2
  rw [Set.ncard_pair hpq, hΩ] at hidx
  have h1 := Subgroup.index_mul_card (fixingSubgroup G ({p, q} : Set Ω))
  rw [hidx, hG] at h1
  norm_num [Nat.choose, Nat.factorial] at h1
  omega

theorem card_fix_four [Finite G] [Finite Ω] (h4 : IsMultiplyPretransitive G Ω 4)
    (hΩ : Nat.card Ω = 23) (hG : Nat.card G = 10200960) {p q c d : Ω} (hpq : p ≠ q) (hpc : p ≠ c)
    (hpd : p ≠ d) (hqc : q ≠ c) (hqd : q ≠ d) (hcd : c ≠ d) :
    Nat.card (fixingSubgroup G ({p, q, c, d} : Set Ω)) = 48 := by
  have hn : ({p, q, c, d} : Set Ω).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [hpq, hpc, hpd]),
      Set.ncard_insert_of_notMem (by simp [hqc, hqd]), Set.ncard_pair hcd]
  have h2 : IsMultiplyPretransitive G Ω ({p, q, c, d} : Set Ω).ncard := by
    rw [hn]
    exact h4
  have hidx := IsMultiplyPretransitive.index_of_fixingSubgroup_eq ({p, q, c, d} : Set Ω) h2
  rw [hn, hΩ] at hidx
  have h1 := Subgroup.index_mul_card (fixingSubgroup G ({p, q, c, d} : Set Ω))
  rw [hidx, hG] at h1
  norm_num [Nat.choose, Nat.factorial] at h1
  omega

theorem exists_ne_three [Finite Ω] (hΩ : Nat.card Ω = 23) (p q c : Ω) :
    ∃ x : Ω, x ≠ p ∧ x ≠ q ∧ x ≠ c := by
  have := Fintype.ofFinite Ω
  have hc : Fintype.card Ω = 23 := by rw [← Nat.card_eq_fintype_card]; exact hΩ
  classical
  have h3 : ({p, q, c} : Finset Ω).card ≤ 3 := Finset.card_le_three
  have hpos : 0 < (Finset.univ \ ({p, q, c} : Finset Ω)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hc]
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hx
  exact ⟨x, hx.1, hx.2.1, hx.2.2⟩

theorem exists_mem_fix_pair_smul_eq [Finite Ω] (h4 : IsMultiplyPretransitive G Ω 4)
    (hΩ : Nat.card Ω = 23) {p q c d : Ω} (hpq : p ≠ q) (hc : c ≠ p ∧ c ≠ q) (hd : d ≠ p ∧ d ≠ q) :
    ∃ a ∈ fixingSubgroup G ({p, q} : Set Ω), a • c = d := by
  obtain ⟨c', hc'p, hc'q, hc'c⟩ := exists_ne_three hΩ p q c
  obtain ⟨d', hd'p, hd'q, hd'd⟩ := exists_ne_three hΩ p q d
  obtain ⟨g, hg0, hg1, hg2, hg3⟩ := exists_smul_eq_four h4 (x₀ := p) (x₁ := q) (x₂ := c)
    (x₃ := c') (y₀ := p) (y₁ := q) (y₂ := d) (y₃ := d')
    (injective_vec4 hpq hc.1.symm hc'p.symm hc.2.symm hc'q.symm hc'c.symm)
    (injective_vec4 hpq hd.1.symm hd'p.symm hd.2.symm hd'q.symm hd'd.symm)
  exact ⟨g, mem_fixingSubgroup_pair.mpr ⟨hg0, hg1⟩, hg2⟩

theorem exists_mem_fix_pair_smul_eq₂ (h4 : IsMultiplyPretransitive G Ω 4) {p q c c' d d' : Ω}
    (hpq : p ≠ q) (hc : c ≠ p ∧ c ≠ q) (hc' : c' ≠ p ∧ c' ≠ q) (hd : d ≠ p ∧ d ≠ q)
    (hd' : d' ≠ p ∧ d' ≠ q) (hcc' : c ≠ c') (hdd' : d ≠ d') :
    ∃ a ∈ fixingSubgroup G ({p, q} : Set Ω), a • c = d ∧ a • c' = d' := by
  obtain ⟨g, hg0, hg1, hg2, hg3⟩ := exists_smul_eq_four h4 (x₀ := p) (x₁ := q) (x₂ := c)
    (x₃ := c') (y₀ := p) (y₁ := q) (y₂ := d) (y₃ := d')
    (injective_vec4 hpq hc.1.symm hc'.1.symm hc.2.symm hc'.2.symm hcc')
    (injective_vec4 hpq hd.1.symm hd'.1.symm hd.2.symm hd'.2.symm hdd')
  exact ⟨g, mem_fixingSubgroup_pair.mpr ⟨hg0, hg1⟩, hg2, hg3⟩

theorem eq_of_forall_fix_pair [Finite Ω] (h4 : IsMultiplyPretransitive G Ω 4)
    (hΩ : Nat.card Ω = 23) {p q : Ω} (hpq : p ≠ q) {y : Ω}
    (hy : ∀ a ∈ fixingSubgroup G ({p, q} : Set Ω), a • y = y) : y = p ∨ y = q := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d, hdp, hdq, hdy⟩ := exists_ne_three hΩ p q y
  obtain ⟨a, ha, hay⟩ := exists_mem_fix_pair_smul_eq h4 hΩ hpq hcon ⟨hdp, hdq⟩
  exact hdy (hay.symm.trans (hy a ha))

theorem smul_pair_mem_of_mem_normalizer [Finite Ω] (h4 : IsMultiplyPretransitive G Ω 4)
    (hΩ : Nat.card Ω = 23) {p q : Ω} (hpq : p ≠ q) {s : G}
    (hs : s ∈ Subgroup.normalizer ((fixingSubgroup G ({p, q} : Set Ω) : Subgroup G) : Set G)) :
    (s • p = p ∨ s • p = q) ∧ (s • q = p ∨ s • q = q) := by
  have hfix : ∀ y, (y = p ∨ y = q) → ∀ a ∈ fixingSubgroup G ({p, q} : Set Ω),
      a • (s • y) = s • y := by
    intro y hy a ha
    have h1 : s⁻¹ * a * s ∈ fixingSubgroup G ({p, q} : Set Ω) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) a).mp ha
      simpa using this
    obtain ⟨hp, hq⟩ := mem_fixingSubgroup_pair.mp h1
    have h2 : (s⁻¹ * a * s) • y = y := by rcases hy with rfl | rfl <;> assumption
    calc a • s • y = s • ((s⁻¹ * a * s) • y) := by simp [mul_smul]
      _ = s • y := by rw [h2]
  exact ⟨eq_of_forall_fix_pair h4 hΩ hpq (hfix p (Or.inl rfl)),
    eq_of_forall_fix_pair h4 hΩ hpq (hfix q (Or.inr rfl))⟩

theorem exists_fixed_point_of_isPGroup [Finite Ω] (hΩ : Nat.card Ω = 23) {p q : Ω}
    (hpq : p ≠ q) {S : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hSpq : ∀ s ∈ S, (s • p = p ∨ s • p = q) ∧ (s • q = p ∨ s • q = q)) :
    ∃ c : Ω, c ≠ p ∧ c ≠ q ∧ ∀ s ∈ S, s • c = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hS2.card_modEq_card_fixedPoints Ω
  by_contra hcon
  push Not at hcon
  have hsub : ∀ c ∈ fixedPoints ↥S Ω, c = p ∨ c = q := by
    intro c hc
    by_contra h
    push Not at h
    obtain ⟨s, hs, hsc⟩ := hcon c h.1 h.2
    exact hsc (hc ⟨s, hs⟩)
  have hiff : p ∈ fixedPoints ↥S Ω ↔ q ∈ fixedPoints ↥S Ω := by
    constructor
    · intro hp s
      have hsp : (s : G) • p = p := hp s
      rcases (hSpq s s.2).2 with h | h
      · have h' : (s : G) • q = (s : G) • p := h.trans hsp.symm
        exact absurd (MulAction.injective (s : G) h') hpq.symm
      · exact h
    · intro hq s
      have hsq : (s : G) • q = q := hq s
      rcases (hSpq s s.2).1 with h | h
      · exact h
      · exact absurd (MulAction.injective (s : G) (h.trans hsq.symm)) hpq
  have hcard : Nat.card ↑(fixedPoints ↥S Ω) = 0 ∨ Nat.card ↑(fixedPoints ↥S Ω) = 2 := by
    by_cases hp : p ∈ fixedPoints ↥S Ω
    · right
      have hq := hiff.mp hp
      have : fixedPoints ↥S Ω = {p, q} := by
        ext c
        constructor
        · intro hc
          rcases hsub c hc with rfl | rfl <;> simp
        · intro hc
          rcases hc with rfl | hc
          · exact hp
          · rw [Set.mem_singleton_iff] at hc
            subst hc
            exact hq
      rw [this, Nat.card_coe_set_eq, Set.ncard_pair hpq]
    · left
      have hq : q ∉ fixedPoints ↥S Ω := fun h => hp (hiff.mpr h)
      have : fixedPoints ↥S Ω = ∅ := by
        ext c
        constructor
        · intro hc
          rcases hsub c hc with rfl | rfl
          · exact absurd hc hp
          · exact absurd hc hq
        · intro hc
          exact absurd hc (Set.notMem_empty c)
      rw [this]
      simp
  rw [hΩ] at hmod
  rcases hcard with h | h <;> rw [h] at hmod <;> exact absurd hmod (by decide)

theorem card_eq_sixty_four_of_isSylowTwoOf [Finite G] {A U : Subgroup G} (hU : IsSylowTwoOf U A)
    (hA : Nat.card A = 20160) : Nat.card U = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU.2.1
  have h1 := Subgroup.index_mul_card (U.subgroupOf A)
  have h2 : Nat.card ↥(U.subgroupOf A) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.1).toEquiv
  rw [h2, hk, hA] at h1
  have hodd : Odd (U.subgroupOf A).index := by
    have := hU.2.2
    rw [Nat.odd_iff]
    omega
  have h3 : 2 ^ k * (U.subgroupOf A).index = 2 ^ 6 * 315 := by
    rw [mul_comm, h1]
    norm_num
  have h4 := two_pow_mul_odd_inj hodd (by decide) h3
  rw [hk, h4.1]
  norm_num

theorem stableMax_of_pair [Finite G] [Finite Ω] (h4 : IsMultiplyPretransitive G Ω 4)
    (hΩ : Nat.card Ω = 23) (hG : Nat.card G = 10200960) {p q : Ω} (hpq : p ≠ q)
    {S : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hSN : S ≤ Subgroup.normalizer ((fixingSubgroup G ({p, q} : Set Ω) : Subgroup G) : Set G))
    (hSyl : IsSylowTwoOf (S ⊓ fixingSubgroup G ({p, q} : Set Ω))
      (fixingSubgroup G ({p, q} : Set Ω))) :
    StableMax S (fixingSubgroup G ({p, q} : Set Ω)) := by
  set A : Subgroup G := fixingSubgroup G ({p, q} : Set Ω) with hAdef
  have hAcard : Nat.card A = 20160 := card_fix_pair h4 hΩ hG hpq
  have hUcard : Nat.card ↥(S ⊓ A) = 64 := card_eq_sixty_four_of_isSylowTwoOf hSyl hAcard
  have hSpq : ∀ s ∈ S, (s • p = p ∨ s • p = q) ∧ (s • q = p ∨ s • q = q) :=
    fun s hs => smul_pair_mem_of_mem_normalizer h4 hΩ hpq (hSN hs)
  obtain ⟨c, hcp, hcq, hcS⟩ := exists_fixed_point_of_isPGroup hΩ hpq hS2 hSpq
  set P : Subgroup G := A ⊓ MulAction.stabilizer G c with hPdef
  have hmemP : ∀ x, x ∈ P ↔ x ∈ A ∧ x • c = c := fun x => by
    simp [hPdef, MulAction.mem_stabilizer_iff]
  have hne : ∀ y ∈ A, ∀ z : Ω, z ≠ p → z ≠ q → y • z ≠ p ∧ y • z ≠ q := by
    intro y hy z hzp hzq
    obtain ⟨hp, hq⟩ := mem_fixingSubgroup_pair.mp hy
    constructor
    · intro h
      exact hzp (MulAction.injective y (show y • z = y • p by rw [h, hp]))
    · intro h
      exact hzq (MulAction.injective y (show y • z = y • q by rw [h, hq]))
  have hunique : ∀ d : Ω, d ≠ p → d ≠ q → (∀ u ∈ S ⊓ A, u • d = d) → d = c := by
    intro d hdp hdq hd
    by_contra hdc
    have hle : S ⊓ A ≤ fixingSubgroup G ({p, q, c, d} : Set Ω) := by
      intro u hu
      obtain ⟨hp, hq⟩ := mem_fixingSubgroup_pair.mp hu.2
      exact mem_fixingSubgroup_four.mpr ⟨hp, hq, hcS u hu.1, hd u hu⟩
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hUcard, card_fix_four h4 hΩ hG hpq hcp.symm hdp.symm hcq.symm hdq.symm (Ne.symm hdc)]
      at hdvd
    omega
  have hB : A ⊓ Subgroup.normalizer ((S ⊓ A : Subgroup G) : Set G) ≤ P := by
    rintro x ⟨hxA, hxN⟩
    rw [hmemP]
    refine ⟨hxA, ?_⟩
    have hx := hne x hxA c hcp hcq
    have hfix : ∀ u ∈ S ⊓ A, u • (x • c) = x • c := by
      intro u hu
      have hu' : x⁻¹ * u * x ∈ S ⊓ A := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) u).mp hu
        simpa using this
      have h1 := hcS _ hu'.1
      calc u • x • c = x • ((x⁻¹ * u * x) • c) := by simp [mul_smul]
        _ = x • c := by rw [h1]
    exact hunique _ hx.1 hx.2 hfix
  have hmax : ∀ Q : Subgroup G, Q ≤ A → P ≤ Q → Q ≠ P → Q = A := by
    intro Q hQA hPQ hQP
    have hex : ∃ x ∈ Q, x ∉ P := by
      by_contra hno
      push Not at hno
      exact hQP (le_antisymm hno hPQ)
    obtain ⟨x, hxQ, hxP⟩ := hex
    have hxA : x ∈ A := hQA hxQ
    have hxc : x • c ≠ c := fun h => hxP ((hmemP x).mpr ⟨hxA, h⟩)
    refine le_antisymm hQA fun a ha => ?_
    by_cases hac : a • c = c
    · exact hPQ ((hmemP a).mpr ⟨ha, hac⟩)
    · have he := hne a ha c hcp hcq
      have hd := hne x hxA c hcp hcq
      obtain ⟨b, hbA, hbc, hbd⟩ := exists_mem_fix_pair_smul_eq₂ h4 hpq ⟨hcp, hcq⟩ hd ⟨hcp, hcq⟩ he
        (Ne.symm hxc) (Ne.symm hac)
      have hbP : b ∈ P := (hmemP b).mpr ⟨hbA, hbc⟩
      have hbx : b * x ∈ Q := Q.mul_mem (hPQ hbP) hxQ
      have hbxc : (b * x) • c = a • c := by rw [mul_smul, hbd]
      have hP2 : a⁻¹ * (b * x) ∈ P := by
        refine (hmemP _).mpr ⟨A.mul_mem (A.inv_mem ha) (A.mul_mem hbA hxA), ?_⟩
        rw [mul_smul, hbxc, inv_smul_smul]
      have h2 := Q.mul_mem hbx (Q.inv_mem (hPQ hP2))
      have e : b * x * (a⁻¹ * (b * x))⁻¹ = a := by group
      rwa [e] at h2
  have hPA : P ≠ A := by
    intro h
    obtain ⟨d, hdp, hdq, hdc⟩ := exists_ne_three hΩ p q c
    obtain ⟨a, haA, hac⟩ := exists_mem_fix_pair_smul_eq h4 hΩ hpq ⟨hcp, hcq⟩ ⟨hdp, hdq⟩
    have : a ∈ P := h ▸ haA
    exact hdc (hac.symm.trans ((hmemP a).mp this).2)
  refine ⟨P, ⟨⟨inf_le_left, S ⊓ A, hSyl, hB⟩, hPA, ?_⟩, hB, ?_⟩
  · intro Q hQ hQne hPQ
    by_contra hne'
    exact hQne (hmax Q hQ.1 hPQ hne')
  · intro s hs
    have hsc : s • c = c := hcS s hs
    have hsc' : s⁻¹ • c = c := by rw [inv_smul_eq_iff]; exact hsc.symm
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    rw [hmemP, hmemP]
    have hA' : x ∈ A ↔ s * x * s⁻¹ ∈ A := Subgroup.mem_normalizer_iff.mp (hSN hs) x
    have hc' : x • c = c ↔ (s * x * s⁻¹) • c = c := by
      rw [mul_smul, mul_smul, hsc']
      constructor
      · intro h
        rw [h, hsc]
      · intro h
        calc x • c = s⁻¹ • s • x • c := by rw [inv_smul_smul]
          _ = s⁻¹ • c := by rw [h]
          _ = c := hsc'
    rw [hA', hc']

end Orb

end QA25

end CFSG.Quasithin
