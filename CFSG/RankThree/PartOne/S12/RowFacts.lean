module

public import CFSG.RankThree.PartOne.S12.InputsTable

public section

namespace CFSG.RankThree.PartOne

variable {G : Type} [Group G]

theorem pCore_eq_bot_of_not_dvd_natCard {W : Type*} [Group W] [Finite W] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card W) : CFSG.pCore p W = ⊥ := by
  have hfact : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := p) (G := W)) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa using hk
  · exact absurd ((dvd_pow_self p hk0.ne').trans (hk ▸ orderOf_dvd_natCard x)) h

theorem pCore_five_perm_five_eq_bot : CFSG.pCore 5 (Equiv.Perm (Fin 5)) = ⊥ := by
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hnorm : (CFSG.pCore 5 (Equiv.Perm (Fin 5))).Normal := CFSG.pCore_normal
  have hp : IsPGroup 5 (CFSG.pCore 5 (Equiv.Perm (Fin 5))) := CFSG.pCore_isPGroup
  have hle : CFSG.pCore 5 (Equiv.Perm (Fin 5)) ≤ alternatingGroup (Fin 5) := by
    intro x hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hp ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [Equiv.Perm.mem_alternatingGroup]
    have hsign : Equiv.Perm.sign x ^ (5 ^ k) = 1 := by
      rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h | h
    · exact h
    · rw [h, Odd.neg_one_pow (Odd.pow (by decide))] at hsign
      exact absurd hsign (by decide)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hN : ((CFSG.pCore 5 (Equiv.Perm (Fin 5))).subgroupOf (alternatingGroup (Fin 5))).Normal :=
    hnorm.subgroupOf _
  rcases hN.eq_bot_or_eq_top with h | h
  · rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hle hx⟩ : alternatingGroup (Fin 5)) ∈
        (CFSG.pCore 5 (Equiv.Perm (Fin 5))).subgroupOf (alternatingGroup (Fin 5)) := hx
    rw [h, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  · exfalso
    have hA : alternatingGroup (Fin 5) ≤ CFSG.pCore 5 (Equiv.Perm (Fin 5)) :=
      Subgroup.subgroupOf_eq_top.mp h
    have hc : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.2 (by decide)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hp ⟨_, hA hc⟩
    rw [Subgroup.orderOf_mk] at hk
    have h3 : orderOf (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime (by decide) (by decide)
    rw [h3] at hk
    have h35 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (show 3 ∣ 5 ^ k from hk ▸ dvd_rfl)
    omega

theorem pCore_eq_bot_of_natCard_dvd_forty_eight {W : Type*} [Group W] [Finite W]
    (hcard : Nat.card W ∣ 2 ^ 4 * 3) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    CFSG.pCore p W = ⊥ := by
  refine pCore_eq_bot_of_not_dvd_natCard hp fun hd => ?_
  rcases (Nat.Prime.dvd_mul hp).1 (hd.trans hcard) with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd (by norm_num) h3
    omega

private structure WeylFacts (W : Type) [Group W] : Prop where
  nonabelian : ∃ a b : W, a * b ≠ b * a
  card_dvd : Nat.card W ∣ 2 ^ 4 * 3 * 5
  pCore_eq_bot : ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.pCore p W = ⊥

private theorem WeylFacts.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : WeylFacts B) : WeylFacts A where
  nonabelian := by
    obtain ⟨a, b, hab⟩ := h.nonabelian
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa using congrArg e hba
  card_dvd := by
    rw [Nat.card_congr e.toEquiv]
    exact h.card_dvd
  pCore_eq_bot p hp h5 := by
    have hmap := CFSG.pCore_map_iso p e
    rw [h.pCore_eq_bot p hp h5] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

private theorem WeylFacts.of_natCard_dvd_forty_eight {W : Type} [Group W] [Finite W]
    (hnab : ∃ a b : W, a * b ≠ b * a) (hcard : Nat.card W ∣ 2 ^ 4 * 3) : WeylFacts W where
  nonabelian := hnab
  card_dvd := hcard.trans ⟨5, by norm_num⟩
  pCore_eq_bot _ hp h5 := pCore_eq_bot_of_natCard_dvd_forty_eight hcard hp h5

private theorem WeylFacts.perm_three : WeylFacts (Equiv.Perm (Fin 3)) :=
  .of_natCard_dvd_forty_eight ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩
    (by rw [Nat.card_perm, Nat.card_fin]; decide)

private theorem WeylFacts.dihedral_six : WeylFacts (DihedralGroup 6) :=
  .of_natCard_dvd_forty_eight ⟨.r 1, .sr 0, by decide⟩
    (by rw [DihedralGroup.nat_card]; decide)

private theorem WeylFacts.dihedral_eight : WeylFacts (DihedralGroup 8) :=
  .of_natCard_dvd_forty_eight ⟨.r 1, .sr 0, by decide⟩
    (by rw [DihedralGroup.nat_card]; decide)

private theorem WeylFacts.dihedral_four : WeylFacts (DihedralGroup 4) :=
  .of_natCard_dvd_forty_eight ⟨.r 1, .sr 0, by decide⟩
    (by rw [DihedralGroup.nat_card]; decide)

private theorem WeylFacts.perm_four : WeylFacts (Equiv.Perm (Fin 4)) :=
  .of_natCard_dvd_forty_eight ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩
    (by rw [Nat.card_perm, Nat.card_fin]; decide)

private theorem WeylFacts.zmod_two_prod_perm_four :
    WeylFacts (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :=
  .of_natCard_dvd_forty_eight
    ⟨(1, Equiv.swap 0 1), (1, Equiv.swap 1 2), fun h =>
      absurd (congrArg Prod.snd h) (by decide)⟩
    (by
      have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
      rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, h2]
      decide)

private theorem WeylFacts.perm_five : WeylFacts (Equiv.Perm (Fin 5)) where
  nonabelian := ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩
  card_dvd := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  pCore_eq_bot p hp h5 := by
    rcases h5.eq_or_lt with rfl | h6
    · exact pCore_five_perm_five_eq_bot
    · refine pCore_eq_bot_of_not_dvd_natCard hp ?_
      rw [Nat.card_perm, Nat.card_fin, hp.dvd_factorial]
      omega

private theorem WeylFacts.of_rowWeylIso {X : Subgroup G} {Γ : Subgroup (MulAut X)} {r : ℕ}
    (hr1 : 1 ≤ r) (hr12 : r ≤ 12) (hr : RowWeylIso X Γ r) : WeylFacts ↥Γ := by
  interval_cases r
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .perm_three
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .dihedral_six
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .dihedral_six
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .dihedral_eight
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .dihedral_four
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .dihedral_four
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .dihedral_four
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .dihedral_four
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .perm_four
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .zmod_two_prod_perm_four
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .perm_five
  · obtain ⟨e⟩ := hr
    exact .of_mulEquiv e .perm_five

variable {X : Subgroup G} {Γ : Subgroup (MulAut X)} {r : ℕ}

theorem rowWeylIso_nonabelian (hr1 : 1 ≤ r) (hr12 : r ≤ 12) (hr : RowWeylIso X Γ r) :
    ∃ a b : Γ, a * b ≠ b * a :=
  (WeylFacts.of_rowWeylIso hr1 hr12 hr).nonabelian

theorem rowWeylIso_card_dvd (hr1 : 1 ≤ r) (hr12 : r ≤ 12) (hr : RowWeylIso X Γ r) :
    Nat.card Γ ∣ 2 ^ 4 * 3 * 5 :=
  (WeylFacts.of_rowWeylIso hr1 hr12 hr).card_dvd

theorem rowWeylIso_pCore_eq_bot (hr1 : 1 ≤ r) (hr12 : r ≤ 12) (hr : RowWeylIso X Γ r) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) : CFSG.pCore p ↥Γ = ⊥ :=
  (WeylFacts.of_rowWeylIso hr1 hr12 hr).pCore_eq_bot p hp h5

theorem rowWeylIso_ne_bot (hr1 : 1 ≤ r) (hr12 : r ≤ 12) (hr : RowWeylIso X Γ r) : Γ ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := rowWeylIso_nonabelian hr1 hr12 hr
  rintro rfl
  exact hab (Subsingleton.elim _ _)

theorem rowWeylIso_perfect_subgroup_of_eleven_or_twelve (h : r = 11 ∨ r = 12)
    (hr : RowWeylIso X Γ r) :
    ∃ Λ : Subgroup (MulAut X), Λ ≤ Γ ∧ Group.IsPerfect ↥Λ ∧ Nat.card Λ = 60 := by
  have hne : Nonempty (Γ ≃* Equiv.Perm (Fin 5)) := by
    rcases h with rfl | rfl <;> exact hr
  obtain ⟨e⟩ := hne
  have hperf : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  have hinj : Function.Injective (Γ.subtype.comp e.symm.toMonoidHom) :=
    Γ.subtype_injective.comp e.symm.injective
  refine ⟨(alternatingGroup (Fin 5)).map (Γ.subtype.comp e.symm.toMonoidHom), ?_,
    Group.IsPerfect.map _, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact (e.symm x).2
  · rw [Subgroup.card_map_of_injective hinj, nat_card_alternatingGroup, Nat.card_fin]
    rfl

theorem rowWeylIso_perfect_subgroup_of_eleven (hr : RowWeylIso X Γ 11) :
    ∃ Λ : Subgroup (MulAut X), Λ ≤ Γ ∧ Group.IsPerfect ↥Λ ∧ Nat.card Λ = 60 :=
  rowWeylIso_perfect_subgroup_of_eleven_or_twelve (Or.inl rfl) hr

theorem rowWeylIso_perfect_subgroup_of_twelve (hr : RowWeylIso X Γ 12) :
    ∃ Λ : Subgroup (MulAut X), Λ ≤ Γ ∧ Group.IsPerfect ↥Λ ∧ Nat.card Λ = 60 :=
  rowWeylIso_perfect_subgroup_of_eleven_or_twelve (Or.inr rfl) hr

theorem rowWeylIso_central_involution_of_ten (hr : RowWeylIso X Γ 10) :
    ∃ z ∈ Γ, z ≠ 1 ∧ z * z = 1 ∧ ∀ g ∈ Γ, g * z = z * g := by
  obtain ⟨e⟩ := hr
  have hne : ((Multiplicative.ofAdd 1, 1) : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ≠ 1 :=
    fun h => absurd (congrArg Prod.fst h) (by decide)
  have hsq : ((Multiplicative.ofAdd 1, 1) : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) *
      (Multiplicative.ofAdd 1, 1) = 1 :=
    Prod.ext (by decide) (by simp)
  have hcomm : ∀ g : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4),
      g * (Multiplicative.ofAdd 1, 1) = (Multiplicative.ofAdd 1, 1) * g :=
    fun g => Prod.ext (mul_comm _ _) (by simp)
  refine ⟨((e.symm (Multiplicative.ofAdd 1, 1) : Γ) : MulAut X), (e.symm _).2, ?_, ?_, ?_⟩
  · intro h
    exact hne (e.symm.injective ((Subtype.ext h).trans e.symm.map_one.symm))
  · have h2 : e.symm (Multiplicative.ofAdd 1, 1) * e.symm (Multiplicative.ofAdd 1, 1) = 1 := by
      rw [← map_mul, hsq, map_one]
    exact congrArg Subtype.val h2
  · intro g hg
    have h2 : (⟨g, hg⟩ : Γ) * e.symm (Multiplicative.ofAdd 1, 1) =
        e.symm (Multiplicative.ofAdd 1, 1) * ⟨g, hg⟩ := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hcomm _
    exact congrArg Subtype.val h2

end CFSG.RankThree.PartOne
