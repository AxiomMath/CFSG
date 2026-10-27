module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin

open Equiv Equiv.Perm

@[expose] def permSetStab {α : Type*} (Ω : Set α) : Subgroup (Perm α) where
  carrier := {σ | ∀ y, σ y ∈ Ω ↔ y ∈ Ω}
  mul_mem' := fun {σ τ} hσ hτ y => by
    show σ (τ y) ∈ Ω ↔ y ∈ Ω
    rw [hσ, hτ]
  one_mem' := fun y => Iff.rfl
  inv_mem' := fun {σ} hσ y => by
    show σ⁻¹ y ∈ Ω ↔ y ∈ Ω
    have := hσ (σ⁻¹ y)
    simpa using this.symm

theorem mem_permSetStab {α : Type*} {Ω : Set α} {σ : Perm α} :
    σ ∈ permSetStab Ω ↔ ∀ y, σ y ∈ Ω ↔ y ∈ Ω := Iff.rfl

@[expose] def fixOutside {α : Type*} (Ω : Set α) : Subgroup (Perm α) where
  carrier := {σ | ∀ y, y ∉ Ω → σ y = y}
  mul_mem' := fun {σ τ} hσ hτ y hy => by
    show σ (τ y) = y
    rw [hτ y hy, hσ y hy]
  one_mem' := fun y _ => rfl
  inv_mem' := fun {σ} hσ y hy => by
    show σ⁻¹ y = y
    rw [Perm.inv_eq_iff_eq]
    exact (hσ y hy).symm

theorem mem_fixOutside {α : Type*} {Ω : Set α} {σ : Perm α} :
    σ ∈ fixOutside Ω ↔ ∀ y, y ∉ Ω → σ y = y := Iff.rfl

theorem exists_small_invariant_set {H : Subgroup (Perm (Fin 7))} (h5 : ¬ 5 ∣ Nat.card H)
    (h7 : ¬ 7 ∣ Nat.card H) :
    ∃ Ω : Finset (Fin 7), (Ω.card = 1 ∨ Ω.card = 3) ∧ H ≤ permSetStab (Ω : Set (Fin 7)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  have hP2 : IsPGroup 2 (P : Subgroup ↥H) := P.isPGroup'
  have hmod := hP2.card_modEq_card_fixedPoints (Fin 7)
  have hfix : ∃ x₀ : Fin 7, ∀ g : (P : Subgroup ↥H), g • x₀ = x₀ := by
    have hpos : 0 < Nat.card ↥(MulAction.fixedPoints (P : Subgroup ↥H) (Fin 7)) := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      rw [h0, Nat.card_fin] at hmod
      exact absurd hmod (by decide)
    obtain ⟨⟨x₀, hx₀⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨x₀, MulAction.mem_fixedPoints.mp hx₀⟩
  obtain ⟨x₀, hx₀⟩ := hfix
  have hstab : (P : Subgroup ↥H) ≤ MulAction.stabilizer ↥H x₀ := fun g hg => by
    rw [MulAction.mem_stabilizer_iff]
    exact hx₀ ⟨g, hg⟩
  have hodd : ¬ 2 ∣ (MulAction.stabilizer ↥H x₀).index := fun h =>
    P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hstab))
  have hdvd : (MulAction.stabilizer ↥H x₀).index ∣ Nat.card H := Subgroup.index_dvd_card _
  have hle : (MulAction.stabilizer ↥H x₀).index ≤ 7 := by
    rw [MulAction.index_stabilizer]
    calc (MulAction.orbit ↥H x₀).ncard ≤ (Set.univ : Set (Fin 7)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      _ = 7 := by rw [Set.ncard_univ, Nat.card_fin]
  have hpos : 0 < (MulAction.stabilizer ↥H x₀).index := Nat.pos_of_ne_zero (by
    intro h0
    rw [h0] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (Nat.card_pos (α := ↥H)).ne')
  have hcard : (MulAction.orbit ↥H x₀).ncard = 1 ∨ (MulAction.orbit ↥H x₀).ncard = 3 := by
    rw [← MulAction.index_stabilizer]
    generalize (MulAction.stabilizer ↥H x₀).index = d at hodd hdvd hle hpos
    interval_cases d
    · exact Or.inl rfl
    · exact absurd (dvd_refl 2) hodd
    · exact Or.inr rfl
    · exact absurd (by norm_num : 2 ∣ 4) hodd
    · exact absurd hdvd h5
    · exact absurd (by norm_num : 2 ∣ 6) hodd
    · exact absurd hdvd h7
  have hfin : (MulAction.orbit ↥H x₀).Finite := Set.toFinite _
  refine ⟨hfin.toFinset, ?_, fun h hh y => ?_⟩
  · rw [← Set.ncard_eq_toFinset_card (MulAction.orbit ↥H x₀) hfin]
    exact hcard
  · have key : ∀ h : Perm (Fin 7), h ∈ H → ∀ y, y ∈ (hfin.toFinset : Set (Fin 7)) →
        h y ∈ (hfin.toFinset : Set (Fin 7)) := by
      intro h hh y hy
      rw [Finset.mem_coe, Set.Finite.mem_toFinset, MulAction.mem_orbit_iff] at hy ⊢
      obtain ⟨g, hg⟩ := hy
      exact ⟨⟨h, hh⟩ * g, by rw [mul_smul, hg]; rfl⟩
    refine ⟨fun hy => ?_, key h hh y⟩
    have := key h⁻¹ (H.inv_mem hh) (h y) hy
    simpa using this

theorem exists_threeCycle_on {A : Finset (Fin 7)} (hA : A.card = 3) :
    ∃ c : Perm (Fin 7), c ∈ alternatingGroup (Fin 7) ∧ orderOf c = 3 ∧ (∀ y, y ∉ A → c y = y) ∧
      (∀ y, y ∈ A → c y ∈ A) ∧ ∃ a ∈ A, c a ≠ a := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hA
  have h3 := Perm.isThreeCycle_swap_mul_swap_same hxy hxz hyz
  have hout : ∀ w, w ∉ ({x, y, z} : Finset (Fin 7)) → (swap x y * swap x z) w = w := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hw.1 hw.2.2, swap_apply_of_ne_of_ne hw.1 hw.2.1]
  refine ⟨swap x y * swap x z, Perm.mem_alternatingGroup.mpr h3.sign, h3.orderOf, hout, ?_, ?_⟩
  · intro w hw
    by_contra hcon
    have h1 := hout _ hcon
    have h2 := (swap x y * swap x z).injective h1
    rw [h2] at hcon
    exact hcon hw
  · refine ⟨x, by simp, ?_⟩
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hxz.symm hyz.symm]
    exact hxz.symm

theorem pow_eq_one_of_mem_closure_pair_of_commute {G : Type*} [Group G] {a b : G} (hab : Commute a b) {n : ℕ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ n = 1 := by
  have hs : ({a, b} : Set G) ⊆ Subgroup.centralizer ({a, b} : Set G) := by
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · rfl
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hab.symm.eq
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rcases hy with rfl | hy
      · exact hab.eq
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        rfl
  have h1 : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({a, b} : Set G) :=
    (Subgroup.closure_le_centralizer_centralizer _).trans (Subgroup.centralizer_le hs)
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b} : Set G), ∀ y ∈ Subgroup.closure ({a, b} : Set G),
      Commute x y := by
    intro x hx y hy
    have hxc := Subgroup.mem_centralizer_iff.mp (h1 hx)
    have h2 : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (hxc h hh).symm
    exact Subgroup.mem_centralizer_iff.mp (h2 hy) x rfl
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hb
  | one => exact one_pow n
  | mul x y hx hy ihx ihy => rw [(hcomm x hx y hy).mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem exists_noncyclic_three_group {A B : Finset (Fin 7)} (hA : A.card = 3) (hB : B.card = 3)
    (hAB : Disjoint A B) :
    ∃ E : Subgroup (Perm (Fin 7)), E ≤ alternatingGroup (Fin 7) ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧
      E ≤ permSetStab (A : Set (Fin 7)) ∧ E ≤ permSetStab (B : Set (Fin 7)) ∧
        E ≤ fixOutside ((A ∪ B : Finset (Fin 7)) : Set (Fin 7)) := by
  classical
  obtain ⟨c₁, hc₁A, hc₁o, hc₁f, hc₁m, a, haA, hca⟩ := exists_threeCycle_on hA
  obtain ⟨c₂, hc₂A, hc₂o, hc₂f, hc₂m, b, hbB, hcb⟩ := exists_threeCycle_on hB
  have hdis : ∀ w, w ∈ A → w ∉ B := fun w hw hwB => Finset.disjoint_left.mp hAB hw hwB
  have hcomm : Commute c₁ c₂ := by
    refine Perm.ext fun w => ?_
    show c₁ (c₂ w) = c₂ (c₁ w)
    by_cases hwA : w ∈ A
    · have h1 : c₂ w = w := hc₂f w (hdis w hwA)
      have h2 : c₂ (c₁ w) = c₁ w := hc₂f _ (hdis _ (hc₁m w hwA))
      rw [h1, h2]
    · by_cases hwB : w ∈ B
      · have h1 : c₁ w = w := hc₁f w hwA
        have h2 : c₁ (c₂ w) = c₂ w := hc₁f _ (fun h => hdis _ h (hc₂m w hwB))
        rw [h1, h2]
      · have h1 := hc₁f w hwA
        have h2 := hc₂f w hwB
        rw [h2, h1, h2]
  have hc₁3 : c₁ ^ 3 = 1 := by rw [← hc₁o]; exact pow_orderOf_eq_one c₁
  have hc₂3 : c₂ ^ 3 = 1 := by rw [← hc₂o]; exact pow_orderOf_eq_one c₂
  have hmemA : c₁ ∈ permSetStab (A : Set (Fin 7)) := fun y => by
    rw [Finset.mem_coe, Finset.mem_coe]
    refine ⟨fun h => ?_, hc₁m y⟩
    by_contra hy
    rw [hc₁f y hy] at h
    exact hy h
  have hmemB : c₂ ∈ permSetStab (B : Set (Fin 7)) := fun y => by
    rw [Finset.mem_coe, Finset.mem_coe]
    refine ⟨fun h => ?_, hc₂m y⟩
    by_contra hy
    rw [hc₂f y hy] at h
    exact hy h
  have hc₁stB : c₁ ∈ permSetStab (B : Set (Fin 7)) := fun y => by
    rw [Finset.mem_coe, Finset.mem_coe]
    by_cases hyA : y ∈ A
    · exact ⟨fun h => absurd h (hdis _ (hc₁m y hyA)), fun h => absurd h (hdis y hyA)⟩
    · rw [hc₁f y hyA]
  have hc₂stA : c₂ ∈ permSetStab (A : Set (Fin 7)) := fun y => by
    rw [Finset.mem_coe, Finset.mem_coe]
    by_cases hyB : y ∈ B
    · have h1 : y ∉ A := fun h => hdis y h hyB
      have h2 : c₂ y ∉ A := fun h => hdis _ h (hc₂m y hyB)
      exact ⟨fun h => absurd h h2, fun h => absurd h h1⟩
    · rw [hc₂f y hyB]
  have hfix₁ : c₁ ∈ fixOutside ((A ∪ B : Finset (Fin 7)) : Set (Fin 7)) := fun y hy => by
    rw [Finset.mem_coe, Finset.mem_union, not_or] at hy
    exact hc₁f y hy.1
  have hfix₂ : c₂ ∈ fixOutside ((A ∪ B : Finset (Fin 7)) : Set (Fin 7)) := fun y hy => by
    rw [Finset.mem_coe, Finset.mem_union, not_or] at hy
    exact hc₂f y hy.2
  refine ⟨Subgroup.closure {c₁, c₂}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact hc₁A
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hc₂A
  · intro g
    exact ⟨1, Subtype.ext (by simpa using pow_eq_one_of_mem_closure_pair_of_commute hcomm hc₁3 hc₂3 g g.2)⟩
  · intro hcyc
    have hcard : Nat.card (Subgroup.closure ({c₁, c₂} : Set (Perm (Fin 7)))) ∣ 3 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using pow_eq_one_of_mem_closure_pair_of_commute hcomm hc₁3 hc₂3 g g.2)
    have hz : Subgroup.zpowers c₁ ≤ Subgroup.closure ({c₁, c₂} : Set (Perm (Fin 7))) :=
      (Subgroup.zpowers_le).mpr (Subgroup.subset_closure (by simp))
    have heq : Subgroup.zpowers c₁ = Subgroup.closure ({c₁, c₂} : Set (Perm (Fin 7))) := by
      refine Subgroup.eq_of_le_of_card_ge hz ?_
      rw [Nat.card_zpowers, hc₁o]
      exact Nat.le_of_dvd (by norm_num) hcard
    have hc₂z : c₂ ∈ Subgroup.zpowers c₁ := by
      rw [heq]
      exact Subgroup.subset_closure (by simp)
    have hzle : Subgroup.zpowers c₁ ≤ fixOutside (A : Set (Fin 7)) := by
      rw [Subgroup.zpowers_le]
      exact fun y hy => hc₁f y hy
    have hbA : b ∉ A := fun h => hdis b h hbB
    exact hcb (hzle hc₂z b hbA)
  · rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact hmemA
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hc₂stA
  · rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact hc₁stB
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hmemB
  · rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact hfix₁
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hfix₂

theorem exists_overgroup_of_card_coprime {H : Subgroup (Perm (Fin 7))} (h5 : ¬ 5 ∣ Nat.card H)
    (h7 : ¬ 7 ∣ Nat.card H) :
    ∃ K : Subgroup (Perm (Fin 7)), H ≤ K ∧ ¬ alternatingGroup (Fin 7) ≤ K ∧
      ∃ E : Subgroup (Perm (Fin 7)), E ≤ K ⊓ alternatingGroup (Fin 7) ∧ IsPGroup 3 ↥E ∧
        ¬ IsCyclic ↥E := by
  classical
  obtain ⟨Ω, hΩ, hHΩ⟩ := exists_small_invariant_set h5 h7
  refine ⟨permSetStab (Ω : Set (Fin 7)), hHΩ, ?_, ?_⟩
  ·
    intro hA7
    have hΩne : Ω.Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨a, ha⟩ := hΩne
    have hcompl : 2 ≤ Ωᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp hcompl
    rw [Finset.mem_compl] at hb hc
    have hab : a ≠ b := fun h => hb (h ▸ ha)
    have hac : a ≠ c := fun h => hc (h ▸ ha)
    have h3 := Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
    have hσ : swap a b * swap a c ∈ alternatingGroup (Fin 7) := Perm.mem_alternatingGroup.mpr h3.sign
    have := hA7 hσ a
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm] at this
    exact hc (Finset.mem_coe.mp (this.mpr (Finset.mem_coe.mpr ha)))
  · have hcompl : Ωᶜ.card = 7 - Ω.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    rcases hΩ with h1 | h3
    ·
      obtain ⟨A, hAΩ, hA⟩ := Finset.exists_subset_card_eq (s := Ωᶜ) (n := 3) (by omega)
      have hsd : (Ωᶜ \ A).card = 3 := by
        rw [Finset.card_sdiff_of_subset hAΩ, hA]
        omega
      obtain ⟨B, hBΩ, hB⟩ := Finset.exists_subset_card_eq (s := Ωᶜ \ A) (n := 3) (by omega)
      have hdis : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        exact (Finset.mem_sdiff.mp (hBΩ hxB)).2 hxA
      obtain ⟨E, hEA, hEp, hEc, hEsA, hEsB, hEf⟩ := exists_noncyclic_three_group hA hB hdis
      have hBc : ∀ y, y ∈ B → y ∉ Ω := fun y hy h =>
        (Finset.mem_compl.mp (Finset.mem_sdiff.mp (hBΩ hy)).1) h
      have hEK : E ≤ permSetStab (Ω : Set (Fin 7)) := by
        intro σ hσ y
        rw [Finset.mem_coe, Finset.mem_coe]
        by_cases hyA : y ∈ A
        · have h1 : y ∉ Ω := fun h => (Finset.mem_compl.mp (hAΩ hyA)) h
          have h2 : σ y ∈ A := by
            have := mem_permSetStab.mp (hEsA hσ) y
            rw [Finset.mem_coe, Finset.mem_coe] at this
            exact this.mpr hyA
          have h3 : σ y ∉ Ω := fun h => (Finset.mem_compl.mp (hAΩ h2)) h
          exact ⟨fun h => absurd h h3, fun h => absurd h h1⟩
        · by_cases hyB : y ∈ B
          · have h1 : y ∉ Ω := hBc y hyB
            have h2 : σ y ∈ B := by
              have := mem_permSetStab.mp (hEsB hσ) y
              rw [Finset.mem_coe, Finset.mem_coe] at this
              exact this.mpr hyB
            have h3 : σ y ∉ Ω := hBc _ h2
            exact ⟨fun h => absurd h h3, fun h => absurd h h1⟩
          · have hyAB : y ∉ ((A ∪ B : Finset (Fin 7)) : Set (Fin 7)) := by
              rw [Finset.mem_coe, Finset.mem_union]
              exact fun h => h.elim hyA hyB
            rw [mem_fixOutside.mp (hEf hσ) y hyAB]
      exact ⟨E, le_inf hEK hEA, hEp, hEc⟩
    · obtain ⟨B, hBΩ, hB⟩ := Finset.exists_subset_card_eq (s := Ωᶜ) (n := 3) (by omega)
      have hdis : Disjoint Ω B := by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        exact (Finset.mem_compl.mp (hBΩ hxB)) hxA
      obtain ⟨E, hEA, hEp, hEc, hEΩ, -, -⟩ := exists_noncyclic_three_group h3 hB hdis
      exact ⟨E, le_inf hEΩ hEA, hEp, hEc⟩

end CFSG.Quasithin
