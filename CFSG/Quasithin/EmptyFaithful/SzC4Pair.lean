module

public import CFSG.Quasithin.EmptyFaithful.SBd7Case3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace SzC4

variable {G : Type} [Group G]

theorem exists_fixed_involution [Finite G] {S E : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hES : E ≤ S)
    (hSE : S ≤ Subgroup.normalizer (E : Set G)) (hE1 : E ≠ ⊥) (hEsq : ∀ e ∈ E, e * e = 1) :
    ∃ e ∈ E, e ≠ 1 ∧ e * e = 1 ∧ ∀ s ∈ S, s * e = e * s := by
  obtain ⟨e, he, he1, hec⟩ := SBd7.exists_central_of_normal hS2 hES hSE hE1
  exact ⟨e, he, he1, hEsq e he, fun s hs => mul_inv_eq_iff_eq_mul.mp (hec s hs)⟩

theorem mem_of_card_four [Finite G] {E : Subgroup G} (hE4 : Nat.card E = 4) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hab1 : a * b ≠ 1) :
    ∀ e ∈ E, e = 1 ∨ e = a ∨ e = b ∨ e = a * b := by
  classical
  intro e he
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have hcuE : a * b ∈ E := E.mul_mem ha hb
  have : Fintype ↥E := Fintype.ofFinite _
  have hsub : ({1, a, b, a * b, e} : Finset G) ⊆ (Finset.univ : Finset ↥E).image Subtype.val := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_image]
    rcases hx with h | h | h | h | h
    · exact ⟨⟨1, E.one_mem⟩, Finset.mem_univ _, h.symm⟩
    · exact ⟨⟨a, ha⟩, Finset.mem_univ _, h.symm⟩
    · exact ⟨⟨b, hb⟩, Finset.mem_univ _, h.symm⟩
    · exact ⟨⟨a * b, hcuE⟩, Finset.mem_univ _, h.symm⟩
    · exact ⟨⟨e, he⟩, Finset.mem_univ _, h.symm⟩
  have hcard5 : ({1, a, b, a * b, e} : Finset G).card = 5 := by
    have hne1 : (1 : G) ≠ a := fun h => ha1 h.symm
    have hne2 : (1 : G) ≠ b := fun h => hb1 h.symm
    have hne3 : (1 : G) ≠ a * b := fun h => hab1 h.symm
    have hne4 : (1 : G) ≠ e := fun h => h1 h.symm
    have hne6 : a ≠ a * b := fun h => hb1 (by
      have : a * 1 = a * b := by simpa using h
      exact (mul_left_cancel this).symm)
    have hne7 : a ≠ e := fun h => h2 h.symm
    have hne8 : b ≠ a * b := fun h => ha1 (by
      have : 1 * b = a * b := by simpa using h
      exact (mul_right_cancel this).symm)
    have hne9 : b ≠ e := fun h => h3 h.symm
    have hne10 : a * b ≠ e := fun h => h4 h.symm
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne1, hne2, hne3, hne4⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, hne6, hne7⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne8, hne9⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact hne10), Finset.card_singleton]
  have hle : ({1, a, b, a * b, e} : Finset G).card ≤
      ((Finset.univ : Finset ↥E).image Subtype.val).card := Finset.card_le_card hsub
  have hle2 : ((Finset.univ : Finset ↥E).image Subtype.val).card ≤ Fintype.card ↥E := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ]
  have hEcard : Fintype.card ↥E = 4 := by
    rw [← Nat.card_eq_fintype_card, hE4]
  omega

theorem case4_pair [Finite G] {L S C U E : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hUZ : IsSumOfNaturalModulesVia L U ⊥ α false 1)
    (hS2 : IsPGroup 2 ↥S) (hC4 : Nat.card C = 4) (hCsq : ∀ c ∈ C, c * c = 1) (hCS : C ≤ S)
    (hSC : S ≤ Subgroup.normalizer (C : Set G)) (hUS : U ≤ S)
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hCU : C ⊓ U = ⊥)
    (hE : omegaOneCenterOf S = E) (hE4 : Nat.card E = 4) :
    ∃ c₀ ∈ C, ∃ u₀ ∈ U, c₀ ≠ 1 ∧ u₀ ≠ 1 ∧ c₀ * u₀ ≠ 1 ∧ (∀ s ∈ S, s * c₀ = c₀ * s) ∧
      (∀ s ∈ S, s * u₀ = u₀ * s) ∧ c₀ ∈ E ∧ u₀ ∈ E ∧ c₀ * u₀ ∈ E ∧
      ∀ e ∈ E, e = 1 ∨ e = c₀ ∨ e = u₀ ∨ e = c₀ * u₀ := by
  classical
  have hmemΩ : ∀ x ∈ S, (∀ s ∈ S, s * x = x * s) → x * x = 1 → x ∈ E := by
    intro x hxS hxc hx2
    rw [← hE]
    refine Subgroup.subset_closure ⟨⟨hxS, Subgroup.mem_centralizer_iff.mpr fun s hs => hxc s hs⟩, ?_⟩
    rw [pow_two]
    exact hx2
  have hC1 : C ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hC4
    omega
  obtain ⟨c₀, hc₀C, hc₀1, hc₀c⟩ := SBd7.exists_central_of_normal hS2 hCS hSC hC1
  have hc₀c' : ∀ s ∈ S, s * c₀ = c₀ * s := fun s hs => mul_inv_eq_iff_eq_mul.mp (hc₀c s hs)
  obtain ⟨-, -, β, hβs, hβk, -⟩ := hUZ
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hU1 : U ≠ ⊥ := by
    intro hb
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (fun _ _ => (1 : F)))
    have hu1 : (u : G) = 1 := by
      have : (u : G) ∈ (⊥ : Subgroup G) := hb ▸ u.2
      exact (Subgroup.mem_bot).mp this
    have : u = 1 := Subtype.ext hu1
    rw [this, map_one] at hu
    have h2 := congrArg (fun w : Multiplicative (Fin 1 → Fin 3 → F) =>
      Multiplicative.toAdd w (0 : Fin 1) (0 : Fin 3)) hu
    simp at h2
  obtain ⟨u₀, hu₀U, hu₀1, hu₀c⟩ := SBd7.exists_central_of_normal hS2 hUS hSU hU1
  have hu₀c' : ∀ s ∈ S, s * u₀ = u₀ * s := fun s hs => mul_inv_eq_iff_eq_mul.mp (hu₀c s hs)
  have hu₀sq : u₀ * u₀ = 1 := by
    have : (⟨u₀ * u₀, U.mul_mem hu₀U hu₀U⟩ : ↥U) = 1 := by
      apply hβi
      rw [show (⟨u₀ * u₀, U.mul_mem hu₀U hu₀U⟩ : ↥U) = ⟨u₀, hu₀U⟩ * ⟨u₀, hu₀U⟩ from rfl, map_mul,
        map_one]
      apply Multiplicative.toAdd.injective
      funext i j
      simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
      exact SBd7.add_self_eq_zero_of_card_two hF _
    exact congrArg Subtype.val this
  have hc₀E : c₀ ∈ E := hmemΩ c₀ (hCS hc₀C) hc₀c' (hCsq c₀ hc₀C)
  have hu₀E : u₀ ∈ E := hmemΩ u₀ (hUS hu₀U) hu₀c' hu₀sq
  have hcu : c₀ ≠ u₀ := by
    intro h
    have : u₀ ∈ C ⊓ U := ⟨h ▸ hc₀C, hu₀U⟩
    rw [hCU, Subgroup.mem_bot] at this
    exact hu₀1 this
  have hcomm : c₀ * u₀ = u₀ * c₀ := by
    have := hc₀c' u₀ (hUS hu₀U)
    exact this.symm
  have hcu1 : c₀ * u₀ ≠ 1 := by
    intro h
    apply hcu
    have h1 : c₀ = u₀⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1]
    exact (inv_eq_of_mul_eq_one_right hu₀sq)
  have hcuE : c₀ * u₀ ∈ E := E.mul_mem hc₀E hu₀E
  exact ⟨c₀, hc₀C, u₀, hu₀U, hc₀1, hu₀1, hcu1, hc₀c', hu₀c', hc₀E, hu₀E, hcuE,
    mem_of_card_four hE4 hc₀E hu₀E hc₀1 hu₀1 hcu hcu1⟩

end SzC4

end CFSG.Quasithin
