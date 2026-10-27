module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.WeakClosure81.DynkinAlt6

open Equiv Subgroup

theorem isCoatom_of_card_eq_24 {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : Nat.card X = 360) {Y : Subgroup X} (hY : Nat.card Y = 24) : IsCoatom Y := by
  refine ⟨fun h => ?_, fun Z hYZ => ?_⟩
  · rw [h, Subgroup.card_top, hX] at hY
    norm_num at hY
  have hdvd : Nat.card Y ∣ Nat.card Z := Subgroup.card_dvd_of_le hYZ.le
  have hlt : Nat.card Y < Nat.card Z := Subgroup.card_lt_of_lt hYZ
  rw [hY] at hdvd hlt
  obtain ⟨m, hm⟩ := hdvd
  have hmi := Z.card_mul_index
  rw [hX, hm, mul_assoc] at hmi
  have h15 : m * Z.index = 15 := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 24)
    (hmi.trans (by norm_num))
  have hm1 : 1 < m := by omega
  have hi_dvd : Z.index ∣ 15 := ⟨m, by rw [mul_comm]; exact h15.symm⟩
  have hi_pos : 0 < Z.index := Nat.pos_of_dvd_of_pos hi_dvd (by norm_num)
  have hi_le : Z.index ≤ 7 := by
    by_contra h
    have : 2 * 8 ≤ m * Z.index := Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [← Subgroup.index_eq_one]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Z.normalCore with hc | hc
  · have hd := Subgroup.index_normalCore_dvd_factorial_index (H := Z)
    rw [hc, Subgroup.index_bot, hX] at hd
    interval_cases h : Z.index <;> first | rfl | (revert hd; decide) | (norm_num at hi_dvd)
  · have hZ : Z = ⊤ := top_le_iff.mp (hc ▸ Subgroup.normalCore_le Z)
    rw [hZ, Subgroup.index_top]

@[expose] def d0List : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3,
    swap 0 3 * swap 3 2 * swap 2 1 * swap 4 5, swap 0 2 * swap 4 5, swap 1 3 * swap 4 5,
    swap 0 1 * swap 2 3, swap 0 3 * swap 1 2]

@[expose] def rho : Perm (Fin 6) := swap 0 2 * swap 1 3 * swap 4 5

theorem d0List_mul : ∀ v ∈ d0List, ∀ w ∈ d0List, v * w ∈ d0List := by decide +kernel

theorem d0List_inv : ∀ v ∈ d0List, v⁻¹ ∈ d0List := by decide +kernel

theorem d0List_sign : ∀ v ∈ d0List, Perm.sign v = 1 := by decide +kernel

theorem d0List_norm : ∀ σ : Perm (Fin 6), (∀ v ∈ d0List, σ * v * σ⁻¹ ∈ d0List) →
    (∀ x : Fin 6, (x = 4 ∨ x = 5) ↔ (σ x = 4 ∨ σ x = 5)) ∧ σ * rho = rho * σ := by
  decide +kernel

@[expose] def stab45 : Subgroup (Perm (Fin 6)) where
  carrier := {σ | ∀ x : Fin 6, (x = 4 ∨ x = 5) ↔ (σ x = 4 ∨ σ x = 5)}
  mul_mem' {σ τ} hσ hτ x := (hτ x).trans (hσ (τ x))
  one_mem' x := Iff.rfl
  inv_mem' {σ} hσ x := by
    have h := hσ (σ⁻¹ x)
    have hx : σ (σ⁻¹ x) = x := by simp
    rw [hx] at h
    exact h.symm

local instance : DecidablePred (· ∈ stab45) := fun σ =>
  inferInstanceAs (Decidable (∀ x : Fin 6, (x = 4 ∨ x = 5) ↔ (σ x = 4 ∨ σ x = 5)))

abbrev A6 : Type := alternatingGroup (Fin 6)

local instance : DecidablePred (· ∈ alternatingGroup (Fin 6)) := Perm.sign.decidableMemKer

local instance : DecidablePred (· ∈ alternatingGroup (Fin 6) ⊓ stab45) := fun σ =>
  decidable_of_iff (σ ∈ alternatingGroup (Fin 6) ∧ σ ∈ stab45) Subgroup.mem_inf.symm

@[expose] def d0 : Subgroup A6 where
  carrier := {g | (g : Perm (Fin 6)) ∈ d0List}
  mul_mem' {g h} hg hh := by
    change ((g : Perm (Fin 6)) * h) ∈ d0List
    exact d0List_mul _ hg _ hh
  one_mem' := by
    change (1 : Perm (Fin 6)) ∈ d0List
    decide
  inv_mem' {g} hg := by
    change ((g : Perm (Fin 6)))⁻¹ ∈ d0List
    exact d0List_inv _ hg

@[expose] def p1 : Subgroup A6 := stab45.comap (alternatingGroup (Fin 6)).subtype

@[expose] def p2 : Subgroup A6 := (centralizer {rho}).comap (alternatingGroup (Fin 6)).subtype

local instance : DecidablePred (· ∈ d0) := fun g =>
  inferInstanceAs (Decidable ((g : Perm (Fin 6)) ∈ d0List))

local instance : DecidablePred (· ∈ alternatingGroup (Fin 6) ⊓ centralizer {rho}) := fun σ =>
  decidable_of_iff (σ ∈ alternatingGroup (Fin 6) ∧ σ * rho = rho * σ)
    (Subgroup.mem_inf.trans (and_congr_right' Subgroup.mem_centralizer_singleton_iff)).symm

theorem mem_p2 {g : A6} : g ∈ p2 ↔ (g : Perm (Fin 6)) * rho = rho * g := by
  simp only [p2, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]

theorem card_A6 : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

local instance : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)

theorem card_stab45_inf : Nat.card ↥(alternatingGroup (Fin 6) ⊓ stab45) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_centralizer_inf :
    Nat.card ↥(alternatingGroup (Fin 6) ⊓ centralizer {rho}) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_d0 : Nat.card d0 = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_comap_subtype (K : Subgroup (Perm (Fin 6))) :
    Nat.card ↥(K.comap (alternatingGroup (Fin 6)).subtype) =
      Nat.card ↥(alternatingGroup (Fin 6) ⊓ K) := by
  rw [← Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective,
    Subgroup.map_comap_eq, Subgroup.range_subtype]

theorem card_p1 : Nat.card p1 = 24 := by
  rw [p1, card_comap_subtype, card_stab45_inf]

theorem card_p2 : Nat.card p2 = 24 := by
  rw [p2, card_comap_subtype, card_centralizer_inf]

theorem p1_ne_p2 : p1 ≠ p2 := by
  intro h
  have hw : (⟨swap 0 1 * swap 4 5, by decide⟩ : A6) ∈ p1 := by
    change swap 0 1 * swap 4 5 ∈ stab45
    decide
  rw [h, mem_p2] at hw
  revert hw
  decide

theorem normalizer_d0_le : normalizer (d0 : Set A6) ≤ p1 ⊓ p2 := by
  intro g hg
  have hn : ∀ v ∈ d0List, (g : Perm (Fin 6)) * v * (g : Perm (Fin 6))⁻¹ ∈ d0List := by
    intro v hv
    have hvA : v ∈ alternatingGroup (Fin 6) := d0List_sign v hv
    have h := (Subgroup.mem_normalizer_iff.mp hg ⟨v, hvA⟩).mp hv
    exact h
  obtain ⟨h1, h2⟩ := d0List_norm _ hn
  exact ⟨h1, mem_p2.mpr h2⟩

theorem card_comap_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (K : Subgroup Y) :
    Nat.card (K.comap e.toMonoidHom) = Nat.card K := by
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
    Subgroup.map_comap_eq_self_of_surjective e.surjective]

theorem exists_two_isCoatom_of_alt6 {X : Type*} [Group X] [Finite X] (ψ : X ≃* A6)
    {D : Subgroup X} (hD : IsPGroup 2 D) (hDi : ¬ 2 ∣ D.index) :
    ∃ P₁ P₂ : Subgroup X, P₁ ≠ P₂ ∧ IsCoatom P₁ ∧ IsCoatom P₂ ∧
      normalizer (D : Set X) ≤ P₁ ∧ normalizer (D : Set X) ≤ P₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial X := ψ.toEquiv.nontrivial
  have : IsSimpleGroup X :=
    IsSimpleGroup.isSimpleGroup_of_surjective ψ.symm.toMonoidHom ψ.symm.surjective
  have hX : Nat.card X = 360 := (Nat.card_congr ψ.toEquiv).trans card_A6
  set D0X : Subgroup X := d0.comap ψ.toMonoidHom with hD0X
  have hcard0 : Nat.card D0X = 8 := by rw [hD0X, card_comap_mulEquiv, card_d0]
  have hD0p : IsPGroup 2 D0X := IsPGroup.of_card (n := 3) (by rw [hcard0]; norm_num)
  have hD0i : ¬ 2 ∣ D0X.index := by
    have h := D0X.card_mul_index
    rw [hcard0, hX] at h
    have h45 : D0X.index = 45 := by omega
    rw [h45]
    norm_num
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X (hD0p.toSylow hD0i) (hD.toSylow hDi)
  have hmemD : ∀ y : X, y ∈ D ↔ x⁻¹ * y * x ∈ D0X := by
    intro y
    have h := congrArg (fun P : Sylow 2 X => y ∈ (P : Subgroup X)) hx
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, eq_iff_iff] at h
    rw [← h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  let Pc : Subgroup A6 → Subgroup X := fun K =>
    (K.comap ψ.toMonoidHom).comap (MulAut.conj x⁻¹).toMonoidHom
  have hmemP : ∀ (K : Subgroup A6) (y : X), y ∈ Pc K ↔ ψ (x⁻¹ * y * x) ∈ K := by
    intro K y
    simp [Pc]
  have hcardP : ∀ K : Subgroup A6, Nat.card (Pc K) = Nat.card K := fun K => by
    simp only [Pc]
    rw [card_comap_mulEquiv, card_comap_mulEquiv]
  have hN : ∀ y ∈ normalizer (D : Set X), ψ (x⁻¹ * y * x) ∈ normalizer (d0 : Set A6) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro h
    have h1 : h ∈ d0 ↔ x * ψ.symm h * x⁻¹ ∈ D := by
      rw [hmemD, hD0X, Subgroup.mem_comap]
      simp [mul_assoc]
    rw [h1, hy, hmemD, hD0X, Subgroup.mem_comap]
    simp [mul_assoc]
  refine ⟨Pc p1, Pc p2, fun h => p1_ne_p2 ?_, isCoatom_of_card_eq_24 hX ?_,
    isCoatom_of_card_eq_24 hX ?_, fun y hy => ?_, fun y hy => ?_⟩
  · ext g
    have := SetLike.ext_iff.mp h (x * ψ.symm g * x⁻¹)
    simpa [hmemP, mul_assoc] using this
  · rw [hcardP, card_p1]
  · rw [hcardP, card_p2]
  · exact (hmemP p1 y).mpr (normalizer_d0_le (hN y hy)).1
  · exact (hmemP p2 y).mpr (normalizer_d0_le (hN y hy)).2

end CFSG.LocalAnalysis.WeakClosure81.DynkinAlt6

end
