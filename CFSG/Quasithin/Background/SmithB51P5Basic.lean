module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace B5

namespace P5

variable {V : Type} [CommGroup V]

theorem mem_fixV_zpowers_iff {t : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers t) ↔ t v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem fixV_sup_eq (A D : Subgroup (MulAut V)) : fixV (A ⊔ D) = fixV A ⊓ fixV D :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq A D

variable [Finite V]

theorem sup_fixV_eq_top_of_card_le {G A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    {U : Subgroup V} (h : Nat.card A * Nat.card ↥(U ⊓ fixV A) ≤ Nat.card U) :
    U ⊔ fixV A = ⊤ ∧ Nat.card A * Nat.card ↥(U ⊓ fixV A) = Nat.card U := by
  have hv : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
    rwa [B1.card_bot_mul_card_fixV] at this
  have hp := card_mul_card_fixV_le A U
  have hc : 0 < Nat.card ↥(U ⊓ fixV A) := Nat.card_pos
  have hf : 0 < Nat.card (fixV A) := Nat.card_pos
  have hsV : Nat.card ↥(U ⊔ fixV A) ≤ Nat.card V := by
    simpa using Subgroup.card_le_of_le (le_top : U ⊔ fixV A ≤ ⊤)
  have hge : Nat.card V ≤ Nat.card ↥(U ⊔ fixV A) := by
    have h1 : Nat.card V * Nat.card ↥(U ⊓ fixV A) ≤
        Nat.card ↥(U ⊔ fixV A) * Nat.card ↥(U ⊓ fixV A) := by
      calc Nat.card V * Nat.card ↥(U ⊓ fixV A)
          ≤ Nat.card A * Nat.card (fixV A) * Nat.card ↥(U ⊓ fixV A) :=
            Nat.mul_le_mul_right _ hv
        _ = Nat.card A * Nat.card ↥(U ⊓ fixV A) * Nat.card (fixV A) := by ring
        _ ≤ Nat.card U * Nat.card (fixV A) := Nat.mul_le_mul_right _ h
        _ = _ := hp.symm
    exact Nat.le_of_mul_le_mul_right h1 hc
  have htop : U ⊔ fixV A = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact le_antisymm hsV hge
  refine ⟨htop, le_antisymm h ?_⟩
  have h2 : Nat.card U * Nat.card (fixV A) ≤
      Nat.card A * Nat.card ↥(U ⊓ fixV A) * Nat.card (fixV A) := by
    calc Nat.card U * Nat.card (fixV A) = Nat.card ↥(U ⊔ fixV A) * Nat.card ↥(U ⊓ fixV A) :=
          hp.symm
      _ ≤ Nat.card V * Nat.card ↥(U ⊓ fixV A) := Nat.mul_le_mul_right _ hsV
      _ ≤ Nat.card A * Nat.card (fixV A) * Nat.card ↥(U ⊓ fixV A) :=
          Nat.mul_le_mul_right _ hv
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h2 hf

omit [Finite V] in
theorem mem_fixV_of_normalizes {A : Subgroup (MulAut V)} {t : MulAut V}
    (htA : ∀ a ∈ A, t⁻¹ * a * t ∈ A) {v : V} (hv : v ∈ fixV A) : t v ∈ fixV A := by
  intro a ha
  have h1 := hv _ (htA a ha)
  have h2 : (t⁻¹ * a * t) v = t⁻¹ (a (t v)) := rfl
  rw [h2] at h1
  have h3 := congrArg t h1
  simpa using h3

omit [Finite V] in
theorem fixV_le_sup_fixV_of_lift (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    {U : Subgroup V} {t : MulAut V} (htA : ∀ a ∈ A, t⁻¹ * a * t ∈ A) (ht2 : t ^ 2 ∈ A)
    (hcU : ∀ v : V, t v * v⁻¹ ∈ U)
    (hlift : ∀ x ∈ U ⊓ fixV (A ⊔ Subgroup.zpowers t), ∃ u ∈ U ⊓ fixV A, t u * u⁻¹ = x) :
    fixV A ≤ U ⊔ fixV (A ⊔ Subgroup.zpowers t) := by
  intro v hv
  have hinv : ∀ y : V, y⁻¹ = y := fun y => by
    have := hV y
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  have htv : t v ∈ fixV A := mem_fixV_of_normalizes htA hv
  have ht2v : t (t v) = v := by
    have := hv _ ht2
    rwa [pow_two] at this
  set x := t v * v⁻¹ with hx
  have hxA : x ∈ fixV A := (fixV A).mul_mem htv ((fixV A).inv_mem hv)
  have htx : t x = x := by
    rw [hx, map_mul, map_inv, ht2v, hinv (t v), hinv v, mul_comm]
  have hxT : x ∈ U ⊓ fixV (A ⊔ Subgroup.zpowers t) := by
    refine ⟨hcU v, ?_⟩
    rw [fixV_sup_eq]
    exact ⟨hxA, mem_fixV_zpowers_iff.2 htx⟩
  obtain ⟨u, ⟨huU, huA⟩, hux⟩ := hlift x hxT
  have hv' : v * u⁻¹ ∈ fixV (A ⊔ Subgroup.zpowers t) := by
    rw [fixV_sup_eq]
    refine ⟨(fixV A).mul_mem hv ((fixV A).inv_mem huA), mem_fixV_zpowers_iff.2 ?_⟩
    have h1 : t v = x * v := by rw [hx, inv_mul_cancel_right]
    have h2 : t u = x * u := by rw [← hux, inv_mul_cancel_right]
    rw [map_mul, map_inv, h1, h2, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv]
  have : v = u * (v * u⁻¹) := by rw [mul_comm v, mul_inv_cancel_left]
  rw [this]
  exact Subgroup.mul_mem_sup huU hv'

theorem lift_of_card (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} {U : Subgroup V}
    {t : MulAut V} (htA : ∀ a ∈ A, t⁻¹ * a * t ∈ A) (ht2 : t ^ 2 ∈ A)
    (hUt : ∀ u ∈ U, t u ∈ U)
    (hcard : Nat.card ↥(U ⊓ fixV A) = Nat.card ↥(U ⊓ fixV (A ⊔ Subgroup.zpowers t)) ^ 2) :
    ∀ x ∈ U ⊓ fixV (A ⊔ Subgroup.zpowers t), ∃ u ∈ U ⊓ fixV A, t u * u⁻¹ = x := by
  have hinv : ∀ y : V, y⁻¹ = y := fun y => by
    have := hV y
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  set C := U ⊓ fixV A with hC
  set D := U ⊓ fixV (A ⊔ Subgroup.zpowers t) with hD
  have hmemC : ∀ u ∈ C, t u * u⁻¹ ∈ C := fun u hu =>
    C.mul_mem ⟨hUt u hu.1, mem_fixV_of_normalizes htA hu.2⟩ (C.inv_mem hu)
  let φ : ↥C →* V :=
    { toFun := fun u => t (u : V) * (u : V)⁻¹
      map_one' := by simp
      map_mul' := fun u w => by
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        rw [mul_comm (w : V)⁻¹ (u : V)⁻¹]
        simp only [mul_assoc, mul_left_comm] }
  have hφ : ∀ u : ↥C, φ u = t (u : V) * (u : V)⁻¹ := fun _ => rfl
  have hrange : φ.range ≤ D := by
    rintro _ ⟨u, rfl⟩
    rw [hφ]
    have hu := hmemC u u.2
    refine ⟨hu.1, ?_⟩
    rw [fixV_sup_eq]
    refine ⟨hu.2, mem_fixV_zpowers_iff.2 ?_⟩
    have ht2u : t (t (u : V)) = u := by
      have := u.2.2 _ ht2
      rwa [pow_two] at this
    rw [map_mul, map_inv, ht2u, hinv (t (u : V)), hinv (u : V), mul_comm]
  have hker : Nat.card φ.ker = Nat.card D := by
    refine Nat.card_congr
      { toFun := fun u => ⟨((u : ↥C) : V), ⟨(u : ↥C).2.1, ?_⟩⟩
        invFun := fun d => ⟨⟨(d : V), ⟨d.2.1, ?_⟩⟩, ?_⟩
        left_inv := fun u => rfl
        right_inv := fun d => rfl }
    · rw [fixV_sup_eq]
      refine ⟨(u : ↥C).2.2, mem_fixV_zpowers_iff.2 ?_⟩
      have h1 : φ (u : ↥C) = 1 := u.2
      rw [hφ, mul_inv_eq_one] at h1
      exact h1
    · have h1 := d.2.2
      rw [fixV_sup_eq] at h1
      exact h1.1
    · show φ _ = 1
      rw [hφ, mul_inv_eq_one]
      have h1 := d.2.2
      rw [fixV_sup_eq] at h1
      exact mem_fixV_zpowers_iff.1 h1.2
  have hcardC : Nat.card φ.range * Nat.card φ.ker = Nat.card C := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hrD : Nat.card φ.range = Nat.card D := by
    rw [hker, hcard, pow_two] at hcardC
    exact Nat.eq_of_mul_eq_mul_right hDpos hcardC
  have heq : φ.range = D := Subgroup.eq_of_le_of_card_ge hrange (le_of_eq hrD.symm)
  intro x hx
  rw [← heq] at hx
  obtain ⟨u, hu⟩ := hx
  exact ⟨u, u.2, hu⟩

end P5

end B5

@[expose] def AsB51G2Dual : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → ∀ G L : Subgroup (MulAut V),
    B51Hyp G L → commV L ∈ IrrPlus L ⊤ →
    ((∃ n, G2Natural L (commV L) (fixV L ⊓ commV L) n) ∨
      G2NaturalDerived L (commV L) (fixV L ⊓ commV L) 1) →
    commV L ⊔ fixV G = ⊤

end CFSG.Quasithin
