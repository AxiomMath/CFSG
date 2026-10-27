module

public import CFSG.RankThree.PartTwo.Sec4.RonanK423Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423

open CFSG CFSG.RankThree.PartTwo.Sec4.Res423Two
open scoped commutatorElement

variable {X Y : Type} [Group X] [Group Y]

structure CentralProductData (C : Subgroup X) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥⁅C, C⁆
  center3 : ∀ z ∈ Subgroup.center ↥⁅C, C⁆, ∃ k : ℕ, z ^ 3 ^ k = 1
  decomp : ∃ A : Subgroup X, (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) ∧
    (∀ a ∈ A, ∀ r ∈ ⁅C, C⁆, a * r = r * a) ∧ C ≤ ⁅C, C⁆ ⊔ A

theorem centralizer_singleton_map (φ : X ≃* Y) (y : X) :
    Subgroup.centralizer ({φ y} : Set Y) =
      (Subgroup.centralizer ({y} : Set X)).map φ.toMonoidHom := by
  ext z
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h
  · intro h
    have := congrArg φ h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    exact this

theorem CentralProductData.map {C : Subgroup X} (h : CentralProductData C) (φ : X ≃* Y) :
    CentralProductData (C.map φ.toMonoidHom) := by
  have hR : ⁅C.map φ.toMonoidHom, C.map φ.toMonoidHom⁆ = (⁅C, C⁆).map φ.toMonoidHom :=
    (Subgroup.map_commutator _ _ _).symm
  set e := Subgroup.equivMapOfInjective ⁅C, C⁆ φ.toMonoidHom φ.injective with he
  refine ⟨?_, ?_, ?_⟩
  · rw [hR]
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 h.quasisimple
  · rw [hR]
    intro z hz
    have hz' : z ∈ (Subgroup.center ↥⁅C, C⁆).map e.toMonoidHom := by
      have hcen := Subgroup.map_center_eq e
      rw [← hcen] at hz
      exact hz
    obtain ⟨c, hc, rfl⟩ := hz'
    obtain ⟨k, hk⟩ := h.center3 c hc
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · obtain ⟨A, hA, hAR, hC⟩ := h.decomp
    refine ⟨A.map φ.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hA a ha a' ha']
    · rintro _ ⟨a, ha, rfl⟩ _ hr
      rw [hR] at hr
      obtain ⟨r, hr, rfl⟩ := hr
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hAR a ha r hr]
    · rw [hR, ← Subgroup.map_sup]
      exact Subgroup.map_mono hC

theorem CentralProductData.of_map {y : X} (h : CentralProductData (Subgroup.centralizer ({y} : Set X)))
    (φ : X ≃* Y) : CentralProductData (Subgroup.centralizer ({φ y} : Set Y)) := by
  rw [centralizer_singleton_map]
  exact h.map φ

variable [Finite X]

theorem alphaVanishes_of_centralProduct (hX : CFSG.IsQuasisimple X) (hZ : Subgroup.center X = ⊥)
    {D : Subgroup X} (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9)
    (hb : ∀ b ∈ D, b ≠ 1 → CentralProductData (Subgroup.centralizer ({b} : Set X)))
    (hgen : (⊤ : Subgroup X) ≤ Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧ x * b = b * x}) :
    AlphaVanishes X D :=
  alphaVanishes_of_derived hX hZ hDc hDexp hD9 (fun b hbD hb1 => (hb b hbD hb1).quasisimple)
    (fun b hbD hb1 => (hb b hbD hb1).center3)
    (fun b hbD hb1 => by
      obtain ⟨A, hA, hAR, hC⟩ := (hb b hbD hb1).decomp
      exact centralizer_le_derived_sup hbD hDc hA hAR hC)
    hgen

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  have hcen := Subgroup.map_center_eq e
  rw [hB, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hcen
  exact hcen

section Ambient

variable {G : Type} [Group G]

theorem centralProductData_subgroupOf (S : Subgroup G) {C R A : Subgroup G} (hCS : C ≤ S)
    (hCR : ⁅C, C⁆ = R) (hq : CFSG.IsQuasisimple ↥R)
    (hZ : ∀ z ∈ Subgroup.center ↥R, ∃ k : ℕ, z ^ 3 ^ k = 1)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hAR : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a)
    (hdec : ∀ g ∈ C, ∃ r ∈ R, ∃ a ∈ A, g = r * a) :
    CentralProductData (C.subgroupOf S) := by
  have hRC : R ≤ C := hCR ▸ derived_le C
  have hRS : R ≤ S := hRC.trans hCS
  have hmapC : (C.subgroupOf S).map S.subtype = C := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCS]
  have hmapR : (R.subgroupOf S).map S.subtype = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRS]
  have hder : ⁅C.subgroupOf S, C.subgroupOf S⁆ = R.subgroupOf S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator, hmapC, hmapR, hCR]
  let e : ↥(R.subgroupOf S) ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRS
  refine ⟨?_, ?_, ?_⟩
  · rw [hder]
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq
  · rw [hder]
    intro z hz
    have hez : e z ∈ Subgroup.center ↥R := by
      have hcen := Subgroup.map_center_eq e
      rw [← hcen]
      exact Subgroup.mem_map_of_mem _ hz
    obtain ⟨k, hk⟩ := hZ (e z) hez
    exact ⟨k, e.injective (by rw [map_pow, hk, map_one])⟩
  · refine ⟨A.subgroupOf S, ?_, ?_, ?_⟩
    · intro a ha a' ha'
      exact Subtype.ext (hA a (Subgroup.mem_subgroupOf.mp ha) a' (Subgroup.mem_subgroupOf.mp ha'))
    · intro a ha r hr
      rw [hder] at hr
      exact Subtype.ext (hAR a (Subgroup.mem_subgroupOf.mp ha) r (Subgroup.mem_subgroupOf.mp hr))
    · intro x hx
      obtain ⟨r, hr, a, ha, hxra⟩ := hdec x (Subgroup.mem_subgroupOf.mp hx)
      have haS : a ∈ S := by
        have : a = r⁻¹ * (x : G) := by rw [hxra]; group
        rw [this]
        exact S.mul_mem (S.inv_mem (hRS hr)) x.2
      rw [hder]
      have hx' : x = ⟨r, hRS hr⟩ * ⟨a, haS⟩ := Subtype.ext hxra
      rw [hx']
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hr) (Subgroup.mem_subgroupOf.mpr ha)

theorem center_eq_bot_of_simple {P : Type} [Group P] [IsSimpleGroup P] (hq : CFSG.IsQuasisimple P) :
    Subgroup.center P = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center P) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hx : x ∈ Subgroup.center P := by rw [h]; trivial
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp hx y)]

end Ambient

@[expose] def conjAut {G : Type} [Group G] (S : Subgroup G) (P : G) (hP : ∀ g, g ∈ S ↔ P * g * P⁻¹ ∈ S) :
    ↥S ≃* ↥S where
  toFun g := ⟨P * g * P⁻¹, (hP g).1 g.2⟩
  invFun g := ⟨P⁻¹ * g * P, (hP _).2 (by
    have : P * (P⁻¹ * (g : G) * P) * P⁻¹ = g := by group
    rw [this]
    exact g.2)⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' g h := Subtype.ext (by simp [mul_assoc])

end CFSG.RankThree.PartTwo.Sec4.RonanK423
