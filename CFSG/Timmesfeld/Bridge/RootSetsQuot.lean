module

public import CFSG.Timmesfeld.Bridge.RootStructQD
public import CFSG.Timmesfeld.Opposite.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def classIn (X : Subgroup G) (x : G) : Set G := {y | ∃ g ∈ X, y = g * x * g⁻¹}

theorem mem_classIn_self (X : Subgroup G) (x : G) : x ∈ classIn X x :=
  ⟨1, X.one_mem, by group⟩

theorem classIn_subset (X : Subgroup G) {x : G} (hx : x ∈ X) : classIn X x ⊆ X := by
  rintro y ⟨g, hg, rfl⟩
  exact X.mul_mem (X.mul_mem hg hx) (X.inv_mem hg)

theorem classIn_subset_of_normal (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (X : Subgroup G)
    {x : G} (hx : x ∈ D) : classIn X x ⊆ D := by
  rintro y ⟨g, -, rfl⟩
  exact hN g x hx

theorem conj_mem_classIn {X : Subgroup G} {x y g : G} (hy : y ∈ classIn X x) (hg : g ∈ X) :
    g * y * g⁻¹ ∈ classIn X x := by
  obtain ⟨h, hh, rfl⟩ := hy
  exact ⟨g * h, X.mul_mem hg hh, by group⟩

theorem classIn_eq_of_mem {X : Subgroup G} {x y : G} (hy : y ∈ classIn X x) :
    classIn X y = classIn X x := by
  obtain ⟨h, hh, rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * h, X.mul_mem hg hh, by group⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * h⁻¹, X.mul_mem hg (X.inv_mem hh), by group⟩

theorem mem_classIn_of_odd (hD : IsRootInvolutionSet D) {X : Subgroup G} {y c : G} (hy : y ∈ D)
    (hc : c ∈ D) (hyX : y ∈ X) (hcX : c ∈ X) (hodd : Odd (orderOf (y * c))) :
    c ∈ classIn X y := by
  refine ⟨dihedralSwap y c, ?_, (dihedralSwap_conj (hD.mul_self_eq_one hy)
    (hD.mul_self_eq_one hc) hodd).symm⟩
  exact X.mul_mem hyX (X.pow_mem (X.mul_mem hyX hcX) _)

theorem qdCore_le {X : Subgroup G} {a b c : G} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) :
    qdCore a b c ≤ X := by
  rw [qdCore, Subgroup.closure_le]
  rintro y ⟨g, hg, rfl⟩
  have hgX : g ∈ X := by
    have : Subgroup.closure ({a, b} : Set G) ≤ X := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact ha
      · exact hb
    exact this hg
  exact X.mul_mem (X.mul_mem hgX hc) (X.inv_mem hgX)

theorem not_opposite_of_collinear_class [Finite G] (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) {X : Subgroup G} {x e w c : G} (hx : x ∈ D)
    (hxX : x ∈ X) (he : e ∈ classIn X x) (hw : w ∈ D) (hwX : w ∈ X) (hwe : Commute w e)
    (hweE : w * e ∈ classIn X x) (hwE : w ∉ classIn X x) (hc : c ∈ D) (hcX : c ∈ X) :
    ¬ (¬ Commute w c ∧ Odd (orderOf (w * c))) := by
  rintro ⟨hnc, hodd⟩
  have heD : e ∈ D := classIn_subset_of_normal hN X hx he
  have heX : e ∈ X := classIn_subset X hxX he
  have hweD : w * e ∈ D := classIn_subset_of_normal hN X hx hweE
  have hweX : w * e ∈ X := classIn_subset X hxX hweE
  have hcE : c ∉ classIn X x := by
    intro hcE
    have hoddc : Odd (orderOf (c * w)) := by
      rw [show c * w = (w * c)⁻¹ by rw [mul_inv_rev, hD.inv_eq hw, hD.inv_eq hc], orderOf_inv]
      exact hodd
    have := mem_classIn_of_odd hD hc hw hcX hwX hoddc
    rw [classIn_eq_of_mem hcE] at this
    exact hwE this
  have hnot : ∀ y ∈ classIn X x, Commute c y ∨ orderOf (c * y) = 4 := by
    intro y hy
    have hyD := classIn_subset_of_normal hN X hx hy
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hc hyD with h | h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
    · have h' : Odd (orderOf (y * c)) := by
        rw [show y * c = (c * y)⁻¹ by rw [mul_inv_rev, hD.inv_eq hc, hD.inv_eq hyD], orderOf_inv]
        exact h
      have := mem_classIn_of_odd hD hyD hc (classIn_subset X hxX hy) hcX h'
      rw [classIn_eq_of_mem hy] at this
      exact absurd this hcE
  have hconj : ∀ y : G, y ∈ D → w * y ∈ D → Commute w y → orderOf (c * y) = 4 → y ∈ X →
      w * y ∈ classIn X x → False := by
    intro y hyD hwyD hwy h4 hyX hwyE
    obtain ⟨z, hzD, hzQ, -, -, hz⟩ := exists_conj_eq_mul_of_odd_special hD hN hw hc hyD hnc hodd
      h4 hwy hwyD
    have hzX : z ∈ X := qdCore_le hwX hcX hyX hzQ
    have hwyw : w * y ∈ classIn X w := ⟨z, hzX, by rw [hD.inv_eq hzD, hz]⟩
    have hww : w ∈ classIn X (w * y) := by
      rw [classIn_eq_of_mem hwyw]
      exact mem_classIn_self X w
    rw [classIn_eq_of_mem hwyE] at hww
    exact hwE hww
  have he2 := hD.mul_self_eq_one heD
  rcases hnot e he with hce | hce
  ·
    rcases hnot (w * e) hweE with hcwe | hcwe
    · apply hnc
      have h := hcwe.mul_right hce
      rw [mul_assoc, he2, mul_one] at h
      exact h.symm
    · refine hconj (w * e) hweD (by rw [← mul_assoc, hD.mul_self_eq_one hw, one_mul]; exact heD)
        ((Commute.refl w).mul_right hwe) hcwe hweX ?_
      rw [← mul_assoc, hD.mul_self_eq_one hw, one_mul]
      exact he
  · exact hconj e heD hweD hwe hce heX hweE

theorem sq_mem_classIn_or_mem_pCoreOf [Finite G] (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) {X : Subgroup G} {x e f : G} (hx : x ∈ D)
    (hxX : x ∈ X) (he : e ∈ classIn X x) (hf : f ∈ classIn X x) (h4 : orderOf (e * f) = 4) :
    (e * f) ^ 2 ∈ classIn X x ∨ (e * f) ^ 2 ∈ (CFSG.pCore 2 X).map X.subtype := by
  by_cases hwE : (e * f) ^ 2 ∈ classIn X x
  · exact Or.inl hwE
  right
  have heD := classIn_subset_of_normal hN X hx he
  have hfD := classIn_subset_of_normal hN X hx hf
  have heX := classIn_subset X hxX he
  have hfX := classIn_subset X hxX hf
  obtain ⟨hwD, hew, -, hfef⟩ := sq_mem_of_orderOf_eq_four hD heD hfD h4
  have hwX : (e * f) ^ 2 ∈ X := X.pow_mem (X.mul_mem heX hfX) 2
  have hweE : (e * f) ^ 2 * e ∈ classIn X x := by
    have := conj_mem_classIn he hfX
    rwa [hD.inv_eq hfD, hfef, hew.eq] at this
  have key : ∀ g ∈ X, IsPGroup 2 (Subgroup.closure
      ({(e * f) ^ 2, g * (e * f) ^ 2 * g⁻¹} : Set G)) := by
    intro g hg
    have hw'D : g * (e * f) ^ 2 * g⁻¹ ∈ D := hN g _ hwD
    have hw'X : g * (e * f) ^ 2 * g⁻¹ ∈ X := X.mul_mem (X.mul_mem hg hwX) (X.inv_mem hg)
    have hno := not_opposite_of_collinear_class hD hN hx hxX he hwD hwX hew.symm hweE hwE hw'D
      hw'X
    have hw2 := hD.mul_self_eq_one hwD
    have hw'2 := hD.mul_self_eq_one hw'D
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hwD hw'D with hcw | h4' | ⟨hodd, hnc⟩
    · refine isPGroup_two_closure_pair hw2 hw'2 (k := 1) ?_
      rw [pow_one, ← (commute_iff_mul_sq_eq_one hw2 hw'2).1 hcw]
    · refine isPGroup_two_closure_pair hw2 hw'2 (k := 2) ?_
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4']
      exact pow_orderOf_eq_one _
    · exact absurd ⟨hnc, hodd⟩ hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : (⟨(e * f) ^ 2, hwX⟩ : X) ∈ CFSG.pCore 2 X := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro g
    set K := Subgroup.closure ({(⟨(e * f) ^ 2, hwX⟩ : X), g * ⟨(e * f) ^ 2, hwX⟩ * g⁻¹} : Set X)
    have hK : K.map X.subtype = Subgroup.closure
        ({(e * f) ^ 2, (g : G) * (e * f) ^ 2 * (g : G)⁻¹} : Set G) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    have hP : IsPGroup 2 (K.map X.subtype) := hK ▸ key g g.2
    exact hP.of_equiv (K.equivMapOfInjective X.subtype X.subtype_injective).symm
  exact ⟨⟨(e * f) ^ 2, hwX⟩, hmem, rfl⟩

end CFSG.Timmesfeld.Bridge
