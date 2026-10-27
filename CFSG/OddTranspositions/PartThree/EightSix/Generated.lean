module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.Timmesfeld.Bridge.Asc72Triangle

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type*} [Group G] {D : Set G}

theorem isConj_of_not_commute (hD : IsOddTransp D) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : ¬ Commute x y) {X : Subgroup G} (hxX : x ∈ X) (hyX : y ∈ X)
    (hX : Subgroup.closure ({x, y} : Set G) ≤ X) :
    IsConj (⟨x, hxX⟩ : X) ⟨y, hyX⟩ := by
  obtain ⟨g, hg, hconj⟩ := hD.exists_conj hx hy hxy
  refine isConj_iff.mpr ⟨⟨g, hX hg⟩, ?_⟩
  apply Subtype.ext
  exact hconj

theorem setup_class_of_generators (hN : IsNormalSet D) (hD : IsOddTransp D) {X : Subgroup G}
    {u' w' v' : X} (hu' : (u' : G) ∈ D) (hw' : (w' : G) ∈ D) (hv' : (v' : G) ∈ D)
    (huw : ¬ Commute (u' : G) (w' : G)) (hvw : ¬ Commute (v' : G) (w' : G))
    (hgen : Subgroup.closure ({u', w', v'} : Set X) = ⊤) :
    Setup X {x | IsConj u' x} ∧ w' ∈ {x | IsConj u' x} ∧ v' ∈ {x | IsConj u' x} := by
  have hE_D : ∀ x ∈ ({x : X | IsConj u' x} : Set X), (x : G) ∈ D := by
    rintro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    have hcoe : ((g * u' * g⁻¹ : X) : G) = (g : G) * (u' : G) * (g : G)⁻¹ := by
      simp
    rw [hcoe]
    exact hN (g : G) (u' : G) hu'
  have hw'E : w' ∈ ({x : X | IsConj u' x} : Set X) :=
    isConj_of_not_commute hD hu' hw' huw u'.2 w'.2 (by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact u'.2
      · exact w'.2)
  have hv'E : v' ∈ ({x : X | IsConj u' x} : Set X) := by
    have hconj : IsConj v' w' :=
      isConj_of_not_commute hD hv' hw' hvw v'.2 w'.2 (by
        rw [Subgroup.closure_le]
        rintro z (rfl | rfl)
        · exact v'.2
        · exact w'.2)
    exact hw'E.trans hconj.symm
  have hE_odd : IsOddTransp {x : X | IsConj u' x} :=
    (hD.preimage X).mono fun x hx => hE_D x hx
  have hgenE : Subgroup.closure ({x : X | IsConj u' x} : Set X) = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup X) = Subgroup.closure ({u', w', v'} : Set X) := hgen.symm
      _ ≤ Subgroup.closure ({x : X | IsConj u' x} : Set X) := by
        refine Subgroup.closure_mono ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx | hx
        · exact hx ▸ IsConj.refl u'
        · exact hx ▸ hw'E
        · exact hx ▸ hv'E
  exact ⟨⟨⟨u', rfl⟩, hE_odd, hgenE⟩, hw'E, hv'E⟩

theorem lemma8_6_of_generated
    (h : ∀ (X : Type) [Group X] [Finite X] (E : Set X), Setup X E → ∀ a b c : X,
      IsTriangle E a b c → orderOf (a * c * b) = 4 →
      Subgroup.closure ({a, b, c} : Set X) = ⊤ → Group.IsSolvable X) :
    Lemma8_6 := by
  intro G _ _ D hN hD u w v htri hord
  let X : Subgroup G := Subgroup.closure ({u, w, v} : Set G)
  have huX : u ∈ X := Subgroup.subset_closure (by simp)
  have hwX : w ∈ X := Subgroup.subset_closure (by simp)
  have hvX : v ∈ X := Subgroup.subset_closure (by simp)
  let u' : X := ⟨u, huX⟩
  let w' : X := ⟨w, hwX⟩
  let v' : X := ⟨v, hvX⟩
  let E : Set X := {x | IsConj u' x}
  have hgenX : Subgroup.closure ({u', w', v'} : Set X) = ⊤ := by
    have hpre : ((↑) : X → G) ⁻¹' ({u, w, v} : Set G) = ({u', w', v'} : Set X) := by
      ext x
      simp [u', w', v', Subtype.ext_iff]
    rw [← hpre]
    exact Subgroup.closure_preimage_eq_top ({u, w, v} : Set G)
  obtain ⟨hS, hw'E, hv'E⟩ :=
    setup_class_of_generators hN hD (by simpa [u'] using htri.1)
      (by simpa [w'] using htri.2.2.1) (by simpa [v'] using htri.2.1)
      (by simpa [u', w'] using htri.2.2.2.2.2.1)
      (by simpa [v', w'] using htri.2.2.2.2.2.2) hgenX
  have htriX : IsTriangle E u' w' v' := by
    refine ⟨IsConj.refl u', hv'E, hw'E, ?_, ?_, ?_, ?_⟩
    · intro he
      exact htri.2.2.2.1 (by simpa [u', v'] using congrArg Subtype.val he)
    · apply Subtype.ext
      simpa [u', v', Subgroup.coe_mul] using htri.2.2.2.2.1.eq
    · intro hc
      exact htri.2.2.2.2.2.1 (by
        show u * w = w * u
        simpa [u', w', Subgroup.coe_mul] using congrArg Subtype.val hc.eq)
    · intro hc
      exact htri.2.2.2.2.2.2 (by
        show v * w = w * v
        simpa [v', w', Subgroup.coe_mul] using congrArg Subtype.val hc.eq)
  have hordX : orderOf (u' * v' * w') = 4 := by
    rw [← Subgroup.orderOf_coe (u' * v' * w')]
    simpa [u', v', w', Subgroup.coe_mul] using hord
  exact h X E hS u' w' v' htriX hordX hgenX

end CFSG.OddTranspositions.PartThree.EightSix
