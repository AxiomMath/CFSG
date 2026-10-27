module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListDerivedCases
public import CFSG.OddTranspositions.PartFour.Fourteen.Statements
import CFSG.OddTranspositions.PartFour.ThirteenList
import CFSG.OddTranspositions.PartFour.Fourteen.Assembly
import CFSG.OddTranspositions.PartFour.Fourteen.ShapeTransport
import CFSG.OddTranspositions.PartFour.Fourteen.UnitaryShapeRigid

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open

section Descent

variable {Y : Type} [Group Y]

noncomputable def quotientCenterEquivOfEqBot (hZ : Subgroup.center Y = ⊥) :
    Y ⧸ Subgroup.center Y ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem quotientCenterEquivOfEqBot_symm_apply (hZ : Subgroup.center Y = ⊥) (y : Y) :
    (quotientCenterEquivOfEqBot hZ).symm y = QuotientGroup.mk y :=
  (MulEquiv.symm_apply_eq _).mpr rfl

theorem isSymplecticTransvection_of_isConj {m f : ℕ} {y y' : Y} (hc : IsConj y y')
    (h : IsSymplecticTransvection Y m f y') : IsSymplecticTransvection Y m f y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  have := isSymplecticTransvection_map (MulAut.conj g⁻¹) h
  rwa [MulAut.conj_apply, inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this

theorem isUnitaryTransvection_of_isConj {m f : ℕ} {y y' : Y} (hc : IsConj y y')
    (h : IsUnitaryTransvection Y m f y') : IsUnitaryTransvection Y m f y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  have := isUnitaryTransvection_map (MulAut.conj g⁻¹) h
  rwa [MulAut.conj_apply, inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this

theorem isOrthReflection_of_isConj {m f : ℕ} {y y' : Y} (hc : IsConj y y')
    (h : IsOrthReflection Y m f y') : IsOrthReflection Y m f y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  have := isOrthReflection_map (MulAut.conj g⁻¹) h
  rwa [MulAut.conj_apply, inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this

theorem isPSUGp_of_isUnitaryTransvection {m f : ℕ} {y : Y} (hm : 3 ≤ m) (hf : 2 ≤ f)
    (h : IsUnitaryTransvection Y m f y) : IsPSUGp (Y ⧸ Subgroup.center Y) m f := by
  obtain ⟨F, hF, hFin, hcard, e, -⟩ := h
  have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  unfold IsPSUGp CFSG.Blueprint.LieModel
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, hm, fun h => ?_⟩, F, hF, hFin, hcard, ⟨e⟩⟩
  simp only [Prod.mk.injEq] at h
  omega

end Descent

section Quotient

variable {X : Type} [Group X]

theorem isSymplecticTransvection_of_quotient_center
    (hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥) {m f : ℕ} {s : X}
    (h : IsSymplecticTransvection (X ⧸ Subgroup.center X) m f (QuotientGroup.mk s)) :
    IsSymplecticTransvection X m f s := by
  obtain ⟨k, hmk, F, hF, hFin, hcard, e', hr⟩ := h
  refine ⟨k, hmk, F, hF, hFin, hcard, (quotientCenterEquivOfEqBot hZ).symm.trans e', ?_⟩
  rwa [MulEquiv.trans_apply, quotientCenterEquivOfEqBot_symm_apply]

theorem isUnitaryTransvection_of_quotient_center
    (hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥) {m f : ℕ} {s : X}
    (h : IsUnitaryTransvection (X ⧸ Subgroup.center X) m f (QuotientGroup.mk s)) :
    IsUnitaryTransvection X m f s := by
  obtain ⟨F, hF, hFin, hcard, e', hr⟩ := h
  refine ⟨F, hF, hFin, hcard, (quotientCenterEquivOfEqBot hZ).symm.trans e', ?_⟩
  rwa [MulEquiv.trans_apply, quotientCenterEquivOfEqBot_symm_apply]

theorem isOrthReflection_of_quotient_center
    (hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥) {m f : ℕ} {s : X}
    (h : IsOrthReflection (X ⧸ Subgroup.center X) m f (QuotientGroup.mk s)) :
    IsOrthReflection X m f s := by
  rcases h with ⟨k, hk, hmk, F, hF, hFin, hcard, e', hr⟩ |
      ⟨k, hk, hmk, F, hF, hFin, hcard, b, c, hbc, e', hr⟩
  · refine Or.inl ⟨k, hk, hmk, F, hF, hFin, hcard,
      (quotientCenterEquivOfEqBot hZ).symm.trans e', ?_⟩
    rwa [MulEquiv.trans_apply, quotientCenterEquivOfEqBot_symm_apply]
  · refine Or.inr ⟨k, hk, hmk, F, hF, hFin, hcard, b, c, hbc,
      (quotientCenterEquivOfEqBot hZ).symm.trans e', ?_⟩
    rwa [MulEquiv.trans_apply, quotientCenterEquivOfEqBot_symm_apply]

theorem isWreathTransposition_of_quotient_center
    (hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥) {f m : ℕ} {s : X}
    {s' : X ⧸ Subgroup.center X} (hc : IsConj (QuotientGroup.mk s) s')
    (h : IsWreathTransposition (X ⧸ Subgroup.center X) f m s') :
    IsWreathTransposition X f m s := by
  obtain ⟨hf, F, hF, hFin, hcard, e', i, j, hij, hr⟩ := h
  refine ⟨hf, F, hF, hFin, hcard, (quotientCenterEquivOfEqBot hZ).symm.trans e', i, j, hij, ?_⟩
  rw [MulEquiv.trans_apply, quotientCenterEquivOfEqBot_symm_apply]
  exact IsConj.trans ((e'.toMonoidHom.comp (QuotientGroup.mk' _)).map_isConj hc) hr

theorem fusionZStar_eq_center (hOZ : fusionOddCore X ≤ Subgroup.center X)
    (hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥) : fusionZStar X = Subgroup.center X := by
  apply le_antisymm
  · intro x hx
    have hx' : (QuotientGroup.mk x : X ⧸ Subgroup.center X) ∈
        Subgroup.center (X ⧸ Subgroup.center X) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      have h1 := Subgroup.mem_center_iff.mp hx (QuotientGroup.mk' (fusionOddCore X) g)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at h1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      exact hOZ h1
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  · intro z hz
    show QuotientGroup.mk' (fusionOddCore X) z ∈ Subgroup.center (X ⧸ fusionOddCore X)
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]

end Quotient

theorem oddTranspositionListInputClsDerivedEq_of_main (hMain : AscMainTheorem)
    (h3 : OddTranspListDerivedEqThreeTransp) (h5 : OddTranspListDerivedEqOFive) :
    OddTranspositionListInputClsDerivedEq := by
  intro X _ _ s hord hodd hncl hO2 hOZ hder
  have hS := setup_quotient_center hodd hncl hO2
  have hrad := eq_bot_of_normal_isSolvable_quotient_center hO2 hOZ
  have hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
    hrad _ inferInstance
      (Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a))
  have hL := hMain _ _ hS hrad hder
  by_cases h3T : ∀ d ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
      ∀ e ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
        orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)
  · exact h3 X s hord hodd hncl hO2 hOZ hder h3T
  rcases hypEShape_of_ascList hS hder hL h3T with
    ⟨s', hs', m, f, hm, hf, hSp | hU | hO⟩ | hO5 | ⟨s', hs', f, m, -, hW⟩ | ⟨f, hSz⟩
  ·
    have h' := isSymplecticTransvection_of_quotient_center hZ
      (isSymplecticTransvection_of_isConj hs' hSp)
    obtain ⟨k, hk, F, hF, hFin, hcard, e, -⟩ := id h'
    exact Or.inl ⟨m, f, Or.inl ⟨⟨k, hk, F, hF, hFin, hcard, ⟨e⟩⟩, h'⟩⟩
  ·
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · have h' := isSymplecticTransvection_of_quotient_center hZ
        (isSymplecticTransvection_of_isConj hs'
          (isSymplecticTransvection_of_isUnitaryTransvection_two hU))
      obtain ⟨k, hk, F, hF, hFin, hcard, e, -⟩ := id h'
      exact Or.inl ⟨2, f, Or.inl ⟨⟨k, hk, F, hF, hFin, hcard, ⟨e⟩⟩, h'⟩⟩
    · have h' := isUnitaryTransvection_of_quotient_center hZ
        (isUnitaryTransvection_of_isConj hs' hU)
      exact Or.inl ⟨m, f, Or.inr (Or.inl ⟨isPSUGp_of_isUnitaryTransvection hm3 hf h', h'⟩)⟩
  ·
    exact Or.inl ⟨m, f, Or.inr (Or.inr (Or.inl
      (isOrthReflection_of_quotient_center hZ (isOrthReflection_of_isConj hs' hO))))⟩
  ·
    exact h5 X s hord hodd hncl hO2 hOZ hder hO5
  ·
    exact Or.inl ⟨m, f, Or.inr (Or.inr (Or.inr (isWreathTransposition_of_quotient_center hZ hs' hW)))⟩
  ·
    obtain ⟨-, a, ha, K, hK, hKfin, hfa, hcard, ⟨e⟩⟩ := hSz
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f, by omega, rfl, a, ha, K, hK, hKfin, hfa, hcard,
      ⟨(QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_center hOZ hZ)).trans e⟩⟩)))

end CFSG.OddTranspositions.PartFour
