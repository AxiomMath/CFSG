module

public import CFSG.OddTranspositions.PartFour.ThirteenListThreeFischerFi22
public import CFSG.OddTranspositions.PartFour.ThirteenListThreeFischerFi24
public import CFSG.OddTranspositions.PartFour.ThirteenListThreeLift
import CFSG.Timmesfeld.Bridge.Asc72YCount

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Fischer.Classification CFSG.OddTranspositions.FischerMarked
open CFSG.OddTranspositions.FischerMarkedY CFSG.LieType.Multipliers.O73
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Blueprint.Fischer Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem exists_sevenNine_of_marked_refl_embedding {X : Type} [Group X] [Finite X] {s : X}
    (hs : s * s = 1) (hZ : Odd (Nat.card (center X))) {m : ℕ} (hm : 7 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (κ : R3 f →* X ⧸ center X) (hκ : Function.Injective κ)
    {v : Fin m → ZMod 3} (hv : f v v = 1) (hκv : κ (reflBar f v) = QuotientGroup.mk s) :
    ∃ L : Subgroup X, s ∈ L ∧ IsSevenNineGroup ↥L
      {x : ↥L | (x : X) ∈ Subgroup.zpowers s ∧ x ≠ 1} := by
  obtain ⟨c, hc, Φ, hΦ, hΦc, hne⟩ := exists_reflGroup_split_six_embedding hm f hf v hv
  let θ := κ.comp ((QuotientGroup.mk' (center (F3.reflGroup f))).comp Φ)
  have hθ := hκ.comp (injective_mk_comp_reflGroup (by omega) hf hΦ hne)
  have hθc : θ (reflElt (diagF3 6 2) c) = QuotientGroup.mk s := by
    have hc' : Φ (reflElt (diagF3 6 2) c) = reflElt f v := Subtype.ext hΦc
    change κ (QuotientGroup.mk (Φ (reflElt (diagF3 6 2) c))) = _
    rw [hc']
    exact hκv
  obtain ⟨T, hT, hTQ⟩ := exists_totallySingular_diagF3_six_two
  obtain ⟨ι, hι, -, hιc⟩ := exists_reflGroup_lift_of_split hs hZ
    (isF3Form_diagF3 (by decide)) ⟨T, hT, fun x hx => hTQ x hx⟩ hc θ hθ hθc
  exact exists_sevenNine_of_reflGroup_embedding hs (isF3Form_diagF3 (by decide)) hc ι hι hιc

theorem exists_sevenNine_of_marked_linear_refl_embedding {X : Type} [Group X] [Finite X] {s : X}
    (hs : s * s = 1) (hZ : Odd (Nat.card (Subgroup.center X))) {m : ℕ} (hm : 7 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (κ : F3.reflGroup f →* X ⧸ Subgroup.center X) (hκ : Function.Injective κ)
    {v : Fin m → ZMod 3} (hv : f v v = 1)
    (hκv : κ (reflElt f v) = QuotientGroup.mk s) :
    ∃ L : Subgroup X, s ∈ L ∧ CFSG.LocalAnalysis.WeakClosure81.IsSevenNineGroup ↥L
      {x : ↥L | (x : X) ∈ Subgroup.zpowers s ∧ x ≠ 1} := by
  obtain ⟨c, hc, Φ, hΦ, hΦc, -⟩ :=
    CFSG.OddTranspositions.PartFour.exists_reflGroup_split_six_embedding hm f hf v hv
  let θ := κ.comp Φ
  have hθ := hκ.comp hΦ
  have hθc : θ (reflElt (diagF3 6 2) c) = QuotientGroup.mk s := by
    have hc' : Φ (reflElt (diagF3 6 2) c) = reflElt f v := Subtype.ext hΦc
    change κ (Φ _) = _
    rw [hc']
    exact hκv
  obtain ⟨T, hT, hTQ⟩ := CFSG.OddTranspositions.PartFour.exists_totallySingular_diagF3_six_two
  obtain ⟨ι, hι, -, hιc⟩ := CFSG.OddTranspositions.PartFour.exists_reflGroup_lift_of_split hs hZ
    (isF3Form_diagF3 (by decide)) ⟨T, hT, fun x hx => hTQ x hx⟩ hc θ hθ hθc
  exact CFSG.OddTranspositions.PartFour.exists_sevenNine_of_reflGroup_embedding hs
    (isF3Form_diagF3 (by decide)) hc ι hι hιc

section Fi22

theorem oddTranspListAlt_of_fi22 {X : Type} [Group X] [Finite X] {s : X}
    (hs : orderOf s = 2) (hZ : Odd (Nat.card (center X)))
    (φ : X ⧸ center X ≃* CFSG.Blueprint.NativeSporadic.Fi22)
    (huniq : ∀ E : Set CFSG.Blueprint.NativeSporadic.Fi22, Pair _ E →
      E = φ '' {x : X ⧸ center X | IsConj (QuotientGroup.mk s) x}) : OddTranspListAlt X s := by
  let ψ : X ⧸ center X ≃* CFSG.Sporadic.Fi22.J :=
    φ.trans CFSG.Sporadic.Fi22.fi22EquivJ
  have hD : CFSG.Sporadic.Fi22.D =
      ψ '' {x : X ⧸ center X | IsConj (QuotientGroup.mk s) x} := by
    have hE : Pair CFSG.Blueprint.NativeSporadic.Fi22
        (CFSG.Sporadic.Fi22.fi22EquivJ.symm '' CFSG.Sporadic.Fi22.D) :=
      @CFSG.Fischer.pair_map CFSG.Sporadic.Fi22.J CFSG.Blueprint.NativeSporadic.Fi22
        (inferInstance : Group CFSG.Sporadic.Fi22.J)
        (inferInstance : Group CFSG.Blueprint.NativeSporadic.Fi22) CFSG.Sporadic.Fi22.D
        CFSG.Sporadic.Fi22.pair_D CFSG.Sporadic.Fi22.fi22EquivJ.symm
    have h := congrArg (Set.image CFSG.Sporadic.Fi22.fi22EquivJ) (huniq _ hE)
    simpa only [ψ, Set.image_image, MulEquiv.apply_symm_apply, Set.image_id',
      MulEquiv.coe_trans, Function.comp_def] using h
  have hsD : ψ (QuotientGroup.mk s) ∈ CFSG.Sporadic.Fi22.D :=
    hD.symm ▸ ⟨_, IsConj.refl _, rfl⟩
  have haD : (fi22Point 0 : CFSG.Sporadic.Fi22.J) ∈ CFSG.Sporadic.Fi22.D := by
    obtain ⟨d, -, he⟩ := (fi22Point 0).2
    exact he ▸ d.2
  obtain ⟨g, hg⟩ := isConj_iff.mp (CFSG.Fischer.Pair.isConj CFSG.Sporadic.Fi22.pair_D haD hsD)
  obtain ⟨κ, hκ, hκpoint⟩ := exists_fi22_refl_embedding
  let κ' : R3 (diagF3 7 1) →* X ⧸ center X :=
    { toFun := fun x => ψ.symm (g * κ x * g⁻¹)
      map_one' := by simp
      map_mul' := fun x y => by
        rw [κ.map_mul, ← ψ.symm.map_mul]
        exact congrArg ψ.symm (by group) }
  have hκ' := ψ.symm.injective.comp ((MulAut.conj g).injective.comp hκ)
  have hκv : κ' (reflBar (diagF3 7 1) (point 0)) = QuotientGroup.mk s := by
    change ψ.symm (g * κ (reflPoint 0) * g⁻¹) = _
    rw [hκpoint, hg, ψ.symm_apply_apply]
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs, pow_two] at h
    exact h
  have h := exists_sevenNine_of_marked_refl_embedding hs2 hZ (by decide)
    (isF3Form_diagF3 (by decide)) κ' hκ' (by rw [diagF3_seven_one_apply]; exact point_norm 0) hκv
  exact Or.inr (Or.inr (Or.inr (Or.inl h)))

end Fi22

section Fi23

theorem oddTranspListAlt_of_fi23 {X : Type} [Group X] [Finite X] {s : X}
    (hs : orderOf s = 2) (hZ : Odd (Nat.card (Subgroup.center X)))
    (φ : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.Fi23)
    (huniq : ∀ E : Set CFSG.Blueprint.NativeSporadic.Fi23, CFSG.Blueprint.Fischer.Pair _ E →
      E = φ '' {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}) :
    CFSG.LocalAnalysis.WeakClosure81.OddTranspListAlt X s := by
  let ψ : X ⧸ Subgroup.center X ≃* CFSG.Sporadic.Fi23.J := φ.trans CFSG.Sporadic.Fi23.fi23EquivJ
  have hD : CFSG.Sporadic.Fi23.D23 = ψ '' {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x} := by
    have hE : CFSG.Blueprint.Fischer.Pair CFSG.Blueprint.NativeSporadic.Fi23
        (CFSG.Sporadic.Fi23.fi23EquivJ.symm '' CFSG.Sporadic.Fi23.D23) :=
      @CFSG.Fischer.pair_map CFSG.Sporadic.Fi23.J CFSG.Blueprint.NativeSporadic.Fi23
        (inferInstance : Group CFSG.Sporadic.Fi23.J) (inferInstance : Group CFSG.Blueprint.NativeSporadic.Fi23)
        CFSG.Sporadic.Fi23.D23 CFSG.Sporadic.Fi23.pair_J CFSG.Sporadic.Fi23.fi23EquivJ.symm
    have h := congrArg (Set.image CFSG.Sporadic.Fi23.fi23EquivJ) (huniq _ hE)
    simpa only [ψ, Set.image_image, MulEquiv.apply_symm_apply, Set.image_id',
      MulEquiv.coe_trans, Function.comp_def] using h
  have hsD : ψ (QuotientGroup.mk s) ∈ CFSG.Sporadic.Fi23.D23 := hD.symm ▸ ⟨_, IsConj.refl _, rfl⟩
  obtain ⟨κ, hκ, i, hi⟩ := exists_fi23_refl_embedding
  obtain ⟨g, hg⟩ := isConj_iff.mp (CFSG.Fischer.Pair.isConj CFSG.Sporadic.Fi23.pair_J hi hsD)
  let κ' : R3 sevenForm →* X ⧸ Subgroup.center X :=
    { toFun := fun x => ψ.symm (g * κ x * g⁻¹)
      map_one' := by simp
      map_mul' := fun x y => by
        rw [κ.map_mul, ← ψ.symm.map_mul]
        exact congrArg ψ.symm (by group) }
  have hκ' := ψ.symm.injective.comp ((MulAut.conj g).injective.comp hκ)
  have hκv : κ' (reflBar sevenForm (coordinates (vecs i))) = QuotientGroup.mk s := by
    change ψ.symm (g * κ (reflBar sevenForm (coordinates (vecs i))) * g⁻¹) = _
    rw [hg, ψ.symm_apply_apply]
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs, pow_two] at h
    exact h
  have h := CFSG.OddTranspositions.PartFour.exists_sevenNine_of_marked_refl_embedding hs2 hZ
    (by decide) isF3Form_sevenForm κ' hκ' (sevenForm_vecs i) hκv
  exact Or.inr (Or.inr (Or.inr (Or.inl h)))

end Fi23

section Fi24

open CFSG.OddTranspositions.FischerMarked24

theorem oddTranspListAlt_of_fi24 {X : Type} [Group X] [Finite X] {s : X}
    (hs : orderOf s = 2) (hZ : Odd (Nat.card (Subgroup.center X)))
    (φ : X ⧸ Subgroup.center X ≃* MulAut CFSG.Blueprint.NativeSporadic.Fi24prime)
    (huniq : ∀ E : Set (MulAut CFSG.Blueprint.NativeSporadic.Fi24prime),
      CFSG.Blueprint.Fischer.Pair _ E →
      E = φ '' {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}) :
    CFSG.LocalAnalysis.WeakClosure81.OddTranspListAlt X s := by
  let ψ : X ⧸ Subgroup.center X ≃* CFSG.Sporadic.Fi24.R := φ.trans CFSG.Sporadic.Schreier.Fi24.autEquivR
  have hD : CFSG.Sporadic.Fi24.D24 = ψ '' {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x} := by
    have hE : CFSG.Blueprint.Fischer.Pair (MulAut CFSG.Blueprint.NativeSporadic.Fi24prime)
        (CFSG.Sporadic.Schreier.Fi24.autEquivR.symm '' CFSG.Sporadic.Fi24.D24) :=
      @CFSG.Fischer.pair_map CFSG.Sporadic.Fi24.R (MulAut CFSG.Blueprint.NativeSporadic.Fi24prime)
        (inferInstance : Group CFSG.Sporadic.Fi24.R)
        (inferInstance : Group (MulAut CFSG.Blueprint.NativeSporadic.Fi24prime))
        CFSG.Sporadic.Fi24.D24 CFSG.Sporadic.Fi24.pair_R CFSG.Sporadic.Schreier.Fi24.autEquivR.symm
    have h := congrArg (Set.image CFSG.Sporadic.Schreier.Fi24.autEquivR) (huniq _ hE)
    simpa only [ψ, Set.image_image, MulEquiv.apply_symm_apply, Set.image_id',
      MulEquiv.coe_trans, Function.comp_def] using h
  have hsD : ψ (QuotientGroup.mk s) ∈ CFSG.Sporadic.Fi24.D24 := hD.symm ▸ ⟨_, IsConj.refl _, rfl⟩
  obtain ⟨κ, hκ, i, hi⟩ := exists_fi24_linear_refl_embedding
  obtain ⟨g, hg⟩ := isConj_iff.mp (CFSG.Fischer.Pair.isConj CFSG.Sporadic.Fi24.pair_R hi hsD)
  let κ' : F3.reflGroup sevenForm →* X ⧸ Subgroup.center X :=
    { toFun := fun x => ψ.symm (g * κ x * g⁻¹)
      map_one' := by simp
      map_mul' := fun x y => by
        rw [κ.map_mul, ← ψ.symm.map_mul]
        exact congrArg ψ.symm (by group) }
  have hκ' := ψ.symm.injective.comp ((MulAut.conj g).injective.comp hκ)
  have hκv : κ' (reflElt sevenForm (coordinates (vecs i))) = QuotientGroup.mk s := by
    change ψ.symm (g * κ (reflElt sevenForm (coordinates (vecs i))) * g⁻¹) = _
    rw [hg, ψ.symm_apply_apply]
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs, pow_two] at h
    exact h
  have h := exists_sevenNine_of_marked_linear_refl_embedding hs2 hZ
    (by decide) isF3Form_sevenForm κ' hκ' (sevenForm_vecs i) hκv
  exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem oddTranspListThreeTranspFischer_holds :
    OddTranspListThreeTranspFischer := by
  intro X _ _ s hs hodd hncl hO2 hOZ hder h3 hFi
  have hZ := CFSG.Timmesfeld.Bridge.Asc72.CentralQuot.odd_card_center hO2
  rcases hFi with ⟨φ, -, huniq⟩ | ⟨φ, -, huniq⟩ | ⟨φ, -, huniq⟩
  · exact oddTranspListAlt_of_fi22 hs hZ φ huniq
  · exact oddTranspListAlt_of_fi23 hs hZ φ huniq
  · exact oddTranspListAlt_of_fi24 hs hZ φ huniq

end Fi24

end CFSG.OddTranspositions.PartFour
