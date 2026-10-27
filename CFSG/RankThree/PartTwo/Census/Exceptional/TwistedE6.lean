module

public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6Local
public import CFSG.RankThree.PartTwo.Census.Exceptional.Geck
public import CFSG.Adapters.TauCetiExceptional.TwistedE6Dual
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.TauCetiBridge.Minuscule CFSG.RankThree.CentralCover TauCeti
open scoped MatrixGroups

section Doubled

open CFSG.TauCetiBridge.Twisted
open scoped Matrix

variable (L : Type) [Field L]

theorem ulHom_injective : Function.Injective (ulHom L) := by
  intro z z' h
  set Z := ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L)
  set Z' := ((z' : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L)
  have hu : ulBlock Z = ulBlock Z' := by
    rw [← coe_ulHom, ← coe_ulHom, h]
  have e1 := Matrix.inv_eq_left_inv (lrBlock_transpose_mul_ulBlock _ z.2)
  have e2 := Matrix.inv_eq_left_inv (lrBlock_transpose_mul_ulBlock _ z'.2)
  have hl : lrBlock Z = lrBlock Z' := by
    calc lrBlock Z = ((lrBlock Z)ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
      _ = ((ulBlock Z)⁻¹)ᵀ := by rw [e1]
      _ = ((ulBlock Z')⁻¹)ᵀ := by rw [hu]
      _ = lrBlock Z' := by rw [e2, Matrix.transpose_transpose]
  exact Subtype.ext (Units.ext (eq_of_blocks (points_isBlockDiag L z) (points_isBlockDiag L z')
    hu hl))

@[expose] noncomputable def dblHom :
    e6Data_valid.minGroup L →* ↥(E6DoubledMinuscule.points L) :=
  (MonoidHom.ofInjective (ulHom_injective L)).symm.toMonoidHom.comp
    (((toMat e6Match.lab L).toMonoidHom.comp (e6Data_valid.minGroup L).subtype).codRestrict _
      fun g => toMat_mem_ulRange L g)

theorem ulHom_dblHom (g : e6Data_valid.minGroup L) :
    ulHom L (dblHom L g) = toMat e6Match.lab L g :=
  MonoidHom.apply_ofInjective_symm (ulHom_injective L) _

theorem dblHom_injective : Function.Injective (dblHom L) := by
  intro g g' h
  have h' := congrArg (ulHom L) h
  rw [ulHom_dblHom, ulHom_dblHom] at h'
  exact Subtype.val_injective ((toMat e6Match.lab L).injective h')

theorem dblHom_xm_single (i : Fin 6) (c : L) :
    dblHom L (e6Data_valid.xm L (Pi.single i 1) c) =
      E6DoubledMinuscule.rootSubgroupPoints (.inl i) L (Multiplicative.ofAdd c) := by
  apply ulHom_injective L
  rw [ulHom_dblHom, ulHom_rootSubgroupPoints, e6_rootSubgroupPoints_inl, e6Match_node,
    rootUnit_eq_xu]
  rfl

theorem dblHom_xm_neg_single (i : Fin 6) (c : L) :
    dblHom L (e6Data_valid.xm L (-Pi.single i 1) c) =
      E6DoubledMinuscule.rootSubgroupPoints (.inr i) L (Multiplicative.ofAdd c) := by
  apply ulHom_injective L
  rw [ulHom_dblHom, ulHom_rootSubgroupPoints, e6_rootSubgroupPoints_inr, e6Match_node,
    rootUnit_eq_xu]
  rfl

theorem rank_E6 : Tag.rank .E6 = 6 := rfl

theorem dblHom_xm_single' (i : Fin (Tag.rank .E6)) (c : L) :
    dblHom L (e6Data_valid.xm L (Pi.single i 1) c) =
      E6DoubledMinuscule.rootSubgroupPoints (.inl (Fin.cast rank_E6 i)) L
        (Multiplicative.ofAdd c) :=
  dblHom_xm_single L (Fin.cast rank_E6 i) c

theorem dblHom_xm_neg_single' (i : Fin (Tag.rank .E6)) (c : L) :
    dblHom L (e6Data_valid.xm L (-Pi.single i 1) c) =
      E6DoubledMinuscule.rootSubgroupPoints (.inr (Fin.cast rank_E6 i)) L
        (Multiplicative.ofAdd c) :=
  dblHom_xm_neg_single L (Fin.cast rank_E6 i) c

end Doubled

section Field

variable (d : TypeTwistedE6LieIndex)

noncomputable abbrev quadField : Subfield d.1.Closure :=
  frobeniusFixedSubfield d.1.Closure d.1.characteristic (d.1.fieldExponent * 2)

theorem frob_mem_quadField (c : quadField d) :
    (c : d.1.Closure) ^ d.1.fieldOrder ∈ quadField d := by
  rw [mem_frobeniusFixedSubfield, ← pow_mul, mul_comm, pow_mul,
    mem_frobeniusFixedSubfield.1 c.2]

@[expose] noncomputable def quadFrob : quadField d →+* quadField d :=
  ((d.1.frobeniusEquiv : d.1.Closure →+* d.1.Closure).comp (quadField d).subtype).codRestrict
    (quadField d) fun c => by
      rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, ValidLieTypeIndex.frobeniusEquiv_apply]
      exact frob_mem_quadField d c

theorem coe_quadFrob (c : quadField d) :
    ((quadFrob d c : quadField d) : d.1.Closure) = (c : d.1.Closure) ^ d.1.fieldOrder :=
  ValidLieTypeIndex.frobeniusEquiv_apply d.1 _

theorem quadFrob_quadFrob (c : quadField d) : quadFrob d (quadFrob d c) = c := by
  apply Subtype.ext
  rw [coe_quadFrob, coe_quadFrob, ← pow_mul, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
    ← pow_add, show d.1.fieldExponent + d.1.fieldExponent = d.1.fieldExponent * 2 by ring]
  exact mem_frobeniusFixedSubfield.1 c.2

theorem fixedField_le_quadField : d.1.fixedField ≤ quadField d := by
  rw [ValidLieTypeIndex.fixedField_def]
  exact frobeniusFixedSubfield_le_of_dvd (dvd_mul_right _ 2)

@[expose] noncomputable def quadIncl : d.1.fixedField →+* quadField d :=
  Subfield.inclusion (fixedField_le_quadField d)

theorem quadFrob_quadIncl (x : d.1.fixedField) : quadFrob d (quadIncl d x) = quadIncl d x :=
  Subtype.ext (by
    rw [coe_quadFrob]
    exact ValidLieTypeIndex.mem_fixedField.1 x.2)

instance : Finite (quadField d) :=
  finite_frobeniusFixedSubfield _ _ _ (by have := d.1.fieldExponent_pos; omega)

theorem card_quadField : Nat.card (quadField d) = d.1.fieldOrder ^ 2 := by
  rw [card_frobeniusFixedSubfield _ _ _ (by have := d.1.fieldExponent_pos; omega),
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, ← pow_mul]

theorem four_le_card_quadField : 4 ≤ Nat.card (quadField d) := by
  rw [card_quadField]
  have h2 : 2 ≤ d.1.fieldOrder := by
    rw [ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
    exact le_trans (Fact.out : d.1.characteristic.Prime).two_le
      (Nat.le_self_pow (by have := d.1.fieldExponent_pos; omega) _)
  nlinarith

end Field

section Embed

variable (d : TypeTwistedE6LieIndex)

@[expose] noncomputable def te6Ambient :
    e6Data_valid.minGroup (quadField d) →* d.AmbientGroup :=
  ((E6DoubledMinuscule.pointsPresentation (quadField d)).map
    (E6DoubledMinuscule.pointsPresentation d.1.Closure) (quadField d).subtype).comp
    (dblHom (quadField d))

theorem te6Ambient_injective : Function.Injective (te6Ambient d) := by
  intro g g' h
  exact dblHom_injective _ (TauCeti.GeneralLinear.IntegralPointsPresentation.map_injective _ _
    (f := (quadField d).subtype) Subtype.val_injective h)

theorem graphPermE6_eq' (i : Fin 6) : graphPermE6 i = TwistTag.E6.perm i := by
  fin_cases i
  · rw [show ((fun i => i) ⟨0, by decide⟩ : Fin 6) = 0 from rfl, graphPermE6_apply_zero]; rfl
  · rw [show ((fun i => i) ⟨1, by decide⟩ : Fin 6) = 1 from rfl, graphPermE6_apply_one]; rfl
  · rw [show ((fun i => i) ⟨2, by decide⟩ : Fin 6) = 2 from rfl, graphPermE6_apply_two]; rfl
  · rw [show ((fun i => i) ⟨3, by decide⟩ : Fin 6) = 3 from rfl, graphPermE6_apply_three]; rfl
  · rw [show ((fun i => i) ⟨4, by decide⟩ : Fin 6) = 4 from rfl, graphPermE6_apply_four]; rfl
  · rw [show ((fun i => i) ⟨5, by decide⟩ : Fin 6) = 5 from rfl, graphPermE6_apply_five]; rfl

theorem graphPermE6_cast (i : Fin (Tag.rank .E6)) :
    graphPermE6 (Fin.cast rank_E6 i) = Fin.cast rank_E6 (rhoPerm i) :=
  graphPermE6_eq' _

theorem steinberg_rootSubgroupPoints (k : Fin 6 ⊕ Fin 6) (c : d.1.Closure) :
    d.steinberg (E6DoubledMinuscule.rootSubgroupPoints k d.1.Closure (Multiplicative.ofAdd c)) =
      E6DoubledMinuscule.rootSubgroupPoints (E6DoubledMinuscule.graphRootPerm k) d.1.Closure
        (Multiplicative.ofAdd (c ^ d.1.fieldOrder)) := by
  rw [TypeTwistedE6LieIndex.steinberg_def, MonoidHom.comp_apply,
    TypeTwistedE6LieIndex.frobenius_def, E6DoubledMinuscule.frobenius_rootSubgroupPoints,
    MulEquiv.coe_toMonoidHom, TypeTwistedE6LieIndex.graphAut_def,
    E6DoubledMinuscule.graphAutomorphismPoints_rootSubgroupPoints, toAdd_ofAdd,
    ← ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

theorem steinberg_te6Ambient (g : e6Data_valid.minGroup (quadField d)) :
    d.steinberg (te6Ambient d g) = te6Ambient d (sigma (quadField d) (quadFrob d) g) := by
  have h : d.steinberg.comp (te6Ambient d) = (te6Ambient d).comp (sigma _ (quadFrob d)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LieType.Steinberg.Isogeny.closure_xm_simple_eq_top e6Data_valid (quadField d)) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply, te6Ambient]
      rw [sigma_xm_single, dblHom_xm_single', dblHom_xm_single',
        E6DoubledMinuscule.map_rootSubgroupPoints, E6DoubledMinuscule.map_rootSubgroupPoints,
        steinberg_rootSubgroupPoints, E6DoubledMinuscule.graphRootPerm_inl, graphPermE6_cast,
        toAdd_ofAdd, toAdd_ofAdd, Subfield.subtype_apply, Subfield.subtype_apply, coe_quadFrob]
    · simp only [MonoidHom.comp_apply, te6Ambient]
      rw [sigma_xm_neg_single, dblHom_xm_neg_single', dblHom_xm_neg_single',
        E6DoubledMinuscule.map_rootSubgroupPoints, E6DoubledMinuscule.map_rootSubgroupPoints,
        steinberg_rootSubgroupPoints, E6DoubledMinuscule.graphRootPerm_inr, graphPermE6_cast,
        toAdd_ofAdd, toAdd_ofAdd, Subfield.subtype_apply, Subfield.subtype_apply, coe_quadFrob]
  exact DFunLike.congr_fun h g

@[expose] noncomputable def te6Embed :
    ↥(fixedGroup (quadField d) (quadFrob d)) →* ↥(fixedSubgroup d.steinberg) :=
  ((te6Ambient d).comp (fixedGroup (quadField d) (quadFrob d)).subtype).codRestrict _ fun g => by
    rw [mem_fixedSubgroup, MonoidHom.comp_apply, steinberg_te6Ambient]
    exact congrArg (te6Ambient d) ((mem_fixedGroup (quadFrob d)).1 g.2)

theorem te6Embed_injective : Function.Injective (te6Embed d) := fun _ _ h =>
  Subtype.val_injective (te6Ambient_injective d (congrArg Subtype.val h))

end Embed

section Rank

variable (d : TypeTwistedE6LieIndex)

theorem commutator_fixedGroup_quadField :
    commutator ↥(fixedGroup (quadField d) (quadFrob d)) = ⊤ :=
  (fixedGroup_isPerfect_of_four_le_card (quadFrob d) (quadFrob_quadFrob d)
    (four_le_card_quadField d)).commutator_eq_top

theorem quadFrob_eq_sq (hq : d.1.fieldOrder = 2) (c : quadField d) : quadFrob d c = c ^ 2 :=
  Subtype.ext (by rw [coe_quadFrob, hq, SubmonoidClass.coe_pow])

theorem four_le_twoLocalOddRank_twistedE6Index [Finite (FixedPointCandidate d.steinberg)] :
    4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.steinberg) := by
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hθ : ∀ c, quadFrob d (quadFrob d c) = c := quadFrob_quadFrob d
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  have hinj : ∀ i, Function.Injective
      ((toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i)) := fun i =>
    toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj i hA
  have hcomm : ∀ i i', i ≠ i' → ∀ A B : SL(2, d.1.fixedField),
      (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i) A *
          (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i') B =
        (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i') B *
          (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i) A := by
    intro i i' hii A B
    simp only [MonoidHom.comp_apply, ← map_mul,
      te6SL2_commute (quadFrob d) (quadIncl d) hj hii A B]
  by_cases hq : d.1.fieldOrder = 2
  · classical
    have : Fintype (quadField d) := Fintype.ofFinite _
    have hKu : Fintype.card (quadField d)ˣ = 3 := by
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card, card_quadField, hq]
      rfl
    have : Nontrivial (quadField d)ˣ := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨t, ht1⟩ := exists_ne (1 : (quadField d)ˣ)
    have ht3 : t ^ 3 = 1 := by
      rw [← hKu]
      exact pow_card_eq_one
    have htt : t * Units.map (quadFrob d : quadField d →* quadField d) t = 1 := by
      have e : Units.map (quadFrob d : quadField d →* quadField d) t = t ^ 2 := Units.ext (by
        rw [Units.coe_map, Units.val_pow_eq_pow_val, MonoidHom.coe_ofClass,
          quadFrob_eq_sq d hq])
      rw [e, ← pow_succ', ht3]
    have ht2 : ((t : quadField d)) ^ 2 ≠ 1 := by
      intro h
      apply ht1
      have h' : t ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
      calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
        _ = 1 := by rw [ht3, h', inv_one, one_mul]
    exact four_le_twoLocalOddRank_of_localRank Nat.prime_three (by norm_num)
      (four_le_localRank_three_te6 (quadFrob d) (quadIncl d) hj hθ (toQuot (te6Embed d) hC)
        (fun g hg => mem_center_of_toQuot_eq_one (te6Embed_injective d) hC hg) hinj
        (ringChar_fixedField_eq_two hq) htt ht3 ht2)
  · exact four_le_twoLocalOddRank_of_four_commuting_SL2 (K := d.1.fixedField)
      (by rw [fintype_card_fixedField]; exact hq)
      (fun i => (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i)) hinj hcomm

end Rank

theorem four_le_twoLocalOddRank_twistedE6 (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid)
    [hfin : Finite (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group :=
  @four_le_twoLocalOddRank_twistedE6Index
    ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩ hfin

end CFSG.RankThree.PartTwo.Census.Exceptional
