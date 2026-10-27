module

public import CFSG.Sporadic.Fi22.LocalPSU

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ExistenceF22 (G : Type) [Group G] (D : Set G) : Prop :=
  Subgroup.center G = ⊥ ∧ IsSimpleGroup (commutator G) ∧ HasType 0 G D ∧
    (∀ E : Set G, Pair G E → E = D) ∧ ∀ d ∈ D, LocalStructureAt 0 d

theorem ExistenceF22.congr {G H : Type} [Group G] [Group H] {D : Set G} (h : ExistenceF22 G D)
    (φ : G ≃* H) : ExistenceF22 H (φ '' D) := by
  obtain ⟨hZ, hS, hT, hU, hL⟩ := h
  refine ⟨?_, ?_, hasType_map hT φ, fun E hE => ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    have h : φ.symm z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (φ g)
    rw [hZ, Subgroup.mem_bot] at h
    rw [Subgroup.mem_bot]
    simpa using congrArg φ h
  · let e : commutator G ≃* commutator H :=
      ((commutator G).equivMapOfInjective (φ : G →* H) φ.injective).trans
        (MulEquiv.subgroupCongr (map_commutator_mulEquiv φ))
    exact e.symm.isSimpleGroup
  · have h1 := hU _ (pair_map hE φ.symm)
    rw [← h1, ← Set.image_comp]
    simp
  · rintro _ ⟨d, hd, rfl⟩
    exact (hL d hd).map φ

theorem localStructureAt_a :
    LocalStructureAt 0 a := by
  refine ⟨fun _ => ⟨commutator_Ca, ?_, card_center_Ca, 1, isNondegenerateHermitian_one,
    ⟨(caQuotEquiv.trans suQuotEquiv.symm).trans psuEquiv⟩⟩,
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  rw [center_Ca_eq, MonoidHom.map_zpowers]
  rfl

theorem localStructureAt_of_mem_D
    {d : J} (hd : d ∈ D) : LocalStructureAt 0 d := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (hd : IsConj a d)
  exact localStructureAt_a.map (MulAut.conj g)

@[expose] def equivOfEqTop {G : Type*} [Group G] {H : Subgroup G} (h : H = ⊤) : H ≃* G where
  toFun := Subtype.val
  invFun x := ⟨x, by rw [h]; trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem isSimpleGroup_commutator_J : IsSimpleGroup (commutator J) :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J (equivOfEqTop commutator_eq_top)

theorem existence_J :
    ExistenceF22 J D :=
  ⟨center_eq_bot, isSimpleGroup_commutator_J, f22_J, pair_eq_D,
    fun _ hd => localStructureAt_of_mem_D hd⟩

theorem existence_native :
    ExistenceF22 Blueprint.NativeSporadic.Fi22 (fi22EquivJ.symm '' D) :=
  @ExistenceF22.congr (↥J) Blueprint.NativeSporadic.Fi22 inferInstance inferInstance D existence_J
    fi22EquivJ.symm

set_option maxRecDepth 100000 in
theorem carrierGroup_zero :
    carrierGroup 0 = (inferInstance : Group Blueprint.NativeSporadic.Fi22) :=
  rfl

noncomputable abbrev D22 : Set (Carrier 0) := fi22EquivJ.symm '' D

theorem existence_carrier :
    @ExistenceF22 (Carrier 0) (carrierGroup 0) D22 := by
  rw [carrierGroup_zero]
  exact existence_native

theorem fischer_existence_zero :
    Subgroup.center (Carrier 0) = ⊥ ∧ IsSimpleGroup (commutator (Carrier 0)) ∧
      ∃ D : Set (Carrier 0), HasType 0 (Carrier 0) D ∧
        (∀ E : Set (Carrier 0), Pair (Carrier 0) E → E = D) ∧ LocalStructure 0 D := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := existence_carrier
  exact ⟨h1, h2, D22, h3, h4, h5⟩

end CFSG.Sporadic.Fi22
