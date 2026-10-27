module

public import CFSG.Sporadic.Fi23.Centralizer
public import CFSG.Sporadic.Fi23.Classes
public import CFSG.Sporadic.Fi22.Fischer

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ExistenceF23 (G : Type) [Group G] (D : Set G) : Prop :=
  Subgroup.center G = ⊥ ∧ IsSimpleGroup (commutator G) ∧ HasType 1 G D ∧
    (∀ E : Set G, Pair G E → E = D) ∧ ∀ d ∈ D, LocalStructureAt 1 d

theorem ExistenceF23.congr
    {G H : Type} [Group G] [Group H] {D : Set G} (h : ExistenceF23 G D)
    (φ : G ≃* H) : ExistenceF23 H (φ '' D) := by
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

theorem center_J : Subgroup.center J = ⊥ := by
  have hs := isSimpleGroup_J
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact h
  · exfalso
    have hd : d ∈ Subgroup.center J := by rw [h]; trivial
    have hc : d * conjPt 2 = conjPt 2 * d := (Subgroup.mem_center_iff.1 hd (conjPt 2)).symm
    have hx : IsConj d (conjPt 2) := (isConj_d_iff _).2 ⟨⟨2, by norm_num⟩, rfl⟩
    have hd2 : d * d = 1 := by rw [← sq, ← orderOf_d, pow_orderOf_eq_one]
    have hx2 : conjPt 2 * conjPt 2 = 1 := by
      have h' := pow_orderOf_eq_one (conjPt 2)
      rw [orderOf_of_isConj hx, sq] at h'
      exact h'
    have hsq : (d * conjPt 2) ^ 2 = 1 := by
      rw [sq]
      calc d * conjPt 2 * (d * conjPt 2) = d * (conjPt 2 * d) * conjPt 2 := by
            simp only [mul_assoc]
        _ = d * (d * conjPt 2) * conjPt 2 := by rw [hc]
        _ = (d * d) * (conjPt 2 * conjPt 2) := by simp only [mul_assoc]
        _ = 1 := by rw [hd2, hx2, one_mul]
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [orderOf_d_mul_conjPt_two] at this
    norm_num at this

theorem commutator_J : commutator J = ⊤ := by
  have hs := isSimpleGroup_J
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator J) with h | h
  · exfalso
    have h2 : (⊤ : Subgroup J) ≤ Subgroup.centralizer (⊤ : Subgroup J) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [← commutator_def]; exact h)
    have hz : Subgroup.center J = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_iff.1 (h2 (Subgroup.mem_top z)) g (Subgroup.mem_top g)
    rw [center_J] at hz
    have := orderOf_d
    rw [show d = 1 from by
      have : d ∈ (⊥ : Subgroup J) := by rw [hz]; trivial
      exact Subgroup.mem_bot.1 this, orderOf_one] at this
    norm_num at this
  · exact h

theorem isSimpleGroup_commutator_J : IsSimpleGroup (commutator J) :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J (Fi22.equivOfEqTop commutator_J)

theorem localStructureAt_d :
    LocalStructureAt 1 d :=
  ⟨fun h => absurd h (by decide), fun _ => ⟨commutator_C, center_C_map, card_center_C,
    ⟨quotCenterEquiv.trans Fi22.fi22EquivJ.symm⟩⟩, fun h => absurd h (by decide)⟩

theorem localStructureAt_of_mem
    {x : J} (hx : x ∈ D23) : LocalStructureAt 1 x := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (hx : IsConj d x)
  exact localStructureAt_d.map (MulAut.conj g)

theorem localImages_eq :
    localQuotientEquiv.symm '' Fi22.D = LocalImages D23 d := by
  rw [← localQuotientEquiv_image]
  exact image_symm_image _ _

theorem f22_local :
    F22 (LocalQuotient D23 d) (LocalImages D23 d) :=
  (@F22_congr (↥Fi22.J) (LocalQuotient D23 d) inferInstance inferInstance Fi22.D
    (LocalImages D23 d) localQuotientEquiv.symm localImages_eq).1 Fi22.f22_J

theorem f23_J :
    F23 J D23 := ⟨pair_J, d, IsConj.refl d, f22_local⟩

theorem existence_J :
    ExistenceF23 J D23 :=
  ⟨center_J, isSimpleGroup_commutator_J, f23_J, pair_eq_D23,
    fun _ hx => localStructureAt_of_mem hx⟩

theorem existence_native :
    ExistenceF23 Blueprint.NativeSporadic.Fi23 (fi23EquivJ.symm '' D23) :=
  @ExistenceF23.congr (↥J) Blueprint.NativeSporadic.Fi23 inferInstance inferInstance D23
    existence_J fi23EquivJ.symm

set_option maxRecDepth 100000 in
theorem carrierGroup_one :
    carrierGroup 1 = (inferInstance : Group Blueprint.NativeSporadic.Fi23) :=
  rfl

noncomputable abbrev D23c : Set (Carrier 1) := fi23EquivJ.symm '' D23

theorem existence_carrier :
    @ExistenceF23 (Carrier 1) (carrierGroup 1) D23c := by
  rw [carrierGroup_one]
  exact existence_native

theorem fischer_existence_one :
    Subgroup.center (Carrier 1) = ⊥ ∧ IsSimpleGroup (commutator (Carrier 1)) ∧
      ∃ D : Set (Carrier 1), HasType 1 (Carrier 1) D ∧
        (∀ E : Set (Carrier 1), Pair (Carrier 1) E → E = D) ∧ LocalStructure 1 D := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := existence_carrier
  exact ⟨h1, h2, D23c, h3, h4, h5⟩

end CFSG.Sporadic.Fi23
