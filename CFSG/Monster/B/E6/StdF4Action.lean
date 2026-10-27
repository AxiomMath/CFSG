module

public import CFSG.Monster.B.E6.StdF4UnitModel
public import CFSG.Monster.B.Geometry.F4Stabilizer
public import CFSG.Monster.B.Generic.OvergroupConjugacy
public import CFSG.Monster.B.E6.StandardSimple

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Generic
open scoped Pointwise

@[expose] def starPerm :
    GStar →* Equiv.Perm stdChamber := MulAction.toPermHom GStar stdChamber

@[expose] def groupPerm :
    stdGroup →* Equiv.Perm stdChamber :=
  starPerm.comp SemidirectProduct.inl

theorem starPerm_apply
    (γ : GStar) (x : stdChamber) : starPerm γ x = γ • x := rfl

theorem groupPerm_apply
    (g : stdGroup) (x : stdChamber) : groupPerm g x = g • x := by
  induction x using QuotientGroup.induction_on with | H y => ?_
  rfl

theorem starPerm_injective :
    Function.Injective starPerm := by
  rw [injective_iff_map_eq_one]
  intro γ h
  exact eq_one_of_forall_smul_eq_star fun q => congrArg (fun f : Equiv.Perm stdChamber => f q) h

theorem groupPerm_injective :
    Function.Injective groupPerm :=
  starPerm_injective.comp SemidirectProduct.inl_injective

abbrev autA :
    Subgroup (Equiv.Perm stdChamber) := typeAut ncs stdDistance

theorem starPerm_mem_autA
    (γ : GStar) : starPerm γ ∈ autA := fun x y i => by
  rw [starPerm_apply, starPerm_apply, stdDistance_smul]

theorem range_starPerm_le :
    starPerm.range ≤ autA := by
  rintro _ ⟨γ, rfl⟩
  exact starPerm_mem_autA γ

theorem range_groupPerm_le_starPerm :
    groupPerm.range ≤ starPerm.range := by
  rintro _ ⟨g, rfl⟩
  exact ⟨_, rfl⟩

theorem range_groupPerm_le :
    groupPerm.range ≤ autA :=
  range_groupPerm_le_starPerm.trans range_starPerm_le

theorem card_range_starPerm :
    Nat.card starPerm.range = 153064959367549707878400 := by
  rw [← card_GStar]
  exact Nat.card_congr (MonoidHom.ofInjective starPerm_injective).toEquiv.symm

theorem card_range_groupPerm :
    Nat.card groupPerm.range = 76532479683774853939200 := by
  rw [← card_stdGroup]
  exact Nat.card_congr (MonoidHom.ofInjective groupPerm_injective).toEquiv.symm

theorem stdDistance_groupPerm
    (g : stdGroup) (a b : stdChamber) :
    stdDistance (MulAction.toPerm g a) (MulAction.toPerm g b) = stdDistance a b := by
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  exact stdDistance_mul_mul g a b

theorem toPerm_c₀
    (g : stdGroup) : MulAction.toPerm g c₀ = (g : stdChamber) := by
  change ((g * 1 : stdGroup) : stdChamber) = (g : stdChamber)
  rw [mul_one]

theorem residueModels :
    (∀ x, IsPlaneFlagResidue (coxeterSystem .F4) stdDistanceF4 (ZMod 2) 0 1 x) ∧
    (∀ x, IsPlaneFlagResidue (coxeterSystem .F4) stdDistanceF4 K 2 3 x) ∧
    ∀ x, IsQuadrangleFlagResidue (coxeterSystem .F4) stdDistanceF4 1 2 x := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩ <;>
    induction x using QuotientGroup.induction_on with | H g => ?_
  · have h := IsPlaneFlagResidue.map (MulAction.toPerm g) (stdDistance_groupPerm g)
      isPlaneFlagResidue_two_c₀
    rw [toPerm_c₀] at h
    exact IsPlaneFlagResidue.mapWeyl nativeWeylEquiv_simple h
  · have h := IsPlaneFlagResidue.map (MulAction.toPerm g) (stdDistance_groupPerm g)
      isPlaneFlagResidue_four_c₀
    rw [toPerm_c₀] at h
    exact IsPlaneFlagResidue.mapWeyl nativeWeylEquiv_simple h
  · have h := IsQuadrangleFlagResidue.map (MulAction.toPerm g) (stdDistance_groupPerm g)
      isQuadrangleFlagResidue_c₀
    rw [toPerm_c₀] at h
    exact IsQuadrangleFlagResidue.mapWeyl nativeWeylEquiv_simple h

theorem mem_typeAut_F4_iff
    (g : Equiv.Perm stdChamber) :
    g ∈ typeAut (coxeterSystem .F4) stdDistanceF4 ↔ g ∈ autA := by
  have key : ∀ (a b : stdChamber) (j : Fin 4),
      stdDistanceF4 a b = (coxeterSystem .F4).simple (nativeIdx j) ↔
        stdDistance a b = ncs.simple j := fun a b j => by
    have h := nativeWeylEquiv_simple j
    constructor
    · intro e
      exact nativeWeylEquiv.injective (e.trans h.symm)
    · intro e
      change nativeWeylEquiv (stdDistance a b) = _
      rw [e]
      exact h
  constructor
  · intro hg x y i
    exact (key _ _ i).symm.trans ((hg x y (nativeIdx i)).trans (key x y i))
  · intro hg x y i
    have hi : (coxeterSystem .F4).simple i = (coxeterSystem .F4).simple (nativeIdx ⟨i.1, i.2⟩) :=
      rfl
    rw [hi]
    exact (key _ _ _).trans ((hg x y ⟨i.1, i.2⟩).trans (key x y _).symm)

@[expose] def w₀N :

    NW := nativeWeylEquiv.symm (longest (coxeterSystem .F4) Set.univ)

@[expose] def d₀ :
    stdChamber := ((stdRep w₀N : stdGroup) : stdChamber)

theorem stdDistance_c₀_d₀ :
    stdDistance c₀ d₀ = w₀N := wOf_stdRep w₀N

theorem stdDistanceF4_c₀_d₀ :
    stdDistanceF4 c₀ d₀ = longest (coxeterSystem .F4) Set.univ := by
  change nativeWeylEquiv (stdDistance c₀ d₀) = _
  rw [stdDistance_c₀_d₀, w₀N]
  exact MulEquiv.apply_symm_apply _ _

abbrev oppPairs :
    Set (stdChamber × stdChamber) := {p | stdDistance p.1 p.2 = w₀N}

abbrev p₀ :
    stdChamber × stdChamber := (c₀, d₀)

theorem orbit_pair_eq
    {H : Subgroup (Equiv.Perm stdChamber)} (hGH : groupPerm.range ≤ H)
    (hHA : H ≤ autA) : MulAction.orbit H p₀ = oppPairs := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨h, hh⟩
    have e : ((h : Equiv.Perm stdChamber) c₀, (h : Equiv.Perm stdChamber) d₀) = (x, y) := hh
    rw [Prod.mk.injEq] at e
    change stdDistance x y = w₀N
    rw [← e.1, ← e.2, dist_typeAut hδ (hHA h.2), stdDistance_c₀_d₀]
  · intro hxy
    change stdDistance x y = w₀N at hxy
    induction x using QuotientGroup.induction_on with | H g => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [stdDistance_mk_mk, wOf_eq_iff, stdCell_eq] at hxy
    obtain ⟨_, ⟨b, hb, n, hn, rfl⟩, b', hb', e⟩ := hxy
    rw [Set.mem_singleton_iff] at hn
    subst hn
    simp only at e
    refine ⟨⟨groupPerm (g * b), hGH ⟨_, rfl⟩⟩, ?_⟩
    change (groupPerm (g * b) c₀, groupPerm (g * b) d₀) = ((g : stdChamber), (y : stdChamber))
    rw [groupPerm_apply, groupPerm_apply]
    refine Prod.ext ?_ ?_
    · change ((g * b * 1 : stdGroup) : stdChamber) = (g : stdChamber)
      rw [mul_one]
      exact QuotientGroup.eq.2 (by rw [mul_inv_rev, inv_mul_cancel_right]; exact inv_mem hb)
    · change ((g * b * stdRep w₀N : stdGroup) : stdChamber) = (y : stdChamber)
      refine QuotientGroup.eq.2 ?_
      have : y = g * (b * stdRep w₀N * b') := by rw [e, mul_inv_cancel_left]
      rw [this]
      have e' : (g * b * stdRep w₀N)⁻¹ * (g * (b * stdRep w₀N * b')) = b' := by group
      rw [e']
      exact hb'

theorem card_eq_card_stabilizer_mul
    {H : Subgroup (Equiv.Perm stdChamber)}
    (hGH : groupPerm.range ≤ H) (hHA : H ≤ autA) :
    Nat.card H = Nat.card (MulAction.stabilizer H p₀) * oppPairs.ncard := by
  rw [← (MulAction.stabilizer H p₀).card_mul_index, MulAction.index_stabilizer,
    orbit_pair_eq hGH hHA]

theorem card_stabilizer_autA :
    Nat.card (MulAction.stabilizer autA p₀) =
      Nat.card (pairStab (coxeterSystem .F4) stdDistanceF4 c₀ d₀) := by
  refine Nat.card_congr
    { toFun := fun a => ⟨a.1.1, mem_pairStab.2 ⟨(mem_typeAut_F4_iff _).2 a.1.2,
        congrArg Prod.fst a.2, congrArg Prod.snd a.2⟩⟩
      invFun := fun t => ⟨⟨t.1, (mem_typeAut_F4_iff _).1 (mem_pairStab.1 t.2).1⟩,
        Prod.ext (mem_pairStab.1 t.2).2.1 (mem_pairStab.1 t.2).2.2⟩
      left_inv := fun a => rfl
      right_inv := fun t => rfl }

theorem card_pairStab_dvd :
    Nat.card (pairStab (coxeterSystem .F4) stdDistanceF4 c₀ d₀) ∣ 18 := by
  obtain ⟨h12, h34, h23⟩ := residueModels
  obtain ⟨p, hp⟩ := exists_isProjection isWeylDistanceBuilding_stdDistanceF4
    ({2, 3} : Set (Fin Tag.F4.rank)) c₀ d₀
  obtain ⟨ρ, -, -, -, h⟩ := F4_opposite_pair_automorphism_stabilizer_bound
    isWeylDistanceBuilding_stdDistanceF4 h12 h34 h23 (by rw [Nat.card_eq_fintype_card, ZMod.card])
    (by rw [Nat.card_eq_fintype_card]; exact C2E6Overlap.card_K) stdDistanceF4_c₀_d₀ hp
  exact h

theorem fixedTorusGen_mem_stdTorus :
    fixedTorusGen ∈ stdTorus :=
  stdTorus0_eq_stdTorus ▸ fixedTorusGen_mem_stdTorus0

theorem fixedTorusGen_mem_stdBorel :
    fixedTorusGen ∈ stdBorel :=
  graphFixedRootTorus_le_graphFixedRootBorel fixedTorusGen_mem_stdTorus

theorem conj_mem_stdBorel
    {h : ModGL Tag.E6 K} (hh : h ∈ stdTorus) :
    (stdRepM w₀N)⁻¹ * h * stdRepM w₀N ∈ stdBorel := by
  have hn := canonicalRep_mem_graphFixedRootMonomial TwistTag.E6 K barHom w₀N.2
  have hHN : stdTorus ≤ graphFixedRootMonomial TwistTag.E6 K barHom :=
    inf_le_inf_right _ (graphFixedTorus_le_graphFixedMonomial TwistTag.E6 K barHom)
  have hN := graphFixedRootTorus_subgroupOf_normal TwistTag.E6 K barHom
  have h' := Subgroup.mem_subgroupOf.1 (hN.conj_mem ⟨h, hHN hh⟩ (Subgroup.mem_subgroupOf.2 hh)
    ⟨_, inv_mem hn⟩)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h'
  exact graphFixedRootTorus_le_graphFixedRootBorel h'

theorem torusGenG_smul_p₀ :
    groupPerm torusGenG • p₀ = p₀ := by
  change (groupPerm torusGenG c₀, groupPerm torusGenG d₀) = (c₀, d₀)
  rw [groupPerm_apply, groupPerm_apply]
  refine Prod.ext ?_ ?_
  · change ((torusGenG * 1 : stdGroup) : stdChamber) = c₀
    refine QuotientGroup.eq.2 ?_
    rw [mul_one, mul_one]
    exact inv_mem fixedTorusGen_mem_stdBorel
  · change ((torusGenG * stdRep w₀N : stdGroup) : stdChamber) = d₀
    refine QuotientGroup.eq.2 ?_
    have e : (((torusGenG * stdRep w₀N)⁻¹ * stdRep w₀N : stdGroup) : ModGL Tag.E6 K) =
        (stdRepM w₀N)⁻¹ * fixedTorusGen⁻¹ * stdRepM w₀N := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
      rfl
    change (((torusGenG * stdRep w₀N)⁻¹ * stdRep w₀N : stdGroup) : ModGL Tag.E6 K) ∈ stdBorel
    rw [e]
    exact conj_mem_stdBorel (inv_mem fixedTorusGen_mem_stdTorus)

theorem groupPerm_torusGenG_ne_one :
    groupPerm torusGenG ≠ 1 := fun h =>
  fixedTorusGen_ne_one (congrArg Subtype.val (groupPerm_injective (h.trans (map_one _).symm)))

theorem two_le_card_stabilizer_groupPerm :
    2 ≤ Nat.card (MulAction.stabilizer groupPerm.range p₀) := by
  have : Finite (MulAction.stabilizer groupPerm.range p₀) := inferInstance
  refine (Finite.one_lt_card_iff_nontrivial).2 ⟨⟨1, one_mem _⟩,
    ⟨⟨groupPerm torusGenG, ⟨_, rfl⟩⟩, torusGenG_smul_p₀⟩, fun h => ?_⟩
  exact groupPerm_torusGenG_ne_one (congrArg (fun x => ((x : groupPerm.range) :
    Equiv.Perm stdChamber)) (congrArg Subtype.val h)).symm

theorem finite_stdChamber' :
    Finite stdChamber := inferInstance

theorem oppPairs_ncard_pos :
    0 < oppPairs.ncard :=
  (Set.ncard_pos (Set.toFinite _)).2 ⟨p₀, stdDistance_c₀_d₀⟩

theorem index_arith {S idx : ℕ} (hS : 2 ≤ S) (hT : S * idx ∣ 18) (heven : 2 ∣ idx) :
    idx = 2 ∨ idx = 6 := by
  have hdvd : idx ∣ 18 := (Dvd.intro_left S rfl).trans hT
  have hle : S * idx ≤ 18 := Nat.le_of_dvd (by norm_num) hT
  have hle' : 2 * idx ≤ 18 := (Nat.mul_le_mul_right idx hS).trans hle
  have hpos : 0 < idx := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have h9 : idx ≤ 9 := by omega
  interval_cases idx
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact absurd heven (by decide)
    | exact absurd hdvd (by decide)

theorem index_groupPerm_eq :
    (groupPerm.range.subgroupOf autA).index = 2 ∨ (groupPerm.range.subgroupOf autA).index = 6 := by
  set idx := (groupPerm.range.subgroupOf autA).index
  have hA := card_eq_card_stabilizer_mul (H := autA) range_groupPerm_le le_rfl
  have hG := card_eq_card_stabilizer_mul (H := groupPerm.range) le_rfl range_groupPerm_le
  have hS := card_stabilizer_autA
  have hT := card_pairStab_dvd
  have h2 := two_le_card_stabilizer_groupPerm
  have hsub : Nat.card (groupPerm.range.subgroupOf autA) = Nat.card groupPerm.range :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe range_groupPerm_le).toEquiv
  have hidx : Nat.card groupPerm.range * idx = Nat.card autA := by
    rw [← hsub]
    exact (groupPerm.range.subgroupOf autA).card_mul_index
  have hTS : Nat.card (MulAction.stabilizer autA p₀) =
      Nat.card (MulAction.stabilizer groupPerm.range p₀) * idx := by
    have := hidx
    rw [hA, hG, mul_assoc, mul_comm _ idx, ← mul_assoc] at this
    exact (Nat.eq_of_mul_eq_mul_right oppPairs_ncard_pos this).symm.trans (by ring)
  have hstar : Nat.card starPerm.range = 2 * Nat.card groupPerm.range := by
    rw [card_range_starPerm, card_range_groupPerm]
  have heven : 2 ∣ idx := by
    have hsub' : Nat.card (starPerm.range.subgroupOf autA) = Nat.card starPerm.range :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe range_starPerm_le).toEquiv
    have h1 := (starPerm.range.subgroupOf autA).card_mul_index
    rw [hsub', hstar, ← hidx] at h1
    have h1' : Nat.card groupPerm.range * idx =
        Nat.card groupPerm.range * (2 * (starPerm.range.subgroupOf autA).index) := by
      rw [← h1]
      ring
    have hpos : 0 < Nat.card groupPerm.range := Nat.card_pos
    exact ⟨_, Nat.eq_of_mul_eq_mul_left hpos h1'⟩
  rw [← hS, hTS] at hT
  exact index_arith h2 hT heven

theorem lt_card_groupPerm :
    720 < Nat.card (groupPerm.range.subgroupOf autA) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe range_groupPerm_le).toEquiv,
    card_range_groupPerm]
  norm_num

theorem isSimpleGroup_groupPerm :
    IsSimpleGroup (groupPerm.range.subgroupOf autA) := by
  have := (standard_twisted_e6_group_simple).2.2
  exact ((MonoidHom.ofInjective groupPerm_injective).trans
    (Subgroup.subgroupOfEquivOfLe range_groupPerm_le).symm).symm.isSimpleGroup

theorem map_subtype_subgroupOf
    {H : Subgroup (Equiv.Perm stdChamber)} (hH : H ≤ autA) :
    (H.subgroupOf autA).map autA.subtype = H := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hH]

theorem card_subgroupOf
    {H : Subgroup (Equiv.Perm stdChamber)} (hH : H ≤ autA) :
    Nat.card (H.subgroupOf autA) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv

theorem standard_F4_building_action_conjugacy :
    Function.Injective starPerm ∧ Function.Injective groupPerm ∧ starPerm.range ≤ autA ∧
    groupPerm.range ≤ starPerm.range ∧
    (∀ (γ : GStar) (x : stdChamber), starPerm γ x = γ • x) ∧
    (∀ (g : stdGroup) (x : stdChamber), groupPerm g x = g • x) ∧
    (groupPerm.range.subgroupOf autA).Normal ∧
    ((groupPerm.range.subgroupOf autA).index = 2 ∨
      (groupPerm.range.subgroupOf autA).index = 6) ∧
    153064959367549707878400 = 2 * Nat.card stdGroup ∧
    ∀ H : Subgroup (Equiv.Perm stdChamber), H ≤ autA →
      Nat.card H = 153064959367549707878400 →
        (∃ a ∈ autA, H.map (MulAut.conj a).toMonoidHom = starPerm.range) ∧
          Nonempty (H ≃* GStar) := by
  obtain ⟨hnormal, -, hconj⟩ := small_index_simple_overgroup_conjugacy
    (groupPerm.range.subgroupOf autA) isSimpleGroup_groupPerm lt_card_groupPerm
    index_groupPerm_eq
  have hG : Nat.card (groupPerm.range.subgroupOf autA) = 76532479683774853939200 := by
    rw [card_subgroupOf range_groupPerm_le, card_range_groupPerm]
  refine ⟨starPerm_injective, groupPerm_injective, range_starPerm_le, range_groupPerm_le_starPerm,
    fun _ _ => rfl, groupPerm_apply, hnormal, index_groupPerm_eq,
    by rw [card_stdGroup], fun H hHA hH => ?_⟩
  have hH' : Nat.card (H.subgroupOf autA) = 2 * Nat.card (groupPerm.range.subgroupOf autA) := by
    rw [card_subgroupOf hHA, hH, hG]
  have hJ' : Nat.card (starPerm.range.subgroupOf autA) =
      2 * Nat.card (groupPerm.range.subgroupOf autA) := by
    rw [card_subgroupOf range_starPerm_le, card_range_starPerm, hG]
  obtain ⟨a, ha⟩ := hconj _ _ hH' hJ'
  have hmap : H.map (MulAut.conj (a : Equiv.Perm stdChamber)).toMonoidHom = starPerm.range := by
    rw [← map_subtype_subgroupOf range_starPerm_le, ← ha]
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, Subtype.exists, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨_, mul_mem (mul_mem a.2 (hHA hh)) (inv_mem a.2), ?_, rfl⟩
      simp only [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
      exact hh
    · rintro ⟨y, hyA, hy, rfl⟩
      refine ⟨_, hy, ?_⟩
      simp only [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  refine ⟨⟨a, a.2, hmap⟩, ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective H _ (MulAut.conj (a : Equiv.Perm stdChamber)).injective).trans
    ((MulEquiv.subgroupCongr hmap).trans (MonoidHom.ofInjective starPerm_injective).symm)

end CFSG.Monster.B.E6.StdF4
