module

public import CFSG.Monster.B.E6.StdF4Opposite

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open Module CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.Monster.B.Classical
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Classical.UnitarySix (ProjSU IsoPt tPt rep₁)

abbrev tW
    (w : NW) : stdGroup := rootMap (stdRep w)

theorem tW_eq
    (w : NW) : tW w = stdRep w * rootInv * (stdRep w)⁻¹ := rfl

theorem coe_tW
    (w : NW) :
    (tW w : ModGL Tag.E6 K) = pinnedX Tag.E6 K (toLat (wsmul w E6Folded.θ)) 1 :=
  coe_rootMap_stdRep w

theorem conjOrbit_parStar_tW
    (w : NW) :
    conjOrbit (parStar firstJ) (SemidirectProduct.inl (tW w)) =
      SemidirectProduct.inl '' levPoints (level w) := by
  rw [conjOrbit_parStar_rootMap, lev_stdRep]

theorem conjOrbit_PJ_tW
    (w : NW) : conjOrbit PJ (tW w) = levPoints (level w) := by
  rw [conjOrbit_PJ_rootMap, lev_stdRep]

theorem ncard_conjOrbit_parStar_tW
    {w : NW} {i : Fin 5} (h : level w = repLevel i) :
    (conjOrbit (parStar firstJ) (SemidirectProduct.inl (tW w))).ncard = repSize i := by
  rw [conjOrbit_parStar_tW, Set.ncard_image_of_injective _ SemidirectProduct.inl_injective, h,
    ncard_levPoints]

theorem ncard_conjOrbit_PJ_tW
    {w : NW} {i : Fin 5} (h : level w = repLevel i) :
    (conjOrbit PJ (tW w)).ncard = repSize i := by
  rw [conjOrbit_PJ_tW, h, ncard_levPoints]

theorem exists_tW
    (x : stdGroup) (hx : x ∈ rootClass) :
    ∃ w : NW, SemidirectProduct.inl x ∈ conjOrbit (parStar firstJ) (SemidirectProduct.inl (tW w)) ∧
      x ∈ conjOrbit PJ (tW w) := by
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff _).1 hx
  obtain ⟨i, hi⟩ := exists_repLevel g
  refine ⟨ncs.wordProd (repWord i), ?_, ?_⟩
  · rw [conjOrbit_parStar_tW, level_repWord, ← hi]
    exact ⟨_, rootMap_mem_levPoints g, rfl⟩
  · rw [conjOrbit_PJ_tW, level_repWord, ← hi]
    exact rootMap_mem_levPoints g

theorem exists_leviG_conj
    (p : IsoPt) :
    ∃ l : stdLevi firstJ, leviG l * repPoint 2 * (leviG l)⁻¹ = rootPt p := by
  have h1 : IsConj (rep₁ : ProjSU) (tPt p) := by
    have hp := UnitarySix.tPt_mem_rankOneClass p
    rw [UnitarySix.rankOneClass_eq_conj] at hp
    have hr := rep₁_mem_rankOneClass
    rw [UnitarySix.rankOneClass_eq_conj] at hr
    exact (isConj_comm.1 hr).trans hp
  obtain ⟨c, hc⟩ := isConj_iff.1 h1
  refine ⟨leviPSU.symm c, ?_⟩
  rw [← leviG_leviOf_rep₁, ← leviPSU_symm_rep₁, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv, ← map_mul, ← map_mul, hc]
  rfl

theorem leviG_mem_PJ
    (l : stdLevi firstJ) : leviG l ∈ PJ :=
  stdLevi_le_nativeParabolic two_mem_firstJ l.2

theorem rootLeviSet_eq_conjOrbit :
    rootLeviSet = conjOrbit ((stdLevi firstJ).subgroupOf stdGroup) (repPoint 2) := by
  ext x
  constructor
  · intro hx
    rw [rootLeviSet_eq_range] at hx
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨l, hl⟩ := exists_leviG_conj p
    exact ⟨leviG l, Subgroup.mem_subgroupOf.2 l.2, hl⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨repPoint_two_mem_rootClass.trans (isConj_iff.2 ⟨c, rfl⟩), ?_⟩
    have h2 : ((repPoint 2 : stdGroup) : ModGL Tag.E6 K) ∈ stdLevi firstJ := by
      rw [← leviG_leviOf_rep₁]
      exact (leviOf rep₁).2
    exact mul_mem (mul_mem (Subgroup.mem_subgroupOf.1 hc) h2)
      (inv_mem (Subgroup.mem_subgroupOf.1 hc))

theorem leviG_mem_rootClass_iff
    (l : stdLevi firstJ) :
    leviG l ∈ rootClass ↔ leviPSU l ∈ UnitarySix.rankOneClass := by
  rw [← UnitarySix.range_tPt]
  constructor
  · intro h
    have hx : leviG l ∈ rootLeviSet := ⟨h, l.2⟩
    rw [rootLeviSet_eq_range] at hx
    obtain ⟨p, hp⟩ := hx
    refine ⟨p, ?_⟩
    have e : leviPSU.symm (tPt p) = l := leviG_injective hp
    rw [← e, MulEquiv.apply_symm_apply]
  · rintro ⟨p, hp⟩
    have e : rootPt p = leviG l := by rw [rootPt, hp, MulEquiv.symm_apply_apply]
    rw [← e]
    exact (rootPt_mem_rootLeviSet p).1

theorem ncard_conjOrbit_parStar_repPoint_two :
    (conjOrbit (parStar firstJ) (SemidirectProduct.inl (repPoint 2))).ncard = 44352 :=
  ncard_conjOrbit_parStar_tW (w := ncs.wordProd (repWord 2)) (level_repWord 2)

theorem rootLeviSet_subset_levPoints :
    rootLeviSet ⊆ levPoints (repLevel 2) := by
  rw [rootLeviSet_eq_conjOrbit]
  rintro _ ⟨c, hc, rfl⟩
  have hc' : c ∈ PJ := stdLevi_le_nativeParabolic two_mem_firstJ (Subgroup.mem_subgroupOf.1 hc)
  have h := (conjOrbit_PJ_tW (ncs.wordProd (repWord 2)))
  rw [level_repWord 2] at h
  rw [← h]
  exact ⟨c, hc', rfl⟩

theorem ncard_conjOrbit_centralizer_of_mem
    {y : stdGroup} (hy : y ∈ rootLeviSet) :
    (conjOrbit (Subgroup.centralizer {rootStar}) (SemidirectProduct.inl y)).ncard = 44352 := by
  obtain ⟨g, hg, rfl⟩ := rootLeviSet_subset_levPoints hy
  rw [centralizer_rootStar, conjOrbit_parStar_rootMap, hg,
    Set.ncard_image_of_injective _ SemidirectProduct.inl_injective, ncard_levPoints]
  rfl

theorem orderOf_mul_comm_of {M : Type*} [Group M] (a b : M) :
    orderOf (b * a) = orderOf (a * b) := by
  have e : b * a = MulAut.conj a⁻¹ (a * b) := by
    rw [MulAut.conj_apply]
    group
  rw [e, MulEquiv.orderOf_eq]

theorem ne_of_commute_of_orderOf
    {p q x : stdGroup} (hpq : orderOf (p * q) = 3)
    (hp : p * p = 1) (hq : q * q = 1) (h1 : Commute x p) (h2 : Commute x q) : x ≠ p := by
  rintro rfl
  have h : (x * q) ^ 2 = 1 := by
    rw [h2.mul_pow, pow_two, pow_two, hp, hq, one_mul]
  have := orderOf_dvd_of_pow_eq_one h
  rw [hpq] at this
  exact absurd this (by decide)

theorem mul_self_of_mem_rootClass
    {x : stdGroup} (hx : x ∈ rootClass) : x * x = 1 := by
  rw [← pow_two]
  exact sq_of_mem_rootClass hx

theorem ncard_conjOrbit_of_commute
    {p q x : stdGroup} (hp : p ∈ rootClass) (hq : q ∈ rootClass)
    (hpq : orderOf (p * q) = 3) (hx : x ∈ rootClass) (h1 : Commute x p) (h2 : Commute x q) :
    (conjOrbit (Subgroup.centralizer {SemidirectProduct.inl p})
      (SemidirectProduct.inl x : GStar)).ncard = 44352 := by
  obtain ⟨g, hgt, hgq, -, hN⟩ :=
    (standard_F4_opposite_root_common_neighbor_geometry).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p q hp hq hpq
  have hpp := mul_self_of_mem_rootClass hp
  have hqq := mul_self_of_mem_rootClass hq
  have hxN : x ∈ commonNbrs p q :=
    ⟨hx, ne_of_commute_of_orderOf hpq hpp hqq h1 h2, h1,
      ne_of_commute_of_orderOf ((orderOf_mul_comm_of p q).trans hpq) hqq hpp h2 h1, h2⟩
  rw [hN, commonNbrs_eq] at hxN
  obtain ⟨y, hy, rfl⟩ := hxN
  have e1 : (SemidirectProduct.inl p : GStar) =
      SemidirectProduct.inl g * rootStar * (SemidirectProduct.inl g)⁻¹ := by
    rw [← hgt, map_mul, map_mul, map_inv]
    rfl
  have e2 : (SemidirectProduct.inl (g * y * g⁻¹) : GStar) =
      SemidirectProduct.inl g * SemidirectProduct.inl y * (SemidirectProduct.inl g)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  have hinj : Function.Injective fun z : GStar =>
      SemidirectProduct.inl g * z * (SemidirectProduct.inl g)⁻¹ := fun a b h => by
    simpa using h
  rw [e1, e2, conjOrbit_centralizer_conj, Set.ncard_image_of_injective _ hinj]
  exact ncard_conjOrbit_centralizer_of_mem hy

theorem standard_F4_Weyl_pair_orbit_and_opposite_slice :
    Function.Injective weylPerm ∧ weylPerm.range = E6Folded.W ∧
    (∀ i : Fin 4, weylPerm (ncs.simple i) = E6Folded.gen i) ∧
    (∀ w : NW, (stdRep w : ModGL Tag.E6 K) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w) ∧
    (∀ w : NW, tW w = stdRep w * rootInv * (stdRep w)⁻¹ ∧
      (tW w : ModGL Tag.E6 K) = pinnedX Tag.E6 K (toLat (wsmul w E6Folded.θ)) 1 ∧
      (weylPerm w E6Folded.θΛ).1 = wsmul w E6Folded.θ) ∧
    repLevel = ![2, 1, 0, -1, -2] ∧ repSize = ![1, 1782, 44352, 1824768, 2097152] ∧
    (∀ w : NW, ∃ i : Fin 5, E6Folded.form E6Folded.θ (weylPerm w E6Folded.θΛ).1 = repLevel i) ∧
    (∀ (w : NW) (i : Fin 5), E6Folded.form E6Folded.θ (weylPerm w E6Folded.θΛ).1 = repLevel i →
      (conjOrbit (parStar firstJ) (SemidirectProduct.inl (tW w))).ncard = repSize i ∧
        (conjOrbit PJ (tW w)).ncard = repSize i) ∧
    Subgroup.centralizer {rootStar} = parStar firstJ ∧
    (∀ x ∈ rootClass, ∃ w : NW,
      SemidirectProduct.inl x ∈ conjOrbit (parStar firstJ) (SemidirectProduct.inl (tW w)) ∧
        x ∈ conjOrbit PJ (tW w)) ∧
    (((leviOf rep₁ : stdLevi firstJ) : ModGL Tag.E6 K) = xUnit Tag.E6 K (i6 3) 1 ∧
      leviPSU (leviOf rep₁) = (rep₁ : ProjSU) ∧
      (((rep₁ : CFSG.LieType.Universal.Unitary.SU CFSG.LinearGroups.frobeniusF4 6) :
        GL (Fin 6) CFSG.Fischer.F4) : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4) =
          1 + Matrix.single 2 3 1) ∧
    (repPoint 2 ∈ rootClass ∧ (repPoint 2 : ModGL Tag.E6 K) = xUnit Tag.E6 K (i6 3) 1) ∧
    rootLeviSet = conjOrbit ((stdLevi firstJ).subgroupOf stdGroup) (repPoint 2) ∧
    (∀ l : stdLevi firstJ, leviG l ∈ rootClass ↔ leviPSU l ∈ UnitarySix.rankOneClass) ∧
    (conjOrbit (parStar firstJ) (SemidirectProduct.inl (repPoint 2))).ncard = 44352 ∧
    ∀ p q : stdGroup, p ∈ rootClass → q ∈ rootClass → orderOf (p * q) = 3 →
      ∀ x ∈ rootClass, Commute x p → Commute x q →
        (conjOrbit (Subgroup.centralizer {SemidirectProduct.inl p})
          (SemidirectProduct.inl x : GStar)).ncard = 44352 ∧
        (conjOrbit (Subgroup.centralizer {SemidirectProduct.inl q})
          (SemidirectProduct.inl x : GStar)).ncard = 44352 := by
  refine ⟨weylPerm_injective, range_weylPerm, weylPerm_simple, fun _ => rfl,
    fun w => ⟨rfl, coe_tW w, coe_weylPerm_apply w _⟩, rfl, rfl,
    fun w => ?_, fun w i h => ?_, centralizer_rootStar, exists_tW,
    ⟨coe_leviOf_rep₁, leviPSU_leviOf _, UnitarySix.coe_rep₁⟩,
    ⟨repPoint_two_mem_rootClass, coe_repPoint_two⟩, rootLeviSet_eq_conjOrbit,
    leviG_mem_rootClass_iff, ncard_conjOrbit_parStar_repPoint_two,
    fun p q hp hq hpq x hx h1 h2 => ⟨ncard_conjOrbit_of_commute hp hq hpq hx h1 h2,
      ncard_conjOrbit_of_commute hq hp ((orderOf_mul_comm_of p q).trans hpq) hx h2 h1⟩⟩
  · rcases level_cases w with h | h | h | h | h
    · exact ⟨0, (level_eq w).symm.trans h⟩
    · exact ⟨1, (level_eq w).symm.trans h⟩
    · exact ⟨2, (level_eq w).symm.trans h⟩
    · exact ⟨3, (level_eq w).symm.trans h⟩
    · exact ⟨4, (level_eq w).symm.trans h⟩
  · have h' : level w = repLevel i := (level_eq w).trans h
    exact ⟨ncard_conjOrbit_parStar_tW h', ncard_conjOrbit_PJ_tW h'⟩

end CFSG.Monster.B.E6.StdF4
