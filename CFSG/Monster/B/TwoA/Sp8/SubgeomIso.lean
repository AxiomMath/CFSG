module


public import CFSG.Monster.B.TwoA.Sp8.SubgeomVec
public import CFSG.Monster.B.TwoA.Sp8.SubgeomData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

attribute [local instance] parAction

theorem obj_le_A8
    {x : ParGeom} (hx : x ∈ subgeom) : x.1.2 ≤ A8 := by
  obtain ⟨h4, h, hh, hxh⟩ := mem_subgeom.1 hx
  rw [hxh]
  exact conjSub_le_A8 hh (Echain_le_A8 (parType_bounds x).1 h4)

theorem isotropic_obj
    {x : ParGeom} (hx : x ∈ subgeom) :
    IsTotallyIsotropic b0 (a8Vec x.1.2) ∧ finrank (ZMod 2) (a8Vec x.1.2) = parType x := by
  obtain ⟨h4, h, hh, hxh⟩ := mem_subgeom.1 hx
  rw [hxh]
  exact isotropic_a8Vec_conjSub ⟨h, hh⟩ (parType_bounds x).1 h4

theorem eq_of_a8Vec_eq
    {x y : ParGeom} (hx : x ∈ subgeom) (hy : y ∈ subgeom)
    (h : a8Vec x.1.2 = a8Vec y.1.2) : x = y := by
  have ht : parType x = parType y := by
    rw [← (isotropic_obj hx).2, ← (isotropic_obj hy).2, h]
  exact Subtype.ext (Prod.ext ht (a8Vec_injective (obj_le_A8 hx) (obj_le_A8 hy) h))

@[expose] def xToS :
    Xgrp →* Shat := Subgroup.inclusion Xgrp_le_Shat

theorem coe_xToS
    (x : Xgrp) : ((xToS x : Shat) : Dfull) = x := rfl

theorem a8Vec_smul
    (x : Xgrp) {c : ParGeom} (hc : c ∈ subgeom) :
    a8Vec (xToS x • c).1.2 = (a8Vec c.1.2).map (rhoX x : V8 →ₗ[ZMod 2] V8) :=
  a8Vec_conjSub x (obj_le_A8 hc)

@[expose, instance_reducible] def subgeomAction :
    MulAction Xgrp subgeom where
  smul x c := ⟨xToS x • c.1, smul_mem_subgeom x.2 c.2⟩
  one_smul c := Subtype.ext (by
    show xToS 1 • c.1 = c.1
    rw [map_one, one_smul])
  mul_smul x y c := Subtype.ext (by
    show xToS (x * y) • c.1 = xToS x • xToS y • c.1
    rw [map_mul, mul_smul])


@[expose] def isoSpaces : Set (Submodule (ZMod 2) V8) :=
  {W | IsTotallyIsotropic b0 W ∧ 1 ≤ finrank (ZMod 2) W ∧ finrank (ZMod 2) W ≤ 4}

theorem pair_mem_of_isoSpaces
    {W : Submodule (ZMod 2) V8} (hW : W ∈ isoSpaces) :
    (finrank (ZMod 2) W, a8Grp W) ∈ subgeomPairs := by
  obtain ⟨hi, h1, h4⟩ := hW
  obtain ⟨x, hx⟩ := exists_conj_eq_a8Grp hi h1 h4 rfl
  exact ⟨h1, h4, x, x.2, hx.symm⟩

@[expose] def objOfIso
    (W : isoSpaces) : subgeom :=
  ⟨⟨(finrank (ZMod 2) W.1, a8Grp W.1), subgeomPairs_subset_ParObj (pair_mem_of_isoSpaces W.2)⟩,
    pair_mem_of_isoSpaces W.2⟩

@[expose] def subgeomEquiv :
    subgeom ≃ isoSpaces where
  toFun x := ⟨a8Vec x.1.1.2, (isotropic_obj x.2).1,
    by rw [(isotropic_obj x.2).2]; exact (parType_bounds x.1).1,
    by rw [(isotropic_obj x.2).2]; exact (mem_subgeom.1 x.2).1⟩
  invFun := objOfIso
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    show (finrank (ZMod 2) (a8Vec x.1.1.2), a8Grp (a8Vec x.1.1.2)) = x.1.1
    rw [(isotropic_obj x.2).2, a8Grp_a8Vec (obj_le_A8 x.2)]
    rfl
  right_inv W := Subtype.ext (a8Vec_a8Grp W.1)

theorem le_iff_subgeomEquiv
    (x y : subgeom) :
    x.1.1.2 ≤ y.1.1.2 ↔
      (subgeomEquiv x : Submodule (ZMod 2) V8) ≤ (subgeomEquiv y : Submodule (ZMod 2) V8) :=
  (a8Vec_le_iff (obj_le_A8 x.2) (obj_le_A8 y.2)).symm

theorem parType_eq_finrank
    (x : subgeom) :
    parType x.1 = finrank (ZMod 2) (subgeomEquiv x : Submodule (ZMod 2) V8) :=
  (isotropic_obj x.2).2.symm

theorem parInc_iff_subgeomEquiv
    (x y : subgeom) :
    parInc x.1 y.1 ↔ x = y ∨
      (finrank (ZMod 2) (subgeomEquiv x).1 ≠ finrank (ZMod 2) (subgeomEquiv y).1 ∧
        ((subgeomEquiv x).1 ≤ (subgeomEquiv y).1 ∨ (subgeomEquiv y).1 ≤ (subgeomEquiv x).1)) := by
  rw [parInc, Subtype.coe_inj, parType_eq_finrank, parType_eq_finrank, le_iff_subgeomEquiv,
    le_iff_subgeomEquiv]

theorem coe_subgeomEquiv
    (x : subgeom) :
    ((subgeomEquiv x : isoSpaces) : Submodule (ZMod 2) V8) = a8Vec x.1.1.2 := rfl

theorem a8Vec_objOfIso
    (W : isoSpaces) : a8Vec (objOfIso W).1.1.2 = W.1 := a8Vec_a8Grp W.1

attribute [local instance] subgeomAction

attribute [local instance] subgeomAction

theorem coe_subgeom_smul
    (x : Xgrp) (c : subgeom) : ((x • c : subgeom) : ParGeom) = xToS x • c.1 :=
  rfl

theorem subgeomEquiv_smul
    (x : Xgrp) (c : subgeom) :
    (subgeomEquiv (x • c) : Submodule (ZMod 2) V8) =
      (subgeomEquiv c : Submodule (ZMod 2) V8).map (rhoX x : V8 →ₗ[ZMod 2] V8) :=
  a8Vec_smul x c.2

theorem smul_eq_self_iff
    (x : Xgrp) {c : ParGeom} (hc : c ∈ subgeom) :
    xToS x • c = c ↔ (a8Vec c.1.2).map (rhoX x : V8 →ₗ[ZMod 2] V8) = a8Vec c.1.2 := by
  constructor
  · intro h
    rw [← a8Vec_smul x hc, h]
  · intro h
    exact eq_of_a8Vec_eq (smul_mem_subgeom x.2 hc) hc ((a8Vec_smul x hc).trans h)

@[expose] def flagVec
    (F : Set ParGeom) (t : ℕ) : Submodule (ZMod 2) V8 :=
  ⨆ y ∈ {y | y ∈ F ∧ parType y = t}, a8Vec y.1.2

theorem flagVec_eq
    {F : Set ParGeom} (hF : IsParFlag F) {y : ParGeom} (hy : y ∈ F) :
    flagVec F (parType y) = a8Vec y.1.2 := by
  apply le_antisymm
  · refine iSup₂_le fun z hz => ?_
    rw [eq_of_parInc (hF z hz.1 y hy) hz.2]
  · exact le_iSup₂_of_le y ⟨hy, rfl⟩ le_rfl

theorem subgeom_flag_transitive
    {F F' : Set ParGeom} (hF : F ⊆ subgeom) (hF' : F' ⊆ subgeom)
    (hFf : IsParFlag F) (hFf' : IsParFlag F') (ht : parType '' F = parType '' F') :
    ∃ x : Xgrp, (xToS x • ·) '' F = F' := by
  set T : Finset ℕ := (Set.toFinite (parType '' F)).toFinset with hT
  have hmem : ∀ t, t ∈ T ↔ t ∈ parType '' F := fun t => Set.Finite.mem_toFinset _
  have key : ∀ {G : Set ParGeom}, G ⊆ subgeom → IsParFlag G → parType '' G = parType '' F →
      (∀ s ∈ T, ∀ t ∈ T, s ≤ t → flagVec G s ≤ flagVec G t) ∧
      (∀ t ∈ T, finrank (ZMod 2) (flagVec G t) = t) ∧
      (∀ t ∈ T, IsTotallyIsotropic b0 (flagVec G t)) := by
    intro G hG hGf hGt
    have hex : ∀ t ∈ T, ∃ y ∈ G, parType y = t := fun t htT => by
      have h := (hmem t).1 htT
      rw [← hGt] at h
      exact h
    refine ⟨fun s hs t htT hst => ?_, fun t htT => ?_, fun t htT => ?_⟩
    · obtain ⟨ys, hys, rfl⟩ := hex s hs
      obtain ⟨yt, hyt, rfl⟩ := hex t htT
      rw [flagVec_eq hGf hys, flagVec_eq hGf hyt]
      exact a8Vec_mono (le_of_parInc (hGf ys hys yt hyt) hst)
    · obtain ⟨y, hy, rfl⟩ := hex t htT
      rw [flagVec_eq hGf hy]
      exact (isotropic_obj (hG hy)).2
    · obtain ⟨y, hy, rfl⟩ := hex t htT
      rw [flagVec_eq hGf hy]
      exact (isotropic_obj (hG hy)).1
  obtain ⟨m1, d1, i1⟩ := key hF hFf rfl
  obtain ⟨m2, d2, i2⟩ := key hF' hFf' ht.symm
  obtain ⟨g, hg, hgF⟩ :=
    exists_isometry_map_chain b0_isAlt b0_nondegenerate finrank_V8 T m1 m2 d1 d2 i1 i2
  obtain ⟨x, hx⟩ := rhoXSp_surjective ⟨g, hg⟩
  have hxg : rhoX x = g := by
    rw [← coe_rhoXSp, hx]
  refine ⟨x, ?_⟩
  have hmap : ∀ y ∈ F, ∀ y' ∈ F', parType y = parType y' → xToS x • y = y' := by
    intro y hy y' hy' hyy'
    have htT : parType y ∈ T := (hmem _).2 ⟨y, hy, rfl⟩
    refine eq_of_a8Vec_eq (smul_mem_subgeom x.2 (hF hy)) (hF' hy') ?_
    rw [a8Vec_smul x (hF hy), ← flagVec_eq hFf hy, hxg, hgF _ htT, hyy', flagVec_eq hFf' hy']
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hyy'⟩ : ∃ y' ∈ F', parType y' = parType y := by
      rw [← Set.mem_image, ← ht]
      exact ⟨y, hy, rfl⟩
    show xToS x • y ∈ F'
    rw [hmap y hy y' hy' hyy'.symm]
    exact hy'
  · intro hz
    obtain ⟨y, hy, hyz⟩ : ∃ y ∈ F, parType y = parType z := by
      rw [← Set.mem_image, ht]
      exact ⟨z, hz, rfl⟩
    exact ⟨y, hy, hmap y hy z hz hyz⟩

theorem span_singleton_mem_isoSpaces {v : V8} (hv : v ≠ 0) :
    span (ZMod 2) {v} ∈ isoSpaces := by
  refine ⟨isTotallyIsotropic_span fun s hs t ht => ?_, ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hs ht
    rw [hs, ht]
    exact b0_isAlt v
  · rw [finrank_span_singleton hv]
  · rw [finrank_span_singleton hv]
    norm_num

theorem subgeom_kernel_iff
    (x : Xgrp) : (∀ c ∈ subgeom, xToS x • c = c) ↔ (x : Dfull) ∈ Lgrp := by
  rw [← rhoX_eq_one_iff]
  constructor
  · intro h
    refine LinearEquiv.ext fun v => ?_
    by_cases hv : v = 0
    · rw [hv, map_zero, map_zero]
    set c := objOfIso ⟨_, span_singleton_mem_isoSpaces hv⟩
    have hc := (smul_eq_self_iff x c.2).1 (h c.1 c.2)
    rw [a8Vec_objOfIso] at hc
    replace hc : (span (ZMod 2) {v}).map (rhoX x : V8 →ₗ[ZMod 2] V8) = span (ZMod 2) {v} := hc
    have hmem : rhoX x v ∈ span (ZMod 2) {v} := by
      rw [← hc]
      exact mem_map_of_mem (mem_span_singleton_self v)
    obtain ⟨a, ha⟩ := mem_span_singleton.1 hmem
    rcases zmod2_cases a with rfl | rfl
    · rw [zero_smul] at ha
      exact absurd ((rhoX x).map_eq_zero_iff.1 ha.symm) hv
    · rw [one_smul] at ha
      rw [← ha]
      rfl
  · intro h c hc
    rw [smul_eq_self_iff x hc, h]
    exact Submodule.map_id _

theorem mem_ker_toPermHom
    (x : Xgrp) :
    x ∈ (MulAction.toPermHom Xgrp subgeom).ker ↔ (x : Dfull) ∈ Lgrp := by
  rw [MonoidHom.mem_ker, ← subgeom_kernel_iff]
  constructor
  · intro h c hc
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨c, hc⟩)
  · intro h
    exact Equiv.ext fun c => Subtype.ext (h c.1 c.2)

theorem ker_toPermHom :
    (MulAction.toPermHom Xgrp subgeom).ker = rhoXSp.ker := by
  ext x
  rw [mem_ker_toPermHom, ker_rhoXSp, Subgroup.mem_subgroupOf]

theorem nonempty_range_toPermHom_equiv :
    Nonempty ((MulAction.toPermHom Xgrp subgeom).range ≃*
      CFSG.Assembly.LowTwoRank.StatedSp 4 (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_Sp_equiv
  exact ⟨(QuotientGroup.quotientKerEquivRange _).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ker_toPermHom).trans
      ((QuotientGroup.quotientKerEquivOfSurjective _ rhoXSp_surjective).trans e))⟩

theorem pair_one_mem
    {a : Dfull} (ha : a ∈ A8) (ha1 : a ≠ 1) :
    (1, Subgroup.zpowers a) ∈ subgeomPairs := by
  obtain ⟨h, hh, hha⟩ := Xgrp_transitive xhat_mem_A8_e0 ha TwoA.xhat_ne_one ha1
  refine ⟨le_rfl, by norm_num, h, hh, ?_⟩
  show Subgroup.zpowers a = conjSub h (Subgroup.zpowers xhat)
  rw [conjSub, MonoidHom.map_zpowers, ← hha]
  rfl

theorem pair_le_A8
    {p : ℕ × Subgroup Dfull} (hp : p ∈ subgeomPairs) : p.2 ≤ A8 :=
  obj_le_A8 (x := ⟨p, subgeomPairs_subset_ParObj hp⟩) hp

theorem Psi_toAdd_aEquiv_symm
    (x : A8) : Psi (Multiplicative.toAdd (aEquiv.symm x)) = x := by
  rw [← coe_aEquiv, MulEquiv.apply_symm_apply]

theorem mem_subgeomPairs_iff
    (p : ℕ × Subgroup Dfull) :
    p ∈ subgeomPairs ↔ 1 ≤ p.1 ∧ p.1 ≤ 4 ∧ p.2 ≤ A8 ∧ Nat.card p.2 = 2 ^ p.1 ∧
      ∀ x y : A8, (x : Dfull) ∈ p.2 → (y : Dfull) ∈ p.2 → bA x y = 0 := by
  constructor
  · intro hp
    have hc : (⟨p, subgeomPairs_subset_ParObj hp⟩ : ParGeom) ∈ subgeom := hp
    obtain ⟨hi, -⟩ := isotropic_obj hc
    refine ⟨hp.1, hp.2.1, obj_le_A8 hc, natCard_obj ⟨p, subgeomPairs_subset_ParObj hp⟩,
      fun x y hx hy => ?_⟩
    have hx' : Multiplicative.toAdd (aEquiv.symm x) ∈ a8Vec p.2 := by
      rw [mem_a8Vec, Psi_toAdd_aEquiv_symm]
      exact hx
    have hy' : Multiplicative.toAdd (aEquiv.symm y) ∈ a8Vec p.2 := by
      rw [mem_a8Vec, Psi_toAdd_aEquiv_symm]
      exact hy
    exact hi _ hx' _ hy'
  · rintro ⟨h1, h4, hA, hc, hiso⟩
    have hd := finrank_a8Vec hA hc
    have hW : a8Vec p.2 ∈ isoSpaces := by
      refine ⟨fun v hv w hw => ?_, by rw [hd]; exact h1, by rw [hd]; exact h4⟩
      have h := hiso (aEquiv (Multiplicative.ofAdd v)) (aEquiv (Multiplicative.ofAdd w))
        (by rw [coe_aEquiv]; exact hv) (by rw [coe_aEquiv]; exact hw)
      rwa [bA_aEquiv] at h
    have h := pair_mem_of_isoSpaces hW
    rwa [hd, a8Grp_a8Vec hA] at h

theorem stab_D_iff
    (d : Dfull) :
    (fun p : ℕ × Subgroup Dfull => (p.1, conjSub d p.2)) '' subgeomPairs = subgeomPairs ↔
      d ∈ Xgrp := by
  constructor
  · intro h
    rw [← normalizer_A8_eq]
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    by_cases ha1 : a = 1
    · rw [ha1, mul_one, mul_inv_cancel]
      exact A8.one_mem
    have hp : (1, conjSub d (Subgroup.zpowers a)) ∈ subgeomPairs := by
      rw [← h]
      exact ⟨_, pair_one_mem ha ha1, rfl⟩
    exact pair_le_A8 hp (conj_mem_conjSub (Subgroup.mem_zpowers a))
  · intro hd
    ext p
    constructor
    · rintro ⟨q, ⟨h1, h4, k, hk, e⟩, rfl⟩
      refine ⟨h1, h4, d * k, Xgrp.mul_mem hd hk, ?_⟩
      show conjSub d q.2 = conjSub (d * k) (Echain q.1)
      rw [e, conjSub_mul]
    · rintro ⟨h1, h4, k, hk, e⟩
      refine ⟨(p.1, conjSub d⁻¹ p.2), ⟨h1, h4, d⁻¹ * k, Xgrp.mul_mem (Xgrp.inv_mem hd) hk, ?_⟩, ?_⟩
      · show conjSub d⁻¹ p.2 = conjSub (d⁻¹ * k) (Echain p.1)
        rw [e, conjSub_mul]
      · show (p.1, conjSub d (conjSub d⁻¹ p.2)) = p
        rw [conjSub_conjSub_inv]

theorem stab_S_iff
    (s : Shat) : (s • ·) '' subgeom = subgeom ↔ (s : Dfull) ∈ Xgrp := by
  refine ⟨fun h => (stab_D_iff s).1 ?_, fun h => subgeomConj_of_mem h⟩
  rw [← image_val_subgeom, Set.image_image]
  conv_rhs => rw [← h]
  rw [Set.image_image]
  rfl

end CFSG.Monster.B.TwoA.Sp8
