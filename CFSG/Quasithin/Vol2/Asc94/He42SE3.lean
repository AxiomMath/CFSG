module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import Certificates.Certificate2022
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.Quasithin.A94.He42SE

open CFSG.ComponentClassification CFSG.ComponentClassification.AS81

private abbrev he42s3_x0 : ↥PSL3Four.S := ⟨PSL3Four.r₁, PSL3Four.r₁_mem_S⟩

private abbrev he42s3_toR (x : ↥PSL3Four.S) : ↥PSL3Four.R :=
  ⟨(x : Equiv.Perm (Fin 42)), PSL3Four.S_le_R x.2⟩

private theorem he42s3_card_centralizer :
    Nat.card (Subgroup.centralizer ({he42s3_x0} : Set ↥PSL3Four.S)) = 64 := by
  have hmap : (Subgroup.centralizer ({he42s3_x0} : Set ↥PSL3Four.S)).map PSL3Four.S.subtype =
      PSL3Four.C₁ := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hp
      rw [Subgroup.mem_centralizer_singleton_iff] at hq
      have hq' : (q : Equiv.Perm (Fin 42)) * PSL3Four.r₁ = PSL3Four.r₁ * (q : Equiv.Perm (Fin 42)) :=
        congrArg Subtype.val hq
      rw [PSL3Four.C₁, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      exact ⟨hq', q.2⟩
    · intro hp
      rw [PSL3Four.C₁, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hp
      rw [Subgroup.mem_map]
      refine ⟨⟨p, hp.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hp.1
  have h := Subgroup.card_map_of_injective
    (K := Subgroup.centralizer ({he42s3_x0} : Set ↥PSL3Four.S))
    (f := PSL3Four.S.subtype) Subtype.coe_injective
  rw [hmap, PSL3Four.card_C₁] at h
  exact h.symm

private theorem he42s3_ncard_conjugates :
    (conjugatesOf he42s3_x0).ncard = 315 := by
  have h1 := Subgroup.index_centralizer_eq_ncard he42s3_x0
  have h2 := Subgroup.card_mul_index (Subgroup.centralizer ({he42s3_x0} : Set ↥PSL3Four.S))
  rw [he42s3_card_centralizer, PSL3Four.card_S, h1] at h2
  omega

private theorem he42s3_ncard_R_class :
    (Subtype.val '' (ConjClasses.mk PSL3Four.r₁R).carrier :
      Set (Equiv.Perm (Fin 42))).ncard = 315 := by
  rw [Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
  exact PSL3Four.conjClass₁.2

private theorem he42s3_subset :
    Subtype.val '' conjugatesOf he42s3_x0 ⊆
      Subtype.val '' (ConjClasses.mk PSL3Four.r₁R).carrier := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : IsConj he42s3_x0 y := hy
  obtain ⟨c, hc⟩ := isConj_iff.1 hy'
  refine ⟨he42s3_toR y, ?_, rfl⟩
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm, isConj_iff]
  refine ⟨he42s3_toR c, Subtype.ext ?_⟩
  have hc' := congrArg Subtype.val hc
  exact hc'

private theorem he42s3_eq :
    Subtype.val '' conjugatesOf he42s3_x0 =
      Subtype.val '' (ConjClasses.mk PSL3Four.r₁R).carrier :=
  Set.eq_of_subset_of_ncard_le he42s3_subset
    (le_of_eq (by
      rw [he42s3_ncard_R_class, Set.ncard_image_of_injective _ Subtype.val_injective,
        he42s3_ncard_conjugates])) (Set.toFinite _)

private theorem he42s3_isConj_x0 (x : ↥PSL3Four.S)
    (hx : orderOf x = 2) : IsConj he42s3_x0 x := by
  have h1 : orderOf (he42s3_toR x) = orderOf (x : Equiv.Perm (Fin 42)) :=
    Subgroup.orderOf_mk (x : Equiv.Perm (Fin 42)) (PSL3Four.S_le_R x.2)
  have h2 : orderOf (x : Equiv.Perm (Fin 42)) = orderOf x := Subgroup.orderOf_coe x
  have hR : orderOf (he42s3_toR x) = 2 := h1.trans (h2.trans hx)
  rcases (PSL3Four.orderOf_eq_two_iff (he42s3_toR x)).1 hR with h | h | h | h
  · have hmem : (x : Equiv.Perm (Fin 42)) ∈
        Subtype.val '' (ConjClasses.mk PSL3Four.r₁R).carrier :=
      ⟨he42s3_toR x, ConjClasses.mem_carrier_iff_mk_eq.2 (ConjClasses.mk_eq_mk_iff_isConj.2 h),
        rfl⟩
    rw [← he42s3_eq] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  · exact absurd x.2 (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₂)
  · exact absurd x.2 (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₃)
  · exact absurd x.2 (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₄)

private theorem he42s3_isConj_S (x y : ↥PSL3Four.S)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  (he42s3_isConj_x0 x hx).symm.trans (he42s3_isConj_x0 y hy)

private theorem he42s3_isSimpleGroup_S :
    IsSimpleGroup ↥PSL3Four.S := by
  have hs := (CFSG.LinearGroups.linear_projective_simple (K := PSL3Four.F4) (n := 3)
    (by norm_num) (Or.inl (by norm_num))).2.1
  exact (PSL3Four.theta.symm.trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
      PSL3Four.F4).symm).isSimpleGroup

theorem typeL34_isSimpleGroup {Y : Type} [Group Y]
    (hY : TypeL34 Y) : IsSimpleGroup Y := by
  obtain ⟨e⟩ := PSL3Four.nonempty_equiv_of_stated Y hY
  have hS := he42s3_isSimpleGroup_S
  exact e.isSimpleGroup

theorem typeL34_isConj {Y : Type} [Group Y] (hY : TypeL34 Y)
    {a b : Y} (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨e⟩ := PSL3Four.nonempty_equiv_of_stated Y hY
  have ha' : orderOf (e a) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ha
  have hb' : orderOf (e b) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hb
  have h := MonoidHom.map_isConj e.symm.toMonoidHom (he42s3_isConj_S (e a) (e b) ha' hb')
  simpa using h

theorem typeL34_card {Y : Type} [Group Y] (hY : TypeL34 Y) :
    Nat.card Y = 20160 := by
  obtain ⟨e⟩ := PSL3Four.nonempty_equiv_of_stated Y hY
  rw [Nat.card_congr e.toEquiv, PSL3Four.card_S]

end CFSG.Quasithin.A94.He42SE
