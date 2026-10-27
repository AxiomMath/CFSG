module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphPoints
public import CFSG.Monster.B.TwoA.Amalgam.CentralExt
public import CFSG.Monster.B.TwoA.Sp8.Par1Center
public import CFSG.Monster.B.E6.StdF4Points
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate3063
public import Certificates.Certificate16040
public import Certificates.Certificate16951
public import CFSG.LieType.Chevalley.C2E6MinusSixStabilizer
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.Monster.B.Geometry.GlobalExtension
public import CFSG.Monster.B.Geometry.UnitaryResidue

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Monster.B.TwoA.Sp8

@[expose] def xhatEam :
    Eam := ⟨xhat, Pc_le_Eam 0 xhat_mem_P1⟩

theorem coe_xhatEam :
    ((xhatEam : Eam) : Dfull) = xhat := rfl

theorem mem_zpowers_subtype_iff {G : Type*} [Group G] {H : Subgroup G} (c x : H) :
    x ∈ Subgroup.zpowers c ↔ (x : G) ∈ Subgroup.zpowers (c : G) := by
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk⟩

theorem mk_eq_mk_iff_P1
    (a b : P1) :
    (QuotientGroup.mk a : P1 ⧸ Subgroup.zpowers cP1) = QuotientGroup.mk b ↔
      (QuotientGroup.mk ⟨a, Pc_le_Eam 0 a.2⟩ : Eam ⧸ Subgroup.zpowers cE') =
        QuotientGroup.mk ⟨b, Pc_le_Eam 0 b.2⟩ := by
  rw [QuotientGroup.eq, QuotientGroup.eq, mem_zpowers_subtype_iff, mem_zpowers_subtype_iff]
  rfl

theorem mk_mem_center_P1_quot
    {e : Eam} (he : (e : Dfull) ∈ P1)
    (h : ∀ p : Eam, (p : Dfull) ∈ Pc 0 →
      Commute (QuotientGroup.mk p : Eam ⧸ Subgroup.zpowers cE') (QuotientGroup.mk e)) :
    (QuotientGroup.mk ⟨e, he⟩ : P1 ⧸ Subgroup.zpowers cP1) ∈
      Subgroup.center (P1 ⧸ Subgroup.zpowers cP1) :=
  Subgroup.mem_center_iff.mpr fun p' => QuotientGroup.induction_on p' fun p =>
    (mk_eq_mk_iff_P1 (p * (⟨e, he⟩ : P1)) ((⟨e, he⟩ : P1) * p)).mpr (h ⟨p, Pc_le_Eam 0 p.2⟩ p.2).eq

theorem eq_mk_xP1_of_mem_center
    {q : P1 ⧸ Subgroup.zpowers cP1}
    (hq : q ∈ Subgroup.center (P1 ⧸ Subgroup.zpowers cP1)) (hq1 : q ≠ 1) :
    q = QuotientGroup.mk xP1 := by
  rw [center_P1_quot, Subgroup.mem_zpowers_iff] at hq
  obtain ⟨k, rfl⟩ := hq
  rw [← zpow_mod_orderOf, orderOf_mk_xP1] at hq1 ⊢
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · rw [Nat.cast_ofNat, hk, zpow_zero] at hq1
    exact absurd rfl hq1
  · rw [Nat.cast_ofNat, hk, zpow_one]

theorem image_residue_eq_of_adj_iff
    {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W]
    {cs : CoxeterSystem M W} {C D : Type*} {X : ChamberSystem ι C} {δ : D → D → W}
    (hδ : IsWeylDistanceBuilding cs δ) (f : C ≃ D)
    (hf : ∀ i x y, X.adj i x y ↔ δ (f x) (f y) = 1 ∨ δ (f x) (f y) = cs.simple i)
    (J : Set ι) (z : C) : f '' X.residue J z = residue cs δ J (f z) := by
  ext y
  obtain ⟨x, rfl⟩ := f.surjective y
  rw [f.injective.mem_set_image]
  constructor
  · rintro ⟨γ, hγ, hJ, rfl⟩
    induction γ generalizing z with
    | nil => exact Relation.ReflTransGen.refl
    | cons p γ ih =>
      obtain ⟨h1, h2⟩ := hγ
      have hrest := ih p.2 h2 fun i hi => hJ i (by simp [galleryType] at hi ⊢; tauto)
      rw [galleryEnd_cons]
      rcases (hf p.1 z p.2).mp h1 with h | h
      · rw [(hδ.eq_one_iff _ _).mp h]
        exact hrest
      · exact Relation.ReflTransGen.head ⟨p.1, hJ p.1 (by simp [galleryType]), h⟩ hrest
  · intro h
    suffices key : ∀ y, y ∈ residue cs δ J (f z) → f.symm y ∈ X.residue J z by
      simpa using key _ h
    intro y hy
    induction hy with
    | refl => simpa using X.self_mem_residue J z
    | @tail b c _ hbc ih =>
      obtain ⟨i, hi, he⟩ := hbc
      refine ChamberSystem.mem_residue_trans ih (X.residue_mono
        (Set.singleton_subset_iff.mpr hi) _ (ChamberSystem.mem_residue_singleton.mpr ?_))
      rw [hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact Or.inr he

theorem exists_inter_nonempty_image_iff {C D : Type*} (f : C ≃ D) {V : C → Set C}
    {W : D → Set D} (hVW : ∀ x, f '' V x = W (f x)) (A A' : Set C) :
    (∃ x, (A ∩ V x).Nonempty ∧ (A' ∩ V x).Nonempty) ↔
      ∃ S ∈ Set.range W, (f '' A ∩ S).Nonempty ∧ (f '' A' ∩ S).Nonempty := by
  constructor
  · rintro ⟨x, h1, h2⟩
    refine ⟨_, ⟨f x, rfl⟩, ?_, ?_⟩
    · rw [← hVW x, ← Set.image_inter f.injective]
      exact h1.image f
    · rw [← hVW x, ← Set.image_inter f.injective]
      exact h2.image f
  · rintro ⟨_, ⟨y, rfl⟩, h1, h2⟩
    obtain ⟨x, rfl⟩ := f.surjective y
    rw [← hVW x, ← Set.image_inter f.injective, Set.image_nonempty] at h1 h2
    exact ⟨x, h1, h2⟩

theorem preimage_compl_zero :
    nativeIdx ⁻¹' {j : Fin Tag.F4.rank | j ≠ (0 : Fin 4)} = firstJ := by
  rw [firstJ_eq]
  exact Set.ext fun _ => Iff.rfl

theorem preimage_compl_three :
    nativeIdx ⁻¹' {j : Fin Tag.F4.rank | j ≠ (3 : Fin 4)} = FourthResidue.fourthJ := by
  rw [fourthJ_eq]
  exact Set.ext fun _ => Iff.rfl

@[expose] def stdBaseVertex :
    typeOneVertex := ⟨residue ncs stdDistance firstJ c₀, c₀, rfl⟩

theorem coe_stdBaseVertex :
    (stdBaseVertex : Set C2E6Std.stdChamber) = residue ncs stdDistance firstJ c₀ := rfl

theorem inl_vertexRoot_stdBaseVertex :
    SemidirectProduct.inl (vertexRoot stdBaseVertex) = rootStar := by
  have h : vertexRoot stdBaseVertex = 1 * rootInv * 1⁻¹ := vertexRoot_mk (1 : stdGroup)
  rw [h, one_mul rootInv, inv_one, mul_one rootInv]
  rfl

section Based

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {f : Chamber ≃ C2E6Std.stdChamber}

theorem image_residue_chamberCS_of_adj
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (L : Set (Fin Tag.F4.rank)) (z : Chamber) :
    f '' chamberCS.residue L z = residue ncs stdDistance (nativeIdx ⁻¹' L) (f z) :=
  (image_residue_eq_of_adj_iff isWeylDistanceBuilding_stdDistanceF4 f hadj L z).trans
    (residue_stdDistanceF4 L (f z))

theorem image_vtx_zero_of_adj
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (z : Chamber) : f '' vtx 0 z = residue ncs stdDistance firstJ (f z) :=
  (image_residue_chamberCS_of_adj hadj _ z).trans
    (congrArg (fun L => residue ncs stdDistance L (f z)) preimage_compl_zero)

theorem image_vtx_three_of_adj
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (z : Chamber) : f '' vtx 3 z = residue ncs stdDistance FourthResidue.fourthJ (f z) :=
  (image_residue_chamberCS_of_adj hadj _ z).trans
    (congrArg (fun L => residue ncs stdDistance L (f z)) preimage_compl_three)

theorem vertexSmul_stdBaseVertex_eq
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
    (hfB : f baseChamber = c₀) (e : Eam) :
    (vertexSmul (θ (QuotientGroup.mk e)) stdBaseVertex : Set C2E6Std.stdChamber) =
      f '' vtx 0 (chamberOf e⁻¹) := by
  have h1 : chamberOf e⁻¹ = chamberMul baseChamber e⁻¹ := by
    rw [chamberMul_chamberOf, one_mul e⁻¹]
  have h2 : f (chamberOf e⁻¹) = θ (QuotientGroup.mk e) • c₀ :=
    ((congrArg f h1).trans (hfeq baseChamber e)).trans
      (congrArg (θ (QuotientGroup.mk e) • ·) hfB)
  exact (image_smul_residue (θ (QuotientGroup.mk e)) firstJ c₀).trans
    ((congrArg (residue ncs stdDistance firstJ) h2).symm.trans
      (image_vtx_zero_of_adj hadj (chamberOf e⁻¹)).symm)

theorem vertexSmul_inv_stdBaseVertex_eq
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
    (hfB : f baseChamber = c₀) (e : Eam) :
    (vertexSmul (θ (QuotientGroup.mk e⁻¹)) stdBaseVertex : Set C2E6Std.stdChamber) =
      f '' vtx 0 (chamberOf e) := by
  have h := vertexSmul_stdBaseVertex_eq hadj hfeq hfB e⁻¹
  rwa [inv_inv e] at h

theorem mem_Pc_zero_iff_of_quotient
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
    (hfB : f baseChamber = c₀) (e : Eam) :
    (e : Dfull) ∈ Pc 0 ↔ θ (QuotientGroup.mk e) ∈ Subgroup.centralizer {rootStar} := by
  have hv := vertexSmul_stdBaseVertex_eq hadj hfeq hfB e
  have hB : f '' vtx 0 baseChamber = (stdBaseVertex : Set C2E6Std.stdChamber) :=
    (image_vtx_zero_of_adj hadj baseChamber).trans (by rw [hfB, coe_stdBaseVertex])
  have hve : vtx 0 (chamberOf e⁻¹) = vtx 0 baseChamber ↔ (e : Dfull) ∈ Pc 0 := by
    rw [vtx_eq_iff 0 e⁻¹ 1, one_mul e⁻¹⁻¹, inv_inv e]
  rw [← inl_vertexRoot_stdBaseVertex, ← vertexSmul_eq_iff (θ (QuotientGroup.mk e)) stdBaseVertex,
    Subtype.ext_iff, hv, ← hB, (Set.image_injective.mpr f.injective).eq_iff, hve]

theorem map_mk_xhatEam_of_quotient
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
    (hfB : f baseChamber = c₀) : θ (QuotientGroup.mk xhatEam) = rootStar := by
  have hstab := mem_Pc_zero_iff_of_quotient hadj hfeq hfB
  obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (θ.symm rootStar)
  have hθe : θ (QuotientGroup.mk e) = rootStar :=
    (congrArg θ he).trans (θ.apply_symm_apply rootStar)
  have hc : ∀ p : Eam, Commute (θ (QuotientGroup.mk p)) (θ (QuotientGroup.mk e)) ↔
      θ (QuotientGroup.mk p) ∈ Subgroup.centralizer {rootStar} := fun p =>
    (iff_of_eq (congrArg (Commute (θ (QuotientGroup.mk p))) hθe)).trans
      Subgroup.mem_centralizer_singleton_iff.symm
  have he₁ : (e : Dfull) ∈ P1 := (hstab e).mpr ((hc e).mp (Commute.refl _))
  have hcen := mk_mem_center_P1_quot he₁ fun p hp =>
    Commute.of_map θ.injective ((hc p).mpr ((hstab p).mp hp))
  have hne : (QuotientGroup.mk ⟨e, he₁⟩ : P1 ⧸ Subgroup.zpowers cP1) ≠ 1 := fun h1 => by
    have h : (QuotientGroup.mk e : Eam ⧸ Subgroup.zpowers cE') = 1 :=
      (mk_eq_mk_iff_P1 ⟨e, he₁⟩ 1).mp h1
    exact rootInv_ne_one (inl_injective ((hθe.symm.trans ((congrArg θ h).trans (map_one θ))).trans
      (map_one SemidirectProduct.inl).symm))
  have hx := (mk_eq_mk_iff_P1 _ _).mp (eq_mk_xP1_of_mem_center hcen hne)
  exact (congrArg θ hx.symm).trans hθe

theorem inl_vertexRoot_vertexSmul_inv_of_quotient
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
    (hfB : f baseChamber = c₀) (e : Eam) :
    SemidirectProduct.inl (vertexRoot (vertexSmul (θ (QuotientGroup.mk e⁻¹)) stdBaseVertex)) =
      θ (QuotientGroup.mk (e⁻¹ * xhatEam * e)) := by
  have hx := map_mk_xhatEam_of_quotient hadj hfeq hfB
  have hq : (QuotientGroup.mk e⁻¹ * QuotientGroup.mk xhatEam * (QuotientGroup.mk e⁻¹)⁻¹ :
      Eam ⧸ Subgroup.zpowers cE') = QuotientGroup.mk (e⁻¹ * xhatEam * e) :=
    congrArg (fun x => (QuotientGroup.mk (e⁻¹ * xhatEam * x) : Eam ⧸ Subgroup.zpowers cE'))
      (inv_inv e)
  calc SemidirectProduct.inl (vertexRoot (vertexSmul (θ (QuotientGroup.mk e⁻¹)) stdBaseVertex))
        = θ (QuotientGroup.mk e⁻¹) * SemidirectProduct.inl (vertexRoot stdBaseVertex) *
            (θ (QuotientGroup.mk e⁻¹))⁻¹ := vertexRoot_vertexSmul _ _
    _ = θ (QuotientGroup.mk e⁻¹) * θ (QuotientGroup.mk xhatEam) *
          (θ (QuotientGroup.mk e⁻¹))⁻¹ :=
        congrArg (fun t => θ (QuotientGroup.mk e⁻¹) * t * (θ (QuotientGroup.mk e⁻¹))⁻¹)
          (inl_vertexRoot_stdBaseVertex.trans hx.symm)
    _ = θ (QuotientGroup.mk e⁻¹ * QuotientGroup.mk xhatEam * (QuotientGroup.mk e⁻¹)⁻¹) :=
        ((map_mul θ (QuotientGroup.mk e⁻¹ * QuotientGroup.mk xhatEam)
          (QuotientGroup.mk e⁻¹)⁻¹).trans
          (congrArg₂ (· * ·) (map_mul θ (QuotientGroup.mk e⁻¹) (QuotientGroup.mk xhatEam))
            (map_inv θ (QuotientGroup.mk e⁻¹)))).symm
    _ = θ (QuotientGroup.mk (e⁻¹ * xhatEam * e)) := congrArg θ hq

theorem vtx_zero_eq_iff_of_quotient
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
    (hfB : f baseChamber = c₀) (e e' : Eam) :
    vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
      (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
        QuotientGroup.mk (e'⁻¹ * xhatEam * e') := by
  have h1 := vertexSmul_inv_stdBaseVertex_eq hadj hfeq hfB e
  have h2 := vertexSmul_inv_stdBaseVertex_eq hadj hfeq hfB e'
  have h3 := inl_vertexRoot_vertexSmul_inv_of_quotient hadj hfeq hfB e
  have h4 := inl_vertexRoot_vertexSmul_inv_of_quotient hadj hfeq hfB e'
  exact (Set.image_injective.mpr f.injective).eq_iff.symm.trans
    ((iff_of_eq (congrArg₂ (· = ·) h1.symm h2.symm)).trans
      (Subtype.ext_iff.symm.trans (vertexRoot_injective.eq_iff.symm.trans
        (inl_injective.eq_iff.symm.trans ((iff_of_eq (congrArg₂ (· = ·) h3 h4)).trans
          θ.injective.eq_iff)))))

theorem exists_vtx_three_iff_commute_of_quotient
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
    (hfB : f baseChamber = c₀) (e e' : Eam) :
    (∃ x, (vtx 0 (chamberOf e) ∩ vtx 3 x).Nonempty ∧ (vtx 0 (chamberOf e') ∩ vtx 3 x).Nonempty) ↔
      Commute (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE')
        (QuotientGroup.mk (e'⁻¹ * xhatEam * e')) := by
  have h1 := vertexSmul_inv_stdBaseVertex_eq hadj hfeq hfB e
  have h2 := vertexSmul_inv_stdBaseVertex_eq hadj hfeq hfB e'
  have h3 := inl_vertexRoot_vertexSmul_inv_of_quotient hadj hfeq hfB e
  have h4 := inl_vertexRoot_vertexSmul_inv_of_quotient hadj hfeq hfB e'
  have hcomm : ∀ a b : stdGroup, Commute a b ↔
      Commute (SemidirectProduct.inl a : GStar) (SemidirectProduct.inl b) := fun a b =>
    ⟨fun h => h.map SemidirectProduct.inl, Commute.of_map inl_injective⟩
  exact (exists_inter_nonempty_image_iff f (image_vtx_three_of_adj hadj) _ _).trans
    ((iff_of_eq (congrArg₂ (fun A A' => ∃ S ∈ typeFourVertex, (A ∩ S).Nonempty ∧
        (A' ∩ S).Nonempty) h1.symm h2.symm)).trans
      ((exists_typeFour_iff_commute _ _).trans ((hcomm _ _).trans
        ((iff_of_eq (congrArg₂ Commute h3 h4)).trans
          ⟨Commute.of_map θ.injective, fun h => h.map θ⟩))))

end Based

theorem exists_normalized_quotient
    (θ₁ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar)
    (f₁ : Chamber ≃ C2E6Std.stdChamber)
    (h1 : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f₁ x) (f₁ y) = 1 ∨ stdDistanceF4 (f₁ x) (f₁ y) = (coxeterSystem .F4).simple i)
    (h2 : ∀ δ : Chamber → Chamber → WeylGroup .F4, IsWeylDistanceBuilding (coxeterSystem .F4) δ →
      (∀ (i : Fin Tag.F4.rank) (x y : Chamber),
        chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i) →
      ∀ x y, stdDistanceF4 (f₁ x) (f₁ y) = δ x y)
    (h3 : ∀ (z : Chamber) (e : Eam), f₁ (chamberMul z e⁻¹) = θ₁ (QuotientGroup.mk e) • f₁ z) :
    ∃ (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) (f : Chamber ≃ C2E6Std.stdChamber),
      (∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
        stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i) ∧
      (∀ δ : Chamber → Chamber → WeylGroup .F4, IsWeylDistanceBuilding (coxeterSystem .F4) δ →
        (∀ (i : Fin Tag.F4.rank) (x y : Chamber),
          chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i) →
        ∀ x y, stdDistanceF4 (f x) (f y) = δ x y) ∧
      (∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z) ∧
      f baseChamber = c₀ := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (f₁ baseChamber)
  have hγ : ∃ γ₀ : GStar, γ₀ = SemidirectProduct.inl g := ⟨_, rfl⟩
  obtain ⟨γ₀, hγ₀⟩ := hγ
  have hF : ∃ f : Chamber ≃ C2E6Std.stdChamber, ∀ z, f z = γ₀⁻¹ • f₁ z :=
    ⟨f₁.trans (MulAction.toPerm γ₀⁻¹), fun _ => rfl⟩
  obtain ⟨f, hf⟩ := hF
  have hΘ : ∃ θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar, ∀ q, θ q = γ₀⁻¹ * θ₁ q * γ₀ :=
    ⟨θ₁.trans (MulAut.conj γ₀⁻¹), fun q =>
      (MulEquiv.trans_apply θ₁ (MulAut.conj γ₀⁻¹) q).trans
        ((MulAut.conj_apply γ₀⁻¹ (θ₁ q)).trans (congrArg (γ₀⁻¹ * θ₁ q * ·) (inv_inv γ₀)))⟩
  obtain ⟨θ, hθ⟩ := hΘ
  have hfd : ∀ x y, stdDistanceF4 (f x) (f y) = stdDistanceF4 (f₁ x) (f₁ y) := fun x y => by
    rw [hf x, hf y]
    exact congrArg nativeWeylEquiv (stdDistance_smul γ₀⁻¹ (f₁ x) (f₁ y))
  refine ⟨θ, f, fun i x y => by rw [hfd x y]; exact h1 i x y,
    fun δ hδ hadj x y => (hfd x y).trans (h2 δ hδ hadj x y), fun z e => ?_, ?_⟩
  · calc f (chamberMul z e⁻¹) = γ₀⁻¹ • θ₁ (QuotientGroup.mk e) • f₁ z :=
          (hf (chamberMul z e⁻¹)).trans (congrArg (γ₀⁻¹ • ·) (h3 z e))
      _ = (γ₀⁻¹ * θ₁ (QuotientGroup.mk e)) • f₁ z := smul_smul _ _ _
      _ = (γ₀⁻¹ * θ₁ (QuotientGroup.mk e) * γ₀ * γ₀⁻¹) • f₁ z :=
          congrArg (· • f₁ z) (mul_inv_cancel_right _ γ₀).symm
      _ = (γ₀⁻¹ * θ₁ (QuotientGroup.mk e) * γ₀) • γ₀⁻¹ • f₁ z := (smul_smul _ _ _).symm
      _ = θ (QuotientGroup.mk e) • f z :=
          congrArg₂ (· • ·) (hθ (QuotientGroup.mk e)).symm (hf z).symm
  · rw [hf baseChamber, ← hg, hγ₀, ← map_inv SemidirectProduct.inl g, smul_mk]
    change ((g⁻¹ * (1 : MulAut stdGroup) g : stdGroup) : C2E6Std.stdChamber) = c₀
    rw [MulAut.one_apply, inv_mul_cancel g]

theorem point_root_of_quotient
    (θ₁ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar)
    (f₁ : Chamber ≃ C2E6Std.stdChamber)
    (h1 : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f₁ x) (f₁ y) = 1 ∨ stdDistanceF4 (f₁ x) (f₁ y) = (coxeterSystem .F4).simple i)
    (h2 : ∀ δ : Chamber → Chamber → WeylGroup .F4, IsWeylDistanceBuilding (coxeterSystem .F4) δ →
      (∀ (i : Fin Tag.F4.rank) (x y : Chamber),
        chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i) →
      ∀ x y, stdDistanceF4 (f₁ x) (f₁ y) = δ x y)
    (h3 : ∀ (z : Chamber) (e : Eam), f₁ (chamberMul z e⁻¹) = θ₁ (QuotientGroup.mk e) • f₁ z) :
    ∃ (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) (f : Chamber ≃ C2E6Std.stdChamber),
      (∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
        stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i) ∧
      (∀ δ : Chamber → Chamber → WeylGroup .F4, IsWeylDistanceBuilding (coxeterSystem .F4) δ →
        (∀ (i : Fin Tag.F4.rank) (x y : Chamber),
          chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i) →
        ∀ x y, stdDistanceF4 (f x) (f y) = δ x y) ∧
      (∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z) ∧
      f '' vtx 0 baseChamber = residue ncs stdDistance firstJ c₀ ∧
      θ (QuotientGroup.mk xhatEam) = rootStar ∧
      (∀ e : Eam, ∃ R : typeOneVertex, (R : Set C2E6Std.stdChamber) = f '' vtx 0 (chamberOf e) ∧
        SemidirectProduct.inl (vertexRoot R) = θ (QuotientGroup.mk (e⁻¹ * xhatEam * e))) ∧
      (∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
        (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
          QuotientGroup.mk (e'⁻¹ * xhatEam * e')) ∧
      ∀ e e' : Eam,
        ((∃ x, (vtx 0 (chamberOf e) ∩ vtx 3 x).Nonempty ∧
            (vtx 0 (chamberOf e') ∩ vtx 3 x).Nonempty) ↔
          Commute (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE')
            (QuotientGroup.mk (e'⁻¹ * xhatEam * e'))) := by
  obtain ⟨θ, f, hadj, hδ, hfeq, hfB⟩ := exists_normalized_quotient θ₁ f₁ h1 h2 h3
  exact ⟨θ, f, hadj, hδ, hfeq,
    (image_vtx_zero_of_adj hadj baseChamber).trans (congrArg (residue ncs stdDistance firstJ) hfB),
    map_mk_xhatEam_of_quotient hadj hfeq hfB,
    fun e => ⟨_, vertexSmul_inv_stdBaseVertex_eq hadj hfeq hfB e,
      inl_vertexRoot_vertexSmul_inv_of_quotient hadj hfeq hfB e⟩,
    vtx_zero_eq_iff_of_quotient hadj hfeq hfB,
    exists_vtx_three_iff_commute_of_quotient hadj hfeq hfB⟩

end CFSG.Monster.B.TwoA.Amalgam
