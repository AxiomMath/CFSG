module

public import CFSG.LocalAnalysis.ZStar.BrauerPrincipal
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockKernel

public section

namespace CFSG

namespace ZStar.ModularBrauerQuotient

open ZStar.BrauerPrincipal
open ZStar.BrauerProjection
open ZStar.Helpers
open ZStar.PrincipalBlockKernel

noncomputable section

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

@[expose] def involutionDifference
    (ρ : Representation (ZMod 2) G V) (w : G) : Module.End (ZMod 2) V :=
  ρ w - 1

@[expose] def brauerKernel (ρ : Representation (ZMod 2) G V) (w : G) :
    Submodule (ZMod 2) V :=
  (involutionDifference ρ w).ker

private theorem mem_brauerKernel_iff
    (ρ : Representation (ZMod 2) G V) (w : G) (x : V) :
    x ∈ brauerKernel ρ w ↔ ρ w x = x := by
  change ρ w x - x = 0 ↔ ρ w x = x
  exact sub_eq_zero

private theorem brauerKernel_fixed
    (ρ : Representation (ZMod 2) G V) (w : G)
    (x : brauerKernel ρ w) :
    ρ w (x : V) = (x : V) :=
  (mem_brauerKernel_iff ρ w (x : V)).mp x.property

@[expose] def brauerRangeInKernel (ρ : Representation (ZMod 2) G V) (w : G) :
    Submodule (ZMod 2) (brauerKernel ρ w) :=
  (involutionDifference ρ w).range.comap (brauerKernel ρ w).subtype

abbrev BrauerQuotient (ρ : Representation (ZMod 2) G V) (w : G) :=
  (brauerKernel ρ w) ⧸ brauerRangeInKernel ρ w

private theorem add_self_eq_zero (x : V) : x + x = 0 := by
  calc
    x + x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by simp only [one_smul]
    _ = ((1 : ZMod 2) + 1) • x := by rw [add_smul]
    _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]

private theorem neg_eq_self (x : V) : -x = x := by
  exact neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero x)

private theorem sum_eq_sum_centralizer_of_conjInvariant_module
    {M : Type w} [AddCommGroup M] [Module (ZMod 2) M]
    (w : G) (hw2 : w * w = 1) (F : G → M)
    (hF : ∀ g : G, F (w * g * w⁻¹) = F g) :
    (∑ g : G, F g) =
      ∑ h : involutionCentralizer w, F (h : G) := by
  classical
  let H : Subgroup G := involutionCentralizer w
  let c : G → G := fun g ↦ w * g * w⁻¹
  have hwinv : w⁻¹ = w := (inv_eq_iff_mul_eq_one).2 hw2
  have hout :
      (∑ g ∈ (Finset.univ.filter fun g : G ↦ g ∉ H), F g) = 0 := by
    have hsum := Finset.sum_involution
      (s := Finset.univ.filter fun g : G ↦ g ∉ H)
      (f := F)
      (fun g _ ↦ c g)
      (by
        intro g hg
        change F g + F (w * g * w⁻¹) = 0
        rw [hF]
        exact add_self_eq_zero _)
      (by
        intro g hg _ hfix
        have hgnot : g ∉ H := (Finset.mem_filter.mp hg).2
        apply hgnot
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hfix' := congrArg (fun z : G ↦ z * w) hfix
        dsimp only [c] at hfix'
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hfix'.symm)
      (by
        intro g hg
        rw [Finset.mem_filter] at hg ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hcg
        apply hg.2
        rw [Subgroup.mem_centralizer_singleton_iff] at hcg ⊢
        dsimp only [c] at hcg
        rw [hwinv] at hcg
        calc
          g * w = (w * w) * g * w := by rw [hw2, one_mul]
          _ = w * (w * g * w) := by group
          _ = (w * g * w) * w := hcg.symm
          _ = w * g * (w * w) := by group
          _ = w * g := by rw [hw2, mul_one])
      (by
        intro g hg
        dsimp only [c]
        rw [hwinv]
        calc
          w * (w * g * w) * w = (w * w) * g * (w * w) := by group
          _ = g := by rw [hw2, one_mul, mul_one])
    exact hsum
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset G) (fun g : G ↦ g ∈ H) F
  have hsubtype :
      (∑ g ∈ (Finset.univ.filter fun g : G ↦ g ∈ H), F g) =
        ∑ h : H, F (h : G) :=
    Finset.sum_subtype _ (by simp) F
  change (∑ g : G, F g) = ∑ h : H, F (h : G)
  calc
    (∑ g : G, F g) =
        (∑ g ∈ (Finset.univ.filter fun g : G ↦ g ∈ H), F g) +
        (∑ g ∈ (Finset.univ.filter fun g : G ↦ g ∉ H), F g) :=
      hpartition.symm
    _ = ∑ g ∈ (Finset.univ.filter fun g : G ↦ g ∈ H), F g := by
      rw [hout, add_zero]
    _ = ∑ h : H, F (h : G) := hsubtype

private theorem representation_asAlgebraHom_eq_sum
    (ρ : Representation (ZMod 2) G V) (a : GroupAlgebraTwo G) :
    ρ.asAlgebraHom a = ∑ g : G, a.coeff g • ρ g := by
  classical
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  apply Finsupp.sum_fintype
  intro g
  exact zero_smul (ZMod 2) (ρ g)

private theorem representation_asAlgebraHom_apply_eq_sum
    (ρ : Representation (ZMod 2) G V) (a : GroupAlgebraTwo G) (x : V) :
    ρ.asAlgebraHom a x = ∑ g : G, a.coeff g • ρ g x := by
  have h := congrArg (fun f : Module.End (ZMod 2) V ↦ f x)
    (representation_asAlgebraHom_eq_sum ρ a)
  simpa using h

theorem centralAlgebraAction_mem_brauerKernel
    (ρ : Representation (ZMod 2) G V) (w : G)
    (a : GroupAlgebraTwo G) (ha : IsGroupCentral G a)
    (x : brauerKernel ρ w) :
    ρ.asAlgebraHom a (x : V) ∈ brauerKernel ρ w := by
  rw [mem_brauerKernel_iff]
  have hmap := congrArg ρ.asAlgebraHom (ha w)
  have hcomm :
      ρ w * ρ.asAlgebraHom a = ρ.asAlgebraHom a * ρ w := by
    simpa only [map_mul, Representation.asAlgebraHom_single_one] using hmap
  have happ := congrArg
    (fun f : Module.End (ZMod 2) V ↦ f (x : V)) hcomm
  change ρ w (ρ.asAlgebraHom a (x : V)) =
    ρ.asAlgebraHom a (ρ w (x : V)) at happ
  rw [brauerKernel_fixed] at happ
  exact happ

private theorem involutionDifference_sq_eq_zero
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1) :
    involutionDifference ρ w * involutionDifference ρ w = 0 := by
  ext x
  have hρ2 : ρ w (ρ w x) = x := by
    have h := congrArg
      (fun f : Module.End (ZMod 2) V ↦ f x)
      (show ρ w * ρ w = 1 by rw [← map_mul, hw2, map_one])
    simpa using h
  change ρ w (ρ w x - x) - (ρ w x - x) = 0
  rw [map_sub, hρ2]
  calc
    x - ρ w x - (ρ w x - x) =
        (x + x) + (ρ w x + ρ w x) := by
      simp only [sub_eq_add_neg, neg_eq_self]
      abel
    _ = 0 := by rw [add_self_eq_zero, add_self_eq_zero, zero_add]

theorem involutionDifference_range_le_ker
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1) :
    (involutionDifference ρ w).range ≤ (involutionDifference ρ w).ker := by
  rintro y ⟨x, rfl⟩
  change involutionDifference ρ w (involutionDifference ρ w x) = 0
  have h := congrArg
    (fun f : Module.End (ZMod 2) V ↦ f x)
    (involutionDifference_sq_eq_zero ρ w hw2)
  simpa using h

private theorem involutionDifference_commute_centralizer
    (ρ : Representation (ZMod 2) G V) (w : G)
    (h : involutionCentralizer w) :
    Commute (involutionDifference ρ w) (ρ (h : G)) := by
  have hhw : (h : G) * w = w * (h : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp h.property
  have hcomm : Commute (ρ w) (ρ (h : G)) := by
    rw [commute_iff_eq, ← map_mul, ← map_mul, ← hhw]
  exact hcomm.sub_left (Commute.one_left _)

private theorem brauerKernel_stable
    (ρ : Representation (ZMod 2) G V) (w : G)
    (h : involutionCentralizer w) :
    brauerKernel ρ w ≤
      Submodule.comap (ρ (h : G)) (brauerKernel ρ w) := by
  intro x hx
  change involutionDifference ρ w (ρ (h : G) x) = 0
  have hc := congrArg
    (fun f : Module.End (ZMod 2) V ↦ f x)
    (involutionDifference_commute_centralizer ρ w h).eq
  change involutionDifference ρ w (ρ (h : G) x) =
    ρ (h : G) (involutionDifference ρ w x) at hc
  rw [show involutionDifference ρ w x = 0 from hx] at hc
  simpa using hc

@[expose] def brauerKernelRepresentation
    (ρ : Representation (ZMod 2) G V) (w : G) :
    Representation (ZMod 2) (involutionCentralizer w) (brauerKernel ρ w) :=
  Representation.subrepresentation
    (ρ.comp (involutionCentralizer w).subtype)
    (brauerKernel ρ w) (fun h ↦ by
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply] using
        brauerKernel_stable ρ w h)

@[simp]
theorem brauerKernelRepresentation_apply_coe
    (ρ : Representation (ZMod 2) G V) (w : G)
    (h : involutionCentralizer w) (x : brauerKernel ρ w) :
    ((brauerKernelRepresentation ρ w h x : brauerKernel ρ w) : V) =
      ρ (h : G) (x : V) := by
  rw [brauerKernelRepresentation, Representation.subrepresentation_apply]
  rfl

theorem brauerRangeInKernel_stable
    (ρ : Representation (ZMod 2) G V) (w : G)
    (h : involutionCentralizer w) :
    brauerRangeInKernel ρ w ≤
      Submodule.comap (brauerKernelRepresentation ρ w h)
        (brauerRangeInKernel ρ w) := by
  intro x hx
  change ρ (h : G) (x : V) ∈ (involutionDifference ρ w).range
  change (x : V) ∈ (involutionDifference ρ w).range at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨ρ (h : G) y, ?_⟩
  have hc := congrArg
    (fun f : Module.End (ZMod 2) V ↦ f y)
    (involutionDifference_commute_centralizer ρ w h).eq
  change involutionDifference ρ w (ρ (h : G) y) =
    ρ (h : G) (involutionDifference ρ w y) at hc
  rw [hy] at hc
  exact hc

@[expose] def brauerQuotientRepresentation
    (ρ : Representation (ZMod 2) G V) (w : G) :
    Representation (ZMod 2) (involutionCentralizer w)
      (BrauerQuotient ρ w) :=
  (brauerKernelRepresentation ρ w).quotient
    (brauerRangeInKernel ρ w) (brauerRangeInKernel_stable ρ w)

@[simp]
theorem brauerQuotientRepresentation_mk
    (ρ : Representation (ZMod 2) G V) (w : G)
    (h : involutionCentralizer w) (x : brauerKernel ρ w) :
    brauerQuotientRepresentation ρ w h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (brauerKernelRepresentation ρ w h x) := by
  rw [brauerQuotientRepresentation, Representation.quotient_apply,
    Submodule.mapQ_apply]

private theorem brauerKernelRepresentation_asAlgebraHom_apply_coe
    (ρ : Representation (ZMod 2) G V) (w : G)
    (a : GroupAlgebraTwo (involutionCentralizer w))
    (x : brauerKernel ρ w) :
    (((brauerKernelRepresentation ρ w).asAlgebraHom a x :
        brauerKernel ρ w) : V) =
      ∑ h : involutionCentralizer w,
        a.coeff h • ρ (h : G) (x : V) := by
  have h := representation_asAlgebraHom_apply_eq_sum
    (brauerKernelRepresentation ρ w) a x
  have hc := congrArg (fun y : brauerKernel ρ w ↦ (y : V)) h
  simpa using hc

private theorem brauerQuotientRepresentation_asAlgebraHom_mk
    (ρ : Representation (ZMod 2) G V) (w : G)
    (a : GroupAlgebraTwo (involutionCentralizer w))
    (x : brauerKernel ρ w) :
    (brauerQuotientRepresentation ρ w).asAlgebraHom a
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ((brauerKernelRepresentation ρ w).asAlgebraHom a x) := by
  rw [representation_asAlgebraHom_apply_eq_sum,
    representation_asAlgebraHom_apply_eq_sum]
  simp_rw [brauerQuotientRepresentation_mk]
  change
    (∑ h : involutionCentralizer w,
        a.coeff h • Submodule.Quotient.mk
          (brauerKernelRepresentation ρ w h x)) =
      (brauerRangeInKernel ρ w).mkQ
        (∑ h : involutionCentralizer w,
          a.coeff h • brauerKernelRepresentation ρ w h x)
  rw [map_sum]
  simp only [map_smul, Submodule.mkQ_apply]

private theorem conjugate_weighted_action_eq_mod_range
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (a : GroupAlgebraTwo G) (ha : IsGroupCentral G a)
    (x : brauerKernel ρ w) (g : G) :
    (Submodule.Quotient.mk
        (a.coeff (w * g * w⁻¹) • ρ (w * g * w⁻¹) (x : V)) :
      V ⧸ (involutionDifference ρ w).range) =
    Submodule.Quotient.mk (a.coeff g • ρ g (x : V)) := by
  apply (Submodule.Quotient.eq (involutionDifference ρ w).range).2
  refine ⟨a.coeff g • ρ g (x : V), ?_⟩
  have hwinv : w⁻¹ = w := (inv_eq_iff_mul_eq_one).2 hw2
  have hcoeff : a.coeff (w * g * w⁻¹) = a.coeff g :=
    (conjInvariantBy_of_isGroupCentral w a ha) g
  have hconj :
      ρ (w * g * w⁻¹) (x : V) = ρ w (ρ g (x : V)) := by
    rw [map_mul, map_mul]
    change ρ w (ρ g (ρ w⁻¹ (x : V))) = ρ w (ρ g (x : V))
    rw [hwinv, brauerKernel_fixed]
  change
    ρ w (a.coeff g • ρ g (x : V)) -
        a.coeff g • ρ g (x : V) =
      a.coeff (w * g * w⁻¹) • ρ (w * g * w⁻¹) (x : V) -
        a.coeff g • ρ g (x : V)
  rw [hcoeff, hconj, map_smul]

private theorem ambient_action_sub_projected_action_mem_range
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (a : GroupAlgebraTwo G) (ha : IsGroupCentral G a)
    (x : brauerKernel ρ w) :
    ρ.asAlgebraHom a (x : V) -
        (((brauerKernelRepresentation ρ w).asAlgebraHom
          (brauerProjection w a) x : brauerKernel ρ w) : V) ∈
      (involutionDifference ρ w).range := by
  let P : Submodule (ZMod 2) V := (involutionDifference ρ w).range
  let F : G → V := fun g ↦ a.coeff g • ρ g (x : V)
  let Fq : G → V ⧸ P := fun g ↦ Submodule.Quotient.mk (F g)
  have hFq : ∀ g : G, Fq (w * g * w⁻¹) = Fq g := by
    intro g
    exact conjugate_weighted_action_eq_mod_range ρ w hw2 a ha x g
  have hsum :=
    sum_eq_sum_centralizer_of_conjInvariant_module w hw2 Fq hFq
  have hq :
      P.mkQ (∑ g : G, F g) =
        P.mkQ (∑ h : involutionCentralizer w, F (h : G)) := by
    simpa only [map_sum, Submodule.mkQ_apply] using hsum
  have hq' :
      (Submodule.Quotient.mk (∑ g : G, F g) : V ⧸ P) =
        Submodule.Quotient.mk
          (∑ h : involutionCentralizer w, F (h : G)) := by
    simpa only [Submodule.mkQ_apply] using hq
  have hmem :
      (∑ g : G, F g) -
          (∑ h : involutionCentralizer w, F (h : G)) ∈ P :=
    (Submodule.Quotient.eq P).mp hq'
  rw [representation_asAlgebraHom_apply_eq_sum,
    brauerKernelRepresentation_asAlgebraHom_apply_coe]
  simpa only [P, F, brauerProjection_coeff] using hmem

theorem brauerProjection_action_mk
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (a : GroupAlgebraTwo G) (ha : IsGroupCentral G a)
    (x : brauerKernel ρ w) :
    (brauerQuotientRepresentation ρ w).asAlgebraHom
        (brauerProjection w a) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨ρ.asAlgebraHom a (x : V),
          centralAlgebraAction_mem_brauerKernel ρ w a ha x⟩ :
          brauerKernel ρ w) := by
  rw [brauerQuotientRepresentation_asAlgebraHom_mk]
  apply (Submodule.Quotient.eq (brauerRangeInKernel ρ w)).2
  change
    (((brauerKernelRepresentation ρ w).asAlgebraHom
          (brauerProjection w a) x : brauerKernel ρ w) : V) -
        ρ.asAlgebraHom a (x : V) ∈
      (involutionDifference ρ w).range
  have hmem :=
    ambient_action_sub_projected_action_mem_range ρ w hw2 a ha x
  have hneg := (involutionDifference ρ w).range.neg_mem hmem
  simpa only [neg_sub] using hneg

private theorem principalBlockActsAsIdentity_brauerQuotient
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (hρ : PrincipalBlockActsAsIdentity ρ)
    (hprojected :
      projectedPrincipalBlock w =
        principalBlockCandidate (involutionCentralizer w)) :
    PrincipalBlockActsAsIdentity (brauerQuotientRepresentation ρ w) := by
  change
    (brauerQuotientRepresentation ρ w).asAlgebraHom
        (principalBlockCandidate (involutionCentralizer w)) = 1
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on (brauerRangeInKernel ρ w) q ?_
  intro x
  change
    (brauerQuotientRepresentation ρ w).asAlgebraHom
        (principalBlockCandidate (involutionCentralizer w))
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x
  rw [← hprojected]
  rw [projectedPrincipalBlock]
  rw [brauerProjection_action_mk ρ w hw2
    (principalBlockCandidate G) (principalBlockCandidate_central G)]
  have hρ' :
      ρ.asAlgebraHom (principalBlockCandidate G) =
        (1 : Module.End (ZMod 2) V) := hρ
  have happ := congrArg
    (fun f : Module.End (ZMod 2) V ↦ f (x : V)) hρ'
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simpa using happ

private theorem oddNormal_action_eq_one_brauerQuotient
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (hρ : PrincipalBlockActsAsIdentity ρ)
    (hprojected :
      projectedPrincipalBlock w =
        principalBlockCandidate (involutionCentralizer w))
    (N : Subgroup (involutionCentralizer w)) [N.Normal]
    (hNodd : Odd (Nat.card N)) (n : N) :
    brauerQuotientRepresentation ρ w (n : involutionCentralizer w) =
      (1 : Module.End (ZMod 2) (BrauerQuotient ρ w)) := by
  exact oddNormal_action_eq_one (brauerQuotientRepresentation ρ w)
    (principalBlockActsAsIdentity_brauerQuotient
      ρ w hw2 hρ hprojected) N hNodd n

theorem oddNormal_action_apply_brauerQuotient
    (ρ : Representation (ZMod 2) G V) (w : G) (hw2 : w * w = 1)
    (hρ : PrincipalBlockActsAsIdentity ρ)
    (hprojected :
      projectedPrincipalBlock w =
        principalBlockCandidate (involutionCentralizer w))
    (N : Subgroup (involutionCentralizer w)) [N.Normal]
    (hNodd : Odd (Nat.card N)) (n : N) (q : BrauerQuotient ρ w) :
    brauerQuotientRepresentation ρ w (n : involutionCentralizer w) q = q := by
  have h := congrArg
    (fun f : Module.End (ZMod 2) (BrauerQuotient ρ w) ↦ f q)
    (oddNormal_action_eq_one_brauerQuotient
      ρ w hw2 hρ hprojected N hNodd n)
  simpa using h

end

end ZStar.ModularBrauerQuotient

end CFSG
