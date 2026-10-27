module

public import CFSG.Monster.B.TwoA.Amalgam.PointRootCore
public import CFSG.Monster.B.E6.RootClassGen

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

abbrev xconj
    (e : Eam) : Eam := e⁻¹ * xhatEam * e

theorem xhat_mem_centralizer_of_mem_Pc_zero
    {p : Dfull} (hp : p ∈ Pc 0) :
    p * xhat = xhat * p := by
  have hJ : p ∈ Jhat := hp.1
  rw [← centralizer_xhat] at hJ
  exact (Subgroup.mem_centralizer_singleton_iff.1 hJ)

theorem xconj_congr
    {e f : Eam} (h : ((f * e⁻¹ : Eam) : Dfull) ∈ Pc 0) : xconj e = xconj f := by
  apply Subtype.ext
  have hc := xhat_mem_centralizer_of_mem_Pc_zero h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_xhatEam] at hc ⊢
  calc (e : Dfull)⁻¹ * xhat * e
      = (f : Dfull)⁻¹ * ((f * (e : Dfull)⁻¹) * xhat) * e := by group
    _ = (f : Dfull)⁻¹ * (xhat * (f * (e : Dfull)⁻¹)) * e := by rw [hc]
    _ = (f : Dfull)⁻¹ * xhat * f := by group

@[expose] def xconjCos :
    P1Cos → Eam :=
  Quotient.lift xconj fun _ _ h => xconj_congr (p1rel_iff.1 h)

theorem xconjCos_mk
    (e : Eam) : xconjCos (Quotient.mk _ e) = xconj e := rfl

section Root

variable (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar)

abbrev rho0 : Eam →* GStar := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.zpowers cE'))

theorem rho0_apply (y : Eam) : rho0 θ y = θ (QuotientGroup.mk y) := rfl

theorem theta_xconj
    (hx : θ (QuotientGroup.mk xhatEam) = rootStar) (e : Eam) :
    rho0 θ (xconj e) = (rho0 θ e)⁻¹ * rootStar * rho0 θ e := by
  have h : rho0 θ xhatEam = rootStar := hx
  show rho0 θ (e⁻¹ * xhatEam * e) = _
  rw [map_mul, map_mul, map_inv, h]

theorem theta_xconj_mem
    (hx : θ (QuotientGroup.mk xhatEam) = rootStar) (e : Eam) :
    rho0 θ (xconj e) ∈ (SemidirectProduct.inl : stdGroup →* GStar) '' rootClass := by
  rw [← setOf_isConj_rootStar, Set.mem_ofPred_eq, theta_xconj θ hx]
  exact isConj_iff.2 ⟨(rho0 θ e)⁻¹, by rw [inv_inv]⟩

@[expose] def rootPt
    (hx : θ (QuotientGroup.mk xhatEam) = rootStar) (u : P1Cos) : rootClass :=
  ⟨(theta_xconj_mem θ hx (Quotient.out u)).choose,
    (theta_xconj_mem θ hx (Quotient.out u)).choose_spec.1⟩

theorem inl_rootPt
    (hx : θ (QuotientGroup.mk xhatEam) = rootStar) (u : P1Cos) :
    (SemidirectProduct.inl (rootPt θ hx u : stdGroup) : GStar) = rho0 θ (xconjCos u) := by
  have h := (theta_xconj_mem θ hx (Quotient.out u)).choose_spec.2
  rw [rootPt]
  dsimp only
  rw [h]
  conv_rhs => rw [← Quotient.out_eq u]
  rfl

theorem inl_rootPt_mk
    (hx : θ (QuotientGroup.mk xhatEam) = rootStar) (e : Eam) :
    (SemidirectProduct.inl (rootPt θ hx (Quotient.mk _ e) : stdGroup) : GStar) =
      rho0 θ (xconj e) :=
  inl_rootPt θ hx _

end Root

section Graph

variable (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar)
  (hx : θ (QuotientGroup.mk xhatEam) = rootStar)
  (hinj : ∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
    (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk (e'⁻¹ * xhatEam * e'))
  (hcomm : ∀ e e' : Eam,
    ((∃ x, (vtx 0 (chamberOf e) ∩ vtx 3 x).Nonempty ∧ (vtx 0 (chamberOf e') ∩ vtx 3 x).Nonempty) ↔
      Commute (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE')
        (QuotientGroup.mk (e'⁻¹ * xhatEam * e'))))

include hinj in
theorem rootPt_injective :
    Function.Injective (rootPt θ hx) := by
  intro u w h
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
  obtain ⟨f, rfl⟩ := Quotient.mk_surjective w
  have h1 := congrArg (fun z : rootClass => (SemidirectProduct.inl (z : stdGroup) : GStar)) h
  simp only [inl_rootPt_mk] at h1
  exact Quotient.sound (p1rel_iff.2 ((vtx_eq_iff 0 e f).1 ((hinj e f).2 (θ.injective h1))))

theorem rootPt_surjective : Function.Surjective (rootPt θ hx) := by
  rintro ⟨x, hx'⟩
  have hmem : (SemidirectProduct.inl x : GStar) ∈ {y : GStar | IsConj rootStar y} := by
    rw [setOf_isConj_rootStar]
    exact ⟨x, hx', rfl⟩
  obtain ⟨γ, hγ⟩ := isConj_iff.1 hmem
  obtain ⟨q, hq⟩ := θ.surjective γ⁻¹
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
  have hq' : rho0 θ e = γ⁻¹ := hq
  have hinl : Function.Injective (SemidirectProduct.inl : stdGroup →* GStar) :=
    SemidirectProduct.inl_injective
  refine ⟨Quotient.mk _ e, Subtype.ext (hinl ?_)⟩
  rw [inl_rootPt_mk, theta_xconj θ hx, hq', inv_inv, ← hγ]

@[expose] def rootPtEquiv :
    P1Cos ≃ rootClass :=
  Equiv.ofBijective (rootPt θ hx) ⟨rootPt_injective θ hx hinj, rootPt_surjective θ hx⟩

theorem mul_mul_of_comm {G : Type*} [Group G] {c a b : G} (hca : c * a = a * c) (hc2 : c * c = 1) :
    (c * a) * (c * b) = a * b := by
  calc (c * a) * (c * b) = c * (a * c) * b := by group
    _ = c * (c * a) * b := by rw [hca]
    _ = (c * c) * a * b := by group
    _ = a * b := by rw [hc2, one_mul]

theorem cQ_comm_of_mem_Eam {y : Dfull} (hy : y ∈ Eam) : cQ * y = y * cQ :=
  (Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer hy)).symm

theorem commute_xconj_of_adj
    {e f : Eam}
    (h : cgraph.Adj (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e))
      (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ f))) : Commute (xconj e) (xconj f) := by
  have hc := (clabel_adj h).2.1
  rw [clabel_nbr, clabel_nbr] at hc
  have he : ((e : Dfull)⁻¹ * xhat * e) ∈ Eam := (xconj e).2
  have hf : ((f : Dfull)⁻¹ * xhat * f) ∈ Eam := (xconj f).2
  rw [mul_mul_of_comm (cQ_comm_of_mem_Eam he) cQ_mul_self,
    mul_mul_of_comm (cQ_comm_of_mem_Eam hf) cQ_mul_self] at hc
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_xhatEam]
  exact hc

include hx hcomm in
theorem adj_of_commute_rootPt
    {e f : Eam} (hne : (Quotient.mk _ e : P1Cos) ≠ Quotient.mk _ f)
    (h : Commute (rootPt θ hx (Quotient.mk _ e) : stdGroup) (rootPt θ hx (Quotient.mk _ f))) :
    cgraph.Adj (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e))
      (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ f)) := by
  have h1 : Commute (rho0 θ (xconj e)) (rho0 θ (xconj f)) := by
    rw [← inl_rootPt_mk θ hx, ← inl_rootPt_mk θ hx]
    exact h.map (SemidirectProduct.inl : stdGroup →* GStar)
  have h2 : Commute (QuotientGroup.mk (xconj e) : Eam ⧸ Subgroup.zpowers cE')
      (QuotientGroup.mk (xconj f)) :=
    Commute.of_map (f := θ) θ.injective h1
  obtain ⟨x, hx1, hx2⟩ := (hcomm e f).2 h2
  exact nbr_adj_of_common_vtx a0_mem_Ehat a0_not_mem_N1 hne x (by rwa [ptMap_mk])
    (by rwa [ptMap_mk])

include hx hcomm in
theorem adj_iff_commute_rootPt
    {u w : P1Cos} (hne : u ≠ w) :
    cgraph.Adj (nbr a0_mem_Ehat a0_not_mem_N1 u) (nbr a0_mem_Ehat a0_not_mem_N1 w) ↔
      Commute (rootPt θ hx u : stdGroup) (rootPt θ hx w) := by
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
  obtain ⟨f, rfl⟩ := Quotient.mk_surjective w
  constructor
  · intro h
    have h1 := (commute_xconj_of_adj h).map (rho0 θ)
    rw [← inl_rootPt_mk θ hx, ← inl_rootPt_mk θ hx] at h1
    exact Commute.of_map (f := (SemidirectProduct.inl : stdGroup →* GStar))
      SemidirectProduct.inl_injective h1
  · exact adj_of_commute_rootPt θ hx hcomm hne

include θ hx hcomm in
theorem adj_iff_common_vtx
    {u w : P1Cos} (hne : u ≠ w) :
    cgraph.Adj (nbr a0_mem_Ehat a0_not_mem_N1 u) (nbr a0_mem_Ehat a0_not_mem_N1 w) ↔
      ∃ x, (ptMap u ∩ vtx 3 x).Nonempty ∧ (ptMap w ∩ vtx 3 x).Nonempty := by
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
  obtain ⟨f, rfl⟩ := Quotient.mk_surjective w
  rw [adj_iff_commute_rootPt θ hx hcomm hne, ptMap_mk, ptMap_mk, hcomm e f]
  constructor
  · intro h
    have h1 : Commute (rho0 θ (xconj e)) (rho0 θ (xconj f)) := by
      rw [← inl_rootPt_mk θ hx, ← inl_rootPt_mk θ hx]
      exact h.map (SemidirectProduct.inl : stdGroup →* GStar)
    exact Commute.of_map (f := θ) θ.injective h1
  · intro h
    have h1 : Commute (rho0 θ (xconj e)) (rho0 θ (xconj f)) := h.map θ
    rw [← inl_rootPt_mk θ hx, ← inl_rootPt_mk θ hx] at h1
    exact Commute.of_map (f := (SemidirectProduct.inl : stdGroup →* GStar))
      SemidirectProduct.inl_injective h1

theorem inl_rootPt_mk_mul (e f : Eam) :
    (SemidirectProduct.inl (rootPt θ hx (Quotient.mk _ (e * f)) : stdGroup) : GStar) =
      (rho0 θ f)⁻¹ * (SemidirectProduct.inl (rootPt θ hx (Quotient.mk _ e) : stdGroup) : GStar) *
        rho0 θ f := by
  rw [inl_rootPt_mk, inl_rootPt_mk, theta_xconj θ hx, theta_xconj θ hx, map_mul]
  group

include θ hx in
theorem act_trivial_iff
    (f : Eam) :
    (∀ e : Eam, cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) (toS f) =
      nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) ↔ f ∈ Subgroup.zpowers cE' := by
  constructor
  · intro h
    have hθ : rho0 θ f = 1 := by
      apply eq_one_of_forall_commute_rootClass
      intro x hxm
      obtain ⟨u, hu⟩ := rootPt_surjective θ hx ⟨x, hxm⟩
      obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
      have h1 := h e
      rw [← nbr_mk_mul] at h1
      have h3 : rootPt θ hx (Quotient.mk _ (e * f)) = rootPt θ hx (Quotient.mk _ e) := by
        rw [nbr_injective a0_mem_Ehat a0_not_mem_N1 h1]
      have h4 : (SemidirectProduct.inl (rootPt θ hx (Quotient.mk _ (e * f)) : stdGroup) : GStar) =
          SemidirectProduct.inl (rootPt θ hx (Quotient.mk _ e) : stdGroup) :=
        congrArg (fun z : rootClass => (SemidirectProduct.inl (z : stdGroup) : GStar)) h3
      rw [inl_rootPt_mk_mul θ hx, hu] at h4
      calc rho0 θ f * (SemidirectProduct.inl x : GStar)
          = rho0 θ f * ((rho0 θ f)⁻¹ * (SemidirectProduct.inl x : GStar) * rho0 θ f) := by
            rw [h4]
        _ = (SemidirectProduct.inl x : GStar) * rho0 θ f := by group
    have hθ' : θ (QuotientGroup.mk f) = 1 := hθ
    rw [map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at hθ'
    exact hθ'
  · intro hf e
    rw [← nbr_mk_mul]
    congr 1
    refine Quotient.sound (p1rel_iff.2 ?_)
    have hc0 : (cE' : Dfull) ∈ Pc 0 := Bam_le_Pc 0 (Nc_le_Bam 0 (Nc_zero ▸ cQ_mem_N1))
    have hfP : (f : Dfull) ∈ Pc 0 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
      rw [Subgroup.coe_zpow]
      exact (Pc 0).zpow_mem hc0 k
    have hfc : f⁻¹ ∈ Subgroup.center Eam :=
      Subgroup.inv_mem _ (Subgroup.zpowers_le.2 cE'_mem_center hf)
    have e1 : e * (e * f)⁻¹ = f⁻¹ := by
      rw [mul_inv_rev, ← mul_assoc, Subgroup.mem_center_iff.1 hfc e, mul_assoc, mul_inv_cancel,
        mul_one]
    rw [e1, Subgroup.coe_inv]
    exact (Pc 0).inv_mem hfP

end Graph

end CFSG.Monster.B.TwoA.Amalgam
