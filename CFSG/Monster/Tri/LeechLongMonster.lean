module

public import CFSG.Monster.Tri.LeechLong
public import CFSG.Monster.Tri.TwoAShort

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open SimpleGraph CFSG.Monster CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.Visible
  CFSG.Monster.Generated CFSG.Monster.B.Short CFSG.Monster.GMS CFSG.Monster.B.Recog
  CFSG.YGroups

section Equivariance

variable {G : Type*} [Group G] {a : G}

theorem preconnected_muGraph_smul (g : G) {y v : ConjVert a}
    (h : (muGraph (longTri a) (twoAGraph a) y v).Preconnected) :
    (muGraph (longTri a) (twoAGraph a) (g • y) (g • v)).Preconnected := by
  have E : EquivariantShort G (twoAGraph a) (shortMid a) (longTri a) := equivariantShort_twoAGraph
  let φ : muGraph (longTri a) (twoAGraph a) y v →g
      muGraph (longTri a) (twoAGraph a) (g • y) (g • v) :=
    { toFun := fun s => ⟨g • (s : ConjVert a), (SimpleGraph.mem_commonNeighbors _).2
        ⟨(E.adj_iff g).2 ((SimpleGraph.mem_commonNeighbors _).1 s.2).1,
          (E.adj_iff g).2 ((SimpleGraph.mem_commonNeighbors _).1 s.2).2⟩⟩
      map_rel' := fun {s t} hst =>
        ⟨(E.adj_iff g).2 hst.1, E.permClosure_smul g hst.2.1, E.permClosure_smul g hst.2.2⟩ }
  refine h.map φ fun t => ?_
  have h1 : (twoAGraph a).Adj y (g⁻¹ • (t : ConjVert a)) := by
    have := (E.adj_iff g⁻¹).2 ((SimpleGraph.mem_commonNeighbors _).1 t.2).1
    simpa using this
  have h2 : (twoAGraph a).Adj v (g⁻¹ • (t : ConjVert a)) := by
    have := (E.adj_iff g⁻¹).2 ((SimpleGraph.mem_commonNeighbors _).1 t.2).2
    simpa using this
  exact ⟨⟨g⁻¹ • (t : ConjVert a), (SimpleGraph.mem_commonNeighbors _).2 ⟨h1, h2⟩⟩,
    Subtype.ext (smul_inv_smul g _)⟩

end Equivariance

theorem isShortCoord_mul_zQ_iff {r : Q} :
    IsShortCoord (coordOf (r * zQ)) ↔ IsShortCoord (coordOf r) := by
  rw [isShortCoord_iff_qCls, isShortCoord_iff_qCls, qCls_mul_zQ]

theorem isShortCoord_of_adj_left {r s : Q} (h : shortQGraph.Adj r s) : IsShortCoord (coordOf r) :=
  (shortQGraph_adj_iff.1 h).1

theorem isShortCoord_of_adj_right {r s : Q} (h : shortQGraph.Adj r s) :
    IsShortCoord (coordOf s) :=
  (shortQGraph_adj_iff.1 h).2.1

theorem shortQGraph_adj_mul_zQ_left {r s : Q} :
    shortQGraph.Adj (r * zQ) s ↔ shortQGraph.Adj r s := by
  rw [shortQGraph_adj_iff_adj, shortQGraph_adj_iff_adj, qCls_mul_zQ]

@[expose] noncomputable def rhoG (q : Q) : Gmat :=
  ⟨rhoEquiv q, Hmat_le_Gmat (Qmat_le_Hmat (rhoEquiv_mem_rhoQ q))⟩

@[simp] theorem coe_rhoG (q : Q) : ((rhoG q : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv q := rfl

theorem rhoG_mul (q q' : Q) : rhoG (q * q') = rhoG q' * rhoG q :=
  Subtype.ext (rhoEquiv_mul q q')

theorem rhoG_injective : Function.Injective rhoG := fun _ _ h =>
  rhoEquiv_injective (congrArg Subtype.val h)

@[expose] noncomputable def tStarG : Gmat := ⟨tStar, tStar_mem_Gmat⟩

theorem isConj_tStarG_iff {x : Gmat} :
    IsConj tStarG x ↔ (x : SpaceB ≃ₗ[ℚ] SpaceB) ∈ shortClass := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, rfl⟩
  · rintro ⟨g, hg, h⟩
    exact ⟨⟨g, hg⟩, Subtype.ext h⟩

theorem isConj_rhoG
    {r : Q} (hr : IsShortCoord (coordOf r)) : IsConj tStarG (rhoG r) :=
  isConj_tStarG_iff.2 (rhoEquiv_mem_shortClass hr)

theorem isConj_rhoG_mul {r s : Q} (h : shortQGraph.Adj r s) :
    IsConj tStarG (rhoG r * rhoG s) :=
  isConj_tStarG_iff.2 (rhoEquiv_mul_mem_shortClass_of_adj h)

variable {a : Gmat}

@[expose] noncomputable def rhoVert (ha : IsConj tStarG a) {r : Q}
    (hr : IsShortCoord (coordOf r)) : ConjVert a :=
  ⟨rhoG r, ha.symm.trans (isConj_rhoG hr)⟩

@[simp] theorem coe_rhoVert
    (ha : IsConj tStarG a) {r : Q} (hr : IsShortCoord (coordOf r)) :
    ((rhoVert ha hr : ConjVert a) : Gmat) = rhoG r := rfl

theorem adj_rhoVert
    (ha : IsConj tStarG a) {r s : Q} (h : shortQGraph.Adj r s) :
    (twoAGraph a).Adj (rhoVert ha (isShortCoord_of_adj_left h))
      (rhoVert ha (isShortCoord_of_adj_right h)) :=
  ⟨fun e => h.ne (rhoG_injective (congrArg Subtype.val e)), ha.symm.trans (isConj_rhoG_mul h)⟩

theorem permClosure_longTri_rhoVert
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (ha : IsConj tStarG a)
    {r s t : Q} (hrs : shortQGraph.Adj r s) (hst : shortQGraph.Adj s t)
    (hrt : shortQGraph.Adj r t) (hne : t ≠ s * r) :
    permClosure (longTri a) (rhoVert ha (isShortCoord_of_adj_left hrs))
      (rhoVert ha (isShortCoord_of_adj_right hrs))
      (rhoVert ha (isShortCoord_of_adj_right hrt)) := by
  have h1 := adj_rhoVert ha hrs
  have h2 := adj_rhoVert ha hst
  have h3 := adj_rhoVert ha hrt
  refine (permClosure_longTri_iff ha2 ha1 h1 h2 h3.symm).2
    ⟨h1, h2, h3.symm, fun e => hne (rhoG_injective ?_)⟩
  exact e.trans (rhoG_mul s r).symm

theorem rhoVert_mem_commonNeighbors (ha : IsConj tStarG a) {r s : Q}
    (hr : IsShortCoord (coordOf r)) (hs : shortQGraph.Adj r s) :
    rhoVert ha (isShortCoord_of_adj_right hs) ∈ (twoAGraph a).commonNeighbors
      (rhoVert ha hr) (rhoVert ha (isShortCoord_mul_zQ_iff.2 hr)) :=
  (SimpleGraph.mem_commonNeighbors _).2
    ⟨adj_rhoVert ha hs, adj_rhoVert ha (shortQGraph_adj_mul_zQ_left.2 hs)⟩

theorem preconnected_muGraph_rhoVert
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (ha : IsConj tStarG a)
    {r : Q} (hr : IsShortCoord (coordOf r))
    (hD : ∀ x ∈ (twoAGraph a).commonNeighbors (rhoVert ha hr)
        (rhoVert ha (isShortCoord_mul_zQ_iff.2 hr)),
      ∃ s, shortQGraph.Adj r s ∧ (x : Gmat) = rhoG s) :
    (muGraph (longTri a) (twoAGraph a) (rhoVert ha hr)
      (rhoVert ha (isShortCoord_mul_zQ_iff.2 hr))).Preconnected := by
  let f : (longQGraph (qCls r)).induce (shortQGraph.neighborSet r) →g
      muGraph (longTri a) (twoAGraph a) (rhoVert ha hr)
        (rhoVert ha (isShortCoord_mul_zQ_iff.2 hr)) :=
    { toFun := fun s => ⟨rhoVert ha (isShortCoord_of_adj_right (show shortQGraph.Adj r s from s.2)),
        rhoVert_mem_commonNeighbors ha hr (show shortQGraph.Adj r s from s.2)⟩
      map_rel' := by
        intro s t hst
        have hs : shortQGraph.Adj r s := s.2
        have ht : shortQGraph.Adj r t := t.2
        have hst1 : (longQGraph (qCls r)).Adj (s : Q) (t : Q) := hst
        have h := (longQGraph_adj_iff_mul (r := r) (s := (s : Q)) (s' := (t : Q))).1 hst1
        refine ⟨adj_rhoVert ha h.1, permClosure_longTri_rhoVert ha2 ha1 ha hs h.1 ht h.2.1, ?_⟩
        exact permClosure_longTri_rhoVert ha2 ha1 ha (shortQGraph_adj_mul_zQ_left.2 hs) h.1
          (shortQGraph_adj_mul_zQ_left.2 ht)
          (fun e => h.2.2 (e.trans (mul_assoc (s : Q) r zQ).symm)) }
  refine (preconnected_longQGraph hr).map f fun x => ?_
  obtain ⟨s, hrs, hx⟩ := hD x x.2
  exact ⟨⟨s, hrs⟩, Subtype.ext (Subtype.ext hx.symm)⟩

theorem preconnected_muGraph_of_smul_rhoVert
    (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (ha : IsConj tStarG a) {r : Q} (hr : IsShortCoord (coordOf r))
    (hD : ∀ x ∈ (twoAGraph a).commonNeighbors (rhoVert ha hr)
        (rhoVert ha (isShortCoord_mul_zQ_iff.2 hr)),
      ∃ s, shortQGraph.Adj r s ∧ (x : Gmat) = rhoG s)
    {y v : ConjVert a} (g : Gmat) (hy : g • y = rhoVert ha hr)
    (hv : g • v = rhoVert ha (isShortCoord_mul_zQ_iff.2 hr)) :
    (muGraph (longTri a) (twoAGraph a) y v).Preconnected := by
  obtain rfl : y = g⁻¹ • rhoVert ha hr := by rw [← hy, inv_smul_smul]
  obtain rfl : v = g⁻¹ • rhoVert ha (isShortCoord_mul_zQ_iff.2 hr) := by
    rw [← hv, inv_smul_smul]
  exact preconnected_muGraph_smul g⁻¹ (preconnected_muGraph_rhoVert ha2 ha1 ha hr hD)

theorem exists_lift_of_mem_rho (ha : IsConj tStarG a)
    (hT : ∀ q : Q, rhoEquiv q ∈ shortClass → IsShortCoord (coordOf q))
    {r : Q} (hr : IsShortCoord (coordOf r)) {x : ConjVert a}
    (hx : x ∈ (twoAGraph a).commonNeighbors (rhoVert ha hr)
      (rhoVert ha (isShortCoord_mul_zQ_iff.2 hr)))
    (hQ : ∃ q : Q, (x : Gmat) = rhoG q) :
    ∃ s, shortQGraph.Adj r s ∧ (x : Gmat) = rhoG s := by
  obtain ⟨q, hq⟩ := hQ
  have h1 := ((SimpleGraph.mem_commonNeighbors _).1 hx).1
  have hqT : IsConj tStarG (rhoG q) := by
    rw [← hq]
    exact ha.trans x.2
  have hqs : IsShortCoord (coordOf q) := hT q (isConj_tStarG_iff.1 hqT)
  have h2 : IsConj tStarG (rhoG r * rhoG q) := by
    have h3 : IsConj a (rhoG r * (x : Gmat)) := h1.2
    rw [hq] at h3
    exact ha.trans h3
  have hqr : IsShortCoord (coordOf (q * r)) := by
    refine hT _ ?_
    rw [rhoEquiv_mul]
    exact isConj_tStarG_iff.1 h2
  refine ⟨q, ?_, hq⟩
  rw [shortQGraph_adj_iff]
  refine ⟨hr, hqs, ?_⟩
  have hcomm : qCls (r * q) = qCls (q * r) := by rw [qCls_mul, qCls_mul, add_comm]
  rw [isShortCoord_iff_qCls, hcomm]
  exact hqr

@[expose] noncomputable def xmatG : Gmat := rhoG zQ

theorem rhoG_mul_xmatG (r : Q) : rhoG r * xmatG = rhoG (r * zQ) := by
  have hc : r * zQ = zQ * r := Subgroup.mem_center_iff.1 CFSG.Monster.B.Short.zQ_mem_center r
  rw [hc, rhoG_mul]
  rfl

theorem exists_smul_eq_rhoVert_of_two_B
    (ha2 : a * a = 1) (ha : IsConj tStarG a)
    (hρ : ∀ t : ConjVert a, (t : Gmat) * xmatG = xmatG * t → IsConj a ((t : Gmat) * xmatG) →
      ∃ r : Q, IsShortCoord (coordOf r) ∧ (t : Gmat) = rhoG r)
    {y v : ConjVert a} (hyv : (y : Gmat) * v = v * y) (h2B : IsConj xmatG ((y : Gmat) * v)) :
    ∃ (g : Gmat) (r : Q) (hr : IsShortCoord (coordOf r)), g • y = rhoVert ha hr ∧
      g • v = rhoVert ha (isShortCoord_mul_zQ_iff.2 hr) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h2B
  have hy2 : (y : Gmat) * y = 1 := conjVert_mul_self ha2 y
  have hz : c⁻¹ * ((y : Gmat) * v) * c = xmatG := by
    rw [← hc]
    group
  have e1 : ((c⁻¹ • y : ConjVert a) : Gmat) = c⁻¹ * y * c := by rw [coe_smul_conjVert, inv_inv]
  have e2 : ((c⁻¹ • v : ConjVert a) : Gmat) = c⁻¹ * v * c := by rw [coe_smul_conjVert, inv_inv]
  have hyyv : (y : Gmat) * ((y : Gmat) * v) = v := by rw [← mul_assoc, hy2, one_mul]
  have hyvy : ((y : Gmat) * v) * y = v := by rw [hyv, mul_assoc, hy2, mul_one]
  have ht : ((c⁻¹ • y : ConjVert a) : Gmat) * xmatG = ((c⁻¹ • v : ConjVert a) : Gmat) := by
    rw [e1, e2, ← hz]
    calc c⁻¹ * y * c * (c⁻¹ * (y * v) * c) = c⁻¹ * ((y : Gmat) * ((y : Gmat) * v)) * c := by group
      _ = c⁻¹ * v * c := by rw [hyyv]
  have hcomm : ((c⁻¹ • y : ConjVert a) : Gmat) * xmatG =
      xmatG * ((c⁻¹ • y : ConjVert a) : Gmat) := by
    rw [ht, e1, e2, ← hz]
    calc c⁻¹ * (v : Gmat) * c = c⁻¹ * (((y : Gmat) * v) * y) * c := by rw [hyvy]
      _ = c⁻¹ * (y * v) * c * (c⁻¹ * y * c) := by group
  obtain ⟨r, hr, hrt⟩ := hρ (c⁻¹ • y) hcomm (by rw [ht]; exact (c⁻¹ • v).2)
  refine ⟨c⁻¹, r, hr, Subtype.ext hrt, Subtype.ext ?_⟩
  rw [← ht, hrt]
  exact rhoG_mul_xmatG r

theorem preconnected_muGraph_of_model
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (ha : IsConj tStarG a)
    (hconj : ∀ {y u : ConjVert a}, (twoAGraph a).Adj (baseVertex a) y →
      (twoAGraph a).Adj (baseVertex a) u → (twoAGraph a).Adj y u →
      permClosure (longTri a) (baseVertex a) y u →
      ∃ (g : Gmat) (r : Q) (hr : IsShortCoord (coordOf r)), g • y = rhoVert ha hr ∧
        g • shortMid a (baseVertex a) u = rhoVert ha (isShortCoord_mul_zQ_iff.2 hr))
    (hD : ∀ {r : Q} (hr : IsShortCoord (coordOf r)),
      ∀ x ∈ (twoAGraph a).commonNeighbors (rhoVert ha hr)
        (rhoVert ha (isShortCoord_mul_zQ_iff.2 hr)),
      ∃ s, shortQGraph.Adj r s ∧ (x : Gmat) = rhoG s)
    {y u : ConjVert a} (hxy : (twoAGraph a).Adj (baseVertex a) y)
    (hxu : (twoAGraph a).Adj (baseVertex a) u) (hyu : (twoAGraph a).Adj y u)
    (hL : permClosure (longTri a) (baseVertex a) y u) :
    (muGraph (longTri a) (twoAGraph a) y (shortMid a (baseVertex a) u)).Preconnected := by
  obtain ⟨g, r, hr, hy, hv⟩ := hconj hxy hxu hyu hL
  exact preconnected_muGraph_of_smul_rhoVert ha2 ha1 ha hr (hD hr) g hy hv

theorem quad_null_twoAGraph_of_model
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (ha : IsConj tStarG a)
    (hconj : ∀ {y u : ConjVert a}, (twoAGraph a).Adj (baseVertex a) y →
      (twoAGraph a).Adj (baseVertex a) u → (twoAGraph a).Adj y u →
      permClosure (longTri a) (baseVertex a) y u →
      ∃ (g : Gmat) (r : Q) (hr : IsShortCoord (coordOf r)), g • y = rhoVert ha hr ∧
        g • shortMid a (baseVertex a) u = rhoVert ha (isShortCoord_mul_zQ_iff.2 hr))
    (hD : ∀ {r : Q} (hr : IsShortCoord (coordOf r)),
      ∀ x ∈ (twoAGraph a).commonNeighbors (rhoVert ha hr)
        (rhoVert ha (isShortCoord_mul_zQ_iff.2 hr)),
      ∃ s, shortQGraph.Adj r s ∧ (x : Gmat) = rhoG s)
    {x y u : ConjVert a} (hxy : (twoAGraph a).Adj x y) (hxu : (twoAGraph a).Adj x u)
    (hyu : (twoAGraph a).Adj y u) (hL : permClosure (longTri a) x y u) :
    MarkedHomotopic (longTri a) ((shortStruct_twoAGraph ha2 ha1).quad hxy hxu hyu hL) .nil :=
  quad_null_twoAGraph_of_mu ha2 ha1
    (fun hxy hxu hyu hL => preconnected_muGraph_of_model ha2 ha1 ha hconj hD hxy hxu hyu hL)
    hxy hxu hyu hL

theorem commute_shortMid (ha2 : a * a = 1) {y u : ConjVert a}
    (hxy : (twoAGraph a).Adj (baseVertex a) y) (hxu : (twoAGraph a).Adj (baseVertex a) u)
    (hyu : (twoAGraph a).Adj y u) :
    (y : Gmat) * (shortMid a (baseVertex a) u : ConjVert a) =
      (shortMid a (baseVertex a) u : ConjVert a) * y := by
  rw [shortMid_coe hxu]
  have h1 := adj_comm ha2 hxy
  have h2 := adj_comm ha2 hyu
  calc (y : Gmat) * ((baseVertex a : ConjVert a) * u)
      = ((y : Gmat) * (baseVertex a : ConjVert a)) * u := (mul_assoc _ _ _).symm
    _ = ((baseVertex a : ConjVert a) * y) * u := by rw [← h1]
    _ = (baseVertex a : ConjVert a) * (y * u) := mul_assoc _ _ _
    _ = (baseVertex a : ConjVert a) * (u * y) := by rw [h2]
    _ = ((baseVertex a : ConjVert a) * u) * y := (mul_assoc _ _ _).symm

theorem quad_null_twoAGraph_of_two_B
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (ha : IsConj tStarG a)
    (h2B : ∀ {y u : ConjVert a}, (twoAGraph a).Adj (baseVertex a) y →
      (twoAGraph a).Adj (baseVertex a) u → (twoAGraph a).Adj y u →
      permClosure (longTri a) (baseVertex a) y u →
      IsConj xmatG ((y : Gmat) * (shortMid a (baseVertex a) u : ConjVert a)))
    (hρ : ∀ t : ConjVert a, (t : Gmat) * xmatG = xmatG * t → IsConj a ((t : Gmat) * xmatG) →
      ∃ r : Q, IsShortCoord (coordOf r) ∧ (t : Gmat) = rhoG r)
    (hD : ∀ {r : Q} (hr : IsShortCoord (coordOf r)),
      ∀ x ∈ (twoAGraph a).commonNeighbors (rhoVert ha hr)
        (rhoVert ha (isShortCoord_mul_zQ_iff.2 hr)),
      ∃ s, shortQGraph.Adj r s ∧ (x : Gmat) = rhoG s)
    {x y u : ConjVert a} (hxy : (twoAGraph a).Adj x y) (hxu : (twoAGraph a).Adj x u)
    (hyu : (twoAGraph a).Adj y u) (hL : permClosure (longTri a) x y u) :
    MarkedHomotopic (longTri a) ((shortStruct_twoAGraph ha2 ha1).quad hxy hxu hyu hL) .nil := by
  refine quad_null_twoAGraph_of_model ha2 ha1 ha (fun {y u} hxy hxu hyu hL => ?_) hD hxy hxu hyu hL
  exact exists_smul_eq_rhoVert_of_two_B ha2 ha hρ (commute_shortMid ha2 hxy hxu hyu)
    (h2B hxy hxu hyu hL)

end CFSG.Monster.Tri.Leech
