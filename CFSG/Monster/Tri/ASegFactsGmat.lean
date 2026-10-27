module

public import CFSG.Monster.Tri.GmatF1Type
public import CFSG.Monster.Tri.LeechModelClasses
public import CFSG.Monster.Tri.LeechModelMaster
public import CFSG.Monster.Tri.ASegFactsLocal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short CFSG.Monster.GMS
  CFSG.Monster.B.Recog CFSG.YGroups CFSG.Monster.Existence CFSG.Monster.Tri.Leech

section Transport

variable {G : Type} [Group G] {a : G}

theorem smul_mem_leechQ_iff (g z : G) (x : ConjVert a) :
    ((g • x : ConjVert a) : G) ∈ leechQ (g * z * g⁻¹) ↔ (x : G) ∈ leechQ z := by
  rw [coe_smul_conjVert, mem_leechQ_conj_iff, show g⁻¹ * (g * (x : G) * g⁻¹) * g = x by group]

theorem preconnected_commonNeighbors_smul (g : G) {x y : ConjVert a}
    (h : ((twoAGraph a).induce ((twoAGraph a).commonNeighbors x y)).Preconnected) :
    ((twoAGraph a).induce ((twoAGraph a).commonNeighbors (g • x) (g • y))).Preconnected := by
  let φ : (twoAGraph a).induce ((twoAGraph a).commonNeighbors x y) →g
      (twoAGraph a).induce ((twoAGraph a).commonNeighbors (g • x) (g • y)) :=
    { toFun := fun s => ⟨g • (s : ConjVert a), (SimpleGraph.mem_commonNeighbors _).2
        ⟨twoAGraph_adj_smul g ((SimpleGraph.mem_commonNeighbors _).1 s.2).1,
          twoAGraph_adj_smul g ((SimpleGraph.mem_commonNeighbors _).1 s.2).2⟩⟩
      map_rel' := fun {s t} hst => twoAGraph_adj_smul g hst }
  refine h.map φ fun t => ?_
  have h1 : (twoAGraph a).Adj x (g⁻¹ • (t : ConjVert a)) := by
    have := twoAGraph_adj_smul g⁻¹ ((SimpleGraph.mem_commonNeighbors _).1 t.2).1
    simpa using this
  have h2 : (twoAGraph a).Adj y (g⁻¹ • (t : ConjVert a)) := by
    have := twoAGraph_adj_smul g⁻¹ ((SimpleGraph.mem_commonNeighbors _).1 t.2).2
    simpa using this
  exact ⟨⟨g⁻¹ • (t : ConjVert a), (SimpleGraph.mem_commonNeighbors _).2 ⟨h1, h2⟩⟩,
    Subtype.ext (smul_inv_smul g _)⟩

theorem leechGraphFacts_of_base {z₀ : G}
    (hdiam : ∀ x y : ConjVert a, (x : G) ∈ leechQ z₀ → (y : G) ∈ leechQ z₀ →
      x = y ∨ (twoAGraph a).Adj x y ∨ ∃ w : ConjVert a, (w : G) ∈ leechQ z₀ ∧
        (twoAGraph a).Adj x w ∧ (twoAGraph a).Adj w y)
    (hmu : ∀ x y : ConjVert a, (x : G) ∈ leechQ z₀ → (y : G) ∈ leechQ z₀ →
      z₀ ∈ Subgroup.zpowers ((x : G) * y) →
        ((twoAGraph a).induce ((twoAGraph a).commonNeighbors x y)).Preconnected) :
    LeechGraphFacts a z₀ := by
  have hQ : ∀ (g : G) (x : ConjVert a), (x : G) ∈ leechQ (g * z₀ * g⁻¹) →
      ((g⁻¹ • x : ConjVert a) : G) ∈ leechQ z₀ := by
    intro g x hx
    have e : g⁻¹ * (g * z₀ * g⁻¹) * g⁻¹⁻¹ = z₀ := by group
    have h := smul_mem_leechQ_iff g⁻¹ (g * z₀ * g⁻¹) x
    rw [e] at h
    exact h.2 hx
  constructor
  · intro z hz x y hx hy
    obtain ⟨g, rfl⟩ := isConj_iff.1 hz
    rcases hdiam (g⁻¹ • x) (g⁻¹ • y) (hQ g x hx) (hQ g y hy) with h | h | ⟨w, hwQ, h1, h2⟩
    · exact Or.inl (smul_left_cancel g⁻¹ h)
    · refine Or.inr (Or.inl ?_)
      have := twoAGraph_adj_smul g h
      simpa using this
    · refine Or.inr (Or.inr ⟨g • w, (smul_mem_leechQ_iff g z₀ w).2 hwQ, ?_, ?_⟩)
      · have := twoAGraph_adj_smul g h1
        simpa using this
      · have := twoAGraph_adj_smul g h2
        simpa using this
  · intro z hz x y hx hy _ hzp
    obtain ⟨g, rfl⟩ := isConj_iff.1 hz
    have hzp' : z₀ ∈ Subgroup.zpowers (((g⁻¹ • x : ConjVert a) : G) * (g⁻¹ • y : ConjVert a)) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzp
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have e : ((g⁻¹ • x : ConjVert a) : G) * (g⁻¹ • y : ConjVert a) =
          g⁻¹ * ((x : G) * y) * g⁻¹⁻¹ := by
        simp only [coe_smul_conjVert]
        group
      rw [e, conj_zpow, hk]
      group
    have h := preconnected_commonNeighbors_smul g (hmu (g⁻¹ • x) (g⁻¹ • y) (hQ g x hx) (hQ g y hy)
      hzp')
    rw [smul_inv_smul, smul_inv_smul] at h
    exact h

end Transport

section Gmat

private noncomputable def centEquiv : cent xGmat ≃* Gvis :=
  ((cent xGmat).equivMapOfInjective Gmat.subtype Gmat.subtype_injective).trans
    (MulEquiv.subgroupCongr map_cent_xGmat)

private theorem centEquiv_coe (h : cent xGmat) :
    ((centEquiv h : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = ((h : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) := rfl

theorem mem_leechQ_xmatG_iff
    {g : Gmat} :
    g ∈ leechQ xmatG ↔ ∃ q : Q, rhoEquiv q = (g : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [← xGmat_eq_xmatG]
  have hmap : (CFSG.pCore 2 (cent xGmat)).map centEquiv.toMonoidHom = rhoQvis := by
    rw [CFSG.pCore_map_iso 2 centEquiv, pCore_Gvis]
  have mem_iff : ∀ y : cent xGmat, y ∈ CFSG.pCore 2 (cent xGmat) ↔ centEquiv y ∈ rhoQvis := by
    intro y
    rw [← hmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  constructor
  · intro hg
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
    have h2 : ((centEquiv h : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoQ := (mem_iff h).1 hh
    obtain ⟨q, hq⟩ := mem_rhoQ.1 h2
    exact ⟨q, hq.trans (centEquiv_coe h)⟩
  · rintro ⟨q, hq⟩
    have hg : g = rhoG q := Subtype.ext hq.symm
    have hcomm : g * xGmat = xGmat * g := by
      rw [hg, xGmat_eq_xmatG]
      exact rhoG_comm_xmatG q
    have hgc : g ∈ cent xGmat := Subgroup.mem_centralizer_singleton_iff.2 hcomm
    refine Subgroup.mem_map.2 ⟨⟨g, hgc⟩, (mem_iff ⟨g, hgc⟩).2 ?_, rfl⟩
    show ((centEquiv ⟨g, hgc⟩ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoQ
    exact mem_rhoQ.2 ⟨q, hq.trans (centEquiv_coe ⟨g, hgc⟩).symm⟩

theorem rhoG_mem_leechQ
    (r : Q) : rhoG r ∈ leechQ xmatG :=
  mem_leechQ_xmatG_iff.2 ⟨r, rfl⟩

theorem exists_short_of_mem_leechQ
    {x : ConjVert tStarG} (hx : (x : Gmat) ∈ leechQ xmatG) :
    ∃ r : Q, IsShortCoord (coordOf r) ∧ (x : Gmat) = rhoG r := by
  obtain ⟨q, hq⟩ := mem_leechQ_xmatG_iff.1 hx
  have hT : rhoEquiv q ∈ shortClass := by
    rw [hq]
    exact isConj_tStarG_iff.1 x.2
  exact ⟨q, isShortCoord_of_rhoEquiv_mem_shortClass hT, Subtype.ext hq.symm⟩

noncomputable abbrev rv
    {r : Q} (hr : IsShortCoord (coordOf r)) : ConjVert tStarG :=
  rhoVert (IsConj.refl tStarG) hr

theorem adj_rv_iff
    {r s : Q} (hr : IsShortCoord (coordOf r)) (hs : IsShortCoord (coordOf s)) :
    (twoAGraph tStarG).Adj (rv hr) (rv hs) ↔ shortQGraph.Adj r s := by
  refine ⟨fun h => ?_, fun h => adj_rhoVert (IsConj.refl tStarG) h⟩
  have h1 : IsConj tStarG (rhoG r * rhoG s) := h.2
  rw [← rhoG_mul s r] at h1
  have h2 : IsShortCoord (coordOf (s * r)) :=
    isShortCoord_of_rhoEquiv_mem_shortClass (isConj_tStarG_iff.1 h1)
  rw [shortQGraph_adj_iff]
  refine ⟨hr, hs, ?_⟩
  rw [isShortCoord_iff_qCls, qCls_mul, add_comm, ← qCls_mul]
  exact isShortCoord_iff_qCls.1 h2

theorem diam_Gmat
    {x y : ConjVert tStarG} (hx : (x : Gmat) ∈ leechQ xmatG)
    (hy : (y : Gmat) ∈ leechQ xmatG) :
    x = y ∨ (twoAGraph tStarG).Adj x y ∨ ∃ w : ConjVert tStarG, (w : Gmat) ∈ leechQ xmatG ∧
      (twoAGraph tStarG).Adj x w ∧ (twoAGraph tStarG).Adj w y := by
  obtain ⟨r, hr, hxr⟩ := exists_short_of_mem_leechQ hx
  obtain ⟨s, hs, hys⟩ := exists_short_of_mem_leechQ hy
  have hx' : x = rv hr := Subtype.ext hxr
  have hy' : y = rv hs := Subtype.ext hys
  subst hx' hy'
  rcases shortQGraph_diam_le_two hr hs with h | h | ⟨t, ht1, ht2⟩
  · subst h
    exact Or.inl rfl
  · exact Or.inr (Or.inl ((adj_rv_iff hr hs).2 h))
  · exact Or.inr (Or.inr ⟨rv (isShortCoord_of_adj_right ht1), rhoG_mem_leechQ t,
      (adj_rv_iff hr _).2 ht1, (adj_rv_iff _ hs).2 ht2⟩)

theorem exists_lift_Gmat
    {r s : Q} (hr : IsShortCoord (coordOf r)) (hs : IsShortCoord (coordOf s))
    (hzs : s = r * zQ ∨ qL (qCls r + qCls s) = 1) {w : ConjVert tStarG}
    (hw : w ∈ (twoAGraph tStarG).commonNeighbors (rv hr) (rv hs)) :
    ∃ t, shortQGraph.Adj r t ∧ shortQGraph.Adj t s ∧ (w : Gmat) = rhoG t := by
  have ha2 : tStarG * tStarG = 1 := tStarG_mul_self
  obtain ⟨hw1, hw2⟩ := (SimpleGraph.mem_commonNeighbors _).1 hw
  rcases hzs with rfl | hq
  · obtain ⟨t, hrt, hwt⟩ := exists_lift_of_commonNeighbors ha2 (IsConj.refl tStarG) hr hw
    exact ⟨t, hrt, (shortQGraph_adj_mul_zQ_left.2 hrt).symm, hwt⟩
  · have hx2 : (rv hr : Gmat) * rv hr = 1 := conjVert_mul_self ha2 _
    have hy2 : (rv hs : Gmat) * rv hs = 1 := conjVert_mul_self ha2 _
    have hxy' : (rv hr : Gmat) * rv hs = rhoG (s * r) := (rhoG_mul s r).symm
    have hsq : (s * r) * (s * r) = zQ := by
      have h1 := sq_eq_zQ_pow (s * r)
      rw [qCls_mul, add_comm (qCls s) (qCls r), hq, pow_two] at h1
      rw [h1]
      exact pow_one zQ
    have hz4 : xmatG = (rv hr : Gmat) * rv hs * ((rv hr : Gmat) * rv hs) := by
      rw [hxy', ← rhoG_mul (s * r) (s * r), hsq]
      rfl
    have hv2 : ((rv (isShortCoord_mul_zQ_iff.2 hr) : ConjVert tStarG) : Gmat) =
        (rv hs : Gmat) * rv hr * rv hs := by
      show rhoG (r * zQ) = _
      rw [← rhoG_mul_xmatG r, hz4]
      calc (rv hr : Gmat) * ((rv hr : Gmat) * rv hs * ((rv hr : Gmat) * rv hs))
          = ((rv hr : Gmat) * rv hr) * ((rv hs : Gmat) * rv hr * rv hs) := by group
        _ = (rv hs : Gmat) * rv hr * rv hs := by rw [hx2, one_mul]
    have hwy : (w : Gmat) * rv hs = rv hs * w := (adj_comm ha2 hw2).symm
    have hwx : IsConj tStarG ((w : Gmat) * rv hr) := by
      have h1 := hw1.2
      rwa [adj_comm ha2 hw1] at h1
    have hconj : IsConj tStarG ((w : Gmat) * ((rv (isShortCoord_mul_zQ_iff.2 hr) :
        ConjVert tStarG) : Gmat)) := by
      rw [hv2]
      have e : (w : Gmat) * ((rv hs : Gmat) * rv hr * rv hs) =
          (rv hs : Gmat) * ((w : Gmat) * rv hr) * (rv hs : Gmat)⁻¹ := by
        rw [inv_eq_of_mul_eq_one_right hy2]
        calc (w : Gmat) * ((rv hs : Gmat) * rv hr * rv hs)
            = ((w : Gmat) * rv hs) * rv hr * rv hs := by group
          _ = ((rv hs : Gmat) * w) * rv hr * rv hs := by rw [hwy]
          _ = (rv hs : Gmat) * ((w : Gmat) * rv hr) * rv hs := by group
      rw [e]
      exact isConj_conj hwx _
    have hne : (w : Gmat) ≠ ((rv (isShortCoord_mul_zQ_iff.2 hr) : ConjVert tStarG) : Gmat) := by
      intro e
      apply ne_one_of_isConj_tStarG hconj
      rw [← e]
      exact conjVert_mul_self ha2 w
    have hwv : (twoAGraph tStarG).Adj w (rv (isShortCoord_mul_zQ_iff.2 hr)) :=
      adj_of_conj hne hconj
    have hmem : w ∈ (twoAGraph tStarG).commonNeighbors (rv hr)
        (rv (isShortCoord_mul_zQ_iff.2 hr)) :=
      (SimpleGraph.mem_commonNeighbors _).2 ⟨hw1, hwv.symm⟩
    obtain ⟨t, hrt, hwt⟩ := exists_lift_of_commonNeighbors ha2 (IsConj.refl tStarG) hr hmem
    have ht : IsShortCoord (coordOf t) := isShortCoord_of_adj_right hrt
    refine ⟨t, hrt, ?_, hwt⟩
    have hwt' : w = rv ht := Subtype.ext hwt
    rw [hwt'] at hw2
    exact ((adj_rv_iff hs ht).1 hw2).symm

theorem eq_or_mul_self_eq_of_mem_zpowers {H : Type*} [Group H] {z g : H}
    (hE : ExtraspecialData (leechQ z) z) (hg : g ∈ leechQ z) (hz : z ∈ Subgroup.zpowers g) :
    z = g ∨ g * g = z := by
  rcases hE.sq g hg with h | h
  · left
    rcases eq_one_or_eq_of_mem_zpowers_of_sq (by rw [pow_two]; exact h) hz with h1 | h1
    · exact absurd h1 hE.ne_one
    · exact h1
  · exact Or.inr h

theorem preconnected_commonNeighbors_rv
    {r s : Q} (hr : IsShortCoord (coordOf r))
    (hs : IsShortCoord (coordOf s)) (hz : xmatG ∈ Subgroup.zpowers (rhoG r * rhoG s)) :
    ((twoAGraph tStarG).induce ((twoAGraph tStarG).commonNeighbors (rv hr) (rv hs))).Preconnected
    := by
  have hE : ExtraspecialData (leechQ xmatG) xmatG := gmsF1Type_Gmat.2.extraspecialData
  have hg : rhoG r * rhoG s ∈ leechQ xmatG := by
    rw [← rhoG_mul s r]
    exact rhoG_mem_leechQ _
  have hzs : s = r * zQ ∨ qL (qCls r + qCls s) = 1 := by
    rcases eq_or_mul_self_eq_of_mem_zpowers hE hg hz with h | h
    · left
      have h1 : rhoG zQ = rhoG (s * r) := by
        rw [rhoG_mul s r]
        exact h
      have h2 : zQ = s * r := rhoG_injective h1
      have hrr : r⁻¹ = r :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact sq_eq_one_of_isShort hr)
      calc s = (s * r) * r⁻¹ := by rw [mul_inv_cancel_right]
        _ = zQ * r := by rw [← h2, hrr]
        _ = r * zQ := (Subgroup.mem_center_iff.1 CFSG.Monster.B.Short.zQ_mem_center r).symm
    · right
      have h1 : rhoG zQ = rhoG ((s * r) * (s * r)) := by
        rw [rhoG_mul (s * r) (s * r), rhoG_mul s r]
        exact h.symm
      have h2 : zQ = (s * r) * (s * r) := rhoG_injective h1
      have h3 := sq_eq_zQ_pow (s * r)
      rw [pow_two, ← h2, qCls_mul, add_comm (qCls s) (qCls r)] at h3
      rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (qL (qCls r + qCls s)) with h0 | h0
      · rw [h0, show (0 : ZMod 2).val = 0 from rfl, pow_zero] at h3
        exact absurd h3 zQ_ne_one
      · exact h0
  have hpre : (shortQGraph.induce (shortQGraph.commonNeighbors r s)).Preconnected := by
    rcases hzs with rfl | hq
    · exact preconnected_mu_Q_fibre hr
    · exact preconnected_mu_Q_three hr hs hq
  have hsh : ∀ t : shortQGraph.commonNeighbors r s, IsShortCoord (coordOf (t : Q)) := fun t =>
    isShortCoord_of_adj_right ((SimpleGraph.mem_commonNeighbors _).1 t.2).1
  let φ : shortQGraph.induce (shortQGraph.commonNeighbors r s) →g
      (twoAGraph tStarG).induce ((twoAGraph tStarG).commonNeighbors (rv hr) (rv hs)) :=
    { toFun := fun t => ⟨rv (hsh t), (SimpleGraph.mem_commonNeighbors _).2
        ⟨(adj_rv_iff hr (hsh t)).2 ((SimpleGraph.mem_commonNeighbors _).1 t.2).1,
          (adj_rv_iff hs (hsh t)).2 ((SimpleGraph.mem_commonNeighbors _).1 t.2).2⟩⟩
      map_rel' := fun {t t'} h => (adj_rv_iff (hsh t) (hsh t')).2 h }
  refine hpre.map φ fun w => ?_
  obtain ⟨t, h1, h2, hwt⟩ := exists_lift_Gmat hr hs hzs w.2
  exact ⟨⟨t, (SimpleGraph.mem_commonNeighbors _).2 ⟨h1, h2.symm⟩⟩,
    Subtype.ext (Subtype.ext hwt.symm)⟩

theorem mu_Gmat
    {x y : ConjVert tStarG} (hx : (x : Gmat) ∈ leechQ xmatG)
    (hy : (y : Gmat) ∈ leechQ xmatG) (hz : xmatG ∈ Subgroup.zpowers ((x : Gmat) * y)) :
    ((twoAGraph tStarG).induce ((twoAGraph tStarG).commonNeighbors x y)).Preconnected := by
  obtain ⟨r, hr, hxr⟩ := exists_short_of_mem_leechQ hx
  obtain ⟨s, hs, hys⟩ := exists_short_of_mem_leechQ hy
  have hx' : x = rv hr := Subtype.ext hxr
  have hy' : y = rv hs := Subtype.ext hys
  subst hx' hy'
  exact preconnected_commonNeighbors_rv hr hs hz

theorem leechGraphFacts_Gmat :
    LeechGraphFacts tStarG xmatG :=
  leechGraphFacts_of_base (fun _ _ hx hy => diam_Gmat hx hy) (fun _ _ hx hy hz => mu_Gmat hx hy hz)

end Gmat

end CFSG.Monster.Tri
