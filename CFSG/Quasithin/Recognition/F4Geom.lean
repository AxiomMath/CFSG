module

public import CFSG.Quasithin.Recognition.F4Basic
public import CFSG.Quasithin.Background.F3Geometry

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7

universe u w

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y] (c : α.Completion Y)

@[expose] def baseVert (b : Bool) : c.Γ := cond b c.lv c.xv

theorem vtype_baseVert (b : Bool) : CosetGeom.vtype (c.baseVert b) = b := by
  cases b <;> rfl

theorem stv_smul (g : c.G0) (u : c.Γ) : stv c (g • u) = conjSub (g : c.G0) (stv c u) :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g u

theorem exists_smul_eq_baseVert (u : c.Γ) :
    ∃ g : c.G0, g • c.baseVert (CosetGeom.vtype u) = u := by
  cases h : CosetGeom.vtype u
  · obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ h
    exact ⟨g, hg.symm⟩
  · obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ h
    exact ⟨g, hg.symm⟩

variable {c}

theorem nbPaths_smul {u : c.Γ} {n : ℕ} {q : GPath c.graph n} (hq : q ∈ GPath.nbPaths c.graph u n)
    (g : c.G0) : g • q ∈ GPath.nbPaths c.graph (g • u) n :=
  ⟨by show g • q 0 = g • u; rw [hq.1], GPath.smul_noBack hq.2⟩

theorem PathTrans.smul {u : c.Γ} {n : ℕ} (h : c.PathTrans u n) (g : c.G0) :
    c.PathTrans (g • u) n := by
  intro q q' hq hq'
  have e : ∀ r : GPath c.graph n, r ∈ GPath.nbPaths c.graph (g • u) n →
      g⁻¹ • r ∈ GPath.nbPaths c.graph u n := by
    intro r hr
    refine ⟨?_, GPath.smul_noBack hr.2⟩
    show g⁻¹ • r 0 = u
    rw [hr.1, inv_smul_smul]
  obtain ⟨k, hk1, hk2⟩ := h (g⁻¹ • q) (g⁻¹ • q') (e q hq) (e q' hq')
  refine ⟨g * k * g⁻¹, ?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, hk1]
  · rw [GPath.mul_smul', GPath.mul_smul', hk2, ← GPath.mul_smul', mul_inv_cancel,
      GPath.one_smul']

theorem pathTrans_smul_iff {u : c.Γ} {n : ℕ} (g : c.G0) :
    c.PathTrans (g • u) n ↔ c.PathTrans u n :=
  ⟨fun h => by simpa using h.smul g⁻¹, fun h => h.smul g⟩

theorem φ1_mem_G0 (a : α.G1) : c.φ1 a ∈ c.φ1.range ⊔ c.φ2.range :=
  Subgroup.mem_sup_left ⟨a, rfl⟩

theorem φ2_mem_G0 (a : α.G2) : c.φ2 a ∈ c.φ1.range ⊔ c.φ2.range :=
  Subgroup.mem_sup_right ⟨a, rfl⟩

@[expose] def f1 : α.G1 →* c.G0 := c.φ1.codRestrict _ (fun a => φ1_mem_G0 a)

@[expose] def f2 : α.G2 →* c.G0 := c.φ2.codRestrict _ (fun a => φ2_mem_G0 a)

@[simp] theorem coe_f1 (a : α.G1) : ((f1 (c := c) a : c.G0) : Y) = c.φ1 a := rfl

@[simp] theorem coe_f2 (a : α.G2) : ((f2 (c := c) a : c.G0) : Y) = c.φ2 a := rfl

theorem f1_smul_xv (a : α.G1) : f1 (c := c) a • c.xv = c.xv :=
  CosetGeom.smul_eq_of_mem_stab (by
    rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left]
    exact ⟨a, rfl⟩)

theorem f2_smul_lv (a : α.G2) : f2 (c := c) a • c.lv = c.lv :=
  CosetGeom.smul_eq_of_mem_stab (by
    rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right]
    exact ⟨a, rfl⟩)

theorem nbrs_xv_card (hc : c.IsFaithful) :
    Nat.card (CosetGeom.nbrs c.xv) = α.α1.range.index := by
  let _ : MulAction α.G1 c.Γ := MulAction.compHom c.Γ (f1 (c := c))
  have horb : MulAction.orbit α.G1 c.lv = CosetGeom.nbrs c.xv := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      show CosetGeom.graph _ _ _ |>.Adj c.xv (f1 (c := c) a • c.lv)
      rw [← f1_smul_xv a]
      exact (CosetGeom.smul_adj _).mpr CosetGeom.adj_γ₀_γ₁
    · intro hv
      obtain ⟨g, hg1, hg2⟩ := CosetGeom.stab_transitive_on_nbrs
        (show c.lv ∈ CosetGeom.nbrs c.xv from CosetGeom.adj_γ₀_γ₁) hv
      rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at hg1
      obtain ⟨a, ha⟩ := hg1
      refine ⟨a, ?_⟩
      show f1 (c := c) a • c.lv = v
      have : f1 (c := c) a = g := Subtype.ext ha
      rw [this, hg2]
  have hstab : MulAction.stabilizer α.G1 c.lv = α.α1.range := by
    ext a
    rw [MulAction.mem_stabilizer_iff]
    show f1 (c := c) a • c.lv = c.lv ↔ _
    constructor
    · intro h
      have h1 := CosetGeom.mem_stab_of_smul_eq h
      rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at h1
      have h2 : c.φ1 a ∈ c.φ1.range ⊓ c.φ2.range := ⟨⟨a, rfl⟩, h1⟩
      rw [c.inter] at h2
      obtain ⟨g, hg⟩ := h2
      refine ⟨g, hc.1 ?_⟩
      rw [c.comm1]
      exact hg
    · rintro ⟨g, rfl⟩
      apply CosetGeom.smul_eq_of_mem_stab
      rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right]
      show c.φ1 (α.α1 g) ∈ c.φ2.range
      rw [c.comm1]
      have : c.φ12 g ∈ c.φ1.range ⊓ c.φ2.range := by
        rw [c.inter]; exact ⟨g, rfl⟩
      exact this.2
  rw [← horb, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer α.G1 c.lv), hstab]
  rfl

theorem nbrs_lv_card (hc : c.IsFaithful) :
    Nat.card (CosetGeom.nbrs c.lv) = α.α2.range.index := by
  let _ : MulAction α.G2 c.Γ := MulAction.compHom c.Γ (f2 (c := c))
  have horb : MulAction.orbit α.G2 c.xv = CosetGeom.nbrs c.lv := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      show CosetGeom.graph _ _ _ |>.Adj c.lv (f2 (c := c) a • c.xv)
      rw [← f2_smul_lv a]
      exact (CosetGeom.smul_adj _).mpr CosetGeom.adj_γ₀_γ₁.symm
    · intro hv
      obtain ⟨g, hg1, hg2⟩ := CosetGeom.stab_transitive_on_nbrs
        (show c.xv ∈ CosetGeom.nbrs c.lv from CosetGeom.adj_γ₀_γ₁.symm) hv
      rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at hg1
      obtain ⟨a, ha⟩ := hg1
      refine ⟨a, ?_⟩
      show f2 (c := c) a • c.xv = v
      have : f2 (c := c) a = g := Subtype.ext ha
      rw [this, hg2]
  have hstab : MulAction.stabilizer α.G2 c.xv = α.α2.range := by
    ext a
    rw [MulAction.mem_stabilizer_iff]
    show f2 (c := c) a • c.xv = c.xv ↔ _
    constructor
    · intro h
      have h1 := CosetGeom.mem_stab_of_smul_eq h
      rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at h1
      have h2 : c.φ2 a ∈ c.φ1.range ⊓ c.φ2.range := ⟨h1, ⟨a, rfl⟩⟩
      rw [c.inter] at h2
      obtain ⟨g, hg⟩ := h2
      refine ⟨g, hc.2.2 ?_⟩
      rw [c.comm2]
      exact hg
    · rintro ⟨g, rfl⟩
      apply CosetGeom.smul_eq_of_mem_stab
      rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left]
      show c.φ2 (α.α2 g) ∈ c.φ1.range
      rw [c.comm2]
      have : c.φ12 g ∈ c.φ1.range ⊓ c.φ2.range := by
        rw [c.inter]; exact ⟨g, rfl⟩
      exact this.1
  rw [← horb, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer α.G2 c.xv), hstab]
  rfl

theorem two_lt_encard_nbrs [Finite Y] (hc : c.IsFaithful) (h1 : 2 ≤ α.qOne) (h2 : 2 ≤ α.qTwo) :
    2 < (CosetGeom.nbrs c.xv).encard ∧ 2 < (CosetGeom.nbrs c.lv).encard := by
  have e1 := nbrs_xv_card (c := c) hc
  have e2 := nbrs_lv_card (c := c) hc
  unfold RankTwoAmalgam.qOne at h1
  unfold RankTwoAmalgam.qTwo at h2
  have hfin1 : (CosetGeom.nbrs c.xv).Finite := Set.toFinite _
  have hfin2 : (CosetGeom.nbrs c.lv).Finite := Set.toFinite _
  have a1 : (CosetGeom.nbrs c.xv).encard = ((CosetGeom.nbrs c.xv).ncard : ℕ∞) :=
    (hfin1.cast_ncard_eq).symm
  have a2 : (CosetGeom.nbrs c.lv).encard = ((CosetGeom.nbrs c.lv).ncard : ℕ∞) :=
    (hfin2.cast_ncard_eq).symm
  have n1 : (CosetGeom.nbrs c.xv).ncard = α.α1.range.index := by
    rw [← Nat.card_coe_set_eq]; exact e1
  have n2 : (CosetGeom.nbrs c.lv).ncard = α.α2.range.index := by
    rw [← Nat.card_coe_set_eq]; exact e2
  refine ⟨?_, ?_⟩
  · rw [a1, n1]
    exact_mod_cast (by omega : 2 < α.α1.range.index)
  · rw [a2, n2]
    exact_mod_cast (by omega : 2 < α.α2.range.index)

theorem exists_nbr_ne [Finite Y] (hc : c.IsFaithful) (h1 : 2 ≤ α.qOne) (h2 : 2 ≤ α.qTwo)
    (v a b : c.Γ) : ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b := by
  obtain ⟨t1, t2⟩ := two_lt_encard_nbrs hc h1 h2
  exact CosetGeom.exists_nbr_ne t1 t2 v a b

@[expose] noncomputable def Qvert (Qx Ql : Subgroup c.G0) (u : c.Γ) : Subgroup c.G0 :=
  ⨆ (g : c.G0) (_ : g • c.baseVert (CosetGeom.vtype u) = u),
    conjSub g (cond (CosetGeom.vtype u) Ql Qx)

@[expose] def QNormalized (Qx Ql : Subgroup c.G0) : Prop :=
  ∀ (b : Bool) (h : c.G0), h • c.baseVert b = c.baseVert b →
    conjSub h (cond b Ql Qx) = cond b Ql Qx

theorem Qvert_eq_conjSub {Qx Ql : Subgroup c.G0} (hQ : QNormalized Qx Ql) {u : c.Γ} {g : c.G0}
    (hg : g • c.baseVert (CosetGeom.vtype u) = u) :
    c.Qvert Qx Ql u = conjSub g (cond (CosetGeom.vtype u) Ql Qx) := by
  refine le_antisymm (iSup₂_le fun g' hg' => ?_) (le_iSup₂ (f := fun (g : c.G0)
    (_ : g • c.baseVert (CosetGeom.vtype u) = u) => conjSub g (cond (CosetGeom.vtype u) Ql Qx)) g hg)
  have hh : (g⁻¹ * g') • c.baseVert (CosetGeom.vtype u) = c.baseVert (CosetGeom.vtype u) := by
    rw [mul_smul, hg']
    exact inv_smul_eq_iff.mpr hg.symm
  have := hQ _ _ hh
  calc conjSub g' (cond (CosetGeom.vtype u) Ql Qx)
      = conjSub (g * (g⁻¹ * g')) (cond (CosetGeom.vtype u) Ql Qx) := by rw [mul_inv_cancel_left]
    _ = conjSub g (conjSub (g⁻¹ * g') (cond (CosetGeom.vtype u) Ql Qx)) := conjSub_mul _ _ _
    _ = conjSub g (cond (CosetGeom.vtype u) Ql Qx) := by rw [this]
    _ ≤ _ := le_rfl

theorem Qvert_baseVert {Qx Ql : Subgroup c.G0} (hQ : QNormalized Qx Ql) (b : Bool) :
    c.Qvert Qx Ql (c.baseVert b) = cond b Ql Qx := by
  have h := Qvert_eq_conjSub hQ (u := c.baseVert b) (g := 1) (by
    rw [vtype_baseVert, one_smul])
  rw [h, vtype_baseVert, conjSub_one]

theorem Qvert_smul {Qx Ql : Subgroup c.G0} (hQ : QNormalized Qx Ql) (h : c.G0) (u : c.Γ) :
    c.Qvert Qx Ql (h • u) = conjSub h (c.Qvert Qx Ql u) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have hv : CosetGeom.vtype (h • u) = CosetGeom.vtype u := CosetGeom.vtype_smul h u
  have e1 := Qvert_eq_conjSub hQ hg
  have e2 : c.Qvert Qx Ql (h • u) = conjSub (h * g) (cond (CosetGeom.vtype u) Ql Qx) := by
    have hg2 : (h * g) • c.baseVert (CosetGeom.vtype (h • u)) = h • u := by
      rw [hv, mul_smul, hg]
    rw [Qvert_eq_conjSub hQ hg2, hv]
  rw [e2, e1, conjSub_mul]

end RankTwoAmalgam.Completion

end CFSG.Quasithin
