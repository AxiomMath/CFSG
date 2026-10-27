module

public import CFSG.Quasithin.Recognition.F4Geom
public import CFSG.Quasithin.Recognition.F4Paths
public import CFSG.Quasithin.Background.F3Compare

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7

universe u w w'

namespace RankTwoAmalgam

variable (α : RankTwoAmalgam.{u})

@[expose] def xi1 : α.G1 →* ↥(α.Ghat1 ⊔ α.Ghat2) :=
  (Amalgam.ξ α.toAmalgam RankTwoIndex.one).codRestrict _
    (fun a => Subgroup.mem_sup_left ⟨a, rfl⟩)

@[expose] def xi2 : α.G2 →* ↥(α.Ghat1 ⊔ α.Ghat2) :=
  (Amalgam.ξ α.toAmalgam RankTwoIndex.two).codRestrict _
    (fun a => Subgroup.mem_sup_right ⟨a, rfl⟩)

@[simp] theorem coe_xi1 (a : α.G1) :
    ((α.xi1 a : ↥(α.Ghat1 ⊔ α.Ghat2)) : α.Ghat) = Amalgam.ξ α.toAmalgam RankTwoIndex.one a := rfl

@[simp] theorem coe_xi2 (a : α.G2) :
    ((α.xi2 a : ↥(α.Ghat1 ⊔ α.Ghat2)) : α.Ghat) = Amalgam.ξ α.toAmalgam RankTwoIndex.two a := rfl

theorem xi1_smul_xhat (a : α.G1) : α.xi1 a • Completion.xhat (α := α) = Completion.xhat := by
  apply CosetGeom.smul_eq_of_mem_stab
  rw [CosetGeom.stab_γ₀ (G₀ := α.Ghat1 ⊔ α.Ghat2) (G₂ := α.Ghat2) le_sup_left]
  exact ⟨a, rfl⟩

theorem xi2_smul_lhat (a : α.G2) : α.xi2 a • Completion.lhat (α := α) = Completion.lhat := by
  apply CosetGeom.smul_eq_of_mem_stab
  rw [CosetGeom.stab_γ₁ (G₀ := α.Ghat1 ⊔ α.Ghat2) (G₁ := α.Ghat1) le_sup_right]
  exact ⟨a, rfl⟩

@[expose] def gam1 {n : ℕ} (q : GPath α.graphHat n) : Subgroup α.G1 :=
  (q.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)).comap α.xi1

@[expose] def gam2 {n : ℕ} (q : GPath α.graphHat n) : Subgroup α.G2 :=
  (q.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)).comap α.xi2

theorem mem_gam1 {n : ℕ} {q : GPath α.graphHat n} {a : α.G1} :
    a ∈ α.gam1 q ↔ α.xi1 a ∈ q.stabPath := Iff.rfl

theorem mem_gam2 {n : ℕ} {q : GPath α.graphHat n} {a : α.G2} :
    a ∈ α.gam2 q ↔ α.xi2 a ∈ q.stabPath := Iff.rfl

namespace Completion

variable {α} {Y : Type w} [Group Y] (c : α.Completion Y) (hc : c.IsFaithful)

theorem Θ_xhat : c.Θ hc xhat = c.xv := (c.coverData hc).Θ_γ₀

theorem Θ_lhat : c.Θ hc lhat = c.lv := (c.coverData hc).Θ_γ₁

theorem theta0_xi1 (a : α.G1) : c.theta0 hc (α.xi1 a) = f1 (c := c) a :=
  Subtype.ext (c.theta_ξ1 a)

theorem theta0_xi2 (a : α.G2) : c.theta0 hc (α.xi2 a) = f2 (c := c) a :=
  Subtype.ext (c.theta_ξ2 a)

theorem mem_stabPath_f1_iff {n : ℕ} (q : GPath α.graphHat n) (hq : q 0 = xhat) (a : α.G1) :
    f1 (c := c) a ∈ ((c.graphCovering hc).pathMap q).stabPath ↔ a ∈ α.gam1 q := by
  have h := (c.graphCovering hc).mem_stabPath_iff (c.stabIso hc xhat) q hq (α.xi1_smul_xhat a)
  rw [mem_gam1, h]
  show f1 (c := c) a ∈ _ ↔ c.theta0 hc (α.xi1 a) ∈ _
  rw [theta0_xi1]

theorem mem_stabPath_f2_iff {n : ℕ} (q : GPath α.graphHat n) (hq : q 0 = lhat) (a : α.G2) :
    f2 (c := c) a ∈ ((c.graphCovering hc).pathMap q).stabPath ↔ a ∈ α.gam2 q := by
  have h := (c.graphCovering hc).mem_stabPath_iff (c.stabIso hc lhat) q hq (α.xi2_smul_lhat a)
  rw [mem_gam2, h]
  show f2 (c := c) a ∈ _ ↔ c.theta0 hc (α.xi2 a) ∈ _
  rw [theta0_xi2]

theorem f1_injective (hc : c.IsFaithful) : Function.Injective (f1 (c := c)) := fun a b h =>
  hc.1 (by simpa using congrArg Subtype.val h)

theorem f2_injective (hc : c.IsFaithful) : Function.Injective (f2 (c := c)) := fun a b h =>
  hc.2.2 (by simpa using congrArg Subtype.val h)

theorem stv_xv_le_range_f1 : stv c c.xv ≤ (f1 (c := c)).range := by
  intro g hg
  have h := CosetGeom.mem_stab_of_smul_eq (MulAction.mem_stabilizer_iff.mp hg)
  rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, Subtype.ext ha⟩

theorem stv_lv_le_range_f2 : stv c c.lv ≤ (f2 (c := c)).range := by
  intro g hg
  have h := CosetGeom.mem_stab_of_smul_eq (MulAction.mem_stabilizer_iff.mp hg)
  rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, Subtype.ext ha⟩

theorem comap_f1_stabPath {n : ℕ} (q : GPath α.graphHat n) (hq : q 0 = xhat) :
    (((c.graphCovering hc).pathMap q).stabPath : Subgroup c.G0).comap (f1 (c := c)) = α.gam1 q := by
  ext a
  exact mem_stabPath_f1_iff c hc q hq a

theorem comap_f2_stabPath {n : ℕ} (q : GPath α.graphHat n) (hq : q 0 = lhat) :
    (((c.graphCovering hc).pathMap q).stabPath : Subgroup c.G0).comap (f2 (c := c)) = α.gam2 q := by
  ext a
  exact mem_stabPath_f2_iff c hc q hq a

theorem comap_f1_stv_inf {n : ℕ} (q : GPath α.graphHat n) (hq : q 0 = xhat) (h1 : 1 ≤ n) :
    (stv c c.xv ⊓ stv c ((c.graphCovering hc).pathMap q 1)).comap (f1 (c := c)) =
      α.gam1 (q.take 1 h1) := by
  have h0 : (c.graphCovering hc).pathMap q 0 = c.xv := by
    rw [GraphCovering.pathMap_apply, hq]; exact Θ_xhat c hc
  have e : stv c c.xv ⊓ stv c ((c.graphCovering hc).pathMap q 1) =
      ((((c.graphCovering hc).pathMap (q.take 1 h1)).stabPath : Subgroup c.G0)) := by
    rw [(c.graphCovering hc).pathMap_take q 1 h1, GPath.stabPath_take_one, h0]
  rw [e]
  exact comap_f1_stabPath c hc (q.take 1 h1) (by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le 1), hq])

theorem comap_f2_stv_inf {n : ℕ} (q : GPath α.graphHat n) (hq : q 0 = lhat) (h1 : 1 ≤ n) :
    (stv c c.lv ⊓ stv c ((c.graphCovering hc).pathMap q 1)).comap (f2 (c := c)) =
      α.gam2 (q.take 1 h1) := by
  have h0 : (c.graphCovering hc).pathMap q 0 = c.lv := by
    rw [GraphCovering.pathMap_apply, hq]; exact Θ_lhat c hc
  have e : stv c c.lv ⊓ stv c ((c.graphCovering hc).pathMap q 1) =
      ((((c.graphCovering hc).pathMap (q.take 1 h1)).stabPath : Subgroup c.G0)) := by
    rw [(c.graphCovering hc).pathMap_take q 1 h1, GPath.stabPath_take_one, h0]
  rw [e]
  exact comap_f2_stabPath c hc (q.take 1 h1) (by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le 1), hq])

theorem pathTrans_of_base {n : ℕ} (hx : c.PathTrans c.xv n) (hl : c.PathTrans c.lv n) (a : c.Γ) :
    c.PathTrans a n := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c a
  rw [← hg, pathTrans_smul_iff]
  cases hv : CosetGeom.vtype a
  · exact hx
  · exact hl

variable {Yb : Type w'} [Group Yb]

include hc in
theorem pathTrans_xv_transfer (ι : α.Completion Yb) (hι : ι.IsFaithful) (n : ℕ)
    (h : ι.PathTrans ι.xv n) : c.PathTrans c.xv n := by
  have key : ∀ (u : ι.Γ) (u' : c.Γ), ι.Θ hι xhat = u → c.Θ hc xhat = u' → ι.PathTrans u n →
      c.PathTrans u' n := by
    rintro u u' rfl rfl h
    exact fun p₁ p₂ h₁ h₂ => lemma_F34_3 ι c hι hc xhat n h p₁ p₂ h₁ h₂
  exact key ι.xv c.xv (Θ_xhat ι hι) (Θ_xhat c hc) h

include hc in
theorem pathTrans_lv_transfer (ι : α.Completion Yb) (hι : ι.IsFaithful) (n : ℕ)
    (h : ι.PathTrans ι.lv n) : c.PathTrans c.lv n := by
  have key : ∀ (u : ι.Γ) (u' : c.Γ), ι.Θ hι lhat = u → c.Θ hc lhat = u' → ι.PathTrans u n →
      c.PathTrans u' n := by
    rintro u u' rfl rfl h
    exact fun p₁ p₂ h₁ h₂ => lemma_F34_3 ι c hι hc lhat n h p₁ p₂ h₁ h₂
  exact key ι.lv c.lv (Θ_lhat ι hι) (Θ_lhat c hc) h

include hc in
theorem pathTrans_transfer (ι : α.Completion Yb) (hι : ι.IsFaithful) (n : ℕ)
    (h : ∀ u : ι.Γ, ι.PathTrans u n) (a : c.Γ) : c.PathTrans a n :=
  pathTrans_of_base c (pathTrans_xv_transfer c hc ι hι n (h _))
    (pathTrans_lv_transfer c hc ι hι n (h _)) a

end Completion

end RankTwoAmalgam

namespace GraphCovering

variable {Vh : Type*} {V : Type*} {V₂ : Type*} {Γh : SimpleGraph Vh} {Γ : SimpleGraph V}
  {Γ₂ : SimpleGraph V₂} {θ : Vh → V} {θ₂ : Vh → V₂} (hθ : GraphCovering Γh Γ θ)
  (hθ₂ : GraphCovering Γh Γ₂ θ₂)

theorem psi_length (uh : Vh) (p : PathSet Γ (θ uh)) : (psi hθ hθ₂ uh p).1 = p.1 := by
  obtain ⟨ph, rfl⟩ := (hθ.pathSetEquiv uh).surjective p
  have e : psi hθ hθ₂ uh (hθ.pathSetEquiv uh ph) = hθ₂.pathSetEquiv uh ph := by simp [psi]
  rw [e]
  rfl

theorem psi_noBack_iff (uh : Vh) (p : PathSet Γ (θ uh)) :
    (psi hθ hθ₂ uh p).NoBack ↔ p.NoBack := by
  obtain ⟨ph, rfl⟩ := (hθ.pathSetEquiv uh).surjective p
  have e : psi hθ hθ₂ uh (hθ.pathSetEquiv uh ph) = hθ₂.pathSetEquiv uh ph := by simp [psi]
  rw [e]
  show (hθ₂.pathMap ph.2.1).NoBack ↔ (hθ.pathMap ph.2.1).NoBack
  rw [hθ₂.noBack_pathMap_iff, hθ.noBack_pathMap_iff]

end GraphCovering

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y] {Yb : Type w'} [Group Yb]

theorem lemma_F46_3_x (ι : α.Completion Yb) (c : α.Completion Y) (hι : ι.IsFaithful)
    (hc : c.IsFaithful) :
    ∃ q : PermQuasiEquiv (stv ι ι.xv) (PathSet ι.graph ι.xv) (stv c c.xv) (PathSet c.graph c.xv),
      (∀ (a : α.G1) (g : stv ι ι.xv) (g' : stv c c.xv), (g : ι.G0) = f1 (c := ι) a →
        (g' : c.G0) = f1 (c := c) a → q.grp g = g') ∧
      (∀ p, (q.set p).1 = p.1) ∧ (∀ p, (q.set p).NoBack ↔ p.NoBack) := by
  have key : ∀ (u : ι.Γ) (u' : c.Γ), ι.Θ hι xhat = u → c.Θ hc xhat = u' →
      ∃ q : PermQuasiEquiv (stv ι u) (PathSet ι.graph u) (stv c u') (PathSet c.graph u'),
        (∀ (a : α.G1) (g : stv ι u) (g' : stv c u'), (g : ι.G0) = f1 (c := ι) a →
          (g' : c.G0) = f1 (c := c) a → q.grp g = g') ∧
        (∀ p, (q.set p).1 = p.1) ∧ (∀ p, (q.set p).NoBack ↔ p.NoBack) := by
    rintro u u' rfl rfl
    refine ⟨lemma_F34_1 ι c hι hc xhat, ?_, ?_, ?_⟩
    · intro a g g' hg hg'
      have h1 : (((g : ι.G0)) : Yb) = ι.φ1 a := by rw [hg]; rfl
      have h2 := stabComp_x ι c hι hc a g h1
      apply Subtype.ext
      apply Subtype.ext
      rw [hg']
      exact h2
    · intro p
      exact GraphCovering.psi_length (ι.graphCovering hι) (c.graphCovering hc) xhat p
    · intro p
      exact GraphCovering.psi_noBack_iff (ι.graphCovering hι) (c.graphCovering hc) xhat p
  exact key ι.xv c.xv (Θ_xhat ι hι) (Θ_xhat c hc)

theorem lemma_F46_3_l (ι : α.Completion Yb) (c : α.Completion Y) (hι : ι.IsFaithful)
    (hc : c.IsFaithful) :
    ∃ q : PermQuasiEquiv (stv ι ι.lv) (PathSet ι.graph ι.lv) (stv c c.lv) (PathSet c.graph c.lv),
      (∀ (a : α.G2) (g : stv ι ι.lv) (g' : stv c c.lv), (g : ι.G0) = f2 (c := ι) a →
        (g' : c.G0) = f2 (c := c) a → q.grp g = g') ∧
      (∀ p, (q.set p).1 = p.1) ∧ (∀ p, (q.set p).NoBack ↔ p.NoBack) := by
  have key : ∀ (u : ι.Γ) (u' : c.Γ), ι.Θ hι lhat = u → c.Θ hc lhat = u' →
      ∃ q : PermQuasiEquiv (stv ι u) (PathSet ι.graph u) (stv c u') (PathSet c.graph u'),
        (∀ (a : α.G2) (g : stv ι u) (g' : stv c u'), (g : ι.G0) = f2 (c := ι) a →
          (g' : c.G0) = f2 (c := c) a → q.grp g = g') ∧
        (∀ p, (q.set p).1 = p.1) ∧ (∀ p, (q.set p).NoBack ↔ p.NoBack) := by
    rintro u u' rfl rfl
    refine ⟨lemma_F34_1 ι c hι hc lhat, ?_, ?_, ?_⟩
    · intro a g g' hg hg'
      have h1 : (((g : ι.G0)) : Yb) = ι.φ2 a := by rw [hg]; rfl
      have h2 := stabComp_l ι c hι hc a g h1
      apply Subtype.ext
      apply Subtype.ext
      rw [hg']
      exact h2
    · intro p
      exact GraphCovering.psi_length (ι.graphCovering hι) (c.graphCovering hc) lhat p
    · intro p
      exact GraphCovering.psi_noBack_iff (ι.graphCovering hι) (c.graphCovering hc) lhat p
  exact key ι.lv c.lv (Θ_lhat ι hι) (Θ_lhat c hc)

end Completion

end RankTwoAmalgam

end CFSG.Quasithin
