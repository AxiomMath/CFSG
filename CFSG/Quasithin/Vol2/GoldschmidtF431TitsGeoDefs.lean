module

public import CFSG.Quasithin.Recognition.F4Basic
public import CFSG.Quasithin.Recognition.F4Paths

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]

@[expose] def NoFixEnd (c : α.Completion Y) (m : ℕ) (a : c.Γ) : Prop :=
  ∀ p ∈ GPath.nbPaths c.graph a m, ∀ y : c.Γ, c.graph.Adj (p m) y → y ≠ p (m - 1) →
    ¬ ∀ g ∈ (p.stabPath : Subgroup c.G0), g • y = y

@[expose] def TransPair (c : α.Completion Y) (m : ℕ) (a : c.Γ) : Prop :=
  ∀ p ∈ GPath.nbPaths c.graph a m, ∀ q ∈ GPath.nbPaths c.graph a m, p 1 ≠ q 1 →
    ∀ y y' : c.Γ, c.graph.Adj a y → c.graph.Adj a y' →
      ∃ g ∈ ((p.stabPath : Subgroup c.G0) ⊔ q.stabPath), g • y = y'

structure TitsHyp (c : α.Completion Y) (k : ℕ) : Prop where
  faithful : c.IsFaithful
  thick1 : 2 ≤ α.qOne
  thick2 : 2 ≤ α.qTwo
  hk : 1 ≤ k
  even : Even k
  transPt : ∀ a : c.Γ, CosetGeom.vtype a = false → c.PathTrans a (k + 2)
  transLn : ∀ a : c.Γ, CosetGeom.vtype a = true → c.PathTrans a (k + 1)
  noFix : ∀ a : c.Γ, CosetGeom.vtype a = false → NoFixEnd c (k + 2) a
  pair : ∀ a : c.Γ, TransPair c (k + 2) a

section Smul

variable {c : α.Completion Y} {m : ℕ}

theorem noFixEnd_smul {a : c.Γ} (h : NoFixEnd c m a) (g : c.G0) : NoFixEnd c m (g • a) := by
  intro p hp y hy hne hall
  have hp' : g⁻¹ • p ∈ GPath.nbPaths c.graph a m := by
    refine ⟨?_, GPath.smul_noBack hp.2⟩
    show g⁻¹ • p 0 = a
    rw [hp.1, inv_smul_smul]
  refine h _ hp' (g⁻¹ • y) ?_ ?_ ?_
  · show c.graph.Adj (g⁻¹ • p m) (g⁻¹ • y)
    exact (GraphAction.adj_smul g⁻¹ _ _).mpr hy
  · intro e
    apply hne
    have := congrArg (g • ·) e
    simpa using this
  · intro k hk
    have e : p = g • (g⁻¹ • p) := by rw [← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
    have h1 : g * k * g⁻¹ ∈ (p.stabPath : Subgroup c.G0) := by
      rw [e, GPath.stabPath_smul]
      exact mul_mem_conjSub hk
    have h2 := hall _ h1
    rw [mul_smul, mul_smul] at h2
    exact (smul_eq_iff_eq_inv_smul g).mp h2

theorem transPair_smul {a : c.Γ} (h : TransPair c m a) (g : c.G0) : TransPair c m (g • a) := by
  intro p hp q hq hpq y y' hy hy'
  have e : ∀ r : GPath c.graph m, r ∈ GPath.nbPaths c.graph (g • a) m →
      g⁻¹ • r ∈ GPath.nbPaths c.graph a m := by
    intro r hr
    refine ⟨?_, GPath.smul_noBack hr.2⟩
    show g⁻¹ • r 0 = a
    rw [hr.1, inv_smul_smul]
  have hadj : ∀ z : c.Γ, c.graph.Adj (g • a) z → c.graph.Adj a (g⁻¹ • z) := fun z hz => by
    have := (GraphAction.adj_smul g⁻¹ _ _).mpr hz
    simpa using this
  obtain ⟨k, hk, hky⟩ := h _ (e p hp) _ (e q hq) (by
    intro h1
    apply hpq
    have := congrArg (g • ·) h1
    simpa using this) (g⁻¹ • y) (g⁻¹ • y') (hadj y hy) (hadj y' hy')
  refine ⟨g * k * g⁻¹, ?_, ?_⟩
  · have e1 : (p.stabPath : Subgroup c.G0) = conjSub g (g⁻¹ • p).stabPath := by
      rw [← GPath.stabPath_smul, ← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
    have e2 : (q.stabPath : Subgroup c.G0) = conjSub g (g⁻¹ • q).stabPath := by
      rw [← GPath.stabPath_smul, ← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
    have h3 : g * k * g⁻¹ ∈ conjSub g ((g⁻¹ • p).stabPath ⊔ (g⁻¹ • q).stabPath) :=
      mul_mem_conjSub hk
    rwa [conjSub_sup, ← e1, ← e2] at h3
  · rw [mul_smul, mul_smul, hky]
    simp

end Smul

end CFSG.Quasithin.TitsGeo
