module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoPtLoc

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Open

universe u v

variable {X : Type u} [Group X] {V : Type v} [MulAction X V] {Γ : SimpleGraph V}

variable [GraphAction X Γ]

namespace PtLoc

variable {a b₀ w₀ : V} (L : PtLoc X Γ a b₀ w₀) (hP : IsGenPolygon Γ 8)

include L hP

theorem pathTrans {q q' : GPath Γ 8} (hq : q ∈ GPath.nbPaths Γ a 8)
    (hq' : q' ∈ GPath.nbPaths Γ a 8) : ∃ g : X, g • a = a ∧ g • q = q' := by
  obtain ⟨h, hha, hhq⟩ := L.orb _ (end_dist hP le_rfl hq)
  obtain ⟨h', hha', hhq'⟩ := L.orb _ (end_dist hP le_rfl hq')
  have hh1 : h⁻¹ • a = a := by rw [inv_smul_eq_iff, hha]
  have hh1' : h'⁻¹ • a = a := by rw [inv_smul_eq_iff, hha']
  have hs : h⁻¹ • q ∈ GPath.nbPaths Γ a 8 := smul_mem_nbPaths hq hh1
  have hs' : h'⁻¹ • q' ∈ GPath.nbPaths Γ a 8 := smul_mem_nbPaths hq' hh1'
  have hs8 : (h⁻¹ • q) 8 = b₀ := by
    rw [GPath.smul_apply, inv_smul_eq_iff, hhq]
  have hs'8 : (h'⁻¹ • q') 8 = b₀ := by
    rw [GPath.smul_apply, inv_smul_eq_iff, hhq']
  have a1 : Γ.Adj a ((h⁻¹ • q) 1) := by
    have := (h⁻¹ • q).adj 0 (by norm_num)
    rwa [hs.1] at this
  have a2 : Γ.Adj a ((h'⁻¹ • q') 1) := by
    have := (h'⁻¹ • q').adj 0 (by norm_num)
    rwa [hs'.1] at this
  obtain ⟨k₁, hk₁a, hk₁b, hk₁w⟩ := L.trans _ a1
  obtain ⟨k₂, hk₂a, hk₂b, hk₂w⟩ := L.trans _ a2
  have hk1a : k₁⁻¹ • a = a := by rw [inv_smul_eq_iff, hk₁a]
  have hk1b : k₁⁻¹ • b₀ = b₀ := by rw [inv_smul_eq_iff, hk₁b]
  have hka : (k₂ * k₁⁻¹) • a = a := by rw [mul_smul, hk1a, hk₂a]
  have hk : (k₂ * k₁⁻¹) • (h⁻¹ • q) = h'⁻¹ • q' := by
    refine eq_of_first_last hP (smul_mem_nbPaths hs hka) hs' ?_ ?_
    · rw [GPath.smul_apply, mul_smul, ← hk₁w, inv_smul_smul, hk₂w]
    · rw [GPath.smul_apply, hs8, hs'8, mul_smul, hk1b, hk₂b]
  refine ⟨h' * (k₂ * k₁⁻¹) * h⁻¹, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hh1, hka, hha']
  · rw [GPath.mul_smul', GPath.mul_smul', hk, ← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']

omit [GraphAction X Γ] in
theorem base_path : ∃ r ∈ GPath.nbPaths Γ a 8, r 1 = w₀ ∧ r 8 = b₀ :=
  exists_base_path hP L.adj L.dist

theorem nontriv {r : GPath Γ 8} (hr : r ∈ GPath.nbPaths Γ a 8) :
    ∃ g ∈ (r.stabPath : Subgroup X), ∃ w, Γ.Adj a w ∧ g • w ≠ w := by
  obtain ⟨p₀, hp₀, hp₁, hp₈⟩ := L.base_path hP
  obtain ⟨h, hha, hhp⟩ := L.pathTrans hP hp₀ hr
  obtain ⟨k, hka, hkb, hkw, w, hw, hkwm⟩ := L.moves w₀ L.adj
  have hk : k ∈ (p₀.stabPath : Subgroup X) :=
    mem_stabPath_of_fix hP hp₀ hka (by rw [hp₁]; exact hkw) (by rw [hp₈]; exact hkb)
  refine ⟨h * k * h⁻¹, ?_, h • w, ?_, ?_⟩
  · rw [← hhp, GPath.stabPath_smul]
    exact mul_mem_conjSub hk
  · have := (GraphAction.adj_smul h a w).mpr hw
    rwa [hha] at this
  · rw [mul_smul, mul_smul, inv_smul_smul]
    intro hcon
    exact hkwm (smul_left_cancel h hcon)

theorem noFix {p : GPath Γ 8} (hp : p ∈ GPath.nbPaths Γ a 8) {y : V} (hy : Γ.Adj (p 8) y)
    (hne : y ≠ p 7) : ¬ ∀ g ∈ (p.stabPath : Subgroup X), g • y = y := by
  obtain ⟨p₀, hp₀, hp₁, hp₈⟩ := L.base_path hP
  obtain ⟨h, hha, hhp⟩ := L.pathTrans hP hp₀ hp
  obtain ⟨k, hka, hkb, hkw, y₀, hy₀, hky₀, hun⟩ := L.exact
  have hk : k ∈ (p₀.stabPath : Subgroup X) :=
    mem_stabPath_of_fix hP hp₀ hka (by rw [hp₁]; exact hkw) (by rw [hp₈]; exact hkb)
  have hp7 : p₀ 7 = y₀ := by
    refine hun _ ?_ (hk 7 (by norm_num))
    have := (p₀.adj 7 (by norm_num)).symm
    rwa [show 7 + 1 = 8 from rfl, hp₈] at this
  intro hall
  have hy' : Γ.Adj b₀ (h⁻¹ • y) := by
    have := (GraphAction.adj_smul h⁻¹ (p 8) y).mpr hy
    rwa [← hhp, GPath.smul_apply, inv_smul_smul, hp₈] at this
  have hne' : h⁻¹ • y ≠ y₀ := by
    rw [← hp7]
    intro hcon
    apply hne
    rw [← hhp, GPath.smul_apply]
    exact (inv_smul_eq_iff.mp hcon)
  have hg : h * k * h⁻¹ ∈ (p.stabPath : Subgroup X) := by
    rw [← hhp, GPath.stabPath_smul]
    exact mul_mem_conjSub hk
  have := hall _ hg
  rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul] at this
  exact hne' (hun _ hy' this)

theorem transPair {lab : ZMod 5 → V} (A : AffLab X Γ a lab) {p q : GPath Γ 8}
    (hp : p ∈ GPath.nbPaths Γ a 8) (hq : q ∈ GPath.nbPaths Γ a 8) (hpq : p 1 ≠ q 1) {y y' : V}
    (hy : Γ.Adj a y) (hy' : Γ.Adj a y') :
    ∃ g ∈ ((p.stabPath : Subgroup X) ⊔ q.stabPath), g • y = y' := by
  obtain ⟨g₁, hg₁, w₁, hw₁, hw₁m⟩ := L.nontriv hP hp
  obtain ⟨g₂, hg₂, w₂, hw₂, hw₂m⟩ := L.nontriv hP hq
  have ha1 : g₁ • a = a := by simpa [hp.1] using hg₁ 0 (Nat.zero_le _)
  have ha2 : g₂ • a = a := by simpa [hq.1] using hg₂ 0 (Nat.zero_le _)
  have hp1 : Γ.Adj a (p 1) := by
    have := p.adj 0 (by norm_num)
    rwa [hp.1] at this
  have hq1 : Γ.Adj a (q 1) := by
    have := q.adj 0 (by norm_num)
    rwa [hq.1] at this
  obtain ⟨g, hgc, hgy⟩ := A.pair ha1 ha2 hp1 hq1 hpq (hg₁ 1 (by norm_num)) (hg₂ 1 (by norm_num))
    ⟨w₁, hw₁, hw₁m⟩ ⟨w₂, hw₂, hw₂m⟩ hy hy'
  refine ⟨g, ?_, hgy⟩
  have hle : Subgroup.closure {g₁, g₂} ≤ (p.stabPath : Subgroup X) ⊔ q.stabPath := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_left hg₁
    · exact Subgroup.mem_sup_right hg₂
  exact hle hgc

end PtLoc

end CFSG.Quasithin.TitsGeo
