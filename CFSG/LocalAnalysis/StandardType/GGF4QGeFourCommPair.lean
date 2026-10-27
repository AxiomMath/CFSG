module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2
import CFSG.LocalAnalysis.StandardType.GGF4CommPair
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem commute_rankOneFamily_of_exists_conj {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A}
    {X H : Subgroup G} (hAH : A ≤ ggAutomizer H Bs) (S : MulAut ↥Bs → Subgroup G)
    (hagree : ∀ t ∈ ggAutomizer X Bs, t ∈ ggCoxRefl M e → S t = ggRankOneIn X Bs t)
    (hequiv : ∀ h ∈ H, h ∈ Subgroup.normalizer (Bs : Set G) → ∀ g : MulAut ↥Bs,
      (∀ b : ↥Bs, ((g b : ↥Bs) : G) = h * b * h⁻¹) → ∀ t ∈ ggCoxRefl M e,
        S (g * t * g⁻¹) = (S t).map (MulAut.conj h).toMonoidHom)
    {u r' : MulAut ↥Bs} (hu : u ∈ ggCoxRefl M e) (hr' : r' ∈ ggCoxRefl M e)
    (hg : ∃ g : MulAut ↥Bs, g ∈ A ∧
      g * u * g⁻¹ ∈ ggAutomizer X Bs ∧ g * r' * g⁻¹ ∈ ggAutomizer X Bs ∧
      g * u * g⁻¹ ∈ ggCoxRefl M e ∧ g * r' * g⁻¹ ∈ ggCoxRefl M e ∧
      ∀ a ∈ ggRankOneIn X Bs (g * u * g⁻¹), ∀ b ∈ ggRankOneIn X Bs (g * r' * g⁻¹),
        a * b = b * a) :
    ∀ a ∈ S u, ∀ b ∈ S r', a * b = b * a := by
  obtain ⟨g, hgA, huX, hrX, huR, hrR, hgc⟩ := hg
  obtain ⟨h, hhH, hhN, hgh⟩ := mem_ggAutomizer_iff.mp (hAH hgA)
  have e₁ := hequiv h hhH hhN g hgh u hu
  have e₂ := hequiv h hhH hhN g hgh r' hr'
  rw [hagree _ huX huR] at e₁
  rw [hagree _ hrX hrR] at e₂
  intro a ha b hb
  have ha' : h * a * h⁻¹ ∈ ggRankOneIn X Bs (g * u * g⁻¹) := by
    rw [e₁]
    exact ⟨a, ha, by simp⟩
  have hb' : h * b * h⁻¹ ∈ ggRankOneIn X Bs (g * r' * g⁻¹) := by
    rw [e₂]
    exact ⟨b, hb, by simp⟩
  have hab := hgc _ ha' _ hb'
  have hconj : h * (a * b) * h⁻¹ = h * (b * a) * h⁻¹ := by
    calc h * (a * b) * h⁻¹ = h * a * h⁻¹ * (h * b * h⁻¹) := by group
      _ = h * b * h⁻¹ * (h * a * h⁻¹) := hab
      _ = h * (b * a) * h⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel hconj)

theorem exists_conj_commPair_mixed_of_label2 {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {ι' : Type} {M' : CoxeterMatrix ι'}
    (ε : M'.Group ≃* ↥(ggAutomizer X Bs))
    (hεrefl : ∀ i, GGIsReflection p ((ε (M'.simple i) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (σ : Fin 3 ≃ ι') (hM : ∀ k l, M' (σ k) (σ l) = CoxeterMatrix.B 3 k l)
    (hlab : ∀ (w₀ : CoxeterMatrix.F₄.Group) (i₀ j₀ : Fin 4),
      ((e (w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
      ((e (w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
      CoxeterMatrix.F₄ i₀ j₀ = 2 →
      ∀ a ∈ ggRankOneIn X Bs ((e (w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹) : ↥A) : MulAut ↥Bs),
      ∀ b ∈ ggRankOneIn X Bs ((e (w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹) : ↥A) : MulAut ↥Bs),
        a * b = b * a)
    (w w' : CoxeterMatrix.F₄.Group) (i j : Fin 4)
    (hij : i.val < 2 ↔ 2 ≤ j.val) {u r' : MulAut ↥Bs}
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hr' : r' = ((e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹) : ↥A) : MulAut ↥Bs))
    (hcomm : u * r' = r' * u) :
    ∃ g : MulAut ↥Bs, g ∈ A ∧
      g * u * g⁻¹ ∈ ggAutomizer X Bs ∧ g * r' * g⁻¹ ∈ ggAutomizer X Bs ∧
      g * u * g⁻¹ ∈ ggCoxRefl CoxeterMatrix.F₄ e ∧ g * r' * g⁻¹ ∈ ggCoxRefl CoxeterMatrix.F₄ e ∧
      ∀ a ∈ ggRankOneIn X Bs (g * u * g⁻¹), ∀ b ∈ ggRankOneIn X Bs (g * r' * g⁻¹),
        a * b = b * a := by
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hsimp : ∀ k, R.s k = CoxeterMatrix.F₄.simple k := by
    intro k
    rw [hRs k, CoxeterMatrix.toCoxeterSystem_simple]
  obtain ⟨t₁, ht₁⟩ : ∃ t, t = w * CoxeterMatrix.F₄.simple i * w⁻¹ := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t, t = w' * CoxeterMatrix.F₄.simple j * w'⁻¹ := ⟨_, rfl⟩
  rw [← ht₁] at hu
  rw [← ht₂] at hr'
  have h₁ : R.IsRefl t₁ := ⟨w, i, by rw [hsimp, ht₁]⟩
  have h₂ : R.IsRefl t₂ := ⟨w', j, by rw [hsimp, ht₂]⟩
  have hc : Commute t₁ t₂ := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hr', hcomm]
  have hcls : R.cls t₁ ≠ R.cls t₂ := by
    have hsi : R.IsRefl (R.s i) := ⟨1, i, by group⟩
    have hsj : R.IsRefl (R.s j) := ⟨1, j, by group⟩
    rw [ht₁, ht₂, ← hsimp i, ← hsimp j, R.cls_conj hsi, R.cls_conj hsj, R.cls_s, R.cls_s]
    by_cases h1 : i.val < 2
    · have h2 : ¬ j.val < 2 := by have := hij.1 h1; omega
      simp only [h1, h2, if_true, if_false]
      decide
    · have h2 : j.val < 2 := by
        by_contra h2
        exact h1 (hij.2 (by omega))
      simp only [h1, h2, if_true, if_false]
      decide
  obtain ⟨v, hv⟩ := R.exists_conj_pair_mixed h₁ h₂ hc hcls
  obtain ⟨φ, -, haR, ha01, ha12, ha02, haX⟩ :=
    exists_f4Triple_map_of_weyl hpp hp2 hEl hNT hAind hpres hXA ε hεrefl σ hM
  set a : Fin 3 → CoxeterMatrix.F₄.Group := fun k => φ (M'.simple (σ k)) with ha
  have haR' : ∀ k, R.IsRefl (a k) := fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (haR k)
  have hfr : ∀ (g : CoxeterMatrix.F₄.Group) (k : Fin 4) (k' : Fin 3), g * a k' * g⁻¹ = R.s k →
      ((e (g⁻¹ * CoxeterMatrix.F₄.simple k * g⁻¹⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs := by
    intro g k k' h
    apply (haX _).mp
    rw [← hsimp k, ← h, show g⁻¹ * (g * a k' * g⁻¹) * g⁻¹⁻¹ = a k' by group]
    exact Subgroup.subset_closure ⟨k', rfl⟩
  have key : ∀ (c w₀ : CoxeterMatrix.F₄.Group) (i₀ j₀ : Fin 4), CoxeterMatrix.F₄ i₀ j₀ = 2 →
      c * t₁ * c⁻¹ = w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹ →
      c * t₂ * c⁻¹ = w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹ →
      ((e (w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
      ((e (w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
      ∃ g : MulAut ↥Bs, g ∈ A ∧
        g * u * g⁻¹ ∈ ggAutomizer X Bs ∧ g * r' * g⁻¹ ∈ ggAutomizer X Bs ∧
        g * u * g⁻¹ ∈ ggCoxRefl CoxeterMatrix.F₄ e ∧ g * r' * g⁻¹ ∈ ggCoxRefl CoxeterMatrix.F₄ e ∧
        ∀ a ∈ ggRankOneIn X Bs (g * u * g⁻¹), ∀ b ∈ ggRankOneIn X Bs (g * r' * g⁻¹),
          a * b = b * a := by
    intro c w₀ i₀ j₀ hl hc₁ hc₂ hi hj
    have hgu : ((e c : ↥A) : MulAut ↥Bs) * u * ((e c : ↥A) : MulAut ↥Bs)⁻¹ =
        ((e (w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹) : ↥A) : MulAut ↥Bs) := by
      rw [hu, ← hc₁, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv,
        ← map_mul, ← map_mul]
    have hgr : ((e c : ↥A) : MulAut ↥Bs) * r' * ((e c : ↥A) : MulAut ↥Bs)⁻¹ =
        ((e (w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹) : ↥A) : MulAut ↥Bs) := by
      rw [hr', ← hc₂, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv,
        ← map_mul, ← map_mul]
    refine ⟨(e c : ↥A), (e c).2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hgu]
      exact hi
    · rw [hgr]
      exact hj
    · rw [hgu]
      exact ⟨w₀, i₀, rfl⟩
    · rw [hgr]
      exact ⟨w₀, j₀, rfl⟩
    · rw [hgu, hgr]
      exact hlab w₀ i₀ j₀ hi hj hl
  obtain ⟨ga, hga | hga⟩ := R.classify (haR' 0) (haR' 1) (haR' 2) ha01 ha12 ha02
  ·
    rcases hv with hv | hv
    · obtain ⟨c₀, c₂⟩ := R.conj_s1s3
      refine key (ga⁻¹ * R.wd [3, 2, 1, 0] * v) ga⁻¹ 0 2 (by decide) ?_ ?_ (hfr ga 0 0 hga.1)
        (hfr ga 2 2 hga.2.2)
      · rw [← hsimp 0, ← c₀, ← hv.1]
        group
      · rw [← hsimp 2, ← c₂, ← hv.2]
        group
    · refine key (ga⁻¹ * v) ga⁻¹ 2 0 (by decide) ?_ ?_ (hfr ga 2 2 hga.2.2) (hfr ga 0 0 hga.1)
      · rw [← hsimp 2, ← hv.1]
        group
      · rw [← hsimp 0, ← hv.2]
        group
  ·
    rcases hv with hv | hv
    · refine key (ga⁻¹ * v) ga⁻¹ 1 3 (by decide) ?_ ?_ (hfr ga 1 2 hga.2.2) (hfr ga 3 0 hga.1)
      · rw [← hsimp 1, ← hv.1]
        group
      · rw [← hsimp 3, ← hv.2]
        group
    · obtain ⟨c₃, c₁⟩ := R.conj_s2s0
      refine key (ga⁻¹ * R.wd [0, 1, 2, 3] * v) ga⁻¹ 3 1 (by decide) ?_ ?_ (hfr ga 3 0 hga.1)
        (hfr ga 1 2 hga.2.2)
      · rw [← hsimp 3, ← c₃, ← hv.1]
        group
      · rw [← hsimp 1, ← c₁, ← hv.2]
        group

section Inputs

theorem exists_conj_commPair_mixed_of_tableBPos_PSp {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .PSp 3 f X) (w w' : CoxeterMatrix.F₄.Group) (i j : Fin 4)
    (hij : i.val < 2 ↔ 2 ≤ j.val) {u r' : MulAut ↥Bs}
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hr' : r' = ((e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹) : ↥A) : MulAut ↥Bs))
    (hcomm : u * r' = r' * u) :
    ∃ g : MulAut ↥Bs, g ∈ A ∧
      g * u * g⁻¹ ∈ ggAutomizer X Bs ∧ g * r' * g⁻¹ ∈ ggAutomizer X Bs ∧
      g * u * g⁻¹ ∈ ggCoxRefl CoxeterMatrix.F₄ e ∧ g * r' * g⁻¹ ∈ ggCoxRefl CoxeterMatrix.F₄ e ∧
      ∀ a ∈ ggRankOneIn X Bs (g * u * g⁻¹), ∀ b ∈ ggRankOneIn X Bs (g * r' * g⁻¹),
        a * b = b * a := by
  obtain ⟨-, -, -, ε, hεrefl, -, -⟩ := id hpos
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_PSp_three]
    rfl
  exact exists_conj_commPair_mixed_of_label2 hpp hp2 hEl hNT hAind hpres hXA ε hεrefl
    (Equiv.refl _) hM (fun w₀ i₀ j₀ hi hj hl =>
      (ggF4QGeFourRk2_of_tableBPos_PSp hpp hp2 hEl hNT hAind hpres hXA hf hpos w₀ i₀ j₀ hi hj).1 hl)
    w w' i j hij hu hr' hcomm

theorem commute_rankOneFamily_of_commPair_mixed {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X H : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) (hAH : A ≤ ggAutomizer H Bs) {f : ℕ}
    (hf : 2 ≤ f) (hpos : GGTableBPosImage p Bs .PSp 3 f X) (S : MulAut ↥Bs → Subgroup G)
    (hagree : ∀ t ∈ ggAutomizer X Bs, t ∈ ggCoxRefl CoxeterMatrix.F₄ e →
      S t = ggRankOneIn X Bs t)
    (hequiv : ∀ h ∈ H, h ∈ Subgroup.normalizer (Bs : Set G) → ∀ g : MulAut ↥Bs,
      (∀ b : ↥Bs, ((g b : ↥Bs) : G) = h * b * h⁻¹) → ∀ t ∈ ggCoxRefl CoxeterMatrix.F₄ e,
        S (g * t * g⁻¹) = (S t).map (MulAut.conj h).toMonoidHom)
    (w w' : CoxeterMatrix.F₄.Group) (i j : Fin 4) (hij : i.val < 2 ↔ 2 ≤ j.val)
    {u r' : MulAut ↥Bs}
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hr' : r' = ((e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹) : ↥A) : MulAut ↥Bs))
    (hcomm : u * r' = r' * u) :
    ∀ a ∈ S u, ∀ b ∈ S r', a * b = b * a := by
  exact commute_rankOneFamily_of_exists_conj hAH S hagree hequiv ⟨w, i, hu⟩ ⟨w', j, hr'⟩
    (exists_conj_commPair_mixed_of_tableBPos_PSp hpp hp2 hEl hNT hAind hpres hXA hf hpos w w' i j
      hij hu hr' hcomm)

end Inputs

end CFSG.StandardType
