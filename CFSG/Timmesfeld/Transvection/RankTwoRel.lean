module

public import CFSG.Timmesfeld.Transvection.ShortRootCommNorm

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace PairFrame

variable [Finite G] {A E D E' : Subgroup G} (F : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
  {k : ℕ} (φ₀ : SL2Coords A E k) (φ₁ : SL2Coords D E' k)
include F hΔ

theorem conjSub_shortRootGroup_mul :
    conjSub (shortRootGroup Δ E A D E') (φ₁.elt (weylElt _) * φ₀.elt (weylElt _)) =
      shortRootGroup Δ E' D A E := by
  have hc : Nat.card E' = Nat.card D := hΔ.root.card_eq F.memE' F.memD
  have hw₁ := φ₁.elt_mem (weylElt _)
  have hA : conjSub A (φ₁.elt (weylElt _)) = A :=
    conjSub_of_forall_commute fun a ha => (F.comm a (Subgroup.mem_sup_left ha) _ hw₁).symm
  have hE : conjSub E (φ₁.elt (weylElt _)) = E :=
    conjSub_of_forall_commute fun a ha => (F.comm a (Subgroup.mem_sup_right ha) _ hw₁).symm
  rw [conjSub_mul, F.conjSub_shortRootGroup_elt_weylElt hΔ φ₀, ← shortRootGroup_conjSub hΔ.root,
    hA, hE, φ₁.conjSub_A_elt_weylElt hc, φ₁.conjSub_E_elt_weylElt hc, shortRootGroup,
    shortRootGroup, lineGroup_comm E' A, lineStab_comm D A, lineStab_comm E' E, inf_right_comm]

theorem conj_mul_mem {x : G} (hx : x ∈ shortRootGroup Δ E A D E') :
    φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * x *
      (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹ ∈ shortRootGroup Δ E' D A E := by
  have h := conj_mem_conjSub (φ₁.elt (weylElt _) * φ₀.elt (weylElt _)) hx
  rwa [F.conjSub_shortRootGroup_mul hΔ φ₀ φ₁] at h

theorem exists_conj_mul_eq {y : G} (hy : y ∈ shortRootGroup Δ E' D A E) :
    ∃ x ∈ shortRootGroup Δ E A D E',
      φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * x *
        (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹ = y := by
  rw [← F.conjSub_shortRootGroup_mul hΔ φ₀ φ₁] at hy
  obtain ⟨x, hx, rfl⟩ := mem_conjSub_iff.1 hy
  exact ⟨x, hx, rfl⟩

theorem aligned_swap (hal : φ₀.Aligned Δ φ₁) : φ₁.Aligned Δ φ₀ := by
  intro ν y hy
  obtain ⟨x, hx, rfl⟩ := F.exists_conj_mul_eq hΔ φ₀ φ₁ hy
  set w₀ := φ₀.elt (weylElt _) with hw₀
  set w₁ := φ₁.elt (weylElt _) with hw₁
  have hc : Commute w₀ w₁ := F.comm _ (φ₀.elt_mem _) _ (φ₁.elt_mem _)
  have hc1 : Commute w₁ (φ₀.torusElt ν) := (F.comm _ (φ₀.torusElt_mem ν) _ (φ₁.elt_mem _)).symm
  have hcomm : Commute (φ₀.torusElt ν⁻¹) (φ₁.torusElt ν⁻¹) :=
    F.comm _ (φ₀.torusElt_mem _) _ (φ₁.torusElt_mem _)
  have h0 : w₀⁻¹ * φ₀.torusElt ν * w₀ = φ₀.torusElt ν⁻¹ := by
    have := φ₀.elt_weylElt_conj_diagElt ν
    rw [φ₀.elt_diagElt, φ₀.elt_diagElt, ← hw₀, φ₀.elt_weylElt_inv] at this
    rw [show w₀⁻¹ = w₀ from φ₀.elt_weylElt_inv, this]
  have h1 : w₁⁻¹ * φ₁.torusElt ν * w₁ = φ₁.torusElt ν⁻¹ := by
    have := φ₁.elt_weylElt_conj_diagElt ν
    rw [φ₁.elt_diagElt, φ₁.elt_diagElt, ← hw₁, φ₁.elt_weylElt_inv] at this
    rw [show w₁⁻¹ = w₁ from φ₁.elt_weylElt_inv, this]
  have e1 : w₁⁻¹ * φ₀.torusElt ν * w₁ = φ₀.torusElt ν := by
    rw [mul_assoc, ← hc1.eq, inv_mul_cancel_left]
  have hc0' : Commute w₀ (φ₁.torusElt ν⁻¹) := F.comm _ (φ₀.elt_mem _) _ (φ₁.torusElt_mem _)
  have e2 : w₀⁻¹ * φ₁.torusElt ν⁻¹ * w₀ = φ₁.torusElt ν⁻¹ := by
    rw [mul_assoc, ← hc0'.eq, inv_mul_cancel_left]
  have hT : (w₁ * w₀)⁻¹ * (φ₁.torusElt ν * φ₀.torusElt ν) * (w₁ * w₀) =
      φ₀.torusElt ν⁻¹ * φ₁.torusElt ν⁻¹ := by
    calc (w₁ * w₀)⁻¹ * (φ₁.torusElt ν * φ₀.torusElt ν) * (w₁ * w₀) =
          (w₀⁻¹ * (w₁⁻¹ * φ₁.torusElt ν * w₁) * w₀) *
            (w₀⁻¹ * (w₁⁻¹ * φ₀.torusElt ν * w₁) * w₀) := by group
      _ = (w₀⁻¹ * φ₁.torusElt ν⁻¹ * w₀) * (w₀⁻¹ * φ₀.torusElt ν * w₀) := by rw [h1, e1]
      _ = φ₁.torusElt ν⁻¹ * φ₀.torusElt ν⁻¹ := by rw [e2, h0]
      _ = φ₀.torusElt ν⁻¹ * φ₁.torusElt ν⁻¹ := hcomm.eq.symm
  have hal' := (hal ν⁻¹ x hx).eq
  rw [Commute, SemiconjBy]
  calc φ₁.torusElt ν * φ₀.torusElt ν * (w₁ * w₀ * x * (w₁ * w₀)⁻¹) =
        (w₁ * w₀) * ((w₁ * w₀)⁻¹ * (φ₁.torusElt ν * φ₀.torusElt ν) * (w₁ * w₀) * x) *
          (w₁ * w₀)⁻¹ := by group
    _ = (w₁ * w₀) * (x * ((w₁ * w₀)⁻¹ * (φ₁.torusElt ν * φ₀.torusElt ν) * (w₁ * w₀))) *
          (w₁ * w₀)⁻¹ := by rw [hT, hal']
    _ = w₁ * w₀ * x * (w₁ * w₀)⁻¹ * (φ₁.torusElt ν * φ₀.torusElt ν) := by group

omit [Finite G] in
theorem eq_of_mul_mul_eq_mul_mul {u u' a a' d d' : G} (hu : u ∈ shortRootGroup Δ A E D E')
    (hu' : u' ∈ shortRootGroup Δ A E D E') (ha : a ∈ A) (ha' : a' ∈ A) (hd : d ∈ D)
    (hd' : d' ∈ D) (h : u * a * d = u' * a' * d') : u = u' ∧ a = a' ∧ d = d' := by
  have hcd : Commute (d' * d⁻¹) a⁻¹ := F.commute_of_mem_lineGroup_AD hΔ
    (F.D_le_lineGroup (Subgroup.mul_mem _ hd' (Subgroup.inv_mem _ hd)))
    (F.A_le_lineGroup (Subgroup.inv_mem _ ha))
  have h1 : u'⁻¹ * u = (a' * a⁻¹) * (d' * d⁻¹) := by
    calc u'⁻¹ * u = u'⁻¹ * (u * a * d) * d⁻¹ * a⁻¹ := by group
      _ = a' * ((d' * d⁻¹) * a⁻¹) := by rw [h]; group
      _ = (a' * a⁻¹) * (d' * d⁻¹) := by rw [hcd.eq]; group
  have h2 : u'⁻¹ * u ∈ shortRootGroup Δ A E D E' ⊓ (A ⊔ D) := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hu') hu, ?_⟩
    rw [h1]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mul_mem _ ha' (Subgroup.inv_mem _ ha)))
      (Subgroup.mem_sup_right (Subgroup.mul_mem _ hd' (Subgroup.inv_mem _ hd)))
  rw [F.shortRootGroup_inf_sup_eq_bot hΔ, Subgroup.mem_bot, inv_mul_eq_one] at h2
  subst h2
  have h3 : a * d = a' * d' := by
    have := h
    rw [mul_assoc, mul_assoc] at this
    exact mul_left_cancel this
  have h4 : a'⁻¹ * a ∈ A ⊓ D := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ ha') ha, ?_⟩
    rw [show a'⁻¹ * a = d' * d⁻¹ by
      calc a'⁻¹ * a = a'⁻¹ * (a * d) * d⁻¹ := by group
        _ = d' * d⁻¹ := by rw [h3]; group]
    exact Subgroup.mul_mem _ hd' (Subgroup.inv_mem _ hd)
  rw [hΔ.inf_eq_bot (F.noIsolated hΔ.root) F.memA F.memD F.ne_AD, Subgroup.mem_bot,
    inv_mul_eq_one] at h4
  subst h4
  exact ⟨rfl, rfl, mul_left_cancel h3⟩

variable (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A) (hX : ShortRootFieldHyp Δ A E D E')
  (hX' : ShortRootFieldHyp Δ D E' A E)
include hpts hq hX hX'

theorem quadNorm_conj_eq (hal : φ₀.Aligned Δ φ₁)
    (hY : ∀ C ∈ lineOf Δ D A, C ≠ A → ∃ y ∈ shortRootGroup Δ E' D A E, conjSub D y = C)
    {x : G} (hx : x ∈ shortRootGroup Δ E A D E') :
    φ₁.quadNorm φ₀ (φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * x *
      (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹) = φ₀.quadNorm φ₁ x := by
  by_cases hx1 : x = 1
  · subst hx1
    simp
  have hqD : 4 ≤ Nat.card D := by rwa [hΔ.root.card_eq F.memD F.memA]
  have hal' := F.aligned_swap hΔ φ₀ φ₁ hal
  set w₀ := φ₀.elt (weylElt _) with hw₀
  set w₁ := φ₁.elt (weylElt _) with hw₁
  obtain ⟨hB, hBA, -, -⟩ := hX.1 x hx hx1
  obtain ⟨y, hy, hyB⟩ := hY _ (lineOf_comm (Δ := Δ) A D ▸ hB) hBA
  have hg : x * φ₀.elt (lowerElt _ 1) * x⁻¹ ∈ conjSub D y := by
    rw [hyB]
    exact conj_mem_conjSub x (φ₀.elt_lowerElt_mem 1)
  obtain ⟨d, hd, hdg⟩ := mem_conjSub_iff.1 hg
  obtain ⟨u, rfl⟩ := φ₁.exists_eq_elt_lowerElt hd
  have hi : x * φ₀.elt (lowerElt _ 1) * x⁻¹ =
      (w₀ * x * w₀⁻¹) * φ₀.elt (lowerElt _ 1) * φ₁.elt (lowerElt _ (φ₀.quadNorm φ₁ x)) := by
    have h1 := F.commutator_eq_mul_elt hΔ φ₀ hpts hq hX φ₁ hal hx 1
    rw [SL2Coords.smulG_one, one_mul] at h1
    have hc : Commute (φ₁.elt (lowerElt _ (φ₀.quadNorm φ₁ x))) (φ₀.elt (lowerElt _ 1)) :=
      (F.commuting_AD _ (φ₀.elt_lowerElt_mem 1) _ (φ₁.elt_lowerElt_mem _)).symm
    calc x * φ₀.elt (lowerElt _ 1) * x⁻¹ = ⁅x, φ₀.elt (lowerElt _ 1)⁆ * φ₀.elt (lowerElt _ 1) := by
          rw [commutatorElement_def]
          group
      _ = _ := by
          rw [h1, mul_assoc (w₀ * x * w₀⁻¹), hc.eq, ← mul_assoc]
  have hj : y * φ₁.elt (lowerElt _ u) * y⁻¹ = (w₁ * φ₁.smulG u y * w₁⁻¹) *
      φ₀.elt (lowerElt _ (u * φ₁.quadNorm φ₀ y)) * φ₁.elt (lowerElt _ u) := by
    have h1 := F.swap.commutator_eq_mul_elt hΔ φ₁ hpts hqD hX' φ₀ hal' hy u
    calc y * φ₁.elt (lowerElt _ u) * y⁻¹ = ⁅y, φ₁.elt (lowerElt _ u)⁆ * φ₁.elt (lowerElt _ u) := by
          rw [commutatorElement_def]
          group
      _ = _ := by rw [h1]
  have hmem1 : w₀ * x * w₀⁻¹ ∈ shortRootGroup Δ A E D E' := F.conj_elt_weylElt_mem hΔ φ₀ hx
  have hmem2 : w₁ * φ₁.smulG u y * w₁⁻¹ ∈ shortRootGroup Δ A E D E' := by
    have h := F.swap.conj_elt_weylElt_mem hΔ φ₁ (F.swap.smulG_mem hΔ φ₁ hy u)
    have hsw : shortRootGroup Δ D E' A E = shortRootGroup Δ A E D E' := by
      rw [shortRootGroup, shortRootGroup, lineGroup_comm D A, lineStab_comm E' A,
        lineStab_comm D E, inf_right_comm]
    rwa [hsw] at h
  obtain ⟨h1, h2, h3⟩ := F.eq_of_mul_mul_eq_mul_mul hΔ hmem1 hmem2 (φ₀.elt_lowerElt_mem 1)
    (φ₀.elt_lowerElt_mem _) (φ₁.elt_lowerElt_mem _) (φ₁.elt_lowerElt_mem _)
    (hi.symm.trans (hdg.trans hj))
  have hu1 : 1 = u * φ₁.quadNorm φ₀ y := φ₀.elt_lowerElt_injective h2
  have hNu : φ₀.quadNorm φ₁ x = u := φ₁.elt_lowerElt_injective h3
  have hww : w₁⁻¹ = w₁ := φ₁.elt_weylElt_inv
  have hTx : w₁ * w₀ * x * (w₁ * w₀)⁻¹ = φ₁.smulG u y := by
    calc w₁ * w₀ * x * (w₁ * w₀)⁻¹ = w₁ * (w₀ * x * w₀⁻¹) * w₁⁻¹ := by group
      _ = w₁ * w₁ * φ₁.smulG u y * (w₁ * w₁)⁻¹ := by rw [h1]; group
      _ = φ₁.smulG u y := by
          rw [φ₁.elt_weylElt_mul_self]
          group
  rw [hTx, F.swap.quadNorm_smulG hΔ φ₁ hpts hqD hX' φ₀ hal' hy u, hNu, mul_assoc, ← hu1,
    mul_one]

end PairFrame

end CFSG.Timmesfeld.Transvection
