module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Glue2_comm_eq_one (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} {B : Subgroup G}
    (hB : B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g)
    (hVg : ¬ V ≤ conjSubgroup D.M g)
    (hs : ¬ (s15 D.M V₀ V hV L = 2 ∧
      delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1))
    {a y : G} (ha : a ∈ B) (hy : y ∈ conjSubgroup D.M g)
    (hc : a * y * a⁻¹ * y⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) :
    a * y * a⁻¹ * y⁻¹ = 1 := by
  by_contra hne1
  have h151 := h.hyp151
  have h125 := h151.hyp125
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h125 hV
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) hV1V
  have hBV0 : B ⊓ V = ⊥ := hB ▸ s15_Glue_inf_V_eq_bot D h hV hVg
  have hym : g * y * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hy
  have haA : g * a * g⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L := by
    rw [hB] at ha
    exact mem_conjSubgroup_iff.1 ha
  have hyy : g * y * g⁻¹ * (g * a * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ ∈
      conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (g * y * g⁻¹)⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have : (g * y * g⁻¹)⁻¹ * (g * y * g⁻¹ * (g * a * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹) *
        ((g * y * g⁻¹)⁻¹)⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ haA
  have hV1m : conjSubgroup (v1Sub D.M V₀ V hV L) (g * y * g⁻¹)⁻¹ = v1Sub D.M V₀ V hV L :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (Subgroup.inv_mem _ (s15_Infra_le_normalizer_v1Sub h125 hV hym))
  have hsup : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (g * y * g⁻¹)⁻¹ =
      conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔ v1Sub D.M V₀ V hV L := by
    have h1 : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (g * y * g⁻¹)⁻¹ =
        conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔
          conjSubgroup (v1Sub D.M V₀ V hV L) (g * y * g⁻¹)⁻¹ := by
      simp only [conjSubgroup]
      exact Subgroup.map_sup _ _ _
    rw [h1, hV1m]
  have hyW : g * y * g⁻¹ * (g * a * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ ∈
      conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔ v1Sub D.M V₀ V hV L := hsup ▸ hyy
  have hgc : g * (a * y * a⁻¹ * y⁻¹) * g⁻¹ = (g * a * g⁻¹) *
      (g * y * g⁻¹ * (g * a * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹) := by group
  by_cases hWm : conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ = wSub V₀ V hV L
  · have hc1 : g * (a * y * a⁻¹ * y⁻¹) * g⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L := by
      rw [hgc]
      refine Subgroup.mul_mem _ haA ?_
      rwa [hWm] at hyW
    have hcB : a * y * a⁻¹ * y⁻¹ ∈ B := by
      rw [hB]
      exact mem_conjSubgroup_iff.2 hc1
    have h2 : a * y * a⁻¹ * y⁻¹ ∈ B ⊓ V := Subgroup.mem_inf.2 ⟨hcB, hWV hc⟩
    rw [hBV0] at h2
    exact hne1 (Subgroup.mem_bot.1 h2)
  · have hginv : g⁻¹ ∉ D.M := by
      intro hginv
      apply hVg
      have hg : g ∈ D.M := by simpa using D.M.inv_mem hginv
      rw [s15_Tools_conjSubgroup_M D hg]
      exact h125.pairFacts.le_M
    have hthird := h.third g⁻¹ hginv (wSub V₀ V hV L)
      ⟨1, D.M.one_mem, (conjSubgroup_one _).symm⟩
      (conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹)
      ⟨(g * y * g⁻¹)⁻¹, D.M.inv_mem hym, rfl⟩ (fun heq => hWm heq.symm) ?_
    · exact hs hthird
    · intro hbot
      have hmem : g * (a * y * a⁻¹ * y⁻¹) * g⁻¹ ∈
          (wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔
            v1Sub D.M V₀ V hV L) ⊓
            conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g⁻¹ := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [hgc]
          refine Subgroup.mul_mem _ ?_ ?_
          · have hle : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤
                wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔
                  v1Sub D.M V₀ V hV L :=
              sup_le (le_sup_left.trans le_sup_left) le_sup_right
            exact hle haA
          · have hle : conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔
                  v1Sub D.M V₀ V hV L ≤
                wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) (g * y * g⁻¹)⁻¹ ⊔
                  v1Sub D.M V₀ V hV L :=
              sup_le (le_sup_right.trans le_sup_left) le_sup_right
            exact hle hyW
        · rw [mem_conjSubgroup_iff]
          have : g⁻¹ * (g * (a * y * a⁻¹ * y⁻¹) * g⁻¹) * (g⁻¹)⁻¹ = a * y * a⁻¹ * y⁻¹ := by
            group
          rw [this]
          exact hc
      rw [hbot] at hmem
      have h3 := Subgroup.mem_bot.1 hmem
      apply hne1
      have h4 : a * y * a⁻¹ * y⁻¹ = g⁻¹ * (g * (a * y * a⁻¹ * y⁻¹) * g⁻¹) * g := by group
      rw [h4, h3]
      group

theorem s15_Glue2_mQuot_inf_normalizer_le_one (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {g : G} {B Y : Subgroup G}
    (hB : B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g)
    (hY : Y ≤ conjSubgroup D.M g) (hY2 : IsPGroup 2 Y) (hs : s15 D.M V₀ V hV L = 2) :
    E3.mQuot Y (Y ⊓ normalizer (B : Set G)) ≤ 1 := by
  have hY'M : conjSubgroup Y g⁻¹ ≤ D.M := by
    have := E3.conjSubgroup_mono_left g⁻¹ hY
    rwa [E3.conjSubgroup_conj_inv] at this
  have hY'2 : IsPGroup 2 (conjSubgroup Y g⁻¹) := E3.isPGroup_conjSubgroup hY2 g⁻¹
  have hYY : conjSubgroup (conjSubgroup Y g⁻¹) g = Y := E3.conjSubgroup_inv_conj Y g
  have hN : normalizer (B : Set G) = conjSubgroup (normalizer
      ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G)) g := by
    rw [hB, E3.conjSubgroup_normalizer]
  have h1 : E3.mQuot Y (Y ⊓ normalizer (B : Set G)) =
      E3.mQuot (conjSubgroup Y g⁻¹) (conjSubgroup Y g⁻¹ ⊓ normalizer
        ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G)) := by
    rw [← E3.mQuot_conjSubgroup (conjSubgroup Y g⁻¹) _ g, E3.conjSubgroup_inf, hYY, hN]
  have h2 : conjSubgroup Y g⁻¹ ⊓ normalizer
      ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) =
      conjSubgroup Y g⁻¹ ⊓ normalizer (wSub V₀ V hV L : Set G) := by
    have e1 := inf_normalizer_wSub_sup_v1Sub_eq_nBar D h hV
    have e2 := inf_normalizer_wSub_eq_nBar D h hV
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, hxn⟩
      have : x ∈ D.M ⊓ normalizer
          ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) :=
        Subgroup.mem_inf.2 ⟨hY'M hx, hxn⟩
      rw [e1, ← e2] at this
      exact ⟨hx, (Subgroup.mem_inf.1 this).2⟩
    · rintro ⟨hx, hxn⟩
      have : x ∈ D.M ⊓ normalizer (wSub V₀ V hV L : Set G) :=
        Subgroup.mem_inf.2 ⟨hY'M hx, hxn⟩
      rw [e2, ← e1] at this
      exact ⟨hx, (Subgroup.mem_inf.1 this).2⟩
  rw [h1, h2]
  exact s15_Glue_mQuot_inf_normalizer_le_one D h hV hY'M hY'2 hs

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
