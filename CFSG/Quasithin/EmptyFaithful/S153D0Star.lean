module

public import CFSG.Quasithin.EmptyFaithful.S153D0Theta
public import CFSG.Quasithin.EmptyFaithful.S153Cases
public import CFSG.Quasithin.EmptyFaithful.S153D0Rad

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

section Generic

variable {G : Type} [Group G]

theorem le_centralizer_of_autOn_eq_bot {X V : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (h : autOn X V = ⊥) :
    X ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  have hmem : conjAct V ⟨x, hXV hx⟩ ∈ autOn X V :=
    mem_autOn_iff_exists.mpr ⟨x, hXV hx, hx, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact A4.conjAct_eq_one_iff.mp hmem

theorem conj_mem_centralizer {U : Subgroup G} {g c : G} (hg : g ∈ Subgroup.normalizer (U : Set G))
    (hc : c ∈ Subgroup.centralizer (U : Set G)) : g * c * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
  have hu' : g⁻¹ * u * g ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hu'
  calc u * (g * c * g⁻¹) = g * ((g⁻¹ * u * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * u := by group

end Generic

end S153D

namespace Hyp15310

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem Yp_le_Y153 (h : Hyp15310 G T Mc M V₁ V₂ Yp t) : Yp ≤ Y153 Mc M := by
  rcases h.cases with hY | ⟨-, hY⟩
  · exact hY ▸ le_rfl
  · rw [hY]
    exact (oTwoUpper_le _).trans inf_le_left

theorem Yp_pow_three_of_odd (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {y : G}
    (hy : y ∈ Yp) (hodd : Odd (orderOf y)) : y ^ 3 = 1 :=
  S153D.Y153_pow_three_of_odd h113 h.hyp (h.Yp_le_Y153 hy) hodd

theorem Yp_le_thetaOf (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    Yp ≤ thetaOf Yp := by
  have := S153D.oTwoUpper_le_thetaOf (A := Yp) fun x hx hodd => h.Yp_pow_three_of_odd h113 hx hodd
  rwa [h.oTwoUpper_eq] at this

theorem theta_eq (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) : Yp = thetaOf (M ⊓ I) := by
  have hYMI : Yp ≤ M ⊓ I := by
    rw [← h.lemma_15_3_11_four h113 hI]
    exact le_inf (le_sup_left.trans hI.1.1) Subgroup.le_normalizer
  apply le_antisymm
  · exact (h.Yp_le_thetaOf h113).trans (S153D.thetaOf_mono hYMI)
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hx3 : x ^ 3 = 1 := by rw [← hx.2]; exact pow_orderOf_eq_one x
    have hxY : x ∈ Y153 Mc M := S153D.mem_Y153_of_pow_three h113 h.hyp hx.1.1 hx3
    have hodd : Odd (orderOf x) := by rw [hx.2]; decide
    rcases h.cases with hY | h2
    · exact hY ▸ hxY
    · have h3 := h.lemma_15_3_11_three h113 h2 hI
      rw [h3.1]
      exact mem_oTwoUpper_of_odd ⟨hxY, hx.1.2⟩ hodd

theorem Yp_not_le_centralizer_UI (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    {I : Subgroup G} (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    ¬ Yp ≤ Subgroup.centralizer (UI153 T I : Set G) := by
  have hYpI : Yp ≤ I := le_sup_left.trans hI.1.1
  intro hle
  rcases h.cases with hY | ⟨-, hY⟩
  ·
    subst hY
    have hVU : VZ T M ≤ UI153 T I := by
      rw [h.hyp.VZ_eq_conjClosure_Y153 h113]
      exact conjClosure_mono le_rfl hYpI
    exact h.hyp.Y153_not_le_centralizer h113 (hle.trans (Subgroup.centralizer_le hVU))
  ·
    have hV₂U : V₂ ≤ UI153 T I := by
      have := h.hyp.V₂_le_conjClosure_Yplus h113 h.decomp
      rw [← hY] at this
      exact this.trans (conjClosure_mono le_rfl hYpI)
    have hYV₁ : Yp ≤ Subgroup.centralizer (V₁ : Set G) := by
      rw [hY]
      exact (oTwoUpper_le _).trans inf_le_right
    have hYV₂ : Yp ≤ Subgroup.centralizer (V₂ : Set G) :=
      hle.trans (Subgroup.centralizer_le hV₂U)
    have hYV : Yp ≤ Subgroup.centralizer (VZ T M : Set G) := by
      rw [Subgroup.le_centralizer_iff, ← h.decomp.sup]
      exact sup_le (Subgroup.le_centralizer_iff.mp hYV₁) (Subgroup.le_centralizer_iff.mp hYV₂)
    rw [hY] at hYV
    exact h.hyp.Yplus_not_le_centralizer h113 h.decomp hYV

theorem star_ne (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) : autOn Yp (UI153 T I) ≠ ⊥ := by
  intro hbot
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  exact h.Yp_not_le_centralizer_UI h113 hI
    (S153D.le_centralizer_of_autOn_eq_bot ((le_sup_left.trans hI.1.1).trans hUN) hbot)

theorem star_lt (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    autOn (M ⊓ I) (UI153 T I) < autOn I (UI153 T I) := by
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  refine lt_of_le_of_ne (autOn_le_autOn _ inf_le_right) fun heq => hI.2 ?_
  exact (S153D.le_of_autOn_le hUN le_rfl inf_le_right (h.lemma_15_3_11_two h113 hI)
    heq.ge).trans inf_le_left

theorem star_norm (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    Subgroup.normalizer (autOn Yp (UI153 T I) : Set (MulAut ↥(UI153 T I))) ⊓
        autOn I (UI153 T I) = autOn (M ⊓ I) (UI153 T I) := by
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hYpI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hnorm := h.lemma_15_3_11_four h113 hI
  have hcent := h.lemma_15_3_11_two h113 hI
  have hYMI : Yp ≤ M ⊓ I := by
    rw [← hnorm]
    exact le_inf hYpI Subgroup.le_normalizer
  have hMIN : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := by
    rw [← hnorm]
    exact inf_le_right
  apply le_antisymm
  · rintro a ⟨haN, haI⟩
    obtain ⟨g, hgU, hgI, rfl⟩ := mem_autOn_iff_exists.mp haI
    set X : Subgroup G := Yp ⊔ (I ⊓ Subgroup.centralizer (UI153 T I : Set G)) with hX
    have hXMI : X ≤ M ⊓ I := sup_le hYMI hcent
    have hgconj : ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
      refine S153D.conj_mem_sup_of_conj_mem (fun y hy => ?_) (fun c hc => ?_)
      · have hgyI : g * y * g⁻¹ ∈ I := I.mul_mem (I.mul_mem hgI (hYpI hy)) (I.inv_mem hgI)
        have hgyN : g * y * g⁻¹ ∈ Subgroup.normalizer (UI153 T I : Set G) := hUN hgyI
        have hym : conjAct (UI153 T I) ⟨g * y * g⁻¹, hgyN⟩ ∈ autOn Yp (UI153 T I) := by
          have e : conjAct (UI153 T I) ⟨g * y * g⁻¹, hgyN⟩ = conjAct (UI153 T I) ⟨g, hgU⟩ *
              conjAct (UI153 T I) ⟨y, hUN (hYpI hy)⟩ * (conjAct (UI153 T I) ⟨g, hgU⟩)⁻¹ := by
            rw [← (conjAct (UI153 T I)).map_inv, ← (conjAct (UI153 T I)).map_mul,
              ← (conjAct (UI153 T I)).map_mul]
            rfl
          rw [e]
          have hy' : conjAct (UI153 T I) ⟨y, hUN (hYpI hy)⟩ ∈ autOn Yp (UI153 T I) :=
            mem_autOn_iff_exists.mpr ⟨y, hUN (hYpI hy), hy, rfl⟩
          exact (Subgroup.mem_normalizer_iff.mp haN _).mp hy'
        obtain ⟨y', hy'U, hy'Y, hy'e⟩ := mem_autOn_iff_exists.mp hym
        have hI' : (g * y * g⁻¹) * y'⁻¹ ∈ I := I.mul_mem hgyI (I.inv_mem (hYpI hy'Y))
        have hkerN : (g * y * g⁻¹) * y'⁻¹ ∈ Subgroup.normalizer (UI153 T I : Set G) := hUN hI'
        have hker : (g * y * g⁻¹) * y'⁻¹ ∈ Subgroup.centralizer (UI153 T I : Set G) := by
          refine (A4.conjAct_eq_one_iff (V := UI153 T I)
            (g := ⟨(g * y * g⁻¹) * y'⁻¹, hkerN⟩)).mp ?_
          have e : (⟨(g * y * g⁻¹) * y'⁻¹, hkerN⟩ : ↥(Subgroup.normalizer (UI153 T I : Set G))) =
              ⟨g * y * g⁻¹, hgyN⟩ * ⟨y', hy'U⟩⁻¹ := rfl
          rw [e, map_mul, map_inv, hy'e, mul_inv_cancel]
        have e : g * y * g⁻¹ = ((g * y * g⁻¹) * y'⁻¹) * y' := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hI', hker⟩) (Subgroup.mem_sup_left hy'Y)
      · exact Subgroup.mem_sup_right ⟨I.mul_mem (I.mul_mem hgI hc.1) (I.inv_mem hgI),
          S153D.conj_mem_centralizer hgU hc.2⟩
    have hgX : g ∈ Subgroup.normalizer (X : Set G) := A4.mem_normalizer_of_conj_mem hgconj
    have hθ : thetaOf X = Yp := by
      apply le_antisymm
      · rw [h.theta_eq h113 hI]
        exact S153D.thetaOf_mono hXMI
      · exact (h.Yp_le_thetaOf h113).trans (S153D.thetaOf_mono le_sup_left)
    have hgY : g ∈ Subgroup.normalizer (Yp : Set G) := by
      have := S153D.normalizer_le_normalizer_thetaOf X hgX
      rwa [hθ] at this
    have hgMI : g ∈ M ⊓ I := by
      rw [← hnorm]
      exact ⟨hgI, hgY⟩
    exact mem_autOn_iff_exists.mpr ⟨g, hgU, hgMI, rfl⟩
  · exact le_inf (autOn_le_normalizer_autOn (inf_le_right.trans hUN) (hYpI.trans hUN) hMIN)
      (autOn_le_autOn _ inf_le_right)

end Hyp15310

end CFSG.Quasithin
