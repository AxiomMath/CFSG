module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec8Inv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem vone_le_Q {C V : Subgroup G} (hV : V ≤ Q) : Vone Q B C V ≤ Q := by
  intro x hx
  exact sup_le inf_le_left hV hx.1

theorem Z_le_vone {C : Subgroup G} {t : G} :
    Z ≤ Vone Q B C (Vt M (LB M Q B) B Z t) :=
  le_inf (sec39_Z_le_Vt.trans le_sup_right) (sec39_Z_le_Vt.trans le_sup_right)

theorem Ctx.Q_le_normalizer_vone (hc : Ctx M Q Z B) (t : G) {C : Subgroup G} :
    Q ≤ Subgroup.normalizer (Vone Q B C (Vt M (LB M Q B) B Z t) : Set G) := by
  intro q hq
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hcQ : ⁅q, x⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hq (vone_le_Q hVQ hx)
  have e : q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
  rw [e]
  exact (Vone Q B C (Vt M (LB M Q B) B Z t)).mul_mem (Z_le_vone hcQ) hx

theorem Ctx.QB_inf_M_le_normalizer_vone (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {r : G} :
    QB B ⊓ M ≤
      Subgroup.normalizer (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) : Set G) := by
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  refine sec8_le_normalizer_of_conj fun g hg y hy => ?_
  have hgR : g ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) hs.mem (le_sup_right (a := Q) hg)
  exact sec8_conj_mem_of_QB hc (hc.B_le_Vt hs.mem) hVQ sec39_Z_le_Vt
    (le_inf le_sup_right le_sup_right) hg.1 (hc.Rt_normalizes_Vt hs.mem hgR) hy.1 hy

theorem Ctx.QBC_inf_M_le_normalizer_vone (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    QB (conjSubgroup r B) ⊓ M ≤
      Subgroup.normalizer (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) : Set G) := by
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hCV : conjSubgroup r B ≤ Vt M (LB M Q B) B Z t := fun x hx =>
    (hc.conj_Rt_le_Vt hs.mem hr) (Subgroup.mem_sup_left hx)
  refine sec8_le_normalizer_of_conj fun g hg y hy => ?_
  have hgR : g ∈ Rt M (LB M Q B) t := by
    rw [QB_conj] at hg
    have hsB : r⁻¹ * g * r ∈ QB B := mem_conjSubgroup.mp hg.1
    have hsM : r⁻¹ * g * r ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hrM) hg.2) hrM
    have hsL : r⁻¹ * g * r ∈ LB M Q B := le_sup_right (a := Q) ⟨hsB, hsM⟩
    have hsR : r⁻¹ * g * r ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) hs.mem hsL
    have e : g = r * (r⁻¹ * g * r) * r⁻¹ := by group
    rw [e]
    exact (Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).mul_mem hr hsR) ((Rt M (LB M Q B) t).inv_mem hr)
  exact sec8_conj_mem_of_QB hcC hCV hVQ sec39_Z_le_Vt
    (le_inf le_sup_right le_sup_right) hg.1 (hc.Rt_normalizes_Vt hs.mem hgR) hy.2 hy

theorem Ctx.comm_LB_A1_le_vone (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {r : G} :
    ⁅LB M Q B,
      (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r⁆ ≤ Sec8V1 M Q Z B t r := by
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hWQ : Sec8W1 M Q Z B t r ≤ Q := inf_le_left
  have hV1Q : Sec8V1 M Q Z B t r ≤ Q := vone_le_Q hVQ
  have hAN : QB B ⊓ Sec8W1 M Q Z B t r ≤
      Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := fun a ha =>
    hc.QB_inf_M_le_normalizer_vone hs ⟨ha.1, hc.hyp.Q_normal.1 (hWQ ha.2)⟩
  have hLN : LB M Q B ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
    sup_le (hc.Q_le_normalizer_vone t) (hc.QB_inf_M_le_normalizer_vone hs)
  refine Subgroup.commutator_le.mpr fun l hl x hx => ?_
  obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hAN hx
  have hla : ⁅l, a⁆ ∈ Sec8V1 M Q Z B t r :=
    ((sup_le sec39_Z_le_Vt (hc.B_le_Vt hs.mem)).trans
      (le_inf le_sup_right le_sup_right))
      (hc.comm_LB_inf_QB_mem_sup hl ⟨hWQ ha.2, ha.1⟩)
  have hlv' : l * v * l⁻¹ ∈ Sec8V1 M Q Z B t r :=
    (Subgroup.mem_normalizer_iff.mp (hLN hl) v).mp hv
  have hlv : ⁅l, v⁆ ∈ Sec8V1 M Q Z B t r := by
    rw [commutatorElement_def]
    exact (Sec8V1 M Q Z B t r).mul_mem hlv' ((Sec8V1 M Q Z B t r).inv_mem hv)
  have hav : a * ⁅l, v⁆ * a⁻¹ ∈ Sec8V1 M Q Z B t r :=
    (Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp hlv
  have e : ⁅l, a * v⁆ = ⁅l, a⁆ * (a * ⁅l, v⁆ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Sec8V1 M Q Z B t r).mul_mem hla hav

theorem Ctx.comm_LBC_A2_le_vone (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    ⁅LB M Q (conjSubgroup r B),
      (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r⁆ ≤
      Sec8V1 M Q Z B t r := by
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hWQ : Sec8W1 M Q Z B t r ≤ Q := inf_le_left
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hCV : conjSubgroup r B ≤ Vt M (LB M Q B) B Z t := fun x hx =>
    (hc.conj_Rt_le_Vt hs.mem hr) (Subgroup.mem_sup_left hx)
  have hAN : QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r ≤
      Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := fun a ha =>
    hc.QBC_inf_M_le_normalizer_vone hs hr ⟨ha.1, hc.hyp.Q_normal.1 (hWQ ha.2)⟩
  have hLN : LB M Q (conjSubgroup r B) ≤
      Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
    sup_le (hc.Q_le_normalizer_vone t) (hc.QBC_inf_M_le_normalizer_vone hs hr)
  refine Subgroup.commutator_le.mpr fun l hl x hx => ?_
  obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hAN hx
  have hla : ⁅l, a⁆ ∈ Sec8V1 M Q Z B t r :=
    ((sup_le sec39_Z_le_Vt hCV).trans (le_inf le_sup_right le_sup_right))
      (hcC.comm_LB_inf_QB_mem_sup hl ⟨hWQ ha.2, ha.1⟩)
  have hlv' : l * v * l⁻¹ ∈ Sec8V1 M Q Z B t r :=
    (Subgroup.mem_normalizer_iff.mp (hLN hl) v).mp hv
  have hlv : ⁅l, v⁆ ∈ Sec8V1 M Q Z B t r := by
    rw [commutatorElement_def]
    exact (Sec8V1 M Q Z B t r).mul_mem hlv' ((Sec8V1 M Q Z B t r).inv_mem hv)
  have hav : a * ⁅l, v⁆ * a⁻¹ ∈ Sec8V1 M Q Z B t r :=
    (Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp hlv
  have e : ⁅l, a * v⁆ = ⁅l, a⁆ * (a * ⁅l, v⁆ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Sec8V1 M Q Z B t r).mul_mem hla hav

theorem Ctx.comm_LB_vone_le_vone (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {r : G} :
    ⁅LB M Q B, Sec8V1 M Q Z B t r⁆ ≤ Sec8V1 M Q Z B t r :=
  (Subgroup.commutator_mono le_rfl le_sup_right).trans (hc.comm_LB_A1_le_vone hs)

theorem Ctx.hsupW_of_prod (hc : Ctx M Q Z B) {t r : G}
    (hprod : Sec8W1 M Q Z B t r ≤
      (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r)) :
    Sec8W1 M Q Z B t r ≤
      ((QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ⊔
        ((QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) := by
  have h1 : (QB B ⊓ Sec8W1 M Q Z B t r) ≤
      (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r := le_sup_left
  have h2 : (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ≤
      (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r := le_sup_left
  refine hprod.trans (sup_le ?_ ?_)
  · exact h1.trans le_sup_left
  · exact h2.trans le_sup_right

theorem Ctx.isOppDecomp_of_components (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hVW : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r)
    (hsupW : Sec8W1 M Q Z B t r ≤
      ((QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ⊔
        ((QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r))
    (hinf : ((QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ⊓
        ((QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ≤
        Sec8V1 M Q Z B t r)
    (hfixB : ∀ x ∈ Sec8W1 M Q Z B t r,
      (∀ l ∈ LB M Q B, ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
        x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r)
    (hfixC : ∀ x ∈ Sec8W1 M Q Z B t r,
      (∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
        x ∈ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) :
    IsOppDecomp (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) (LB M Q B)
      (LB M Q (conjSubgroup r B))
      ((QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r)
      ((QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) := by
  have hWQ : Sec8W1 M Q Z B t r ≤ Q := inf_le_left
  have hA1W : (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r :=
    sup_le inf_le_right hVW
  have hA2W : (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r ≤
      Sec8W1 M Q Z B t r :=
    sup_le inf_le_right hVW
  refine ⟨le_sup_right, hA1W, le_sup_right, hA2W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_antisymm (sup_le hA1W hA2W) hsupW
  · exact le_antisymm hinf (le_inf le_sup_right le_sup_right)
  · intro x hx y hy
    exact Z_le_vone (hc.hyp.toHyp79.comm_mem_V (hWQ hx) (hWQ hy))
  · intro x hx
    exact Z_le_vone (hc.hyp.toHyp79.sq_mem_V (hWQ hx))
  · intro x hx
    exact ⟨fun hxA l hl => (Subgroup.commutator_le.mp (hc.comm_LB_A1_le_vone hs)) l hl x hxA,
      hfixB x hx⟩
  · intro x hx
    exact ⟨fun hxA l hl => (Subgroup.commutator_le.mp (hc.comm_LBC_A2_le_vone hs hr)) l hl x hxA,
      hfixC x hx⟩

theorem stroth53c_of_components
    (hVW : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r)
    (hsupW : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        Sec8W1 M Q Z B t r ≤
          ((QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ⊔
            ((QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r))
    (hinf : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ((QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ⊓
          ((QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ≤
          Sec8V1 M Q Z B t r)
    (hfixB : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Sec8W1 M Q Z B t r,
          (∀ l ∈ LB M Q B, ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
            x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r)
    (hfixC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Sec8W1 M Q Z B t r,
          (∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
            x ∈ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) :
    Stroth53cStatement := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane C L L' V W₁ V₁ hC hL hL' hV hV₁ hW₁
  subst hC hL hL' hV hV₁ hW₁
  exact hc.isOppDecomp_of_components hs hr (hVW G M Q Z B hc n t hs hsp r hr hplane)
    (hsupW G M Q Z B hc n t hs hsp r hr hplane)
    (hinf G M Q Z B hc n t hs hsp r hr hplane)
    (hfixB G M Q Z B hc n t hs hsp r hr hplane)
    (hfixC G M Q Z B hc n t hs hsp r hr hplane)

theorem stroth53c_of_53b_components
    (h53b : Stroth53bStatement)
    (hVW : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r)
    (hinf : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ((QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ⊓
          ((QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ≤
          Sec8V1 M Q Z B t r)
    (hfixB : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Sec8W1 M Q Z B t r,
          (∀ l ∈ LB M Q B, ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
            x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r)
    (hfixC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Sec8W1 M Q Z B t r,
          (∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
            x ∈ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) :
    Stroth53cStatement := by
  refine stroth53c_of_components hVW ?_ hinf hfixB hfixC
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane
  have h := (h53b G M Q Z B hc n t hs hsp r hr hplane (conjSubgroup r B) (hc.CN t)
    (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl).1
  refine hc.hsupW_of_prod ?_
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h x hx
  exact Subgroup.mul_mem_sup ha hb

end CFSG.RankThree.GF2n.Stroth80
