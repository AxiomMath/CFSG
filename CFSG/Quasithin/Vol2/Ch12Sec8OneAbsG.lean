module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbs
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem sup_uA_le_LT (S : Setting V V₁ L T) : L ⊔ uA V V₁ ≤ L ⊔ T :=
  sup_le_sup_left S.uA_le_T L

theorem sup_uA_le_normalizer_V (S : Setting V V₁ L T) :
    L ⊔ uA V V₁ ≤ Subgroup.normalizer (V : Set G) :=
  S.sup_uA_le_LT.trans S.LT_le_normalizer_V

theorem sup_rconj_uA_eq (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    uA V V₁ ⊔ rconj (uA V V₁) g = L ⊔ uA V V₁ :=
  S.hyp.G23_two hg.mem hg.not_mem

theorem le_inf_rconj (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    V ≤ uA V V₁ ⊓ rconj (uA V V₁) g :=
  (S.hyp.G23_four hg.mem hg.not_mem).1

theorem inf_rconj_le_pCoreOf (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    uA V V₁ ⊓ rconj (uA V V₁) g ≤ pCoreOf 2 (L ⊔ uA V V₁) := by
  rw [← S.sup_rconj_uA_eq hg]
  exact (S.hyp.G23_four hg.mem hg.not_mem).2.1

theorem sup_le_normalizer_inf_rconj (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    L ⊔ uA V V₁ ≤
      Subgroup.normalizer ((uA V V₁ ⊓ rconj (uA V V₁) g : Subgroup G) : Set G) := by
  rw [← S.sup_rconj_uA_eq hg]
  exact (S.hyp.G23_four hg.mem hg.not_mem).2.2.2.2.1

theorem commutator_inf_rconj_le (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    ⁅uA V V₁ ⊓ rconj (uA V V₁) g, L ⊔ uA V V₁⁆ ≤ V := by
  rw [← S.sup_rconj_uA_eq hg]
  exact (S.hyp.G23_five hg.mem hg.not_mem).1

theorem isElemAbelian_inf_rconj (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    IsElemAbelian 2 (uA V V₁ ⊓ rconj (uA V V₁) g) :=
  (S.hyp.G23_five hg.mem hg.not_mem).2

noncomputable def l2Setting (S : Setting V V₁ L T) :
    L2Setting 1 V V₁ L T (Subgroup.normalizer (V₁ : Set G)) :=
  ⟨S.hyp, Classical.choice S.hyp.natural.nonempty_data⟩

theorem pCoreOf_sup_eq (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    pCoreOf 2 (L ⊔ uA V V₁) = (L ⊔ uA V V₁) ⊓ Subgroup.centralizer (V : Set G) := by
  apply le_antisymm
  · have hle : pCoreOf 2 (L ⊔ uA V V₁) ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← S.sup_rconj_uA_eq hg]
      exact S.l2Setting.pCoreOf_I_le_O hg.mem hg.not_mem
    refine le_inf (pCoreOf_le 2 _) ?_
    have : pCoreOf 2 (L ⊔ uA V V₁) ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
      rw [S.centralizer]
      exact hle
    exact this.trans inf_le_right
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx,
          (normalizer_le_normalizer_centralizer'' _ (S.sup_uA_le_normalizer_V hx))⟩
    · have : (L ⊔ uA V V₁) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
        rw [← S.centralizer]
        exact inf_le_inf_right _ S.sup_uA_le_LT
      exact (pCoreOf_isPGroup 2 (L ⊔ T)).to_le this

theorem wA_eq_inf_pCoreOf (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    wA V V₁ = uA V V₁ ⊓ pCoreOf 2 (L ⊔ uA V V₁) := by
  rw [S.pCoreOf_sup_eq hg, ← inf_assoc,
    inf_eq_left.mpr (le_sup_right : uA V V₁ ≤ L ⊔ uA V V₁)]

theorem pCoreOf_sup_le_T (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    pCoreOf 2 (L ⊔ uA V V₁) ≤ T := by
  have h1 : pCoreOf 2 (L ⊔ uA V V₁) ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
    rw [S.pCoreOf_sup_eq hg]
    exact inf_le_inf_right _ S.sup_uA_le_LT
  rw [S.centralizer] at h1
  exact h1.trans (pCoreOf_two_le_of_isSylowTwoOf S.base.sylow_LT)

theorem pCoreOf_sup_le_normalizer_uA (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    pCoreOf 2 (L ⊔ uA V V₁) ≤ Subgroup.normalizer (uA V V₁ : Set G) :=
  (S.pCoreOf_sup_le_T hg).trans S.T_le_normalizer_uA

theorem pCoreOf_sup_le_normalizer_wA (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    pCoreOf 2 (L ⊔ uA V V₁) ≤ Subgroup.normalizer (wA V V₁ : Set G) := by
  intro s hs
  have h1 : s ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer'' _ (S.sup_uA_le_normalizer_V (pCoreOf_le 2 _ hs))
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨S.pCoreOf_sup_le_normalizer_uA hg hs, h1⟩

theorem rconj_wA_eq (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    rconj (wA V V₁) g = rconj (uA V V₁) g ⊓ pCoreOf 2 (L ⊔ uA V V₁) := by
  rw [S.wA_eq_inf_pCoreOf hg, rconj_inf_eq,
    rconj_eq_of_mem_normalizer (hg.mem_normalizer_pCoreOf _)]

theorem wA_inf_rconj_eq (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    wA V V₁ ⊓ rconj (wA V V₁) g = uA V V₁ ⊓ rconj (uA V V₁) g := by
  have hS := S.inf_rconj_le_pCoreOf hg
  rw [S.rconj_wA_eq hg, S.wA_eq_inf_pCoreOf hg]
  apply le_antisymm
  · exact inf_le_inf inf_le_left inf_le_left
  · exact le_inf (le_inf inf_le_left hS) (le_inf inf_le_right hS)

theorem pCoreOf_sup_eq_wA_sup (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    pCoreOf 2 (L ⊔ uA V V₁) = wA V V₁ ⊔ rconj (wA V V₁) g ∧
      ((pCoreOf 2 (L ⊔ uA V V₁) : Subgroup G) : Set G) =
        (wA V V₁ : Set G) * (rconj (wA V V₁) g : Set G) :=
  S.hyp.G23_three (U := uA V V₁) (I := L ⊔ uA V V₁) (S := pCoreOf 2 (L ⊔ uA V V₁))
    (W := wA V V₁) rfl hg.mem hg.not_mem (S.sup_rconj_uA_eq hg).symm rfl
    (S.wA_eq_inf_pCoreOf hg)

theorem wA_le_pCoreOf (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    wA V V₁ ≤ pCoreOf 2 (L ⊔ uA V V₁) := by
  rw [S.wA_eq_inf_pCoreOf hg]
  exact inf_le_right

theorem rconj_wA_le_pCoreOf (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    rconj (wA V V₁) g ≤ pCoreOf 2 (L ⊔ uA V V₁) := by
  rw [S.rconj_wA_eq hg]
  exact inf_le_right

theorem pCoreOf_sup_le_normalizer_X (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    pCoreOf 2 (L ⊔ uA V V₁) ≤ Subgroup.normalizer (rconj (wA V V₁) g : Set G) :=
  le_normalizer_rconj_of (hg.mem_normalizer_pCoreOf _) (S.pCoreOf_sup_le_normalizer_wA hg)

theorem commutator_wA_rconj_le (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    ⁅wA V V₁, rconj (wA V V₁) g⁆ ≤ wA V V₁ ⊓ rconj (wA V V₁) g := by
  rw [Subgroup.commutator_le]
  intro w hw x hx
  have hwS := S.wA_le_pCoreOf hg hw
  have hxS := S.rconj_wA_le_pCoreOf hg hx
  refine ⟨?_, ?_⟩
  · have h1 : x * w⁻¹ * x⁻¹ ∈ wA V V₁ :=
      (Subgroup.mem_normalizer_iff.mp (S.pCoreOf_sup_le_normalizer_wA hg hxS) _).mp
        ((wA V V₁).inv_mem hw)
    have e : ⁅w, x⁆ = w * (x * w⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact (wA V V₁).mul_mem hw h1
  · have h1 : w * x * w⁻¹ ∈ rconj (wA V V₁) g :=
      (Subgroup.mem_normalizer_iff.mp (S.pCoreOf_sup_le_normalizer_X hg hwS) _).mp hx
    have e : ⁅w, x⁆ = (w * x * w⁻¹) * x⁻¹ := by simp [commutatorElement_def]
    rw [e]
    exact (rconj (wA V V₁) g).mul_mem h1 ((rconj (wA V V₁) g).inv_mem hx)

theorem commutator_rconj_uA_mem (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) {a b : G}
    (ha : a ∈ rconj (uA V V₁) g) (hb : b ∈ rconj (uA V V₁) g) : a * b * a⁻¹ * b⁻¹ ∈ V :=
  S.l2Setting.V₁_le_rconj_V hg.mem (S.l2Setting.rconj_commutator_mem ha hb)

theorem mem_inf_of_commutator_mem (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) {u y : G}
    (hu : u ∈ uA V V₁) (huW : u ∉ wA V V₁) (hy : y ∈ rconj (wA V V₁) g)
    (hyu : y * u * y⁻¹ * u⁻¹ ∈ wA V V₁ ⊓ rconj (wA V V₁) g) :
    y ∈ wA V V₁ ⊓ rconj (wA V V₁) g := by
  set U := uA V V₁ with hUdef
  set W := wA V V₁ with hWdef
  set E := W ⊓ rconj W g with hEdef
  have hE : E = U ⊓ rconj U g := S.wA_inf_rconj_eq hg
  have hEN : L ⊔ U ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]
    exact S.sup_le_normalizer_inf_rconj hg
  have hEV : V ≤ E := by
    rw [hE]
    exact S.le_inf_rconj hg
  have hUI : U ≤ L ⊔ U := le_sup_right
  have hWC : W ≤ Hyp1281Two.stabCoset128 E y := by
    intro w hw
    refine Hyp1281Two.mem_stabCoset128.2 ⟨hEN (hUI (wA_le_uA V V₁ hw)), ?_⟩
    have := S.commutator_wA_rconj_le hg (Subgroup.commutator_mem_commutator hw hy)
    exact this
  have huC : u ∈ Hyp1281Two.stabCoset128 E y := by
    refine Hyp1281Two.mem_stabCoset128.2 ⟨hEN (hUI hu), ?_⟩
    have e : u * y * u⁻¹ * y⁻¹ = (y * u * y⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]
    exact E.inv_mem hyu
  have hUC : U ≤ Hyp1281Two.stabCoset128 E y := by
    intro u' hu'
    by_cases hu'W : u' ∈ W
    · exact hWC hu'W
    · have hmem : u⁻¹ * u' ∈ W := (S.mem_wA_or_inv_mul_mem hu hu' huW).resolve_left hu'W
      have : u * (u⁻¹ * u') ∈ Hyp1281Two.stabCoset128 E y :=
        (Hyp1281Two.stabCoset128 E y).mul_mem huC (hWC hmem)
      simpa using this
  have hUgC : rconj U g ≤ Hyp1281Two.stabCoset128 E y := by
    intro a ha
    have haI : a ∈ L ⊔ U := by
      rw [← S.sup_rconj_uA_eq hg]
      exact Subgroup.mem_sup_right ha
    have hyUg : y ∈ rconj U g := by
      have : rconj W g ≤ rconj U g := by
        intro z hz
        rw [mem_rconj] at hz ⊢
        exact wA_le_uA V V₁ hz
      exact this hy
    refine Hyp1281Two.mem_stabCoset128.2 ⟨hEN haI, ?_⟩
    exact hEV (S.commutator_rconj_uA_mem hg ha hyUg)
  have hIC : L ⊔ U ≤ Hyp1281Two.stabCoset128 E y := by
    rw [← S.sup_rconj_uA_eq hg]
    exact sup_le hUC hUgC
  have hgC : g ∈ Hyp1281Two.stabCoset128 E y := hIC (hg.mem_sup U)
  obtain ⟨-, hgy⟩ := Hyp1281Two.mem_stabCoset128.1 hgC
  have hgyW : g * y * g⁻¹ ∈ W := (mem_rconj).mp hy
  have hgyE : g * y * g⁻¹ ∈ E := by
    refine ⟨hgyW, ?_⟩
    have e : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact (rconj W g).mul_mem hgy.2 hy
  have hyinv : y⁻¹ ∈ E := by
    have e : y⁻¹ = (g * y * g⁻¹)⁻¹ * (g * y * g⁻¹ * y⁻¹) := by group
    rw [e]
    exact E.mul_mem (E.inv_mem hgyE) hgy
  simpa using E.inv_mem hyinv

theorem V₁_le_inf_rconj (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    V₁ ≤ wA V V₁ ⊓ rconj (wA V V₁) g := by
  rw [S.wA_inf_rconj_eq hg]
  exact S.V₁_le.trans (S.le_inf_rconj hg)

theorem nine_four (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) {y u : G}
    (hy : y ∈ rconj (wA V V₁) g) (hyW : y ∉ wA V V₁) (hu : u ∈ uA V V₁)
    (hyu : y * u * y⁻¹ * u⁻¹ ∈ V₁) : u ∈ wA V V₁ := by
  by_contra huW
  exact hyW (S.mem_inf_of_commutator_mem hg hu huW hy (S.V₁_le_inf_rconj hg hyu)).1

omit [Finite G] in
theorem nine_seven (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    rconj V₁ g ⊓ centerOf (uA V V₁) = ⊥ := by
  have hle : rconj V₁ g ≤ V := S.l2Setting.V₁_le_rconj_V hg.mem
  have hTI := S.l2Setting.V₁_inf_rconj hg.mem hg.not_mem
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ V ⊓ centerOf (uA V V₁) := ⟨hle hx.1, hx.2⟩
  rw [S.inf_centerOf] at h1
  have h2 : x ∈ V₁ ⊓ rconj V₁ g := ⟨h1, hx.1⟩
  rw [hTI] at h2
  exact h2

theorem rconj_wA_le_T (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    rconj (wA V V₁) g ≤ T :=
  (S.rconj_wA_le_pCoreOf hg).trans (S.pCoreOf_sup_le_T hg)

theorem nine_five (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) :
    centralizerMod (centerOf (uA V V₁)) (rconj (wA V V₁) g) (uA V V₁) =
        wA V V₁ ⊓ rconj (wA V V₁) g ∧
      centralizerMod V₁ (rconj (wA V V₁) g) (uA V V₁) = wA V V₁ ⊓ rconj (wA V V₁) g := by
  set U := uA V V₁ with hUdef
  set Zu := centerOf U with hZudef
  set W := wA V V₁ with hWdef
  set X := rconj W g with hXdef
  set E := W ⊓ X with hEdef
  set H := Subgroup.normalizer (V₁ : Set G) with hHdef
  have hA := S.base
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := normalizer_le_normalizer_uA V V₁
  have hHZu : H ≤ Subgroup.normalizer (Zu : Set G) :=
    hHU.trans (normalizer_le_normalizer_centerOf U)
  have hHN : H ≤ Subgroup.normalizer (V₁ : Set G) := le_rfl
  set C := centralizerMod Zu H U with hCdef
  have hHC : H ≤ Subgroup.normalizer (C : Set G) :=
    CFSG.Quasithin.le_normalizer_centralizerMod hHZu Subgroup.le_normalizer hHU
  set R := T ⊓ C with hRdef
  set F := centralizerMod V₁ U R with hFdef
  have hUH : U ≤ H := S.uA_le_normalizer
  have hfr := fun x (hx : x ∈ H) =>
    exists_mul_mem_normalizer_inf_of_isSylowTwoOf hHC hA.sylow_H hx
  have hFn : ∀ n ∈ H, n ∈ Subgroup.normalizer (R : Set G) →
      n ∈ Subgroup.normalizer (F : Set G) := by
    intro n hn hnR
    have hz : Subgroup.zpowers n ≤ Subgroup.normalizer (F : Set G) :=
      CFSG.Quasithin.le_normalizer_centralizerMod (V₁ := V₁) (X := U) (U := R)
        (Subgroup.zpowers_le.mpr (hHN hn)) (Subgroup.zpowers_le.mpr (hHU hn))
        (Subgroup.zpowers_le.mpr hnR)
    exact hz (Subgroup.mem_zpowers n)
  have hVF : V ≤ F := by
    intro v hv
    refine ⟨le_uA V V₁ hv, hA.V_le_N hv, fun r hr => ?_⟩
    have hrT : r ∈ T := hr.1
    have hrC : r ∈ C := hr.2
    have hrN : r ∈ Subgroup.normalizer (V : Set G) := hA.T_le_normV hrT
    have h1 : r * v * r⁻¹ * v⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.mp hrN v).mp hv) (V.inv_mem hv)
    have h2 : r * v * r⁻¹ * v⁻¹ ∈ Zu := hrC.2.2 v (le_uA V V₁ hv)
    have h3 : r * v * r⁻¹ * v⁻¹ ∈ V ⊓ Zu := ⟨h1, h2⟩
    rw [S.inf_centerOf] at h3
    have e : v * r * v⁻¹ * r⁻¹ = (r * v * r⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact V₁.inv_mem h3
  have hUF : U ≤ F ⊔ Zu := by
    refine conjClosure_le fun x hx v hv => ?_
    obtain ⟨c, hc, n, hnH, hnR, rfl⟩ := hfr x hx
    have hnF : n ∈ Subgroup.normalizer (F : Set G) := hFn n hnH hnR
    have hf : n * v * n⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hnF v).mp (hVF hv)
    have hfU : n * v * n⁻¹ ∈ U := hf.1
    have hcf : c * (n * v * n⁻¹) * c⁻¹ * (n * v * n⁻¹)⁻¹ ∈ Zu := hc.2.2 _ hfU
    have e : c * n * v * (c * n)⁻¹ =
        (c * (n * v * n⁻¹) * c⁻¹ * (n * v * n⁻¹)⁻¹) * (n * v * n⁻¹) := by group
    rw [e]
    have := Subgroup.mul_mem_sup hcf hf
    rwa [sup_comm] at this
  obtain ⟨u, huF, huW⟩ : ∃ u ∈ F, u ∉ W := by
    by_contra hall
    push Not at hall
    apply S.not_le_centralizer_V
    have : U ≤ W := hUF.trans (sup_le (fun u hu => hall u hu) (centerOf_uA_le_wA V V₁))
    exact fun x hx => (this hx).2
  have key : centralizerMod Zu X U ≤ E := by
    intro y hy
    obtain ⟨hyX, hyN, hyc⟩ := hy
    have hyT : y ∈ T := S.rconj_wA_le_T hg hyX
    have hyH : y ∈ H := hA.T_le_H hyT
    have hyC : y ∈ C := ⟨hyH, hyN, hyc⟩
    have hyR : y ∈ R := ⟨hyT, hyC⟩
    by_contra hyE
    have hyW : y ∉ W := fun hyW => hyE ⟨hyW, hyX⟩
    have hcomm : y * u * y⁻¹ * u⁻¹ ∈ V₁ := by
      have h1 := huF.2.2 y hyR
      have e : y * u * y⁻¹ * u⁻¹ = (u * y * u⁻¹ * y⁻¹)⁻¹ := by group
      rw [e]
      exact V₁.inv_mem h1
    exact huW (S.nine_four hg hyX hyW huF.1 hcomm)
  have hEX : E ≤ X := inf_le_right
  have hEU : ∀ e ∈ E, e ∈ U := fun e he => wA_le_uA V V₁ he.1
  have hE1 : E ≤ centralizerMod V₁ X U := by
    intro e he
    exact ⟨hEX he, hUH (hEU e he), fun u hu => S.commutator_mem (hEU e he) hu⟩
  have hE2 : centralizerMod V₁ X U ≤ centralizerMod Zu X U := by
    intro y hy
    obtain ⟨hyX, hyN, hyc⟩ := hy
    exact ⟨hyX, hHZu hyN, fun u hu => S.V₁_le_centerOf (hyc u hu)⟩
  exact ⟨le_antisymm key (hE1.trans hE2), le_antisymm ((hE2.trans key)) hE1⟩

end Setting

end L128A

end CFSG.Quasithin.H13
