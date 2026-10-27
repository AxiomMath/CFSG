module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Setting
public import CFSG.LocalAnalysis.StandardType.FS81.RootE8A
public import CFSG.LocalAnalysis.StandardType.FS81.S7Fusion
public import CFSG.LocalAnalysis.StandardType.FS81.S79Radical
public import CFSG.LocalAnalysis.StandardType.FS81.RootFusionGen

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem RootSetting.centralizer_le_of_e8 {G : Type} [Group G] [Finite G] {r : Row} {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (r.n + 1)} {Y : Subgroup G} (h : RootSetting r b₀ K E B Y)
    (hr : r ≠ Row.D6) (hC : RowCentAt r) (hR : E8RadicalAt r) (hA : E8AutAt r) :
    Subgroup.centralizer ({b₀} : Set G) ≤ Y := by
  obtain ⟨R, hRC, hRn, hR3, hCR⟩ := hC G b₀ K E h.std B h.adapted h.recOut h.fus
  obtain ⟨t₀, L, U, ht₀, hLY, hLt₀, hU2, ht₀U, hUY, hUt₀, hUmax, hirr, hAL⟩ :=
    hR G b₀ K E B Y h
  have hC' : Subgroup.centralizer ({b₀} : Set G) =
      R ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Y) :=
    calc Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K) := hCR
      _ = R ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Y) := by rw [h.cap]
  have hRY : R ≤ Subgroup.centralizer (Y : Set G) := h.core R hRC hRn hR3
  have hRbot : R = ⊥ :=
    (s79_radical (A := s79A r B) h.centralizer_inf_eq_bot hC' hRY
      (fun P hP h1 h2 => h.eq_bot_of_isPGroup_two hP h1 h2)
      ht₀ hLY hLt₀ hU2 ht₀U hUY hUt₀ hUmax hirr
      (isElemAbelian_s79A B) (card_s79A hr B) hAL
      (fun F hF h9 => h.exists_conj_mem_of_le_s79A hr (hA G b₀ K E B Y h) hF h9)
      (fun t ht _ => centralizer_inf_le_pCoreOf_of_isCharTwoType h.charTwo ht)).1
  have hinf : Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.centralizer ({b₀} : Set G) := by
    rw [h.cap, hCR, hRbot, bot_sup_eq]
  exact inf_eq_left.mp hinf

theorem RootSetting.exists_conj_eq_of_conj_mem {G : Type} [Group G] [Finite G] {r : Row}
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G (r.n + 1)} {Y : Subgroup G}
    (h : RootSetting r b₀ K E B Y) (hA : E8AutAt r) (hT : E8TorusAt r) {g : G}
    (hg : g * b₀ * g⁻¹ ∈ Y) : ∃ y ∈ Y, g * b₀ * g⁻¹ = y * b₀ * y⁻¹ := by
  have hfusE : ∀ a : G, a * b₀ * a⁻¹ ∈ E →
      ∃ x ∈ Subgroup.normalizer (E : Set G), a * b₀ * a⁻¹ = x * b₀ * x⁻¹ := by
    intro a ha
    obtain ⟨x, hx, hx'⟩ := h.fus.2 a (by simpa [h.adapted.1] using ha)
    exact ⟨x, by simpa [h.adapted.1] using hx, hx'⟩
  refine exists_conj_Y_of_toral (B := E) (W := Y) h.std.2.1.2.2.1 hfusE
    (hA G b₀ K E B Y h) (fun a ha => ?_) hg
  have hord : orderOf (a * b₀ * a⁻¹) = 3 := by
    have : orderOf (a * b₀ * a⁻¹) = orderOf b₀ := by
      simpa using (MulAut.conj a).orderOf_eq b₀
    rw [this]
    exact h.std.2.1.1.1
  exact hT G b₀ K E B Y h (a * b₀ * a⁻¹) ha hord

theorem l3RootFusionAt_E7_of (hC : RowCentAt Row.E7) (hR : E8RadicalAt Row.E7)
    (hA : E8AutAt Row.E7) (hT : E8TorusAt Row.E7) (hI : E8InvCommAt Row.E7)
    (hRC : E8RootCentAt Row.E7) : L3RootFusionAt Row.E7 := by
  intro G _ _ b₀ K E hstd hchar B hB hrec hfus Y hY hcap hcore
  have h : RootSetting Row.E7 b₀ K E B Y := ⟨hstd, hchar, hB, hrec, hfus, hY, hcap, hcore⟩
  have hbC := h.centralizer_le_of_e8 (by decide) hC hR hA
  have hfusY : ∀ a : G, a * b₀ * a⁻¹ ∈ Y → ∃ y ∈ Y, a * b₀ * a⁻¹ = y * b₀ * y⁻¹ :=
    fun a ha => h.exists_conj_eq_of_conj_mem hA hT ha
  obtain ⟨S, t, hS, htS, ht2, htc, htC⟩ := hRC G b₀ K E B Y h hbC hfusY hbC hfusY
  refine ⟨S, t, hS, htS, ht2, htc, fun a ha => ?_⟩
  refine mem_of_conj_mem_of_commute_conj hbC (fun x hx => hfusY x (htC hx))
    (fun a' ha' => ?_) ha
  refine hI G b₀ K E B Y h _ ha' ?_
  have : orderOf (a' * t * a'⁻¹) = orderOf t := by
    simpa using (MulAut.conj a').orderOf_eq t
  rw [this, ht2]

end CFSG.StandardType.FrameRoute.FS81
