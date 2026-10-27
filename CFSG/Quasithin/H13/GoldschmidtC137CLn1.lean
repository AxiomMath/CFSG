module

public import CFSG.Quasithin.H13.GoldschmidtC137CPt1
public import CFSG.Quasithin.H13.GoldschmidtC137Off
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin5

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace C137Base

variable [Finite G] {X T V L P : Subgroup G} (h : C137Base X T V L P)
include h

theorem hVT : V ≤ T := (C124.le_pCoreOf_of_reduced h.hred).trans h.hQT

theorem hTN : T ≤ normalizer (V : Set G) := h.hT.1.trans h.hXN

theorem line_isMax_T (hall : ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ pCoreOf 2 P)
    {A : Subgroup G} (hA : IsMaxElemAbelian (pCoreOf 2 P) A) : IsMaxElemAbelian T A := by
  obtain ⟨AT, hAT⟩ := exists_isMaxElemAbelian T
  have h1 : Nat.card AT ≤ Nat.card A := hA.2.2 AT (hall AT hAT) hAT.2.1
  exact ⟨hA.1.trans h.hRT, hA.2.1, fun B hBT hBe => (hAT.2.2 B hBT hBe).trans h1⟩


end C137Base

namespace C137FrameB

variable [Finite G] {X T V L P : Subgroup G} {h : C137Base X T V L P} (F : C137FrameB h)

theorem offender_two_cases {B : Subgroup (MulAut (IntMod V h.hVe))} (hBT : B ≤ T6.map F.ρ)
    (hoff : IsFFStarOffender (autI h.hVe X) B) (hc : Nat.card B ≤ 2) :
    B = Z0.map F.ρ ∨ B = Z2.map F.ρ ∨ B = Z1.map F.ρ := by
  set K := B.comap F.ρ with hK
  have hKmap : K.map F.ρ = B := F.map_comap_eq hoff.1
  have hKT6 : K ≤ T6 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hBT hx
    rwa [← F.inj hyx]
  have hKoff : IsOffG 6 Mod.ut0 K := (F.offender_ρ K).1 (by rw [hKmap]; exact hoff)
  obtain ⟨hKne, hKF⟩ := offender_F_ge hKoff
  have hK1 : 1 < Nat.card K := (Subgroup.one_lt_card_iff_ne_bot _).2 hKne
  have hK2 : Nat.card K = 2 := by
    have := F.card_ρ K
    rw [hKmap] at this
    omega
  rcases T6_offender_two hKT6 hK2 hKF with h0 | h0 | h0
  · left
    rw [← hKmap, h0]
  · right
    left
    rw [← hKmap, h0]
  · right
    right
    rw [← hKmap, h0]

theorem Z_le_R2 {B : Subgroup (MulAut (IntMod V h.hVe))}
    (hB : B = Z0.map F.ρ ∨ B = Z2.map F.ρ ∨ B = Z1.map F.ρ) : B ≤ R2.map F.ρ := by
  rcases hB with rfl | rfl | rfl
  · exact Subgroup.map_mono Z0_le_R2
  · exact Subgroup.map_mono Z2_le_R2
  · exact Subgroup.map_mono Z1_le_R2

theorem line_A_le_R (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2)
    {A : Subgroup G} (hA : IsMaxElemAbelian T A) : A ≤ pCoreOf 2 P := by
  have hAX : A ≤ X := hA.1.trans h.hT.1
  by_cases hAC : A ≤ centralizer (V : Set G)
  · exact fun a ha => h.hTCR ⟨hA.1 ha, hAC ha⟩
  · have hB : autI h.hVe A ∈ offenderImages h.hVe T := ⟨A, ⟨hA, hAC⟩, rfl⟩
    have hoff := offenderImages_isFFStarOffender h.hVe h.hVT h.hTN hB
    have hoffX := isFFStarOffender_mono (autI_mono h.hVe h.hT.1) hoff
    have hBT : autI h.hVe A ≤ T6.map F.ρ := F.hT ▸ hoff.1
    have hcard : Nat.card (autI h.hVe A) ≤ 2 := h5 A hA
    have hBR := Z_le_R2 F (F.offender_two_cases hBT hoffX hcard)
    refine le_of_autI_le h.hVe h.hTN h.hRT h.hTCR hA.1 ?_
    rw [hR]
    exact hBR

theorem line_offender_cases (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2)
    {A : Subgroup G} (hA : IsFFOffender (pCoreOf 2 P) V A) :
    autI h.hVe A = Z0.map F.ρ ∨ autI h.hVe A = Z2.map F.ρ ∨ autI h.hVe A = Z1.map F.ρ := by
  have hAT : IsMaxElemAbelian T A := h.line_isMax_T (fun A' hA' => F.line_A_le_R hR h5 hA') hA.1
  have hB : autI h.hVe A ∈ offenderImages h.hVe (pCoreOf 2 P) := ⟨A, hA, rfl⟩
  have hoff := offenderImages_isFFStarOffender h.hVe h.toBaum.hVR h.R_le_N hB
  have hoffX := isFFStarOffender_mono (autI_mono h.hVe h.R_le_X) hoff
  have hBT : autI h.hVe A ≤ T6.map F.ρ := by
    have h1 : autI h.hVe A ≤ R2.map F.ρ := hR ▸ hoff.1
    exact h1.trans (Subgroup.map_mono (R2_le_T6))
  exact F.offender_two_cases hBT hoffX (h5 A hAT)


end C137FrameB

end CFSG.Quasithin.H13.U3.GC137
