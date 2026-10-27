module

public import CFSG.Quasithin.H13.GoldschmidtC137Pt1Aux
public import CFSG.Quasithin.H13.GoldschmidtC137CDict
public import CFSG.Quasithin.H13.GoldschmidtC137CBase
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin3
public import CFSG.Quasithin.H13.GoldschmidtC137S6Std

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace C137Base

variable [Finite G] {X T V L P : Subgroup G} (h : C137Base X T V L P)
include h

theorem R_le_N : pCoreOf 2 P ≤ normalizer (V : Set G) :=
  ((CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans h.hPX.le).trans h.hXN

theorem R_le_X : pCoreOf 2 P ≤ X :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans h.hPX.le

theorem autI_P_le_N_J :
    autI h.hVe P ≤ normalizer (autI h.hVe (thompsonJ (pCoreOf 2 P)) : Set _) :=
  autI_le_normalizer_autI_gc h.hVe (P_le_N_J P)

theorem exists_offender (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) :
    ∃ A : Subgroup G, IsFFOffender (pCoreOf 2 P) V A :=
  (offenderImages_nonempty_iff h.hVe).1 ((offenderImages_nonempty_iff_not_le h.hVe).2 hJ)


end C137Base

namespace C137FrameB

variable [Finite G] {X T V L P : Subgroup G} {h : C137Base X T V L P} (F : C137FrameB h)

theorem R1_map_le_X : R1.map F.ρ ≤ autI h.hVe X := by
  rw [← F.hX]
  exact Subgroup.map_mono le_top

theorem point_J_cases (hP : autI h.hVe P = H1.map F.ρ)
    (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) :
    autI h.hVe (thompsonJ (pCoreOf 2 P)) = Z1.map F.ρ ∨
      autI h.hVe (thompsonJ (pCoreOf 2 P)) = R1.map F.ρ := by
  set R := pCoreOf 2 P with hRdef
  have hRN : R ≤ normalizer (V : Set G) := h.R_le_N
  have hVR : V ≤ R := h.toBaum.hVR
  have hRX : R ≤ X := h.R_le_X
  set J := autI h.hVe (thompsonJ R) with hJdef
  have hJR : J ≤ autI h.hVe R := autI_mono h.hVe (thompsonJ_le_self R)
  have hJX : J ≤ autI h.hVe X := hJR.trans (autI_mono h.hVe hRX)
  set K := J.comap F.ρ with hK
  have hKmap : K.map F.ρ = J := F.map_comap_eq hJX
  have hKR1 : K ≤ R1 := by
    intro x hx
    have hx' : F.ρ x ∈ R1.map F.ρ := hR ▸ hJR hx
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [← F.inj hyx]
  obtain ⟨A, hA⟩ := h.exists_offender hJ
  have hB : autI h.hVe A ∈ offenderImages h.hVe R := ⟨A, hA, rfl⟩
  have hBoff := offenderImages_isFFStarOffender h.hVe hVR hRN hB
  have hBX : IsFFStarOffender (autI h.hVe X) (autI h.hVe A) :=
    isFFStarOffender_mono (autI_mono h.hVe hRX) hBoff
  have hBle : autI h.hVe A ≤ J := autI_mono h.hVe (le_iSup₂_of_le A hA.1 le_rfl)
  set B' := (autI h.hVe A).comap F.ρ with hB'
  have hB'map : B'.map F.ρ = autI h.hVe A := F.map_comap_eq (hBle.trans hJX)
  have hoff : IsOffG 6 Mod.ut0 B' := (F.offender_ρ B').1 (by rw [hB'map]; exact hBX)
  obtain ⟨hB'ne, hB'F⟩ := offender_F_ge hoff
  have hB'K : B' ≤ K := fun x hx => hBle hx
  have hτ : Equiv.swap (4 : Fin 6) 5 ∈ K := hB'K (R1_swap_mem (hB'K.trans hKR1) hB'ne hB'F)
  have hnorm := h.autI_P_le_N_J
  have hKN : ∀ x ∈ H1, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk
    have hρx : F.ρ x ∈ autI h.hVe P := by rw [hP]; exact ⟨x, hx, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.1 (hnorm hρx) (F.ρ k)).1 hk
    show F.ρ (x * k * x⁻¹) ∈ J
    simpa [map_mul, map_inv] using h2
  rcases R1_normal_cases hKR1 hτ hKN with h1 | h1
  · left
    rw [← hKmap, h1]
  · right
    rw [← hKmap, h1]

theorem point_no_strong (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ) :
    ∀ B, ¬ IsStrongFFStarOffender (autI h.hVe (pCoreOf 2 P)) B := by
  intro B hB
  have hBR : B ≤ R1.map F.ρ := hR ▸ hB.1.1
  set K := B.comap F.ρ with hK
  have hKmap : K.map F.ρ = B := F.map_comap_eq (hBR.trans F.R1_map_le_X)
  have hKR1 : K ≤ R1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hBR hx
    rwa [← F.inj hyx]
  have hlt := (rAV_lt_one_iff (fun v => IntMod.sq_eq_one v) hB.1.isA2).1 hB.2
  rw [F.card_V, ← hKmap, F.card_ρ, F.card_fixV_ρ] at hlt
  have := R1_F_le hKR1
  rw [card_map_act] at this
  have h2 : Nat.card K * (cK F.k * Nat.card (fixV (K.map (Mod.act 6 Mod.ut0)))) ≤
      16 * cK F.k := by
    calc _ = cK F.k * (Nat.card K * Nat.card (fixV (K.map (Mod.act 6 Mod.ut0)))) := by ring
      _ ≤ cK F.k * 16 := Nat.mul_le_mul_left _ this
      _ = 16 * cK F.k := by ring
  omega


end C137FrameB

end CFSG.Quasithin.H13.U3.GC137
