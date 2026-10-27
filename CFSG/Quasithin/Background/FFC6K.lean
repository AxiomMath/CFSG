module

public import CFSG.Quasithin.Background.FFC6F
public import CFSG.Quasithin.Background.FFC6J

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

namespace B59

section CaseA

variable {V : Type} [CommGroup V] [Finite V]

theorem caseA
    (hI : B58Inputs) (hB42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 G = ⊥) (hmin : IsFFStarMin G A) (hL : CFSG.Open.IsComponentOf L G)
    (hLA : ⁅L, A⁆ = L) (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hno : ¬ ThreeRank2 ↥(Kr L A))
    (hb : B51Hyp (Xr L A) (Kr L A)) (hXK : Xr L A = Kr L A)
    (hirr : commV (Kr L A) ∈ IrrPlus (Kr L A) ⊤) (hα : commV (Kr L A) ⊔ fixV (Kr L A) = ⊤)
    (hnat : ∃ n, BinaryNaturalSL (Kr L A) (commV (Kr L A)) (fixV (Kr L A) ⊓ commV (Kr L A)) 2 n) :
    B59Case1 A L := by
  obtain ⟨-, -, -, hst, -, -⟩ := red_basic hV hL hmin.1 hLA
  have hLG : L ≤ G := hL.1
  have hAG : A ≤ G := hmin.1.1
  have hLU : L ≤ stabSub (W0 L A) := le_sup_left.trans hst
  have hAU : A ≤ stabSub (W0 L A) := le_sup_right.trans hst
  have hfaith : L ⊓ centSub (W0 L A) = ⊥ := (B55.faithful_on_fixV hV hO2 hL hmin.1 hLA).1
  have hfaithL := faithL hV hO2 hL hmin hLA
  obtain ⟨hO2b, hFb, hLbq, hLbH, hLbn, hHb2, hoff, hcomm, hsup⟩ := red_aut hV hL hmin.1 hLA
  have hmin' : IsFFStarMin (Xr L A) (Ar L A) := red_min hV hL hmin hLA
  have hVM : ∀ v : ↥(W0 L A), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  obtain ⟨hr, hSyl⟩ := caseA_M hI hB42 hVM hb hmin' hXK hno hirr hnat
  obtain ⟨hsupV, hfA⟩ := lift_q hV hL hmin hLA hr
  have hĀK : Ar L A ≤ Kr L A := hXK ▸ hoff.1
  have hMU : commV (Kr L A) ⊔ fixV (Ar L A) = ⊤ :=
    top_le_iff.1 (hα ▸ sup_le_sup_left (B1.fixV_le_fixV hĀK) _)
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl => hn a (hAG ha) l hl
  obtain ⟨hVU, hcommV, hAq, hcommW⟩ := lift_V hLU hAU hAn hLA hsupV hMU
  have hAL : A ≤ L := A_le_L hV hO2 hLG hAG hn hAU hAq hcommW hĀK
  refine ⟨?_, ?_, by rw [hcommV]; exact hVU⟩
  · obtain ⟨n, hn2⟩ := hnat
    exact ⟨n, binaryNaturalSL_lift hLU hfaithL hcommV hn2⟩
  · exact sylow_of_autSub hAL hLU hfaith hfA hmin.1.2.2.1.isPGroup hSyl

end CaseA

end B59

end FFC

end CFSG.Quasithin
