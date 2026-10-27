module

public import CFSG.Quasithin.Background.FFC6Q
public import CFSG.Quasithin.Background.FFC5Tail
public import CFSG.Quasithin.Background.FFC6F

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace B59

section CaseVV

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem b482Module_lift {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W)
    (hf : ∀ g ∈ L, (∀ v ∈ W, g v = v) → g = 1) (hcomm : commV L = commSub W L)
    (h : B482Module (autSub L W) (commV (autSub L W))) : B482Module L (commV L) := by
  obtain ⟨hcard, hnat, hind⟩ := h
  have hmap : (commV (autSub L W)).map W.subtype = commV L := by
    rw [map_commV_aut hst, ← hcomm]
  have hcW : commV L ≤ W := by
    rw [hcomm]
    exact commSub_le_of_invariant fun x hx w hw => (hst hx w).2 hw
  refine ⟨?_, binaryNaturalSL_lift hst hf hcomm hnat, ?_⟩
  · rw [← hmap, Subgroup.card_map_of_injective W.subtype_injective]
    exact hcard
  · rintro ⟨A', B', hA, hB, hAi, hBi, hsup, hinf⟩
    apply hind
    have hAW : A' ≤ W := (hsup ▸ le_sup_left : A' ≤ commV L).trans hcW
    have hBW : B' ≤ W := (hsup ▸ le_sup_right : B' ≤ commV L).trans hcW
    have hmapA : (A'.comap W.subtype).map W.subtype = A' := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.2 hAW]
    have hmapB : (B'.comap W.subtype).map W.subtype = B' := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.2 hBW]
    have hinvc : ∀ P : Subgroup V, XMod.IsInv ↥L P →
        XMod.IsInv ↥(autSub L W) (P.comap W.subtype) := by
      intro P hP φ w hw
      obtain ⟨g, hg, hgφ⟩ := mem_autSub.1 φ.2
      have h1 : (((φ : MulAut ↥W) w : ↥W) : V) = (g : MulAut V) (w : V) := by
        rw [← hgφ]
        rfl
      show (((φ : MulAut ↥W) w : ↥W) : V) ∈ P
      rw [h1]
      exact hP ⟨g.1, hg⟩ _ hw
    refine ⟨A'.comap W.subtype, B'.comap W.subtype, ?_, ?_, hinvc A' hAi, hinvc B' hBi, ?_, ?_⟩
    · refine bot_lt_iff_ne_bot.2 fun hb => hA.ne' ?_
      rw [← hmapA, hb, Subgroup.map_bot]
    · refine bot_lt_iff_ne_bot.2 fun hb => hB.ne' ?_
      rw [← hmapB, hb, Subgroup.map_bot]
    · apply Subgroup.map_injective W.subtype_injective
      rw [Subgroup.map_sup, hmapA, hmapB, hsup, hmap]
    · rw [← Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective,
        Subgroup.map_inf _ _ _ W.subtype_injective, hmapA, hmapB, hinf]

theorem caseV (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥)
    (hmin : IsFFStarMin G A) (hL : CFSG.Open.IsComponentOf L G) (hLA : ⁅L, A⁆ = L)
    (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hXK : Xr L A = Kr L A)
    (hirr : commV (Kr L A) ∈ IrrPlus (Kr L A) ⊤) (hα : commV (Kr L A) ⊔ fixV (Kr L A) = ⊤)
    (hnat : BinaryNaturalSL (Kr L A) (commV (Kr L A)) (fixV (Kr L A) ⊓ commV (Kr L A)) 3 1)
    (hcard : Nat.card ↥(commV (Kr L A)) = 2 ^ 4) : B59Case5 A L := by
  obtain ⟨-, -, -, hst, -, -⟩ := red_basic hV hL hmin.1 hLA
  have hLG : L ≤ G := hL.1
  have hAG : A ≤ G := hmin.1.1
  have hLU : L ≤ stabSub (W0 L A) := le_sup_left.trans hst
  have hAU : A ≤ stabSub (W0 L A) := le_sup_right.trans hst
  have hfaithL := faithL hV hO2 hL hmin hLA
  obtain ⟨-, -, -, -, -, -, hoff, -, -⟩ := red_aut hV hL hmin.1 hLA
  have hmin' : IsFFStarMin (Xr L A) (Ar L A) := red_min hV hL hmin hLA
  have hVM : ∀ v : ↥(W0 L A), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  obtain ⟨hB482, hcard4, hr⟩ := caseV_M hVM hXK hmin' hirr hα hnat hcard
  obtain ⟨hsupV, hfA⟩ := lift_q hV hL hmin hLA (by exact_mod_cast hr)
  have hĀK : Ar L A ≤ Kr L A := hXK ▸ hoff.1
  have hMU : commV (Kr L A) ⊔ fixV (Ar L A) = ⊤ :=
    top_le_iff.1 (hα ▸ sup_le_sup_left (B1.fixV_le_fixV hĀK) _)
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl => hn a (hAG ha) l hl
  obtain ⟨hVU, hcommV, hAq, hcommW⟩ := lift_V hLU hAU hAn hLA hsupV hMU
  have hAL : A ≤ L := A_le_L hV hO2 hLG hAG hn hAU hAq hcommW hĀK
  have hfA' : ∀ g ∈ A, (∀ v ∈ W0 L A, g v = v) → g = 1 := fun g hg hgW => by
    have : g ∈ A ⊓ centSub (W0 L A) := ⟨hg, hgW⟩
    rw [hfA, Subgroup.mem_bot] at this
    exact this
  have hcardA : Nat.card ↥A = 4 := (card_autSub_eq hAU hfA').symm.trans hcard4
  have hnatL := binaryNaturalSL_lift hLU hfaithL hcommV hnat
  have hiso : Nonempty (↥L ≃* ↥(Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) := by
    obtain ⟨π, hπ⟩ := BinaryNaturalSL.exists_zmod hnatL
    exact nonempty_equiv_of_natural_zmod hπ
  exact ⟨hiso, hAL, hcardA, b482Module_lift hLU hfaithL hcommV hB482, by rw [hcommV]; exact hVU⟩

end CaseVV

end B59

end FFC

end CFSG.Quasithin
