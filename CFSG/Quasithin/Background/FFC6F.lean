module

public import CFSG.Quasithin.Background.FFC6A
public import CFSG.Quasithin.Background.FFC6C
public import CFSG.Quasithin.Background.FFC6E

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace B59

section Cases

variable {V : Type} [CommGroup V] [Finite V]

theorem red_min (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L G) (hmin : IsFFStarMin G A) (hLA : ⁅L, A⁆ = L) :
    IsFFStarMin (Xr L A) (Ar L A) := by
  obtain ⟨hn', hsq, hker, hst, hLnc, hAnc⟩ := red_basic hV hL hmin.1 hLA
  have hW : ∀ a ∈ A, ∀ w ∈ W0 L A, a w ∈ W0 L A := fun a ha w hw =>
    (hst (Subgroup.mem_sup_right ha) w).2 hw
  have hWA : commSub (W0 L A) A ≠ ⊥ := by
    intro h
    apply hAnc
    intro a ha u hu
    exact (commSub_eq_bot_iff.1 h) hu a ha
  have h1 := (B1_5_2 hV hmin hW hWA).1
  have hXG : Xr L A ≤ autSub G (W0 L A) := autSub_mono (sup_le hL.1 hmin.1.1) _
  exact isFFStarMin_of_le h1 (autSub_mono le_sup_right _) hXG

omit [Finite V] in
theorem A_quot {L A : Subgroup (MulAut V)} {W₀ : Subgroup V} (hAW : A ≤ stabSub W₀)
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (hsup : commSub W₀ L ⊔ fixV A = ⊤) :
    ∀ a ∈ A, ∀ v : V, a v * v⁻¹ ∈ commSub W₀ L := by
  have hAinv : ∀ a ∈ A, ∀ w ∈ W₀, a w ∈ W₀ := fun a ha w hw => (hAW ha w).2 hw
  have hUA : ∀ a ∈ A, ∀ u ∈ commSub W₀ L, a u ∈ commSub W₀ L :=
    B1.commSub_invariant_of_normalizes (Y := L) (Bg := A) hAn hAinv
  intro a ha v
  obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 (hsup ▸ (Subgroup.mem_top v))
  have : a (u * c) * (u * c)⁻¹ = a u * u⁻¹ := by
    rw [map_mul, hc a ha]; simp [mul_comm]
  rw [this]
  exact (commSub W₀ L).mul_mem (hUA a ha u hu) ((commSub W₀ L).inv_mem hu)

omit [Finite V] in
theorem lift_V {A L : Subgroup (MulAut V)} {W : Subgroup V} (hLU : L ≤ stabSub W)
    (hAU : A ≤ stabSub W) (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L)
    (hLA : ⁅L, A⁆ = L) (hsupV : W ⊔ fixV A = ⊤)
    (hMU : commV (autSub L W) ⊔ fixV (autSub A W) = ⊤) :
    commSub W L ⊔ fixV A = ⊤ ∧ commV L = commSub W L ∧
      (∀ a ∈ A, ∀ v : V, a v * v⁻¹ ∈ commV L) ∧ commV L ≤ W := by
  have hmapU := congrArg (Subgroup.map W.subtype) hMU
  rw [Subgroup.map_sup, map_commV_aut hLU, map_subtype_fixV_autSub hAU, Subgroup.map_top,
    Subgroup.range_subtype] at hmapU
  have hVU : commSub W L ⊔ fixV A = ⊤ := by
    refine eq_top_iff.2 ?_
    calc (⊤ : Subgroup V) = W ⊔ fixV A := hsupV.symm
      _ ≤ commSub W L ⊔ fixV A := by
        refine sup_le ?_ le_sup_right
        calc W = commSub W L ⊔ W ⊓ fixV A := hmapU.symm
          _ ≤ commSub W L ⊔ fixV A := sup_le le_sup_left (inf_le_right.trans le_sup_right)
  have hcommV : commV L = commSub W L := commV_eq_commSub_of_sup hLU hAU hAn hLA hVU
  refine ⟨hVU, hcommV, ?_, ?_⟩
  · rw [hcommV]
    exact A_quot hAU hAn hVU
  · rw [hcommV]
    exact commSub_le_of_invariant (fun x hx w hw => (hLU hx w).2 hw)

theorem A_le_L (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)} {W : Subgroup V}
    (hO2 : pCoreOf 2 G = ⊥) (hLG : L ≤ G) (hAG : A ≤ G)
    (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hAU : A ≤ stabSub W)
    (hAq : ∀ a ∈ A, ∀ v : V, a v * v⁻¹ ∈ commV L) (hcommW : commV L ≤ W)
    (hĀK : autSub A W ≤ autSub L W) : A ≤ L := by
  intro a ha
  have hmem : (resHom W) ⟨a, hAU ha⟩ ∈ autSub L W :=
    hĀK (mem_autSub.2 ⟨⟨a, hAU ha⟩, ha, rfl⟩)
  obtain ⟨l, hlL, hlr⟩ := mem_autSub.1 hmem
  refine mem_of_eq_on hV hO2 hLG hAG hn hcommW hAq ha hlL ?_
  intro w hw
  have := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : V)) hlr
  exact this.symm

theorem lift_q (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L G) (hmin : IsFFStarMin G A) (hLA : ⁅L, A⁆ = L)
    (hr : (1 : ℚ) ≤ rAV (Ar L A)) : W0 L A ⊔ fixV A = ⊤ ∧ A ⊓ centSub (W0 L A) = ⊥ := by
  obtain ⟨hn', hsq, hker, hst, hLnc, hAnc⟩ := red_basic hV hL hmin.1 hLA
  have hns : ¬ IsStrongFFStarOffender (autSub G (W0 L A)) (autSub A (W0 L A)) :=
    fun h => absurd h.2 (not_lt.2 hr)
  have hW : ∀ a ∈ A, ∀ w ∈ W0 L A, a w ∈ W0 L A := fun a ha w hw =>
    (hst (Subgroup.mem_sup_right ha) w).2 hw
  have hWA : commSub (W0 L A) A ≠ ⊥ := by
    intro h
    apply hAnc
    intro a ha u hu
    exact (commSub_eq_bot_iff.1 h) hu a ha
  exact (B1_5_2 hV hmin hW hWA).2 hns

theorem faithL (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥)
    (hL : CFSG.Open.IsComponentOf L G) (hmin : IsFFStarMin G A) (hLA : ⁅L, A⁆ = L) :
    ∀ g ∈ L, (∀ v ∈ W0 L A, g v = v) → g = 1 := by
  have hfaith : L ⊓ centSub (W0 L A) = ⊥ := (B55.faithful_on_fixV hV hO2 hL hmin.1 hLA).1
  intro g hg hgW
  have : g ∈ L ⊓ centSub (W0 L A) := ⟨hg, hgW⟩
  rw [hfaith, Subgroup.mem_bot] at this
  exact this

theorem caseD (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥)
    (hmin : IsFFStarMin G A) (hL : CFSG.Open.IsComponentOf L G) (hLA : ⁅L, A⁆ = L)
    (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hno : ¬ ThreeRank2 ↥(Kr L A))
    (hP5 : B51Part5 (Xr L A) (Kr L A)) (hd : B51Case1ii (Xr L A) (Kr L A)) : B59Case3 A L := by
  obtain ⟨-, -, -, hst, -, -⟩ := red_basic hV hL hmin.1 hLA
  have hLG : L ≤ G := hL.1
  have hAG : A ≤ G := hmin.1.1
  have hLU : L ≤ stabSub (W0 L A) := le_sup_left.trans hst
  have hAU : A ≤ stabSub (W0 L A) := le_sup_right.trans hst
  have hfaithL := faithL hV hO2 hL hmin hLA
  obtain ⟨hO2b, hFb, hLbq, hLbH, hLbn, hHb2, hoff, hcomm, hsup⟩ := red_aut hV hL hmin.1 hLA
  have hmin' : IsFFStarMin (Xr L A) (Ar L A) := red_min hV hL hmin hLA
  obtain ⟨hXK, n, K', hK', hf', hcK, I, π, hind, hsupI, hreal, -, hq⟩ := hd
  have hVM : ∀ v : ↥(W0 L A), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  have hquad : IsQuadratic (Ar L A) := B1_4_3 hVM hmin'
  have hr : (1 : ℚ) ≤ rAV (Ar L A) := by
    have h1 : qOf (Xr L A) ≤ ((rAV (Ar L A) : ℚ) : WithTop ℚ) :=
      qOf_le_iff.2 ⟨Ar L A, hoff.isA2, hquad, le_rfl⟩
    rw [hq] at h1
    exact_mod_cast h1
  obtain ⟨hsupV, hfA⟩ := lift_q hV hL hmin hLA hr
  have hα : commV (Kr L A) ⊔ fixV (Kr L A) = ⊤ := by
    rcases hP5 with h | ⟨hirr, -⟩
    · rw [hXK] at h
      exact h
    · exact absurd (hXK ▸ hirr) (not_mem_irrPlus_of_two_summands hind hsupI hreal)
  have hĀK : Ar L A ≤ Kr L A := hXK ▸ hoff.1
  have hMU : commV (Kr L A) ⊔ fixV (Ar L A) = ⊤ :=
    top_le_iff.1 (hα ▸ sup_le_sup_left (B1.fixV_le_fixV hĀK) _)
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl => hn a (hAG ha) l hl
  obtain ⟨hVU, hcommV, hAq, hcommW⟩ := lift_V hLU hAU hAn hLA hsupV hMU
  have hAL : A ≤ L := A_le_L hV hO2 hLG hAG hn hAU hAq hcommW hĀK
  have hnodd : Odd n := by
    by_contra hn'
    obtain ⟨ζ, hζ3, hζ1⟩ := exists_unit_order_three hcK (Nat.not_odd_iff_even.1 hn')
    exact hno (threeRank2_of_realizes (FFModel.nat_faithful _) (hreal 0)
      (threeRank2_statedSL_three hζ3 hζ1))
  have hds : DirectSumOfCopies (Kr L A) (commV (Kr L A)) ⊥ (FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K')) 2 := by
    refine ⟨I, π, fun _ => bot_le, fun i => ?_, by rw [bot_sup_eq, hsupI], hreal⟩
    rw [bot_sup_eq]
    have := hind i
    simpa [disjoint_iff] using this
  exact ⟨⟨n, K', hK', hf', hnodd, hcK, directSum_lift hLU hfaithL hcommV hds⟩, hAL, by
    rw [hcommV]; exact hVU⟩

end Cases

end B59

end FFC

end CFSG.Quasithin
