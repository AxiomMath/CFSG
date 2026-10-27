module

public import CFSG.Quasithin.Background.FFC6N
public import CFSG.Quasithin.Background.FFC6F
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.B1Red
open scoped commutatorElement

namespace B59

section CaseIV

variable {V : Type} [CommGroup V] [Finite V]

theorem pCore_commute (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L G) (hA : IsFFStarOffender G A) (hLA : ⁅L, A⁆ = L) :
    ∀ q ∈ pCoreOf 2 (L ⊔ A), ∀ l ∈ L, q * l = l * q := by
  obtain ⟨hH₀n, -, -, -, -, -⟩ := red_basic hV hL hA hLA
  have hLo : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLperf : Group.IsPerfect ↥L := ⟨hLo.1⟩
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLo
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ A)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ A)
  have hQH : pCoreOf 2 (L ⊔ A) ≤ L ⊔ A := CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ A)
  refine commute_of_normal_not_le hLo (fun q hq l hl => hH₀n q (hQH hq) l hl)
    (fun l hl q hq => conj_mem_pCoreOf (Subgroup.mem_sup_left hl) hq) ?_
  intro hle
  exact Group.IsPerfect.not_isNilpotent ↥L (hQ2.to_le hle).isNilpotent

omit [Finite V] in
theorem exists_eq_on_of_le {L A : Subgroup (MulAut V)} {W : Subgroup V} (hAU : A ≤ stabSub W)
    (hĀK : autSub A W ≤ autSub L W) {a : MulAut V} (ha : a ∈ A) :
    ∃ l ∈ L, ∀ w ∈ W, a w = l w := by
  have hmem : (resHom W) ⟨a, hAU ha⟩ ∈ autSub L W :=
    hĀK (mem_autSub.2 ⟨⟨a, hAU ha⟩, ha, rfl⟩)
  obtain ⟨g, hgL, hg⟩ := mem_autSub.1 hmem
  refine ⟨g.1, hgL, fun w hw => ?_⟩
  have := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : V)) hg
  exact this.symm

theorem inner_aut (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L G) (hA : IsFFStarOffender G A) (hLA : ⁅L, A⁆ = L)
    (hĀK : Ar L A ≤ Kr L A) : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹ := by
  obtain ⟨-, -, hker, hst, -, -⟩ := red_basic hV hL hA hLA
  have hAU : A ≤ stabSub (W0 L A) := le_sup_right.trans hst
  intro a ha
  obtain ⟨l, hl, hal⟩ := exists_eq_on_of_le hAU hĀK ha
  refine ⟨l, hl, fun x hx => ?_⟩
  have hcQ : l⁻¹ * a ∈ pCoreOf 2 (L ⊔ A) := by
    rw [← hker]
    refine ⟨(L ⊔ A).mul_mem ((L ⊔ A).inv_mem (Subgroup.mem_sup_left hl)) (Subgroup.mem_sup_right ha),
      fun w hw => ?_⟩
    show l⁻¹ (a w) = w
    rw [hal w hw]
    simp
  have hcomm := pCore_commute hV hL hA hLA _ hcQ x hx
  have hcx : l⁻¹ * a * x * (l⁻¹ * a)⁻¹ = x := by rw [hcomm, mul_inv_cancel_right]
  have ha' : a = l * (l⁻¹ * a) := by group
  calc a * x * a⁻¹ = l * ((l⁻¹ * a) * x * (l⁻¹ * a)⁻¹) * l⁻¹ := by
        conv_lhs => rw [ha']
        group
    _ = l * x * l⁻¹ := by rw [hcx]

omit [Finite V] in
theorem binaryNaturalSL_map_bot {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W)
    (hf : ∀ g ∈ L, (∀ v ∈ W, g v = v) → g = 1) {d n : ℕ}
    (h : BinaryNaturalSL (autSub L W) (commV (autSub L W)) ⊥ d n) :
    BinaryNaturalSL L (commSub W L) ⊥ d n := by
  obtain ⟨K, hK, hfin, hc, hr⟩ := h
  refine ⟨K, hK, hfin, hc, ?_⟩
  have := realizes_map hst hf hr
  rwa [map_commV_aut hst, Subgroup.map_bot] at this

theorem caseIV (hLast : B59Last) {G A L : Subgroup (MulAut V)} (hc : B56Counterex G)
    (hV : ∀ v : V, v ^ 2 = 1) (hO2 : pCoreOf 2 G = ⊥) (hmin : IsFFStarMin G A)
    (hL : CFSG.Open.IsComponentOf L G) (hLA : ⁅L, A⁆ = L) (hXK : Xr L A = Kr L A)
    (hC : fixV (Kr L A) ⊓ commV (Kr L A) = ⊥)
    (hnat : ∃ m, Odd m ∧
      BinaryNaturalSL (Kr L A) (commV (Kr L A)) (fixV (Kr L A) ⊓ commV (Kr L A)) 3 m) :
    B59Case4 A L := by
  obtain ⟨-, -, -, hst, -, -⟩ := red_basic hV hL hmin.1 hLA
  have hLU : L ≤ stabSub (W0 L A) := le_sup_left.trans hst
  have hfaithL := faithL hV hO2 hL hmin hLA
  obtain ⟨-, -, -, -, -, -, hoff, -, -⟩ := red_aut hV hL hmin.1 hLA
  have hĀK : Ar L A ≤ Kr L A := hXK ▸ hoff.1
  have hinner := inner_aut hV hL hmin.1 hLA hĀK
  obtain ⟨m, hm, hn⟩ := hnat
  rw [hC] at hn
  have hnatU : ∃ m, Odd m ∧ BinaryNaturalSL L (commSub (fixV (pCoreOf 2 (L ⊔ A))) L) ⊥ 3 m :=
    ⟨m, hm, binaryNaturalSL_map_bot hLU hfaithL hn⟩
  have hAU : A ≤ stabSub (W0 L A) := le_sup_right.trans hst
  have hLast' : commV L = commSub (fixV (pCoreOf 2 (L ⊔ A))) L :=
    hLast V G hc A L hmin hL hLA hnatU fun a ha => by
      obtain ⟨l, hl, hal⟩ := exists_eq_on_of_le hAU hĀK ha
      exact ⟨l, hl, fun u hu => hal u (commSub_le_of_invariant (fun x hx w hw => (hLU hx w).2 hw) hu)⟩
  refine ⟨?_, hinner⟩
  obtain ⟨m', hm', hn'⟩ := hnatU
  exact ⟨m', hm', by rw [hLast']; exact hn'⟩

end CaseIV

end B59

end FFC

end CFSG.Quasithin
