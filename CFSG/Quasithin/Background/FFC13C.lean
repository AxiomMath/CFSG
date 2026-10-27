module

public import CFSG.Quasithin.Background.FFC12B

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem section_nonstrong (hV : ∀ v : V, v ^ 2 = 1) {X T M A L : Subgroup (MulAut V)}
    (hH : CompHyp X T M A L) {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    (hq : qOf (wtLA A L W) = ((1 : ℚ) : WithTop ℚ)) :
    Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L))) ≤
      Nat.card (Sec W (W ⊓ fixV L)) := by
  obtain ⟨-, -, -, -, -, hA, hL, hLA⟩ := hH
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hAW := a_stab_irr hV hA hLq hLA hW
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  have hnA : commSub W A ≠ ⊥ := commSub_ne_bot_of_irr hLA hW
  have hbot : autSec A W (W ⊓ fixV L) ≠ ⊥ := by
    intro hb
    apply hnA
    have hAWs : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
    have hAZs : A ≤ stabSub (W ⊓ fixV L) :=
      B1.le_stabSub_of_invariant (isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn))
    rw [commSub_eq_bot_iff]
    intro w hw a ha
    have hmem : B5.secHom A hAWs hAZs ⟨a, ha⟩ ∈ autSec A W (W ⊓ fixV L) := by
      rw [← B5.range_secHom A hAWs hAZs]
      exact ⟨⟨a, ha⟩, rfl⟩
    rw [hb] at hmem
    have h1 : B5.secHom A hAWs hAZs ⟨a, ha⟩ = 1 := Subgroup.mem_bot.1 hmem
    exact sec_triv_imp_triv hLq hAn hW hAW ha
      (fun w' hw' => (((B5.mem_ker_secHom A hAWs hAZs ⟨a, ha⟩).1 (MonoidHom.mem_ker.2 h1)).2 w'
        hw').2) w hw
  have hA2 : IsA2 (wtLA A L W) (autSec A W (W ⊓ fixV L)) :=
    ⟨autSec_mono le_sup_right W _, hbot, isElemAbelian2_autSec W _ hA.1.2.2.1⟩
  by_contra hlt
  push Not at hlt
  have hr : rAV (autSec A W (W ⊓ fixV L)) < 1 := (rAV_lt_one_iff hS2 hA2).2 hlt
  exact not_isStrongFFModule_of_one_le_qOf hS2 (hq ▸ le_rfl)
    ((isStrongFFModule_iff hS2).2 ⟨_, hA2, hr⟩)

theorem conj_fixes_W (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsComponentOf L X) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hcV : commV L = W) (hAcQ : A ≤ centQuot W)
    {x : MulAut V} (hx : x ∈ X) (hxL : B6.conjSub x L ≠ L) :
    (∀ l ∈ L, ∀ w ∈ W, l (x w) = x w) ∧ (∀ a ∈ A, ∀ w ∈ W, a (x w) = x w) := by
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.1.2.2.1.2
  have hWc : commV L ∈ IrrPlus L (⊤ : Subgroup V) := hcV ▸ hW
  have hL₂ : CFSG.Open.IsComponentOf (B6.conjSub x L) X := B113.isComponentOf_conj hL hx
  have hxinv : x⁻¹ ∈ X := X.inv_mem hx
  have hL₃ : CFSG.Open.IsComponentOf (B6.conjSub x⁻¹ L) X := B113.isComponentOf_conj hL hxinv
  have hne₃ : L ≠ B6.conjSub x⁻¹ L := by
    intro h
    apply hxL
    calc B6.conjSub x L = B6.conjSub x (B6.conjSub x⁻¹ L) := by rw [← h]
      _ = L := by rw [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one]
  have hne₂ : L ≠ B6.conjSub x L := fun h => hxL h.symm
  have hAc : ∀ k ∈ B6.conjSub x L, ∀ b ∈ A, k * b = b * k :=
    mul_comm_of_commutator_eq_bot (commutator_eq_bot_of_natural hV hA hL hW hcV hAcQ hL₂ hne₂)
  have hcomm₃ : ∀ k ∈ B6.conjSub x⁻¹ L, ∀ l' ∈ L, k * l' = l' * k :=
    components_mul_comm_of_ne hL hL₃ hne₃
  constructor
  · intro l hl w hw
    have hmem : x⁻¹ * l * x ∈ B6.conjSub x⁻¹ L := by
      rw [B6.mem_conjSub]
      have : (x⁻¹)⁻¹ * (x⁻¹ * l * x) * x⁻¹ = l := by group
      rw [this]
      exact hl
    have h1 := comm_trivial_on_commV hV hL₃.2.2 (L := L) hcomm₃ hWc (x⁻¹ * l * x) hmem w
      (by rw [hcV]; exact hw)
    have hmul : l * x = x * (x⁻¹ * l * x) := by group
    calc l (x w) = (l * x) w := rfl
      _ = (x * (x⁻¹ * l * x)) w := by rw [hmul]
      _ = x ((x⁻¹ * l * x) w) := rfl
      _ = x w := by rw [h1]
  · intro a ha w hw
    have hg2L : ∀ l' ∈ L, (x⁻¹ * a * x) * l' = l' * (x⁻¹ * a * x) := by
      intro l' hl'
      have hmem : x * l' * x⁻¹ ∈ B6.conjSub x L := by
        rw [B6.mem_conjSub]
        have : x⁻¹ * (x * l' * x⁻¹) * x = l' := by group
        rw [this]
        exact hl'
      have hc := hAc _ hmem a ha
      calc (x⁻¹ * a * x) * l' = x⁻¹ * (a * (x * l' * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * l' * x⁻¹) * a) * x := by rw [hc]
        _ = l' * (x⁻¹ * a * x) := by group
    have hg2W : ∀ w ∈ W, (x⁻¹ * a * x) w ∈ W := by
      intro w hw
      rw [← hcV] at hw ⊢
      exact commV_invariant_of_commute hg2L w hw
    have hg2sq : ∀ w ∈ W, (x⁻¹ * a * x) ((x⁻¹ * a * x) w) = w := by
      intro w _
      have h2 : a * a = 1 := by rw [← pow_two]; exact hA2 a ha
      have h3 : (x⁻¹ * a * x) * (x⁻¹ * a * x) = 1 := by
        calc (x⁻¹ * a * x) * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
          _ = 1 := by rw [h2]; group
      have := congrArg (fun g : MulAut V => g w) h3
      simpa using this
    have h₂ : ∀ w ∈ W, (x⁻¹ * a * x) w = w := trivial_of_sq_one_commute hV hW hg2L hg2W hg2sq
    have hmul : a * x = x * (x⁻¹ * a * x) := by group
    calc a (x w) = (a * x) w := rfl
      _ = (x * (x⁻¹ * a * x)) w := by rw [hmul]
      _ = x ((x⁻¹ * a * x) w) := rfl
      _ = x w := by rw [h₂ w hw]

theorem eq_one_of_trivial_on_W (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) (hA : IsFFStarMin X A) (hL : CFSG.Open.IsComponentOf L X)
    (hLA : ⁅L, A⁆ = L) {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    (hsup : W ⊔ fixV A = ⊤) {g : MulAut V} (hg : g ∈ L ⊔ A) (hgW : ∀ w ∈ W, g w = w) : g = 1 := by
  obtain ⟨hcV, hAcQ, hLcQ⟩ := commV_eq_of_sup hV hA hL.2.2 hLA hW hsup
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAX : A ≤ X := hA.1.1
  have hLX : L ≤ X := hL.1
  obtain ⟨l, hl, a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hg
  set U : Subgroup V := Subgroup.closure {v | ∃ x ∈ X, ∃ w ∈ W, v = x w} with hUdef
  have hWU : W ≤ U := fun w hw => Subgroup.subset_closure ⟨1, X.one_mem, w, hw, by simp⟩
  have hUinv : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U := by
    intro g hg u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, w, hw, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨g * y, X.mul_mem hg hy, w, hw, by simp [MulAut.mul_apply]⟩
    | one => simp
    | mul x y _ _ ihx ihy => simpa using U.mul_mem ihx ihy
    | inv x _ ih => simpa using U.inv_mem ih
  have hdx : ∀ x ∈ X, ∀ w ∈ W, (l * a) (x w) = x w := by
    intro x hx w hw
    by_cases hxL : B6.conjSub x L = L
    · have hxW : x w ∈ W := by
        have h1 := map_mem_commV_conj (H := L) x w (by rw [hcV]; exact hw)
        rw [hxL, hcV] at h1
        exact h1
      exact hgW _ hxW
    · obtain ⟨h1, h2⟩ := conj_fixes_W hV hA hL hW hcV hAcQ hx hxL
      calc (l * a) (x w) = l (a (x w)) := rfl
        _ = l (x w) := by rw [h2 a ha w hw]
        _ = x w := h1 l hl w hw
  refine eq_one_of_stab hV hO2 hUinv (X.mul_mem (hLX hl) (hAX ha)) ?_ ?_
  · intro u hu
    induction hu using Subgroup.closure_induction with
    | mem v hv =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hv
      exact hdx x hx w hw
    | one => simp
    | mul x y _ _ ihx ihy => simp [map_mul, ihx, ihy]
    | inv x _ ih => simp [map_inv, ih]
  · intro v
    have h1 : (l * a) v * v⁻¹ = (l (a v) * (a v)⁻¹) * (a v * v⁻¹) := by
      change l (a v) * v⁻¹ = _
      simp [mul_comm, mul_left_comm]
    rw [h1]
    exact U.mul_mem (hWU (hLcQ hl (a v))) (hWU (hAcQ ha v))

omit [Finite V] in
theorem fixV_eq_sup_of_sup {E A : Subgroup (MulAut V)} (hEA : E ≤ A) {W : Subgroup V}
    (hsup : W ⊔ fixV A = ⊤) : fixV E = (W ⊓ fixV E) ⊔ fixV A := by
  apply le_antisymm
  · intro v hv
    have hv' : v ∈ W ⊔ fixV A := by rw [hsup]; trivial
    obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv'
    have hwE : w ∈ fixV E := by
      intro e he
      have h1 := hv e he
      rw [map_mul, hc e (hEA he)] at h1
      exact mul_right_cancel h1
    exact Subgroup.mul_mem_sup ⟨hw, hwE⟩ hc
  · exact sup_le inf_le_right (B1.fixV_le_fixV hEA)

omit [Finite V] in
theorem card_fixV_mul_of_sup {E A : Subgroup (MulAut V)} (hEA : E ≤ A) {W : Subgroup V}
    (hsup : W ⊔ fixV A = ⊤) :
    Nat.card (fixV E) * Nat.card ↥(W ⊓ fixV A) = Nat.card ↥(W ⊓ fixV E) * Nat.card (fixV A) := by
  have h1 := card_sup_mul_card_inf (W ⊓ fixV E) (fixV A)
  rw [← fixV_eq_sup_of_sup hEA hsup] at h1
  have h2 : (W ⊓ fixV E) ⊓ fixV A = W ⊓ fixV A := by
    rw [inf_assoc, inf_eq_right.2 (B1.fixV_le_fixV hEA)]
  rw [h2] at h1
  exact h1

theorem card_fixV_autSec_bot {E : Subgroup (MulAut V)} {W : Subgroup V} (hEW : E ≤ stabSub W)
    (hEU : E ≤ stabSub (⊥ : Subgroup V)) :
    Nat.card (fixV (autSec E W ⊥)) = Nat.card ↥(W ⊓ fixV E) := by
  apply le_antisymm
  · classical
    let f : ↥(fixV (autSec E W ⊥)) → ↥(W ⊓ fixV E) := fun s =>
      ⟨((QuotientGroup.mk_surjective (s : Sec W ⊥)).choose : V), (QuotientGroup.mk_surjective
        (s : Sec W ⊥)).choose.2, fun g hg => by
        set w := (QuotientGroup.mk_surjective (s : Sec W ⊥)).choose with hw
        have hs : (QuotientGroup.mk w : Sec W ⊥) = (s : Sec W ⊥) :=
          (QuotientGroup.mk_surjective (s : Sec W ⊥)).choose_spec
        have hφ : B5.secHom E hEW hEU ⟨g, hg⟩ ∈ autSec E W ⊥ := by
          rw [← B5.range_secHom E hEW hEU]
          exact ⟨⟨g, hg⟩, rfl⟩
        have h1 := (mem_fixV.1 s.2) _ hφ
        rw [← hs, B5.secHom_mk] at h1
        have h2 := QuotientGroup.eq.1 h1
        rw [Subgroup.mem_subgroupOf] at h2
        have h3 : ((g : MulAut V) (w : V))⁻¹ * (w : V) = 1 := by
          have := h2
          simpa using this
        exact inv_mul_eq_one.1 h3⟩
    refine Nat.card_le_card_of_injective f ?_
    intro s t hst
    have hs : (QuotientGroup.mk (QuotientGroup.mk_surjective (s : Sec W ⊥)).choose : Sec W ⊥) =
        (s : Sec W ⊥) := (QuotientGroup.mk_surjective (s : Sec W ⊥)).choose_spec
    have ht : (QuotientGroup.mk (QuotientGroup.mk_surjective (t : Sec W ⊥)).choose : Sec W ⊥) =
        (t : Sec W ⊥) := (QuotientGroup.mk_surjective (t : Sec W ⊥)).choose_spec
    have hst' : (((QuotientGroup.mk_surjective (s : Sec W ⊥)).choose : ↥W) : V) =
        (((QuotientGroup.mk_surjective (t : Sec W ⊥)).choose : ↥W) : V) :=
      congrArg (fun z : ↥(W ⊓ fixV E) => (z : V)) hst
    have hw : (QuotientGroup.mk_surjective (s : Sec W ⊥)).choose =
        (QuotientGroup.mk_surjective (t : Sec W ⊥)).choose := Subtype.ext hst'
    apply Subtype.ext
    rw [← hs, ← ht, hw]
  · have := card_inf_fixV_le_autSec (A := E) (bot_le : (⊥ : Subgroup V) ≤ W) hEW
    simpa using this

omit [Finite V] in
theorem card_autSec_bot_eq {E A : Subgroup (MulAut V)} (hEA : E ≤ A) {W : Subgroup V}
    (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub (⊥ : Subgroup V)) (hfaith : A ⊓ centSub W = ⊥) :
    Nat.card (autSec E W ⊥) = Nat.card E := by
  have h := card_autSec_mul (hEA.trans hAW) (hEA.trans hAU)
  have hb : E ⊓ centSec W ⊥ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgE, hgc⟩
    have hg : g ∈ A ⊓ centSub W := ⟨hEA hgE, fun w hw => by
      have := hgc.2 w hw
      rw [Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this⟩
    rw [hfaith] at hg
    exact hg
  rw [hb, Subgroup.card_bot, mul_one] at h
  exact h

theorem kf {E A : Subgroup (MulAut V)} (hEA : E ≤ A) {W : Subgroup V} (hsup : W ⊔ fixV A = ⊤)
    (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub (⊥ : Subgroup V)) (hfaith : A ⊓ centSub W = ⊥) :
    Nat.card E * Nat.card (fixV E) * Nat.card ↥(W ⊓ fixV A) =
      Nat.card (autSec E W ⊥) * Nat.card (fixV (autSec E W ⊥)) * Nat.card (fixV A) := by
  rw [card_autSec_bot_eq hEA hAW hAU hfaith, card_fixV_autSec_bot (hEA.trans hAW) (hEA.trans hAU),
    mul_assoc, card_fixV_mul_of_sup hEA hsup]
  ring

theorem lift_offender {X A : Subgroup (MulAut V)} (hA : IsFFStarMin X A) {W U : Subgroup V}
    (hU : U = ⊥) (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub U) (hsup : W ⊔ fixV A = ⊤)
    (hfaith : A ⊓ centSub W = ⊥) {B₀ : Subgroup (MulAut (Sec W U))}
    (hB₀ : IsFFStarOffender (autSec A W U) B₀)
    (hprod : Nat.card B₀ * Nat.card (fixV B₀) =
      Nat.card (autSec A W U) * Nat.card (fixV (autSec A W U))) :
    B₀ = autSec A W U := by
  subst hU
  set σ := B5.secHom A hAW hAU with hσ
  have hB₀A : B₀ ≤ autSec A W ⊥ := hB₀.1
  set A₀ : Subgroup (MulAut V) := (B₀.comap σ).map A.subtype with hA₀
  have hA₀A : A₀ ≤ A := by
    rintro _ ⟨a, _, rfl⟩
    exact a.2
  have hA₀B : autSec A₀ W ⊥ = B₀ := by
    have hsub : A₀.subgroupOf A = B₀.comap σ :=
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
    rw [← B5.map_secHom_eq_autSec A hAW hAU hA₀A, hsub, Subgroup.map_comap_eq]
    exact inf_eq_right.2 (hB₀A.trans (B5.range_secHom A hAW hAU).ge)
  have hcardA₀ : Nat.card B₀ = Nat.card A₀ := by
    rw [← hA₀B]
    exact card_autSec_bot_eq hA₀A hAW hAU hfaith
  have hA₀bot : A₀ ≠ ⊥ := by
    intro hb
    apply hB₀.2.1
    apply Subgroup.eq_bot_of_card_eq
    rw [hcardA₀, hb, Subgroup.card_bot]
  have hA₀el : IsElemAbelian2 A₀ :=
    ⟨fun a ha b hb => hA.1.2.2.1.1 a (hA₀A ha) b (hA₀A hb), fun a ha => hA.1.2.2.1.2 a (hA₀A ha)⟩
  have hkA₀ := kf hA₀A hsup hAW hAU hfaith
  rw [hA₀B] at hkA₀
  have hkA := kf (le_refl A) hsup hAW hAU hfaith
  have hpos : 0 < Nat.card ↥(W ⊓ fixV A) := Nat.card_pos
  have hoff : IsFFStarOffender X A₀ := by
    refine ⟨hA₀A.trans hA.1.1, hA₀bot, hA₀el, fun B'' hB'' => ?_⟩
    have hk1 := kf (hB''.trans hA₀A) hsup hAW hAU hfaith
    have hle : Nat.card (autSec B'' W ⊥) * Nat.card (fixV (autSec B'' W ⊥)) ≤
        Nat.card B₀ * Nat.card (fixV B₀) :=
      hB₀.card_le (hA₀B ▸ autSec_mono hB'' W ⊥)
    have h1 : Nat.card B'' * Nat.card (fixV B'') * Nat.card ↥(W ⊓ fixV A) ≤
        Nat.card A₀ * Nat.card (fixV A₀) * Nat.card ↥(W ⊓ fixV A) := by
      rw [hk1, hkA₀]
      exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hFFLe : FFLe X A₀ A := by
    refine ⟨hoff.isA2, hA.1.isA2, hA₀A, ?_⟩
    have h1 : Nat.card A₀ * Nat.card (fixV A₀) * Nat.card ↥(W ⊓ fixV A) =
        Nat.card A * Nat.card (fixV A) * Nat.card ↥(W ⊓ fixV A) := by
      rw [hkA₀, hkA, hprod]
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hEq : A₀ = A := hA.2 A₀ hoff hFFLe
  rw [← hA₀B, hEq]

end Main

local instance coreMemDec5 : DecidablePred (· ∈ G6.coreMod 5) := fun _ =>
  decidable_of_iff _ G6.mem_coreMod.symm

theorem card_coreMod_five : Nat.card ↥(G6.coreMod 5) = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_fix_swap_coreMod (i j : Fin 5) (hij : i ≠ j) :
    Nat.card {x : ↥(G6.coreMod 5) // G6.coreAct 5 (Equiv.swap i j) x = x} = 8 := by
  rw [Nat.card_eq_fintype_card]
  revert i j
  decide

section Swap

variable {S : Type} [CommGroup S]

theorem card_fixV_swap (e : S ≃* ↥(G6.coreMod 5)) (ψ : Equiv.Perm (Fin 5) →* MulAut S)
    (hψ : ∀ (σ : Equiv.Perm (Fin 5)) (s : S), e (ψ σ s) = G6.coreAct 5 σ (e s))
    {t : Equiv.Perm (Fin 5)} (ht : t.IsSwap) :
    Nat.card (fixV ((Subgroup.zpowers t).map ψ)) = 8 := by
  obtain ⟨i, j, hij, rfl⟩ := ht
  have hmem : ∀ s : S, s ∈ fixV ((Subgroup.zpowers (Equiv.swap i j)).map ψ) ↔
      G6.coreAct 5 (Equiv.swap i j) (e s) = e s := by
    intro s
    constructor
    · intro hs
      have h1 : ψ (Equiv.swap i j) s = s :=
        hs _ (Subgroup.mem_map.2 ⟨_, Subgroup.mem_zpowers _, rfl⟩)
      rw [← hψ, h1]
    · intro hs
      have h1 : ψ (Equiv.swap i j) s = s := e.injective (by rw [hψ]; exact hs)
      have h2 : Subgroup.zpowers (ψ (Equiv.swap i j)) ≤
          MulAction.stabilizer (MulAut S) s := by
        rw [Subgroup.zpowers_le]
        exact h1
      intro b hb
      rw [MonoidHom.map_zpowers] at hb
      exact h2 hb
  have := Nat.card_congr (e.toEquiv.subtypeEquiv (p := fun s : S => s ∈ fixV ((Subgroup.zpowers
    (Equiv.swap i j)).map ψ)) (q := fun x : ↥(G6.coreMod 5) =>
      G6.coreAct 5 (Equiv.swap i j) x = x) hmem)
  rw [show Nat.card (fixV ((Subgroup.zpowers (Equiv.swap i j)).map ψ)) =
      Nat.card {s : S // s ∈ fixV ((Subgroup.zpowers (Equiv.swap i j)).map ψ)} from rfl, this]
  exact card_fix_swap_coreMod i j hij

end Swap

section Single

variable {V : Type} [CommGroup V] [Finite V]

theorem single_swap {X A : Subgroup (MulAut V)} (hA : IsFFStarMin X A) {W U : Subgroup V} (hU : U = ⊥)
    (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub U) (hsup : W ⊔ fixV A = ⊤)
    (hfaith : A ⊓ centSub W = ⊥) (e : Sec W U ≃* ↥(G6.coreMod 5))
    (ψ : Equiv.Perm (Fin 5) →* MulAut (Sec W U)) (hψi : Function.Injective ψ)
    (hψ : ∀ (σ : Equiv.Perm (Fin 5)) (s : Sec W U), e (ψ σ s) = G6.coreAct 5 σ (e s))
    {B : Subgroup (MulAut (Sec W U))} (hB : IsFFStarOffender (autSec A W U) B)
    (hBeq : B = autSec A W U)
    (hAprod : Nat.card (autSec A W U) * Nat.card (fixV (autSec A W U)) = Nat.card (Sec W U))
    (T' : Set (Equiv.Perm (Fin 5))) (hT'sw : ∀ t ∈ T', t.IsSwap)
    (hBT : B = (Subgroup.closure T').map ψ) :
    ∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧ autSec A W U = (Subgroup.zpowers t).map ψ := by
  have hS16 : Nat.card (Sec W U) = 16 := by
    rw [Nat.card_congr e.toEquiv, card_coreMod_five]
  obtain ⟨t, htT'⟩ : T'.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hB.2.1
    rw [hBT, hne, Subgroup.closure_empty, Subgroup.map_bot]
  have ht : t.IsSwap := hT'sw t htT'
  set B₁ : Subgroup (MulAut (Sec W U)) := (Subgroup.zpowers t).map ψ with hB₁
  have hB₁B : B₁ ≤ B := by
    rw [hBT]
    exact Subgroup.map_mono (Subgroup.zpowers_le.2 (Subgroup.subset_closure htT'))
  have hcard1 : Nat.card B₁ = 2 := by
    rw [hB₁, Subgroup.card_map_of_injective hψi, Nat.card_zpowers, ht.orderOf]
  have hfix1 : Nat.card (fixV B₁) = 8 := card_fixV_swap e ψ hψ ht
  have hprod1 : Nat.card B₁ * Nat.card (fixV B₁) = 16 := by rw [hcard1, hfix1]
  have hne1 : B₁ ≠ ⊥ := by
    intro hb
    have hψt : ψ t ∈ B₁ := Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers t)
    rw [hb, Subgroup.mem_bot] at hψt
    have : t = 1 := hψi (by rw [hψt, map_one])
    have h2 := ht.orderOf
    rw [this, orderOf_one] at h2
    omega
  have hoff : IsFFStarOffender (autSec A W U) B₁ := by
    refine ⟨hB₁B.trans hB.1, hne1, ⟨fun a ha b hb => hB.2.2.1.1 a (hB₁B ha) b (hB₁B hb),
      fun a ha => hB.2.2.1.2 a (hB₁B ha)⟩, fun B'' hB'' => ?_⟩
    have h1 := hB.card_le (hB''.trans hB₁B)
    rw [hBeq, hAprod, hS16] at h1
    rw [hprod1]
    exact h1
  have hprod : Nat.card B₁ * Nat.card (fixV B₁) =
      Nat.card (autSec A W U) * Nat.card (fixV (autSec A W U)) := by
    rw [hprod1, hAprod, hS16]
  exact ⟨t, ht, (lift_offender hA hU hAW hAU hsup hfaith hoff hprod).symm⟩

end Single

end B69

end CFSG.Quasithin
