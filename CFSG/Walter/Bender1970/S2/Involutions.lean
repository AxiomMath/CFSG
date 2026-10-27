module

public import CFSG.Walter.Bender1970.S2.Basic
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Walter.JRFacts
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

theorem isConj_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ x y : B, orderOf x = 2 → orderOf y = 2 → IsConj x y) {x y : A} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (h (e x) (e y) (by rwa [MulEquiv.orderOf_eq]) (by rwa [MulEquiv.orderOf_eq]))
  refine isConj_iff.mpr ⟨e.symm c, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]

theorem IsTypeL2.isConj_of_orderOf_eq_two {L : Type*} [Group L] (hL : IsTypeL2 L) {x y : L}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  rcases hL with ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf, -, -, ⟨e⟩⟩
  · exact isConj_of_mulEquiv e (fun _ _ ha hb => psl2_even_isConj_of_orderOf_eq_two hf ha hb) hx hy
  · exact isConj_of_mulEquiv e (fun _ _ ha hb => psl2_odd_isConj_of_orderOf_eq_two hpodd hf ha hb)
      hx hy

theorem isConj_of_isTypeL2_or_isTypeJR {L : Type} [Group L] [Finite L]
    (hL : IsTypeL2 L ∨ IsTypeJR L) {x y : L} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  rcases hL with hL | hL
  · exact hL.isConj_of_orderOf_eq_two hx hy
  · exact hL.isConj_of_orderOf_eq_two hx hy

theorem isComponentOf_top_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (h : ∃ a b : Q, a * b ≠ b * a) : IsComponentOf (⊤ : Subgroup Q) ⊤ :=
  (isComponent_iff_isComponentOf_top ⊤).mp
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h).1, Subgroup.IsSubnormal.top⟩

theorem pPrimeCore_eq_bot_of_isSimpleGroup {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h : ∃ a b : X, a * b ≠ b * a) : pPrimeCore 2 X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 X) with hO | hO
  · exact hO
  · exfalso
    have hcop := pPrimeCore_coprime_card (p := 2) (G := X)
    rw [hO, Subgroup.card_top] at hcop
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp hcop)) (even_card_of_isSimpleGroup h)

theorem IsAStar.isTypeL2_or_isTypeJR_of_isSimpleGroup {X : Type} [Group X] [Finite X]
    (hX : IsAStar X) [IsSimpleGroup X] (h : ∃ a b : X, a * b ≠ b * a) :
    IsTypeL2 X ∨ IsTypeJR X := by
  set Q := X ⧸ pPrimeCore 2 X
  let e : X ≃* Q := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_bot_of_isSimpleGroup h).symm)
  have : IsSimpleGroup Q := e.symm.isSimpleGroup
  have hQ : ∃ a b : Q, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := h
    exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩
  obtain ⟨-, htype⟩ := hX.2.2 ⊤ (isComponentOf_top_of_isSimpleGroup hQ)
  let e' : X ≃* (⊤ : Subgroup Q) := e.trans Subgroup.topEquiv.symm
  rcases htype with h2 | h2
  · exact Or.inl (h2.of_mulEquiv e'.symm)
  · exact Or.inr (h2.of_mulEquiv e'.symm)

theorem bender1970_2_2 {X : Type} [Group X] [Finite X] (hX : IsAStar X) [IsSimpleGroup X]
    {x y : X} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  by_cases hab : ∃ a b : X, a * b ≠ b * a
  · exact isConj_of_isTypeL2_or_isTypeJR (hX.isTypeL2_or_isTypeJR_of_isSimpleGroup hab) hx hy
  ·
    push Not at hab
    have hxN : (Subgroup.zpowers x).Normal :=
      ⟨fun n hn g => by rw [hab g n, mul_inv_cancel_right]; exact hn⟩
    have hx1 : x ≠ 1 := by rintro rfl; simp at hx
    have hy1 : y ≠ 1 := by rintro rfl; simp at hy
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h | h
    · exact absurd (Subgroup.zpowers_eq_bot.mp h) hx1
    · rcases eq_one_or_eq_of_mem_zpowers hx (h ▸ Subgroup.mem_top y) with h1 | h1
      · exact absurd h1 hy1
      · rw [h1]

theorem bender1970_2_2_subgroup {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsAStar H) [IsSimpleGroup H] {x y : G} (hxH : x ∈ H) (hyH : y ∈ H)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : ∃ h ∈ H, h * x * h⁻¹ = y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (bender1970_2_2 hH (x := ⟨x, hxH⟩) (y := ⟨y, hyH⟩)
    (by rwa [Subgroup.orderOf_mk]) (by rwa [Subgroup.orderOf_mk]))
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem IsAStar.isConj_of_isComponentOf {X : Type} [Group X] [Finite X] (hX : IsAStar X)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) {x y : K ⧸ Subgroup.center K}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  isConj_of_isTypeL2_or_isTypeJR (hX.isTypeL2_or_isTypeJR hK) hx hy

end CFSG.Walter
