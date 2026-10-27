module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.ONanE68LieFacts
public import CFSG.Quasithin.Background.ONanE68LieSinger

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Join

variable {S : Type} [Group S]

theorem exists_mul_of_mem_sup_of_commute {X Y : Subgroup S}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {g : S} (hg : g ∈ X ⊔ Y) :
    ∃ x ∈ X, ∃ y ∈ Y, g = x * y := by
  have hXN : X ≤ Subgroup.normalizer (Y : Set S) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [show x * y * x⁻¹ = y by rw [h x hx y hy]; group]
      exact hy
    · intro hy
      have h1 : x⁻¹ * (x * y * x⁻¹) = (x * y * x⁻¹) * x⁻¹ := h x⁻¹ (X.inv_mem hx) _ hy
      have h2 : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = (x * y * x⁻¹) * x⁻¹ * x := by rw [h1]
          _ = x * y * x⁻¹ := by group
      rw [h2]
      exact hy
  have hg' : g ∈ (↑(X ⊔ Y) : Set S) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXN] at hg'
  obtain ⟨x, hx, y, hy, rfl⟩ := hg'
  exact ⟨x, hx, y, hy, rfl⟩

theorem omegaCenter_commute {P : Subgroup S} {a b : S} (ha : a ∈ omegaCenter P)
    (hb : b ∈ omegaCenter P) : a * b = b * a :=
  (mem_omegaCenter.1 ha).2.1 b (mem_omegaCenter.1 hb).1

end Join

section Alg

variable {S : Type} [Group S] [Finite S] {P Za Zb W : Subgroup S} {xa : S}

theorem le_of_component (hS : SingerHyp (Subgroup.normalizer (P : Set S)) Za xa)
    (h3 : 3 ≤ Nat.card Za) (hZaZ : Za ≤ omegaCenter P) (hZbZ : Zb ≤ omegaCenter P)
    (hxb : ∀ z ∈ Zb, xa * z = z * xa) (hWxa : ∀ w ∈ W, xa * w * xa⁻¹ ∈ W) {za zb : S}
    (hza : za ∈ Za) (hzb : zb ∈ Zb) (hw : za * zb ∈ W) (hne : za ≠ 1) : Za ≤ W := by
  have hxaza : xa * za * xa⁻¹ ∈ Za := hS.inv xa hS.mem za hza
  have hz' : za⁻¹ * (xa * za * xa⁻¹) ∈ Za := Za.mul_mem (Za.inv_mem hza) hxaza
  have hcomm : zb⁻¹ * (za⁻¹ * (xa * za * xa⁻¹)) = (za⁻¹ * (xa * za * xa⁻¹)) * zb⁻¹ :=
    omegaCenter_commute (hZbZ (Zb.inv_mem hzb)) (hZaZ hz')
  have hxz : xa * zb * xa⁻¹ = zb := by rw [hxb zb hzb]; group
  have hmem : za⁻¹ * (xa * za * xa⁻¹) ∈ W := by
    have h1 := W.mul_mem (W.inv_mem hw) (hWxa _ hw)
    have hx : xa * (za * zb) * xa⁻¹ = (xa * za * xa⁻¹) * zb := by
      calc xa * (za * zb) * xa⁻¹ = (xa * za * xa⁻¹) * (xa * zb * xa⁻¹) := by group
        _ = (xa * za * xa⁻¹) * zb := by rw [hxz]
    have e : (za * zb)⁻¹ * (xa * (za * zb) * xa⁻¹) =
        zb⁻¹ * (za⁻¹ * (xa * za * xa⁻¹)) * zb := by
      rw [hx]
      group
    rw [e, hcomm] at h1
    simpa using h1
  have hne' : za⁻¹ * (xa * za * xa⁻¹) ≠ 1 := by
    intro h1
    apply hne
    refine hS.eq_one_of_fixed h3 hza ?_
    calc xa * za * xa⁻¹ = za * (za⁻¹ * (xa * za * xa⁻¹)) := by group
      _ = za := by rw [h1, mul_one]
  have hinter : W ⊓ Za = Za := by
    refine hS.eq_of_invariant (W' := W ⊓ Za) inf_le_right (fun w hw => ?_) ?_
    · exact ⟨hWxa w hw.1, hS.inv xa hS.mem w hw.2⟩
    · intro h0
      have : za⁻¹ * (xa * za * xa⁻¹) ∈ W ⊓ Za := ⟨hmem, hz'⟩
      rw [h0, Subgroup.mem_bot] at this
      exact hne' this
  rw [← hinter]
  exact inf_le_left

theorem eq_cases_of_invariant {Zs Zl : Subgroup S} {xs xl : S}
    (hsS : SingerHyp (Subgroup.normalizer (P : Set S)) Zs xs)
    (hlS : SingerHyp (Subgroup.normalizer (P : Set S)) Zl xl)
    (h3s : 3 ≤ Nat.card Zs) (h3l : 3 ≤ Nat.card Zl) (hZs : Zs ≤ omegaCenter P)
    (hZl : Zl ≤ omegaCenter P) (hsup : Zs ⊔ Zl = omegaCenter P)
    (hxs : ∀ z ∈ Zl, xs * z = z * xs) (hxl : ∀ z ∈ Zs, xl * z = z * xl)
    (hWZ : W ≤ omegaCenter P) (hW0 : W ≠ ⊥) (hWs : ∀ w ∈ W, xs * w * xs⁻¹ ∈ W)
    (hWl : ∀ w ∈ W, xl * w * xl⁻¹ ∈ W) : W = Zs ∨ W = Zl ∨ W = omegaCenter P := by
  have hcomm : ∀ a ∈ Zs, ∀ b ∈ Zl, a * b = b * a := fun a ha b hb =>
    omegaCenter_commute (hZs ha) (hZl hb)
  have hdec : ∀ w ∈ omegaCenter P, ∃ a ∈ Zs, ∃ b ∈ Zl, w = a * b := fun w hw =>
    exists_mul_of_mem_sup_of_commute hcomm (hsup ▸ hw)
  have hs : ∀ w ∈ W, ∀ a ∈ Zs, ∀ b ∈ Zl, w = a * b → a ≠ 1 → Zs ≤ W := by
    intro w hw a ha b hb hwab hne
    exact le_of_component hsS h3s hZs hZl hxs hWs ha hb (hwab ▸ hw) hne
  have hl : ∀ w ∈ W, ∀ a ∈ Zs, ∀ b ∈ Zl, w = a * b → b ≠ 1 → Zl ≤ W := by
    intro w hw a ha b hb hwab hne
    have hw' : b * a ∈ W := by rw [← hcomm a ha b hb, ← hwab]; exact hw
    exact le_of_component hlS h3l hZl hZs hxl hWl hb ha hw' hne
  obtain ⟨w0, hw0, hw01⟩ : ∃ w0 ∈ W, w0 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hW0 ((Subgroup.eq_bot_iff_forall W).2 hcon)
  obtain ⟨a0, ha0, b0, hb0, hw0ab⟩ := hdec w0 (hWZ hw0)
  have hone : Zs ≤ W ∨ Zl ≤ W := by
    by_cases ha1 : a0 = 1
    · right
      have hb1 : b0 ≠ 1 := by
        intro hb1
        apply hw01
        rw [hw0ab, ha1, hb1, one_mul]
      exact hl w0 hw0 a0 ha0 b0 hb0 hw0ab hb1
    · left
      exact hs w0 hw0 a0 ha0 b0 hb0 hw0ab ha1
  rcases hone with hsW | hlW
  · by_cases hWs' : W ≤ Zs
    · exact Or.inl (le_antisymm hWs' hsW)
    · right
      right
      obtain ⟨w, hw, hwnot⟩ := IsConcreteLE.not_le_iff_exists.1 hWs'
      obtain ⟨a, ha, b, hb, hwab⟩ := hdec w (hWZ hw)
      have hb1 : b ≠ 1 := by
        intro hb1
        apply hwnot
        rw [hwab, hb1, mul_one]
        exact ha
      have hlW := hl w hw a ha b hb hwab hb1
      refine le_antisymm hWZ ?_
      rw [← hsup]
      exact sup_le hsW hlW
  · by_cases hWl' : W ≤ Zl
    · exact Or.inr (Or.inl (le_antisymm hWl' hlW))
    · right
      right
      obtain ⟨w, hw, hwnot⟩ := IsConcreteLE.not_le_iff_exists.1 hWl'
      obtain ⟨a, ha, b, hb, hwab⟩ := hdec w (hWZ hw)
      have ha1 : a ≠ 1 := by
        intro ha1
        apply hwnot
        rw [hwab, ha1, one_mul]
        exact hb
      have hsW := hs w hw a ha b hb hwab ha1
      refine le_antisymm hWZ ?_
      rw [← hsup]
      exact sup_le hsW hlW

theorem eq_one_of_fixed_both {Zs Zl : Subgroup S} {xs xl : S}
    (hsS : SingerHyp (Subgroup.normalizer (P : Set S)) Zs xs)
    (hlS : SingerHyp (Subgroup.normalizer (P : Set S)) Zl xl)
    (h3s : 3 ≤ Nat.card Zs) (h3l : 3 ≤ Nat.card Zl) (hZs : Zs ≤ omegaCenter P)
    (hZl : Zl ≤ omegaCenter P) (hsup : Zs ⊔ Zl = omegaCenter P)
    (hxs : ∀ z ∈ Zl, xs * z = z * xs) (hxl : ∀ z ∈ Zs, xl * z = z * xl) {w : S}
    (hw : w ∈ omegaCenter P) (hfs : xs * w * xs⁻¹ = w) (hfl : xl * w * xl⁻¹ = w) : w = 1 := by
  have hcomm : ∀ a ∈ Zs, ∀ b ∈ Zl, a * b = b * a := fun a ha b hb =>
    omegaCenter_commute (hZs ha) (hZl hb)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm (hsup ▸ hw)
  have hxsb : xs * b * xs⁻¹ = b := by rw [hxs b hb]; group
  have hxla : xl * a * xl⁻¹ = a := by rw [hxl a ha]; group
  have h1 : xs * a * xs⁻¹ = a := by
    have : (xs * a * xs⁻¹) * b = a * b := by
      calc (xs * a * xs⁻¹) * b = (xs * a * xs⁻¹) * (xs * b * xs⁻¹) := by rw [hxsb]
        _ = xs * (a * b) * xs⁻¹ := by group
        _ = a * b := hfs
    exact mul_right_cancel this
  have h2 : xl * b * xl⁻¹ = b := by
    have : a * (xl * b * xl⁻¹) = a * b := by
      calc a * (xl * b * xl⁻¹) = (xl * a * xl⁻¹) * (xl * b * xl⁻¹) := by rw [hxla]
        _ = xl * (a * b) * xl⁻¹ := by group
        _ = a * b := hfl
    exact mul_left_cancel this
  rw [hsS.eq_one_of_fixed h3s ha h1, hlS.eq_one_of_fixed h3l hb h2, one_mul]

end Alg

end E68Proof

end E6

end CFSG.Quasithin
