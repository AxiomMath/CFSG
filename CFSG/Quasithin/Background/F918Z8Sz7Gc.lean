module

public import CFSG.Quasithin.Background.F918Z8Sz7Gb
public import CFSG.Quasithin.Background.F918Z8Sz6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Chief

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

omit [Finite Y] in
theorem chief_quarter_stable {W : Subgroup Y} {P Ξ : Subgroup (MulAut Y)}
    (hΞ : ∀ ξ ∈ Ξ, ∀ x ∈ P, ξ * x = x * ξ) (hΞW : Ξ ≤ stabSub W) :
    Ξ ≤ stabSub (W ⊓ fixV P) := by
  refine le_stabSub_of_forall_mem fun ξ hξ w hw => ⟨(hΞW hξ w).2 hw.1, fun p hp => ?_⟩
  have h1 : p (ξ w) = ξ (p w) := by
    have := hΞ ξ hξ p hp
    calc p (ξ w) = (p * ξ) w := rfl
      _ = (ξ * p) w := by rw [this]
      _ = ξ (p w) := rfl
  rw [h1, hw.2 p hp]

theorem chief_trivial_of_quarter {W : Subgroup Y} {P : Subgroup (MulAut Y)}
    (hfix : ∀ U : Subgroup Y, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) →
      Nat.card ↥U = Nat.card ↥(U ⊓ fixV P) ^ 4)
    (hWΛ : ∀ l ∈ Λ, ∀ w ∈ W, l w ∈ W) {a : MulAut Y} (haΛ : ∀ l ∈ Λ, a * l = l * a)
    (haM : ∀ u ∈ W ⊓ fixV P, a u = u) : ∀ w ∈ W, a w = w := by
  set M : Subgroup Y := W ⊓ fixV P with hM
  set U' : Subgroup Y := Subgroup.closure {y | ∃ l ∈ Λ, ∃ m ∈ M, y = l m} with hU'
  have hU'W : U' ≤ W := by
    rw [hU', Subgroup.closure_le]
    rintro _ ⟨l, hl, m, hm, rfl⟩
    exact hWΛ l hl m hm.1
  have hMU' : M ≤ U' := fun m hm => Subgroup.subset_closure ⟨1, Λ.one_mem, m, hm, by simp⟩
  have hinv : ∀ l ∈ Λ, ∀ u ∈ U', l u ∈ U' := by
    intro l hl u hu
    induction hu using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨l', hl', m, hm, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨l * l', Λ.mul_mem hl hl', m, hm, rfl⟩
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact U'.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact U'.inv_mem hx
  have hfixU' : U' ⊓ fixV P = M := by
    refine le_antisymm (fun u hu => ⟨hU'W hu.1, hu.2⟩) (fun u hu => ⟨hMU' hu, hu.2⟩)
  have hcard : Nat.card ↥U' = Nat.card ↥W := by
    have h1 := hfix U' hinv
    have h2 := hfix W hWΛ
    rw [hfixU'] at h1
    rw [h1, h2]
  have hUW : U' = W :=
    Subgroup.eq_of_le_of_card_ge hU'W (by rw [hcard])
  intro w hw
  rw [← hUW] at hw
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl, m, hm, rfl⟩ := hy
    have h1 : a (l m) = l (a m) := by
      calc a (l m) = (a * l) m := rfl
        _ = (l * a) m := by rw [haΛ l hl]
        _ = l (a m) := rfl
    rw [h1, haM m hm]
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  | inv x _ hx => rw [map_inv, hx]

theorem suz_chief_proved (hI : SuzXirr) {A X K : Subgroup (MulAut Y)} {W : Subgroup Y}
    (d : SuzData Γ Λ S V A X K W) (hXK : X = K) {n : ℕ} {P : Subgroup (MulAut Y)}
    {t : MulAut Y} (hn3 : 3 ≤ n) (hnodd : n % 2 = 1)
    (hP : IsSylowTwoOf P Λ) (htΛ : t ∈ Λ) (htN : t ∈ Subgroup.normalizer (P : Set (MulAut Y)))
    (htord : orderOf t = 2 ^ n - 1)
    (hfree : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → W ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥)
    (hfix : ∀ U : Subgroup Y, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) →
      Nat.card ↥U = Nat.card ↥(U ⊓ fixV P) ^ 4)
    (hrat : rAV (autSub A (W ⊓ fixV P)) ≤ ((1 / 2 : ℚ))) :
    ∃ I J : Subgroup Y, J < I ∧ I ≤ W ⊓ fixV P ∧ X ≤ stabSub I ∧ X ≤ stabSub J ∧
      A ≤ stabSub I ∧ A ≤ stabSub J ∧ (∀ w ∈ I, t w ∈ I) ∧ (∀ w ∈ J, t w ∈ J) ∧
      (∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) → T = J ∨ T = I) ∧
      (∃ x ∈ X, ∃ w ∈ I, x w * w⁻¹ ∉ J) ∧ A ⊓ centSec I J = A ⊓ centSub (W ⊓ fixV P) := by
  have hq : CFSG.Open.IsQuasisimple ↥X := hXK ▸ d.hKc.2.2
  have hPΛ : P ≤ Λ := hP.1
  have hXM : X ≤ stabSub (W ⊓ fixV P) :=
    chief_quarter_stable (fun ξ hξ x hx => d.hXc ξ hξ x (hPΛ hx)) d.hWX
  have hAM : A ≤ stabSub (W ⊓ fixV P) :=
    chief_quarter_stable (fun ξ hξ x hx => d.hAc ξ hξ x (hPΛ hx)) d.hWA
  have htM : ∀ w ∈ W ⊓ fixV P, t w ∈ W ⊓ fixV P := by
    intro w hw
    refine ⟨d.hWΛ t htΛ w hw.1, fun p hp => ?_⟩
    have hp' : t⁻¹ * p * t ∈ P := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ htN) p).1 hp
      simpa using this
    have e : p * t = t * (t⁻¹ * p * t) := by group
    calc p (t w) = (p * t) w := rfl
      _ = (t * (t⁻¹ * p * t)) w := by rw [e]
      _ = t ((t⁻¹ * p * t) w) := rfl
      _ = t w := by rw [hw.2 _ hp']
  have hnt : ∃ x ∈ X, ∃ w ∈ W ⊓ fixV P, x w ≠ w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, w, hw, hne⟩ := d.hXnt
    exact hne (chief_trivial_of_quarter hfix d.hWΛ (fun l hl => d.hXc x hx l hl)
      (fun u hu => hcon x hx u hu) w hw)
  obtain ⟨I, J, hJI, hIM, hXI, hXJ, hAI, hAJ, htI, htJ, hirr, hntI⟩ :=
    chief_exists_irr hq.1 (fun x hx w hw => (hXM hx w).2 hw) (fun a ha w hw => (hAM ha w).2 hw) htM
      d.hAX (fun x hx => (d.hXc x hx t htΛ).symm) hnt
  have hfaith : A ⊓ centSec I J = A ⊓ centSub (W ⊓ fixV P) := by
    refine le_antisymm ?_ ?_
    · intro a ha
      have hcomm := chief_faithful_aux hq hXI hXJ d.hAX hntI a ha
      exact ⟨ha.1, fun u hu => d.hBW a ha.1 (fun x hx => hcomm x hx) u hu.1⟩
    · intro a ha
      exact ⟨ha.1, hAI ha.1, fun w hw => by rw [ha.2 w (hIM hw)]; simp⟩
  exact ⟨I, J, hJI, hIM, hXI, hXJ, hAI, hAJ, htI, htJ,
    suz_xirr hI d hXK hn3 hnodd hP htΛ htN htord hfree hrat hJI hIM hXI hXJ hAI hAJ htI htJ hirr
      hntI hfaith, hntI, hfaith⟩

end Chief

end CFSG.Quasithin
