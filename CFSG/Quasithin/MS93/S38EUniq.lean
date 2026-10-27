module

public import CFSG.Quasithin.MS93.S38ECount
public import CFSG.Quasithin.MS93.S38EMod

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin

variable {Y : Type*} [CommGroup Y]

@[expose] def IrrSec (X : Subgroup (MulAut Y)) (W N : Subgroup Y) : Prop :=
  N < W ∧ Stab X W ∧ Stab X N ∧
    ∀ J : Subgroup Y, Stab X J → N ≤ J → J ≤ W → J = N ∨ J = W

@[expose] def NonCent (K : Subgroup (MulAut Y)) (W N : Subgroup Y) : Prop :=
  ∃ k ∈ K, ∃ w ∈ W, k w * w⁻¹ ∉ N

theorem Stab.mono {X X' : Subgroup (MulAut Y)} {W : Subgroup Y} (h : Stab X W) (hX : X' ≤ X) :
    Stab X' W := fun x hx => h x (hX hx)

theorem stab_fixV {X K : Subgroup (MulAut Y)}
    (hKn : X ≤ Subgroup.normalizer (K : Set (MulAut Y))) : Stab X (fixV K) := by
  intro x hx y hy k hk
  have hk' : x⁻¹ * k * x⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKn (X.inv_mem hx)) k).mp hk
  have h1 := hy _ hk'
  have : k (x y) = x ((x⁻¹ * k * x) y) := by simp [MulAut.mul_apply]
  rw [this]
  rw [inv_inv] at h1
  rw [h1]

theorem stab_commV {X K : Subgroup (MulAut Y)}
    (hKn : X ≤ Subgroup.normalizer (K : Set (MulAut Y))) : Stab X (commV K) := by
  intro x hx y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, v, rfl⟩ := hy
    have hk' : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKn hx) k).mp hk
    have e : x (k v * v⁻¹) = (x * k * x⁻¹) (x v) * (x v)⁻¹ := by
      simp [MulAut.mul_apply, map_mul, map_inv]
    rw [e]
    exact Subgroup.subset_closure ⟨_, hk', _, rfl⟩
  | one => rw [map_one]; exact (commV K).one_mem
  | mul a b _ _ ha hb => rw [map_mul]; exact (commV K).mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact (commV K).inv_mem ha

theorem stab_top (X : Subgroup (MulAut Y)) : Stab X ⊤ := fun _ _ _ _ => Subgroup.mem_top _

theorem stab_bot (X : Subgroup (MulAut Y)) : Stab X ⊥ := by
  intro x _ y hy
  rw [Subgroup.mem_bot] at hy ⊢
  rw [hy, map_one]

theorem stab_inf {X : Subgroup (MulAut Y)} {A B : Subgroup Y} (hA : Stab X A) (hB : Stab X B) :
    Stab X (A ⊓ B) := fun x hx y hy => ⟨hA x hx y hy.1, hB x hx y hy.2⟩

section Finite

variable [Finite Y]

theorem exists_minimal {X : Subgroup (MulAut Y)} {W N : Subgroup Y} (hNW : N < W)
    (hW : Stab X W) :
    ∃ S : Subgroup Y, Stab X S ∧ N < S ∧ S ≤ W ∧
      ∀ J : Subgroup Y, Stab X J → N < J → J ≤ S → J = S := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Subgroup Y, Stab X S ∧ N < S ∧ S ≤ W ∧ Nat.card S = n
  have hP : ∃ n, P n := ⟨_, W, hW, hNW, le_rfl, rfl⟩
  obtain ⟨S, hS, hNS, hSW, hcard⟩ := Nat.find_spec hP
  refine ⟨S, hS, hNS, hSW, fun J hJ hNJ hJS => ?_⟩
  have hmin := Nat.find_min' hP ⟨J, hJ, hNJ, hJS.trans hSW, rfl⟩
  rw [← hcard] at hmin
  exact Subgroup.eq_of_le_of_card_ge hJS hmin

theorem exists_maximal {X : Subgroup (MulAut Y)} {W N : Subgroup Y} (hNW : N < W)
    (hN : Stab X N) :
    ∃ S : Subgroup Y, Stab X S ∧ N ≤ S ∧ S < W ∧
      ∀ J : Subgroup Y, Stab X J → S ≤ J → J < W → J = S := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Subgroup Y, Stab X S ∧ N ≤ S ∧ S < W ∧
    Nat.card Y - Nat.card S = n
  have hP : ∃ n, P n := ⟨_, N, hN, le_rfl, hNW, rfl⟩
  obtain ⟨S, hS, hNS, hSW, hcard⟩ := Nat.find_spec hP
  refine ⟨S, hS, hNS, hSW, fun J hJ hSJ hJW => ?_⟩
  have hmin := Nat.find_min' hP ⟨J, hJ, hNS.trans hSJ, hJW, rfl⟩
  rw [← hcard] at hmin
  have h1 : Nat.card J ≤ Nat.card Y := Subgroup.card_le_card_group J
  have h2 : Nat.card S ≤ Nat.card J := Subgroup.card_le_of_le hSJ
  exact (Subgroup.eq_of_le_of_card_ge hSJ (by omega)).symm

theorem cI_eq_aI_of_pairing (p : Pairing Y ℂˣ) {E : Subgroup (MulAut Y)} (hE : p.IsInv E) :
    cI E ⊤ ⊥ = aI E ⊤ ⊥ := by
  rw [cI_top_bot, aI_top_bot]
  have h1 := p.card_commV_mul_card_fixV hE
  have h2 := (fixV E).index_mul_card
  have hpos : 0 < Nat.card (fixV E) := Nat.card_pos
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem irrSec_commV (hY : ∀ y : Y, y ^ 2 = 1) (p : Pairing Y ℂˣ) {X K E : Subgroup (MulAut Y)}
    (hpX : p.IsInv X) (hKX : K ≤ X) (hEX : E ≤ X)
    (hKn : X ≤ Subgroup.normalizer (K : Set (MulAut Y))) (hKp : ⁅K, K⁆ = K)
    {e : ℕ} (he : e = 2 ∨ e = 4) (hFF : (fixV E).index ≤ e)
    (hfaith : ∀ W N : Subgroup Y, ∀ hirr : IrrSec X W N, NonCent K W N →
      e ≤ (kerRel E W N (hirr.2.2.1.mono hEX)).relIndex E)
    (hK1 : NonCent K ⊤ ⊥) :
    IrrSec X (commV K) (commV K ⊓ fixV K) := by
  set W₀ := commV K with hW₀
  set M₀ := commV K ⊓ fixV K with hM₀
  have hW₀s : Stab X W₀ := stab_commV hKn
  have hFs : Stab X (fixV K) := stab_fixV hKn
  have hM₀s : Stab X M₀ := stab_inf hW₀s hFs
  have hKs : ∀ k ∈ K, ∀ y : Y, k y * y⁻¹ ∈ W₀ := fun k hk y =>
    Subgroup.subset_closure ⟨k, hk, y, rfl⟩
  have htriv : ∀ A : Subgroup Y, Stab K A → (∀ k ∈ K, ∀ a ∈ A, k a * a⁻¹ ∈ fixV K) →
      A ≤ fixV K := by
    intro A hA h a ha k hk
    have := perfect_trivial_of_two_step hKp hA (stab_bot K) h
      (fun k hk w hw => by rw [Subgroup.mem_bot, mul_inv_eq_one]; exact hw k hk) k hk a ha
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
  have hc : cI E ⊤ ⊥ = aI E ⊤ ⊥ := cI_eq_aI_of_pairing p (hpX.mono hEX)
  have haY : aI E ⊤ ⊥ ≤ e := by rw [aI_top_bot]; exact hFF
  have hlt : M₀ < W₀ := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    have hW₀F : W₀ ≤ fixV K := by rw [← heq]; exact inf_le_right
    obtain ⟨k, hk, y, -, hy⟩ := hK1
    apply hy
    rw [Subgroup.mem_bot, mul_inv_eq_one]
    have h1 := htriv ⊤ (stab_top K) (fun k hk a _ => hW₀F (hKs k hk a)) (Subgroup.mem_top y)
    exact h1 k hk
  refine ⟨hlt, hW₀s, hM₀s, fun J hJ hMJ hJW => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hJM, hJW'⟩ := hcon
  have hMJ' : M₀ < J := lt_of_le_of_ne hMJ (Ne.symm hJM)
  have hJW'' : J < W₀ := lt_of_le_of_ne hJW hJW'
  obtain ⟨S, hS, hMS, hSJ, hSmin⟩ := exists_minimal hMJ' hJ
  obtain ⟨N', hN', hJN', hN'W, hN'max⟩ := exists_maximal hJW'' hJ
  have hirrS : IrrSec X S M₀ := ⟨hMS, hS, hM₀s, fun J' hJ' h1 h2 => by
    rcases eq_or_lt_of_le h1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hSmin J' hJ' h h2)⟩
  have hirrW : IrrSec X W₀ N' := ⟨hN'W, hW₀s, hN', fun J' hJ' h1 h2 => by
    rcases eq_or_lt_of_le h2 with h | h
    · exact Or.inr h
    · exact Or.inl (hN'max J' hJ' h1 h)⟩
  have hSW : S ≤ W₀ := hSJ.trans hJW
  have hncS : NonCent K S M₀ := by
    by_contra hnc
    unfold NonCent at hnc
    push Not at hnc
    have h1 : S ≤ fixV K := htriv S (hS.mono hKX) fun k hk a ha => (hnc k hk a ha).2
    exact (lt_irrefl M₀) (lt_of_lt_of_le hMS (le_inf hSW h1))
  have hncW : NonCent K W₀ N' := by
    by_contra hnc
    unfold NonCent at hnc
    push Not at hnc
    have h1 := perfect_trivial_of_two_step hKp (stab_top K) (hN'.mono hKX)
      (fun k hk y _ => hKs k hk y) hnc
    have h2 : W₀ ≤ N' := by
      rw [hW₀, commV, Subgroup.closure_le]
      rintro _ ⟨k, hk, y, rfl⟩
      exact h1 k hk y (Subgroup.mem_top y)
    exact (lt_irrefl N') (lt_of_lt_of_le hN'W h2)
  have he2 : 2 ≤ e := by rcases he with rfl | rfl <;> omega
  have hnt : ∀ W N : Subgroup Y, ∀ hirr : IrrSec X W N, NonCent K W N →
      ∃ x ∈ E, ∃ w ∈ W, x w * w⁻¹ ∉ N := by
    intro W N hirr hnc
    have h1 := hfaith W N hirr hnc
    by_contra hcon
    push Not at hcon
    have h2 : (kerRel E W N (hirr.2.2.1.mono hEX)).relIndex E = 1 :=
      Subgroup.relIndex_eq_one.mpr fun x hx => ⟨hx, fun w hw => hcon x hx w hw⟩
    omega
  obtain ⟨x₁, hx₁, w₁, hw₁, hn₁⟩ := hnt S M₀ hirrS hncS
  obtain ⟨x₂, hx₂, w₂, hw₂, hn₂⟩ := hnt W₀ N' hirrW hncW
  have hEs : ∀ A : Subgroup Y, Stab X A → Stab E A := fun A hA => hA.mono hEX
  have ha1 := two_le_aI hx₁ hw₁ hn₁
  have ha2 := two_le_aI hx₂ hw₂ hn₂
  have hc1 := two_le_cI hx₁ hw₁ hn₁
  have hc2 := two_le_cI hx₂ hw₂ hn₂
  have hSN' : S ≤ N' := hSJ.trans hJN'
  have hA : aI E W₀ N' * aI E S M₀ ≤ aI E ⊤ ⊥ := by
    have h1 := aI_mul_le (E := E) (W := W₀) (W' := N') (N := M₀) (hEs N' hN')
      (hMS.le.trans hSN') hN'W.le
    have h2 := aI_le_of_le (E := E) (W := N') (W' := S) (N := M₀) (hEs S hS) hMS.le hSN'
    have h3 := aI_le_of_le (E := E) (W := ⊤) (W' := W₀) (N := M₀) (hEs W₀ hW₀s) hlt.le le_top
    have h4 := aI_le_of_le' (E := E) (W := ⊤) (W' := M₀) (N := ⊥) (hEs M₀ hM₀s) bot_le le_top
    calc aI E W₀ N' * aI E S M₀ ≤ aI E W₀ N' * aI E N' M₀ := Nat.mul_le_mul_left _ h2
      _ ≤ aI E W₀ M₀ := h1
      _ ≤ aI E ⊤ M₀ := h3
      _ ≤ aI E ⊤ ⊥ := h4
  have hC : cI E W₀ N' * cI E S M₀ ≤ cI E ⊤ ⊥ := by
    have h1 := cI_mul_le (E := E) (W := W₀) (W' := N') (N := M₀) (hEs N' hN')
      (hMS.le.trans hSN') hN'W.le
    have h2 := cI_le_of_le (E := E) (W := N') (W' := S) (N := M₀) (hEs S hS) hMS.le hSN'
    have h3 := cI_le_of_le (E := E) (W := ⊤) (W' := W₀) (N := M₀) (hEs W₀ hW₀s) hlt.le le_top
    have h4 := cI_le_of_le' (E := E) (W := ⊤) (W' := M₀) (N := ⊥) (hEs M₀ hM₀s) bot_le le_top
    calc cI E W₀ N' * cI E S M₀ ≤ cI E W₀ N' * cI E N' M₀ := Nat.mul_le_mul_left _ h2
      _ ≤ cI E W₀ M₀ := h1
      _ ≤ cI E ⊤ M₀ := h3
      _ ≤ cI E ⊤ ⊥ := h4
  have ha_eq : aI E S M₀ = 2 := by
    have : aI E W₀ N' * aI E S M₀ ≤ 4 := by rcases he with rfl | rfl <;> omega
    nlinarith
  have hc_eq : cI E S M₀ = 2 := by
    have : cI E W₀ N' * cI E S M₀ ≤ 4 := by rcases he with rfl | rfl <;> omega
    nlinarith
  have he4 : e = 4 := by
    rcases he with rfl | rfl
    · exfalso
      nlinarith
    · rfl
  have hk := relIndex_kerRel_le_two hY (hEs S hS) (hEs M₀ hM₀s) ha_eq hc_eq
  have := hfaith S M₀ hirrS hncS
  omega

end Finite

end CFSG.Quasithin.MS93.S38E
