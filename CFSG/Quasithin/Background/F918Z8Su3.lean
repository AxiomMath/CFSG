module

public import CFSG.Quasithin.Background.F918Z8Su2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

section Suz

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

omit [Finite Y] in
theorem suz_norm (hexp : ∀ y : Y, y ^ 2 = 1) {x : MulAut Y} (hx2 : x * x * x = 1) (u : Y)
    (h : x (x u * u⁻¹) = x u * u⁻¹) : x u * u⁻¹ = 1 := by
  have hxxx : ∀ v : Y, x (x (x v)) = v := fun v => by
    calc x (x (x v)) = (x * x * x) v := rfl
      _ = v := by rw [hx2]; rfl
  have hprod : (x u * u⁻¹) * x (x u * u⁻¹) * x (x (x u * u⁻¹)) = 1 := by
    simp only [map_mul, map_inv, hxxx]
    exact d321s_comm_aux (x u) u (x (x u))
  simp only [h] at hprod
  have hw2 : (x u * u⁻¹) * (x u * u⁻¹) = 1 := by rw [← sq]; exact hexp _
  rw [hw2, one_mul] at hprod
  exact hprod

theorem suz_AxB_data
    (h : LocCfg Γ Λ S V) {A : Subgroup (MulAut Y)} (hA : A ∈ QhatStar Γ)
    (hAc : ∀ a ∈ A, ∀ x ∈ Λ, a * x = x * a) {X : Subgroup (MulAut Y)}
    (hXc : ∀ x ∈ X, ∀ y ∈ Λ, x * y = y * x) (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut Y)))
    (hXA : ⁅X, A⁆ = X) (h3 : 3 ∣ Nat.card ↥X) :
    ∃ W : Subgroup Y, W ≠ ⊥ ∧ (∀ l ∈ Λ, ∀ w ∈ W, l w ∈ W) ∧ A ≤ stabSub W ∧ X ≤ stabSub W ∧
      (∀ b ∈ A, (∀ x ∈ X, b * x = x * b) → ∀ w ∈ W, b w = w) ∧
      (∃ x ∈ X, ∃ w ∈ W, x w ≠ w) ∧ commSub W A ≠ ⊥ ∧
      IsA2 (autSub Γ W) (autSub A W) ∧ commSeries (autSub A W) 3 = ⊥ ∧ rAV (autSub A W) ≤ 2 := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := QhatStar_spec hA
  have hexp : ∀ y : Y, y ^ 2 = 1 := h.std.hyp.exp
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA2.2.2.1
  have hA2' : ∀ a ∈ A, a ^ 2 = 1 := hA2.2.2.2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3
  set x : MulAut Y := (g : MulAut Y) with hxdef
  have hxX : x ∈ X := g.2
  have hx3 : x ^ 3 = 1 := by
    have : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    simpa using congrArg Subtype.val this
  have hx1 : x ≠ 1 := by
    intro hx1
    have : g = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hg
    omega
  have hx2 : x * x * x = 1 := by simpa [pow_succ] using hx3
  set B : Subgroup (MulAut Y) := A ⊓ Subgroup.centralizer (X : Set (MulAut Y)) with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBX : ∀ b ∈ B, ∀ x' ∈ X, b * x' = x' * b := fun b hb x' hx' =>
    ((Subgroup.mem_centralizer_iff.1 hb.2) x' hx').symm
  set F : Subgroup Y := fixV B with hFdef
  have hFA : ∀ a ∈ A, ∀ u ∈ F, a u ∈ F := fun a ha u hu b hb => by
    have hab : b * a = a * b := hAab b (hBA hb) a ha
    calc b (a u) = (b * a) u := rfl
      _ = (a * b) u := by rw [hab]
      _ = a (b u) := rfl
      _ = a u := by rw [hu b hb]
  have hFX : ∀ x' ∈ X, ∀ u ∈ F, x' u ∈ F := fun x' hx' u hu b hb => by
    calc b (x' u) = (b * x') u := rfl
      _ = (x' * b) u := by rw [hBX b hb x' hx']
      _ = x' (b u) := rfl
      _ = x' u := by rw [hu b hb]
  have hFΛ : ∀ l ∈ Λ, ∀ u ∈ F, l u ∈ F := fun l hl u hu b hb => by
    have hbl : b * l = l * b := hAc b (hBA hb) l hl
    calc b (l u) = (b * l) u := rfl
      _ = (l * b) u := by rw [hbl]
      _ = l (b u) := rfl
      _ = l u := by rw [hu b hb]
  set W : Subgroup Y := commSub F X with hWdef
  have hFsA : A ≤ stabSub F := le_stabSub_of_forall_mem hFA
  have hFsX : X ≤ stabSub F := le_stabSub_of_forall_mem hFX
  have hFsΛ : Λ ≤ stabSub F := le_stabSub_of_forall_mem hFΛ
  have hWA : A ≤ stabSub W := fun a ha => mem_stabSub_commSub (hFsA ha) (hAX ha)
  have hWX : X ≤ stabSub W := fun x' hx' =>
    mem_stabSub_commSub (hFsX hx') (Subgroup.le_normalizer hx')
  have hΛnorm : ∀ l ∈ Λ, l ∈ Subgroup.normalizer (X : Set (MulAut Y)) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : l * y * l⁻¹ = y := by
        have := hXc y hy l hl
        calc l * y * l⁻¹ = (l * y) * l⁻¹ := rfl
          _ = (y * l) * l⁻¹ := by rw [← this]
          _ = y := by group
      rw [this]; exact hy
    · intro hy
      have hc := hXc _ hy l hl
      have : y = l⁻¹ * (l * y * l⁻¹) * l := by group
      have h2 : l⁻¹ * (l * y * l⁻¹) * l = l * y * l⁻¹ := by
        calc l⁻¹ * (l * y * l⁻¹) * l = l⁻¹ * ((l * y * l⁻¹) * l) := by rw [mul_assoc]
          _ = l⁻¹ * (l * (l * y * l⁻¹)) := by rw [hc]
          _ = l * y * l⁻¹ := by group
      rw [this, h2]; exact hy
  have hWΛ : ∀ l ∈ Λ, ∀ w ∈ W, l w ∈ W := fun l hl w hw =>
    ((mem_stabSub_commSub (hFsΛ hl) (hΛnorm l hl)) w).2 hw
  have hWF : W ≤ F := by
    rw [hWdef, commSub, Subgroup.closure_le]
    rintro _ ⟨x', hx', u, hu, rfl⟩
    exact F.mul_mem (hFX x' hx' u hu) (F.inv_mem hu)
  have hBW : ∀ b ∈ A, (∀ x' ∈ X, b * x' = x' * b) → ∀ w ∈ W, b w = w := by
    intro b hb hbX w hw
    have hbB : b ∈ B := ⟨hb, Subgroup.mem_centralizer_iff.2 fun x' hx' => (hbX x' hx').symm⟩
    exact hWF hw b hbB
  have hWc : ∀ u ∈ F, x u * u⁻¹ ∈ W := fun u hu =>
    Subgroup.subset_closure ⟨x, hxX, u, hu, rfl⟩
  have hnoFix : ¬ ∀ u ∈ F, x u = u := by
    intro hfix
    have hR : IsPGroup 2 Y := fun y => ⟨1, by simpa using hexp y⟩
    have hA' : ¬ 2 ∣ Nat.card ↥(Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]; norm_num
    have hB2 : IsPGroup 2 ↥B := fun b =>
      ⟨1, Subtype.ext (by simpa using hA2' (b : MulAut Y) (hBA b.2))⟩
    have hcomm : ∀ (a : ↥(Subgroup.zpowers x)) (b : ↥B),
        (Subgroup.zpowers x).subtype a * B.subtype b =
          B.subtype b * (Subgroup.zpowers x).subtype a := by
      intro a b
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 a.2
      show (a : MulAut Y) * (b : MulAut Y) = (b : MulAut Y) * (a : MulAut Y)
      rw [← hk]
      exact (Commute.zpow_right (hBX b b.2 x hxX : Commute (b : MulAut Y) x) k).symm
    have hfix' : ∀ (a : ↥(Subgroup.zpowers x)) (r : Y), (∀ b : ↥B, B.subtype b r = r) →
        (Subgroup.zpowers x).subtype a r = r := by
      intro a r hr
      have hrF : r ∈ F := fun b hb => hr ⟨b, hb⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 a.2
      show (a : MulAut Y) r = r
      rw [← hk]
      have hxr : x ∈ MulAction.stabilizer (MulAut Y) r := by
        rw [MulAction.mem_stabilizer_iff]
        exact hfix r hrF
      have := Subgroup.zpow_mem _ hxr k
      rwa [MulAction.mem_stabilizer_iff] at this
    have hall := CFSG.GroupTheory.thompson_A_times_B (p := 2) hR hA' hB2
      (Subgroup.zpowers x).subtype B.subtype hcomm hfix'
    exact hx1 (hall ⟨x, Subgroup.mem_zpowers x⟩)
  have hW0 : W ≠ ⊥ := by
    intro hW0
    apply hnoFix
    intro u hu
    have hmem : x u * u⁻¹ ∈ W := hWc u hu
    rw [hW0, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hXnt : ∃ x' ∈ X, ∃ w ∈ W, x' w ≠ w := by
    by_contra hcon
    push Not at hcon
    apply hnoFix
    intro u hu
    have h1 := suz_norm hexp hx2 u (hcon x hxX _ (hWc u hu))
    exact mul_inv_eq_one.1 h1
  have hAW : A ≤ stabSub W := hWA
  have hUA : commSub W A ≠ ⊥ := by
    intro hbot
    rw [commSub_eq_bot_iff] at hbot
    have hcomm : ⁅X, A⁆ ≤ centSub W := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂ w hw
      rw [commutatorElement_def]
      have e1 : g₂⁻¹ w = w := by
        have := hbot hw g₂⁻¹ (A.inv_mem hg₂)
        exact this
      have e2 : g₁⁻¹ w ∈ W := ((hWX (X.inv_mem hg₁)) w).2 hw
      have e3 : g₂ (g₁⁻¹ w) = g₁⁻¹ w := hbot e2 g₂ hg₂
      show g₁ (g₂ (g₁⁻¹ (g₂⁻¹ w))) = w
      rw [e1, e3]
      simp
    rw [hXA] at hcomm
    obtain ⟨x', hx', w, hw, hne⟩ := hXnt
    exact hne (hcomm hx' w hw)
  have hRP : A ∈ RPlusLe Γ r := by
    obtain ⟨⟨⟨hA2', hAr'⟩, -⟩, hplus⟩ := (D2_7 hexp hr hA hAW hUA).1
    exact ⟨⟨hA2', hAr'.le⟩, hplus⟩
  obtain ⟨hAU, hrAU⟩ := D2_5 hexp hRP hAW hUA
  exact ⟨W, hW0, hWΛ, hAW, hWX, hBW, hXnt, hUA, hAU, commSeries_autSub_eq_bot hAW hA3,
    hrAU.trans hr2⟩
end Suz

end CFSG.Quasithin
