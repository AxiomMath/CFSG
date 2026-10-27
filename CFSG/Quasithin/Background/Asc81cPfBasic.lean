module

public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W]

section General

theorem mul_comm_of_isCyclic {X : Subgroup (MulAut W)} (hX : IsCyclic X) {a b : MulAut W}
    (ha : a ∈ X) (hb : b ∈ X) : a * b = b * a := by
  have := hX
  let _ : CommGroup X := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : X) ⟨b, hb⟩)

theorem odd_orderOf_of_mem {X : Subgroup (MulAut W)} (hX : Odd (Nat.card X)) {x : MulAut W}
    (hx : x ∈ X) : Odd (orderOf x) :=
  Odd.of_dvd_nat hX (Subgroup.orderOf_dvd_natCard X hx)

theorem odd_orderOf_mul {a b : MulAut W} (hab : Commute a b) (ha : Odd (orderOf a))
    (hb : Odd (orderOf b)) : Odd (orderOf (a * b)) :=
  Odd.of_dvd_nat (Odd.of_dvd_nat (ha.mul hb) (Nat.lcm_dvd_mul _ _)) hab.orderOf_mul_dvd_lcm

theorem commSub_stable_of_commute {X : Subgroup (MulAut W)} {c : MulAut W}
    (hc : ∀ x ∈ X, c * x = x * c) {u : W} (hu : u ∈ commSub (⊤ : Subgroup W) X) :
    c u ∈ commSub (⊤ : Subgroup W) X := by
  have hX : X.map (MulAut.conj c).toMonoidHom = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : c * x * c⁻¹ = x := by rw [hc x hx, mul_inv_cancel_right]
      show c * x * c⁻¹ ∈ X
      rw [h1]
      exact hx
    · intro hy
      refine ⟨y, hy, ?_⟩
      show c * y * c⁻¹ = y
      rw [hc y hy, mul_inv_cancel_right]
  have h := commSub_map_conj X c
  rw [hX] at h
  rw [h]
  exact ⟨u, hu, rfl⟩

theorem eq_one_of_stab (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W} (hg : Odd (orderOf g))
    {S : Subgroup W} (hS : ∀ s ∈ S, g s = s) (hgS : ∀ v, g v * v⁻¹ ∈ S) : g = 1 := by
  ext v
  obtain ⟨s, hsS, hs⟩ : ∃ s ∈ S, g v = s * v := ⟨g v * v⁻¹, hgS v, by rw [inv_mul_cancel_right]⟩
  have hfix : g s = s := hS s hsS
  have hpow : ∀ n : ℕ, (g ^ n) v = s ^ n * v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, hs, pow_succ, mul_assoc]
  have h1 := hpow (orderOf g)
  rw [pow_orderOf_eq_one, MulAut.one_apply] at h1
  have hsn : s ^ orderOf g = 1 := by
    have h2 : s ^ orderOf g * v = 1 * v := by rw [← h1, one_mul]
    exact mul_right_cancel h2
  obtain ⟨k, hk⟩ := hg
  have hs1 : s = 1 := by
    rw [hk, pow_succ, pow_mul, hW, one_pow, one_mul] at hsn
    exact hsn
  rw [MulAut.one_apply, hs, hs1, one_mul]

theorem commSub_iSup {ι : Type*} (L : ι → Subgroup (MulAut W)) :
    commSub (⊤ : Subgroup W) (⨆ i, L i) = ⨆ i, commSub (⊤ : Subgroup W) (L i) := by
  refine le_antisymm ?_ (iSup_le fun i => commSub_mono le_rfl (le_iSup L i))
  let S : Subgroup W := ⨆ i, commSub (⊤ : Subgroup W) (L i)
  let T : Subgroup (MulAut W) :=
    { carrier := {g | ∀ w, g w * w⁻¹ ∈ S}
      one_mem' := fun w => by
        show (1 : MulAut W) w * w⁻¹ ∈ S
        rw [MulAut.one_apply, mul_inv_cancel]
        exact S.one_mem
      mul_mem' := fun {a b} ha hb w => by
        have h1 := S.mul_mem (ha (b w)) (hb w)
        have h2 : (a * b) w * w⁻¹ = a (b w) * (b w)⁻¹ * (b w * w⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [h2]
        exact h1
      inv_mem' := fun {a} ha w => by
        have h1 := S.inv_mem (ha (a⁻¹ w))
        have h2 : a⁻¹ w * w⁻¹ = (a (a⁻¹ w) * (a⁻¹ w)⁻¹)⁻¹ := by
          rw [MulAut.apply_inv_self]
          group
        rw [h2]
        exact h1 }
  have hT : (⨆ i, L i) ≤ T := iSup_le fun i g hg w =>
    (le_iSup (fun i => commSub (⊤ : Subgroup W) (L i)) i)
      (Subgroup.subset_closure ⟨g, hg, w, Subgroup.mem_top w, rfl⟩)
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨g, hg, w, -, rfl⟩
  exact hT hg w

end General

section Hyp

variable {G X Y : Subgroup (MulAut W)}

theorem eq_one_of_apply_eq (h : Hyp101 G X) {x : MulAut W} (hx : x ∈ X) {v : W}
    (hv : v ∈ commSub (⊤ : Subgroup W) X) (hv1 : v ≠ 1) (hxv : x v = v) : x = 1 := by
  obtain ⟨y, -, huniq⟩ := h.2.2.2.2.1 v hv hv1 v hv hv1
  have h1 := huniq ⟨x, hx⟩ hxv
  have h2 := huniq 1 rfl
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem exists_apply_eq (h : Hyp101 G X) {v w : W} (hv : v ∈ commSub (⊤ : Subgroup W) X)
    (hv1 : v ≠ 1) (hw : w ∈ commSub (⊤ : Subgroup W) X) (hw1 : w ≠ 1) : ∃ x ∈ X, x v = w := by
  obtain ⟨x, hx, -⟩ := h.2.2.2.2.1 v hv hv1 w hw hw1
  exact ⟨x, x.2, hx⟩

theorem commSub_le_of_invariant' (h : Hyp101 G X) {S : Subgroup W}
    (hS : ∀ x ∈ X, ∀ s ∈ S, x s ∈ S) {w : W} (hwS : w ∈ S)
    (hw : w ∈ commSub (⊤ : Subgroup W) X) (hw1 : w ≠ 1) : commSub (⊤ : Subgroup W) X ≤ S := by
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    exact S.one_mem
  obtain ⟨x, hx, rfl⟩ := exists_apply_eq h hw hw1 hv hv1
  exact hS x hx w hwS

theorem commSub_ne_bot (h : Hyp101 G X) : commSub (⊤ : Subgroup W) X ≠ ⊥ := by
  intro h0
  apply h.2.1
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  ext w
  rw [MulAut.one_apply]
  exact (commSub_eq_bot_iff.1 h0) (Subgroup.mem_top w) x hx

theorem exists_ne_one (h : Hyp101 G X) : ∃ w ∈ commSub (⊤ : Subgroup W) X, w ≠ 1 := by
  by_contra hall
  push Not at hall
  exact commSub_ne_bot h ((Subgroup.eq_bot_iff_forall _).2 hall)

theorem exists_eq_on_commSub (h : Hyp101 G X) {c : MulAut W} (hc : ∀ x ∈ X, c * x = x * c) :
    ∃ x₀ ∈ X, ∀ v ∈ commSub (⊤ : Subgroup W) X, c v = x₀ v := by
  obtain ⟨w₀, hw₀, hw₀1⟩ := exists_ne_one h
  have hcw : c w₀ ∈ commSub (⊤ : Subgroup W) X := commSub_stable_of_commute hc hw₀
  have hcw1 : c w₀ ≠ 1 := fun h0 => hw₀1 (c.injective (h0.trans (map_one c).symm))
  obtain ⟨x₀, hx₀, hx₀w⟩ := exists_apply_eq h hw₀ hw₀1 hcw hcw1
  refine ⟨x₀, hx₀, fun v hv => ?_⟩
  by_cases hv1 : v = 1
  · rw [hv1, map_one, map_one]
  obtain ⟨x, hx, rfl⟩ := exists_apply_eq h hw₀ hw₀1 hv hv1
  have e1 : c (x w₀) = x (c w₀) := by
    rw [← MulAut.mul_apply, hc x hx, MulAut.mul_apply]
  have e2 : x₀ (x w₀) = x (x₀ w₀) := by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, mul_comm_of_isCyclic h.2.2.1 hx₀ hx]
  rw [e1, e2, hx₀w]

variable [Finite W]

theorem card_commSub (h : Hyp101 G X) :
    Nat.card (commSub (⊤ : Subgroup W) X) = Nat.card X + 1 := by
  obtain ⟨w₀, hw₀, hw₀1⟩ := exists_ne_one h
  have hmem : ∀ x : X, (x : MulAut W) w₀ ∈ ((commSub (⊤ : Subgroup W) X : Set W) \ {1}) := by
    intro x
    refine ⟨commSub_stable' x.2 hw₀, fun h0 => hw₀1 ?_⟩
    have h1 : (x : MulAut W) w₀ = (x : MulAut W) 1 := by
      rw [map_one]
      exact h0
    exact (x : MulAut W).injective h1
  let f : X → ↥((commSub (⊤ : Subgroup W) X : Set W) \ {1}) := fun x => ⟨_, hmem x⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : (x : MulAut W) w₀ = (y : MulAut W) w₀ := congrArg Subtype.val hxy
      have hyw : (y : MulAut W) w₀ ≠ 1 := fun h0 => (hmem y).2 h0
      obtain ⟨z, -, huniq⟩ := h.2.2.2.2.1 w₀ hw₀ hw₀1 _ (commSub_stable' y.2 hw₀) hyw
      exact (huniq x h1).trans (huniq y rfl).symm
    · rintro ⟨w, hwS, hw1⟩
      obtain ⟨x, hx, -⟩ := h.2.2.2.2.1 w₀ hw₀ hw₀1 w hwS hw1
      exact ⟨x, Subtype.ext hx⟩
  have h1 := Nat.card_congr (Equiv.ofBijective f hf)
  rw [card_diff_one] at h1
  have h2 : 0 < Nat.card (commSub (⊤ : Subgroup W) X) := Nat.card_pos
  omega

theorem fixV_eq_of_le (hW : ∀ w : W, w ^ 2 = 1) (h : Hyp101 G X) {A : Subgroup (MulAut W)}
    (hAX : A ≤ X) (hA : A ≠ ⊥) : fixV A = fixV X := by
  refine le_antisymm (fun v hv => ?_) (fun v hv a ha => hv a (hAX ha))
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hA ((Subgroup.eq_bot_iff_forall A).2 hall)
  have hv' : v ∈ fixV X ⊔ commSub ⊤ X := by
    rw [fixV_sup_commSub_eq_top' hW h.2.2.2.1]
    exact Subgroup.mem_top v
  obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv'
  have hac : a c = c := by
    have h1 : a (u * c) = u * c := hv a haA
    rw [map_mul, hu a (hAX haA)] at h1
    exact mul_left_cancel h1
  by_cases hc1 : c = 1
  · rw [hc1, mul_one]
    exact hu
  · exact absurd (eq_one_of_apply_eq h (hAX haA) hc hc1 hac) ha1

theorem commSub_eq_of_le (hW : ∀ w : W, w ^ 2 = 1) (h : Hyp101 G X) {A : Subgroup (MulAut W)}
    (hAX : A ≤ X) (hA : A ≠ ⊥) : commSub (⊤ : Subgroup W) A = commSub ⊤ X := by
  have hAodd : Odd (Nat.card A) := Odd.of_dvd_nat h.2.2.2.1 (Subgroup.card_dvd_of_le hAX)
  refine Subgroup.eq_of_le_of_card_ge (commSub_mono le_rfl hAX) ?_
  have h1 := card_fixV_mul_card_commSub hW hAodd
  have h2 := card_fixV_mul_card_commSub hW h.2.2.2.1
  rw [fixV_eq_of_le hW h hAX hA] at h1
  have hpos : 0 < Nat.card (fixV X) := Nat.card_pos
  have h3 := Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  omega

theorem commSub_le_fixV_of_commute (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X)
    (hY : Hyp101 G Y) (hXY : X ≠ Y) (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    commSub (⊤ : Subgroup W) X ≤ fixV Y := by
  by_contra hle
  obtain ⟨u, hu, hnot⟩ : ∃ u ∈ commSub (⊤ : Subgroup W) X, u ∉ fixV Y := by
    by_contra hall
    push Not at hall
    exact hle hall
  obtain ⟨y, hy, hyu⟩ : ∃ y ∈ Y, y u ≠ u := by
    by_contra hall
    push Not at hall
    exact hnot hall
  have hYU : ∀ y ∈ Y, ∀ v ∈ commSub (⊤ : Subgroup W) X, y v ∈ commSub (⊤ : Subgroup W) X :=
    fun y hy v hv => commSub_stable_of_commute (fun x hx => (hc x hx y hy).symm) hv
  have hXU' : ∀ x ∈ X, ∀ v ∈ commSub (⊤ : Subgroup W) Y, x v ∈ commSub (⊤ : Subgroup W) Y :=
    fun x hx v hv => commSub_stable_of_commute (fun y hy => hc x hx y hy) hv
  have hc0 : y u * u⁻¹ ∈ commSub (⊤ : Subgroup W) X :=
    (commSub ⊤ X).mul_mem (hYU y hy u hu) ((commSub ⊤ X).inv_mem hu)
  have hc0' : y u * u⁻¹ ∈ commSub (⊤ : Subgroup W) Y :=
    Subgroup.subset_closure ⟨y, hy, u, Subgroup.mem_top u, rfl⟩
  have hc01 : y u * u⁻¹ ≠ 1 := fun h0 => hyu (mul_inv_eq_one.1 h0)
  have hU'U : commSub (⊤ : Subgroup W) Y ≤ commSub ⊤ X :=
    commSub_le_of_invariant' hY hYU hc0 hc0' hc01
  obtain ⟨w', hw'U', hw'1⟩ := exists_ne_one hY
  obtain ⟨x, hx, hxw'⟩ : ∃ x ∈ X, x w' ≠ w' := by
    by_contra hall
    push Not at hall
    have h1 : w' ∈ fixV X ⊓ commSub ⊤ X := ⟨hall, hU'U hw'U'⟩
    rw [fixV_inf_commSub_eq_bot' hW hX.2.2.2.1] at h1
    exact hw'1 h1
  have hc1 : x w' * w'⁻¹ ∈ commSub (⊤ : Subgroup W) Y :=
    (commSub ⊤ Y).mul_mem (hXU' x hx w' hw'U') ((commSub ⊤ Y).inv_mem hw'U')
  have hc1' : x w' * w'⁻¹ ∈ commSub (⊤ : Subgroup W) X :=
    Subgroup.subset_closure ⟨x, hx, w', Subgroup.mem_top w', rfl⟩
  have hc11 : x w' * w'⁻¹ ≠ 1 := fun h0 => hxw' (mul_inv_eq_one.1 h0)
  have hUU' : commSub (⊤ : Subgroup W) X ≤ commSub ⊤ Y :=
    commSub_le_of_invariant' hX hXU' hc1 hc1' hc11
  have hUeq : commSub (⊤ : Subgroup W) X = commSub ⊤ Y := le_antisymm hUU' hU'U
  have hYX : Y ≤ X := by
    intro y' hy'
    obtain ⟨x₀, hx₀, hx₀v⟩ :=
      exists_eq_on_commSub hX (c := y') fun x hx => (hc x hx y' hy').symm
    have hcomm : Commute x₀⁻¹ y' := (show Commute x₀ y' from hc x₀ hx₀ y' hy').inv_left
    have hodd : Odd (orderOf (x₀⁻¹ * y')) :=
      odd_orderOf_mul hcomm (odd_orderOf_of_mem hX.2.2.2.1 (X.inv_mem hx₀))
        (odd_orderOf_of_mem hY.2.2.2.1 hy')
    have hg : x₀⁻¹ * y' = 1 := by
      refine eq_one_of_stab hW hodd (S := commSub ⊤ X) (fun s hs => ?_) (fun v => ?_)
      · rw [MulAut.mul_apply, hx₀v s hs, MulAut.inv_apply_self]
      · have h1 : x₀⁻¹ (y' v) * (y' v)⁻¹ ∈ commSub (⊤ : Subgroup W) X :=
          Subgroup.subset_closure ⟨x₀⁻¹, X.inv_mem hx₀, y' v, Subgroup.mem_top _, rfl⟩
        have h2 : y' v * v⁻¹ ∈ commSub (⊤ : Subgroup W) X := by
          rw [hUeq]
          exact Subgroup.subset_closure ⟨y', hy', v, Subgroup.mem_top _, rfl⟩
        have h3 := (commSub ⊤ X).mul_mem h1 h2
        have h4 : (x₀⁻¹ * y') v * v⁻¹ = x₀⁻¹ (y' v) * (y' v)⁻¹ * (y' v * v⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [h4]
        exact h3
    rw [← inv_mul_eq_one.1 hg]
    exact hx₀
  have hcard : Nat.card X = Nat.card Y := by
    have h1 := card_commSub hX
    have h2 := card_commSub hY
    rw [hUeq] at h1
    omega
  exact hXY (Subgroup.eq_of_le_of_card_ge hYX (by rw [hcard])).symm

theorem commSub_inf_commSub_eq_bot (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X)
    (hY : Hyp101 G Y) (hXY : X ≠ Y) (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    commSub (⊤ : Subgroup W) X ⊓ commSub ⊤ Y = ⊥ := by
  have h1 := commSub_le_fixV_of_commute hW hX hY hXY hc
  rw [eq_bot_iff]
  intro w hw
  have h2 : w ∈ fixV Y ⊓ commSub ⊤ Y := ⟨h1 hw.1, hw.2⟩
  rwa [fixV_inf_commSub_eq_bot' hW hY.2.2.2.1] at h2

end Hyp

end Pf

end Asc81c

end CFSG.Quasithin
