module

public import CFSG.Quasithin.Background.B1Coprime
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin

namespace E6

variable {W : Type*} [CommGroup W] [Finite W]

omit [Finite W] in
theorem comm_of_isCyclic {X : Subgroup (MulAut W)} (hX : IsCyclic X) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  let _ : CommGroup X := IsCyclic.commGroup
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : X) ⟨b, hb⟩)

omit [Finite W] in
theorem card_diff_one' (S : Subgroup W) : Nat.card ↥((S : Set W) \ {1}) = Nat.card S - 1 := by
  rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem S.one_mem, ← Nat.card_coe_set_eq]
  rfl

theorem relIndex_centSub_le_aux (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hXc : IsCyclic X) (hXo : Odd (Nat.card X)) (N : ℕ) :
    ∀ (S : Subgroup W), Nat.card S = N → (∀ x ∈ X, ∀ s ∈ S, x s ∈ S) → S ≠ ⊥ →
      (X ⊓ centSub S).relIndex X ≤ Nat.card S - 1 ∧
      ((X ⊓ centSub S).relIndex X = Nat.card S - 1 →
        ∀ s ∈ S, s ≠ 1 → ∀ x ∈ X, x s = s → x ∈ centSub S) := by
  classical
  have hXab := comm_of_isCyclic hXc
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro S h hSinv hS1
  by_cases hA : ∀ s ∈ S, s ≠ 1 → ∀ x ∈ X, x s = s → x ∈ centSub S
  ·
    refine ⟨?_, fun _ => hA⟩
    obtain ⟨s, hsS, hs1⟩ : ∃ s ∈ S, s ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hS1 ((Subgroup.eq_bot_iff_forall S).2 hall)
    let C := (X ⊓ centSub S).subgroupOf X
    let f : ↥X ⧸ C → ↥((S : Set W) \ {1}) := fun q => Quotient.liftOn' q
      (fun x => ⟨(x : MulAut W) s, hSinv x x.2 s hsS, fun h1 => hs1 (by
        have h2 : (x : MulAut W) s = (x : MulAut W) 1 := by rw [map_one]; exact h1
        exact (x : MulAut W).injective h2)⟩)
      (fun x y hxy => by
        apply Subtype.ext
        have hc : x⁻¹ * y ∈ C := QuotientGroup.leftRel_apply.1 hxy
        have h1 : ((x⁻¹ * y : X) : MulAut W) s = s := (Subgroup.mem_subgroupOf.1 hc).2 s hsS
        have h2 : (x : MulAut W)⁻¹ ((y : MulAut W) s) = s := h1
        show (x : MulAut W) s = (y : MulAut W) s
        conv_lhs => rw [← h2]
        exact MulAut.apply_inv_self W (x : MulAut W) _)
    have hf : Function.Injective f := by
      intro q₁ q₂ h12
      induction q₁ using QuotientGroup.induction_on with | H x => ?_
      induction q₂ using QuotientGroup.induction_on with | H y => ?_
      have h1 : (x : MulAut W) s = (y : MulAut W) s := congrArg Subtype.val h12
      apply QuotientGroup.eq.2
      refine Subgroup.mem_subgroupOf.2 ⟨(x⁻¹ * y : X).2, ?_⟩
      apply hA s hsS hs1 _ (x⁻¹ * y : X).2
      show (x : MulAut W)⁻¹ ((y : MulAut W) s) = s
      rw [← h1, MulAut.inv_apply_self]
    have := Nat.card_le_card_of_injective f hf
    rw [card_diff_one'] at this
    exact this
  ·
    push Not at hA
    obtain ⟨s, hsS, hs1, η, hηX, hηs, hηC⟩ := hA
    set Y := Subgroup.zpowers η with hYdef
    have hYX : Y ≤ X := Subgroup.zpowers_le.2 hηX
    have hYo : Odd (Nat.card Y) := Odd.of_dvd_nat hXo (Subgroup.card_dvd_of_le hYX)
    have hYinv : ∀ y ∈ Y, ∀ m ∈ S, y m ∈ S := fun y hy m hm => hSinv y (hYX hy) m hm
    obtain ⟨hdec1, hdec2⟩ := B1.coprime_decomp hW hYo (M := S) hYinv
    set S₁ := S ⊓ fixV Y with hS₁def
    set S₂ := commSub S Y with hS₂def
    have hS₁inv : ∀ x ∈ X, ∀ m ∈ S₁, x m ∈ S₁ := by
      intro x hx m hm
      refine ⟨hSinv x hx m hm.1, fun y hy => ?_⟩
      have hyx : y * x = x * y := hXab y (hYX hy) x hx
      have h1 : (y * x) m = (x * y) m := by rw [hyx]
      rw [MulAut.mul_apply, MulAut.mul_apply, hm.2 y hy] at h1
      exact h1
    have hS₂inv : ∀ x ∈ X, ∀ m ∈ S₂, x m ∈ S₂ := by
      intro x hx m hm
      have hmap : S₂.map (x : MulAut W).toMonoidHom ≤ S₂ := by
        rw [hS₂def, commSub, MonoidHom.map_closure]
        refine Subgroup.closure_mono ?_
        rintro _ ⟨_, ⟨y, hy, t, ht, rfl⟩, rfl⟩
        refine ⟨y, hy, x t, hSinv x hx t ht, ?_⟩
        have hyx : y * x = x * y := hXab y (hYX hy) x hx
        have h1 : (y * x) t = (x * y) t := by rw [hyx]
        rw [MulAut.mul_apply, MulAut.mul_apply] at h1
        show y (x t) * (x t)⁻¹ = x (y t * t⁻¹)
        rw [map_mul, map_inv, ← h1]
      exact hmap ⟨m, hm, rfl⟩
    have hS₁S : S₁ ≤ S := inf_le_left
    have hS₂S : S₂ ≤ S := commSub_le_of_invariant hYinv
    have hS₁1 : S₁ ≠ ⊥ := by
      intro h0
      apply hs1
      have : s ∈ S₁ := ⟨hsS, fun y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have hk : ∀ k : ℕ, (η ^ k) s = s := by
          intro k
          induction k with
          | zero => simp
          | succ k ih => rw [pow_succ, MulAut.mul_apply, hηs, ih]
        rcases Int.eq_nat_or_neg k with ⟨j, rfl | rfl⟩
        · rw [zpow_natCast]
          exact hk j
        · rw [zpow_neg, zpow_natCast]
          have h2 := congrArg (fun w => (η ^ j)⁻¹ w) (hk j)
          simp only [MulAut.inv_apply_self] at h2
          exact h2.symm⟩
      rw [h0] at this
      exact this
    have hS₂1 : S₂ ≠ ⊥ := by
      intro h0
      apply hηC
      intro t ht
      have h1 : η t * t⁻¹ ∈ S₂ :=
        Subgroup.subset_closure ⟨η, Subgroup.mem_zpowers η, t, ht, rfl⟩
      rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
    have hcard : Nat.card S₁ * Nat.card S₂ = Nat.card S := by
      have h1 := card_sup_mul_card_inf S₁ S₂
      rw [hdec1, hdec2, Subgroup.card_bot, mul_one] at h1
      exact h1.symm
    have hS₁2 : 2 ≤ Nat.card S₁ := by
      have := Nat.card_pos (α := S₁)
      rcases Nat.lt_or_ge (Nat.card S₁) 2 with h | h
      · exfalso
        exact hS₁1 (Subgroup.eq_bot_of_card_eq _ (by omega))
      · exact h
    have hS₂2 : 2 ≤ Nat.card S₂ := by
      have := Nat.card_pos (α := S₂)
      rcases Nat.lt_or_ge (Nat.card S₂) 2 with h | h
      · exfalso
        exact hS₂1 (Subgroup.eq_bot_of_card_eq _ (by omega))
      · exact h
    have hlt₁ : Nat.card S₁ < N := by
      rw [← h, ← hcard]
      nlinarith
    have hlt₂ : Nat.card S₂ < N := by
      rw [← h, ← hcard]
      nlinarith
    obtain ⟨h₁, -⟩ := ih _ hlt₁ S₁ rfl hS₁inv hS₁1
    obtain ⟨h₂, -⟩ := ih _ hlt₂ S₂ rfl hS₂inv hS₂1
    clear ih
    have hle : (X ⊓ centSub S₁) ⊓ (X ⊓ centSub S₂) ≤ X ⊓ centSub S := by
      rintro x ⟨⟨hxX, hx₁⟩, -, hx₂⟩
      refine ⟨hxX, fun m hm => ?_⟩
      have hm' : m ∈ S₁ ⊔ S₂ := by rw [hdec1]; exact hm
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hm'
      rw [map_mul, hx₁ a ha, hx₂ b hb]
    have hidx : (X ⊓ centSub S).relIndex X ≤
        (X ⊓ centSub S₁).relIndex X * (X ⊓ centSub S₂).relIndex X :=
      (Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite).trans
        (Subgroup.relIndex_inf_le)
    have hprod : (Nat.card S₁ - 1) * (Nat.card S₂ - 1) < Nat.card S - 1 := by
      rw [← hcard]
      obtain ⟨a, ha⟩ : ∃ a, Nat.card S₁ = a + 2 := ⟨Nat.card S₁ - 2, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, Nat.card S₂ = b + 2 := ⟨Nat.card S₂ - 2, by omega⟩
      rw [ha, hb]
      have : (a + 2 - 1) * (b + 2 - 1) = (a + 1) * (b + 1) := rfl
      rw [this]
      have : (a + 2) * (b + 2) - 1 = (a + 1) * (b + 1) + a + b + 2 := by
        ring_nf
        omega
      rw [this]
      omega
    have hfin : (X ⊓ centSub S).relIndex X < Nat.card S - 1 :=
      lt_of_le_of_lt (hidx.trans (Nat.mul_le_mul h₁ h₂)) hprod
    exact ⟨hfin.le, fun heq => absurd heq hfin.ne⟩

theorem relIndex_centSub_le (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hXc : IsCyclic X) (hXo : Odd (Nat.card X)) {S : Subgroup W}
    (hSinv : ∀ x ∈ X, ∀ s ∈ S, x s ∈ S) (hS1 : S ≠ ⊥) :
    (X ⊓ centSub S).relIndex X ≤ Nat.card S - 1 ∧
      ((X ⊓ centSub S).relIndex X = Nat.card S - 1 →
        ∀ s ∈ S, s ≠ 1 → ∀ x ∈ X, x s = s → x ∈ centSub S) :=
  relIndex_centSub_le_aux hW hXc hXo _ S rfl hSinv hS1

omit [Finite W] in
theorem commSub_top_stable {X : Subgroup (MulAut W)} {x : MulAut W} (hx : x ∈ X) {u : W}
    (hu : u ∈ commSub (⊤ : Subgroup W) X) : x u ∈ commSub (⊤ : Subgroup W) X := by
  have hmap : (commSub (⊤ : Subgroup W) X).map x.toMonoidHom ≤ commSub ⊤ X := by
    rw [commSub, MonoidHom.map_closure]
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨_, ⟨y, hy, t, -, rfl⟩, rfl⟩
    have hy' : x * y * x⁻¹ ∈ X := X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
    refine Subgroup.subset_closure ⟨x * y * x⁻¹, hy', x t, Subgroup.mem_top _, ?_⟩
    show (x * y * x⁻¹) (x t) * (x t)⁻¹ = x (y t * t⁻¹)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]
  exact hmap ⟨u, hu, rfl⟩

theorem singer (hW : ∀ w : W, w ^ 2 = 1) {ξ : MulAut W} {n : ℕ} (hn : 2 ≤ n)
    (hξ : orderOf ξ = 2 ^ n - 1) {U : Subgroup W} (hU : U ≤ fixV (Subgroup.zpowers ξ))
    (hUi : U.index = 2 ^ n) :
    fixV (Subgroup.zpowers ξ) = U ∧ Nat.card (commSub ⊤ (Subgroup.zpowers ξ)) = 2 ^ n ∧
      ∀ v ∈ commSub ⊤ (Subgroup.zpowers ξ), v ≠ 1 →
        ∀ x ∈ Subgroup.zpowers ξ, x v = v → x = 1 := by
  classical
  set X := Subgroup.zpowers ξ with hXdef
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hXcard : Nat.card X = 2 ^ n - 1 := by rw [Nat.card_zpowers, hξ]
  have hXo : Odd (Nat.card X) := by
    rw [hXcard]
    have he : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
    exact Nat.Even.sub_odd (by omega) he odd_one
  have hXc : IsCyclic X := inferInstance
  set S := commSub (⊤ : Subgroup W) X with hSdef
  have hSinv : ∀ x ∈ X, ∀ s ∈ S, x s ∈ S := fun x hx s hs => commSub_top_stable hx hs
  obtain ⟨hdec1, hdec2⟩ := B1.coprime_decomp hW hXo (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  rw [top_inf_eq] at hdec1 hdec2
  have hC1 : X ⊓ centSub S = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxS⟩
    rw [Subgroup.mem_bot]
    ext w
    have hw : w ∈ fixV X ⊔ S := by rw [hdec1]; exact Subgroup.mem_top w
    obtain ⟨c, hc, v, hv, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [MulAut.one_apply, map_mul, hc x hxX, hxS v hv]
  have hidx : (X ⊓ centSub S).relIndex X = 2 ^ n - 1 := by
    rw [hC1, Subgroup.relIndex_bot_left, hXcard]
  have hprod : Nat.card (fixV X) * Nat.card S = Nat.card W := by
    have h1 := card_sup_mul_card_inf (fixV X) S
    rw [hdec1, hdec2, Subgroup.card_bot, mul_one, Subgroup.card_top] at h1
    exact h1.symm
  have hUW : Nat.card U * 2 ^ n = Nat.card W := by
    rw [← hUi]
    exact U.card_mul_index
  have hUfix : Nat.card U ≤ Nat.card (fixV X) := Subgroup.card_le_of_le hU
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hSle : Nat.card S ≤ 2 ^ n := by
    by_contra hgt
    push Not at hgt
    have : Nat.card U * 2 ^ n < Nat.card (fixV X) * Nat.card S :=
      Nat.mul_lt_mul_of_le_of_lt hUfix hgt (Nat.card_pos)
    omega
  have hS1 : S ≠ ⊥ := by
    intro h0
    have : X ⊓ centSub S = X := by
      rw [h0]
      exact inf_eq_left.2 fun x _ u hu => by rw [(Subgroup.mem_bot.1 hu), map_one]
    rw [hC1] at this
    have h2 := congrArg (fun H : Subgroup (MulAut W) => Nat.card H) this
    simp only [Subgroup.card_bot] at h2
    omega
  obtain ⟨hle, heq⟩ := relIndex_centSub_le hW hXc hXo hSinv hS1
  rw [hidx] at hle heq
  have hScard : Nat.card S = 2 ^ n := by omega
  have hsemi := heq (by omega)
  refine ⟨?_, hScard, fun v hv hv1 x hx hxv => ?_⟩
  · symm
    apply Subgroup.eq_of_le_of_card_ge hU
    have : Nat.card (fixV X) * 2 ^ n = Nat.card U * 2 ^ n :=
      calc Nat.card (fixV X) * 2 ^ n = Nat.card (fixV X) * Nat.card S := by rw [hScard]
        _ = Nat.card W := hprod
        _ = Nat.card U * 2 ^ n := hUW.symm
    exact (Nat.eq_of_mul_eq_mul_right (by omega) this).le
  · have hxC : x ∈ X ⊓ centSub S := ⟨hx, hsemi v hv hv1 x hx hxv⟩
    rw [hC1] at hxC
    exact Subgroup.mem_bot.1 hxC

end E6

end CFSG.Quasithin
