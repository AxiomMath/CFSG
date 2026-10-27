module

public import CFSG.Quasithin.Background.D2Y5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem eq_of_mem_zpowers_cube {G : Type*} [Group G] {z w : G} (hz3 : z ^ 3 = 1)
    (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z ∨ w = z⁻¹ := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h3 : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
  have hred : z ^ m = z ^ (m % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv m 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have hz2 : z ^ (2 : ℤ) = z⁻¹ := by
    calc z ^ (2 : ℤ) = z ^ (3 : ℤ) * z⁻¹ := by
          rw [← zpow_neg_one, ← zpow_add]; norm_num
      _ = z⁻¹ := by rw [h3, one_mul]
  rw [hred]
  have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases this with h | h | h
  · left; rw [h, zpow_zero]
  · right; left; rw [h, zpow_one]
  · right; right; rw [h, hz2]

omit [Finite V] in
theorem E9_orders {a b : MulAut V} (hao : orderOf a = 3) (hbo : orderOf b = 3)
    (hab : a * b = b * a) (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b) :
    orderOf (a * b) = 3 ∧ orderOf (a * b * b) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have ha3 : a ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  have hcab : Commute a b := hab
  have hab3 : (a * b) ^ 3 = 1 := by rw [hcab.mul_pow, ha3, hb3, mul_one]
  have hc : Commute (a * b) b := Commute.mul_left hcab (Commute.refl b)
  have habb3 : (a * b * b) ^ 3 = 1 := by rw [hc.mul_pow, hab3, hb3, mul_one]
  have hab1 : a * b ≠ 1 := by
    intro e
    apply hne
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [this, Subgroup.zpowers_inv]
  have habb1 : a * b * b ≠ 1 := by
    intro e
    apply hne
    have : a = b := by
      calc a = a * b ^ 3 := by rw [hb3, mul_one]
        _ = (a * b * b) * b := by rw [pow_three']; simp only [mul_assoc]
        _ = b := by rw [e, one_mul]
    rw [this]
  exact ⟨orderOf_eq_prime hab3 hab1, orderOf_eq_prime habb3 habb1⟩

section Basic

variable {X : Subgroup (MulAut V)}

theorem exists_EData (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {t x : MulAut V} (h : InvPair X t x)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) : ∃ y, EData X t x y := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Y, hY, hYP, hYne⟩ := exists_second_inverted hV c hX1 h htwo
  obtain ⟨y, t', hp, hz, hyo, -⟩ := Yinv_data hV c hX1 hY
  have hyY : y ∈ Y := hz ▸ Subgroup.mem_zpowers y
  have hxo := (inverted_data hV c hX1 h.ht h.hx h.hx1 h.hinv).1
  refine ⟨y, ⟨h, hYP hyY, ?_, ?_, by rw [hz]; exact hY⟩⟩
  · rw [← hyo]
    exact pow_orderOf_eq_one y
  · intro hyx
    apply hYne
    rw [← hz]
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyx) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hyo]

omit [Finite V] in
theorem commV_le_fixV_of_inf_bot {x y : MulAut V} (hxy : x * y = y * x)
    (hbot : commV (Subgroup.zpowers x) ⊓ commV (Subgroup.zpowers y) = ⊥) :
    commV (Subgroup.zpowers y) ≤ fixV (Subgroup.zpowers x) := by
  intro w hw g hg
  have hcom : ∀ g ∈ Subgroup.zpowers x, ∀ y' ∈ Subgroup.zpowers y, g * y' = y' * g := by
    intro g hg y' hy'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact ((show Commute x y from hxy).zpow_zpow m n).eq
  have hgw : g w ∈ commV (Subgroup.zpowers y) :=
    commV_smul_mem (fun p hp => by
      rw [hcom g hg p hp, mul_inv_cancel_right]
      exact hp) hw
  have hmem : g w * w⁻¹ ∈ commV (Subgroup.zpowers x) :=
    Subgroup.subset_closure ⟨g, hg, w, rfl⟩
  have hboth : g w * w⁻¹ ∈ commV (Subgroup.zpowers x) ⊓ commV (Subgroup.zpowers y) :=
    ⟨hmem, (commV (Subgroup.zpowers y)).mul_mem hgw ((commV (Subgroup.zpowers y)).inv_mem hw)⟩
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hboth
  exact hboth

theorem inverter_kind (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {t x : MulAut V} (h : InvPair X t x) {V₂ : Subgroup V}
    (hd : IsDirectSum ⊤ (commV (Subgroup.zpowers x)) V₂) (hV₂ : V₂ ≤ fixV (Subgroup.zpowers x)) :
    Subgroup.zpowers t ≤ centSub V₂ ∧
      commV (Subgroup.zpowers t) ≤ commV (Subgroup.zpowers x) := by
  have hfix := (inverted_data hV c hX1 h.ht h.hx h.hx1 h.hinv).2.2.1
  have hcen : Subgroup.zpowers t ≤ centSub V₂ := by
    intro g hg w hw
    have hs : Subgroup.zpowers t ≤ MulAction.stabilizer (MulAut V) w :=
      Subgroup.zpowers_le.mpr (hfix w (hV₂ hw))
    exact hs hg
  refine ⟨hcen, ?_⟩
  have hnorm : ∀ g ∈ Subgroup.zpowers t, ∀ p ∈ Subgroup.zpowers x,
      g * p * g⁻¹ ∈ Subgroup.zpowers x := by
    intro g hg p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases zpow_involution h.ht.2.2.1 k with e | e
    · rw [e]
      simpa using hp
    · rw [e]
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      rw [← conj_zpow, h.hinv, inv_zpow]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) m)
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  have hv : v ∈ commV (Subgroup.zpowers x) ⊔ V₂ := by
    rw [hd.1]
    exact Subgroup.mem_top v
  obtain ⟨w, hw, u, hu, rfl⟩ := Subgroup.mem_sup.mp hv
  have hgu : g u = u := hcen hg u hu
  have hgw : g w ∈ commV (Subgroup.zpowers x) := commV_smul_mem (hnorm g hg) hw
  have : g (w * u) * (w * u)⁻¹ = g w * w⁻¹ := by
    rw [map_mul, hgu, mul_inv_rev]
    calc g w * u * (u⁻¹ * w⁻¹) = (g w * w⁻¹) * (u * u⁻¹) := by ac_rfl
      _ = g w * w⁻¹ := by rw [mul_inv_cancel, mul_one]
  rw [this]
  exact (commV (Subgroup.zpowers x)).mul_mem hgw ((commV (Subgroup.zpowers x)).inv_mem hw)

theorem commute_of_conjBy_eq {A : Subgroup (MulAut V)} (hA : Nat.card A = 3) {g : MulAut V}
    (hodd : Odd (orderOf g)) (h : conjBy g A = A) : ∀ a ∈ A, g * a = a * g := by
  refine commute_of_normalizes_three_odd hA hodd (fun a ha => ?_) (fun a ha => ?_)
  · have := mem_conjBy_of_mem (g := g) ha
    rwa [h] at this
  · have h1 : a ∈ conjBy g A := by rw [h]; exact ha
    exact mem_conjBy_iff.mp h1

omit [Finite V] in
theorem mem_of_sq_mem {H : Subgroup (MulAut V)} {g : MulAut V} (hodd : Odd (orderOf g))
    (hg : g * g ∈ H) : g ∈ H := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
  have h2 : g = (g * g) ^ (k + 1) := by
    calc g = g * g ^ (2 * k + 1) := by rw [h1, mul_one]
      _ = g ^ (2 * k + 1 + 1) := (pow_succ' g (2 * k + 1)).symm
      _ = (g * g) ^ (k + 1) := by rw [← pow_two, ← pow_mul]; ring_nf
  rw [h2]
  exact H.pow_mem hg _

omit [Finite V] in
theorem false_of_commV_le_bot {s : MulAut V} [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hs1 : s ≠ 1)
    (hle : commV (Subgroup.zpowers s) ≤ ⊥) : False := by
  have h1 := one_le_rk_commV_zpowers hV hs1
  have h2 := rk_mono hle
  rw [rk_bot] at h2
  omega

theorem pattern8_false (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {t x y : MulAut V} (d : EData X t x y)
    (h8 : rk (commV (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) = 8)
    (h8ab : rk (commV (Subgroup.zpowers (x * y))) = 8)
    (h8abb : rk (commV (Subgroup.zpowers (x * y * y))) = 8) : False := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hxo := d.orderOf_x hV c hX1
  have hyo := d.orderOf_y
  have hrkx := d.rk_x hV c hX1
  have hrky := d.rk_y hV c hX1
  have hxc : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
  obtain ⟨hEcard, hEcomm, hform⟩ := E9_data hxo hyo d.comm d.hne
  have hEodd : Odd (Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup (MulAut V))) := by
    rw [hEcard]; exact ⟨4, rfl⟩
  have hxE : x ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyE : y ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hrank4 : ∀ w ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, w ≠ 1 →
      rk (commV (Subgroup.zpowers w)) = 4 →
      Subgroup.zpowers w = Subgroup.zpowers x ∨ Subgroup.zpowers w = Subgroup.zpowers y := by
    intro w hw hw1 hr
    rcases sub_E_cases hxo hyo d.comm d.hne hw hw1 with e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exfalso; rw [e] at hr; omega
    · exfalso; rw [e] at hr; omega
  have hRP : centR X x = pCoreOf 3 X := by
    by_contra hne
    obtain ⟨g, hgR, hgN, hgP⟩ := exists_mem_normalizer_of_ne (pCoreOf_isPGroup 3 X)
      (inf_le_left : centR X x ≤ pCoreOf 3 X) hne
    have hg : ∀ p ∈ centR X x, g * p * g⁻¹ ∈ centR X x := fun p hp =>
      (Subgroup.mem_normalizer_iff.mp hgN p).mp hp
    have hodd : Odd (orderOf g) := odd_orderOf_of_mem_pCoreOf hgR
    have hx' := conj_mem_E hV c hX1 d hg hxE
    have hy' := conj_mem_E hV c hX1 d hg hyE
    have hx'1 : g * x * g⁻¹ ≠ 1 := by
      intro e
      apply d.h.hx1
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, e]
      group
    have hy'1 : g * y * g⁻¹ ≠ 1 := by
      intro e
      apply d.hy1
      have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [this, e]
      group
    have hr1 : rk (commV (Subgroup.zpowers (g * x * g⁻¹))) = 4 := by
      rw [rk_commV_zpowers_conj]; exact hrkx
    have hr2 : rk (commV (Subgroup.zpowers (g * y * g⁻¹))) = 4 := by
      rw [rk_commV_zpowers_conj]; exact hrky
    rcases hrank4 _ hx' hx'1 hr1 with e1 | e1
    · have hn : conjBy g (Subgroup.zpowers x) = Subgroup.zpowers x := by
        rw [← zpowers_conj]; exact e1
      have hcomm := commute_of_conjBy_eq hxc hodd hn
      exact hgP (mem_centR.mpr ⟨hgR, hcomm x (Subgroup.mem_zpowers x)⟩)
    · rcases hrank4 _ hy' hy'1 hr2 with e2 | e2
      · have hn : conjBy (g * g) (Subgroup.zpowers x) = Subgroup.zpowers x := by
          rw [← conjBy_conjBy, ← zpowers_conj, e1, ← zpowers_conj, e2]
        have hodd2 : Odd (orderOf (g * g)) :=
          odd_orderOf_of_mem_pCoreOf ((pCoreOf 3 X).mul_mem hgR hgR)
        have hcomm := commute_of_conjBy_eq hxc hodd2 hn
        exact hgP (mem_of_sq_mem hodd
          (mem_centR.mpr ⟨(pCoreOf 3 X).mul_mem hgR hgR, hcomm x (Subgroup.mem_zpowers x)⟩))
      · exfalso
        apply d.hne
        apply conjBy_injective g
        rw [← zpowers_conj, ← zpowers_conj, e1, e2]
  have hYinv : ∀ Y ∈ Yinv X, Y = Subgroup.zpowers x ∨ Y = Subgroup.zpowers y := by
    intro Y hY
    obtain ⟨η, t', hp, hz, hηo, hηr⟩ := Yinv_data hV c hX1 hY
    have hηP : η ∈ centR X x := by rw [hRP]; exact hp.hx
    have hη3 : η ^ 3 = 1 := by rw [← hηo]; exact pow_orderOf_eq_one η
    have hηE := mem_E_of_cube hV c hX1 d.h d.hy d.hy3 d.hyx hηP hη3
    rcases hrank4 η hηE hp.hx1 (by rw [hz]; exact hηr) with e | e
    · left; rw [← hz]; exact e
    · right; rw [← hz]; exact e
  have hfixE : fixV (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = ⊥ := by
    refine eq_bot_of_le_fixV_inverted hV c hX1 (fun x' hx' hx'1 ⟨t', ht', hinv'⟩ => ?_)
    have hY : Subgroup.zpowers x' ∈ Yinv X := zpowers_mem_Yinv hV ht' hx' hx'1 hinv'
    rcases hYinv _ hY with e | e
    · exact fixV_anti (by rw [e]; exact le_sup_left)
    · exact fixV_anti (by rw [e]; exact le_sup_right)
  obtain ⟨hdec1, -⟩ :=
    coprime_decomp hEodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, top_inf_eq, hfixE, sup_bot_eq] at hdec1
  have hrkV : rk V = 8 := by rw [← rk_top, ← hdec1]; exact h8
  rw [commV_sup] at hdec1
  have hbot : commV (Subgroup.zpowers x) ⊓ commV (Subgroup.zpowers y) = ⊥ := by
    have h1 := rk_sup_add_rk_inf (commV (Subgroup.zpowers x)) (commV (Subgroup.zpowers y))
    rw [hdec1, rk_top, hrkx, hrky, hrkV] at h1
    exact (rk_eq_zero_iff hV).mp (by omega)
  have hd : IsDirectSum ⊤ (commV (Subgroup.zpowers x)) (commV (Subgroup.zpowers y)) :=
    ⟨hdec1, hbot⟩
  have hd' : IsDirectSum ⊤ (commV (Subgroup.zpowers y)) (commV (Subgroup.zpowers x)) :=
    ⟨by rw [sup_comm]; exact hdec1, by rw [inf_comm]; exact hbot⟩
  have hfix_y : commV (Subgroup.zpowers y) ≤ fixV (Subgroup.zpowers x) :=
    commV_le_fixV_of_inf_bot d.comm hbot
  have hfix_x : commV (Subgroup.zpowers x) ≤ fixV (Subgroup.zpowers y) :=
    commV_le_fixV_of_inf_bot d.comm.symm (by rw [inf_comm]; exact hbot)
  have hcases : ∀ B ∈ QhatStar X,
      (B ≤ centSub (commV (Subgroup.zpowers y)) ∧ commV B ≤ commV (Subgroup.zpowers x)) ∨
      (B ≤ centSub (commV (Subgroup.zpowers x)) ∧ commV B ≤ commV (Subgroup.zpowers y)) := by
    intro B hB
    obtain ⟨t', ht', rfl⟩ := c.exists_tinv hB
    obtain ⟨x', hx'R, hx'1, hinv'⟩ := exists_inverted hV c ht'
    have hp : InvPair X t' x' := ⟨ht', hx'R, hx'1, hinv'⟩
    rcases hYinv _ (zpowers_mem_Yinv hV ht' hx'R hx'1 hinv') with e | e
    · left
      have := inverter_kind hV c hX1 hp (V₂ := commV (Subgroup.zpowers y))
        (by rw [e]; exact hd) (by rw [e]; exact hfix_y)
      rw [e] at this
      exact this
    · right
      have := inverter_kind hV c hX1 hp (V₂ := commV (Subgroup.zpowers x))
        (by rw [e]; exact hd') (by rw [e]; exact hfix_x)
      rw [e] at this
      exact this
  have hfirst := inverter_kind hV c hX1 d.h hd hfix_y
  obtain ⟨y', t₁, hp₁, hz₁, -, -⟩ := Yinv_data hV c hX1 d.hY
  have hsecond := inverter_kind hV c hX1 hp₁ (V₂ := commV (Subgroup.zpowers x))
    (by rw [hz₁]; exact hd') (by rw [hz₁]; exact hfix_x)
  rw [hz₁] at hsecond
  rcases qhatStar_cases_of_indecomposable c.hyp.indecomposable hd hcases with hall | hall
  · have := (hall _ (c.zpowers_mem_qhatStar hV hp₁.ht)).2
    exact false_of_commV_le_bot hV hp₁.ht.2.1
      (le_trans (le_inf this hsecond.2) (by rw [hbot]))
  · have := (hall _ (c.zpowers_mem_qhatStar hV d.h.ht)).2
    exact false_of_commV_le_bot hV d.h.ht.2.1
      (le_trans (le_inf hfirst.2 this) (by rw [hbot]))

end Basic

end CFSG.Quasithin
