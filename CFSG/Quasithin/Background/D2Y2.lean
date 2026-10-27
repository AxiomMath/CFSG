module

public import CFSG.Quasithin.Background.D2X2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_order_three_fixed_sub (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} (hU : rk U = 4)
    {Q : Subgroup (MulAut V)} (hQ : Nat.card Q = 9) (hinv : ∀ g ∈ Q, ∀ u ∈ U, g u ∈ U) :
    ∃ q ∈ Q, orderOf q = 3 ∧ ∃ u ∈ U, u ≠ 1 ∧ q u = u := by
  by_contra hcon
  push Not at hcon
  have hfree : ∀ g ∈ Q, ∀ u ∈ {u : V | u ∈ U ∧ u ≠ 1}, g u = u → g = 1 := by
    intro g hg u hu hgu
    by_contra hg1
    have hdvd : orderOf g ∣ 9 := by
      have := orderOf_dvd_natCard (⟨g, hg⟩ : ↥Q)
      rwa [Subgroup.orderOf_mk, hQ] at this
    have h3 : 3 ∣ orderOf g := by
      have hg1' : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
      have hd : orderOf g ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdivs : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hdivs] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h | h
      · exact absurd h hg1'
      · rw [h]
      · rw [h]; norm_num
    have hco : orderOf g ≠ 0 := (orderOf_pos g).ne'
    set q := g ^ (orderOf g / 3) with hq
    have hqo : orderOf q = 3 := orderOf_pow_orderOf_div hco h3
    have hqQ : q ∈ Q := Q.pow_mem hg _
    have hqv : q u = u := by
      have hs : g ∈ MulAction.stabilizer (MulAut V) u := hgu
      exact Subgroup.pow_mem _ hs _
    exact hcon q hqQ hqo u hu.1 hu.2 hqv
  have hΩ : ∀ g ∈ Q, ∀ u ∈ {u : V | u ∈ U ∧ u ≠ 1}, g u ∈ {u : V | u ∈ U ∧ u ≠ 1} := by
    intro g hg u hu
    exact ⟨hinv g hg u hu.1, fun h => hu.2 (g.injective (by rw [h, map_one]))⟩
  have hdvd := card_dvd_card_of_free hΩ hfree
  have hΩcard : Nat.card {u : V | u ∈ U ∧ u ≠ 1} = 15 := by
    have h1 := card_ne_one_add_one U
    have h2 : Nat.card U = 16 := by rw [card_eq_two_pow hV, hU]; norm_num
    have h3 : Nat.card {u : V | u ∈ U ∧ u ≠ 1} = Nat.card {c : V // c ∈ U ∧ c ≠ 1} := rfl
    omega
  rw [hQ, hΩcard] at hdvd
  omega

theorem exists_Xk_of_card_nine (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    {E : Subgroup (MulAut V)} (hEX : E ≤ pCoreOf 3 X) (hE : Nat.card E = 9) {U C : Subgroup V}
    (hd : IsDirectSum ⊤ U C) (hU : rk U = 4) (hEU : ∀ g ∈ E, ∀ u ∈ U, g u ∈ U)
    (hEC : ∀ g ∈ E, ∀ v ∈ C, g v = v) : ∃ Y, Y ∈ Xk X 1 := by
  obtain ⟨q, hqE, hqord, u, huU, hu1, hqu⟩ := exists_order_three_fixed_sub hV hU hE hEU
  have hq1 : q ≠ 1 := by intro h; rw [h, orderOf_one] at hqord; omega
  have hqcard : Nat.card (Subgroup.zpowers q) = 3 := by rw [Nat.card_zpowers, hqord]
  refine ⟨Subgroup.zpowers q, ?_, by rw [hqcard], ?_⟩
  · rw [c.fittingOf_eq hV]; exact Subgroup.zpowers_le.mpr (hEX hqE)
  · have hqz : Subgroup.zpowers q ≤ E := Subgroup.zpowers_le.mpr hqE
    have hUq : ∀ x ∈ Subgroup.zpowers q, ∀ w ∈ U, x w ∈ U := fun x hx w hw => hEU x (hqz hx) w hw
    have hCq : ∀ x ∈ Subgroup.zpowers q, ∀ w ∈ C, x w ∈ C := fun x hx w hw => by
      rw [hEC x (hqz hx) w hw]; exact hw
    have hsum := rk_commSub_isDirectSum (g := q) hd hUq hCq
    have hCbot : commSub C (Subgroup.zpowers q) = ⊥ :=
      commSub_eq_bot_iff.mpr fun w hw x hx => hEC x (hqz hx) w hw
    rw [← commV_eq_commSub, hCbot, rk_bot, add_zero] at hsum
    have h2 := rk_commSub_add_rk_inf_fixV hUq
    have hpos : 1 ≤ rk (U ⊓ fixV (Subgroup.zpowers q) : Subgroup V) := by
      by_contra h0
      have : rk (U ⊓ fixV (Subgroup.zpowers q) : Subgroup V) = 0 := by omega
      have hbot := (rk_eq_zero_iff hV).mp this
      have : u ∈ U ⊓ fixV (Subgroup.zpowers q) := ⟨huU, mem_fixV_zpowers_iff.mpr hqu⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hu1 this
    obtain ⟨-, -, -, hev⟩ := commV_card_three hV hqcard
    have hc1 := one_le_rk_commV_zpowers hV hq1
    obtain ⟨m, hm⟩ := hev
    omega

@[expose] def avg3 (g : MulAut V) : V →* V where
  toFun w := w * g w * g (g w)
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    ac_rfl

omit [Finite V] in
theorem avg3_apply (g : MulAut V) (w : V) : avg3 g w = w * g w * g (g w) := rfl

omit [Finite V] in
theorem apply_cube {g : MulAut V} (hg : g ^ 3 = 1) (w : V) : g (g (g w)) = w := by
  have := congrArg (fun h : MulAut V => h w) hg
  simpa [pow_succ, MulAut.mul_apply] using this

omit [Finite V] in
theorem apply_avg3 {g : MulAut V} (hg : g ^ 3 = 1) (w : V) : g (avg3 g w) = avg3 g w := by
  rw [avg3_apply, map_mul, map_mul, apply_cube hg]
  ac_rfl

omit [Finite V] in
theorem avg3_of_fixed (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} {w : V} (hw : g w = w) :
    avg3 g w = w := by
  rw [avg3_apply, hw, hw, ← pow_two, hV w, one_mul]

omit [Finite V] in
theorem apply_avg3_comm {g h : MulAut V} (hgh : g * h = h * g) (w : V) :
    h (avg3 g w) = avg3 g (h w) := by
  have key : ∀ x, h (g x) = g (h x) := fun x => by
    calc h (g x) = (h * g) x := rfl
      _ = (g * h) x := by rw [hgh]
      _ = g (h x) := rfl
  rw [avg3_apply, avg3_apply, map_mul, map_mul, key, key, key]

omit [Finite V] in
theorem avg3_mem {g : MulAut V} {W : Subgroup V} (hW : ∀ w ∈ W, g w ∈ W) {w : V} (hw : w ∈ W) :
    avg3 g w ∈ W := by
  rw [avg3_apply]
  exact W.mul_mem (W.mul_mem hw (hW w hw)) (hW _ (hW w hw))

omit [Finite V] in
theorem mem_stabSub_of_cube {g : MulAut V} (hg : g ^ 3 = 1) {W : Subgroup V}
    (hW : ∀ w ∈ W, g w ∈ W) : g ∈ stabSub W := by
  intro u
  refine ⟨fun h => ?_, hW u⟩
  have := hW _ (hW _ h)
  rwa [apply_cube hg] at this

omit [Finite V] in
theorem invariant_zpowers_of_cube {g : MulAut V} (hg : g ^ 3 = 1) {W : Subgroup V}
    (hW : ∀ w ∈ W, g w ∈ W) : ∀ x ∈ Subgroup.zpowers g, ∀ w ∈ W, x w ∈ W := by
  intro x hx w hw
  have h1 : Subgroup.zpowers g ≤ stabSub W :=
    Subgroup.zpowers_le.mpr (mem_stabSub_of_cube hg hW)
  exact (mem_stabSub.mp (h1 hx) w).mpr hw

omit [Finite V] in
theorem avg3_kill {g h a b : MulAut V} (hg : g ^ 3 = 1) (hgh : g * h = h * g) {W : Subgroup V}
    (hWg : ∀ w ∈ W, g w ∈ W)
    (hgen : ∀ st : Subgroup (MulAut V), g ∈ st → h ∈ st → a ∈ st ∧ b ∈ st)
    (hfix : ∀ w ∈ W, a w = w → b w = w → w = 1) {x : V} (hx : x ∈ W) (hhx : h x = x) :
    avg3 g x = 1 := by
  have hgy : g ∈ MulAction.stabilizer (MulAut V) (avg3 g x) := apply_avg3 hg x
  have hhy : h ∈ MulAction.stabilizer (MulAut V) (avg3 g x) := by
    show h (avg3 g x) = avg3 g x
    rw [apply_avg3_comm hgh, hhx]
  have hab := hgen _ hgy hhy
  exact hfix _ (avg3_mem hWg hx) hab.1 hab.2

omit [Finite V] in
theorem inf_ker_avg3 (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} {F : Subgroup V}
    (hF : F ≤ fixV (Subgroup.zpowers g)) : F ⊓ (avg3 g).ker = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxF, hxk⟩
  have h1 : g x = x := mem_fixV_zpowers_iff.mp (hF hxF)
  have h2 : avg3 g x = x := avg3_of_fixed hV h1
  have h3 : avg3 g x = 1 := hxk
  rw [h2] at h3
  rw [h3]
  exact Subgroup.one_mem _

omit [Finite V] in
theorem prod_avg3 (hV : ∀ v : V, v ^ 2 = 1) {a b : MulAut V} (hab : a * b = b * a)
    (hb : b ^ 3 = 1) (w : V) :
    avg3 a w * avg3 b w * avg3 (a * b) w * avg3 (a * b * b) w = w * avg3 a (avg3 b w) := by
  have key : ∀ x, b (a x) = a (b x) := fun x => by
    calc b (a x) = (b * a) x := rfl
      _ = (a * b) x := by rw [hab]
      _ = a (b x) := rfl
  have hbbb : ∀ x, b (b (b x)) = x := apply_cube hb
  have hw : w * w = 1 := by rw [← pow_two]; exact hV w
  calc avg3 a w * avg3 b w * avg3 (a * b) w * avg3 (a * b * b) w
      = (w * avg3 a (avg3 b w)) * (w * w) := by
        simp only [avg3_apply, MulAut.mul_apply, map_mul, key, hbbb]
        ac_rfl
    _ = w * avg3 a (avg3 b w) := by rw [hw, mul_one]

omit [Finite V] in
theorem stab_of_pairs {G : Type*} [Group G] {a b : G} (hb3 : b ^ 3 = 1) (st : Subgroup G) :
    (a ∈ st → a * b ∈ st → a ∈ st ∧ b ∈ st) ∧
    (a ∈ st → a * b * b ∈ st → a ∈ st ∧ b ∈ st) ∧
    (b ∈ st → a * b ∈ st → a ∈ st ∧ b ∈ st) ∧
    (b ∈ st → a * b * b ∈ st → a ∈ st ∧ b ∈ st) ∧
    (a * b ∈ st → a * b * b ∈ st → a ∈ st ∧ b ∈ st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ha hab
    refine ⟨ha, ?_⟩
    have : b = a⁻¹ * (a * b) := by group
    rw [this]
    exact st.mul_mem (st.inv_mem ha) hab
  · intro ha habb
    refine ⟨ha, ?_⟩
    have h2 : b * b ∈ st := by
      have : b * b = a⁻¹ * (a * b * b) := by group
      rw [this]
      exact st.mul_mem (st.inv_mem ha) habb
    have hbb : (b * b)⁻¹ = b := by
      apply inv_eq_of_mul_eq_one_left
      rw [← hb3, pow_three]
    rw [← hbb]
    exact st.inv_mem h2
  · intro hb hab
    refine ⟨?_, hb⟩
    have : a = (a * b) * b⁻¹ := by group
    rw [this]
    exact st.mul_mem hab (st.inv_mem hb)
  · intro hb habb
    refine ⟨?_, hb⟩
    have : a = (a * b * b) * b⁻¹ * b⁻¹ := by group
    rw [this]
    exact st.mul_mem (st.mul_mem habb (st.inv_mem hb)) (st.inv_mem hb)
  · intro hab habb
    have hb : b ∈ st := by
      have : b = (a * b)⁻¹ * (a * b * b) := by group
      rw [this]
      exact st.mul_mem (st.inv_mem hab) habb
    refine ⟨?_, hb⟩
    have : a = (a * b) * b⁻¹ := by group
    rw [this]
    exact st.mul_mem hab (st.inv_mem hb)

theorem rk_four_sum {F₁ F₂ F₃ F₄ : Subgroup V} (h12 : F₁ ⊓ F₂ = ⊥) (h123 : (F₁ ⊔ F₂) ⊓ F₃ = ⊥)
    (h1234 : (F₁ ⊔ F₂ ⊔ F₃) ⊓ F₄ = ⊥) :
    rk F₁ + rk F₂ + rk F₃ + rk F₄ = rk (F₁ ⊔ F₂ ⊔ F₃ ⊔ F₄ : Subgroup V) := by
  have e1 := rk_sup_add_rk_inf F₁ F₂
  have e2 := rk_sup_add_rk_inf (F₁ ⊔ F₂) F₃
  have e3 := rk_sup_add_rk_inf (F₁ ⊔ F₂ ⊔ F₃) F₄
  rw [h12, rk_bot] at e1
  rw [h123, rk_bot] at e2
  rw [h1234, rk_bot] at e3
  omega

theorem rk_sum_weights (hV : ∀ v : V, v ^ 2 = 1) {a b : MulAut V} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) {W : Subgroup V} (hWa : ∀ w ∈ W, a w ∈ W)
    (hWb : ∀ w ∈ W, b w ∈ W) (hfix : ∀ w ∈ W, a w = w → b w = w → w = 1) :
    rk (W ⊓ fixV (Subgroup.zpowers a) : Subgroup V) +
      rk (W ⊓ fixV (Subgroup.zpowers b) : Subgroup V) +
      rk (W ⊓ fixV (Subgroup.zpowers (a * b)) : Subgroup V) +
      rk (W ⊓ fixV (Subgroup.zpowers (a * b * b)) : Subgroup V) = rk W := by
  have hc : Commute (a * b) b := Commute.mul_left hab (Commute.refl b)
  have hab3 : (a * b) ^ 3 = 1 := by rw [Commute.mul_pow hab, ha, hb, mul_one]
  have habb3 : (a * b * b) ^ 3 = 1 := by rw [Commute.mul_pow hc, hab3, hb, mul_one]
  have hWab : ∀ w ∈ W, (a * b) w ∈ W := fun w hw => hWa _ (hWb w hw)
  have hWabb : ∀ w ∈ W, (a * b * b) w ∈ W := fun w hw => hWab _ (hWb w hw)
  have cab : Commute a b := hab
  have ca_ab : Commute a (a * b) := Commute.mul_right (Commute.refl a) cab
  have cb_ab : Commute b (a * b) := Commute.mul_right cab.symm (Commute.refl b)
  have ca_abb : Commute a (a * b * b) := Commute.mul_right ca_ab cab
  have cb_abb : Commute b (a * b * b) := Commute.mul_right cb_ab (Commute.refl b)
  have cab_abb : Commute (a * b) (a * b * b) := Commute.mul_right (Commute.refl (a * b)) hc
  have P := stab_of_pairs (a := a) (b := b) hb
  have m1 : ∀ w ∈ W, avg3 a w ∈ W ⊓ fixV (Subgroup.zpowers a) := fun w hw =>
    ⟨avg3_mem hWa hw, mem_fixV_zpowers_iff.mpr (apply_avg3 ha w)⟩
  have m2 : ∀ w ∈ W, avg3 b w ∈ W ⊓ fixV (Subgroup.zpowers b) := fun w hw =>
    ⟨avg3_mem hWb hw, mem_fixV_zpowers_iff.mpr (apply_avg3 hb w)⟩
  have m3 : ∀ w ∈ W, avg3 (a * b) w ∈ W ⊓ fixV (Subgroup.zpowers (a * b)) := fun w hw =>
    ⟨avg3_mem hWab hw, mem_fixV_zpowers_iff.mpr (apply_avg3 hab3 w)⟩
  have m4 : ∀ w ∈ W, avg3 (a * b * b) w ∈ W ⊓ fixV (Subgroup.zpowers (a * b * b)) :=
    fun w hw => ⟨avg3_mem hWabb hw, mem_fixV_zpowers_iff.mpr (apply_avg3 habb3 w)⟩
  have hsum : (W ⊓ fixV (Subgroup.zpowers a) : Subgroup V) ⊔
      (W ⊓ fixV (Subgroup.zpowers b) : Subgroup V) ⊔
      (W ⊓ fixV (Subgroup.zpowers (a * b)) : Subgroup V) ⊔
      (W ⊓ fixV (Subgroup.zpowers (a * b * b)) : Subgroup V) = W := by
    refine le_antisymm (sup_le (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
      inf_le_left) fun w hw => ?_
    have hN : avg3 a (avg3 b w) = 1 := by
      refine hfix _ (avg3_mem hWa (avg3_mem hWb hw)) (apply_avg3 ha _) ?_
      rw [apply_avg3_comm hab, apply_avg3 hb]
    have hprod := prod_avg3 hV hab hb w
    rw [hN, mul_one] at hprod
    rw [← hprod]
    exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup (Subgroup.mul_mem_sup (m1 w hw) (m2 w hw))
      (m3 w hw)) (m4 w hw)
  have k21 : (W ⊓ fixV (Subgroup.zpowers a) : Subgroup V) ≤ (avg3 b).ker := fun x hx =>
    avg3_kill hb hab.symm hWb (fun st hb' ha' => ⟨ha', hb'⟩) hfix hx.1
      (mem_fixV_zpowers_iff.mp hx.2)
  have k31 : (W ⊓ fixV (Subgroup.zpowers a) : Subgroup V) ≤ (avg3 (a * b)).ker := fun x hx =>
    avg3_kill hab3 ca_ab.symm.eq hWab (fun st h1 h2 => (P st).1 h2 h1) hfix hx.1
      (mem_fixV_zpowers_iff.mp hx.2)
  have k32 : (W ⊓ fixV (Subgroup.zpowers b) : Subgroup V) ≤ (avg3 (a * b)).ker := fun x hx =>
    avg3_kill hab3 cb_ab.symm.eq hWab (fun st h1 h2 => (P st).2.2.1 h2 h1) hfix hx.1
      (mem_fixV_zpowers_iff.mp hx.2)
  have k41 : (W ⊓ fixV (Subgroup.zpowers a) : Subgroup V) ≤ (avg3 (a * b * b)).ker := fun x hx =>
    avg3_kill habb3 ca_abb.symm.eq hWabb (fun st h1 h2 => (P st).2.1 h2 h1) hfix hx.1
      (mem_fixV_zpowers_iff.mp hx.2)
  have k42 : (W ⊓ fixV (Subgroup.zpowers b) : Subgroup V) ≤ (avg3 (a * b * b)).ker := fun x hx =>
    avg3_kill habb3 cb_abb.symm.eq hWabb (fun st h1 h2 => (P st).2.2.2.1 h2 h1) hfix hx.1
      (mem_fixV_zpowers_iff.mp hx.2)
  have k43 : (W ⊓ fixV (Subgroup.zpowers (a * b)) : Subgroup V) ≤ (avg3 (a * b * b)).ker :=
    fun x hx => avg3_kill habb3 cab_abb.symm.eq hWabb (fun st h1 h2 => (P st).2.2.2.2 h2 h1) hfix
      hx.1 (mem_fixV_zpowers_iff.mp hx.2)
  have h12 : (W ⊓ fixV (Subgroup.zpowers a) : Subgroup V) ⊓
      (W ⊓ fixV (Subgroup.zpowers b) : Subgroup V) = ⊥ := by
    have := inf_ker_avg3 hV (g := b) (F := W ⊓ fixV (Subgroup.zpowers b)) inf_le_right
    rw [eq_bot_iff] at this ⊢
    exact fun x hx => this ⟨hx.2, k21 hx.1⟩
  have h123 : ((W ⊓ fixV (Subgroup.zpowers a) : Subgroup V) ⊔
      (W ⊓ fixV (Subgroup.zpowers b) : Subgroup V)) ⊓
      (W ⊓ fixV (Subgroup.zpowers (a * b)) : Subgroup V) = ⊥ := by
    have := inf_ker_avg3 hV (g := a * b) (F := W ⊓ fixV (Subgroup.zpowers (a * b))) inf_le_right
    rw [eq_bot_iff] at this ⊢
    exact fun x hx => this ⟨hx.2, sup_le k31 k32 hx.1⟩
  have h1234 : ((W ⊓ fixV (Subgroup.zpowers a) : Subgroup V) ⊔
      (W ⊓ fixV (Subgroup.zpowers b) : Subgroup V) ⊔
      (W ⊓ fixV (Subgroup.zpowers (a * b)) : Subgroup V)) ⊓
      (W ⊓ fixV (Subgroup.zpowers (a * b * b)) : Subgroup V) = ⊥ := by
    have := inf_ker_avg3 hV (g := a * b * b)
      (F := W ⊓ fixV (Subgroup.zpowers (a * b * b))) inf_le_right
    rw [eq_bot_iff] at this ⊢
    exact fun x hx => this ⟨hx.2, sup_le (sup_le k41 k42) k43 hx.1⟩
  have := rk_four_sum h12 h123 h1234
  rwa [hsum] at this

theorem commV_eq_commSub_commV {P S : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (hP : Odd (Nat.card P)) (hS : S ≤ P) : commV S = commSub (commV P) S := by
  apply le_antisymm
  · have hdec := (coprime_decomp hP hV (W := ⊤) (fun g _ w _ => Subgroup.mem_top _)).1
    rw [commV_eq_commSub S, commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, -, rfl⟩
    have hv : v ∈ commSub ⊤ P ⊔ (⊤ ⊓ fixV P) := by
      rw [hdec]
      exact Subgroup.mem_top v
    obtain ⟨c, hc, f, hf, rfl⟩ := Subgroup.mem_sup.mp hv
    have hfx : x f = f := hf.2 x (hS hx)
    have hc' : c ∈ commV P := by rwa [commV_eq_commSub P]
    have : x (c * f) * (c * f)⁻¹ = x c * c⁻¹ := by
      rw [map_mul, hfx, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    rw [this]
    exact Subgroup.subset_closure ⟨x, hx, c, hc', rfl⟩
  · rw [commV_eq_commSub S]
    exact commSub_mono le_top le_rfl

theorem rk_commV_add_rk_inf_fixV {P : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (hP : Odd (Nat.card P)) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {g : MulAut V}
    (hg : g ∈ P) :
    rk (commV (Subgroup.zpowers g)) + rk (commV P ⊓ fixV (Subgroup.zpowers g) : Subgroup V) =
      rk (commV P) := by
  have hinv : ∀ x ∈ Subgroup.zpowers g, ∀ w ∈ commV P, x w ∈ commV P := by
    intro x hx w hw
    have hxP : x ∈ P := Subgroup.zpowers_le.mpr hg hx
    refine commV_smul_mem (fun p hp => ?_) hw
    rw [hcomm x hxP p hp, mul_inv_cancel_right]
    exact hp
  rw [commV_eq_commSub_commV hV hP (Subgroup.zpowers_le.mpr hg)]
  exact rk_commSub_add_rk_inf_fixV hinv

theorem rk_commV_sum_E9 (hV : ∀ v : V, v ^ 2 = 1) {a b : MulAut V} (ha : orderOf a = 3)
    (hb : orderOf b = 3) (hab : a * b = b * a) (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b) :
    rk (commV (Subgroup.zpowers a)) + rk (commV (Subgroup.zpowers b)) +
      rk (commV (Subgroup.zpowers (a * b))) + rk (commV (Subgroup.zpowers (a * b * b))) =
        3 * rk (commV (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) := by
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  obtain ⟨E, hE⟩ : ∃ E, E = Subgroup.zpowers a ⊔ Subgroup.zpowers b := ⟨_, rfl⟩
  rw [← hE]
  have hcard_a : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha]
  have hcard_b : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb]
  have hcomm_ab : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hab) m n).eq
  obtain ⟨hEcard, -⟩ := sup_structure hcard_a hcard_b hne hcomm_ab
  have hEodd : Odd (Nat.card E) := by rw [hE, hEcard]; exact ⟨4, rfl⟩
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rw [hE]
    exact sup_comm_elements hcard_a hcard_b hne hcomm_ab
  have haE : a ∈ E := by rw [hE]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hbE : b ∈ E := by rw [hE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have habE : a * b ∈ E := E.mul_mem haE hbE
  have habbE : a * b * b ∈ E := E.mul_mem habE hbE
  have hWinv : ∀ g ∈ E, ∀ w ∈ commV E, g w ∈ commV E := fun g hg w hw =>
    commV_smul_mem (fun p hp => by
      rw [hEcomm g hg p hp, mul_inv_cancel_right]
      exact hp) hw
  have hfix : ∀ w ∈ commV E, a w = w → b w = w → w = 1 := by
    intro w hw haw hbw
    have hwF : w ∈ fixV E := by
      have hle : E ≤ MulAction.stabilizer (MulAut V) w := by
        rw [hE]
        exact sup_le (Subgroup.zpowers_le.mpr haw) (Subgroup.zpowers_le.mpr hbw)
      exact fun x hx => hle hx
    have hdec := (coprime_decomp hEodd hV (W := ⊤) (fun g _ w _ => Subgroup.mem_top _)).2
    rw [← commV_eq_commSub, top_inf_eq] at hdec
    have hmem : w ∈ commV E ⊓ fixV E := ⟨hw, hwF⟩
    rw [hdec] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hW := rk_sum_weights hV hab ha3 hb3 (W := commV E) (hWinv a haE) (hWinv b hbE) hfix
  have e1 := rk_commV_add_rk_inf_fixV hV hEodd hEcomm haE
  have e2 := rk_commV_add_rk_inf_fixV hV hEodd hEcomm hbE
  have e3 := rk_commV_add_rk_inf_fixV hV hEodd hEcomm habE
  have e4 := rk_commV_add_rk_inf_fixV hV hEodd hEcomm habbE
  omega

end CFSG.Quasithin
