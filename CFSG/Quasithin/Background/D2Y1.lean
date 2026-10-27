module

public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def Yinv (X : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {Y | Y ≤ pCoreOf 3 X ∧ Nat.card Y = 3 ∧ ∃ t ∈ TInv X, ∀ y ∈ Y, t * y * t⁻¹ = y⁻¹}

section Basic

variable {X : Subgroup (MulAut V)}

theorem zpowers_mem_Yinv (hV : ∀ v : V, v ^ 2 = 1) {t x : MulAut V} (ht : t ∈ TInv X)
    (hx : x ∈ pCoreOf 3 X) (hx1 : x ≠ 1) (hinv : t * x * t⁻¹ = x⁻¹) :
    Subgroup.zpowers x ∈ Yinv X := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord := (inverted_elem hV ht (p := 3) (by norm_num) (pCoreOf_le 3 X)
    (pCoreOf_isPGroup 3 X) hx hx1 hinv).1
  refine ⟨Subgroup.zpowers_le.mpr hx, by rw [Nat.card_zpowers, hord], t, ht, ?_⟩
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow, hinv, inv_zpow]

theorem Yinv_conj {Y : Subgroup (MulAut V)} (hY : Y ∈ Yinv X) {g : MulAut V} (hg : g ∈ X) :
    conjBy g Y ∈ Yinv X := by
  obtain ⟨hYR, hcard, t, ht, hinv⟩ := hY
  refine ⟨?_, by rw [card_conjBy, hcard], g * t * g⁻¹, conj_mem_TInv ht hg, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hg) y).mp (hYR hy)
    simpa [MulAut.conj_apply] using this
  · intro y' hy'
    have hy := mem_conjBy_iff.mp hy'
    have e : y' = g * (g⁻¹ * y' * g) * g⁻¹ := by group
    rw [e]
    calc g * t * g⁻¹ * (g * (g⁻¹ * y' * g) * g⁻¹) * (g * t * g⁻¹)⁻¹
        = g * (t * (g⁻¹ * y' * g) * t⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * y' * g)⁻¹ * g⁻¹ := by rw [hinv _ hy]
      _ = (g * (g⁻¹ * y' * g) * g⁻¹)⁻¹ := by group

theorem nonempty_mulEquiv_dihedral_of_subgroup {G : Type*} [Group G] {X : Subgroup G} {d t : G}
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hdX : d ∈ X) (htX : t ∈ X) (hd : orderOf d = p)
    (ht : orderOf t = 2) (hinv : t * d * t⁻¹ = d⁻¹)
    (hgen : ∀ g ∈ X, g ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers t) :
    Nonempty (↥X ≃* DihedralGroup p) := by
  have hd' : orderOf (⟨d, hdX⟩ : ↥X) = p := by rw [Subgroup.orderOf_mk, hd]
  have ht' : orderOf (⟨t, htX⟩ : ↥X) = 2 := by rw [Subgroup.orderOf_mk, ht]
  have hinv' : (⟨t, htX⟩ : ↥X) * ⟨d, hdX⟩ * (⟨t, htX⟩ : ↥X)⁻¹ = (⟨d, hdX⟩ : ↥X)⁻¹ :=
    Subtype.ext hinv
  refine nonempty_mulEquiv_dihedral hp hd' ht' hinv' fun g => ?_
  have hmap : (Subgroup.zpowers (⟨d, hdX⟩ : ↥X) ⊔ Subgroup.zpowers (⟨t, htX⟩ : ↥X)).map
      X.subtype = Subgroup.zpowers d ⊔ Subgroup.zpowers t := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hgmem : (g : G) ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers t := hgen g g.2
  rw [← hmap] at hgmem
  exact (Subgroup.mem_map_iff_mem X.subtype_injective).mp hgmem

end Basic

section Y1

variable {X : Subgroup (MulAut V)}

theorem inverted_data (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {t x : MulAut V} (ht : t ∈ TInv X) (hx : x ∈ pCoreOf 3 X) (hx1 : x ≠ 1)
    (hinv : t * x * t⁻¹ = x⁻¹) :
    orderOf x = 3 ∧ rk (commV (Subgroup.zpowers x)) = 4 ∧
      (∀ w ∈ fixV (Subgroup.zpowers x), t w = w) ∧
      (∀ y ∈ X, y * x = x * y → (∀ u ∈ commV (Subgroup.zpowers x), y u = u) → y * t = t * y) ∧
      commSub (commV (Subgroup.zpowers x)) (Subgroup.zpowers t) = commV (Subgroup.zpowers t) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord := (inverted_elem hV ht (p := 3) (by norm_num) (pCoreOf_le 3 X)
    (pCoreOf_isPGroup 3 X) hx hx1 hinv).1
  have hodd : Odd (orderOf x) := by rw [hord]; exact ⟨1, rfl⟩
  have hxX := pCoreOf_le 3 X hx
  have hrkt := c.rk_eq_two hV ht
  obtain ⟨-, -, h3⟩ := d2_11_core hV ht.2.2.1 ht.2.2.2 hx1 hodd hinv
  have hrk4 : rk (commV (Subgroup.zpowers x)) = 4 := by
    rcases h3 with ⟨hr2, -⟩ | ⟨hr4, -⟩
    · exfalso
      apply hX1 (Subgroup.zpowers x)
      refine ⟨?_, ?_, ?_⟩
      · rw [c.fittingOf_eq hV]; exact Subgroup.zpowers_le.mpr hx
      · rw [Nat.card_zpowers, hord]
      · rw [hr2]
    · exact hr4
  have h3' := D2_11_3 hV ht hxX hx1 hodd hinv (by rw [hrk4, hrkt])
  refine ⟨hord, hrk4, ?_, ?_, h3'.1⟩
  · intro w hw
    exact mem_fixV_zpowers_iff.mp (commSub_eq_bot_iff.mp h3'.2.1 hw)
  · intro y hyX hyx hyU
    exact h3'.2.2 y hyX (Subgroup.mem_centralizer_singleton_iff.mpr hyx) hyU

theorem exists_inverted (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) {t : MulAut V}
    (ht : t ∈ TInv X) : ∃ x ∈ pCoreOf 3 X, x ≠ 1 ∧ t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨y, hy, hne⟩ := c.faithful_three hV ht
  refine ⟨y⁻¹ * (t * y * t⁻¹), ?_, ne_one_of_not_commute hne,
    inv_conj_of_involution y ht.2.2.1⟩
  exact (pCoreOf 3 X).mul_mem ((pCoreOf 3 X).inv_mem hy)
    ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X ht.1) y).mp hy)

theorem eq_bot_of_le_fixV_inverted (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) {W : Subgroup V}
    (hW : ∀ x ∈ pCoreOf 3 X, x ≠ 1 → (∃ t ∈ TInv X, t * x * t⁻¹ = x⁻¹) →
      W ≤ fixV (Subgroup.zpowers x)) : W = ⊥ := by
  refine c.fixV_T hV fun t ht w hw => ?_
  obtain ⟨x, hx, hx1, hinv⟩ := exists_inverted hV c ht
  exact (inverted_data hV c hX1 ht hx hx1 hinv).2.2.1 w (hW x hx hx1 ⟨t, ht, hinv⟩ hw)

theorem D2_27_rank (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {Y₀ : Subgroup (MulAut V)} (hY₀ : Y₀ ∈ Yinv X) (hone : ∀ Y ∈ Yinv X, Y = Y₀) :
    fixV Y₀ = ⊥ ∧ rk V = 4 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hY₀R, hY₀card, t₀, ht₀, hinv₀⟩ := hY₀
  obtain ⟨d, hdY, hd1, hdz, hdord⟩ := exists_generator_of_prime_card (p := 3) hY₀card
  have hfix : fixV Y₀ = ⊥ := by
    refine eq_bot_of_le_fixV_inverted hV c hX1 fun x hx hx1 ⟨t, ht, hinv⟩ => ?_
    have := hone _ (zpowers_mem_Yinv hV ht hx hx1 hinv)
    rw [this]
  refine ⟨hfix, ?_⟩
  obtain ⟨-, -, hrksum, -⟩ := commV_card_three hV hY₀card
  have h4 : rk (commV Y₀) = 4 := by
    have := (inverted_data hV c hX1 ht₀ (hY₀R hdY) hd1 (hinv₀ d hdY)).2.1
    rwa [hdz] at this
  rw [hfix, rk_bot] at hrksum
  omega

theorem card_pCoreOf_three_of_rk_four (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) (hrkV : rk V = 4) {Y₀ : Subgroup (MulAut V)}
    (hY₀R : Y₀ ≤ pCoreOf 3 X) (hY₀card : Nat.card Y₀ = 3) : Nat.card (pCoreOf 3 X) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hR := c.fittingOf_eq hV
  have hRdvd := three_group_card_dvd_nine hV hrkV (pCoreOf_isPGroup 3 X)
  have hge : 3 ≤ Nat.card (pCoreOf 3 X) := by
    have := Subgroup.card_le_of_le hY₀R
    omega
  by_contra hne
  have h9 : Nat.card (pCoreOf 3 X) = 9 := by
    have hd : Nat.card (pCoreOf 3 X) ∈ Nat.divisors 9 :=
      Nat.mem_divisors.mpr ⟨hRdvd, by norm_num⟩
    have hdivs : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdivs] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  obtain ⟨q, hqR, hqord, v, hv1, hqv⟩ := exists_order_three_fixed hV hrkV h9
  apply hX1 (Subgroup.zpowers q)
  have hq1 : q ≠ 1 := by intro h; rw [h, orderOf_one] at hqord; omega
  have hqcard : Nat.card (Subgroup.zpowers q) = 3 := by rw [Nat.card_zpowers, hqord]
  obtain ⟨-, -, hrksum, hev⟩ := commV_card_three hV hqcard
  have hfix1 : 1 ≤ rk (fixV (Subgroup.zpowers q)) := by
    by_contra h0
    have : rk (fixV (Subgroup.zpowers q)) = 0 := by omega
    have hbot := (rk_eq_zero_iff hV).mp this
    have : v ∈ fixV (Subgroup.zpowers q) := mem_fixV_zpowers_iff.mpr hqv
    rw [hbot, Subgroup.mem_bot] at this
    exact hv1 this
  have hc1 := one_le_rk_commV_zpowers hV hq1
  refine ⟨?_, ?_, ?_⟩
  · rw [hR]; exact Subgroup.zpowers_le.mpr hqR
  · rw [Nat.card_zpowers, hqord]
  · obtain ⟨m, hm⟩ := hev
    omega

omit [Finite V] in
theorem generation_of_card_three (hfstar : X ⊓ Subgroup.centralizer (fittingOf X : Set (MulAut V)) ≤
      fittingOf X) {d t₀ : MulAut V} (hdord : orderOf d = 3) (hFd : fittingOf X = Subgroup.zpowers d)
    (ht₀ : t₀ ∈ X) (hinv : t₀ * d * t₀⁻¹ = d⁻¹) :
    ∀ g ∈ X, g ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers t₀ := by
  have hd3 : d ^ 3 = 1 := by rw [← hdord]; exact pow_orderOf_eq_one d
  have hd1 : d ≠ 1 := by intro h; rw [h, orderOf_one] at hdord; omega
  have hcent : ∀ g ∈ X, g * d * g⁻¹ = d → g ∈ Subgroup.zpowers d := by
    intro g hg hgd
    have hgc : g ∈ Subgroup.centralizer (fittingOf X : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hFd] at hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : g * d ^ k * g⁻¹ = d ^ k := by rw [← conj_zpow, hgd]
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    have := hfstar ⟨hg, hgc⟩
    rwa [hFd] at this
  intro g hg
  have hnorm : g * d * g⁻¹ ∈ fittingOf X :=
    conj_mem_fittingOf hg (by rw [hFd]; exact Subgroup.mem_zpowers d)
  rw [hFd] at hnorm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnorm
  have hmod : d ^ (k % 3) = d ^ k := by
    have := zpow_mod_orderOf d k
    rw [hdord] at this
    simpa using this
  have hdcase : g * d * g⁻¹ = d ∨ g * d * g⁻¹ = d⁻¹ := by
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h | h | h
    · exfalso
      rw [h, zpow_zero] at hmod
      have h1 : g * d * g⁻¹ = 1 := by rw [← hk, ← hmod]
      apply hd1
      calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · left; rw [← hk, ← hmod, h, zpow_one]
    · right
      rw [← hk, ← hmod, h]
      have : d ^ (2 : ℤ) * d = 1 := by
        rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num]
        simpa using hd3
      exact mul_eq_one_iff_eq_inv.mp this
  rcases hdcase with h | h
  · exact Subgroup.mem_sup_left (hcent g hg h)
  · have hgt : g * t₀ * d * (g * t₀)⁻¹ = d := by
      calc g * t₀ * d * (g * t₀)⁻¹ = g * (t₀ * d * t₀⁻¹) * g⁻¹ := by group
        _ = g * d⁻¹ * g⁻¹ := by rw [hinv]
        _ = (g * d * g⁻¹)⁻¹ := by group
        _ = d := by rw [h, inv_inv]
    have hmem : g * t₀ ∈ Subgroup.zpowers d := hcent _ (X.mul_mem hg ht₀) hgt
    have : g = (g * t₀) * t₀⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers t₀)))

theorem D2_27 (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {Y₀ : Subgroup (MulAut V)} (hY₀ : Y₀ ∈ Yinv X) (hone : ∀ Y ∈ Yinv X, Y = Y₀) :
    Nonempty (↥X ≃* DihedralGroup 3) ∧ rk V = 4 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, hrkV⟩ := D2_27_rank hV c hX1 hY₀ hone
  obtain ⟨hY₀R, hY₀card, t₀, ht₀, hinv₀⟩ := hY₀
  obtain ⟨d, hdY, hd1, hdz, hdord⟩ := exists_generator_of_prime_card (p := 3) hY₀card
  have hRcard := card_pCoreOf_three_of_rk_four hV c hX1 hrkV hY₀R hY₀card
  have hRY : pCoreOf 3 X = Y₀ :=
    (Subgroup.eq_of_le_of_card_ge hY₀R (by rw [hRcard, hY₀card])).symm
  have hFd : fittingOf X = Subgroup.zpowers d := by rw [c.fittingOf_eq hV, hRY, hdz]
  refine ⟨?_, hrkV⟩
  exact nonempty_mulEquiv_dihedral_of_subgroup (by norm_num) (pCoreOf_le 3 X (hY₀R hdY)) ht₀.1
    hdord (orderOf_eq_prime ht₀.2.2.1 ht₀.2.1) (hinv₀ d hdY)
    (generation_of_card_three c.hyp.fstar hdord hFd ht₀.1 (hinv₀ d hdY))

end Y1

end CFSG.Quasithin
