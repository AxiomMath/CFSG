module

public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Quasithin.Background.F918Z3A2Sec
public import CFSG.Quasithin.Background.F918Z8Def3
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

theorem suz_card_ge {X : Type} [Group X]
    (hsz : ∃ n, IsSz n X) : 20161 ≤ Nat.card X := by
  obtain ⟨n, -, a, ha, K, _, _, hn, hK, ⟨e⟩⟩ := hsz
  subst hn
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * a + 1) = t at h8 ⊢
  have h1 : 64 ≤ t ^ 2 := by nlinarith
  have h2 : 7 ≤ t - 1 := by omega
  have h3 : 65 ≤ t ^ 2 + 1 := by omega
  calc 20161 ≤ 64 * 7 * 65 := by norm_num
    _ ≤ t ^ 2 * (t - 1) * (t ^ 2 + 1) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

theorem d321s_rk_le_one_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) :
    rk G ≤ 1 := by
  unfold rk
  have hpos : 0 < Nat.card G := Nat.card_pos
  generalize Nat.card G = n at h hpos
  interval_cases n <;> simp

theorem d321s_comm_aux {G : Type*} [CommGroup G] (p q r : G) :
    (p * q⁻¹) * (r * p⁻¹) * (q * r⁻¹) = 1 := by
  calc (p * q⁻¹) * (r * p⁻¹) * (q * r⁻¹) = (p * p⁻¹) * (q * q⁻¹) * (r * r⁻¹) := by ac_rfl
    _ = 1 := by simp

section Suz

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem suz_rk_ge_five
    (h : LocCfg Γ Λ S V) (hsz : ∃ n, IsSz n ↥Λ) {W : Subgroup Y}
    (hWΛ : ∀ l ∈ Λ, ∀ w ∈ W, l w ∈ W) (hW0 : W ≠ ⊥) : 5 ≤ rk ↥W := by
  have hsimp : IsSimpleGroup ↥Λ := insp5a_sec_isSimpleGroup h.a38
  have hnt : ∃ y ∈ Λ, ∃ v ∈ W, y v ≠ v := by
    obtain ⟨w, hw, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hW0 ((Subgroup.eq_bot_iff_forall _).2 hcon)
    by_contra hcon
    push Not at hcon
    apply hw1
    have : w ∈ fixV Λ := fun y hy => hcon y hy w hw
    rw [h.fix] at this
    simpa using this
  have hfaith := CaseIISec.faithful hsimp hWΛ hnt
  have hΛs : Λ ≤ stabSub W := le_stabSub_of_forall_mem hWΛ
  have hcard := card_autSub_mul hΛs
  rw [hfaith, Subgroup.card_bot, mul_one] at hcard
  by_contra hlt
  push Not at hlt
  have hWexp : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simp [h.std.hyp.exp])
  have hle : Nat.card ↥(autSub Λ W) ≤ Nat.card (MulAut ↥W) := Subgroup.card_le_card_group _
  have hbound : Nat.card (MulAut ↥W) ≤ 20160 := by
    rw [card_mulAut_eq hWexp]
    generalize rk ↥W = n at hlt ⊢
    interval_cases n <;> decide
  have := suz_card_ge hsz
  omega

theorem suz_half_fixed {W C : Subgroup Y} {x a : MulAut Y} (hx3 : x ^ 3 = 1)
    (hax : a * x * a⁻¹ = x⁻¹) (hxW : ∀ w ∈ W, x w ∈ W) (hfree : ∀ w ∈ W, x w = w → w = 1)
    (hCW : C ≤ W) (hCa : ∀ c ∈ C, a c = c) (hexp : ∀ y : Y, y ^ 2 = 1) :
    2 * rk ↥C ≤ rk ↥W := by
  let φ : ↥C × ↥C → ↥W := fun p =>
    ⟨(p.1 : Y) * x (p.2 : Y), W.mul_mem (hCW p.1.2) (hxW _ (hCW p.2.2))⟩
  have hinj : Function.Injective φ := by
    rintro ⟨c₁, c₂⟩ ⟨c₁', c₂'⟩ hφ
    have h1 : (c₁ : Y) * x (c₂ : Y) = (c₁' : Y) * x (c₂' : Y) := congrArg Subtype.val hφ
    set d : Y := (c₂' : Y) * (c₂ : Y)⁻¹ with hd
    have hdC : d ∈ C := C.mul_mem c₂'.2 (C.inv_mem c₂.2)
    have hz : x d = (c₁ : Y) * (c₁' : Y)⁻¹ := by
      rw [hd, map_mul, map_inv]
      have : (c₁ : Y) * x (c₂ : Y) = (c₁' : Y) * x (c₂' : Y) := h1
      calc x (c₂' : Y) * (x (c₂ : Y))⁻¹
          = ((c₁' : Y)⁻¹ * (c₁' : Y)) * x (c₂' : Y) * (x (c₂ : Y))⁻¹ := by
            rw [inv_mul_cancel, one_mul]
        _ = (c₁' : Y)⁻¹ * ((c₁' : Y) * x (c₂' : Y)) * (x (c₂ : Y))⁻¹ := by
            rw [mul_assoc (c₁' : Y)⁻¹]
        _ = (c₁' : Y)⁻¹ * ((c₁ : Y) * x (c₂ : Y)) * (x (c₂ : Y))⁻¹ := by rw [this]
        _ = (c₁ : Y) * (c₁' : Y)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel_right]; exact mul_comm _ _
    have hzC : x d ∈ C := by rw [hz]; exact C.mul_mem c₁.2 (C.inv_mem c₁'.2)
    have hxd : a (x d) = x d := hCa _ hzC
    have hax' : a (x d) = x⁻¹ (a d) := by
      have : a (x d) = (a * x * a⁻¹) (a d) := by simp [MulAut.mul_apply]
      rw [this, hax]
    rw [hax', hCa d hdC] at hxd
    have hxd2 : x d = d := by
      have h2 : x (x⁻¹ d) = x (x d) := by rw [hxd]
      have h3 : x (x d) = x⁻¹ d := by
        have : x ^ 2 = x⁻¹ := by
          have : x ^ 2 * x = 1 := by rw [← pow_succ]; exact hx3
          exact eq_inv_of_mul_eq_one_left this
        calc x (x d) = (x * x) d := rfl
          _ = (x ^ 2) d := by rw [sq]
          _ = x⁻¹ d := by rw [this]
      have h4 : x (x⁻¹ d) = d := by simp
      rw [h4, h3] at h2
      exact hxd.symm.trans h2.symm
    have hd1 : d = 1 := hfree d (hCW hdC) hxd2
    have hc2 : (c₂' : Y) = c₂ := by
      have : (c₂' : Y) * (c₂ : Y)⁻¹ = 1 := hd1
      exact mul_inv_eq_one.1 this
    have hc1 : (c₁ : Y) = c₁' := by
      have h5 : x d = 1 := by rw [hd1]; simp
      rw [h5] at hz
      exact (mul_inv_eq_one.1 hz.symm)
    have e1 : c₁ = c₁' := Subtype.ext hc1
    have e2 : c₂ = c₂' := (Subtype.ext hc2).symm
    rw [e1, e2]
  have hcard : Nat.card ↥C * Nat.card ↥C ≤ Nat.card ↥W := by
    have := Nat.card_le_card_of_injective φ hinj
    rwa [Nat.card_prod] at this
  rw [card_eq_two_pow hexp C, card_eq_two_pow hexp W, ← pow_add] at hcard
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  omega

theorem suz_order_three
    (h : LocCfg Γ Λ S V) (hsz : ∃ n, IsSz n ↥Λ)
    {A : Subgroup (MulAut Y)} (hA : A ∈ QhatStar Γ)
    (hAc : ∀ a ∈ A, ∀ x ∈ Λ, a * x = x * a) {X : Subgroup (MulAut Y)}
    (hXc : ∀ x ∈ X, ∀ y ∈ Λ, x * y = y * x) (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut Y)))
    (hXA : ⁅X, A⁆ = X) (hX3 : Nat.card ↥X = 3) : False := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := QhatStar_spec hA
  have hexp : ∀ y : Y, y ^ 2 = 1 := h.std.hyp.exp
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA2.2.2.1
  have hA2' : ∀ a ∈ A, a ^ 2 = 1 := hA2.2.2.2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic ↥X := isCyclic_of_prime_card hX3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥X)
  set x : MulAut Y := (g : MulAut Y) with hxdef
  have hxX : x ∈ X := g.2
  have hXx : ∀ y ∈ X, ∃ k : ℤ, x ^ k = y := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hy⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hx1 : x ≠ 1 := by
    intro hx1
    have hbot : X = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun y hy => by
      obtain ⟨k, rfl⟩ := hXx y hy
      simp [hx1]
    rw [hbot, Subgroup.card_bot] at hX3
    omega
  have hx3 : x ^ 3 = 1 := by
    have : g ^ 3 = 1 := by
      rw [← hX3]
      exact pow_card_eq_one'
    simpa using congrArg Subtype.val this
  have hx2 : x * x * x = 1 := by simpa [pow_succ] using hx3
  have hxinv : x⁻¹ = x * x := (eq_inv_of_mul_eq_one_left hx2).symm
  have hX3elts : ∀ y ∈ X, y = 1 ∨ y = x ∨ y = x⁻¹ := by
    intro y hy
    obtain ⟨k, rfl⟩ := hXx y hy
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hk : x ^ (k % 3) = x ^ k := by simpa [hord] using zpow_mod_orderOf x k
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · left
      rw [← hk, h0]
      simp
    · right; left
      rw [← hk, h1]
      simp
    · right; right
      rw [← hk, h2, hxinv]
      simp [pow_two]
  have hinv : ∀ a ∈ A, a * x * a⁻¹ = x ∨ a * x * a⁻¹ = x⁻¹ := by
    intro a ha
    have hmem : a * x * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hAX ha) x).1 hxX
    rcases hX3elts _ hmem with h1 | h1 | h1
    · exfalso
      apply hx1
      calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
        _ = 1 := by rw [h1]; group
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨a₁, ha₁, ha₁x⟩ : ∃ a ∈ A, a * x * a⁻¹ = x⁻¹ := by
    by_contra hcon
    push Not at hcon
    have hAx : ∀ a ∈ A, a * x = x * a := by
      intro a ha
      rcases hinv a ha with h1 | h1
      · calc a * x = a * x * a⁻¹ * a := by group
          _ = x * a := by rw [h1]
      · exact absurd h1 (hcon a ha)
    have hbot : ⁅X, A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨k, rfl⟩ := hXx y hy
      exact (Commute.zpow_right (hAx a ha : Commute a x) k)
    rw [hXA] at hbot
    rw [hbot, Subgroup.card_bot] at hX3
    omega
  set B : Subgroup (MulAut Y) := A ⊓ Subgroup.centralizer ({x} : Set (MulAut Y)) with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBx : ∀ b ∈ B, b * x = x * b := fun b hb =>
    ((Subgroup.mem_centralizer_iff.1 hb.2) x (Set.mem_singleton x)).symm
  set F : Subgroup Y := fixV B with hFdef
  have hFA : ∀ a ∈ A, ∀ u ∈ F, a u ∈ F := fun a ha u hu b hb => by
    have hab : b * a = a * b := hAab b (hBA hb) a ha
    calc b (a u) = (b * a) u := rfl
      _ = (a * b) u := by rw [hab]
      _ = a (b u) := rfl
      _ = a u := by rw [hu b hb]
  have hFx : ∀ u ∈ F, x u ∈ F := fun u hu b hb => by
    calc b (x u) = (b * x) u := rfl
      _ = (x * b) u := by rw [hBx b hb]
      _ = x (b u) := rfl
      _ = x u := by rw [hu b hb]
  have hFx' : ∀ u ∈ F, x⁻¹ u ∈ F := fun u hu => by
    rw [hxinv]
    exact hFx _ (hFx u hu)
  have hFΛ : ∀ l ∈ Λ, ∀ u ∈ F, l u ∈ F := fun l hl u hu b hb => by
    have hbl : b * l = l * b := hAc b (hBA hb) l hl
    calc b (l u) = (b * l) u := rfl
      _ = (l * b) u := by rw [hbl]
      _ = l (b u) := rfl
      _ = l u := by rw [hu b hb]
  let c : Y →* Y :=
    { toFun := fun u => x u * u⁻¹
      map_one' := by simp
      map_mul' := fun u v => by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  set W : Subgroup Y := F.map c with hWdef
  have hWmem : ∀ w ∈ W, ∃ u ∈ F, w = x u * u⁻¹ := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := hw
    exact ⟨u, hu, rfl⟩
  have hWc : ∀ u ∈ F, x u * u⁻¹ ∈ W := fun u hu => ⟨u, hu, rfl⟩
  have hWA : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W := by
    intro a ha w hw
    obtain ⟨u, hu, rfl⟩ := hWmem w hw
    have e : a (x u * u⁻¹) = (a * x * a⁻¹) (a u) * (a u)⁻¹ := by
      simp [MulAut.mul_apply]
    rw [e]
    rcases hinv a ha with h1 | h1
    · rw [h1]
      exact hWc _ (hFA a ha u hu)
    · rw [h1]
      have hu' := hFA a ha u hu
      have := W.inv_mem (hWc _ (hFx' _ hu'))
      convert this using 1
      simp
  have hWx : ∀ w ∈ W, x w ∈ W := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := hWmem w hw
    have e : x (x u * u⁻¹) = x (x u) * (x u)⁻¹ := by simp
    rw [e]
    exact hWc _ (hFx u hu)
  have hWΛ : ∀ l ∈ Λ, ∀ w ∈ W, l w ∈ W := by
    intro l hl w hw
    obtain ⟨u, hu, rfl⟩ := hWmem w hw
    have hlx : l * x = x * l := (hXc x hxX l hl).symm
    have e : l (x u * u⁻¹) = x (l u) * (l u)⁻¹ := by
      have : l (x u) = x (l u) := by
        calc l (x u) = (l * x) u := rfl
          _ = (x * l) u := by rw [hlx]
          _ = x (l u) := rfl
      rw [map_mul, map_inv, this]
    rw [e]
    exact hWc _ (hFΛ l hl u hu)
  have hWF : W ≤ F := by
    rintro _ ⟨u, hu, rfl⟩
    exact F.mul_mem (hFx u hu) (F.inv_mem hu)
  have hW0 : W ≠ ⊥ := by
    intro hW0
    have hfix : ∀ u ∈ F, x u = u := fun u hu => by
      have hmem : x u * u⁻¹ ∈ W := hWc u hu
      rw [hW0, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact hmem
    have hR : IsPGroup 2 Y := fun y => ⟨1, by simpa using hexp y⟩
    have hAX' : ¬ 2 ∣ Nat.card ↥X := by rw [hX3]; norm_num
    have hB2 : IsPGroup 2 ↥B := fun b =>
      ⟨1, Subtype.ext (by simpa using hA2' (b : MulAut Y) (hBA b.2))⟩
    have hcomm : ∀ (a : ↥X) (b : ↥B), X.subtype a * B.subtype b = B.subtype b * X.subtype a := by
      intro a b
      obtain ⟨k, hk⟩ := hXx (a : MulAut Y) a.2
      show (a : MulAut Y) * (b : MulAut Y) = (b : MulAut Y) * (a : MulAut Y)
      rw [← hk]
      exact (Commute.zpow_right (hBx b b.2 : Commute (b : MulAut Y) x) k).symm
    have hfix' : ∀ (a : ↥X) (r : Y), (∀ b : ↥B, B.subtype b r = r) → X.subtype a r = r := by
      intro a r hr
      have hrF : r ∈ F := fun b hb => hr ⟨b, hb⟩
      obtain ⟨k, hk⟩ := hXx (a : MulAut Y) a.2
      show (a : MulAut Y) r = r
      rw [← hk]
      have hxr : x ∈ MulAction.stabilizer (MulAut Y) r := by
        rw [MulAction.mem_stabilizer_iff]
        exact hfix r hrF
      have := Subgroup.zpow_mem _ hxr k
      rw [MulAction.mem_stabilizer_iff] at this
      exact this
    have hall := CFSG.GroupTheory.thompson_A_times_B (p := 2) hR hAX' hB2 X.subtype B.subtype
      hcomm hfix'
    exact hx1 (hall ⟨x, hxX⟩)
  have hxxx : ∀ v : Y, x (x (x v)) = v := fun v => by
    calc x (x (x v)) = (x * x * x) v := rfl
      _ = v := by rw [hx2]; rfl
  have hfree : ∀ w ∈ W, x w = w → w = 1 := by
    intro w hw hxw
    obtain ⟨u, hu, rfl⟩ := hWmem w hw
    have hprod : (x u * u⁻¹) * x (x u * u⁻¹) * x (x (x u * u⁻¹)) = 1 := by
      simp only [map_mul, map_inv, hxxx]
      exact d321s_comm_aux (x u) u (x (x u))
    simp only [hxw] at hprod
    have hw2 : (x u * u⁻¹) * (x u * u⁻¹) = 1 := by rw [← sq]; exact hexp _
    rw [hw2, one_mul] at hprod
    exact hprod
  have hrk5 : 5 ≤ rk ↥W := suz_rk_ge_five h hsz hWΛ hW0
  have hAW : A ≤ stabSub W := le_stabSub_of_forall_mem hWA
  have hhalf := suz_half_fixed (W := W) (C := W ⊓ fixV A) hx3 ha₁x hWx hfree inf_le_left
    (fun c hc => hc.2 a₁ ha₁) hexp
  have hUA : commSub W A ≠ ⊥ := by
    intro hbot
    rw [commSub_eq_bot_iff] at hbot
    have : W ⊓ fixV A = W := inf_eq_left.2 hbot
    rw [this] at hhalf
    omega
  have hRP : A ∈ RPlusLe Γ r := by
    obtain ⟨⟨⟨hA2', hAr'⟩, -⟩, hplus⟩ := (D2_7 hexp hr hA hAW hUA).1
    exact ⟨⟨hA2', hAr'.le⟩, hplus⟩
  obtain ⟨hAU, hrAU⟩ := D2_5 hexp hRP hAW hUA
  have hBW : ∀ b ∈ B, ∀ w ∈ W, b w = w := fun b hb w hw => hWF hw b hb
  have hcard2 : Nat.card ↥(autSub A W) ≤ 2 := by
    let a₁' : stabSub W := ⟨a₁, hAW ha₁⟩
    have hsq : resHom W a₁' ^ 2 = 1 := by
      rw [← map_pow]
      have : a₁' ^ 2 = 1 := Subtype.ext (by simpa using hA2' a₁ ha₁)
      rw [this, map_one]
    have hle : autSub A W ≤ Subgroup.zpowers (resHom W a₁') := by
      intro φ hφ
      obtain ⟨g, hgA, rfl⟩ := mem_autSub.1 hφ
      have hres : ∀ b : stabSub W, (b : MulAut Y) ∈ B → resHom W b = 1 := by
        intro b hb
        ext w
        exact hBW _ hb w w.2
      rcases hinv _ hgA with h1 | h1
      · have : resHom W g = 1 := hres g ⟨hgA, Subgroup.mem_centralizer_iff.2 (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          calc x * (g : MulAut Y) = ((g : MulAut Y) * x * (g : MulAut Y)⁻¹) * g := by rw [h1]
            _ = g * x := by group)⟩
        rw [this]
        exact Subgroup.one_mem _
      · have hb : ((a₁'⁻¹ * g : stabSub W) : MulAut Y) ∈ B := by
          refine ⟨A.mul_mem (A.inv_mem ha₁) hgA, Subgroup.mem_centralizer_iff.2 ?_⟩
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          have hx' : a₁⁻¹ * x⁻¹ * a₁ = x := by
            calc a₁⁻¹ * x⁻¹ * a₁ = a₁⁻¹ * (a₁ * x * a₁⁻¹) * a₁ := by rw [ha₁x]
              _ = x := by group
          have e1 : (g : MulAut Y) * x = x⁻¹ * g := by
            calc (g : MulAut Y) * x = ((g : MulAut Y) * x * (g : MulAut Y)⁻¹) * g := by group
              _ = x⁻¹ * g := by rw [h1]
          show x * (a₁⁻¹ * (g : MulAut Y)) = (a₁⁻¹ * (g : MulAut Y)) * x
          calc x * (a₁⁻¹ * (g : MulAut Y))
              = (a₁⁻¹ * x⁻¹ * a₁) * (a₁⁻¹ * (g : MulAut Y)) := by rw [hx']
            _ = a₁⁻¹ * x⁻¹ * (a₁ * a₁⁻¹) * (g : MulAut Y) := by group
            _ = a₁⁻¹ * (x⁻¹ * g) := by group
            _ = a₁⁻¹ * ((g : MulAut Y) * x) := by rw [e1]
            _ = (a₁⁻¹ * (g : MulAut Y)) * x := by group
        have h2 := hres _ hb
        have h3 : resHom W g = resHom W a₁' := by
          have : g = a₁' * (a₁'⁻¹ * g) := by group
          rw [this, map_mul, h2, mul_one]
        rw [h3]
        exact Subgroup.mem_zpowers _
    calc Nat.card ↥(autSub A W) ≤ Nat.card ↥(Subgroup.zpowers (resHom W a₁')) :=
          Subgroup.card_le_of_le hle
      _ = orderOf (resHom W a₁') := Nat.card_zpowers _
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hsq
  have hrkĀ : rk ↥(autSub A W) = 1 := by
    have h1 := hAU.rk_pos
    have h2 := d321s_rk_le_one_of_card_le_two hcard2
    omega
  have hidx := rkIdx_autSub_add hAW
  have hr' : (rkIdx (fixV (autSub A W)) : ℚ) ≤ 2 := by
    have := hrAU
    unfold rAV at this
    rw [hrkĀ] at this
    simp only [Nat.cast_one, div_one] at this
    linarith
  have : rkIdx (fixV (autSub A W)) ≤ 2 := by exact_mod_cast hr'
  omega

end Suz

end CFSG.Quasithin
