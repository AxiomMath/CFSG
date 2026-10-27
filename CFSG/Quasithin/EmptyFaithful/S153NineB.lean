module

public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.S153Cases
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationFinal
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open CFSG.Quasithin.S14110

section Abstract

variable {G : Type*} [Group G]

private theorem exists_central_involution_of_normal [Finite G] {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hU : U ≠ ⊥) (hn : T ≤ Subgroup.normalizer (U : Set G)) :
    ∃ z ∈ U, z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ y ∈ T, y * z = z * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzU, hz1, hzc⟩ := exists_ne_one_mem_center_of_normalized hT hUT hU hn
  have hzT : z ∈ T := hUT hzU
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨z, hzT⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hz1 (orderOf_eq_one_iff.mp hk)
  have hdvd : 2 ∣ orderOf z := by rw [hk]; exact dvd_pow_self 2 hk0
  have hpos : orderOf z ≠ 0 := by rw [hk]; positivity
  have hord : orderOf (z ^ (orderOf z / 2)) = 2 := orderOf_pow_orderOf_div hpos hdvd
  refine ⟨z ^ (orderOf z / 2), U.pow_mem hzU _, ?_, ?_, fun y hy => ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hord
    omega
  · have := pow_orderOf_eq_one (z ^ (orderOf z / 2))
    rwa [hord] at this
  · exact (Commute.pow_right (show Commute y z from hzc y hy) (orderOf z / 2)).eq

theorem S14110.A4Data.mem_centralizer_of_cube {X W : Subgroup G} {c : G} (h : A4Data X W c) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hgW : g ∈ Subgroup.centralizer (W : Set G))
    (hg3 : g ^ 3 = 1) : g ∈ Subgroup.centralizer (X : Set G) := by
  obtain ⟨w, hw, hz⟩ := h.exists_mul_mem_centralizer hg hgW
  set z : G := w⁻¹ * g with hzdef
  have hgz : g = w * z := by rw [hzdef]; group
  have hwz : w * z = z * w := Subgroup.mem_centralizer_iff.1 hz w (h.le hw)
  have hz3 : z ^ 3 = w⁻¹ := by
    have h1 : (w * z) ^ 3 = w ^ 3 * z ^ 3 := (Commute.mul_pow (show Commute w z from hwz) 3)
    have h2 : w ^ 3 = w := by
      have := h.sq_eq_one w hw
      calc w ^ 3 = w ^ 2 * w := by rw [pow_succ]
        _ = w := by rw [this, one_mul]
    rw [← hgz, hg3, h2] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  have hz3W : z ^ 3 ∈ X := by rw [hz3]; exact X.inv_mem (h.le hw)
  have hz3c : ∀ l ∈ X, z ^ 3 * l = l * z ^ 3 := by
    intro l hl
    have hl' : l * z = z * l := Subgroup.mem_centralizer_iff.1 hz l hl
    exact (Commute.pow_left (show Commute z l from hl'.symm) 3).eq
  have h1 : z ^ 3 = 1 := h.center _ hz3W hz3c
  have hw1 : w = 1 := by
    rw [h1] at hz3
    exact inv_eq_one.mp hz3.symm
  rw [hgz, hw1, one_mul]
  exact hz

private theorem card_sup_of_le_normalizer_of_inf_eq_bot {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) (hHK : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left H K hK
  let φ : H × K → (H ⊔ K : Subgroup G) := fun x =>
    ⟨x.1 * x.2, mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 : (x.1 : G) * x.2 = y.1 * y.2 := congrArg Subtype.val hxy
      have h2 : ((y.1 : G))⁻¹ * x.1 = y.2 * (x.2 : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
      have h3 : ((y.1 : G))⁻¹ * x.1 ∈ H ⊓ K :=
        Subgroup.mem_inf.2 ⟨H.mul_mem (H.inv_mem y.1.2) x.1.2,
          h2 ▸ K.mul_mem y.2.2 (K.inv_mem x.2.2)⟩
      rw [hHK, Subgroup.mem_bot, inv_mul_eq_one] at h3
      have h4 : (x.2 : G) = y.2 := by
        rw [← h3] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)
    · have hz : (z : G) ∈ ((H ⊔ K : Subgroup G) : Set G) := z.2
      rw [hset] at hz
      obtain ⟨x, hx, v, hv, hxv⟩ := hz
      exact ⟨(⟨x, hx⟩, ⟨v, hv⟩), Subtype.ext hxv⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective φ hφ)).symm

theorem a4Data_of_data {W : Subgroup G} {c : G} (hW4 : Nat.card W = 4)
    (hsq : ∀ w ∈ W, w ^ 2 = 1) (hcomm : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u)
    (hc3 : orderOf c = 3) (hcn : c ∈ Subgroup.normalizer (W : Set G))
    (hfpf : ∀ w ∈ W, w ≠ 1 → c * w * c⁻¹ ≠ w) :
    A4Data (W ⊔ Subgroup.zpowers c) W c := by
  have hc3' : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  have hc3z : c ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact hc3'
  have hnW : ∀ k : ℤ, c ^ k ∈ Subgroup.normalizer (W : Set G) := fun k => zpow_mem hcn k
  have hzW : ∀ k : ℤ, c ^ k ∈ W → c ^ k = 1 := by
    intro k hk
    have h2 : (c ^ k) ^ 2 = 1 := hsq _ hk
    have h3 : (c ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast (c ^ k) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3', one_zpow]
    calc c ^ k = (c ^ k) ^ 3 * ((c ^ k) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, h3]; simp
  have hzc : ∀ j : ℤ, (∀ u ∈ W, c ^ j * u * (c ^ j)⁻¹ = u) → c ^ j = 1 := by
    intro j hj
    have hmod : c ^ (j % 3) = c ^ j := by
      have := zpow_mod_orderOf c j
      rw [hc3] at this
      simpa using this
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ W, u ≠ 1 := by
      have hfin : Finite W := Nat.finite_of_card_ne_zero (by rw [hW4]; norm_num)
      have : 1 < Nat.card W := by rw [hW4]; norm_num
      have hnt : Nontrivial W := (Finite.one_lt_card_iff_nontrivial (α := W)).1 this
      obtain ⟨⟨u, hu⟩, hu1⟩ := exists_ne (1 : W)
      exact ⟨u, hu, fun h' => hu1 (Subtype.ext h')⟩
    have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [← hmod, h0]; simp
    · exfalso
      rw [← hmod, h1] at hj
      have := hj u hu
      simp only [zpow_one] at this
      exact hfpf u hu hu1 this
    · exfalso
      rw [← hmod, h2] at hj
      apply hfpf u hu hu1
      have h3 := hj u hu
      calc c * u * c⁻¹ = c * (c ^ (2 : ℤ) * u * (c ^ (2 : ℤ))⁻¹) * c⁻¹ := by rw [h3]
        _ = c ^ (3 : ℤ) * u * (c ^ (3 : ℤ))⁻¹ := by group
        _ = u := by rw [hc3z]; simp
  have hinf : W ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxc⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxc
    rw [Subgroup.mem_bot]
    exact hzW k hxW
  have hdecomp : ∀ {x : G}, x ∈ W ⊔ Subgroup.zpowers c → ∃ w ∈ W, ∃ k : ℤ, x = w * c ^ k := by
    intro x hx
    have h1 : x ∈ ((W ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left W (Subgroup.zpowers c)
      (Subgroup.zpowers_le.2 hcn)] at h1
    obtain ⟨w, hw, y, hy, rfl⟩ := h1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨w, hw, k, rfl⟩
  exact
  { le := le_sup_left
    card_W := hW4
    sq_eq_one := hsq
    comm := hcomm
    mem_X := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    order_c := hc3
    mem_normalizer := hcn
    fpf := hfpf
    eq_sup := rfl
    card_X := by
      rw [card_sup_of_le_normalizer_of_inf_eq_bot (Subgroup.zpowers_le.2 hcn) hinf, hW4,
        Nat.card_zpowers, hc3]
    center := by
      intro g hg hgc
      obtain ⟨w, hw, k, rfl⟩ := hdecomp hg
      have hck : ∀ u ∈ W, c ^ k * u * (c ^ k)⁻¹ = u := by
        intro u hu
        have hcu : (w * c ^ k) * u = u * (w * c ^ k) :=
          hgc u (Subgroup.mem_sup_left hu)
        have hwu : w * u = u * w := hcomm w hw u hu
        have h1 : w * (c ^ k * u * (c ^ k)⁻¹) = w * u := by
          calc w * (c ^ k * u * (c ^ k)⁻¹) = ((w * c ^ k) * u) * (c ^ k)⁻¹ := by group
            _ = (u * (w * c ^ k)) * (c ^ k)⁻¹ := by rw [hcu]
            _ = u * w := by group
            _ = w * u := hwu.symm
        exact mul_left_cancel h1
      have hk1 : c ^ k = 1 := hzc k hck
      rw [hk1, mul_one] at hgc ⊢
      have hwc : w * c = c * w := hgc c (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
      by_contra hw1
      apply hfpf w hw hw1
      calc c * w * c⁻¹ = (w * c) * c⁻¹ := by rw [← hwc]
        _ = w := by group }

end Abstract

section WreathAssembly

open Subgroup CFSG.Quasithin.S14110

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_wreath_of_two_conj_outer {T M X W Y : Subgroup G} {c : G}
    (hT : quasithinIsSylowTwo T) (hTM : T ≤ M) (hX : A4Data X W c)
    (hTC : TwoConj M X Y) (hXM : X ≤ M) (hYM : Y ≤ M) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hK : M ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G) = ⊥)
    (hS2 : ∃ a ∈ M ⊓ centralizer (Y : Set G), a ∉ X) :
    Nonempty (↥M ≃* Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2)) := by
  classical
  set M₁ : Subgroup G := M ⊓ centralizer (Y : Set G) with hM₁
  set M₂ : Subgroup G := M ⊓ centralizer (X : Set G) with hM₂
  set N : Subgroup G := M ⊓ normalizer (X : Set G) with hN
  have hK0 : ∀ k ∈ M, k ∈ centralizer (X : Set G) → k ∈ centralizer (Y : Set G) → k = 1 := by
    intro k hk hkX hkY
    have hle : X ⊔ Y ≤ centralizer ({k} : Set G) :=
      sup_le (fun x hx => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hkX x hx))
        (fun y hy => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hkY y hy))
    have : k ∈ M ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G) :=
      ⟨hk, mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (hle hl)⟩
    rw [hK] at this
    exact Subgroup.mem_bot.1 this
  obtain ⟨t, htT, htn⟩ := hTC.exists_mem_not_mem_normalizer hT hTM
  have htM : t ∈ M := hTM htT
  obtain ⟨hts1, hts2⟩ := hTC.swap htM htn
  have hM₁N : ∀ m ∈ M₁, m ∈ normalizer (X : Set G) := fun m hm =>
    (hTC.mem_normalizer_Y_iff hm.1).1 (Subgroup.centralizer_le_normalizer (Y : Set G) hm.2)
  have hM₂N : ∀ m ∈ M₂, m ∈ normalizer (X : Set G) := fun m hm =>
    Subgroup.centralizer_le_normalizer (X : Set G) hm.2
  have hM₂nY : ∀ m ∈ M₂, m ∈ normalizer (Y : Set G) := fun m hm =>
    (hTC.mem_normalizer_Y_iff hm.1).2 (hM₂N m hm)
  have hXM₁ : X ≤ M₁ := fun x hx => ⟨hXM hx, mem_centralizer_iff.2 fun y hy => (hXY x hx y hy).symm⟩
  have hYM₂ : Y ≤ M₂ := fun y hy => ⟨hYM hy, mem_centralizer_iff.2 fun x hx => hXY x hx y hy⟩
  have hcomm : ∀ a ∈ M₁, ∀ b ∈ M₂, a * b = b * a := by
    intro a ha b hb
    have h1 : a * b * a⁻¹ * b⁻¹ ∈ centralizer (X : Set G) :=
      Subgroup.mul_mem _
        (conj_mem_centralizer (M := normalizer (X : Set G)) le_rfl (hM₁N a ha) hb.2)
        (inv_mem hb.2)
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ centralizer (Y : Set G) := by
      have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha.2
        (conj_mem_centralizer (M := normalizer (Y : Set G)) le_rfl (hM₂nY b hb) (inv_mem ha.2))
    have h3 : a * b * a⁻¹ * b⁻¹ = 1 :=
      hK0 _ (M.mul_mem (M.mul_mem (M.mul_mem ha.1 hb.1) (M.inv_mem ha.1)) (M.inv_mem hb.1)) h1 h2
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h3, one_mul]
  have hdisj : ∀ x ∈ M₁, x ∈ M₂ → x = 1 := fun x hx1 hx2 => hK0 x hx1.1 hx2.2 hx1.2
  obtain ⟨a₀, ha₀M₁, ha₀X⟩ := hS2
  have ha₀N : a₀ ∈ normalizer (X : Set G) := hM₁N a₀ ha₀M₁
  have hfactN : ∀ n ∈ N, ∃ a ∈ M₁, ∃ b ∈ M₂, n = a * b := by
    intro n hn
    have hna₀ : ∀ i : ℤ, (c ^ i)⁻¹ * a₀ ∉ centralizer (W : Set G) := by
      intro i hi
      have hcX : (c ^ i)⁻¹ ∈ normalizer (X : Set G) :=
        Subgroup.le_normalizer (inv_mem (zpow_mem hX.mem_X i))
      have hnx : (c ^ i)⁻¹ * a₀ ∈ normalizer (X : Set G) := Subgroup.mul_mem _ hcX ha₀N
      obtain ⟨w, hw, hwc⟩ := hX.exists_mul_mem_centralizer hnx hi
      have hk : w⁻¹ * ((c ^ i)⁻¹ * a₀) = 1 := by
        refine hK0 _ ?_ hwc ?_
        · exact M.mul_mem (M.inv_mem (hXM (hX.le hw)))
            (M.mul_mem (M.inv_mem (hXM (zpow_mem hX.mem_X i))) ha₀M₁.1)
        · refine mem_centralizer_iff.2 fun y hy => ?_
          have h1 : y * w⁻¹ = w⁻¹ * y := (hXY w⁻¹ (X.inv_mem (hX.le hw)) y hy).symm
          have h2 : y * (c ^ i)⁻¹ = (c ^ i)⁻¹ * y :=
            (hXY _ (X.inv_mem (zpow_mem hX.mem_X i)) y hy).symm
          have h3 : y * a₀ = a₀ * y := mem_centralizer_iff.1 ha₀M₁.2 y hy
          calc y * (w⁻¹ * ((c ^ i)⁻¹ * a₀)) = (y * w⁻¹) * ((c ^ i)⁻¹ * a₀) := by group
            _ = w⁻¹ * (y * (c ^ i)⁻¹) * a₀ := by rw [h1]; group
            _ = w⁻¹ * ((c ^ i)⁻¹ * y) * a₀ := by rw [h2]
            _ = w⁻¹ * ((c ^ i)⁻¹ * (y * a₀)) := by group
            _ = w⁻¹ * ((c ^ i)⁻¹ * (a₀ * y)) := by rw [h3]
            _ = w⁻¹ * ((c ^ i)⁻¹ * a₀) * y := by group
      apply ha₀X
      have : a₀ = c ^ i * w := by
        calc a₀ = c ^ i * (w * (w⁻¹ * ((c ^ i)⁻¹ * a₀))) := by group
          _ = c ^ i * w := by rw [hk]; group
      rw [this]
      exact X.mul_mem (zpow_mem hX.mem_X i) (hX.le hw)
    have hnW : n ∈ normalizer (W : Set G) := hX.normalizer_le_normalizer_W hn.2
    have ha₀W : a₀ ∈ normalizer (W : Set G) := hX.normalizer_le_normalizer_W ha₀N
    obtain ⟨i, hi⟩ := hX.exists_zpow_or_zpow_mul hnW ha₀W hna₀
    have hex : ∃ a ∈ M₁, a⁻¹ * n ∈ centralizer (W : Set G) := by
      rcases hi with hi | hi
      · refine ⟨c ^ i, hXM₁ (zpow_mem hX.mem_X i), ?_⟩
        simpa using hi
      · refine ⟨c ^ i * a₀, M₁.mul_mem (hXM₁ (zpow_mem hX.mem_X i)) ha₀M₁, ?_⟩
        simpa using hi
    obtain ⟨a, haM₁, hac⟩ := hex
    have haN : a ∈ normalizer (X : Set G) := hM₁N a haM₁
    have hanN : a⁻¹ * n ∈ normalizer (X : Set G) := Subgroup.mul_mem _ (inv_mem haN) hn.2
    obtain ⟨w, hw, hwc⟩ := hX.exists_mul_mem_centralizer hanN hac
    have hwM₁ : w ∈ M₁ := hXM₁ (hX.le hw)
    have hb : w⁻¹ * (a⁻¹ * n) ∈ M₂ :=
      ⟨M.mul_mem (M.inv_mem hwM₁.1) (M.mul_mem (M.inv_mem haM₁.1) hn.1), hwc⟩
    refine ⟨a * w, M₁.mul_mem haM₁ hwM₁, _, hb, ?_⟩
    group
  have htt : t * t ∈ N := by
    refine ⟨M.mul_mem htM htM, ?_⟩
    show t * t ∈ normalizer (X : Set G)
    rw [mem_normalizer_iff_cj, ← cj_cj, hts1, hts2]
  obtain ⟨a, ha, b, hb, hab⟩ := hfactN _ htt
  have hta : t * a * t⁻¹ ∈ M₂ :=
    ⟨M.mul_mem (M.mul_mem htM ha.1) (M.inv_mem htM), conj_mem_centralizer_of_cj hts2 ha.2⟩
  have htb : t * b * t⁻¹ ∈ M₁ :=
    ⟨M.mul_mem (M.mul_mem htM hb.1) (M.inv_mem htM), conj_mem_centralizer_of_cj hts1 hb.2⟩
  have hprod : (t * b * t⁻¹) * (t * a * t⁻¹) = a * b := by
    have h1 : (t * a * t⁻¹) * (t * b * t⁻¹) = a * b := by
      calc (t * a * t⁻¹) * (t * b * t⁻¹) = t * (a * b) * t⁻¹ := by group
        _ = t * (t * t) * t⁻¹ := by rw [← hab]
        _ = t * t := by group
        _ = a * b := hab
    rw [← h1]
    exact hcomm _ htb _ hta
  have hu : a⁻¹ * (t * b * t⁻¹) = b * (t * a * t⁻¹)⁻¹ := by
    have h1 : t * b * t⁻¹ = a * (b * (t * a * t⁻¹)⁻¹) := by
      calc t * b * t⁻¹ = ((t * b * t⁻¹) * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
        _ = (a * b) * (t * a * t⁻¹)⁻¹ := by rw [hprod]
        _ = a * (b * (t * a * t⁻¹)⁻¹) := by group
    rw [h1]; group
  have hu1 : a⁻¹ * (t * b * t⁻¹) = 1 :=
    hdisj _ (M₁.mul_mem (M₁.inv_mem ha) htb)
      (by rw [hu]; exact M₂.mul_mem hb (M₂.inv_mem hta))
  have hta' : t * a * t⁻¹ = b := by
    have h1 : b * (t * a * t⁻¹)⁻¹ = 1 := by rw [← hu]; exact hu1
    exact (mul_inv_eq_one.1 h1).symm
  set s : G := a⁻¹ * t with hs
  have hsM : s ∈ M := M.mul_mem (M.inv_mem ha.1) htM
  have haN : a ∈ normalizer (X : Set G) := hM₁N a ha
  have hsN : s ∉ normalizer (X : Set G) := by
    intro hsn
    apply htn
    have : t = a * s := by rw [hs]; group
    rw [this]
    exact Subgroup.mul_mem _ haN hsn
  have hs2 : s * s = 1 := by
    have h1 : t * a⁻¹ * t⁻¹ = b⁻¹ := by
      rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ by group, hta']
    calc s * s = a⁻¹ * (t * a⁻¹ * t⁻¹) * (t * t) := by rw [hs]; group
      _ = a⁻¹ * b⁻¹ * (a * b) := by rw [h1, hab]
      _ = 1 := by rw [hcomm a ha b hb]; group
  obtain ⟨hss1, hss2⟩ := hTC.swap hsM hsN
  have hs₁ : ∀ x ∈ M₁, s * x * s⁻¹ ∈ M₂ := fun x hx =>
    ⟨M.mul_mem (M.mul_mem hsM hx.1) (M.inv_mem hsM), conj_mem_centralizer_of_cj hss2 hx.2⟩
  have hs₂ : ∀ x ∈ M₂, s * x * s⁻¹ ∈ M₁ := fun x hx =>
    ⟨M.mul_mem (M.mul_mem hsM hx.1) (M.inv_mem hsM), conj_mem_centralizer_of_cj hss1 hx.2⟩
  have hcosets : ∀ m ∈ M, m ∈ N ∨ m * s⁻¹ ∈ N := by
    intro m hm
    by_cases hmn : m ∈ normalizer (X : Set G)
    · exact Or.inl ⟨hm, hmn⟩
    · right
      refine ⟨M.mul_mem hm (M.inv_mem hsM), ?_⟩
      show m * s⁻¹ ∈ normalizer (X : Set G)
      rw [mem_normalizer_iff_cj, cj_mul, cj_inv_eq hss2, (hTC.swap hm hmn).2]
  obtain ⟨φ⟩ := nonempty_mulEquiv_perm_four hX hXM₁ (fun m hm => hM₁N m hm)
    (fun m hm hcom => hK0 m hm.1 (mem_centralizer_iff.2 fun x hx => (hcom x hx).symm) hm.2)
    ⟨a₀, ha₀M₁, ha₀X⟩
  exact nonempty_mulEquiv_wreath M N M₁ M₂ s (fun x hx => hx.1) hsM
    (fun x hx => ⟨hx.1, hM₁N x hx⟩) (fun x hx => ⟨hx.1, hM₂N x hx⟩) hcomm hdisj hs2
    (fun hsn => hsN hsn.2) hcosets hfactN hs₁ hs₂ φ

end WreathAssembly

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

private theorem conj_mem_inf_centralizer (h : Hyp153 G T Mc M) {m k : G} (hm : m ∈ M)
    (hk : k ∈ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) :
    m * k * m⁻¹ ∈ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_Y153 Mc M hm) k).mp hk.1, ?_⟩
  have hmn : m ∈ Subgroup.normalizer ((Subgroup.centralizer (VZ T M : Set G) : Subgroup G) :
      Set G) := B2F.le_normalizer_centralizer h.le_normalizer hm
  exact (Subgroup.mem_normalizer_iff.mp hmn k).mp hk.2

theorem inf_centralizer_le_of_pCoreOf_le (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (hEq : pCoreOf 2 (Y153 Mc M) ≤ VZ T M) :
    Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ VZ T M := by
  set Y := Y153 Mc M with hYdef
  set V := VZ T M with hVdef
  set K : Subgroup G := Y ⊓ Subgroup.centralizer (V : Set G) with hK
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := h.elemAbelian.2
  have hYM : Y ≤ M := Y153_le Mc M
  obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ h.T_le
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtfe.qtke.2.1 M h.inM.1.1 ⟨S, hSM⟩
  set Q : Subgroup G := pCoreOf 2 M with hQ
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := fun m hm => by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => h.conj_mem_inf_centralizer hm hk, fun hk => ?_⟩
    have := h.conj_mem_inf_centralizer (M.inv_mem hm) hk
    have e : m⁻¹ * (m * k * m⁻¹) * m⁻¹⁻¹ = k := by group
    rw [e] at this
    exact this
  have hKQ : K ⊓ Q ≤ V := by
    refine le_trans ?_ hEq
    refine le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans inf_le_left) ?_
      ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hMK (hYM hy), le_normalizer_pCoreOf 2 M (hYM hy)⟩
  have hcube : ∀ x ∈ K, x ^ 3 = 1 → x = 1 := by
    intro x hxK hx3
    have hxM : x ∈ M := hYM hxK.1
    have hxQ : x ∈ Q := by
      apply hF
      refine ⟨hxM, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      have hqM : q ∈ M := pCoreOf_le 2 M hq
      obtain ⟨c, hc⟩ : ∃ c : G, c = x * q * x⁻¹ * q⁻¹ := ⟨_, rfl⟩
      have hcK : c ∈ K := by
        have e : c = x * (q * x⁻¹ * q⁻¹) := by rw [hc]; group
        rw [e]
        exact K.mul_mem hxK (h.conj_mem_inf_centralizer hqM (K.inv_mem hxK))
      have hcQ : c ∈ Q := by
        have e : c = (x * q * x⁻¹) * q⁻¹ := by rw [hc]
        rw [e]
        exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M hxM) q).mp hq)
          (Q.inv_mem hq)
      have hcV : c ∈ V := hKQ ⟨hcK, hcQ⟩
      have hc2 : c ^ 2 = 1 := hV2 c hcV
      have hxc : c * x = x * c := Subgroup.mem_centralizer_iff.1 hxK.2 c hcV
      have e1 : x * q * x⁻¹ = c * q := by rw [hc]; group
      have e2 : x * (c * q) * x⁻¹ = q := by
        calc x * (c * q) * x⁻¹ = (x * c * x⁻¹) * (x * q * x⁻¹) := by group
          _ = c * (c * q) := by
            rw [show x * c * x⁻¹ = c by rw [← hxc]; group, e1]
          _ = c ^ 2 * q := by rw [pow_two]; group
          _ = q := by rw [hc2, one_mul]
      have e4 : x ^ 2 * q * (x ^ 2)⁻¹ = q := by
        calc x ^ 2 * q * (x ^ 2)⁻¹ = x * (x * q * x⁻¹) * x⁻¹ := by rw [pow_two]; group
          _ = x * (c * q) * x⁻¹ := by rw [e1]
          _ = q := e2
      have e5 : (x ^ 2)⁻¹ * q * x ^ 2 = q := by
        calc (x ^ 2)⁻¹ * q * x ^ 2 = (x ^ 2)⁻¹ * (x ^ 2 * q * (x ^ 2)⁻¹) * x ^ 2 := by rw [e4]
          _ = q := by group
      have hxinv : x⁻¹ = x ^ 2 := by
        calc x⁻¹ = x ^ 3 * x⁻¹ := by rw [hx3, one_mul]
          _ = x ^ 2 := by group
      have hx_eq : x = (x ^ 2)⁻¹ := by
        calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
          _ = (x ^ 2)⁻¹ := by rw [hx3, one_mul]
      have e3 : x * q * x⁻¹ = q := by
        calc x * q * x⁻¹ = (x ^ 2)⁻¹ * q * x ^ 2 := by rw [← hx_eq, ← hxinv]
          _ = q := e5
      have : x * q = q * x := by
        calc x * q = (x * q * x⁻¹) * x := by group
          _ = q * x := by rw [e3]
      exact this.symm
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 M) ⟨x, hxQ⟩
    have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 : x ^ Nat.gcd (2 ^ n) 3 = 1 := pow_gcd_eq_one.mpr ⟨hxn, hx3⟩
    have hg : Nat.gcd (2 ^ n) 3 = 1 := by
      apply Nat.Coprime.pow_left
      norm_num
    rwa [hg, pow_one] at h1
  have hk2 : ∀ k ∈ K, k ^ 2 = 1 := by
    intro k hk
    have hk3 : k ^ 3 ∈ pCoreOf 2 Y := h.pow_three_mem_pCoreOf_Y153 h113 hk.1
    have hk6 : k ^ 6 = 1 := by
      have := hV2 _ (hEq hk3)
      calc k ^ 6 = (k ^ 3) ^ 2 := by rw [← pow_mul]
        _ = 1 := this
    have hx : (k ^ 4) ^ 3 = 1 := by
      calc (k ^ 4) ^ 3 = (k ^ 6) ^ 2 := by rw [← pow_mul, ← pow_mul]
        _ = 1 := by rw [hk6, one_pow]
    have hk4 : k ^ 4 = 1 := hcube (k ^ 4) (K.pow_mem hk 4) hx
    calc k ^ 2 = k ^ 6 * (k ^ 4)⁻¹ := by group
      _ = 1 := by rw [hk6, hk4]; simp
  have hKp : IsPGroup 2 K := fun g => ⟨1, Subtype.ext (by simpa using hk2 (g : G) g.2)⟩
  exact (le_pCoreOf_of_le_normalizer 2 (inf_le_left : K ≤ Y) (fun y hy => hMK (hYM hy)) hKp).trans
    hEq

end Hyp153

section Pair

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

private def blockOf {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (L : Subgroup (MulAut (IntMod V hV))) : Subgroup G :=
  (commV L).map (inclMod hV)

omit [Finite G] in
private theorem cj_map_inclMod {V : Subgroup G} (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) (A : Subgroup (IntMod V hV)) :
    cj m (A.map (inclMod hV)) = (A.map (convI hV ⟨m, hm⟩).toMonoidHom).map (inclMod hV) := by
  ext x
  rw [mem_cj_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨convI hV ⟨m, hm⟩ u, Subgroup.mem_map.2 ⟨u, hu, rfl⟩, ?_⟩
    rw [inclMod_apply, inclMod_apply, convI_apply_val]
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
    refine ⟨inclMod hV u, Subgroup.mem_map.2 ⟨u, hu, rfl⟩, ?_⟩
    rw [inclMod_apply, inclMod_apply]
    exact (convI_apply_val hV ⟨m, hm⟩ u).symm

omit [Finite G] in
private theorem cj_blockOf_pair {V M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) {L L' : Subgroup (MulAut (IntMod V hV))}
    {tb : MulAut (IntMod V hV)} (hS : OfourStruct (autI hV M) L L' tb) {m : G} (hm : m ∈ M) :
    (cj m (blockOf hV L) = blockOf hV L ∧ cj m (blockOf hV L') = blockOf hV L') ∨
      (cj m (blockOf hV L) = blockOf hV L' ∧ cj m (blockOf hV L') = blockOf hV L) := by
  have hmN := hMN hm
  have hg : convI hV ⟨m, hmN⟩ ∈ autI hV M := convI_mem_autI hV hm hmN
  rcases hS.perm _ hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    unfold blockOf
    rw [cj_map_inclMod hV hmN, cj_map_inclMod hV hmN, commV_map_conjAut, commV_map_conjAut,
      h1, h2]
    exact ⟨rfl, rfl⟩
  · right
    unfold blockOf
    rw [cj_map_inclMod hV hmN, cj_map_inclMod hV hmN, commV_map_conjAut, commV_map_conjAut,
      h1, h2]
    exact ⟨rfl, rfl⟩

omit [Finite G] in
private theorem cj_centralizer (m : G) (B : Subgroup G) :
    cj m (Subgroup.centralizer (B : Set G)) =
      Subgroup.centralizer ((cj m B : Subgroup G) : Set G) := by
  ext x
  rw [mem_cj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    obtain ⟨b, hb, rfl⟩ := mem_cj_iff.1 hy
    have := hx b hb
    calc m * b * m⁻¹ * x = m * (b * (m⁻¹ * x * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * x * m) * b) * m⁻¹ := by rw [this]
      _ = x * (m * b * m⁻¹) := by group
  · intro hx b hb
    have := hx (m * b * m⁻¹) (conj_mem_cj hb)
    calc b * (m⁻¹ * x * m) = m⁻¹ * ((m * b * m⁻¹) * x) * m := by group
      _ = m⁻¹ * (x * (m * b * m⁻¹)) * m := by rw [this]
      _ = (m⁻¹ * x * m) * b := by group

omit [Finite G] in
private theorem cj_blockOf_swap {V M : Subgroup G} (hV : IsElemAbelian 2 V)
    {L L' : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}
    (hS : OfourStruct (autI hV M) L L' tb) {g : G} (hgN : g ∈ Subgroup.normalizer (V : Set G))
    (hg : convI hV ⟨g, hgN⟩ = tb) :
    cj g (blockOf hV L') = blockOf hV L := by
  unfold blockOf
  rw [cj_map_inclMod hV hgN, hg, commV_map_conjAut, hS.conj₂]

private theorem cj_oTwoUpper_inf_centralizer {m : G} (hm : m ∈ M) (B : Subgroup G) :
    cj m (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (B : Set G))) =
      oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer ((cj m B : Subgroup G) : Set G)) := by
  have hY : cj m (Y153 Mc M) = Y153 Mc M :=
    mem_normalizer_iff_cj.1 (le_normalizer_Y153 Mc M hm)
  have e1 : cj m (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (B : Set G))) =
      oTwoUpper (cj m (Y153 Mc M ⊓ Subgroup.centralizer (B : Set G))) :=
    (oTwoUpper_map (MulAut.conj m).toMonoidHom _).symm
  have e2 : cj m (Y153 Mc M ⊓ Subgroup.centralizer (B : Set G)) =
      cj m (Y153 Mc M) ⊓ cj m (Subgroup.centralizer (B : Set G)) :=
    Subgroup.map_inf _ _ _ (MulAut.conj m).injective
  rw [e1, e2, hY, cj_centralizer]

end Pair

section ModelCube

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {U : Subgroup W}

private theorem eq_one_or_eq_or_eq_inv_of_cube (hN : ActsAsNaturalL2 L U) {x c : MulAut W} (hx : x ∈ L)
    (hc : c ∈ L) (hx3 : x ^ 3 = 1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    x = 1 ∨ x = c ∨ x = c⁻¹ := by
  obtain ⟨hxc3, hxc⟩ := cube_mul_of_cube hN hx hc hx3 hc3
  obtain ⟨e, -, -⟩ := hN
  have hc3' : (e ⟨c, hc⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hc⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hc1' : e ⟨c, hc⟩ ≠ 1 := by
    intro h1
    apply hc1
    have h' : (⟨c, hc⟩ : L) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h'
  have hcomm : e ⟨x, hx⟩ * e ⟨c, hc⟩ = e ⟨c, hc⟩ * e ⟨x, hx⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxc
  rcases S1417.SL2_cent_three _ _ hc3' hc1' hcomm with h1 | h1 | h1
  · left
    have h' : (⟨x, hx⟩ : L) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h'
  · right; left
    have h' : (⟨x, hx⟩ : L) = ⟨c, hc⟩ := e.injective h1
    exact congrArg Subtype.val h'
  · right; right
    have h' : (⟨x, hx⟩ : L) = ⟨c, hc⟩⁻¹ := e.injective (by rw [h1, map_inv])
    exact congrArg Subtype.val h'

end ModelCube

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

private theorem exists_cube_elt (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (hEq : pCoreOf 2 (Y153 Mc M) ≤ VZ T M)
    {L L' : Subgroup (MulAut (IntMod (VZ T M) h.elemAbelian))}
    {tb : MulAut (IntMod (VZ T M) h.elemAbelian)}
    (hS : OfourStruct (autI h.elemAbelian M) L L' tb) :
    ∃ c : G, c ∈ Y153 Mc M ∧ c ∈ Subgroup.centralizer (blockOf h.elemAbelian L' : Set G) ∧
      c ^ 3 = 1 ∧ ∃ hcN : c ∈ Subgroup.normalizer (VZ T M : Set G),
        convI h.elemAbelian ⟨c, hcN⟩ ∈ L ∧ convI h.elemAbelian ⟨c, hcN⟩ ≠ 1 := by
  have hV := h.elemAbelian
  obtain ⟨x₁, hx₁L, hx₁3, hx₁1⟩ := exists_orderThree hS.nat₁
  have hodd : Odd (orderOf x₁) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hx₁3)
  have hx₁P : x₁ ∈ oTwoUpper (autI hV M) := mem_oTwoUpper_of_odd (hS.L₁_le hx₁L) hodd
  have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
  rw [← e] at hx₁P
  obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hx₁P
  have hgN : (g : G) ∈ Subgroup.normalizer (VZ T M : Set G) := g.2
  have hg3 : ((g : G) ^ 3) ^ 2 = 1 := h.elemAbelian.2 _ (hEq (h.pow_three_mem_pCoreOf_Y153 h113 hgY))
  have hgC : (g : G) ∈ Subgroup.centralizer (blockOf hV L' : Set G) :=
    (mem_centralizer_map_inclMod_iff hV hgN (commV L')).2 fun u hu => by
      rw [hg]; exact hS.L₁_fix₂ hx₁L hu
  have hcN : (g : G) ^ 4 ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.pow_mem _ hgN 4
  have hconv : convI hV ⟨(g : G) ^ 4, hcN⟩ = x₁ := by
    have : (⟨(g : G) ^ 4, hcN⟩ : Subgroup.normalizer (VZ T M : Set G)) = g ^ 4 :=
      Subtype.ext (by simp)
    rw [this, map_pow, hg]
    calc x₁ ^ 4 = x₁ ^ 3 * x₁ := by rw [pow_succ]
      _ = x₁ := by rw [hx₁3, one_mul]
  refine ⟨(g : G) ^ 4, Subgroup.pow_mem _ hgY 4, Subgroup.pow_mem _ hgC 4, ?_, hcN, ?_, ?_⟩
  · calc ((g : G) ^ 4) ^ 3 = (((g : G) ^ 3) ^ 2) ^ 2 := by rw [← pow_mul, ← pow_mul, ← pow_mul]
      _ = 1 := by rw [hg3, one_pow]
  · rw [hconv]; exact hx₁L
  · rw [hconv]; exact hx₁1

private theorem fpf_of_cube_elt (h : Hyp153 G T Mc M)
    {L L' : Subgroup (MulAut (IntMod (VZ T M) h.elemAbelian))}
    {tb : MulAut (IntMod (VZ T M) h.elemAbelian)}
    (hS : OfourStruct (autI h.elemAbelian M) L L' tb) {c : G} (hc3 : c ^ 3 = 1)
    (hcN : c ∈ Subgroup.normalizer (VZ T M : Set G))
    (hcL : convI h.elemAbelian ⟨c, hcN⟩ ∈ L) (hc1 : convI h.elemAbelian ⟨c, hcN⟩ ≠ 1) :
    ∀ u ∈ blockOf h.elemAbelian L, u ≠ 1 → c * u * c⁻¹ ≠ u := by
  have hV := h.elemAbelian
  intro u hu hu1 hfix
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hu
  have hw1 : w ≠ 1 := fun h' => hu1 (by rw [h']; rfl)
  have hcw : convI hV ⟨c, hcN⟩ w = w := by
    apply IntMod.val_injective
    rw [convI_apply_val]
    exact hfix
  have hcube : (convI hV ⟨c, hcN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcN⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hodd : Odd (orderOf (convI hV ⟨c, hcN⟩)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hcube)
  exact hc1 (eq_one_of_odd_of_fixed hS.nat₁ (fun l hl u hu => commV_stable L hl hu) hcL hodd hw hw1
    hcw)

private theorem a4Data_blockOf (h : Hyp153 G T Mc M)
    {L L' : Subgroup (MulAut (IntMod (VZ T M) h.elemAbelian))}
    {tb : MulAut (IntMod (VZ T M) h.elemAbelian)}
    (hS : OfourStruct (autI h.elemAbelian M) L L' tb) {c : G} (hc3 : c ^ 3 = 1)
    (hcN : c ∈ Subgroup.normalizer (VZ T M : Set G))
    (hcL : convI h.elemAbelian ⟨c, hcN⟩ ∈ L) (hc1 : convI h.elemAbelian ⟨c, hcN⟩ ≠ 1) :
    A4Data (blockOf h.elemAbelian L ⊔ Subgroup.zpowers c) (blockOf h.elemAbelian L) c := by
  have hV := h.elemAbelian
  have hle : blockOf hV L ≤ VZ T M := map_inclMod_le hV _
  have hcne : c ≠ 1 := fun h' => hc1 (by
    have : (⟨c, hcN⟩ : Subgroup.normalizer (VZ T M : Set G)) = 1 := Subtype.ext h'
    rw [this, map_one])
  have hord : orderOf c = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hc3 hcne
  refine a4Data_of_data ?_ (fun w hw => h.elemAbelian.2 w (hle hw))
    (fun u hu v hv => B2F.isElemAbelian_comm h.elemAbelian (hle hu) (hle hv)) hord ?_
    (fpf_of_cube_elt h hS hc3 hcN hcL hc1)
  · unfold blockOf
    rw [Subgroup.card_map_of_injective (inclMod_injective hV)]
    exact (card_of_actsAsNaturalL2 hS.nat₁).2
  · refine (mem_normalizer_map_inclMod_iff hV hcN (commV L)).2 ?_
    exact mem_stabSub_of_forall (fun u hu => commV_stable L hcL hu)
      (fun u hu => commV_stable L (L.inv_mem hcL) hu)

private theorem convI_mem_of_mem_inf_centralizer (h : Hyp153 G T Mc M)
    {L L' : Subgroup (MulAut (IntMod (VZ T M) h.elemAbelian))}
    {tb : MulAut (IntMod (VZ T M) h.elemAbelian)}
    (hS : OfourStruct (autI h.elemAbelian M) L L' tb) {x : G} (hxY : x ∈ Y153 Mc M)
    (hxC : x ∈ Subgroup.centralizer (blockOf h.elemAbelian L' : Set G)) :
    ∃ hxN : x ∈ Subgroup.normalizer (VZ T M : Set G), convI h.elemAbelian ⟨x, hxN⟩ ∈ L := by
  have hV := h.elemAbelian
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) :=
    ((Y153_le Mc M).trans h.le_normalizer) hxY
  have hmem : convI hV ⟨x, hxN⟩ ∈ autI hV M := convI_mem_autI hV (Y153_le Mc M hxY) hxN
  refine ⟨hxN, (hS.mem_L₁_iff hmem).2 ?_⟩
  exact (mem_centralizer_map_inclMod_iff hV hxN (commV L')).1 hxC

private theorem oTwoUpper_inf_centralizer_eq (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (hEq : pCoreOf 2 (Y153 Mc M) ≤ VZ T M)
    {L L' : Subgroup (MulAut (IntMod (VZ T M) h.elemAbelian))}
    {tb : MulAut (IntMod (VZ T M) h.elemAbelian)}
    (hS : OfourStruct (autI h.elemAbelian M) L L' tb) {c : G} (hcY : c ∈ Y153 Mc M)
    (hcC : c ∈ Subgroup.centralizer (blockOf h.elemAbelian L' : Set G)) (hc3 : c ^ 3 = 1)
    (hcN : c ∈ Subgroup.normalizer (VZ T M : Set G))
    (hcL : convI h.elemAbelian ⟨c, hcN⟩ ∈ L) (hc1 : convI h.elemAbelian ⟨c, hcN⟩ ≠ 1) :
    oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf h.elemAbelian L' : Set G)) =
      blockOf h.elemAbelian L ⊔ Subgroup.zpowers c := by
  have hV := h.elemAbelian
  have hC := h.inf_centralizer_le_of_pCoreOf_le h113 hEq
  have hA4 := a4Data_blockOf h hS hc3 hcN hcL hc1
  have hleL : blockOf hV L ≤ VZ T M := map_inclMod_le hV _
  have hleL' : blockOf hV L' ≤ VZ T M := map_inclMod_le hV _
  have hVY : VZ T M ≤ Y153 Mc M := h.VZ_le_Y153 h113
  have hcodd : Odd (orderOf c) := by
    have hcne : c ≠ 1 := fun h' => hc1 (by
      have : (⟨c, hcN⟩ : Subgroup.normalizer (VZ T M : Set G)) = 1 := Subtype.ext h'
      rw [this, map_one])
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [orderOf_eq_prime hc3 hcne]
    decide
  apply le_antisymm
  · refine oTwoUpper_le_of_pow_mem fun x hx => ⟨1, ?_⟩
    obtain ⟨hxN, hxL⟩ := convI_mem_of_mem_inf_centralizer h hS hx.1 hx.2
    have hxbar : convI hV ⟨x, hxN⟩ ∈ oTwoUpper (autI hV M) := by
      have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
      rw [← e]
      exact convI_mem_autI hV hx.1 hxN
    have hx3 : (convI hV ⟨x, hxN⟩) ^ 3 = 1 := hS.pow_three_of_mem_oTwoUpper hxbar
    have hcube : (convI hV ⟨c, hcN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨c, hcN⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hc3)
      rw [this, map_one]
    obtain ⟨j, hj⟩ : ∃ j : ℤ, convI hV ⟨x, hxN⟩ = (convI hV ⟨c, hcN⟩) ^ j := by
      rcases eq_one_or_eq_or_eq_inv_of_cube hS.nat₁ hxL hcL hx3 hcube hc1 with h1 | h1 | h1
      · exact ⟨0, by rw [h1]; simp⟩
      · exact ⟨1, by rw [h1]; simp⟩
      · exact ⟨-1, by rw [h1]; simp⟩
    have hcj : c ^ j ∈ Subgroup.normalizer (VZ T M : Set G) := zpow_mem hcN j
    have hvN : x * (c ^ j)⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hcj)
    have hvY : x * (c ^ j)⁻¹ ∈ Y153 Mc M :=
      Subgroup.mul_mem _ hx.1 (Subgroup.inv_mem _ (zpow_mem hcY j))
    have hvC : x * (c ^ j)⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := by
      refine (convI_eq_one_iff hV ⟨x * (c ^ j)⁻¹, hvN⟩).1 ?_
      have e : (⟨x * (c ^ j)⁻¹, hvN⟩ : Subgroup.normalizer (VZ T M : Set G)) =
          ⟨x, hxN⟩ * (⟨c, hcN⟩ ^ j)⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_inv, map_zpow, hj, mul_inv_cancel]
    have hvV : x * (c ^ j)⁻¹ ∈ VZ T M := hC ⟨hvY, hvC⟩
    obtain ⟨w, hw⟩ := IntMod.exists_eq_mk (hV := hV) (⟨x * (c ^ j)⁻¹, hvV⟩ : VZ T M)
    obtain ⟨u₁, hu₁, u₂, hu₂, hwu⟩ := hS.exists_decomp_W w
    have hxe : x * (c ^ j)⁻¹ = u₁.val * u₂.val := by
      have := congrArg IntMod.val hwu
      rw [IntMod.val_mul] at this
      have h2 : w.val = x * (c ^ j)⁻¹ := hw
      rw [← h2]; exact this
    set a : G := u₁.val with ha
    set b : G := u₂.val with hb
    have haL : a ∈ blockOf hV L := Subgroup.mem_map.2 ⟨u₁, hu₁, rfl⟩
    have hbL' : b ∈ blockOf hV L' := Subgroup.mem_map.2 ⟨u₂, hu₂, rfl⟩
    have hxeq : x = (a * c ^ j) * b := by
      have : x = (x * (c ^ j)⁻¹) * c ^ j := by group
      rw [this, hxe]
      have hcb : c ^ j * b = b * c ^ j :=
        (Subgroup.mem_centralizer_iff.1 (zpow_mem hcC j) b hbL').symm
      calc a * b * c ^ j = a * (b * c ^ j) := by group
        _ = a * (c ^ j * b) := by rw [hcb]
        _ = a * c ^ j * b := by group
    have hcomm : Commute (a * c ^ j) b := by
      have hab : a * b = b * a := B2F.isElemAbelian_comm hV (hleL haL) (hleL' hbL')
      have hcb : c ^ j * b = b * c ^ j :=
        (Subgroup.mem_centralizer_iff.1 (zpow_mem hcC j) b hbL').symm
      show a * c ^ j * b = b * (a * c ^ j)
      calc a * c ^ j * b = a * (c ^ j * b) := by group
        _ = a * (b * c ^ j) := by rw [hcb]
        _ = (a * b) * c ^ j := by group
        _ = (b * a) * c ^ j := by rw [hab]
        _ = b * (a * c ^ j) := by group
    have hb2 : b ^ 2 = 1 := h.elemAbelian.2 b (hleL' hbL')
    have hmem : a * c ^ j ∈ blockOf hV L ⊔ Subgroup.zpowers c :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left haL)
        (Subgroup.mem_sup_right (zpow_mem (Subgroup.mem_zpowers c) j))
    have : x ^ 2 ^ 1 = (a * c ^ j) ^ 2 := by
      rw [pow_one, hxeq, Commute.mul_pow hcomm, hb2, mul_one]
    rw [this]
    exact Subgroup.pow_mem _ hmem 2
  · refine sup_le (fun u hu => ?_) (Subgroup.zpowers_le.2 ?_)
    · obtain ⟨w₀, hw₀, hw⟩ := hA4.exists_mul_conj_inv_eq hu
      have hw₀K : w₀ ∈ Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L' : Set G) :=
        ⟨hVY (hleL hw₀), Subgroup.mem_centralizer_iff.2 fun b hb =>
          B2F.isElemAbelian_comm hV (hleL' hb) (hleL hw₀)⟩
      have hcK : c ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L' : Set G)) :=
        mem_oTwoUpper_of_odd ⟨hcY, hcC⟩ hcodd
      have h1 : w₀ * c * w₀⁻¹ ∈
          oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L' : Set G)) :=
        conj_mem_oTwoUpper (Subgroup.le_normalizer hw₀K) hcK
      have e : u = (w₀ * c * w₀⁻¹) * c⁻¹ := by rw [← hw]; group
      rw [e]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hcK)
    · exact mem_oTwoUpper_of_odd ⟨hcY, hcC⟩ hcodd

private theorem inf_centralizer_eq_bot (h : Hyp153 G T Mc M)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) h.elemAbelian))}
    {tb : MulAut (IntMod (VZ T M) h.elemAbelian)}
    (hS : OfourStruct (autI h.elemAbelian M) L₁ L₂ tb) {c₁ c₂ : G}
    (hc₁fpf : ∀ u ∈ blockOf h.elemAbelian L₁, u ≠ 1 → c₁ * u * c₁⁻¹ ≠ u)
    (hc₂fpf : ∀ u ∈ blockOf h.elemAbelian L₂, u ≠ 1 → c₂ * u * c₂⁻¹ ≠ u)
    (hc₁C : c₁ ∈ Subgroup.centralizer (blockOf h.elemAbelian L₂ : Set G))
    (hc₂C : c₂ ∈ Subgroup.centralizer (blockOf h.elemAbelian L₁ : Set G))
    {A : Subgroup G} (hc₁A : c₁ ∈ A) (hc₂A : c₂ ∈ A)
    (hMA : M ≤ Subgroup.normalizer (A : Set G)) :
    M ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
  have hV := h.elemAbelian
  obtain ⟨Sy, hSy⟩ := h.qtfe.exists_sylow
  have hO2T : pCoreOf 2 M ≤ T := by
    have := pCoreOf_two_le_sylow M Sy (hSy ▸ h.T_le)
    rwa [hSy] at this
  have hMCA : M ≤ Subgroup.normalizer
      ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_centralizer hMA
  have hT0 : T ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    by_contra hne
    have hn : T ≤ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hMCA (h.T_le ht)⟩
    obtain ⟨z, hzU, hz1, hz2, hzc⟩ :=
      exists_central_involution_of_normal h.qtfe.sylow.1 inf_le_left hne hn
    have hzZ : z ∈ quasithinOmegaOneCenter T :=
      Subgroup.subset_closure ⟨⟨hzU.1, Subgroup.mem_centralizer_iff.2 hzc⟩, hz2⟩
    have hzV : z ∈ VZ T M := h.Z_le_VZ hzZ
    obtain ⟨w, hw⟩ := IntMod.exists_eq_mk (hV := hV) (⟨z, hzV⟩ : VZ T M)
    obtain ⟨u₁, hu₁, u₂, hu₂, hwu⟩ := hS.exists_decomp_W w
    have hze : z = u₁.val * u₂.val := by
      have h1 := congrArg IntMod.val hwu
      rw [IntMod.val_mul] at h1
      have h2 : w.val = z := hw
      rw [← h2]; exact h1
    have haU : u₁.val ∈ blockOf hV L₁ := Subgroup.mem_map.2 ⟨u₁, hu₁, rfl⟩
    have hbU : u₂.val ∈ blockOf hV L₂ := Subgroup.mem_map.2 ⟨u₂, hu₂, rfl⟩
    have hzc₁ : c₁ * z = z * c₁ := Subgroup.mem_centralizer_iff.1 hzU.2 c₁ hc₁A
    have hzc₂ : c₂ * z = z * c₂ := Subgroup.mem_centralizer_iff.1 hzU.2 c₂ hc₂A
    have hbc₁ : u₂.val * c₁ = c₁ * u₂.val := Subgroup.mem_centralizer_iff.1 hc₁C _ hbU
    have hac₂ : u₁.val * c₂ = c₂ * u₁.val := Subgroup.mem_centralizer_iff.1 hc₂C _ haU
    have ha1 : u₁.val = 1 := by
      by_contra ha1
      apply hc₁fpf _ haU ha1
      have h1 : c₁ * u₁.val = u₁.val * c₁ := by
        have : c₁ * (u₁.val * u₂.val) * c₁⁻¹ = u₁.val * u₂.val := by
          rw [← hze]; calc c₁ * z * c₁⁻¹ = (z * c₁) * c₁⁻¹ := by rw [hzc₁]
            _ = z := by group
        have h2 : c₁ * u₁.val * c₁⁻¹ * u₂.val = u₁.val * u₂.val := by
          calc c₁ * u₁.val * c₁⁻¹ * u₂.val = c₁ * u₁.val * (c₁⁻¹ * u₂.val * c₁) * c₁⁻¹ := by group
            _ = c₁ * u₁.val * (u₂.val) * c₁⁻¹ := by
              rw [show c₁⁻¹ * u₂.val * c₁ = u₂.val by
                calc c₁⁻¹ * u₂.val * c₁ = c₁⁻¹ * (u₂.val * c₁) := by group
                  _ = c₁⁻¹ * (c₁ * u₂.val) := by rw [hbc₁]
                  _ = u₂.val := by group]
            _ = u₁.val * u₂.val := by rw [← this]; group
        have h3 := mul_right_cancel h2
        calc c₁ * u₁.val = (c₁ * u₁.val * c₁⁻¹) * c₁ := by group
          _ = u₁.val * c₁ := by rw [h3]
      calc c₁ * u₁.val * c₁⁻¹ = (u₁.val * c₁) * c₁⁻¹ := by rw [h1]
        _ = u₁.val := by group
    have hb1 : u₂.val = 1 := by
      by_contra hb1
      apply hc₂fpf _ hbU hb1
      have h1 : c₂ * u₂.val = u₂.val * c₂ := by
        have : c₂ * (u₁.val * u₂.val) * c₂⁻¹ = u₁.val * u₂.val := by
          rw [← hze]; calc c₂ * z * c₂⁻¹ = (z * c₂) * c₂⁻¹ := by rw [hzc₂]
            _ = z := by group
        have h2 : u₁.val * (c₂ * u₂.val * c₂⁻¹) = u₁.val * u₂.val := by
          calc u₁.val * (c₂ * u₂.val * c₂⁻¹) = (c₂ * u₁.val * c₂⁻¹) * (c₂ * u₂.val * c₂⁻¹) := by
                rw [show c₂ * u₁.val * c₂⁻¹ = u₁.val by
                  calc c₂ * u₁.val * c₂⁻¹ = (u₁.val * c₂) * c₂⁻¹ := by rw [hac₂]
                    _ = u₁.val := by group]
            _ = c₂ * (u₁.val * u₂.val) * c₂⁻¹ := by group
            _ = u₁.val * u₂.val := this
        have h3 := mul_left_cancel h2
        calc c₂ * u₂.val = (c₂ * u₂.val * c₂⁻¹) * c₂ := by group
          _ = u₂.val * c₂ := by rw [h3]
      calc c₂ * u₂.val * c₂⁻¹ = (u₂.val * c₂) * c₂⁻¹ := by rw [h1]
        _ = u₂.val := by group
    exact hz1 (by rw [hze, ha1, hb1, mul_one])
  have hQnorm : ∀ m ∈ M, ∀ q ∈ M ⊓ Subgroup.centralizer (A : Set G),
      m * q * m⁻¹ ∈ M ⊓ Subgroup.centralizer (A : Set G) := fun m hm q hq =>
    ⟨M.mul_mem (M.mul_mem hm hq.1) (M.inv_mem hm),
      (Subgroup.mem_normalizer_iff.mp (hMCA hm) q).mp hq.2⟩
  rw [eq_bot_iff]
  intro q hq
  have hqM : q ∈ M := hq.1
  have hqO : q ∈ pCoreOf 2 M := by
    obtain ⟨S', hS'⟩ := h.qtfe.exists_sylow
    have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
      h.qtfe.qtke.2.1 M h.inM.1.1 ⟨S', hS' ▸ h.T_le⟩
    apply hF
    refine ⟨hqM, Subgroup.mem_centralizer_iff.2 fun o ho => ?_⟩
    have hoM : o ∈ M := pCoreOf_le 2 M ho
    have hcom : q * o * q⁻¹ * o⁻¹ ∈ T ⊓ Subgroup.centralizer (A : Set G) := by
      refine ⟨hO2T ?_, ?_⟩
      · exact (pCoreOf 2 M).mul_mem
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M hqM) o).mp ho)
          ((pCoreOf 2 M).inv_mem ho)
      · have e : q * o * q⁻¹ * o⁻¹ = q * (o * q⁻¹ * o⁻¹) := by group
        rw [e]
        exact ((M ⊓ Subgroup.centralizer (A : Set G)).mul_mem hq
          (hQnorm o hoM q⁻¹ ((M ⊓ Subgroup.centralizer (A : Set G)).inv_mem hq))).2
    rw [hT0, Subgroup.mem_bot] at hcom
    calc o * q = (q * o * q⁻¹ * o⁻¹)⁻¹ * (q * o) := by group
      _ = q * o := by rw [hcom]; group
  have hqT : q ∈ T ⊓ Subgroup.centralizer (A : Set G) := ⟨hO2T hqO, hq.2⟩
  rw [hT0] at hqT
  exact hqT

private theorem exists_outer_elt (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) h.elemAbelian))}
    {tb : MulAut (IntMod (VZ T M) h.elemAbelian)}
    (hS : OfourStruct (autI h.elemAbelian M) L₁ L₂ tb) {c₂ : G}
    (hA₂ : A4Data (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
      (blockOf h.elemAbelian L₁ : Set G))) (blockOf h.elemAbelian L₂) c₂) :
    ∃ a ∈ M ⊓ Subgroup.centralizer ((oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
        (blockOf h.elemAbelian L₁ : Set G)) : Subgroup G) : Set G),
      a ∉ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf h.elemAbelian L₂ : Set G)) := by
  have hV := h.elemAbelian
  have hleL₂ : blockOf hV L₂ ≤ VZ T M := map_inclMod_le hV _
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts h.isSylowTwoOf_autI
  have hs₁L : s₁ ∈ L₁ := hF.sylow.s₁_mem_L
  have hs₁T : s₁ ∈ autI hV T := hF.sylow.s₁_mem_S.1
  have hs₁1 : s₁ ≠ 1 := hF.sylow.s₁_ne
  have hs₁sq : s₁ * s₁ = 1 := hF.s₁_sq
  obtain ⟨g, hgT, hg⟩ := (mem_autI hV).1 hs₁T
  have hgN : (g : G) ∈ Subgroup.normalizer (VZ T M : Set G) := g.2
  have hgM : (g : G) ∈ M := h.T_le hgT
  have hgC : (g : G) ∈ Subgroup.centralizer (blockOf hV L₂ : Set G) :=
    (mem_centralizer_map_inclMod_iff hV hgN (commV L₂)).2 fun u hu => by
      rw [hg]; exact hS.L₁_fix₂ hs₁L hu
  have hgNU₁ : (g : G) ∈ Subgroup.normalizer (blockOf hV L₁ : Set G) :=
    (mem_normalizer_map_inclMod_iff hV hgN (commV L₁)).2 (by
      rw [hg]
      exact mem_stabSub_of_forall (fun u hu => commV_stable L₁ hs₁L hu)
        (fun u hu => commV_stable L₁ (L₁.inv_mem hs₁L) hu))
  have hgNY₂ : (g : G) ∈ Subgroup.normalizer ((oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
      (blockOf hV L₁ : Set G)) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_Y153 Mc M hgM, B2F.le_normalizer_centralizer le_rfl hgNU₁⟩)
  obtain ⟨w, hw, hwc⟩ := hA₂.exists_mul_mem_centralizer hgNY₂ hgC
  have hwV : w ∈ VZ T M := hleL₂ hw
  refine ⟨w⁻¹ * g, ⟨M.mul_mem (M.inv_mem (h.T_le (h.VZ_le_T hwV))) hgM, hwc⟩, ?_⟩
  intro haY₁
  have haY : w⁻¹ * (g : G) ∈ Y153 Mc M := ((oTwoUpper_le _).trans inf_le_left) haY₁
  have haN : w⁻¹ * (g : G) ∈ Subgroup.normalizer (VZ T M : Set G) :=
    ((Y153_le Mc M).trans h.le_normalizer) haY
  have hwinvN : w⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.le_normalizer ((VZ T M).inv_mem hwV)
  have hconv1 : convI hV ⟨w⁻¹, hwinvN⟩ = 1 := by
    refine (convI_eq_one_iff hV ⟨w⁻¹, hwinvN⟩).2 ?_
    exact Subgroup.mem_centralizer_iff.2 fun v hv =>
      B2F.isElemAbelian_comm hV hv ((VZ T M).inv_mem hwV)
  have hconv : convI hV ⟨w⁻¹ * g, haN⟩ = s₁ := by
    have : (⟨w⁻¹ * (g : G), haN⟩ : Subgroup.normalizer (VZ T M : Set G)) =
        ⟨w⁻¹, hwinvN⟩ * g := Subtype.ext rfl
    rw [this, map_mul, hconv1, one_mul, hg]
  have hmem : s₁ ∈ oTwoUpper (autI hV M) := by
    have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
    rw [← e, ← hconv]
    exact convI_mem_autI hV haY haN
  have h3 : s₁ ^ 3 = 1 := hS.pow_three_of_mem_oTwoUpper hmem
  apply hs₁1
  have h4 : s₁ ^ 3 = s₁ := by
    calc s₁ ^ 3 = (s₁ * s₁) * s₁ := by rw [pow_succ, pow_two]
      _ = s₁ := by rw [hs₁sq, one_mul]
  rw [← h4]
  exact h3

private theorem twoConj_Yfac (h : Hyp153 G T Mc M)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) h.elemAbelian))}
    {tb : MulAut (IntMod (VZ T M) h.elemAbelian)}
    (hS : OfourStruct (autI h.elemAbelian M) L₁ L₂ tb)
    (hne : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf h.elemAbelian L₁ : Set G)) ≠
      oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf h.elemAbelian L₂ : Set G))) :
    TwoConj M (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
        (blockOf h.elemAbelian L₂ : Set G)))
      (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf h.elemAbelian L₁ : Set G))) := by
  have hV := h.elemAbelian
  refine ⟨hne, ?_, fun m hm => ?_⟩
  · obtain ⟨g, hgM, hg⟩ := (mem_autI hV).1 hS.t_mem
    refine ⟨g, hgM, ?_⟩
    rw [cj_oTwoUpper_inf_centralizer hgM, cj_blockOf_swap hV hS g.2 hg]
  · rw [cj_oTwoUpper_inf_centralizer hm]
    rcases cj_blockOf_pair hV h.le_normalizer hS hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h2]
    · right; rw [h2]


private theorem exists_wreath_data (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (hEq : pCoreOf 2 (Y153 Mc M) ≤ VZ T M) :
    ∃ (X Y W W' : Subgroup G) (c c' : G), A4Data X W c ∧ A4Data Y W' c' ∧ TwoConj M X Y ∧
      X ≤ M ∧ Y ≤ M ∧ (∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) ∧
      M ⊓ Subgroup.centralizer ((X ⊔ Y : Subgroup G) : Set G) = ⊥ ∧
      ∃ a ∈ M ⊓ Subgroup.centralizer (Y : Set G), a ∉ X := by
  obtain ⟨q, L₁, L₂, tb, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hV := h.elemAbelian
  obtain ⟨c₁, hc₁Y, hc₁C, hc₁3, hc₁N, hc₁L, hc₁1⟩ := exists_cube_elt h113 h hEq hS
  obtain ⟨c₂, hc₂Y, hc₂C, hc₂3, hc₂N, hc₂L, hc₂1⟩ := exists_cube_elt h113 h hEq hS.symm
  have hX₁ := oTwoUpper_inf_centralizer_eq h113 h hEq hS hc₁Y hc₁C hc₁3 hc₁N hc₁L hc₁1
  have hX₂ := oTwoUpper_inf_centralizer_eq h113 h hEq hS.symm hc₂Y hc₂C hc₂3 hc₂N hc₂L hc₂1
  have hA₁ := a4Data_blockOf h hS hc₁3 hc₁N hc₁L hc₁1
  have hA₂ := a4Data_blockOf h hS.symm hc₂3 hc₂N hc₂L hc₂1
  rw [← hX₁] at hA₁
  rw [← hX₂] at hA₂
  have hc₁Y₁ : c₁ ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
      (blockOf hV L₂ : Set G)) := by
    rw [hX₁]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c₁)
  have hc₂Y₂ : c₂ ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
      (blockOf hV L₁ : Set G)) := by
    rw [hX₂]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c₂)
  have hY₁M : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L₂ : Set G)) ≤ M :=
    (oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))
  have hY₂M : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L₁ : Set G)) ≤ M :=
    (oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))
  have hne : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L₁ : Set G)) ≠
      oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L₂ : Set G)) := by
    intro heq
    have hc₁C₁ : c₁ ∈ Subgroup.centralizer (blockOf hV L₁ : Set G) :=
      ((oTwoUpper_le _).trans inf_le_right) (heq ▸ hc₁Y₁)
    obtain ⟨u, hu, hu1⟩ := hA₁.exists_ne_one_mem_W
    apply fpf_of_cube_elt h hS hc₁3 hc₁N hc₁L hc₁1 u hu hu1
    have := Subgroup.mem_centralizer_iff.1 hc₁C₁ u hu
    calc c₁ * u * c₁⁻¹ = (u * c₁) * c₁⁻¹ := by rw [this]
      _ = u := by group
  have hTC := twoConj_Yfac h hS hne
  have hc₂NY₁ : c₂ ∈ Subgroup.normalizer ((oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
      (blockOf hV L₂ : Set G)) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_Y153 Mc M (Y153_le Mc M hc₂Y),
        B2F.le_normalizer_centralizer le_rfl hA₂.mem_normalizer⟩)
  have hc₂C₁ : c₂ ∈ Subgroup.centralizer ((oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
      (blockOf hV L₂ : Set G)) : Subgroup G) : Set G) :=
    hA₁.mem_centralizer_of_cube hc₂NY₁ hc₂C hc₂3
  have hY₁C₂ : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L₂ : Set G)) ≤
      Subgroup.centralizer (blockOf hV L₂ : Set G) := (oTwoUpper_le _).trans inf_le_right
  have hU₂C : blockOf hV L₂ ≤ Subgroup.centralizer ((oTwoUpper (Y153 Mc M ⊓
      Subgroup.centralizer (blockOf hV L₂ : Set G)) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.1 hY₁C₂
  have hY₂C : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L₁ : Set G)) ≤
      Subgroup.centralizer ((oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
        (blockOf hV L₂ : Set G)) : Subgroup G) : Set G) := by
    rw [hX₂]
    exact sup_le hU₂C (Subgroup.zpowers_le.2 hc₂C₁)
  have hcomm : ∀ x ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L₂ : Set G)),
      ∀ y ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (blockOf hV L₁ : Set G)),
        x * y = y * x := fun x hx y hy => Subgroup.mem_centralizer_iff.1 (hY₂C hy) x hx
  have hK := inf_centralizer_eq_bot h hS (fpf_of_cube_elt h hS hc₁3 hc₁N hc₁L hc₁1)
    (fpf_of_cube_elt h hS.symm hc₂3 hc₂N hc₂L hc₂1) hc₁C hc₂C (Subgroup.mem_sup_left hc₁Y₁)
    (Subgroup.mem_sup_right hc₂Y₂) hTC.le_normalizer_sup
  exact ⟨_, _, _, _, c₁, c₂, hA₁, hA₂, hTC, hY₁M, hY₂M, hcomm, hK,
    exists_outer_elt h113 h hS hA₂⟩


end Hyp153

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem VZ_lt_pCoreOf_Y153
    (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    VZ T M < pCoreOf 2 (Y153 Mc M) := by
  refine lt_of_le_of_ne (h.VZ_le_pCoreOf_Y153 h113) fun heq => ?_
  have hEq : pCoreOf 2 (Y153 Mc M) ≤ VZ T M := heq ▸ le_rfl
  obtain ⟨X, Y, W, W', c, c', hX, hY, hTC, hXM, hYM, hXY, hK, hS2⟩ :=
    exists_wreath_data h113 h hEq
  obtain ⟨φ⟩ := nonempty_mulEquiv_wreath_of_two_conj_outer h.qtfe.sylow h.T_le hX hTC hXM hYM
    hXY hK hS2
  exact A10.theorem1391 G T h.qtfe.simple h.qtfe.nonabelian h.qtfe.qtke h.qtfe.sylow M h.inM.1
    h.T_le ⟨φ⟩

end Hyp153

end CFSG.Quasithin
