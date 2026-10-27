module

public import CFSG.Quasithin.H13.A5S1327y

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.S14110

theorem mem_of_two_pow_of_odd_pow {X : Type*} [Group X] {N : Subgroup X} {x : X} {m k : ℕ}
    (hm : Odd m) (hx : x ^ 2 ^ k = 1) (hxm : x ^ m ∈ N) : x ∈ N := by
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm)
  have hg := Nat.gcd_eq_gcd_ab m (2 ^ k)
  rw [hcop.gcd_eq_one] at hg
  have h1 : (x ^ m) ^ (Nat.gcdA m (2 ^ k)) = x ^ ((m : ℤ) * Nat.gcdA m (2 ^ k)) := by
    rw [zpow_mul, zpow_natCast]
  have h2 : (x ^ (2 ^ k)) ^ (Nat.gcdB m (2 ^ k)) =
      x ^ (((2 ^ k : ℕ) : ℤ) * Nat.gcdB m (2 ^ k)) := by
    rw [zpow_mul, zpow_natCast]
  have e : x = (x ^ m) ^ (Nat.gcdA m (2 ^ k)) * (x ^ (2 ^ k)) ^ (Nat.gcdB m (2 ^ k)) := by
    rw [h1, h2, ← zpow_add, ← hg, Nat.cast_one, zpow_one]
  rw [e, hx, one_zpow, mul_one]
  exact N.zpow_mem hxm _

namespace TwoBlocks

variable {G : Type} [Group G] [Finite G] {U : Subgroup G} {hU : IsElemAbelian 2 U}
  {H T : Subgroup G} {K₁ K₂ : Subgroup (MulAut (IntMod U hU))} (B : TwoBlocks hU H T K₁ K₂)
include B

theorem le_of_comm_blk (htop : commV K₁ ⊔ commV K₂ = ⊤) (hTH : T ≤ H) {P : Subgroup G}
    (hPT : P ≤ T) (hUP : U ≤ P) (hP2 : IsPGroup 2 ↥P)
    (hHP : H ≤ Subgroup.normalizer (P : Set G))
    (hCU : H ⊓ Subgroup.centralizer (U : Set G) ≤ P)
    (hUZ : ∀ p ∈ P, ∀ u ∈ U, p * u = u * p)
    (hcent : T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥)
    {c₁ : G} (hc₁L : c₁ ∈ twoResidual H) (hc₁N : c₁ ∈ Subgroup.normalizer (U : Set G))
    (hc₁3 : c₁ ^ 3 = 1) (hc₁K : convI hU ⟨c₁, hc₁N⟩ ∈ K₁) (hc₁1 : convI hU ⟨c₁, hc₁N⟩ ≠ 1)
    (hcomm : ∀ p ∈ P, p * c₁ * p⁻¹ * c₁⁻¹ ∈ blk hU K₁) : P ≤ U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := B.le_norm
  have hPH : P ≤ H := hPT.trans hTH
  have B' := B.symm
  have hc₁H : c₁ ∈ H := twoResidual_le H hc₁L
  obtain ⟨t, htT, ht⟩ := B.swap
  obtain ⟨t₀, ht₀T, rfl⟩ := (mem_autI hU).1 htT
  have ht₀H : (t₀ : G) ∈ H := hTH ht₀T
  set c₂ := (t₀ : G) * c₁ * (t₀ : G)⁻¹ with hc₂def
  have hc₂N : c₂ ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ t₀.2 hc₁N) (Subgroup.inv_mem _ t₀.2)
  have hc₂v : convI hU ⟨c₂, hc₂N⟩ = convI hU t₀ * convI hU ⟨c₁, hc₁N⟩ * (convI hU t₀)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  have hc₂K : convI hU ⟨c₂, hc₂N⟩ ∈ K₂ := by
    rw [hc₂v, ← ht, B1.mem_conjAut]
    simpa [mul_assoc] using hc₁K
  have hc₂1 : convI hU ⟨c₂, hc₂N⟩ ≠ 1 := by
    rw [hc₂v]
    intro h
    apply hc₁1
    have e : convI hU ⟨c₁, hc₁N⟩ = (convI hU t₀)⁻¹ *
        (convI hU t₀ * convI hU ⟨c₁, hc₁N⟩ * (convI hU t₀)⁻¹) * convI hU t₀ := by group
    rw [e, h]; group
  have hc₂3 : c₂ ^ 3 = 1 := by rw [hc₂def, conj_pow, hc₁3]; group
  have hc₂L : c₂ ∈ twoResidual H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H ht₀H) c₁).mp hc₁L
  have hc₂H : c₂ ∈ H := twoResidual_le H hc₂L
  have hcjb : cj (t₀ : G) (blk hU K₁) = blk hU K₂ := TwoBlocks.cj_blk t₀.2 ht
  have hcomm₂ : ∀ p ∈ P, p * c₂ * p⁻¹ * c₂⁻¹ ∈ blk hU K₂ := by
    intro p hp
    have hp' : (t₀ : G)⁻¹ * p * t₀ ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hHP (H.inv_mem ht₀H)) p).mp hp
      simpa using this
    have h1 := hcomm _ hp'
    rw [← hcjb]
    refine mem_cj_iff.2 ⟨_, h1, ?_⟩
    rw [hc₂def]; group
  set X₁ := blk hU K₁ ⊔ Subgroup.zpowers c₁ with hX₁def
  set X₂ := blk hU K₂ ⊔ Subgroup.zpowers c₂ with hX₂def
  have hX₁ : A4Data X₁ (blk hU K₁) c₁ := B.a4Data hc₁N hc₁3 hc₁K hc₁1
  have hX₂ : A4Data X₂ (blk hU K₂) c₂ := B'.a4Data hc₂N hc₂3 hc₂K hc₂1
  have hU₂X₁ : ∀ u ∈ blk hU K₂, ∀ x ∈ X₁, u * x = x * u := by
    intro u hu x hx
    obtain ⟨huU, huK⟩ := mem_blk.1 hu
    obtain ⟨w, hw, k, rfl⟩ := (TwoBlocks.mem_sup_zpowers_iff hX₁.mem_normalizer).1 hx
    have hcu : c₁ * u = u * c₁ := by
      have h1 : convI hU ⟨c₁, hc₁N⟩ (IntMod.mk hU ⟨u, huU⟩) = IntMod.mk hU ⟨u, huU⟩ :=
        B.apply_eq₁ hc₁K huK
      have h2 := congrArg IntMod.val h1
      rw [convI_apply_val] at h2
      have h3 : c₁ * u * c₁⁻¹ = u := h2
      calc c₁ * u = (c₁ * u * c₁⁻¹) * c₁ := by group
        _ = u * c₁ := by rw [h3]
    have hwu : Commute u w := B2F.isElemAbelian_comm hU huU (blk_le K₁ hw)
    exact (hwu.mul_right ((Commute.symm hcu).zpow_right k)).eq
  have hU₁X₂ : ∀ u ∈ blk hU K₁, ∀ x ∈ X₂, u * x = x * u := by
    intro u hu x hx
    obtain ⟨huU, huK⟩ := mem_blk.1 hu
    obtain ⟨w, hw, k, rfl⟩ := (TwoBlocks.mem_sup_zpowers_iff hX₂.mem_normalizer).1 hx
    have hcu : c₂ * u = u * c₂ := by
      have h1 : convI hU ⟨c₂, hc₂N⟩ (IntMod.mk hU ⟨u, huU⟩) = IntMod.mk hU ⟨u, huU⟩ :=
        B.apply_eq₂ hc₂K huK
      have h2 := congrArg IntMod.val h1
      rw [convI_apply_val] at h2
      have h3 : c₂ * u * c₂⁻¹ = u := h2
      calc c₂ * u = (c₂ * u * c₂⁻¹) * c₂ := by group
        _ = u * c₂ := by rw [h3]
    have hwu : Commute u w := B2F.isElemAbelian_comm hU huU (blk_le K₂ hw)
    exact (hwu.mul_right ((Commute.symm hcu).zpow_right k)).eq
  have hPX : ∀ {W : Subgroup G} {c : G}, W ≤ U → c ∈ Subgroup.normalizer (W : Set G) →
      (∀ p ∈ P, p * c * p⁻¹ * c⁻¹ ∈ W) → ∀ p ∈ P,
        p ∈ Subgroup.normalizer ((W ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := by
    intro W c hWU hcN hWc
    have key : ∀ p ∈ P, ∀ x ∈ W ⊔ Subgroup.zpowers c, p * x * p⁻¹ ∈ W ⊔ Subgroup.zpowers c := by
      intro p hp x hx
      obtain ⟨w, hw, k, rfl⟩ := (TwoBlocks.mem_sup_zpowers_iff hcN).1 hx
      have hpw : p * w * p⁻¹ = w := by rw [hUZ p hp w (hWU hw)]; group
      have e : p * (w * c ^ k) * p⁻¹ = w * ((p * c * p⁻¹ * c⁻¹) * c) ^ k := by
        rw [show (p * c * p⁻¹ * c⁻¹) * c = p * c * p⁻¹ by group, conj_zpow]
        calc p * (w * c ^ k) * p⁻¹ = (p * w * p⁻¹) * (p * c ^ k * p⁻¹) := by group
          _ = w * (p * c ^ k * p⁻¹) := by rw [hpw]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.zpow_mem _
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hWc p hp))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))) k)
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key p hp x, fun h => ?_⟩
    have := key p⁻¹ (P.inv_mem hp) _ h
    simpa [mul_assoc] using this
  have hPX₁ : ∀ p ∈ P, p ∈ Subgroup.normalizer (X₁ : Set G) :=
    hPX (blk_le K₁) hX₁.mem_normalizer hcomm
  have hPX₂ : ∀ p ∈ P, p ∈ Subgroup.normalizer (X₂ : Set G) :=
    hPX (blk_le K₂) hX₂.mem_normalizer hcomm₂
  have hPC : ∀ {W : Subgroup G}, W ≤ U → ∀ p ∈ P, p ∈ Subgroup.centralizer (W : Set G) := by
    intro W hWU p hp
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hUZ p hp w (hWU hw)).symm
  have hdecomp : ∀ p ∈ P, ∃ u ∈ U, ∃ d ∈ P, p = u * d ∧
      d ∈ Subgroup.centralizer (X₁ : Set G) ∧ d ∈ Subgroup.centralizer (X₂ : Set G) := by
    intro p hp
    obtain ⟨u₁, hu₁, hd₁⟩ := hX₁.exists_mul_mem_centralizer (hPX₁ p hp) (hPC (blk_le K₁) p hp)
    have hd₁P : u₁⁻¹ * p ∈ P := P.mul_mem (P.inv_mem (hUP (blk_le K₁ hu₁))) hp
    obtain ⟨u₂, hu₂, hd₂⟩ := hX₂.exists_mul_mem_centralizer (hPX₂ _ hd₁P)
      (hPC (blk_le K₂) _ hd₁P)
    refine ⟨u₁ * u₂, U.mul_mem (blk_le K₁ hu₁) (blk_le K₂ hu₂), u₂⁻¹ * (u₁⁻¹ * p),
      P.mul_mem (P.inv_mem (hUP (blk_le K₂ hu₂))) hd₁P, by group, ?_, hd₂⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := Subgroup.mem_centralizer_iff.mp hd₁ x hx
    have h2 := hU₂X₁ u₂ hu₂ x hx
    calc x * (u₂⁻¹ * (u₁⁻¹ * p)) = u₂⁻¹ * (u₂ * x * u₂⁻¹) * (u₁⁻¹ * p) := by group
      _ = u₂⁻¹ * (x * (u₁⁻¹ * p)) := by rw [h2]; group
      _ = u₂⁻¹ * ((u₁⁻¹ * p) * x) := by rw [h1]
      _ = u₂⁻¹ * (u₁⁻¹ * p) * x := by group
  have hw2 : ∀ {W : Subgroup G} {c : G} (w : G), W ≤ U → c ^ 3 = 1 →
      (∀ p ∈ P, p * c * p⁻¹ * c⁻¹ ∈ W) → w ∈ P → (w * c) ^ 3 = 1 → w ∈ W := by
    intro W c w hWU hc3 hWc hw hwc
    have ha : ∀ q ∈ P, ∃ a ∈ W, c * q * c⁻¹ = q * a := by
      intro q hq
      refine ⟨q⁻¹ * c * q * c⁻¹, ?_, by group⟩
      have := hWc q⁻¹ (P.inv_mem hq)
      simpa using this
    obtain ⟨a₁, ha₁, e₁⟩ := ha w hw
    have hcw : c * w * c⁻¹ ∈ P := by
      rw [e₁]; exact P.mul_mem hw (hUP (hWU ha₁))
    obtain ⟨a₂, ha₂, e₂⟩ := ha (c * w * c⁻¹) hcw
    have hexp : (w * c) ^ 3 = w * (w * a₁) * ((w * a₁) * a₂) := by
      have : (w * c) ^ 3 = w * (c * w * c⁻¹) * (c * (c * w * c⁻¹) * c⁻¹) * c ^ 3 := by
        simp only [pow_succ, pow_zero, one_mul]; group
      rw [this, hc3, mul_one, e₂, e₁]
    rw [hexp] at hwc
    have hcomm₁ : w * a₁ = a₁ * w := hUZ w hw a₁ (hWU ha₁)
    have hcomm₂ : w * a₂ = a₂ * w := hUZ w hw a₂ (hWU ha₂)
    have hcomm₃ : a₁ * a₂ = a₂ * a₁ := B2F.isElemAbelian_comm hU (hWU ha₁) (hWU ha₂)
    have h3 : w ^ 3 * (a₁ * a₁ * a₂) = 1 := by
      calc w ^ 3 * (a₁ * a₁ * a₂) = w * (w * a₁) * ((w * a₁) * a₂) := by
            rw [pow_succ, pow_succ, pow_one]
            calc w * w * w * (a₁ * a₁ * a₂) = w * w * (w * a₁) * a₁ * a₂ := by group
              _ = w * w * (a₁ * w) * a₁ * a₂ := by rw [hcomm₁]
              _ = w * (w * a₁) * (w * a₁) * a₂ := by group
              _ = w * (w * a₁) * ((w * a₁) * a₂) := by group
        _ = 1 := hwc
    have hw3 : w ^ 3 ∈ W := by
      have : w ^ 3 = (a₁ * a₁ * a₂)⁻¹ := eq_inv_of_mul_eq_one_left h3
      rw [this]
      exact W.inv_mem (W.mul_mem (W.mul_mem ha₁ ha₁) ha₂)
    obtain ⟨k, hk⟩ := hP2 ⟨w, hw⟩
    have hk' : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact mem_of_two_pow_of_odd_pow (by decide) hk' hw3
  have hc₁c₂ : c₁ * c₂ = c₂ * c₁ := by
    set w := c₂ * c₁ * c₂⁻¹ * c₁⁻¹ with hwdef
    have hwN : w ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc₂N hc₁N)
        (Subgroup.inv_mem _ hc₂N)) (Subgroup.inv_mem _ hc₁N)
    have hwP : w ∈ P := by
      refine hCU ⟨H.mul_mem (H.mul_mem (H.mul_mem hc₂H hc₁H) (H.inv_mem hc₂H))
        (H.inv_mem hc₁H), (convI_eq_one_iff hU ⟨w, hwN⟩).1 ?_⟩
      have hcomm' := B.comm _ hc₁K _ hc₂K
      rw [show (⟨w, hwN⟩ : ↥(Subgroup.normalizer (U : Set G))) =
        ⟨c₂, hc₂N⟩ * ⟨c₁, hc₁N⟩ * (⟨c₂, hc₂N⟩)⁻¹ * (⟨c₁, hc₁N⟩)⁻¹ from rfl, map_mul, map_mul,
        map_mul, map_inv, map_inv, ← hcomm']
      group
    have hw₁ : w ∈ blk hU K₁ := by
      refine hw2 w (blk_le K₁) hc₁3 hcomm hwP ?_
      rw [show w * c₁ = c₂ * c₁ * c₂⁻¹ by rw [hwdef]; group, conj_pow, hc₁3]; group
    have hw₂ : w⁻¹ ∈ blk hU K₂ := by
      refine hw2 w⁻¹ (blk_le K₂) hc₂3 hcomm₂ (P.inv_mem hwP) ?_
      rw [show w⁻¹ * c₂ = c₁ * c₂ * c₁⁻¹ by rw [hwdef]; group, conj_pow, hc₂3]; group
    have hinf : blk hU K₁ ⊓ blk hU K₂ = ⊥ := by
      refine eq_bot_iff.mpr fun g hg => ?_
      obtain ⟨hgU, hg1⟩ := mem_blk.1 hg.1
      obtain ⟨hgU', hg2⟩ := mem_blk.1 hg.2
      have h5 : IntMod.mk hU ⟨g, hgU⟩ ∈ commV K₁ ⊓ commV K₂ := ⟨hg1, hg2⟩
      rw [B.commV_inf, Subgroup.mem_bot] at h5
      exact Subgroup.mem_bot.mpr (congrArg IntMod.val h5)
    have hw1 : w = 1 := by
      have : w ∈ blk hU K₁ ⊓ blk hU K₂ := ⟨hw₁, by simpa using (blk hU K₂).inv_mem hw₂⟩
      rw [hinf] at this
      exact this
    calc c₁ * c₂ = w⁻¹ * (c₂ * c₁) := by rw [hwdef]; group
      _ = c₂ * c₁ := by rw [hw1]; group
  have hUX : U ≤ X₁ ⊔ X₂ :=
    (TwoBlocks.le_blk_sup htop).trans (sup_le_sup le_sup_left le_sup_left)
  have hodd : ∀ y ∈ H, Odd (orderOf y) → y ∈ X₁ ⊔ X₂ := by
    intro y hyH hyodd
    have hyL : y ∈ twoResidual H := by
      rw [twoResidual_eq_oTwoUpper']
      exact Subgroup.subset_closure ⟨hyH, hyodd⟩
    have hyN := hHN hyH
    have hφ3 : ∀ (d : G) (hd : d ∈ Subgroup.normalizer (U : Set G)), d ^ 3 = 1 →
        convI hU ⟨d, hd⟩ ^ 3 = 1 := fun d hd hd3 => by
      rw [← map_pow]
      have : (⟨d, hd⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ 3 = 1 := Subtype.ext hd3
      rw [this, map_one]
    have hL := B.autI_twoResidual_eq hc₁K (hφ3 c₁ hc₁N hc₁3) hc₁1 hc₂K (hφ3 c₂ hc₂N hc₂3) hc₂1
    have hyL' : convI hU ⟨y, hyN⟩ ∈ autI hU (twoResidual H) := convI_mem_autI hU hyL hyN
    rw [hL] at hyL'
    have hcz : ∀ a ∈ Subgroup.zpowers (convI hU ⟨c₁, hc₁N⟩),
        ∀ b ∈ Subgroup.zpowers (convI hU ⟨c₂, hc₂N⟩), a * b = b * a := fun a ha b hb =>
      B.comm a ((Subgroup.zpowers_le).2 hc₁K ha) b ((Subgroup.zpowers_le).2 hc₂K hb)
    obtain ⟨p', ⟨i, rfl⟩, q', ⟨j, rfl⟩, hpq⟩ := S1417.exists_mul_of_mem_sup_of_commute hcz hyL'
    set e := c₁ ^ i * c₂ ^ j with hedef
    have heN : e ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ (Subgroup.zpow_mem _ hc₁N i) (Subgroup.zpow_mem _ hc₂N j)
    have heH : e ∈ H := H.mul_mem (H.zpow_mem hc₁H i) (H.zpow_mem hc₂H j)
    have hev : convI hU ⟨e, heN⟩ = convI hU ⟨c₁, hc₁N⟩ ^ i * convI hU ⟨c₂, hc₂N⟩ ^ j := by
      rw [← map_zpow, ← map_zpow, ← map_mul]; rfl
    have hpN : y * e⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ heN)
    have hpP : y * e⁻¹ ∈ P := by
      refine hCU ⟨H.mul_mem hyH (H.inv_mem heH), (convI_eq_one_iff hU ⟨_, hpN⟩).1 ?_⟩
      rw [show (⟨y * e⁻¹, hpN⟩ : ↥(Subgroup.normalizer (U : Set G))) =
        ⟨y, hyN⟩ * (⟨e, heN⟩)⁻¹ from rfl, map_mul, map_inv, hev, hpq, mul_inv_cancel]
    obtain ⟨u, huU, d, hdP, hpud, hd₁, hd₂⟩ := hdecomp _ hpP
    have hdc₁ : d * c₁ = c₁ * d :=
      Subgroup.mem_centralizer_iff.mp hd₁ c₁ (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₁))
      |>.symm
    have hdc₂ : d * c₂ = c₂ * d :=
      Subgroup.mem_centralizer_iff.mp hd₂ c₂ (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₂))
      |>.symm
    have hde : Commute d e :=
      (Commute.zpow_right hdc₁ i).mul_right (Commute.zpow_right hdc₂ j)
    have he3 : e ^ 3 = 1 := by
      have hcc : Commute c₁ c₂ := hc₁c₂
      rw [hedef, (hcc.zpow_zpow i j).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
        ← zpow_mul, mul_comm i, mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hc₁3,
        hc₂3, one_zpow, one_zpow, one_mul]
    have hy : y = u * (d * e) := by
      have : y = (y * e⁻¹) * e := by group
      rw [this, hpud]; group
    set m := orderOf y with hmdef
    have hzN : d * e ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ (hHN (hPH hdP)) heN
    have hpowU : ∀ n : ℕ, (u * (d * e)) ^ n * ((d * e) ^ n)⁻¹ ∈ U := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hconj : (d * e) ^ n * u * ((d * e) ^ n)⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hzN n) u).mp huU
        have e' : (u * (d * e)) ^ (n + 1) * ((d * e) ^ (n + 1))⁻¹ =
            ((u * (d * e)) ^ n * ((d * e) ^ n)⁻¹) * ((d * e) ^ n * u * ((d * e) ^ n)⁻¹) := by
          rw [pow_succ, pow_succ]; group
        rw [e']
        exact U.mul_mem ih hconj
    have hzm : (d * e) ^ m ∈ U := by
      have := hpowU m
      rw [← hy, hmdef, pow_orderOf_eq_one, one_mul] at this
      simpa using U.inv_mem this
    rw [hde.mul_pow] at hzm
    obtain ⟨k, hk⟩ := hP2 ⟨d, hdP⟩
    have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    set a := d ^ m * e ^ m with hadef
    have hda : Commute (d ^ m) a := by
      have h1 : d ^ m ∈ P := P.pow_mem hdP m
      exact hUZ _ h1 a hzm
    have ha2 : a ^ 2 = 1 := hU.2 a hzm
    have hdN : (d ^ m) ^ 2 ^ (k + 1) = 1 := by
      rw [← pow_mul, pow_succ, show m * (2 ^ k * 2) = 2 ^ k * (m * 2) by ring, pow_mul, hk',
        one_pow]
    have haN : a ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, mul_comm, pow_mul, ha2, one_pow]
    have hem : (e ^ m) ^ 2 ^ (k + 1) = 1 := by
      have e1 : e ^ m = (d ^ m)⁻¹ * a := by rw [hadef]; group
      rw [e1, (hda.inv_left).mul_pow, inv_pow, hdN, haN, inv_one, one_mul]
    have he1 : e ^ m = 1 := by
      have h3 : (e ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, he3, one_pow]
      exact eq_one_of_pow_coprime h3 hem
        (Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2))
    have hzm' : d ^ m ∈ U := by
      have h := hzm
      rw [hadef, he1, mul_one] at h
      exact h
    have hdU : d ∈ U := mem_of_two_pow_of_odd_pow hyodd hk' hzm'
    rw [hy]
    refine Subgroup.mul_mem _ (hUX huU) (Subgroup.mul_mem _ (hUX hdU) ?_)
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers c₁)) i))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers c₂)) j))
  intro p hp
  obtain ⟨u, huU, d, hdP, rfl, hd₁, hd₂⟩ := hdecomp p hp
  have hdC : d ∈ Subgroup.centralizer (oTwoUpper H : Set G) := by
    have hle : oTwoUpper H ≤ Subgroup.centralizer ({d} : Set G) := by
      refine (Subgroup.closure_le _).2 fun y hy => ?_
      have hyX := hodd y hy.1 hy.2
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hX12 : X₁ ⊔ X₂ ≤ Subgroup.centralizer ({d} : Set G) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hd₁ x hx
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hd₂ x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hX12 hyX)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hd1 : d ∈ T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := ⟨hPT hdP, hdC⟩
  rw [hcent, Subgroup.mem_bot] at hd1
  rw [hd1, mul_one]
  exact huU

end TwoBlocks

end CFSG.Quasithin.H13.A5
