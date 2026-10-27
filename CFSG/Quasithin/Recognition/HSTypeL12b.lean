module

public import CFSG.Quasithin.Recognition.HSTypeK
public import Certificates.Data.A5
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

theorem perm_five_invol_inverts : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 → σ ≠ 1 →
    ∃ τ : Equiv.Perm (Fin 5), τ * τ * τ = 1 ∧ τ ≠ 1 ∧ σ * τ * σ⁻¹ = τ⁻¹ := by
  decide +kernel

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem centralizer_Q_eq_ZQ_of_orderOf_three [Finite G] (h : HSSetting z V) {y : G}
    (hyH : y ∈ hsH z) (hy : orderOf y = 3) :
    hsQ z ⊓ Subgroup.centralizer ({y} : Set G) = hsZQ z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite ↥(hsH z ⊓ hsM V)
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card (G := ↥(hsH z ⊓ hsM V)) 3
    (by rw [← Nat.card_eq_fintype_card, h.card_H_inf_M]; norm_num)
  have hy₀o : orderOf (y₀ : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy₀
  have hC₀ := h.centralizer_Q_eq_ZQ_of_three y₀.2.1 y₀.2.2 hy₀o
  have hidx : ∀ w : ↥(hsH z), orderOf w = 3 → ¬ 3 ∣ (Subgroup.zpowers w).index := by
    intro w hw hd
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers w)
    rw [Nat.card_zpowers, hw, h.card_H] at h1
    obtain ⟨c, hc⟩ := hd
    omega
  have hp : ∀ w : ↥(hsH z), orderOf w = 3 → IsPGroup 3 (Subgroup.zpowers w) := fun w hw =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw, pow_one])
  let y' : ↥(hsH z) := ⟨y, hyH⟩
  let w₀ : ↥(hsH z) := ⟨y₀, y₀.2.1⟩
  have hy'o : orderOf y' = 3 := (Subgroup.orderOf_coe y').symm.trans hy
  have hw₀o : orderOf w₀ = 3 := (Subgroup.orderOf_coe w₀).symm.trans hy₀o
  let S := (hp y' hy'o).toSylow (hidx y' hy'o)
  let S₀ := (hp w₀ hw₀o).toSylow (hidx w₀ hw₀o)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(hsH z) S₀ S
  have hy'S : y' ∈ (S : Subgroup ↥(hsH z)) := by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.mem_zpowers y'
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hy'S
  obtain ⟨w, hwS₀, hwy⟩ := hy'S
  rw [IsPGroup.toSylow_coe] at hwS₀
  have hw1 : w ≠ 1 := by
    rintro rfl
    simp only [map_one, MulAut.smul_def] at hwy
    have := congrArg Subtype.val hwy
    rw [OneMemClass.coe_one] at this
    have hy1 : y = 1 := this.symm
    rw [hy1, orderOf_one] at hy
    omega
  have hzw : Subgroup.zpowers w = Subgroup.zpowers w₀ := by
    have hle : Subgroup.zpowers w ≤ Subgroup.zpowers w₀ := (Subgroup.zpowers_le).mpr hwS₀
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hw₀o]
    have hwo : orderOf w ∣ 3 := by
      rw [← hw₀o]
      exact orderOf_dvd_of_mem_zpowers hwS₀
    rcases (Nat.dvd_prime Nat.prime_three).mp hwo with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hw1
    · omega
  have hcen : Subgroup.centralizer ({(w : G)} : Set G) =
      Subgroup.centralizer ({(y₀ : G)} : Set G) := by
    have hmap := congrArg (Subgroup.map (hsH z).subtype) hzw
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
    rw [← Subgroup.centralizer_closure, ← Subgroup.centralizer_closure ({(y₀ : G)} : Set G),
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
    exact congrArg (fun X : Subgroup G => Subgroup.centralizer (X : Set G)) hmap
  have hyw : y = (g : G) * w * (g : G)⁻¹ := by
    have := congrArg Subtype.val hwy
    simp only [MulAut.smul_def, MulAut.conj_apply] at this
    exact this.symm.trans (by simp)
  have hgQ := le_normalizer_quasithinGenFitting (hsH z) g.2
  have hgZ := h.H_le_normalizer_ZQ g.2
  set gg : G := (g : G) with hgg
  set ww : G := (w : G) with hww
  ext x
  constructor
  · rintro ⟨hxQ, hxc⟩
    have hx' : gg⁻¹ * x * gg ∈ hsQ z ⊓ Subgroup.centralizer ({ww} : Set G) := by
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgQ) x).mp hxQ
        simpa using this
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have hc : x * (gg * ww * gg⁻¹) = (gg * ww * gg⁻¹) * x := by
          rw [← hyw]
          exact Subgroup.mem_centralizer_singleton_iff.mp hxc
        calc gg⁻¹ * x * gg * ww = gg⁻¹ * (x * (gg * ww * gg⁻¹)) * gg := by group
          _ = gg⁻¹ * ((gg * ww * gg⁻¹) * x) * gg := by rw [hc]
          _ = ww * (gg⁻¹ * x * gg) := by group
    rw [hcen, hC₀] at hx'
    have := (Subgroup.mem_normalizer_iff.mp hgZ _).mp hx'
    simpa [mul_assoc] using this
  · intro hxZ
    refine ⟨hxZ.1, ?_⟩
    show x ∈ Subgroup.centralizer ({y} : Set G)
    rw [hyw]
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hx' : gg⁻¹ * x * gg ∈ hsZQ z := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgZ) x).mp hxZ
      simpa using this
    rw [← hC₀, ← hcen] at hx'
    have hc : gg⁻¹ * x * gg * ww = ww * (gg⁻¹ * x * gg) :=
      Subgroup.mem_centralizer_singleton_iff.mp hx'.2
    calc x * (gg * ww * gg⁻¹) = gg * ((gg⁻¹ * x * gg) * ww) * gg⁻¹ := by group
      _ = gg * (ww * (gg⁻¹ * x * gg)) * gg⁻¹ := by rw [hc]
      _ = gg * ww * gg⁻¹ * x := by group

end HSSetting

@[expose] def hsStabQ (z q : G) : Subgroup G where
  carrier := {g | g ∈ hsH z ∧ g * q * g⁻¹ * q⁻¹ ∈ hsZQ z}
  mul_mem' := by
    rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
    refine ⟨(hsH z).mul_mem ha hb, ?_⟩
    have hZ := hsH_le_normalizer_hsZQ z ha
    have := (hsZQ z).mul_mem ((Subgroup.mem_normalizer_iff.mp hZ _).mp hbc) hac
    have heq : a * b * q * (a * b)⁻¹ * q⁻¹ =
        a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ * (a * q * a⁻¹ * q⁻¹) := by group
    rw [heq]
    exact this
  one_mem' := ⟨(hsH z).one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, hac⟩
    refine ⟨(hsH z).inv_mem ha, ?_⟩
    have hZ := hsH_le_normalizer_hsZQ z ((hsH z).inv_mem ha)
    have := (hsZQ z).inv_mem ((Subgroup.mem_normalizer_iff.mp hZ _).mp hac)
    have heq : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = (a⁻¹ * (a * q * a⁻¹ * q⁻¹) * a⁻¹⁻¹)⁻¹ := by group
    rw [heq]
    exact this

@[expose] def hsFixQ (z t : G) : Subgroup G where
  carrier := {q | q ∈ hsQ z ∧ t * q * t⁻¹ * q⁻¹ ∈ hsZQ z}
  mul_mem' := by
    rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
    refine ⟨(hsQ z).mul_mem ha hb, ?_⟩
    have hcomm : a * (t * b * t⁻¹ * b⁻¹) = (t * b * t⁻¹ * b⁻¹) * a :=
      Subgroup.mem_centralizer_iff.mp hbc.2 a ha
    have heq : t * (a * b) * t⁻¹ * (a * b)⁻¹ =
        (t * a * t⁻¹ * a⁻¹) * (a * (t * b * t⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [heq, hcomm, mul_inv_cancel_right]
    exact (hsZQ z).mul_mem hac hbc
  one_mem' := ⟨(hsQ z).one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, hac⟩
    refine ⟨(hsQ z).inv_mem ha, ?_⟩
    have hcomm : a⁻¹ * (t * a * t⁻¹ * a⁻¹)⁻¹ = (t * a * t⁻¹ * a⁻¹)⁻¹ * a⁻¹ :=
      Subgroup.mem_centralizer_iff.mp ((hsZQ z).inv_mem hac).2 a⁻¹ ((hsQ z).inv_mem ha)
    have heq : t * a⁻¹ * t⁻¹ * a⁻¹⁻¹ = a⁻¹ * (t * a * t⁻¹ * a⁻¹)⁻¹ * a := by group
    rw [heq, hcomm, inv_mul_cancel_right]
    exact (hsZQ z).inv_mem hac

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem Q_le_stabQ [Finite G] (h : HSSetting z V) {q : G} (hq : q ∈ hsQ z) :
    hsQ z ≤ hsStabQ z q := by
  intro c hc
  refine ⟨h.Q_le_H hc, ?_⟩
  rcases h.mul_comm_or_mul_z hc hq with hcq | hcq
  · rw [hcq, mul_inv_cancel_right, mul_inv_cancel]
    exact (hsZQ z).one_mem
  · have hzc : c * z = z * c := h.comm_z_of_mem_Q hc
    have hzq : q * z = z * q := h.comm_z_of_mem_Q hq
    have : c * q * c⁻¹ * q⁻¹ = z := by
      rw [hcq]
      calc q * c * z * c⁻¹ * q⁻¹ = q * (c * z * c⁻¹) * q⁻¹ := by group
        _ = q * z * q⁻¹ := by rw [hzc, mul_inv_cancel_right]
        _ = z := by rw [hzq, mul_inv_cancel_right]
    rw [this]
    exact h.z_mem_ZQ

theorem mem_ZQ_of_mem_stabQ_three [Finite G] (h : HSSetting z V) {y q : G} (hq : q ∈ hsQ z)
    (hy : orderOf y = 3) (hyq : y ∈ hsStabQ z q) : q ∈ hsZQ z := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨hyH, hyc⟩ := hyq
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hCy := h.centralizer_Q_eq_ZQ_of_orderOf_three hyH hy
  have hyZ := h.ZQ_le_centralizer_of_three hyH hy3
  set C := (Finset.univ.filter fun c : G => c ∈ hsZQ z).image (q * ·) with hC
  have hCcard : C.card = 4 := by
    rw [hC, Finset.card_image_of_injective _ (mul_right_injective q), ← h.card_ZQ,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  by_contra hqZ
  have h3 : 3 ∣ C.card := by
    refine prime_dvd_card_of_free C (fun w => y * w * y⁻¹) Nat.prime_three
      (fun w _ => by rw [iterate_conj, hy3]; group) (fun w hw => ?_) (fun w hw hfix => ?_)
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
      have hcZ : c ∈ hsZQ z := (Finset.mem_filter.mp hc).2
      refine Finset.mem_image.mpr ⟨q⁻¹ * (y * q * y⁻¹) * c, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · have hd : q⁻¹ * (y * q * y⁻¹) = (y * q * y⁻¹ * q⁻¹) := by
          have hcomm := (Subgroup.mem_centralizer_iff.mp hyc.2 q hq)
          calc q⁻¹ * (y * q * y⁻¹) = q⁻¹ * ((y * q * y⁻¹ * q⁻¹) * q) := by group
            _ = q⁻¹ * (q * (y * q * y⁻¹ * q⁻¹)) := by rw [hcomm]
            _ = y * q * y⁻¹ * q⁻¹ := by group
        rw [hd]
        exact (hsZQ z).mul_mem hyc hcZ
      · have hyc' : y * c * y⁻¹ = c := by
          rw [(Subgroup.mem_centralizer_singleton_iff.mp (hyZ hcZ)).symm, mul_inv_cancel_right]
        show q * (q⁻¹ * (y * q * y⁻¹) * c) = y * (q * c) * y⁻¹
        calc q * (q⁻¹ * (y * q * y⁻¹) * c) = y * q * y⁻¹ * c := by group
          _ = y * q * y⁻¹ * (y * c * y⁻¹) := by rw [hyc']
          _ = y * (q * c) * y⁻¹ := by group
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
      have hcZ : c ∈ hsZQ z := (Finset.mem_filter.mp hc).2
      apply hqZ
      have hqc : q * c ∈ hsQ z ⊓ Subgroup.centralizer ({y} : Set G) := by
        refine ⟨(hsQ z).mul_mem hq hcZ.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc q * c * y = y * (q * c) * y⁻¹ * y := by rw [hfix]
          _ = y * (q * c) := by group
      rw [hCy] at hqc
      have := (hsZQ z).mul_mem hqc ((hsZQ z).inv_mem hcZ)
      rwa [mul_inv_cancel_right] at this
  rw [hCcard] at h3
  omega

theorem ZQ_le_fixQ (_h : HSSetting z V) {t : G} (htH : t ∈ hsH z) : hsZQ z ≤ hsFixQ z t :=
  fun c hc => ⟨hc.1, (hsZQ z).mul_mem
    ((Subgroup.mem_normalizer_iff.mp (hsH_le_normalizer_hsZQ z htH) c).mp hc)
    ((hsZQ z).inv_mem hc)⟩

theorem Q_le_normalizer_fixQ [Finite G] (h : HSSetting z V) {t : G} (htH : t ∈ hsH z) :
    hsQ z ≤ Subgroup.normalizer (hsFixQ z t : Set G) := by
  have key : ∀ q ∈ hsQ z, ∀ d ∈ hsFixQ z t, q * d * q⁻¹ ∈ hsFixQ z t := by
    intro q hq d hd
    rcases h.mul_comm_or_mul_z hq hd.1 with hc | hc
    · rw [hc, mul_inv_cancel_right]
      exact hd
    · have hzq : q * z = z * q := h.comm_z_of_mem_Q hq
      have : q * d * q⁻¹ = d * z := by
        rw [hc]
        calc d * q * z * q⁻¹ = d * (q * z * q⁻¹) := by group
          _ = d * z := by rw [hzq, mul_inv_cancel_right]
      rw [this]
      exact (hsFixQ z t).mul_mem hd (h.ZQ_le_fixQ htH h.z_mem_ZQ)
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨key q hq d, fun hd => ?_⟩
  have := key q⁻¹ ((hsQ z).inv_mem hq) _ hd
  simpa [mul_assoc] using this

theorem card_fixQ_le [Finite G] (h : HSSetting z V) {t : G} (htH : t ∈ hsH z)
    (htQ : t ∉ hsQ z) (ht2 : t * t ∈ hsQ z) : Nat.card (hsFixQ z t) ≤ 16 := by
  obtain ⟨φ, hφ, hker⟩ := h.one.quot
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := by
    intro g
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  set t' : ↥(hsH z) := ⟨t, htH⟩
  have hσ2 : φ t' * φ t' = 1 := by
    rw [← map_mul, hkerQ]
    exact ht2
  have hσ1 : φ t' ≠ 1 := fun h1 => htQ ((hkerQ t').mp h1)
  obtain ⟨τ, hτ3, hτ1, hστ⟩ := perm_five_invol_inverts (φ t') hσ2 hσ1
  obtain ⟨h₀, hh₀⟩ := hφ τ
  set y : G := (h₀ : G) ^ 64 with hydef
  have hyH : y ∈ hsH z := (hsH z).pow_mem h₀.2 64
  have hτ64 : τ ^ 64 = τ := by
    have : τ ^ 3 = 1 := by rw [pow_succ, pow_succ, pow_one]; exact hτ3
    calc τ ^ 64 = (τ ^ 3) ^ 21 * τ := by rw [← pow_mul, ← pow_succ]
      _ = τ := by rw [this, one_pow, one_mul]
  have hφy : φ ⟨y, hyH⟩ = τ := by
    have : (⟨y, hyH⟩ : ↥(hsH z)) = h₀ ^ 64 := Subtype.ext (by simp [hydef])
    rw [this, map_pow, hh₀, hτ64]
  have hy3 : y ^ 3 = 1 := by
    have h3Q : (h₀ : G) ^ 3 ∈ hsQ z := by
      have : φ (h₀ ^ 3) = 1 := by rw [map_pow, hh₀, pow_succ, pow_succ, pow_one]; exact hτ3
      have := (hkerQ (h₀ ^ 3)).mp this
      simpa using this
    have h64 := pow_card_eq_one' (G := ↥(hsQ z)) (x := ⟨_, h3Q⟩)
    rw [h.card_Q] at h64
    have := congrArg Subtype.val h64
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [hydef, ← pow_mul, show 64 * 3 = 3 * 64 by norm_num, pow_mul]
    exact this
  have hy1 : y ≠ 1 := by
    intro h1
    apply hτ1
    rw [← hφy]
    have : (⟨y, hyH⟩ : ↥(hsH z)) = 1 := Subtype.ext h1
    rw [this, map_one]
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hc₀ : t * y * t⁻¹ * y ∈ hsQ z := by
    have hφ1 : φ (t' * ⟨y, hyH⟩ * t'⁻¹ * ⟨y, hyH⟩) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hφy, hστ, inv_mul_cancel]
    exact (hkerQ _).mp hφ1
  set D := hsFixQ z t with hD
  set D' := D.map (MulAut.conj y).toMonoidHom with hD'
  have hDQ : D ≤ hsQ z := fun d hd => hd.1
  have hyQ := le_normalizer_quasithinGenFitting (hsH z) hyH
  have hD'Q : D' ≤ hsQ z := by
    rintro _ ⟨d, hd, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hyQ d).mp hd.1
  have hD'N : D' ≤ Subgroup.normalizer (D : Set G) :=
    hD'Q.trans (h.Q_le_normalizer_fixQ htH)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hD'N
  have hcardD' : Nat.card D' = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hsup : Nat.card ↥(D' ⊔ D) ≤ 64 :=
    h.card_Q ▸ Subgroup.card_le_of_le (sup_le hD'Q hDQ)
  by_contra hlt
  push Not at hlt
  have hinf : 4 < Nat.card ↥(D' ⊓ D) := by
    rw [hcardD'] at hprod
    nlinarith
  obtain ⟨q, hqDD, hqZ⟩ : ∃ q ∈ D' ⊓ D, q ∉ hsZQ z := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show D' ⊓ D ≤ hsZQ z from fun q hq => hne q hq)
    rw [h.card_ZQ] at this
    omega
  obtain ⟨⟨d, hd, hdq⟩, hqD⟩ := hqDD
  have hdq' : y * d * y⁻¹ = q := hdq
  have hqQ : q ∈ hsQ z := hqD.1
  have htS : t ∈ hsStabQ z q := ⟨htH, hqD.2⟩
  have hytS : y * t * y⁻¹ ∈ hsStabQ z q := by
    refine ⟨(hsH z).mul_mem ((hsH z).mul_mem hyH htH) ((hsH z).inv_mem hyH), ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (hsH_le_normalizer_hsZQ z hyH) _).mp hd.2
    have heq : y * t * y⁻¹ * q * (y * t * y⁻¹)⁻¹ * q⁻¹ =
        y * (t * d * t⁻¹ * d⁻¹) * y⁻¹ := by rw [← hdq']; group
    rw [heq]
    exact this
  have hprodS := (hsStabQ z q).mul_mem htS hytS
  set c₂ : G := (t * y * t⁻¹ * y) * (y⁻¹ * (t * t) * y) with hc₂
  have hc₂Q : c₂ ∈ hsQ z := (hsQ z).mul_mem hc₀ (by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyQ) (t * t)).mp ht2
    simpa [mul_assoc] using this)
  have hyeq : y = c₂⁻¹ * (t * (y * t * y⁻¹)) := by
    have hy3' : y * y * y = 1 := by rw [← hy3, pow_succ, pow_succ, pow_one]
    have hyy : y⁻¹ * y⁻¹ = y := by
      calc y⁻¹ * y⁻¹ = y⁻¹ * y⁻¹ * (y * y * y) := by rw [hy3', mul_one]
        _ = y := by group
    rw [hc₂]
    calc y = y⁻¹ * y⁻¹ := hyy.symm
      _ = ((t * y * t⁻¹ * y) * (y⁻¹ * (t * t) * y))⁻¹ * (t * (y * t * y⁻¹)) := by group
  have hyS : y ∈ hsStabQ z q := by
    rw [hyeq]
    exact (hsStabQ z q).mul_mem ((hsStabQ z q).inv_mem (h.Q_le_stabQ hqQ hc₂Q)) hprodS
  exact hqZ (h.mem_ZQ_of_mem_stabQ_three hqQ hyo hyS)

end HSSetting

end CFSG.Quasithin.HSType
