module

public import CFSG.Quasithin.EmptyFaithful.S1421L2Two
public import CFSG.Quasithin.Recognition.RuTypeJ44d
public import CFSG.Quasithin.Recognition.RuTypeSz2

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups

theorem exists_mul_pow_of_normalizes {X : Type*} [Group X] {K : Subgroup X} {g α : X}
    (hg : ∀ a ∈ K, g * a * g⁻¹ ∈ K) (hα : α ∈ K) :
    ∀ n : ℕ, ∃ α' ∈ K, (α * g) ^ n = α' * g ^ n := by
  have hgn : ∀ n : ℕ, ∀ a ∈ K, g ^ n * a * (g ^ n)⁻¹ ∈ K := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih =>
      intro a ha
      have e : g ^ (n + 1) * a * (g ^ (n + 1))⁻¹ = g ^ n * (g * a * g⁻¹) * (g ^ n)⁻¹ := by
        rw [pow_succ]
        group
      rw [e]
      exact ih _ (hg a ha)
  intro n
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨α', hα', h⟩ := ih
    refine ⟨α' * (g ^ n * α * (g ^ n)⁻¹), mul_mem hα' (hgn n α hα), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

namespace SL3

@[expose] def rr : SL(3, ZMod 2) := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

theorem rr_mem_R0 : rr ∈ R0 := by decide

theorem rr_not_mem_R2m : rr ∉ R2m := by decide

theorem rr_mul_rr : rr * rr = 1 := by decide

theorem rr_conj_x0 : rr * (x0 * rr * x0⁻¹) = x0 := by decide

theorem x0_pow_two_pow : x0 ^ 2 ^ 14 = x0 := by
  rw [show 2 ^ 14 = 3 * 5461 + 1 by norm_num, pow_succ, pow_mul, x0_pow_three, one_pow, one_mul]

theorem x0_not_mem_R2m : x0 ∉ R2m := by decide

theorem x0_not_mem_P0 : x0 ∉ P0 := by decide

theorem x0_sq_not_mem_P0 : x0 ^ 2 ∉ P0 := by decide

theorem x0_conj_rr_not_mem_P0 : x0 * rr * x0⁻¹ ∉ P0 := by decide

theorem R0_elems : ∀ g ∈ R0, g = 1 ∨ g = zP0 ∨ g = rr ∨ g = rr * zP0 := by decide +kernel

theorem rr_mul_R2m_ne_one : ∀ g ∈ R2m, rr * g ≠ 1 := by decide +kernel

theorem x0_zpow_mem_P0 {j : ℤ} (h : x0 ^ j ∈ P0) : j % 3 = 0 := by
  have hj : x0 ^ j = x0 ^ (j % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod j 3, zpow_add, zpow_mul]
    rw [show x0 ^ (3 : ℤ) = 1 by rw [zpow_ofNat]; exact x0_pow_three, one_zpow, one_mul]
  rw [hj] at h
  have h3 : 0 ≤ j % 3 ∧ j % 3 < 3 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _
    (by norm_num)⟩
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h1 | h2
  · exact h0
  · rw [h1, zpow_one] at h
    exact absurd h x0_not_mem_P0
  · rw [h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at h
    exact absurd h x0_sq_not_mem_P0

end SL3

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G) [Finite G]

theorem exists_qel :
    ∃ q ∈ M.Q5 M.b5el_mem_H, ∃ hq : q ∈ M.L, M.θ ⟨q, hq⟩ = SL3.rr :=
  M.exists_Q5_θ M.b5el_mem_H M.orderOf_b5el SL3.rr_mem_R0

@[expose] noncomputable def qel : G := M.exists_qel.choose

theorem qel_mem_Q5 : M.qel ∈ M.Q5 M.b5el_mem_H :=
  M.exists_qel.choose_spec.1

theorem qel_mem_L : M.qel ∈ M.L :=
  M.exists_qel.choose_spec.2.choose

theorem θ_qel : M.θ ⟨M.qel, M.qel_mem_L⟩ = SL3.rr :=
  M.exists_qel.choose_spec.2.choose_spec

theorem qel_mem_G2 : M.qel ∈ M.G2 :=
  M.T_le_G2 (M.Q5_le_T M.qel_mem_Q5)

theorem qel_mem_TF : M.qel ∈ M.TF :=
  Subgroup.mem_sup_right M.qel_mem_Q5

theorem qel_sq_mem_W : M.qel ^ 2 ∈ M.W := by
  have hS : M.qel ^ 2 ∈ ruS M.L := by
    rw [M.mem_S_iff_θ (pow_mem M.qel_mem_L 2)]
    have e : (⟨M.qel ^ 2, pow_mem M.qel_mem_L 2⟩ : M.L) = ⟨M.qel, M.qel_mem_L⟩ ^ 2 := rfl
    rw [e, map_pow, M.θ_qel, pow_two, SL3.rr_mul_rr]
  exact M.Q5_inf_S_le_W ⟨pow_mem M.qel_mem_Q5 2, hS⟩

theorem qel_not_mem_Agrp : M.qel ∉ M.Agrp := by
  intro h
  have := (mem_pullL.mp (M.Agrp_le_R2 h)).2
  rw [M.θ_qel] at this
  exact SL3.rr_not_mem_R2m this

theorem G2_le_normalizer_Agrp :
    M.G2 ≤ Subgroup.normalizer (M.Agrp : Set G) :=
  fun _ hg => mem_normalizer_of_conj_mem fun _ hy => M.conj_mem_Agrp hg hy

@[expose] noncomputable def uel : G :=
  M.qel * ((M.xel : G) * M.qel * (M.xel : G)⁻¹)

theorem uel_mem_G2 : M.uel ∈ M.G2 :=
  mul_mem M.qel_mem_G2 (mul_mem (mul_mem M.xel_mem_G2 M.qel_mem_G2) (inv_mem M.xel_mem_G2))

theorem uel_mem_L : M.uel ∈ M.L :=
  (mem_pullL.mp M.uel_mem_G2).1

theorem θ_uel : M.θ ⟨M.uel, M.uel_mem_L⟩ = SL3.x0 := by
  have e : (⟨M.uel, M.uel_mem_L⟩ : M.L) =
      ⟨M.qel, M.qel_mem_L⟩ * (M.xel * ⟨M.qel, M.qel_mem_L⟩ * M.xel⁻¹) := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, M.θ_qel, M.θ_xel, SL3.rr_conj_x0]

theorem qel_conj_uel :
    M.qel * M.uel * M.qel⁻¹ =
      (M.qel ^ 2 * ((M.xel : G) * M.qel ^ 2 * (M.xel : G)⁻¹)) * M.uel⁻¹ := by
  simp only [uel, pow_two]
  group

theorem qel_conj_uel_factor_mem :
    M.qel ^ 2 * ((M.xel : G) * M.qel ^ 2 * (M.xel : G)⁻¹) ∈ M.Agrp :=
  mul_mem (M.W_le_Agrp M.qel_sq_mem_W)
    (M.W_le_Agrp (M.conj_mem_W M.xel_mem_G2 M.qel_sq_mem_W))

@[expose] noncomputable def x2el : G := M.uel ^ 2 ^ 14

theorem x2el_mem_G2 : M.x2el ∈ M.G2 := pow_mem M.uel_mem_G2 _

theorem x2el_mem_L : M.x2el ∈ M.L :=
  (mem_pullL.mp M.x2el_mem_G2).1

theorem θ_x2el : M.θ ⟨M.x2el, M.x2el_mem_L⟩ = SL3.x0 := by
  have e : (⟨M.x2el, M.x2el_mem_L⟩ : M.L) = ⟨M.uel, M.uel_mem_L⟩ ^ 2 ^ 14 := rfl
  rw [e, map_pow, M.θ_uel, SL3.x0_pow_two_pow]

theorem x2el_pow_three : M.x2el ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := (⟨M.uel, M.uel_mem_G2⟩ : M.G2))
  rw [M.card_G2] at h
  have h' : M.uel ^ (2 ^ 11 * 24) = 1 := congrArg Subtype.val h
  rw [x2el, ← pow_mul]
  rw [show 2 ^ 14 * 3 = 2 ^ 11 * 24 by norm_num]
  exact h'

theorem x2el_not_mem_Agrp : M.x2el ∉ M.Agrp := by
  intro h
  have := (mem_pullL.mp (M.Agrp_le_R2 h)).2
  rw [M.θ_x2el] at this
  exact SL3.x0_not_mem_R2m this

theorem orderOf_x2el : orderOf M.x2el = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime M.x2el_pow_three fun h => M.x2el_not_mem_Agrp ?_
  rw [h]
  exact one_mem _

theorem qel_conj_x2el :
    ∃ α ∈ M.Agrp, M.qel * M.x2el * M.qel⁻¹ = α * M.x2el⁻¹ := by
  have hg : ∀ a ∈ M.Agrp, M.uel⁻¹ * a * M.uel⁻¹⁻¹ ∈ M.Agrp := fun a ha =>
    M.conj_mem_Agrp (inv_mem M.uel_mem_G2) ha
  obtain ⟨α, hα, h⟩ := exists_mul_pow_of_normalizes hg M.qel_conj_uel_factor_mem (2 ^ 14)
  refine ⟨α, hα, ?_⟩
  rw [x2el, ← conj_pow, M.qel_conj_uel, h, inv_pow]

noncomputable abbrev XA : Subgroup G :=
  Subgroup.zpowers M.x2el ⊔ M.Agrp

theorem zpowers_x2el_le_normalizer_Agrp :
    Subgroup.zpowers M.x2el ≤ Subgroup.normalizer (M.Agrp : Set G) := by
  rw [Subgroup.zpowers_le]
  exact M.G2_le_normalizer_Agrp M.x2el_mem_G2

theorem mem_XA {x : G} (hx : x ∈ M.XA) :
    ∃ j : ℤ, ∃ a ∈ M.Agrp, x = M.x2el ^ j * a := by
  have hx' : x ∈ ((Subgroup.zpowers M.x2el ⊔ M.Agrp : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ M.zpowers_x2el_le_normalizer_Agrp] at hx'
  obtain ⟨z, hz, a, ha, rfl⟩ := hx'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ⟨j, a, ha, rfl⟩

theorem zpowers_x2el_inf_Agrp :
    Subgroup.zpowers M.x2el ⊓ M.Agrp = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have h1 : orderOf x ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard _ hx1
    rwa [Nat.card_zpowers, M.orderOf_x2el] at this
  have h2 : orderOf x ∣ 2 ^ 11 := by
    have := Subgroup.orderOf_dvd_natCard _ hx2
    rwa [M.card_Agrp] at this
  have hd := Nat.dvd_gcd h1 h2
  have : Nat.gcd 3 (2 ^ 11) = 1 := by norm_num
  rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact (Subgroup.mem_bot).mpr hd

theorem card_XA : Nat.card M.XA = 3 * 2 ^ 11 := by
  have h := card_sup_mul_inf_of_normalizes M.zpowers_x2el_le_normalizer_Agrp
  rw [M.zpowers_x2el_inf_Agrp, Subgroup.card_bot, mul_one, Nat.card_zpowers, M.orderOf_x2el,
    M.card_Agrp] at h
  exact h

theorem Agrp_le_XA : M.Agrp ≤ M.XA := le_sup_right

theorem conj_mem_XA_of {g : G} (hg : g ∈ M.G2)
    (hx : g * M.x2el * g⁻¹ ∈ M.XA) {y : G} (hy : y ∈ M.XA) : g * y * g⁻¹ ∈ M.XA := by
  refine conj_mem_sup_of (fun z hz => ?_) (fun a ha => M.Agrp_le_XA (M.conj_mem_Agrp hg ha)) hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← conj_zpow]
  exact zpow_mem hx j

theorem Agrp_conj_x2el_mem_XA {a : G} (ha : a ∈ M.Agrp) :
    a * M.x2el * a⁻¹ ∈ M.XA := by
  have e : a * M.x2el * a⁻¹ = M.x2el * (M.x2el⁻¹ * a * M.x2el⁻¹⁻¹ * a⁻¹) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) (M.Agrp_le_XA
    (mul_mem (M.conj_mem_Agrp (inv_mem M.x2el_mem_G2) ha) (inv_mem ha)))

theorem qel_conj_x2el_mem_XA :
    M.qel * M.x2el * M.qel⁻¹ ∈ M.XA := by
  obtain ⟨α, hα, h⟩ := M.qel_conj_x2el
  rw [h]
  exact mul_mem (M.Agrp_le_XA hα) (inv_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))

theorem mem_TF {x : G} (hx : x ∈ M.TF) :
    x ∈ M.Agrp ∨ M.qel⁻¹ * x ∈ M.Agrp := by
  have hx' : x ∈ ((M.Agrp ⊔ M.Q5 M.b5el_mem_H : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ M.Agrp_le_normalizer_Q5] at hx'
  obtain ⟨a, ha, p, hp, hap⟩ := hx'
  beta_reduce at hap
  subst hap
  have hpL := M.Q5_le_L _ hp
  have hθ : M.θ ⟨p, hpL⟩ ∈ SL3.R0 := by
    rw [← M.θQ_eq]
    exact ⟨⟨p, hpL⟩, Subgroup.mem_subgroupOf.mpr (M.Q5_le_Q _ hp), rfl⟩
  have key : ∀ c ∈ M.Q5 M.b5el_mem_H, ∀ hc : c ∈ M.L, M.θ ⟨c, hc⟩ = M.θ ⟨p, hpL⟩ →
      c⁻¹ * p ∈ M.Agrp := by
    intro c hc hcL hθc
    refine M.W_le_Agrp (M.Q5_inf_S_le_W (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hc) hp, ?_⟩))
    rw [M.mem_S_iff_θ (mul_mem (inv_mem hcL) hpL)]
    have e : (⟨c⁻¹ * p, mul_mem (inv_mem hcL) hpL⟩ : M.L) = (⟨c, hcL⟩ : M.L)⁻¹ * ⟨p, hpL⟩ := rfl
    rw [e, map_mul, map_inv, hθc, inv_mul_cancel]
  rcases SL3.R0_elems _ hθ with h | h | h | h
  · left
    exact mul_mem ha (M.W_le_Agrp (M.Q5_inf_S_le_W
      (Subgroup.mem_inf.mpr ⟨hp, (M.mem_S_iff_θ hpL).mpr h⟩)))
  · left
    have := key M.ael M.ael_mem_Q5 M.ael_mem_L (by rw [M.θ_ael, h])
    have e : a * p = a * M.ael * (M.ael⁻¹ * p) := by group
    rw [e]
    exact mul_mem (mul_mem ha M.ael_mem_Agrp) this
  · right
    have := key M.qel M.qel_mem_Q5 M.qel_mem_L (by rw [M.θ_qel, h])
    have e : M.qel⁻¹ * (a * p) = (M.qel⁻¹ * a * M.qel⁻¹⁻¹) * (M.qel⁻¹ * p) := by group
    rw [e]
    exact mul_mem (M.conj_mem_Agrp (inv_mem M.qel_mem_G2) ha) this
  · right
    have hcL : M.qel * M.ael ∈ M.L := mul_mem M.qel_mem_L M.ael_mem_L
    have := key (M.qel * M.ael) (mul_mem M.qel_mem_Q5 M.ael_mem_Q5) hcL (by
      have e : (⟨M.qel * M.ael, hcL⟩ : M.L) = ⟨M.qel, M.qel_mem_L⟩ * ⟨M.ael, M.ael_mem_L⟩ := rfl
      rw [e, map_mul, M.θ_qel, M.θ_ael, h])
    have e : M.qel⁻¹ * (a * p) =
        (M.qel⁻¹ * a * M.qel⁻¹⁻¹) * M.ael * ((M.qel * M.ael)⁻¹ * p) := by group
    rw [e]
    exact mul_mem (mul_mem (M.conj_mem_Agrp (inv_mem M.qel_mem_G2) ha) M.ael_mem_Agrp) this

theorem TF_le_normalizer_XA :
    M.TF ≤ Subgroup.normalizer (M.XA : Set G) := by
  intro t ht
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  have htG := M.T_le_G2 (M.TF_le_T ht)
  refine M.conj_mem_XA_of htG ?_ hy
  rcases M.mem_TF ht with h | h
  · exact M.Agrp_conj_x2el_mem_XA h
  · have e : t * M.x2el * t⁻¹ = M.qel * ((M.qel⁻¹ * t) * M.x2el * (M.qel⁻¹ * t)⁻¹) * M.qel⁻¹ := by
      group
    rw [e]
    exact M.conj_mem_XA_of M.qel_mem_G2 M.qel_conj_x2el_mem_XA (M.Agrp_conj_x2el_mem_XA h)

noncomputable abbrev F2 : Subgroup G :=
  M.TF ⊔ Subgroup.zpowers M.x2el

theorem F2_eq : M.F2 = M.TF ⊔ M.XA := by
  refine le_antisymm (sup_le le_sup_left (le_sup_left.trans le_sup_right)) (sup_le le_sup_left ?_)
  exact sup_le le_sup_right ((le_sup_left : M.Agrp ≤ M.TF).trans le_sup_left)

theorem TF_le_F2 : M.TF ≤ M.F2 := le_sup_left

theorem x2el_mem_F2 : M.x2el ∈ M.F2 :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem F2_le_G2 : M.F2 ≤ M.G2 :=
  sup_le (M.TF_le_T.trans M.T_le_G2) ((Subgroup.zpowers_le).mpr M.x2el_mem_G2)

theorem Agrp_le_F2 : M.Agrp ≤ M.F2 :=
  (le_sup_left : M.Agrp ≤ M.TF).trans M.TF_le_F2

theorem mem_F2 {x : G} (hx : x ∈ M.F2) :
    ∃ t ∈ M.TF, ∃ j : ℤ, ∃ a ∈ M.Agrp, x = t * (M.x2el ^ j * a) := by
  rw [M.F2_eq] at hx
  have hx' : x ∈ ((M.TF ⊔ M.XA : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ M.TF_le_normalizer_XA] at hx'
  obtain ⟨t, ht, y, hy, rfl⟩ := hx'
  obtain ⟨j, a, ha, rfl⟩ := M.mem_XA hy
  exact ⟨t, ht, j, a, ha, rfl⟩

theorem TF_inf_XA : M.TF ⊓ M.XA = M.Agrp := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (le_inf le_sup_left M.Agrp_le_XA) ?_
  rw [M.card_Agrp]
  obtain ⟨k, hk, hcard⟩ := RuDataN.exists_card_eq_two_pow
    (inf_le_left : M.TF ⊓ M.XA ≤ M.TF) M.card_TF
  have hdvd := Subgroup.card_dvd_of_le (inf_le_right : M.TF ⊓ M.XA ≤ M.XA)
  rw [hcard, M.card_XA] at hdvd
  have hk11 : k ≤ 11 := by
    have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
      (hc.dvd_of_dvd_mul_left hdvd)
    exact this
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) hk11

theorem card_F2 : Nat.card M.F2 = 2 ^ 12 * 3 := by
  have h := card_sup_mul_inf_of_normalizes M.TF_le_normalizer_XA
  rw [M.TF_inf_XA, M.card_Agrp, M.card_TF, M.card_XA, ← M.F2_eq] at h
  have h' : Nat.card M.F2 * 2 ^ 11 = 2 ^ 12 * 3 * 2 ^ 11 := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem relIndex_TF_F2 : M.TF.relIndex M.F2 = 3 := by
  have h := Subgroup.relIndex_mul_card (H := M.TF) (K := M.F2)
  rw [inf_eq_left.mpr M.TF_le_F2, M.card_TF, M.card_F2] at h
  have h' : M.TF.relIndex M.F2 * 2 ^ 12 = 3 * 2 ^ 12 := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem isSylowTwoOf_TF_F2 : IsSylowTwoOf M.TF M.F2 :=
  ⟨M.TF_le_F2, IsPGroup.of_card M.card_TF, by
    show ¬ 2 ∣ M.TF.relIndex M.F2
    rw [M.relIndex_TF_F2]
    norm_num⟩

theorem θ_mem_P0_of_TF {t : G} (ht : t ∈ M.TF)
    (htL : t ∈ M.L) : M.θ ⟨t, htL⟩ ∈ SL3.P0 :=
  M.toRuDataN.θ_mem_P0 (M.TF_le_T ht) htL

theorem F2_inf_S : M.F2 ⊓ ruS M.L = M.W := by
  refine le_antisymm ?_ (le_inf (M.W_le_Agrp.trans M.Agrp_le_F2) M.W_le_S)
  rintro x ⟨hxF, hxS⟩
  obtain ⟨t, ht, j, a, ha, rfl⟩ := M.mem_F2 hxF
  have htL := M.toRuData.T_le_L (M.TF_le_T ht)
  have haL := M.Agrp_le_L ha
  have hxL := M.toRuData.S_le_L hxS
  have hθ := (M.mem_S_iff_θ hxL).mp hxS
  have e : (⟨t * (M.x2el ^ j * a), hxL⟩ : M.L) =
      ⟨t, htL⟩ * (⟨M.x2el, M.x2el_mem_L⟩ ^ j * ⟨a, haL⟩) := rfl
  rw [e, map_mul, map_mul, map_zpow, M.θ_x2el] at hθ
  have hP : SL3.x0 ^ j ∈ SL3.P0 := by
    have h1 : SL3.x0 ^ j = (M.θ ⟨t, htL⟩)⁻¹ * (M.θ ⟨a, haL⟩)⁻¹ := by
      have := eq_inv_mul_of_mul_eq hθ
      rw [mul_one] at this
      exact eq_mul_inv_of_mul_eq this
    rw [h1]
    exact mul_mem (inv_mem (M.θ_mem_P0_of_TF ht htL))
      (inv_mem (SL3.R2m_le_P0 (mem_pullL.mp (M.Agrp_le_R2 ha)).2))
  have hj := SL3.x0_zpow_mem_P0 hP
  have hx1 : M.x2el ^ j = 1 := by
    rw [← Int.mul_ediv_add_emod j 3, hj, add_zero, zpow_mul]
    rw [show M.x2el ^ (3 : ℤ) = 1 by rw [zpow_ofNat]; exact M.x2el_pow_three, one_zpow]
  rw [hx1, one_mul] at hxS ⊢
  have htaTF : t * a ∈ M.TF := mul_mem ht (Subgroup.mem_sup_left ha)
  rcases M.mem_TF htaTF with h | h
  · rw [← M.Agrp_inf_S]
    exact ⟨h, hxS⟩
  · exfalso
    have hL : M.qel⁻¹ * (t * a) ∈ M.L := M.Agrp_le_L h
    have hθ2 := (M.mem_S_iff_θ (mul_mem htL haL)).mp hxS
    have e2 : (⟨t * a, mul_mem htL haL⟩ : M.L) =
        ⟨M.qel, M.qel_mem_L⟩ * ⟨M.qel⁻¹ * (t * a), hL⟩ := Subtype.ext (by
      show t * a = M.qel * (M.qel⁻¹ * (t * a)); group)
    rw [e2, map_mul, M.θ_qel] at hθ2
    exact SL3.rr_mul_R2m_ne_one _ (mem_pullL.mp (M.Agrp_le_R2 h)).2 hθ2

noncomputable abbrev AF2 : Subgroup ↥M.F2 :=
  M.Agrp.subgroupOf M.F2

instance AF2_normal : M.AF2.Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact M.conj_mem_Agrp (M.F2_le_G2 g.2) hx⟩

theorem card_F2_quot : Nat.card (↥M.F2 ⧸ M.AF2) = 6 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup M.AF2
  rw [card_subgroupOf_of_le M.Agrp_le_F2, M.card_Agrp, M.card_F2] at h
  have h' : Nat.card (↥M.F2 ⧸ M.AF2) * 2 ^ 11 = 6 * 2 ^ 11 := by
    rw [← h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem qel_mem_F2 : M.qel ∈ M.F2 := M.TF_le_F2 M.qel_mem_TF

theorem mk_eq_one_iff_F2 {x : ↥M.F2} :
    ((x : ↥M.F2 ⧸ M.AF2) = 1) ↔ (x : G) ∈ M.Agrp := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem nonempty_F2_quot_perm3 :
    Nonempty ((↥M.F2 ⧸ M.AF2) ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ub : ↥M.F2 ⧸ M.AF2 := ((⟨M.x2el, M.x2el_mem_F2⟩ : ↥M.F2) : ↥M.F2 ⧸ M.AF2) with hub
  set wb : ↥M.F2 ⧸ M.AF2 := ((⟨M.qel, M.qel_mem_F2⟩ : ↥M.F2) : ↥M.F2 ⧸ M.AF2) with hwb
  have hu : orderOf ub = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hub, ← QuotientGroup.mk_pow, M.mk_eq_one_iff_F2]
      show M.x2el ^ 3 ∈ M.Agrp
      rw [M.x2el_pow_three]
      exact one_mem _
    · rw [hub, Ne, M.mk_eq_one_iff_F2]
      exact M.x2el_not_mem_Agrp
  have hw : orderOf wb = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hwb, ← QuotientGroup.mk_pow, M.mk_eq_one_iff_F2]
      exact M.W_le_Agrp M.qel_sq_mem_W
    · rw [hwb, Ne, M.mk_eq_one_iff_F2]
      exact M.qel_not_mem_Agrp
  have hr : wb * ub * wb⁻¹ = ub ^ 2 := by
    obtain ⟨α, hα, h⟩ := M.qel_conj_x2el
    have hαF : α ∈ M.F2 := M.Agrp_le_F2 hα
    rw [hwb, hub, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_pow, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    show (M.qel * M.x2el * M.qel⁻¹)⁻¹ * M.x2el ^ 2 ∈ M.Agrp
    rw [h]
    have e : (α * M.x2el⁻¹)⁻¹ * M.x2el ^ 2 = M.x2el * α⁻¹ * M.x2el⁻¹ * M.x2el ^ 3 := by group
    rw [e, M.x2el_pow_three, mul_one]
    exact M.conj_mem_Agrp M.x2el_mem_G2 (inv_mem hα)
  exact nonempty_mulEquiv_perm3 M.card_F2_quot hu hw hr

theorem pCore_perm3 : CFSG.Open.pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : ∀ g : Equiv.Perm (Fin 3), (∀ h : Equiv.Perm (Fin 3), h * g * h⁻¹ = g) → g = 1 := by
    decide
  set N := CFSG.Open.pCore 2 (Equiv.Perm (Fin 3))
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hdvd : Nat.card N ∣ 6 := by
    have := Subgroup.card_dvd_of_le (le_top : N ≤ ⊤)
    rwa [Subgroup.card_top, Nat.card_perm, Nat.card_fin] at this
  rw [hk] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have : 2 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  by_contra hn1
  have hcard : Nat.card N = 2 := by
    interval_cases k
    · exfalso
      rw [pow_zero] at hk
      have := (Subgroup.card_eq_one).mp hk
      rw [this] at hn
      exact hn1 hn
    · rw [hk, pow_one]
  refine hn1 (hcen n fun h => ?_)
  have hc : h * n * h⁻¹ ∈ N := hNn.conj_mem n hn h
  by_contra hne
  have h1 : h * n * h⁻¹ ≠ 1 := fun h1 => hn1 (by
    have := congrArg (fun z => h⁻¹ * z * h) h1
    simpa [mul_assoc] using this)
  have h3 : 3 ≤ Nat.card N := by
    classical
    have _ : Fintype N := Fintype.ofFinite N
    have hs : ({⟨1, one_mem _⟩, ⟨n, hn⟩, ⟨h * n * h⁻¹, hc⟩} : Finset N).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro he
        exact hne (congrArg Subtype.val he).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun he => hn1 (congrArg Subtype.val he).symm,
          fun he => h1 (congrArg Subtype.val he).symm⟩
    have := Finset.card_le_univ ({⟨1, one_mem _⟩, ⟨n, hn⟩, ⟨h * n * h⁻¹, hc⟩} : Finset N)
    rw [hs, ← Nat.card_eq_fintype_card] at this
    exact this
  omega

theorem pCore_F2 : CFSG.Open.pCore 2 ↥M.F2 = M.AF2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCore 2 (inferInstance) ?_)
  · obtain ⟨e⟩ := M.nonempty_F2_quot_perm3
    have h1 := CFSG.LieType.BorelTits.map_pCore_le 2 (QuotientGroup.mk' M.AF2)
      (QuotientGroup.mk'_surjective _)
    have h2 : CFSG.Open.pCore 2 (↥M.F2 ⧸ M.AF2) = ⊥ := by
      have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
      rw [pCore_perm3] at this
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp this
    rw [h2, Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot,
      QuotientGroup.ker_mk'] at h1
    exact h1
  · exact (IsPGroup.of_card M.card_Agrp).of_equiv (Subgroup.subgroupOfEquivOfLe M.Agrp_le_F2).symm

theorem pCoreOf_F2 : pCoreOf 2 M.F2 = M.Agrp := by
  rw [pCoreOf, M.pCore_F2, AF2, Subgroup.map_subgroupOf_eq_of_le M.Agrp_le_F2]

theorem isL2Quot_F2 : IsL2Quot 1 (oTwoQuot ↥M.F2) := by
  obtain ⟨e⟩ := M.nonempty_F2_quot_perm3
  exact isL2Quot_one_iff_perm3.mpr ⟨(QuotientGroup.quotientMulEquivOfEq M.pCore_F2).trans e⟩

omit [Finite G] in
theorem mem_H_of_centralizes_U {c : G} (hc : ∀ u ∈ ruU M.L M.T, u * c = c * u) :
    c ∈ ruH M.T :=
  M.toRuData.mem_H_iff.mpr fun z hz => hc z (M.two.Z_le_U hz)

theorem mem_zpowers_sup_U {c : G} (hc : c ∈ M.HC) {x : G}
    (hx : x ∈ Subgroup.zpowers c ⊔ ruU M.L M.T) : x ∈ ruU M.L M.T ∨ c⁻¹ * x ∈ ruU M.L M.T := by
  have hcQ := M.HC_le_Q hc
  have hcH := (Subgroup.mem_inf.mp hc).1
  have hc2 : c ^ 2 ∈ ruU M.L M.T := (M.two.QU_elem _ hcQ _ hcQ).2
  have hle : Subgroup.zpowers c ≤ Subgroup.normalizer (ruU M.L M.T : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_conj_mem fun u hu => M.conj_mem_U hcH hu
  have hx' : x ∈ ((Subgroup.zpowers c ⊔ ruU M.L M.T : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx'
  obtain ⟨z, hz, u, hu, rfl⟩ := hx'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' j
  · left
    rw [zpow_mul, zpow_ofNat]
    exact mul_mem (zpow_mem hc2 i) hu
  · right
    rw [zpow_add, zpow_mul, zpow_one, zpow_ofNat]
    have h1 : c⁻¹ * (c ^ 2) ^ i * c⁻¹⁻¹ ∈ ruU M.L M.T :=
      M.conj_mem_U (inv_mem hcH) (zpow_mem hc2 i)
    rw [inv_inv] at h1
    have e : c⁻¹ * ((c ^ 2) ^ i * c * u) = (c⁻¹ * (c ^ 2) ^ i * c) * u := by group
    rw [e]
    exact mul_mem h1 hu

theorem card_le_of_centralizes_HC {c : G} (hc : c ∈ M.HC) (hcU : c ∉ ruU M.L M.T)
    {X : Subgroup G} (hXQ : X ≤ ruQ M.T) (hXc : ∀ x ∈ X, x * c = c * x) : Nat.card X ≤ 64 := by
  have hJ := (M.lemma_J24 hc hcU).2.2
  have hsub : ((X : Subgroup G) : Set G) ⊆
      (ruU M.L M.T : Set G) ∪ (fun u => c * u) '' (ruU M.L M.T : Set G) := by
    intro x hx
    have hmem : x ∈ ruQ M.T ⊓ Subgroup.centralizer ({c} : Set G) :=
      ⟨hXQ hx, Subgroup.mem_centralizer_singleton_iff.mpr (hXc x hx)⟩
    rw [hJ] at hmem
    rcases M.mem_zpowers_sup_U hc hmem with h | h
    · exact Or.inl h
    · exact Or.inr ⟨c⁻¹ * x, h, mul_inv_cancel_left c x⟩
  have hcard := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
    ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _))
  have e1 : Nat.card X = ((X : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
  have e2 : Nat.card ↥(ruU M.L M.T) = (ruU M.L M.T : Set G).ncard := Nat.card_coe_set_eq _
  rw [← e1, ← e2, M.toRuData.card_U] at hcard
  omega

theorem charTwo_F2 : CharTwo M.F2 := by
  unfold CharTwo
  rw [M.pCoreOf_F2]
  rintro c ⟨hcF, hcA⟩
  have hcU : ∀ u ∈ ruU M.L M.T, u * c = c * u := fun u hu =>
    Subgroup.mem_centralizer_iff.mp hcA u (M.W_le_Agrp (M.U_le_W hu))
  have hcH := M.mem_H_of_centralizes_U hcU
  have hcHC : c ∈ M.HC := Subgroup.mem_inf.mpr ⟨hcH, Subgroup.mem_centralizer_iff.mpr hcU⟩
  by_cases hcU' : c ∈ ruU M.L M.T
  · exact M.W_le_Agrp (M.U_le_W hcU')
  exfalso
  have hcard := M.card_le_of_centralizes_HC hcHC hcU'
    (X := M.Q5 M.b5el_mem_H ⊓ ruS M.L) (inf_le_left.trans (M.Q5_le_Q _))
    (fun x hx => Subgroup.mem_centralizer_iff.mp hcA x (M.W_le_Agrp (M.Q5_inf_S_le_W hx)))
  rw [M.card_Q5_inf_S M.b5el_mem_H M.orderOf_b5el] at hcard
  norm_num at hcard

theorem x2el_not_mem_normalizer_TF :
    M.x2el ∉ Subgroup.normalizer (M.TF : Set G) := by
  intro hx
  have h := (Subgroup.mem_normalizer_iff.mp hx _).mp M.qel_mem_TF
  have hL : M.x2el * M.qel * M.x2el⁻¹ ∈ M.L :=
    mul_mem (mul_mem M.x2el_mem_L M.qel_mem_L) (inv_mem M.x2el_mem_L)
  have hP := M.θ_mem_P0_of_TF h hL
  have e : (⟨M.x2el * M.qel * M.x2el⁻¹, hL⟩ : M.L) =
      ⟨M.x2el, M.x2el_mem_L⟩ * ⟨M.qel, M.qel_mem_L⟩ * (⟨M.x2el, M.x2el_mem_L⟩ : M.L)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, M.θ_x2el, M.θ_qel] at hP
  exact SL3.x0_conj_rr_not_mem_P0 hP

theorem F2_inf_normalizer_TF :
    M.F2 ⊓ Subgroup.normalizer (M.TF : Set G) = M.TF := by
  set K := M.F2 ⊓ Subgroup.normalizer (M.TF : Set G)
  have hTK : M.TF ≤ K := le_inf M.TF_le_F2 Subgroup.le_normalizer
  have hKF : K ≤ M.F2 := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hTK hKF
  rw [M.relIndex_TF_F2] at hmul
  have hd : M.TF.relIndex K ∣ 3 := Dvd.intro _ hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hTK
  · exfalso
    rw [h] at hmul
    have h1 : K.relIndex M.F2 = 1 := by omega
    have hFK := Subgroup.relIndex_eq_one.mp h1
    exact M.x2el_not_mem_normalizer_TF (Subgroup.mem_inf.mp (hFK M.x2el_mem_F2)).2

end RuDataM

end CFSG.Quasithin.RuType
