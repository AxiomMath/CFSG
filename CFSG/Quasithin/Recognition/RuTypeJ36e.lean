module

public import CFSG.Quasithin.Recognition.RuTypeJ36d
public import CFSG.Quasithin.Recognition.RuTypeGL25

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem comm_zpowers_mem {b x β : G} (hx : x ∈ P5 b) (hβ : β ∈ Subgroup.zpowers b) :
    β * x = x * β := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ
  exact (comm_zpowers_P5 hx k).symm

theorem actV_mul [Finite G] {b c d : G}
    (hc : c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G))
    (hd : d ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) (v : V5 b) :
    actV (mul_mem hc hd) v = actV hc (actV hd v) := by
  induction v using QuotientGroup.induction_on with
  | H x =>
  rw [actV_mk, actV_mk, actV_mk]
  congr 1
  apply Subtype.ext
  show c * d * x * (c * d)⁻¹ = c * (d * x * d⁻¹) * c⁻¹
  group

theorem actV_one [Finite G] {b : G} (v : V5 b) :
    actV (one_mem (Subgroup.normalizer (Subgroup.zpowers b : Set G))) v = v := by
  induction v using QuotientGroup.induction_on with
  | H x =>
  rw [actV_mk]
  congr 1
  apply Subtype.ext
  show (1 : G) * (x : G) * (1 : G)⁻¹ = x
  group

@[expose] noncomputable def actVAut [Finite G] {b c : G}
    (hc : c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) : MulAut (V5 b) :=
  { actV hc with
    invFun := actV (inv_mem hc)
    left_inv := fun v => by
      show actV (inv_mem hc) (actV hc v) = v
      rw [← actV_mul]
      induction v using QuotientGroup.induction_on with
      | H x =>
      rw [actV_mk]
      congr 1
      apply Subtype.ext
      show c⁻¹ * c * (x : G) * (c⁻¹ * c)⁻¹ = x
      group
    right_inv := fun v => by
      show actV hc (actV (inv_mem hc) v) = v
      rw [← actV_mul]
      induction v using QuotientGroup.induction_on with
      | H x =>
      rw [actV_mk]
      congr 1
      apply Subtype.ext
      show c * c⁻¹ * (x : G) * (c * c⁻¹)⁻¹ = x
      group }

theorem actVAut_apply [Finite G] {b c : G}
    (hc : c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) (v : V5 b) :
    actVAut hc v = actV hc v := rfl

namespace RuDataM

variable (M : RuDataM G) [Finite G]

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

@[expose] noncomputable def actVR
    : RB5 hbH hb5 →* MulAut (V5 b) where
  toFun r := actVAut (RB5_le_normalizer hbH hb5 r.2)
  map_one' := by
    apply MulEquiv.ext
    intro v
    rw [actVAut_apply]
    exact actV_one v
  map_mul' r s := by
    apply MulEquiv.ext
    intro v
    rw [MulAut.mul_apply, actVAut_apply, actVAut_apply, actVAut_apply, ← actV_mul]

theorem actVR_apply (r : RB5 hbH hb5) (v : V5 b) :
    actVR hbH hb5 r v = actV (RB5_le_normalizer hbH hb5 r.2) v := rfl

theorem comm_V5
    (u v : V5 b) : u * v = v * u := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (G := V5 b)
    (by rw [card_V5 hbH hb5]; norm_num)
  exact h.is_comm.comm u v

theorem actVR_injective
    : Function.Injective (actVR hbH hb5) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have htriv : ∀ v : V5 b, actV (RB5_le_normalizer hbH hb5 r.2) v = v := fun v => by
    rw [← actVR_apply, hr, MulAut.one_apply]
  have hnc := not_comm_P5 hbH hb5
  push Not at hnc
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  have hconj : ∀ u : G, ∀ hu : u ∈ P5 b, ∃ β ∈ Subgroup.zpowers b,
      (r : G) * u * (r : G)⁻¹ = u * β := by
    intro u hu
    have h := htriv ((⟨u, hu⟩ : P5 b) : V5 b)
    rw [actV_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    refine ⟨((conjP5 (RB5_le_normalizer hbH hb5 r.2) ⟨u, hu⟩)⁻¹ * ⟨u, hu⟩ : P5 b)⁻¹,
      inv_mem h, ?_⟩
    show (r : G) * u * (r : G)⁻¹ = u * (((r : G) * u * (r : G)⁻¹)⁻¹ * u)⁻¹
    group
  obtain ⟨β1, hβ1, h1⟩ := hconj x hx
  obtain ⟨β2, hβ2, h2⟩ := hconj y hy
  have hc1x := (comm_zpowers_mem hx hβ1)
  have hc1y := (comm_zpowers_mem hy hβ1)
  have hc2x := (comm_zpowers_mem hx hβ2)
  have hc2y := (comm_zpowers_mem hy hβ2)
  have hβ12 : β1 * β2 = β2 * β1 := by
    obtain ⟨k1, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ1
    obtain ⟨k2, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ2
    exact (Commute.zpow_zpow_self b k1 k2).eq
  set w := x * y * x⁻¹ * y⁻¹ with hw
  have hrw : (r : G) * w * (r : G)⁻¹ = w := by
    calc (r : G) * w * (r : G)⁻¹ = ((r : G) * x * (r : G)⁻¹) * ((r : G) * y * (r : G)⁻¹) *
        ((r : G) * x * (r : G)⁻¹)⁻¹ * ((r : G) * y * (r : G)⁻¹)⁻¹ := by rw [hw]; group
      _ = x * β1 * (y * β2) * (x * β1)⁻¹ * (y * β2)⁻¹ := by rw [h1, h2]
      _ = x * (β1 * y) * β2 * β1⁻¹ * x⁻¹ * β2⁻¹ * y⁻¹ := by group
      _ = x * (y * β1) * β2 * β1⁻¹ * x⁻¹ * β2⁻¹ * y⁻¹ := by rw [hc1y]
      _ = x * y * (β1 * β2) * β1⁻¹ * x⁻¹ * β2⁻¹ * y⁻¹ := by group
      _ = x * y * (β2 * β1) * β1⁻¹ * x⁻¹ * β2⁻¹ * y⁻¹ := by rw [hβ12]
      _ = x * y * β2 * x⁻¹ * β2⁻¹ * y⁻¹ := by group
      _ = x * y * (β2 * x⁻¹) * β2⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * β2) * β2⁻¹ * y⁻¹ := by
          rw [show β2 * x⁻¹ = x⁻¹ * β2 from (Commute.inv_right
            (show Commute β2 x from hc2x)).eq]
      _ = w := by rw [hw]; group
  have hwB : w ∈ Subgroup.zpowers b := by
    have h := comm_V5 hbH hb5 ((⟨x, hx⟩ : P5 b) : V5 b) ((⟨y, hy⟩ : P5 b) : V5 b)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    have e : (((⟨x, hx⟩ * ⟨y, hy⟩ : P5 b)⁻¹ * (⟨y, hy⟩ * ⟨x, hx⟩) : P5 b) : G) =
        y⁻¹ * x⁻¹ * y * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e] at h
    have h' : (y⁻¹ * x⁻¹ * y * x)⁻¹ ∈ Subgroup.zpowers b := inv_mem h
    have hcen := comm_zpowers_mem (mul_mem hx hy) h'
    have e2 : w = (x * y) * (y⁻¹ * x⁻¹ * y * x)⁻¹ * (x * y)⁻¹ := by rw [hw]; group
    rw [e2, ← hcen, mul_inv_cancel_right]
    exact h'
  have hw1 : w ≠ 1 := by
    intro h
    apply hxy
    calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
      _ = y * x := by rw [← hw, h, one_mul]
  have hzw : Subgroup.zpowers w = Subgroup.zpowers b := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwB) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hb5]
    have hwo : orderOf w ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard _ hwB
      rwa [Nat.card_zpowers, hb5] at this
    rcases (Nat.dvd_prime Nat.prime_five).mp hwo with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · rw [h]
  have hrb : (r : G) * b = b * r := by
    have hbw : b ∈ Subgroup.zpowers w := by rw [hzw]; exact Subgroup.mem_zpowers b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbw
    have hrw' : (r : G) * w = w * r := by
      calc (r : G) * w = ((r : G) * w * (r : G)⁻¹) * r := by group
        _ = w * r := by rw [hrw]
    have := ((Commute.zpow_right (show Commute (r : G) w from hrw') k)).eq
    rw [hk] at this
    exact this
  have hrT := mem_T5_of_mem_RB5 hbH hb5 r.2 (mem_G5.mpr hrb)
  by_contra hr1
  have hr1' : (r : G) ≠ 1 := fun h => hr1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (z_mem_zpowers_T5 hbH hb5 hrT hr1')
  have hzR : (⟨M.z, z_mem_RB5 hbH hb5⟩ : RB5 hbH hb5) = r ^ k := Subtype.ext (by simp [← hk])
  have hzact : actVR hbH hb5 ⟨M.z, z_mem_RB5 hbH hb5⟩ = 1 := by
    rw [hzR, map_zpow, hr, one_zpow]
  have hinv := actV_z_eq_inv hbH hb5
  have hall : ∀ v : V5 b, v = v⁻¹ := by
    intro v
    have h1 := congrArg (fun f : MulAut (V5 b) => f v) hzact
    simp only [MulAut.one_apply] at h1
    rw [actVR_apply] at h1
    have h2 := congrFun hinv v
    rw [← h2]
    exact h1.symm
  have h1V : ∀ v : V5 b, v = 1 := by
    intro v
    have h2 : v ^ 2 = 1 := by
      rw [pow_two]
      calc v * v = v⁻¹ * v := by rw [← hall v]
        _ = 1 := inv_mul_cancel v
    have h5 := pow_five_eq_one_V hbH hb5 v
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h5)
    simpa using this
  have hc := card_V5 hbH hb5
  have : Subsingleton (V5 b) := ⟨fun u v => (h1V u).trans (h1V v).symm⟩
  rw [Nat.card_unique] at hc
  norm_num at hc

theorem nonempty_RB5_W42
    : Nonempty (RB5 hbH hb5 ≃* GL25.W42) :=
  GL25.nonempty_mulEquiv_W42_of_faithful (comm_V5 hbH hb5) (card_V5 hbH hb5)
    (pow_five_eq_one_V hbH hb5) (actVR hbH hb5) (actVR_injective hbH hb5) (card_RB5 hbH hb5)

end Five

end RuDataM

end CFSG.Quasithin.RuType
