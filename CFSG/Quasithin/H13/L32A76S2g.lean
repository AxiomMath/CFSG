module

public import CFSG.Quasithin.H13.L32A76S2d
public import CFSG.Quasithin.EmptyFaithful.S153E57A
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.G2Omega4PlusQuot

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76 CFSG.Quasithin.F7
open scoped commutatorElement

section Fix

variable {W : Type} [CommGroup W] [Finite W]

theorem trivial_of_comm (hV : ∀ w : W, w ^ 2 = 1) {U : Subgroup W} {x d : MulAut W} {p : ℕ}
    [Fact p.Prime] (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) (hxd : x * d = d * x) (hdp : d ^ p = 1)
    (hUx : ∀ u ∈ U, x u ∈ U) (hUd : ∀ u ∈ U, d u ∈ U) (hfix : U ⊓ fixV (Subgroup.zpowers d) = ⊥)
    (hrk : ∀ r, r ≤ rk U → p ∣ 2 ^ r - 1 → r = 0 ∨ r = rk U) : ∀ u ∈ U, x u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hU : U = ⊥
  · intro u hu
    rw [hU, Subgroup.mem_bot] at hu
    rw [hu, map_one]
  set F := U ⊓ fixV (Subgroup.zpowers x) with hF
  have hFU : F ≤ U := inf_le_left
  have hFd : ∀ u ∈ F, d u ∈ F := fun u hu =>
    ⟨hUd u hu.1, mem_fix_of_comm hxd.symm hu.2⟩
  have hFfix : F ⊓ fixV (Subgroup.zpowers d) = ⊥ :=
    le_bot_iff.mp (hfix ▸ inf_le_inf_right _ hFU)
  have hdvd := dvd_two_pow_rk_sub_one hV hFd hdp hFfix
  have hFne : F ≠ ⊥ := by
    obtain ⟨k, hk⟩ := hx2
    have hS : IsPGroup 2 (Subgroup.zpowers x) := by
      intro y
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    obtain ⟨u, huU, hu1, hux⟩ := S153E57.exists_fixed_of_isPGroup hS
      (fun s hs u hu => zpowers_invariant hUx s hs u hu) hU
      ((isPGroup_two_of_sq_eq_one hV).to_subgroup U)
    intro hbot
    have : u ∈ F := ⟨huU, fun s hs => hux s hs⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hu1 this
  rcases hrk (rk F) (rk_mono hFU) hdvd with h0 | h1
  · exact absurd ((rk_eq_zero_iff hV).mp h0) hFne
  · have heq : F = U := eq_of_le_of_rk_le hV hFU h1.ge
    intro u hu
    have : u ∈ F := heq ▸ hu
    exact mem_fixV_zpowers_iff.mp this.2

omit [Finite W] in
theorem rk_cond_five {U : Subgroup W} (h4 : rk U = 4) :
    ∀ r, r ≤ rk U → 5 ∣ 2 ^ r - 1 → r = 0 ∨ r = rk U := fun r hr hd => by
  rw [h4] at hr ⊢
  exact rk_of_dvd_five hd hr

omit [Finite W] in
theorem rk_cond_three {U : Subgroup W} (h2 : rk U = 2) :
    ∀ r, r ≤ rk U → 3 ∣ 2 ^ r - 1 → r = 0 ∨ r = rk U := fun r hr hd => by
  rw [h2] at hr ⊢
  interval_cases r <;> simp_all

end Fix

variable {G : Type} [Group G] [Finite G] {T L V H Y : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

namespace Ctx

@[expose] noncomputable def Pe (C : Ctx G T L V H Y)
    (e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) : Subgroup G :=
  ((Subgroup.zpowers e).comap (FixR.rho C.h91)).map H.subtype

variable (C : Ctx G T L V H Y)
include C

theorem mem_Pe {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} {x : G} :
    x ∈ C.Pe e ↔ ∃ hx : x ∈ H, FixR.rho C.h91 ⟨x, hx⟩ ∈ Subgroup.zpowers e := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem Pe_le_H (e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) : C.Pe e ≤ H :=
  Subgroup.map_subtype_le _

theorem le_Q_of_isPGroup {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (he5 : e ^ 5 = 1) {X : Subgroup G} (hX : X ≤ C.Pe e) (h2 : IsPGroup 2 X) :
    X ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro x hx
  obtain ⟨hxH, hxe⟩ := (C.mem_Pe).mp (hX hx)
  obtain ⟨k, hk⟩ := h2 ⟨x, hx⟩
  have hx2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set r := FixR.rho C.h91 ⟨x, hxH⟩ with hr
  have hr5 : r ^ 5 = 1 := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxe
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he5, one_zpow]
  have hr2 : r ^ 2 ^ k = 1 := by
    rw [hr, ← map_pow]
    have : (⟨x, hxH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hx2)
    rw [this, map_one]
  have hr1 : r = 1 := by
    have h1 : orderOf r ∣ 5 := orderOf_dvd_of_pow_eq_one hr5
    have h2' : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hr2
    have : orderOf r = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num))
      h1 h2'
    exact orderOf_eq_one_iff.mp this
  exact (FixR.rho_eq_one_iff C.h91 ⟨x, hxH⟩).mp hr1

theorem pow_five_of_odd {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (he5 : e ^ 5 = 1) {x : G} (hx : x ∈ C.Pe e) (ho : Odd (orderOf x)) : x ^ 5 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx5 : x ^ 5 ∈ pCoreOf 2 H := by
    have hle := C.le_Q_of_isPGroup he5 (X := Subgroup.zpowers (x ^ 5)) ?_ ?_
    · exact hle (Subgroup.mem_zpowers _)
    · exact Subgroup.zpowers_le.mpr ((C.Pe e).pow_mem hx 5)
    ·
      obtain ⟨hxH, hxe⟩ := (C.mem_Pe).mp hx
      have hr5 : FixR.rho C.h91 ⟨x, hxH⟩ ^ 5 = 1 := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxe
        rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he5, one_zpow]
      have hq : x ^ 5 ∈ pCoreOf 2 H := by
        rw [← map_pow] at hr5
        simpa using (FixR.rho_eq_one_iff C.h91 _).mp hr5
      exact (pCoreOf_isPGroup 2 H).to_le (Subgroup.zpowers_le.mpr hq)
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hx5⟩
  have h1 : (x ^ 5) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hodd : Odd (orderOf (x ^ 5)) := Odd.of_dvd_nat ho (orderOf_pow_dvd 5)
  have h2 : orderOf (x ^ 5) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (x ^ 5) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)) dvd_rfl h2
  exact orderOf_eq_one_iff.mp h3

theorem exists_mem_K {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} (he5 : e ^ 5 = 1)
    (he1 : e ≠ 1)
    (heE : e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))) :
    ∃ z : ↥H, (z : G) ∈ oTwoUpper (C.Pe e) ∧ FixR.rho C.h91 z ≠ 1 ∧
      FixR.rho C.h91 z ∈ Subgroup.zpowers e ∧ e ∈ Subgroup.zpowers (FixR.rho C.h91 z) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, -, rfl⟩ := (FixR.mem_autOn_tilde_iff C.h91 C.hYH).mp heE
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hyP : (y : G) ∈ C.Pe (FixR.rho C.h91 y) := (C.mem_Pe).mpr ⟨y.2, Subgroup.mem_zpowers _⟩
  refine ⟨y ^ 2 ^ k, ?_, ?_, ?_, ?_⟩
  · refine mem_oTwoUpper_of_odd (by simpa using (C.Pe _).pow_mem hyP (2 ^ k)) ?_
    have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
    have : orderOf ((y : G) ^ 2 ^ k) = m := by
      rw [orderOf_pow' _ h2k, Subgroup.orderOf_coe, hkm, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (by positivity)]
    simpa [this] using hm
  · rw [map_pow]
    intro h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_eq_prime he5 he1] at hdvd
    exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd))) (by norm_num)
  · rw [map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [map_pow]
    exact A4.mem_zpowers_pow_of_coprime (by
      rw [orderOf_eq_prime he5 he1]
      exact Nat.Coprime.pow_left k (by norm_num))

theorem mem_normalizer_Pe {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} (t : ↥H)
    (ht : FixR.rho C.h91 t * e * (FixR.rho C.h91 t)⁻¹ ∈ Subgroup.zpowers e) :
    (t : G) ∈ Subgroup.normalizer (C.Pe e : Set G) := by
  have key : ∀ x ∈ C.Pe e, (t : G) * x * (t : G)⁻¹ ∈ C.Pe e := by
    intro x hx
    obtain ⟨hxH, hxe⟩ := (C.mem_Pe).mp hx
    refine (C.mem_Pe).mpr ⟨H.mul_mem (H.mul_mem t.2 hxH) (H.inv_mem t.2), ?_⟩
    have e1 : FixR.rho C.h91 ⟨(t : G) * x * (t : G)⁻¹,
        H.mul_mem (H.mul_mem t.2 hxH) (H.inv_mem t.2)⟩ =
        FixR.rho C.h91 t * FixR.rho C.h91 ⟨x, hxH⟩ * (FixR.rho C.h91 t)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxe
    rw [← hj, ← conj_zpow]
    exact Subgroup.zpow_mem _ ht j
  exact Subgroup.mem_normalizer_fintype key

end Ctx

end CFSG.Quasithin.H13.L32A.S2

end
