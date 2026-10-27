module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinDefs
import Mathlib.Tactic.Group
import Mathlib.Data.Fintype.Prod

public section

namespace CFSG.Quasithin.NoE9Z4MinGrp

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def InC (Q Uc : Subgroup G) (x : G) : Prop := x ∈ Q ∧ ∀ u ∈ Uc, ⁅u, x⁆ = 1

theorem InC_one {Q : Subgroup G} (Uc : Subgroup G) : InC Q Uc 1 :=
  ⟨Q.one_mem, fun u _ => by simp [commutatorElement_def]⟩

@[expose] def Ec (g x : G) : G := x * (g⁻¹ * x * g) * (g⁻¹ * g⁻¹ * x * g * g)

@[expose] def Eu (g u : G) : G := u * (g * u * g⁻¹) * (g * g * u * g⁻¹ * g⁻¹)

namespace PairCtx

variable {Q U Z Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Hs z)
include P

theorem Ec_mem {g x : G} (hg : g ∈ Hs) (hx : x ∈ Q) : Ec g x ∈ Q := by
  have h1 : g⁻¹ * x * g ∈ Q := by
    have := P.normQ g⁻¹ (inv_mem hg) x hx
    simpa using this
  have h2 : g⁻¹ * g⁻¹ * x * g * g ∈ Q := by
    have := P.normQ (g⁻¹ * g⁻¹) (mul_mem (inv_mem hg) (inv_mem hg)) x hx
    simpa [mul_assoc] using this
  exact Q.mul_mem (Q.mul_mem hx h1) h2

theorem pair_Ec {g : G} (hg : g ∈ Hs) {u : G} (hu : u ∈ U) {x : G} (hx : x ∈ Q) :
    ⁅u, Ec g x⁆ = ⁅Eu g u, x⁆ := by
  have hx1 : g⁻¹ * x * g ∈ Q := by
    have := P.normQ g⁻¹ (inv_mem hg) x hx
    simpa using this
  have hx2 : g⁻¹ * g⁻¹ * x * g * g ∈ Q := by
    have := P.normQ (g⁻¹ * g⁻¹) (mul_mem (inv_mem hg) (inv_mem hg)) x hx
    simpa [mul_assoc] using this
  have hu1 : g * u * g⁻¹ ∈ U := P.normU g hg u hu
  have hu2 : g * g * u * g⁻¹ * g⁻¹ ∈ U := by
    have := P.normU (g * g) (mul_mem hg hg) u hu
    simpa [mul_assoc] using this
  have e1 : ⁅u, g⁻¹ * x * g⁆ = ⁅g * u * g⁻¹, x⁆ := by
    have h := P.pair_conj hg hu hx1
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e] at h
    exact h.symm
  have e2 : ⁅u, g⁻¹ * g⁻¹ * x * g * g⁆ = ⁅g * g * u * g⁻¹ * g⁻¹, x⁆ := by
    have hgg : g * g ∈ Hs := mul_mem hg hg
    have h := P.pair_conj hgg hu hx2
    have e : g * g * (g⁻¹ * g⁻¹ * x * g * g) * (g * g)⁻¹ = x := by group
    have e' : g * g * u * (g * g)⁻¹ = g * g * u * g⁻¹ * g⁻¹ := by group
    rw [e, e'] at h
    exact h.symm
  unfold Ec Eu
  rw [P.pair_mul_right hu (Q.mul_mem hx hx1) hx2, P.pair_mul_right hu hx hx1, e1, e2,
    P.pair_mul_left (U.mul_mem hu hu1) hu2 hx, P.pair_mul_left hu hu1 hx]

theorem pair_Z_mul {c u : G} (hc : c ∈ Z) (hu : u ∈ U) {x : G} (hx : x ∈ Q) :
    ⁅c * u, x⁆ = ⁅u, x⁆ := by
  rw [P.pair_mul_left (P.Z_le_U hc) hu hx, P.pair_one_of_mem_Z hc hx, one_mul]

theorem pair_conj_triv {g u : G} (hg : g ∈ Hs) (hu : u ∈ U) (h : ⁅g, u⁆ ∈ Z) {x : G}
    (hx : x ∈ Q) : ⁅g * u * g⁻¹, x⁆ = ⁅u, x⁆ := by
  rw [(P.conj_of_comm_mem_Z hg h).1, P.pair_Z_mul h hu hx]

theorem pair_conj_inv_triv {g u : G} (hg : g ∈ Hs) (hu : u ∈ U) (h : ⁅g, u⁆ ∈ Z) {x : G}
    (hx : x ∈ Q) : ⁅g⁻¹ * u * g, x⁆ = ⁅u, x⁆ := by
  rw [(P.conj_of_comm_mem_Z hg h).2, P.pair_Z_mul h hu hx]

theorem fix_inv {h y : G} (hh : h ∈ Hs) (hfix : y⁻¹ * (h * y * h⁻¹) ∈ U) :
    y⁻¹ * (h⁻¹ * y * h) ∈ U := by
  have h1 := P.normU h⁻¹ (inv_mem hh) _ hfix
  have e : h⁻¹ * (y⁻¹ * (h * y * h⁻¹)) * h⁻¹⁻¹ = (h⁻¹ * y * h)⁻¹ * y := by group
  rw [e] at h1
  have := U.inv_mem h1
  simpa using this

theorem fix_sq {h y : G} (hh : h ∈ Hs) (hfix : y⁻¹ * (h * y * h⁻¹) ∈ U) :
    y⁻¹ * (h * h * y * (h * h)⁻¹) ∈ U := by
  have h1 := P.normU h hh _ hfix
  have e : (y⁻¹ * (h * y * h⁻¹)) * (h * (y⁻¹ * (h * y * h⁻¹)) * h⁻¹)
      = y⁻¹ * (h * h * y * (h * h)⁻¹) := by group
  rw [← e]
  exact U.mul_mem hfix h1

theorem T_shift_left {h : G} (hh : h ∈ Hs) {x y q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q)
    (hfy : y⁻¹ * (h * y * h⁻¹) ∈ U) (hfq : q⁻¹ * (h * q * h⁻¹) ∈ U) :
    T (h * x * h⁻¹) y q = T x y q := by
  have hx' := P.normQ h hh x hx
  have hy' := P.normQ h hh y hy
  have hq' := P.normQ h hh q hq
  rw [P.T_congr_mid hx' hy hy' hq hfy, P.T_congr_right hx' hy' hq hq' hfq, P.T_conj hh hx hy hq]

theorem T_shift_right {h : G} (hh : h ∈ Hs) {x y q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q)
    (hfx : x⁻¹ * (h * x * h⁻¹) ∈ U) (hfy : y⁻¹ * (h * y * h⁻¹) ∈ U) :
    T x y (h * q * h⁻¹) = T x y q := by
  have hx' := P.normQ h hh x hx
  have hy' := P.normQ h hh y hy
  have hq' := P.normQ h hh q hq
  rw [← P.T_conj hh hx hy hq, P.T_congr_left hx hx' hy hq' hfx,
    P.T_congr_mid hx' hy hy' hq' hfy]

theorem eq_one_of_mul_mul {t : G} (ht : t ∈ Z) (h : t * t * t = 1) : t = 1 := by
  have := P.Z_sq ht
  rw [mul_assoc, this, mul_one] at h
  exact h

theorem InC_mul {Uc : Subgroup G} (hUc : Uc ≤ U) {x y : G} (hx : InC Q Uc x) (hy : InC Q Uc y) :
    InC Q Uc (x * y) :=
  ⟨Q.mul_mem hx.1 hy.1, fun u hu => by
    rw [P.pair_mul_right (hUc hu) hx.1 hy.1, hx.2 u hu, hy.2 u hu, mul_one]⟩

omit P in
theorem T_one_mid (x q : G) : PairCtx.T x 1 q = 1 := by
  show ⁅⁅x, (1 : G)⁆, q⁆ = (1 : G)
  simp [commutatorElement_def]

omit P in
theorem T_one_right (x y : G) : PairCtx.T x y 1 = 1 := by
  show ⁅⁅x, y⁆, (1 : G)⁆ = (1 : G)
  simp [commutatorElement_def]

theorem Z_eq_of_mul_eq_one {c d : G} (hd : d ∈ Z) (h : c * d = 1) : c = d := by
  have hdd := P.Z_sq hd
  calc c = c * (d * d) := by rw [hdd, mul_one]
    _ = (c * d) * d := by rw [mul_assoc]
    _ = d := by rw [h, one_mul]

end PairCtx

namespace WtCtx

variable {Q U Z Hs : Subgroup G} {z : G} {P : PairCtx Q U Z Hs z} {a b : G} {Ua Ub : Subgroup G}
  (W : WtCtx P a b Ua Ub)
include W

theorem Eu_a_Ua {u : G} (hu : u ∈ Ua) {x : G} (hx : x ∈ Q) : ⁅Eu a u, x⁆ = 1 :=
  P.pair_one_of_mem_Z (W.a_kill u hu) hx

theorem Eu_a_Ub {u : G} (hu : u ∈ Ub) {x : G} (hx : x ∈ Q) : ⁅Eu a u, x⁆ = ⁅u, x⁆ := by
  have huU : u ∈ U := W.Ub_le hu
  have h1c : ⁅a, u⁆ ∈ Z := W.a_triv u hu
  have hu1 : a * u * a⁻¹ ∈ Ub := by
    rw [(P.conj_of_comm_mem_Z W.a_mem h1c).1]
    exact Ub.mul_mem (W.Z_le_Ub h1c) hu
  have hu1U := W.Ub_le hu1
  have h2c : ⁅a, a * u * a⁻¹⁆ ∈ Z := W.a_triv _ hu1
  have e2 : a * a * u * a⁻¹ * a⁻¹ = a * (a * u * a⁻¹) * a⁻¹ := by group
  have hu2U : a * (a * u * a⁻¹) * a⁻¹ ∈ U := P.normU a W.a_mem _ hu1U
  unfold Eu
  rw [e2, P.pair_mul_left (U.mul_mem huU hu1U) hu2U hx, P.pair_mul_left huU hu1U hx,
    P.pair_conj_triv W.a_mem hu1U h2c hx, P.pair_conj_triv W.a_mem huU h1c hx, mul_assoc,
    P.pair_sq huU hx, mul_one]

theorem pair_Ecb {ua ub : G} (hua : ua ∈ Ua) (hub : ub ∈ Ub) {x : G} (hx : x ∈ Q) :
    ⁅ua * ub, Ec b x⁆ = ⁅ua, x⁆ := by
  have hb := W.b_mem
  have huaU := W.Ua_le hua
  have hubU := W.Ub_le hub
  rw [P.pair_mul_left huaU hubU (P.Ec_mem hb hx), P.pair_Ec hb huaU hx, P.pair_Ec hb hubU hx,
    W.symm.Eu_a_Ub hua hx, W.symm.Eu_a_Ua hub hx, mul_one]

theorem pair_Eca {ua ub : G} (hua : ua ∈ Ua) (hub : ub ∈ Ub) {x : G} (hx : x ∈ Q) :
    ⁅ua * ub, Ec a x⁆ = ⁅ub, x⁆ := by
  have ha := W.a_mem
  have huaU := W.Ua_le hua
  have hubU := W.Ub_le hub
  rw [P.pair_mul_left huaU hubU (P.Ec_mem ha hx), P.pair_Ec ha huaU hx, P.pair_Ec ha hubU hx,
    W.Eu_a_Ua hua hx, W.Eu_a_Ub hub hx, one_mul]

theorem InC_Ec_b {x : G} (hx : x ∈ Q) : InC Q Ub (Ec b x) :=
  ⟨P.Ec_mem W.b_mem hx, fun u hu => by
    rw [P.pair_Ec W.b_mem (W.Ub_le hu) hx, W.symm.Eu_a_Ua hu hx]⟩

theorem InC_Ec_a {x : G} (hx : x ∈ Q) : InC Q Ua (Ec a x) :=
  ⟨P.Ec_mem W.a_mem hx, fun u hu => by
    rw [P.pair_Ec W.a_mem (W.Ua_le hu) hx, W.Eu_a_Ua hu hx]⟩

theorem decomp_Q {x : G} (hx : x ∈ Q) : x⁻¹ * (Ec b x * Ec a x) ∈ U := by
  refine P.pair_ext hx (Q.mul_mem (P.Ec_mem W.b_mem hx) (P.Ec_mem W.a_mem hx)) fun u hu => ?_
  obtain ⟨ua, hua, ub, hub, rfl⟩ := W.decomp u hu
  rw [P.pair_mul_right (U.mul_mem (W.Ua_le hua) (W.Ub_le hub)) (P.Ec_mem W.b_mem hx)
    (P.Ec_mem W.a_mem hx), W.pair_Ecb hua hub hx, W.pair_Eca hua hub hx,
    P.pair_mul_left (W.Ua_le hua) (W.Ub_le hub) hx]

theorem Ec_a_mem_U {x : G} (hx : InC Q Ub x) : Ec a x ∈ U := by
  refine P.ker_left _ (P.Ec_mem W.a_mem hx.1) fun u hu => ?_
  obtain ⟨ua, hua, ub, hub, rfl⟩ := W.decomp u hu
  rw [W.pair_Eca hua hub hx.1, hx.2 ub hub]

theorem conj_b_cong {x : G} (hx : InC Q Ub x) : x⁻¹ * (b * x * b⁻¹) ∈ U := by
  have hb := W.b_mem
  refine P.pair_ext hx.1 (P.normQ b hb x hx.1) fun u hu => ?_
  obtain ⟨ua, hua, ub, hub, rfl⟩ := W.decomp u hu
  have huaU := W.Ua_le hua
  have hubU := W.Ub_le hub
  have e : b⁻¹ * (ua * ub) * b = (b⁻¹ * ua * b) * (b⁻¹ * ub * b) := by group
  have h1 : b⁻¹ * ua * b ∈ U := by
    have := P.normU b⁻¹ (inv_mem hb) ua huaU
    simpa using this
  have h2 : b⁻¹ * ub * b ∈ U := by
    have := P.normU b⁻¹ (inv_mem hb) ub hubU
    simpa using this
  rw [P.pair_conj_inv hb (U.mul_mem huaU hubU) hx.1, e, P.pair_mul_left h1 h2 hx.1,
    P.pair_conj_inv_triv hb huaU (W.b_triv ua hua) hx.1, hx.2 _ (W.b_inv ub hub),
    P.pair_mul_left huaU hubU hx.1, hx.2 ub hub]

theorem InC_conj_a {x : G} (hx : InC Q Ub x) : InC Q Ub (a * x * a⁻¹) :=
  ⟨P.normQ a W.a_mem x hx.1, fun u hu => by
    rw [P.pair_conj_inv W.a_mem (W.Ub_le hu) hx.1,
      P.pair_conj_inv_triv W.a_mem (W.Ub_le hu) (W.a_triv u hu) hx.1, hx.2 u hu]⟩

theorem mixed {x y q : G} (hx : InC Q Ub x) (hy : InC Q Ua y) (hq : InC Q Ua q) :
    PairCtx.T x y q = 1 ∧ PairCtx.T y x q = 1 ∧ PairCtx.T y q x = 1 := by
  have ha := W.a_mem
  have hai : a⁻¹ ∈ Hs := inv_mem ha
  have haai : a⁻¹ * a⁻¹ ∈ Hs := mul_mem hai hai
  have hE : Ec a x ∈ U := W.Ec_a_mem_U hx
  have fy1 : y⁻¹ * (a⁻¹ * y * a⁻¹⁻¹) ∈ U := by
    have := P.fix_inv ha (W.symm.conj_b_cong hy)
    simpa using this
  have fq1 : q⁻¹ * (a⁻¹ * q * a⁻¹⁻¹) ∈ U := by
    have := P.fix_inv ha (W.symm.conj_b_cong hq)
    simpa using this
  have fy2 := P.fix_sq hai fy1
  have fq2 := P.fix_sq hai fq1
  have hx1 : a⁻¹ * x * a ∈ Q := by
    have := P.normQ a⁻¹ hai x hx.1
    simpa using this
  have hx2 : a⁻¹ * a⁻¹ * x * a * a ∈ Q := by
    have := P.normQ (a⁻¹ * a⁻¹) haai x hx.1
    simpa [mul_assoc] using this
  have e1 : a⁻¹ * x * a = a⁻¹ * x * a⁻¹⁻¹ := by rw [inv_inv]
  have e2 : a⁻¹ * a⁻¹ * x * a * a = (a⁻¹ * a⁻¹) * x * (a⁻¹ * a⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv]; simp only [mul_assoc]
  have h1 : PairCtx.T x y q = 1 := by
    have h0 : PairCtx.T (Ec a x) y q = 1 := P.T_of_mem_U_left hE hy.1 hq.1
    unfold Ec at h0
    rw [P.T_mul_left (Q.mul_mem hx.1 hx1) hx2 hy.1 hq.1, P.T_mul_left hx.1 hx1 hy.1 hq.1,
      e1, e2, P.T_shift_left hai hx.1 hy.1 hq.1 fy1 fq1,
      P.T_shift_left haai hx.1 hy.1 hq.1 fy2 fq2] at h0
    exact P.eq_one_of_mul_mul (P.T_mem_Z hx.1 hy.1 hq.1) h0
  refine ⟨h1, by rw [P.T_swap hx.1 hy.1 hq.1]; exact h1, ?_⟩
  have h0 : PairCtx.T y q (Ec a x) = 1 := P.T_of_mem_U_right hy.1 hq.1 hE
  unfold Ec at h0
  rw [P.T_mul_right hy.1 hq.1 (Q.mul_mem hx.1 hx1) hx2, P.T_mul_right hy.1 hq.1 hx.1 hx1,
    e1, e2, P.T_shift_right hai hy.1 hq.1 hx.1 fy1 fq1,
    P.T_shift_right haai hy.1 hq.1 hx.1 fy2 fq2] at h0
  exact P.eq_one_of_mul_mul (P.T_mem_Z hy.1 hq.1 hx.1) h0

omit [Group G] W in
theorem fin_pigeon : ∀ pe pf py : Bool × Bool, pe ≠ (false, false) → pf ≠ (false, false) →
    pe ≠ pf → py = (false, false) ∨ py = pe ∨ py = pf ∨
      py = (xor pe.1 pf.1, xor pe.2 pf.2) := by decide

open Classical in
theorem pigeon {e f y : G} (he : InC Q Ub e) (hf : InC Q Ub f) (hy : InC Q Ub y)
    (heU : e ∉ U) (hfU : f ∉ U) (hef : e⁻¹ * f ∉ U) :
    y⁻¹ * 1 ∈ U ∨ y⁻¹ * e ∈ U ∨ y⁻¹ * f ∈ U ∨ y⁻¹ * (e * f) ∈ U := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hgen⟩ := W.a_gen
  have hw₁U := W.Ua_le hw₁
  have hw₂U := W.Ua_le hw₂
  have claimA : ∀ t t' : G, InC Q Ub t → InC Q Ub t' → ⁅w₁, t⁆ = ⁅w₁, t'⁆ →
      ⁅w₂, t⁆ = ⁅w₂, t'⁆ → t⁻¹ * t' ∈ U := by
    intro t t' ht ht' h1 h2
    refine P.pair_ext ht.1 ht'.1 fun u hu => ?_
    obtain ⟨ua, hua, ub, hub, rfl⟩ := W.decomp u hu
    have huaU := W.Ua_le hua
    have hubU := W.Ub_le hub
    rw [P.pair_mul_left huaU hubU ht.1, P.pair_mul_left huaU hubU ht'.1, ht.2 ub hub,
      ht'.2 ub hub, mul_one, mul_one]
    obtain ⟨c, hc, hu'⟩ := hgen ua hua
    have hcU := P.Z_le_U hc
    have hc1 := P.pair_one_of_mem_Z hc ht.1
    have hc1' := P.pair_one_of_mem_Z hc ht'.1
    rcases hu' with rfl | rfl | rfl | rfl
    · rw [hc1, hc1']
    · rw [P.pair_mul_left hw₁U hcU ht.1, P.pair_mul_left hw₁U hcU ht'.1, hc1, hc1', h1]
    · rw [P.pair_mul_left hw₂U hcU ht.1, P.pair_mul_left hw₂U hcU ht'.1, hc1, hc1', h2]
    · rw [P.pair_mul_left (U.mul_mem hw₁U hw₂U) hcU ht.1,
        P.pair_mul_left (U.mul_mem hw₁U hw₂U) hcU ht'.1, hc1, hc1',
        P.pair_mul_left hw₁U hw₂U ht.1, P.pair_mul_left hw₁U hw₂U ht'.1, h1, h2]
  have hz2 : z * z = 1 := P.Z_sq P.z_mem
  have hz1 : z ≠ 1 := P.z_ne
  let bit : G → Bool := fun c => decide (c = z)
  have hZ : ∀ u ∈ U, ∀ t ∈ Q, ⁅u, t⁆ = 1 ∨ ⁅u, t⁆ = z := fun u hu t ht =>
    P.Z_eq _ (P.pair_mem u hu t ht)
  have h1z : (1 : G) ≠ z := hz1.symm
  have bit_eq : ∀ c d : G, (c = 1 ∨ c = z) → (d = 1 ∨ d = z) → bit c = bit d → c = d := by
    intro c d hc hd h
    rcases hc with hc | hc <;> rcases hd with hd | hd <;> simp [bit, hc, hd, h1z] at h ⊢
  have bit_mul : ∀ c d : G, (c = 1 ∨ c = z) → (d = 1 ∨ d = z) →
      bit (c * d) = xor (bit c) (bit d) := by
    intro c d hc hd
    rcases hc with hc | hc <;> rcases hd with hd | hd <;> simp [bit, hc, hd, h1z, hz2]
  have bit_one : bit 1 = false := by simp [bit, hz1.symm]
  let pr : G → Bool × Bool := fun t => (bit ⁅w₁, t⁆, bit ⁅w₂, t⁆)
  have pr_mul : ∀ t t' : G, t ∈ Q → t' ∈ Q →
      pr (t * t') = (xor (pr t).1 (pr t').1, xor (pr t).2 (pr t').2) := by
    intro t t' ht ht'
    simp only [pr]
    rw [P.pair_mul_right hw₁U ht ht', P.pair_mul_right hw₂U ht ht',
      bit_mul _ _ (hZ _ hw₁U t ht) (hZ _ hw₁U t' ht'),
      bit_mul _ _ (hZ _ hw₂U t ht) (hZ _ hw₂U t' ht')]
  have pr_one : pr 1 = (false, false) := by
    simp [pr, commutatorElement_def, bit_one]
  have claim' : ∀ t t' : G, InC Q Ub t → InC Q Ub t' → pr t = pr t' → t⁻¹ * t' ∈ U := by
    intro t t' ht ht' h
    have h1 : bit ⁅w₁, t⁆ = bit ⁅w₁, t'⁆ := congrArg Prod.fst h
    have h2 : bit ⁅w₂, t⁆ = bit ⁅w₂, t'⁆ := congrArg Prod.snd h
    exact claimA t t' ht ht' (bit_eq _ _ (hZ _ hw₁U t ht.1) (hZ _ hw₁U t' ht'.1) h1)
      (bit_eq _ _ (hZ _ hw₂U t ht.1) (hZ _ hw₂U t' ht'.1) h2)
  have hone := InC_one (Q := Q) Ub
  have hefC := P.InC_mul W.Ub_le he hf
  have hne : pr e ≠ (false, false) := fun h => heU (by
    have := claim' e 1 he hone (h.trans pr_one.symm)
    simpa using this)
  have hnf : pr f ≠ (false, false) := fun h => hfU (by
    have := claim' f 1 hf hone (h.trans pr_one.symm)
    simpa using this)
  have hnef : pr e ≠ pr f := fun h => hef (claim' e f he hf h)
  rcases fin_pigeon (pr e) (pr f) (pr y) hne hnf hnef with h | h | h | h
  · exact Or.inl (claim' y 1 hy hone (h.trans pr_one.symm))
  · exact Or.inr (Or.inl (claim' y e hy he h))
  · exact Or.inr (Or.inr (Or.inl (claim' y f hy hf h)))
  · refine Or.inr (Or.inr (Or.inr (claim' y (e * f) hy hefC ?_)))
    rw [pr_mul e f he.1 hf.1]
    exact h

theorem not_cong {e : G} (he : InC Q Ub e) (heU : e ∉ U) : e⁻¹ * (a * e * a⁻¹) ∉ U := by
  intro hu
  have ha := W.a_mem
  obtain ⟨f, hf_def⟩ : ∃ f, f = a * e * a⁻¹ := ⟨_, rfl⟩
  rw [← hf_def] at hu
  have hf : InC Q Ub f := hf_def ▸ W.InC_conj_a he
  obtain ⟨g₂, hg₂_def⟩ : ∃ g₂, g₂ = a * f * a⁻¹ := ⟨_, rfl⟩
  have hg₂ : InC Q Ub g₂ := hg₂_def ▸ W.InC_conj_a hf
  have hEc : Ec a g₂ = g₂ * f * e := by
    unfold Ec
    have e1 : a⁻¹ * g₂ * a = f := by rw [hg₂_def]; group
    have e2 : a⁻¹ * a⁻¹ * g₂ * a * a = e := by
      rw [hg₂_def, hf_def]
      group
    rw [e1, e2]
  have hW1 : g₂ * f * e ∈ U := hEc ▸ W.Ec_a_mem_U hg₂
  obtain ⟨u₁, hu₁def⟩ : ∃ u₁, u₁ = e⁻¹ * f := ⟨_, rfl⟩
  rw [← hu₁def] at hu
  have hfe : f = e * u₁ := by rw [hu₁def]; group
  have hu₃ : a * u₁ * a⁻¹ ∈ U := P.normU a ha _ hu
  have hg₂e : g₂ = e * u₁ * (a * u₁ * a⁻¹) := by
    calc g₂ = a * f * a⁻¹ := hg₂_def
      _ = (a * e * a⁻¹) * (a * (e⁻¹ * f) * a⁻¹) := by group
      _ = f * (a * u₁ * a⁻¹) := by rw [← hf_def, ← hu₁def]
      _ = e * u₁ * (a * u₁ * a⁻¹) := by rw [hfe]
  have hee : e⁻¹ * e⁻¹ ∈ Hs := mul_mem (inv_mem (P.Q_le_H he.1)) (inv_mem (P.Q_le_H he.1))
  have hconj1 : e⁻¹ * e⁻¹ * (u₁ * (a * u₁ * a⁻¹)) * (e * e) ∈ U := by
    have := P.normU (e⁻¹ * e⁻¹) hee _ (U.mul_mem hu hu₃)
    simpa [mul_assoc] using this
  have hconj2 : e⁻¹ * u₁ * e ∈ U := by
    have := P.normU e⁻¹ (inv_mem (P.Q_le_H he.1)) _ hu
    simpa using this
  have h3 : e⁻¹ * e⁻¹ * e⁻¹ * (g₂ * f * e) ∈ U := by
    have e3 : e⁻¹ * e⁻¹ * e⁻¹ * (g₂ * f * e) =
        (e⁻¹ * e⁻¹ * (u₁ * (a * u₁ * a⁻¹)) * (e * e)) * (e⁻¹ * u₁ * e) := by
      rw [hg₂e, hfe]
      group
    rw [e3]
    exact U.mul_mem hconj1 hconj2
  have h4 : e⁻¹ * e⁻¹ * e⁻¹ ∈ U := by
    have e4 : e⁻¹ * e⁻¹ * e⁻¹ = (e⁻¹ * e⁻¹ * e⁻¹ * (g₂ * f * e)) * (g₂ * f * e)⁻¹ := by group
    rw [e4]
    exact U.mul_mem h3 (U.inv_mem hW1)
  have h5 : e ∈ U := by
    have h6 := U.mul_mem (U.inv_mem h4) (U.inv_mem (P.sq_mem_U he.1))
    have e6 : (e⁻¹ * e⁻¹ * e⁻¹)⁻¹ * (e * e)⁻¹ = e := by group
    rwa [e6] at h6
  exact heU h5

theorem AAA {x y q : G} (hx : InC Q Ub x) (hy : InC Q Ub y) (hq : InC Q Ub q) :
    PairCtx.T x y q = 1 := by
  by_cases hxU : x ∈ U
  · exact P.T_of_mem_U_left hxU hy.1 hq.1
  have ha := W.a_mem
  obtain ⟨f, hf_def⟩ : ∃ f, f = a * x * a⁻¹ := ⟨_, rfl⟩
  have hf : InC Q Ub f := hf_def ▸ W.InC_conj_a hx
  obtain ⟨g₂, hg₂_def⟩ : ∃ g₂, g₂ = a * f * a⁻¹ := ⟨_, rfl⟩
  have hg₂ : InC Q Ub g₂ := hg₂_def ▸ W.InC_conj_a hf
  have hEc : Ec a g₂ = g₂ * f * x := by
    unfold Ec
    have e1 : a⁻¹ * g₂ * a = f := by rw [hg₂_def]; group
    have e2 : a⁻¹ * a⁻¹ * g₂ * a * a = x := by
      rw [hg₂_def, hf_def]
      group
    rw [e1, e2]
  have hEU : g₂ * f * x ∈ U := hEc ▸ W.Ec_a_mem_U hg₂
  have hxQ := hx.1
  have hfQ := hf.1
  have hg₂Q := hg₂.1
  have Rl : ∀ y' q' : G, y' ∈ Q → q' ∈ Q →
      PairCtx.T g₂ y' q' * PairCtx.T f y' q' * PairCtx.T x y' q' = 1 := by
    intro y' q' hy' hq'
    have h0 := P.T_of_mem_U_left hEU hy' hq'
    rw [P.T_mul_left (Q.mul_mem hg₂Q hfQ) hxQ hy' hq', P.T_mul_left hg₂Q hfQ hy' hq'] at h0
    exact h0
  have Rr : ∀ x' y' : G, x' ∈ Q → y' ∈ Q →
      PairCtx.T x' y' g₂ * PairCtx.T x' y' f * PairCtx.T x' y' x = 1 := by
    intro x' y' hx' hy'
    have h0 := P.T_of_mem_U_right hx' hy' hEU
    rw [P.T_mul_right hx' hy' (Q.mul_mem hg₂Q hfQ) hxQ, P.T_mul_right hx' hy' hg₂Q hfQ] at h0
    exact h0
  have inv1 : PairCtx.T f g₂ f = PairCtx.T x f x := by
    have := P.T_conj ha hxQ hfQ hxQ
    rw [← hf_def, ← hg₂_def] at this
    exact this
  have inv2 : PairCtx.T f g₂ g₂ = PairCtx.T x f f := by
    have := P.T_conj ha hxQ hfQ hfQ
    rw [← hf_def, ← hg₂_def] at this
    exact this
  have hZ3 : ∀ x' y' q' : G, x' ∈ Q → y' ∈ Q → q' ∈ Q → PairCtx.T x' y' q' ∈ Z :=
    fun x' y' q' hx' hy' hq' => P.T_mem_Z hx' hy' hq'
  have e1 : PairCtx.T x f x = PairCtx.T x f f := by
    have h1 := Rl f f hfQ hfQ
    rw [PairCtx.T_self f f, mul_one] at h1
    have h2 : PairCtx.T g₂ f f = PairCtx.T x f f :=
      P.Z_eq_of_mul_eq_one (hZ3 x f f hxQ hfQ hfQ) h1
    rw [← inv1, P.T_swap hg₂Q hfQ hfQ, h2]
  have e2 : PairCtx.T x f x = 1 := by
    have h1 := Rl f g₂ hfQ hg₂Q
    rw [PairCtx.T_self f g₂, mul_one] at h1
    have h2 : PairCtx.T g₂ f g₂ = PairCtx.T x f g₂ :=
      P.Z_eq_of_mul_eq_one (hZ3 x f g₂ hxQ hfQ hg₂Q) h1
    have h3 := Rr x f hxQ hfQ
    have h4 : PairCtx.T x f f = PairCtx.T x f g₂ := by
      rw [← inv2, P.T_swap hg₂Q hfQ hg₂Q, h2]
    rw [← h4, ← e1] at h3
    rw [P.Z_sq (hZ3 x f x hxQ hfQ hxQ), one_mul] at h3
    exact h3
  have e3 : PairCtx.T x f f = 1 := by rw [← e1]; exact e2
  have hfU : f ∉ U := fun h => hxU (by
    have := P.normU a⁻¹ (inv_mem ha) f h
    have e : a⁻¹ * f * a⁻¹⁻¹ = x := by rw [hf_def]; group
    rwa [e] at this)
  have hef : x⁻¹ * f ∉ U := hf_def ▸ W.not_cong hx hxU
  have hxfC : x * f ∈ Q := Q.mul_mem hxQ hfQ
  have hmemS : ∀ s : G, (s = 1 ∨ s = x ∨ s = f ∨ s = x * f) → s ∈ Q := by
    intro s hs
    rcases hs with hs | hs | hs | hs
    · rw [hs]; exact Q.one_mem
    · rw [hs]; exact hxQ
    · rw [hs]; exact hfQ
    · rw [hs]; exact hxfC
  have tf : ∀ s : G, (s = 1 ∨ s = x ∨ s = f ∨ s = x * f) → PairCtx.T x f s = 1 := by
    intro s hs
    rcases hs with hs | hs | hs | hs
    · rw [hs]; exact PairCtx.T_one_right x f
    · rw [hs]; exact e2
    · rw [hs]; exact e3
    · rw [hs, P.T_mul_right hxQ hfQ hxQ hfQ, e2, e3, mul_one]
  have tab : ∀ s s' : G, (s = 1 ∨ s = x ∨ s = f ∨ s = x * f) →
      (s' = 1 ∨ s' = x ∨ s' = f ∨ s' = x * f) → PairCtx.T x s s' = 1 := by
    intro s s' hs hs'
    rcases hs with hs | hs | hs | hs
    · rw [hs]; exact PairCtx.T_one_mid x s'
    · rw [hs]; exact PairCtx.T_self x s'
    · rw [hs]; exact tf s' hs'
    · rw [hs, P.T_mul_mid hxQ hxQ hfQ (hmemS s' hs'), PairCtx.T_self x s', one_mul]
      exact tf s' hs'
  have cy : ∃ s : G, (s = 1 ∨ s = x ∨ s = f ∨ s = x * f) ∧ y⁻¹ * s ∈ U := by
    rcases W.pigeon hx hf hy hxU hfU hef with h | h | h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨x, Or.inr (Or.inl rfl), h⟩
    · exact ⟨f, Or.inr (Or.inr (Or.inl rfl)), h⟩
    · exact ⟨x * f, Or.inr (Or.inr (Or.inr rfl)), h⟩
  have cq : ∃ s : G, (s = 1 ∨ s = x ∨ s = f ∨ s = x * f) ∧ q⁻¹ * s ∈ U := by
    rcases W.pigeon hx hf hq hxU hfU hef with h | h | h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨x, Or.inr (Or.inl rfl), h⟩
    · exact ⟨f, Or.inr (Or.inr (Or.inl rfl)), h⟩
    · exact ⟨x * f, Or.inr (Or.inr (Or.inr rfl)), h⟩
  obtain ⟨sy, hsy, hy'⟩ := cy
  obtain ⟨sq, hsq, hq'⟩ := cq
  rw [P.T_congr_mid hxQ hy.1 (hmemS sy hsy) hq.1 hy',
    P.T_congr_right hxQ (hmemS sy hsy) hq.1 (hmemS sq hsq) hq']
  exact tab sy sq hsy hsq

theorem T_basic {x y q : G} (hx : InC Q Ub x ∨ InC Q Ua x) (hy : InC Q Ub y ∨ InC Q Ua y)
    (hq : InC Q Ub q ∨ InC Q Ua q) : PairCtx.T x y q = 1 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hq with hq | hq
  · exact W.AAA hx hy hq
  · exact (W.symm.mixed hq hx hy).2.2
  · exact (W.symm.mixed hy hx hq).2.1
  · exact (W.mixed hx hy hq).1
  · exact (W.symm.mixed hx hy hq).1
  · exact (W.mixed hy hx hq).2.1
  · exact (W.mixed hq hx hy).2.2
  · exact W.symm.AAA hx hy hq

theorem T_slot1 {y q : G} (hy : y ∈ Q) (hq : q ∈ Q)
    (h : ∀ x : G, (InC Q Ub x ∨ InC Q Ua x) → PairCtx.T x y q = 1) {x : G} (hx : x ∈ Q) :
    PairCtx.T x y q = 1 := by
  have hxA := W.InC_Ec_b hx
  have hxB := W.InC_Ec_a hx
  rw [P.T_congr_left hx (Q.mul_mem hxA.1 hxB.1) hy hq (W.decomp_Q hx),
    P.T_mul_left hxA.1 hxB.1 hy hq, h _ (Or.inl hxA), h _ (Or.inr hxB), mul_one]

theorem T_slot2 {x q : G} (hx : x ∈ Q) (hq : q ∈ Q)
    (h : ∀ y : G, (InC Q Ub y ∨ InC Q Ua y) → PairCtx.T x y q = 1) {y : G} (hy : y ∈ Q) :
    PairCtx.T x y q = 1 := by
  have hyA := W.InC_Ec_b hy
  have hyB := W.InC_Ec_a hy
  rw [P.T_congr_mid hx hy (Q.mul_mem hyA.1 hyB.1) hq (W.decomp_Q hy),
    P.T_mul_mid hx hyA.1 hyB.1 hq, h _ (Or.inl hyA), h _ (Or.inr hyB), mul_one]

theorem T_slot3 {x y : G} (hx : x ∈ Q) (hy : y ∈ Q)
    (h : ∀ q : G, (InC Q Ub q ∨ InC Q Ua q) → PairCtx.T x y q = 1) {q : G} (hq : q ∈ Q) :
    PairCtx.T x y q = 1 := by
  have hqA := W.InC_Ec_b hq
  have hqB := W.InC_Ec_a hq
  rw [P.T_congr_right hx hy hq (Q.mul_mem hqA.1 hqB.1) (W.decomp_Q hq),
    P.T_mul_right hx hy hqA.1 hqB.1, h _ (Or.inl hqA), h _ (Or.inr hqB), mul_one]

theorem T_all {x y q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q) :
    PairCtx.T x y q = 1 := by
  have hQ : ∀ t : G, (InC Q Ub t ∨ InC Q Ua t) → t ∈ Q := fun t ht => by
    rcases ht with ht | ht <;> exact ht.1
  have s1 : ∀ y' q' : G, (InC Q Ub y' ∨ InC Q Ua y') → (InC Q Ub q' ∨ InC Q Ua q') →
      ∀ x' ∈ Q, PairCtx.T x' y' q' = 1 := fun y' q' hy' hq' x' hx' =>
    W.T_slot1 (hQ y' hy') (hQ q' hq') (fun x'' hx'' => W.T_basic hx'' hy' hq') hx'
  have s2 : ∀ q' : G, (InC Q Ub q' ∨ InC Q Ua q') → ∀ x' ∈ Q, ∀ y' ∈ Q,
      PairCtx.T x' y' q' = 1 := fun q' hq' x' hx' y' hy' =>
    W.T_slot2 hx' (hQ q' hq') (fun y'' hy'' => s1 y'' q' hy'' hq' x' hx') hy'
  exact W.T_slot3 hx hy (fun q' hq' => s2 q' hq' x hx y hy) hq

theorem comm_mem_Z {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : ⁅x, y⁆ ∈ Z :=
  P.Q_comm_mem_Z hx hy fun _ hq => W.T_all hx hy hq

end WtCtx

end CFSG.Quasithin.NoE9Z4MinGrp
