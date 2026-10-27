module

public import CFSG.Quasithin.H13.A6S1372L76N3n
public import CFSG.Quasithin.H13.A6S1372L76N3l

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76N3

theorem eq_one_of_dec {N M : Type*} [Group N] [Group M] (φ : N →* M) {x₀ x : N} (h0 : φ x₀ = 1)
    {i j : ℕ} (hj : (x₀ ^ i * x) ^ 2 ^ j = 1) {m : ℕ} (hm : x ^ m = 1) (hodd : Odd m) :
    φ x = 1 := by
  have h1 : φ x ^ 2 ^ j = 1 := by
    have h2 := congrArg φ hj
    rwa [map_pow, map_mul, map_pow, h0, one_pow, one_mul, map_one] at h2
  have h3 : φ x ^ m = 1 := by rw [← map_pow, hm, map_one]
  exact eq_one_of_pow_two_pow h1 h3 hodd

theorem eq_one_of_comm_P0 {N C : Type*} [Group N] [Group C] (φ : N →* SL3.S) (ψ : N →* C)
    {x₀ : N} (hx₀ : x₀ ^ 3 = 1) (ha1 : φ x₀ ≠ 1) {g : SL3.S} {Tₛ : Set N}
    (hψT : ∀ t ∈ Tₛ, ψ t = 1)
    (hdec : ∀ t ∈ Tₛ, ∃ i : ℕ, i < 3 ∧ ∃ j : ℕ, (x₀ ^ i * (t * x₀ * t⁻¹ * x₀⁻¹)) ^ 2 ^ j = 1)
    (hP : ∀ q ∈ SL3.P0, ∃ t ∈ Tₛ, φ t = g⁻¹ * q * g) : ψ x₀ = 1 := by
  obtain ⟨a, ha⟩ : ∃ a, φ x₀ = a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, ψ x₀ = c := ⟨_, rfl⟩
  rw [ha] at ha1
  rw [hc]
  have ha3 : a ^ 3 = 1 := by rw [← ha, ← map_pow, hx₀, map_one]
  have hc3 : c ^ 3 = 1 := by rw [← hc, ← map_pow, hx₀, map_one]
  by_contra hc1
  obtain ⟨q, hq1, hq2, hq⟩ := comm_not_two (g * a * g⁻¹)
    (by rw [conj_pow, ha3, mul_one, mul_inv_cancel]) (fun h => ha1 (conj_eq_one_iff.1 h))
  obtain ⟨t, ht, hteq⟩ := hP q ⟨hq1, hq2⟩
  obtain ⟨i, hi3, j, hj⟩ := hdec t ht
  have hψm : ψ (t * x₀ * t⁻¹ * x₀⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hψT t ht]
    group
  have hψj := congrArg ψ hj
  rw [map_pow, map_mul, map_pow, hψm, mul_one, map_one, hc] at hψj
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
  · have hφj := congrArg φ hj
    rw [map_pow, pow_zero, one_mul, map_one] at hφj
    have h4 := pow_four_of_two hφj
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hteq] at h4
    apply hq
    have e : q * (g * a * g⁻¹) * q⁻¹ * (g * a * g⁻¹)⁻¹ =
        g * (g⁻¹ * q * g * a * (g⁻¹ * q * g)⁻¹ * a⁻¹) * g⁻¹ := by group
    rw [e, conj_pow, h4]
    group
  · rw [pow_one] at hψj
    exact hc1 (eq_one_of_pow_two_pow hψj hc3 (by decide))
  · have h3 : (c ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hc3, one_pow]
    have h2 := eq_one_of_pow_two_pow hψj h3 (by decide)
    apply hc1
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, h2]; group

theorem P0_le_normalizer_map {N : Type*} [Group N] (φ : N →* SL3.S) {g : SL3.S} {Tₛ : Set N}
    (hP : ∀ q ∈ SL3.P0, ∃ t ∈ Tₛ, φ t = g⁻¹ * q * g) {M : Subgroup N}
    (hTM : ∀ t ∈ Tₛ, ∀ m ∈ M, t * m * t⁻¹ ∈ M) :
    SL3.P0 ≤ Subgroup.normalizer (((M.map φ).map (MulAut.conj g).toMonoidHom :
      Subgroup SL3.S) : Set SL3.S) := by
  intro q hq
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨z, ⟨m, hm, rfl⟩, rfl⟩ := hy
  obtain ⟨t, ht, hteq⟩ := hP q hq
  refine ⟨φ (t * m * t⁻¹), ⟨t * m * t⁻¹, hTM t ht m hm, rfl⟩, ?_⟩
  show g * φ (t * m * t⁻¹) * g⁻¹ = q * (g * φ m * g⁻¹) * q⁻¹
  rw [map_mul, map_mul, map_inv, hteq]
  group

end A6L76N3

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1_le_sup_of_conj_P0 (h38 : A38ForSQTK)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (φ : ↥(H ⊓ Subgroup.normalizer (K : Set G)) →* SL3.S) {g : SL3.S}
    {Tₛ : Set ↥(H ⊓ Subgroup.normalizer (K : Set G))} (hTₛ : ∀ t ∈ Tₛ, (t : G) ∈ T)
    (hP : ∀ q ∈ SL3.P0, ∃ t ∈ Tₛ, φ t = g⁻¹ * q * g)
    (hφ1 : ∀ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)), φ n = 1 → ∀ k ∈ K,
      (n : G) * k * (n : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    {x₀ : ↥(H ⊓ Subgroup.normalizer (K : Set G))} (hx₀ : (x₀ : G) ∈ S.X1375)
    (ha3 : φ x₀ ^ 3 = 1) (ha1 : φ x₀ ≠ 1) :
    S.L1 ≤ S.X1375 ⊔ centralizerMod (pCoreOf 2 K) S.L1 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hsqtk : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  have P := S.plusData_X1375
  have hL1N : S.L1 ≤ H ⊓ Subgroup.normalizer (K : Set G) :=
    le_inf hL1H (SBc13.le_normalizer_of_odd_gen h38 hsqtk hK hL1H S.L1_le_oTwoUpper)
  have hTM : ∀ M : Subgroup G, T ≤ Subgroup.normalizer (M : Set G) → ∀ t ∈ Tₛ,
      ∀ m ∈ M.subgroupOf (H ⊓ Subgroup.normalizer (K : Set G)),
        t * m * t⁻¹ ∈ M.subgroupOf (H ⊓ Subgroup.normalizer (K : Set G)) :=
    fun M hM t ht m hm => Subgroup.mem_subgroupOf.2
      ((Subgroup.mem_normalizer_iff.mp (hM (hTₛ t ht)) m).mp (Subgroup.mem_subgroupOf.1 hm))
  have hnormX := A6L76N3.P0_le_normalizer_map φ hP (hTM S.X1375 P.T_le)
  have hnormL := A6L76N3.P0_le_normalizer_map φ hP (hTM S.L1 S.T_le_normalizer_L1)
  have hAB : ((S.X1375.subgroupOf (H ⊓ Subgroup.normalizer (K : Set G))).map φ).map
        (MulAut.conj g).toMonoidHom ≤
      ((S.L1.subgroupOf (H ⊓ Subgroup.normalizer (K : Set G))).map φ).map
        (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono (Subgroup.map_mono fun x hx => (X1375_le_L1 (S := S)) hx)
  have ha : g * φ x₀ * g⁻¹ ∈ ((S.X1375.subgroupOf (H ⊓ Subgroup.normalizer (K : Set G))).map
      φ).map (MulAut.conj g).toMonoidHom := ⟨_, ⟨x₀, hx₀, rfl⟩, rfl⟩
  have hBe : ∀ b ∈ ((S.L1.subgroupOf (H ⊓ Subgroup.normalizer (K : Set G))).map φ).map
      (MulAut.conj g).toMonoidHom, ∃ k : ℕ, b ^ (18 * 2 ^ k) = 1 := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    obtain ⟨k, hk⟩ := S.pow_eq_one_of_mem_L1 (Subgroup.mem_subgroupOf.1 hl)
    refine ⟨k, ?_⟩
    have e : l ^ (18 * 2 ^ k) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk)
    show (g * φ l * g⁻¹) ^ (18 * 2 ^ k) = 1
    rw [conj_pow, ← map_pow, e, map_one]
    group
  have hBtop := A6L76N3.sup_P0_ne_top hnormL hBe
  refine S.L1_le_oTwoUpper.trans ((Subgroup.closure_le _).2 ?_)
  rintro l ⟨hl, hlo⟩
  have hb : g * φ ⟨l, hL1N hl⟩ * g⁻¹ ∈ ((S.L1.subgroupOf (H ⊓ Subgroup.normalizer
      (K : Set G))).map φ).map (MulAut.conj g).toMonoidHom := ⟨_, ⟨⟨l, hL1N hl⟩, hl, rfl⟩, rfl⟩
  have hbo : Odd (orderOf (g * φ ⟨l, hL1N hl⟩ * g⁻¹)) := by
    have h1 : orderOf (g * φ ⟨l, hL1N hl⟩ * g⁻¹) = orderOf (φ ⟨l, hL1N hl⟩) :=
      MulEquiv.orderOf_eq (MulAut.conj g) (φ ⟨l, hL1N hl⟩)
    rw [h1]
    exact Odd.of_dvd_nat hlo ((orderOf_map_dvd φ _).trans
      (dvd_of_eq (Subgroup.orderOf_coe (⟨l, hL1N hl⟩ :
        ↥(H ⊓ Subgroup.normalizer (K : Set G)))).symm))
  obtain ⟨_, ⟨xN, hxN, rfl⟩, hxeq⟩ := A6L76N3.odd_mem_of_overgroups hAB hnormX ha
    (by rw [conj_pow, ha3, mul_one, mul_inv_cancel]) (fun h => ha1 (conj_eq_one_iff.1 h))
    hBtop hb hbo
  have hxeq' : φ xN = φ ⟨l, hL1N hl⟩ := by
    have h1 : g * φ xN * g⁻¹ = g * φ ⟨l, hL1N hl⟩ * g⁻¹ := hxeq
    exact mul_left_cancel (mul_right_cancel h1)
  have hxX : (xN : G) ∈ S.X1375 := hxN
  have hn1 : φ (xN⁻¹ * ⟨l, hL1N hl⟩) = 1 := by rw [map_mul, map_inv, hxeq', inv_mul_cancel]
  have hC : (xN : G)⁻¹ * l ∈ centralizerMod (pCoreOf 2 K) S.L1 K := by
    refine ⟨S.L1.mul_mem (S.L1.inv_mem ((X1375_le_L1 (S := S)) hxX)) hl,
      normalizer_le_normalizer_pCoreOf 2 K (xN⁻¹ * ⟨l, hL1N hl⟩).2.2, fun k hk => ?_⟩
    rw [← GoldS146R.inf_pCoreOf_eq_of_mem_cComp hK]
    refine ⟨?_, hφ1 _ hn1 k hk⟩
    have hk' : ((xN⁻¹ * ⟨l, hL1N hl⟩ : ↥(H ⊓ Subgroup.normalizer (K : Set G))) : G) * k *
        ((xN⁻¹ * ⟨l, hL1N hl⟩ : ↥(H ⊓ Subgroup.normalizer (K : Set G))) : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (xN⁻¹ * ⟨l, hL1N hl⟩).2.2 k).mp hk
    exact K.mul_mem hk' (K.inv_mem hk)
  have e : l = (xN : G) * ((xN : G)⁻¹ * l) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hxX hC

theorem L1_le_of_natSL32 (h139 : Stmt13_3_9) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (hNS : ¬ LieModel G .PSp 3 2 1) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H)
    (D : A6L76N3.NatReal (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
    (hc : ∃ x ∈ S.X1375, ∃ hxH : x ∈ H, ∃ y ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)),
      A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) ⟨x, hxH⟩ * y ≠
        y * A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) ⟨x, hxH⟩) :
    S.L1 ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have P := S.plusData_X1375
  have hXN : S.X1375 ≤ H ⊓ Subgroup.normalizer (K : Set G) :=
    le_inf (X1375_le_H hH) (X1375_le_normalizer h38 hH hK)
  have hKN : K ≤ H ⊓ Subgroup.normalizer (K : Set G) := le_inf hKH Subgroup.le_normalizer
  obtain ⟨σ, hσdef⟩ : ∃ f, f = S.secActN hH hK := ⟨_, rfl⟩
  have hσcoe : ∀ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
      (σ n).1 = A6Mod.secAct hHU hHV ⟨n, n.2.1⟩ := fun n => by subst hσdef; rfl
  obtain ⟨φ, hφdef⟩ : ∃ f, f = D.phiN.comp σ := ⟨_, rfl⟩
  have hφapp : ∀ n, φ n = D.phiN (σ n) := fun n => by subst hφdef; rfl
  obtain ⟨ψ, hψdef⟩ : ∃ f, f = D.cN.comp σ := ⟨_, rfl⟩
  have hψapp : ∀ n, ψ n = D.cN (σ n) := fun n => by subst hψdef; rfl
  have hσK : ∀ (k : G) (hk : k ∈ K), σ ⟨k, hKN hk⟩ = A6L76N3.incY
      ⟨_, (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩⟩ :=
    fun k hk => Subtype.ext (hσcoe _)
  have hψK : ∀ (k : G) (hk : k ∈ K), ψ ⟨k, hKN hk⟩ = 1 := fun k hk => by
    rw [hψapp, hσK k hk]
    exact D.cN_incY _
  have hQ : ∀ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)), σ n = 1 →
      (n : G) ∈ pCoreOf 2 H := fun n hn =>
    (S.mem_QH_iff_tilde hNS h13315 h1356two hH n.2.1).2
      ((A6Mod.secAct_eq_one_iff hHU hHV _).1 ((hσcoe n).symm.trans (congrArg Subtype.val hn)))
  have hφ1 : ∀ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)), φ n = 1 → ∀ k ∈ K,
      (n : G) * k * (n : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    intro n hn k hk
    have hc2 : σ n * σ ⟨k, hKN hk⟩ = σ ⟨k, hKN hk⟩ * σ n := by
      rw [hσK k hk]
      exact Subtype.ext (D.comm_of_phiN_eq_one (n := σ n) ((hφapp n).symm.trans hn)
        ⟨_, (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩⟩)
    refine hQ (n * ⟨k, hKN hk⟩ * n⁻¹ * ⟨k, hKN hk⟩⁻¹) ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc2]
    group
  obtain ⟨x₀, hx₀X, hx₀ρ, hx₀3⟩ := S.exists_X1375_c012_cube
  obtain ⟨x₀N, hx₀N⟩ : ∃ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (n : G) = x₀ :=
    ⟨⟨x₀, hXN hx₀X⟩, rfl⟩
  have hx₀N3 : x₀N ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hx₀N]; exact hx₀3)
  have hx₀NX : (x₀N : G) ∈ S.X1375 := by rw [hx₀N]; exact hx₀X
  have hdec : ∀ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (n : G) ∈ S.X1375 →
      ∃ i : ℕ, i < 3 ∧ ∃ j : ℕ, (x₀N ^ i * n) ^ 2 ^ j = 1 := by
    intro n hn
    have h2 : ∀ y : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (y : G) ∈ pCoreOf 2 S.X1375 →
        ∃ j : ℕ, y ^ 2 ^ j = 1 := by
      intro y hy
      obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 S.X1375 ⟨(y : G), hy⟩
      exact ⟨j, Subtype.ext (by simpa using congrArg Subtype.val hj)⟩
    rcases S.X1375_decomp hx₀X hx₀ρ hn with h | h | h
    · obtain ⟨j, hj⟩ := h2 n h
      exact ⟨0, by norm_num, j, by rw [pow_zero, one_mul]; exact hj⟩
    · refine ⟨2, by norm_num, h2 _ ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_pow, hx₀N, pow_two]
      exact h
    · refine ⟨1, by norm_num, h2 _ ?_⟩
      rw [Subgroup.coe_mul, pow_one, hx₀N]
      exact h
  have hpowodd : ∀ (x : G) (hx : x ∈ H ⊓ Subgroup.normalizer (K : Set G)),
      (⟨x, hx⟩ : ↥(H ⊓ Subgroup.normalizer (K : Set G))) ^ orderOf x = 1 :=
    fun x hx => Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one x)
  have ha1 : φ x₀N ≠ 1 := by
    intro ha1
    have hle : S.X1375 ≤ (φ.ker).map (H ⊓ Subgroup.normalizer (K : Set G)).subtype := by
      refine (X1375_le_oTwoUpper (S := S)).trans ((Subgroup.closure_le _).2 ?_)
      rintro x ⟨hx, hxo⟩
      obtain ⟨i, -, j, hj⟩ := hdec ⟨x, hXN hx⟩ hx
      exact ⟨⟨x, hXN hx⟩, MonoidHom.mem_ker.2 (A6L76N3.eq_one_of_dec φ ha1 hj
        (hpowodd x (hXN hx)) hxo), rfl⟩
    obtain ⟨x, hxX, hxH, y, hy, hne⟩ := hc
    apply hne
    obtain ⟨n, hn, hnx⟩ := hle hxX
    have e : n = ⟨x, hXN hxX⟩ := Subtype.ext hnx
    rw [e] at hn
    have h := D.comm_of_phiN_eq_one (n := σ ⟨x, hXN hxX⟩)
      ((hφapp _).symm.trans (MonoidHom.mem_ker.1 hn)) ⟨y, hy⟩
    rw [hσcoe] at h
    exact h
  obtain ⟨φK, hφKdef⟩ : ∃ f : ↥K →* SL3.S, f = φ.comp (Subgroup.inclusion hKN) := ⟨_, rfl⟩
  have hφK : Function.Surjective φK := by
    intro A
    obtain ⟨y, hy⟩ := D.phiY_bijective.2 A
    obtain ⟨f, hfK, hf⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 y.2
    refine ⟨⟨(f : G), hfK⟩, ?_⟩
    have e : σ (Subgroup.inclusion hKN ⟨(f : G), hfK⟩) = A6L76N3.incY y :=
      Subtype.ext ((hσcoe _).trans hf)
    rw [hφKdef, MonoidHom.comp_apply, hφapp, e]
    exact hy
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hsyl := S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hK) hTs
  have hP2 : IsPGroup 2 ↥(((T ⊓ K).subgroupOf K).map φK) :=
    (hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm).map φK
  have hPodd : ¬ 2 ∣ (((T ⊓ K).subgroupOf K).map φK).index := fun hd =>
    hsyl.2.2 (hd.trans (Subgroup.index_map_dvd _ hφK))
  obtain ⟨g, hg⟩ := A6L76N3.exists_conj_P0 hP2 hPodd
  have hga : ∀ q ∈ SL3.P0, ∃ t ∈ {n : ↥(H ⊓ Subgroup.normalizer (K : Set G)) | (n : G) ∈ T ⊓ K},
      φ t = g⁻¹ * q * g := by
    intro q hq
    obtain ⟨t', ht', hteq⟩ := hg q hq
    rw [hφKdef, MonoidHom.comp_apply] at hteq
    exact ⟨Subgroup.inclusion hKN t', Subgroup.mem_subgroupOf.1 ht', hteq⟩
  have hmX : ∀ t : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (t : G) ∈ T ⊓ K →
      ((t * x₀N * t⁻¹ * x₀N⁻¹ : ↥(H ⊓ Subgroup.normalizer (K : Set G))) : G) ∈ S.X1375 := by
    intro t ht
    show (t : G) * x₀N * (t : G)⁻¹ * (x₀N : G)⁻¹ ∈ S.X1375
    exact S.X1375.mul_mem ((Subgroup.mem_normalizer_iff.mp (P.T_le ht.1) _).mp hx₀NX)
      (S.X1375.inv_mem hx₀NX)
  have hc1 : ψ x₀N = 1 := A6L76N3.eq_one_of_comm_P0 φ ψ hx₀N3 ha1
    (fun t ht => hψK t ht.2) (fun t ht => hdec _ (hmX t ht)) hga
  have hXK : S.X1375 ≤ K := by
    refine (X1375_le_oTwoUpper (S := S)).trans ((Subgroup.closure_le _).2 ?_)
    rintro x ⟨hx, hxo⟩
    obtain ⟨i, -, j, hj⟩ := hdec ⟨x, hXN hx⟩ hx
    have hψx := A6L76N3.eq_one_of_dec ψ hc1 hj (hpowodd x (hXN hx)) hxo
    have hmem := D.mem_of_cN_eq_one (n := σ ⟨x, hXN hx⟩) ((hψapp _).symm.trans hψx)
    obtain ⟨f, hfK, hf⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hmem
    have hfx : (f : G)⁻¹ * x ∈ H ⊓ Subgroup.normalizer (K : Set G) :=
      (H ⊓ Subgroup.normalizer (K : Set G)).mul_mem (Subgroup.inv_mem _ (hKN hfK)) (hXN hx)
    have hq : (f : G)⁻¹ * x ∈ pCoreOf 2 H := by
      refine hQ ⟨_, hfx⟩ (Subtype.ext ?_)
      rw [hσcoe]
      show A6Mod.secAct hHU hHV ⟨(f : G)⁻¹ * x, hfx.1⟩ = 1
      have e : (⟨(f : G)⁻¹ * x, hfx.1⟩ : ↥H) = f⁻¹ * ⟨x, (hXN hx).1⟩ := Subtype.ext rfl
      rw [e, map_mul, map_inv, hf, hσcoe]
      exact inv_mul_cancel _
    have h4 := A6L76N3.mem_of_odd_of_mul_QH hK hfK hq (by rwa [mul_inv_cancel_left])
    rwa [mul_inv_cancel_left] at h4
  by_contra hL1K
  have : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    A6L76A.isSimpleGroup_statedSL (le_refl 3) (by simp)
  have : Nontrivial SL3.S := ⟨⟨SL3.s1, 1, by decide⟩⟩
  have : Nontrivial ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := D.phiYEquiv.toEquiv.nontrivial
  have hrad := A6L76A.rad_eq_bot_of_surjective
    (A6L76A.not_isSolvable_statedSL (le_refl 3)) D.π D.surj
  exact S.lem1375_seven h139 h37 h38 hH hK hXK hL1K hrad
    (S.L1_le_sup_of_conj_P0 h38 hH hK φ (fun t ht => ht.1) hga hφ1 hx₀NX
      (by rw [← map_pow, hx₀N3, map_one]) ha1)

end Setting4

theorem lem1376OddNCL32_of (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two) :
    Lem1376OddNCL32 := by
  intro G _ _ T L V S hNS _ H hH _ _ K hK hSL hc
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSL
  obtain ⟨D⟩ := A6L76N3.nonempty_natReal (by rw [hF, pow_one]) hπ
  exact S.L1_le_of_natSL32 h139 h37 h38 h13315 h1356two hNS hH hK D hc

theorem lem1376Full_holds
    (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h1337 : Stmt13_3_7) : Lem1376Full :=
  lem1376Full_of_l32 (lem1376OddNCL32_of h139 h37 h38 h13315 h1356two) hF h36 h37 h38 h139
    h13314 h13315 h1356two h1337

end CFSG.Quasithin.H13.A6
