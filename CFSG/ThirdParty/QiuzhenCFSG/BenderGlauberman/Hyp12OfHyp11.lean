module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.DihedralStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Constructor for Hypothesis 1.2 from Hypothesis 1.1

Given a `Hyp11` structure, this module constructs the full `Hyp12` packet:
`H0' ≤ U ⊲ H0 ⊲ H`, the TI-set `T = H0 \ U` with `N_G(T) = H`, and the set
`Λ` of linear characters of `H0/U`.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

variable {G : Type u} [Group G] [Finite G]
variable (c : Hyp11 G)

section Infrastructure

/-- `O(H) ≤ H`. -/
private lemma U_le_H (c : Hyp11 G) : c.U ≤ c.H := by
  intro x hx
  simpa [Hyp11.U] using (Subgroup.map_subtype_le (pPrimeCore 2 c.H) hx)

/-- `U ⊴ H`: conjugation by any element of `H` preserves `U = O(H)`. -/
private lemma U_normal_in_H (c : Hyp11 G) {h u : G} (hh : h ∈ c.H) (hu : u ∈ c.U) :
    h * u * h⁻¹ ∈ c.U := by
  have huU : u ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
    simpa [Hyp11.U, oddCoreOf] using hu
  have huH : u ∈ c.H :=
    SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU
  have hchar : (pPrimeCore 2 c.H).Characteristic :=
    pPrimeCore_characteristic (p := 2) (G := c.H)
  have hcomap : (pPrimeCore 2 c.H) ≤ (pPrimeCore 2 c.H).comap
      (MulAut.conj ⟨h, hh⟩).toMonoidHom :=
    (Subgroup.characteristic_iff_le_comap.mp hchar) (MulAut.conj ⟨h, hh⟩)
  have huK : (⟨u, huH⟩ : ↥c.H) ∈ pPrimeCore 2 c.H := by
    rcases (Subgroup.mem_map.mp huU) with ⟨x, hx, hxeq⟩
    have hxeq' : (⟨u, huH⟩ : ↥c.H) = x := by
      ext
      simpa using hxeq.symm
    simpa [hxeq'] using hx
  have hconj : (MulAut.conj ⟨h, hh⟩) ⟨u, huH⟩ ∈ pPrimeCore 2 c.H :=
    Subgroup.mem_comap.mp (hcomap huK)
  refine (Subgroup.mem_map.mpr ?_)
  refine ⟨⟨h * u * h⁻¹, c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩, ?_, rfl⟩
  have hcx : (MulAut.conj ⟨h, hh⟩) ⟨u, huH⟩ =
      (⟨h * u * h⁻¹, c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩ : ↥c.H) := by
    ext
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hcx]
  exact hconj

/-- Every element of `S` normalizes `U = O(H)`. -/
private lemma S_le_normalizer_U (c : Hyp11 G) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact S_normalizes_U c s hs u hu
  · intro hsu
    have hs' : s⁻¹ ∈ (c.S : Subgroup G) := (c.S : Subgroup G).inv_mem hs
    have h1 := S_normalizes_U c s⁻¹ hs' (s * u * s⁻¹) hsu
    have h2 : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
    rwa [h2] at h1

/-- `S0` normalizes `U`. -/
private lemma S0_le_normalizer_U (c : Hyp11 G) :
    (c.S0 : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  exact le_trans c.S0_le_S (S_le_normalizer_U c)

/-- `U ⊴ H0`. -/
private lemma U_normal_in_H0 (c : Hyp11 G) : IsNormalIn c.U c.H0 := by
  constructor
  · exact U_le_H0 c
  · intro h hh u hu
    have hUN : c.U ≤ Subgroup.normalizer ((c.U : Subgroup G) : Set G) :=
      Subgroup.le_normalizer
    have hH0N : c.H0 ≤ Subgroup.normalizer ((c.U : Subgroup G) : Set G) :=
      sup_le hUN (S0_le_normalizer_U c)
    exact ((Subgroup.mem_normalizer_iff.mp (hH0N hh)) u).1 hu

/-- Every element of `H` decomposes as `u·s` with `u ∈ U`, `s ∈ S`. -/
private lemma H_eq_U_mul_S_local (c : Hyp11 G) {x : G} (hx : x ∈ c.H) :
    ∃ u ∈ c.U, ∃ s ∈ (c.S : Subgroup G), x = u * s := by
  have hset : (↑c.H : Set G) = (c.U : Set G) * ((c.S : Subgroup G) : Set G) := by
    rw [← c.H_eq_US]
    exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G)
      (S_le_normalizer_U c)
  have hx' : x ∈ (c.U : Set G) * ((c.S : Subgroup G) : Set G) := by
    rw [← hset]
    exact hx
  rcases hx' with ⟨u, hu, s, hs, hEq⟩
  exact ⟨u, hu, s, hs, hEq.symm⟩

/-- Every element of `H0` decomposes as `u·r` with `u ∈ U`, `r ∈ S0`. -/
private lemma H0_eq_U_mul_S0_local (c : Hyp11 G) {x : G} (hx : x ∈ c.H0) :
    ∃ u ∈ c.U, ∃ r ∈ (c.S0 : Subgroup G), x = u * r := by
  have hset : (↑c.H0 : Set G) = (c.U : Set G) * ((c.S0 : Subgroup G) : Set G) := by
    dsimp [Hyp11.H0]
    exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S0 : Subgroup G)
      (S0_le_normalizer_U c)
  have hx' : x ∈ (c.U : Set G) * ((c.S0 : Subgroup G) : Set G) := by
    rw [← hset]
    exact hx
  rcases hx' with ⟨u, hu, r, hr, hEq⟩
  exact ⟨u, hu, r, hr, hEq.symm⟩

/-- `S0` is abelian. -/
private lemma S0_comm (c : Hyp11 G) : IsMulCommutative ↥(c.S0 : Subgroup G) := by
  let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
  let : CommGroup ↥(c.S0 : Subgroup G) := IsCyclic.commGroup
  infer_instance

/-- The quotient commutativity condition `H0/U`: commutators of elements of
`H0` lie in `U`. -/
private lemma hcomm_core (c : Hyp11 G) : ∀ x y : ↥c.H0,
    (x * y) / (y * x) ∈ c.U.subgroupOf c.H0 := by
  intro x y
  apply (Subgroup.mem_subgroupOf).2
  rcases H0_eq_U_mul_S0_local c x.2 with ⟨u, hu, r, hr, hx⟩
  rcases H0_eq_U_mul_S0_local c y.2 with ⟨v, hv, s, hs, hy⟩
  have hrs : (r : G) * (s : G) = (s : G) * (r : G) := by
    exact congrArg Subtype.val
      ((isMulCommutative_iff.mp (S0_comm c)) ⟨r, hr⟩ ⟨s, hs⟩)
  have hsri : (s : G) * (r : G)⁻¹ = (r : G)⁻¹ * (s : G) := by
    calc
      (s : G) * (r : G)⁻¹ = (r : G)⁻¹ * ((r : G) * (s : G)) * (r : G)⁻¹ := by group
      _ = (r : G)⁻¹ * ((s : G) * (r : G)) * (r : G)⁻¹ := by rw [hrs]
      _ = (r : G)⁻¹ * (s : G) := by group
  have hrvs : (r : G) * (v : G) * (r : G)⁻¹ ∈ c.U :=
    (U_normal_in_H0 c).2 (r : G) (S0_le_H0 c hr) (v : G) hv
  have hsui : (s : G) * (u : G)⁻¹ * (s : G)⁻¹ ∈ c.U :=
    (U_normal_in_H0 c).2 (s : G) (S0_le_H0 c hs) (u : G)⁻¹ (c.U.inv_mem hu)
  have hEq : ((x : G) * (y : G)) / ((y : G) * (x : G)) =
      (u : G) * ((r : G) * (v : G) * (r : G)⁻¹) *
        ((s : G) * (u : G)⁻¹ * (s : G)⁻¹) * (v : G)⁻¹ := by
    rw [hx, hy]
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      (u : G) * (r : G) * ((v : G) * (s : G)) *
          ((r : G)⁻¹ * (u : G)⁻¹ * ((s : G)⁻¹ * (v : G)⁻¹))
          = (u : G) * (r : G) * (v : G) * (s : G) *
              ((r : G)⁻¹ * (u : G)⁻¹ * (s : G)⁻¹ * (v : G)⁻¹) := by group
      _ = (u : G) * (r : G) * (v : G) * ((s : G) * (r : G)⁻¹) *
              (u : G)⁻¹ * (s : G)⁻¹ * (v : G)⁻¹ := by group
      _ = (u : G) * (r : G) * (v : G) * ((r : G)⁻¹ * (s : G)) *
              (u : G)⁻¹ * (s : G)⁻¹ * (v : G)⁻¹ := by rw [hsri]
      _ = (u : G) * ((r : G) * (v : G) * (r : G)⁻¹) *
              ((s : G) * (u : G)⁻¹ * (s : G)⁻¹) * (v : G)⁻¹ := by group
  change ((x : G) * (y : G)) / ((y : G) * (x : G)) ∈ c.U
  rw [hEq]
  exact c.U.mul_mem (c.U.mul_mem (c.U.mul_mem hu hrvs) hsui) (c.U.inv_mem hv)

/-- `H0' ≤ U`. -/
private lemma H0_comm_le_U (c : Hyp11 G) : ⁅c.H0, c.H0⁆ ≤ c.U := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hc : ((x : G) * (y : G)) / ((y : G) * (x : G)) = ⁅(x : G), (y : G)⁆ := by
    rw [commutatorElement_def]
    simp [div_eq_mul_inv, mul_inv_rev]
    group
  have hU : ((x : G) * (y : G)) / ((y : G) * (x : G)) ∈ c.U := by
    simpa using (Subgroup.mem_subgroupOf.mp (hcomm_core c ⟨x, hx⟩ ⟨y, hy⟩))
  rw [← hc]
  exact hU

/-- `H0 ⊴ H`. -/
private lemma H0_normal_in_H (c : Hyp11 G) : IsNormalIn c.H0 c.H := by
  constructor
  · exact sup_le (U_le_H c) (le_trans c.S0_le_S (S_le_H c))
  · intro h hh x hx
    rcases H_eq_U_mul_S_local c hh with ⟨u, hu, s, hs, heq⟩
    rcases H0_eq_U_mul_S0_local c hx with ⟨u0, hu0, s0, hs0, hxeq⟩
    have hmemU0 : s * (u0 : G) * s⁻¹ ∈ c.U :=
      U_normal_in_H c (S_le_H c hs) hu0
    have hmemS0 : s * (s0 : G) * s⁻¹ ∈ (c.S0 : Subgroup G) :=
      S_conj_mem_S0 c hs hs0
    have hprod : (u : G) * (s * (u0 : G) * s⁻¹) * (s * (s0 : G) * s⁻¹) ∈ c.H0 :=
      c.H0.mul_mem (c.H0.mul_mem (U_le_H0 c hu) (U_le_H0 c hmemU0))
        (S0_le_H0 c hmemS0)
    have htail : (u : G)⁻¹ ∈ c.H0 := c.H0.inv_mem (U_le_H0 c hu)
    have hEq : h * x * h⁻¹ =
        (u : G) * (s * (u0 : G) * s⁻¹) * (s * (s0 : G) * s⁻¹) * (u : G)⁻¹ := by
      rw [heq, hxeq]
      group
    rw [hEq]
    exact c.H0.mul_mem hprod htail

end Infrastructure

section TISet

/-- `U` has odd order. -/
private lemma U_coprime_two (c : Hyp11 G) : Nat.Coprime 2 (Nat.card ↥c.U) := by
  have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
    dsimp [Hyp11.U]
    rw [oddCoreOf]
    exact Subgroup.card_map_of_injective (f := c.H.subtype)
      (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
  rw [h1]
  exact pPrimeCore_coprime_card (p := 2) (G := c.H)

/-- An element of the odd subgroup `U` whose square is one is trivial. -/
private lemma U_sq_eq_one (c : Hyp11 G) {u : G} (hu : u ∈ c.U) (hsq : u ^ 2 = 1) :
    u = 1 := by
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := U_coprime_two c
  have hordU : orderOf u ∣ Nat.card ↥c.U := by
    have hord' : orderOf (⟨u, hu⟩ : ↥c.U) ∣ Nat.card ↥c.U :=
      orderOf_dvd_natCard (⟨u, hu⟩ : ↥c.U)
    simpa using hord'
  have hord2 : orderOf u ∣ 2 :=
    (orderOf_dvd_iff_pow_eq_one (x := u) (n := 2)).mpr hsq
  have hord1 : orderOf u = 1 := by
    have hdvd : orderOf u ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hord2 hordU
    exact Nat.dvd_one.mp hdvd
  exact orderOf_eq_one_iff.mp hord1

/-- A power of a decomposed element `x = u·r` stays in `U·r^n`. -/
private lemma exists_U_mul_pow_S0 (c : Hyp11 G) {x r u : G} (hx : x = u * r)
    (hu : u ∈ c.U) (hr : r ∈ (c.S0 : Subgroup G)) (n : ℕ) :
    ∃ w ∈ c.U, x ^ n = w * (r : G) ^ n := by
  classical
  induction n with
  | zero =>
      refine ⟨1, c.U.one_mem, ?_⟩
      simp
  | succ k ih =>
      rcases ih with ⟨w, hw, hpow⟩
      have hrkS0 : (r : G) ^ k ∈ (c.S0 : Subgroup G) := (c.S0 : Subgroup G).pow_mem hr k
      have hconjU : (r : G) ^ k * u * ((r : G) ^ k)⁻¹ ∈ c.U :=
        (U_normal_in_H0 c).2 ((r : G) ^ k) (S0_le_H0 c hrkS0) u hu
      refine ⟨w * ((r : G) ^ k * u * ((r : G) ^ k)⁻¹),
        c.U.mul_mem hw hconjU, ?_⟩
      calc
        x ^ (k + 1) = (w * (r : G) ^ k) * (u : G) * (r : G) := by
          rw [pow_succ, hpow, hx]
          group
        _ = (w * ((r : G) ^ k * u * ((r : G) ^ k)⁻¹)) * (r : G) ^ (k + 1) := by
          group

/-- Elements of `T = H0 \ U` have even order. -/
private lemma T_even_order (c : Hyp11 G) {x : G} (hxT : x ∈ c.T) :
    2 ∣ orderOf x := by
  rcases H0_eq_U_mul_S0_local c hxT.1 with ⟨u, hu, r, hr, hx⟩
  have hr1 : r ≠ 1 := by
    intro hr1
    apply hxT.2
    rw [hx, hr1, mul_one]
    exact hu
  have hS0p : IsPGroup 2 ↥(c.S0 : Subgroup G) := by
    apply IsPGroup.of_card (n := c.m)
    simpa using S0_nat_card c
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2sub : 2 ∣ orderOf (⟨r, hr⟩ : ↥(c.S0 : Subgroup G)) :=
    IsPGroup.dvd_orderOf (p := 2) hS0p (by
    intro h
    apply hr1
    have htyped : (⟨r, hr⟩ : ↥(c.S0 : Subgroup G)) = 1 := h
    have hval : (r : G) = 1 := by
      simpa using congrArg Subtype.val htyped
    exact hval)
  have h2r : 2 ∣ orderOf r := by
    simpa using h2sub
  have hxpow1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  rcases exists_U_mul_pow_S0 c hx hu hr (orderOf x) with ⟨w, hw, hpow⟩
  have hx' : w * (r : G) ^ orderOf x = 1 := by
    rw [← hpow]
    exact hxpow1
  have hw_eq : w = ((r : G) ^ orderOf x)⁻¹ := by
    calc
      w = (w * (r : G) ^ orderOf x) * ((r : G) ^ orderOf x)⁻¹ := by group
      _ = 1 * ((r : G) ^ orderOf x)⁻¹ := by rw [hx']
      _ = ((r : G) ^ orderOf x)⁻¹ := by simp
  have hwS : w ∈ (c.S0 : Subgroup G) := by
    rw [hw_eq]
    exact (c.S0 : Subgroup G).inv_mem ((c.S0 : Subgroup G).pow_mem hr (orderOf x))
  have hw1 : w = 1 := U_inter_S0_eq_bot c hw hwS
  have hrN : (r : G) ^ orderOf x = 1 := by
    simpa [hw1] using hx'
  have hordx : orderOf r ∣ orderOf x :=
    orderOf_dvd_of_pow_eq_one (x := r) hrN
  exact dvd_trans h2r hordx

/-- The power `x ^ (orderOf x / 2)` of an element of `T` is an involution in
`T`. -/
private lemma T_half_pow (c : Hyp11 G) {x : G} (hxT : x ∈ c.T) :
    IsInvolution (x ^ (orderOf x / 2)) ∧ x ^ (orderOf x / 2) ∈ c.T := by
  let z := x ^ (orderOf x / 2)
  have h2x := T_even_order c hxT
  have hordz : orderOf z = 2 := by
    dsimp [z]
    exact orderOf_pow_orderOf_div (x := x) (n := 2) (orderOf_pos x).ne' h2x
  have hz_sq : z ^ 2 = 1 := by
    calc
      z ^ 2 = z ^ (orderOf z) := by rw [hordz]
      _ = 1 := pow_orderOf_eq_one z
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hord1 : orderOf (1 : G) = 1 := by simp
    rw [hz1] at hordz
    norm_num at hordz
  have hzInv : IsInvolution z := ⟨hz_ne, hz_sq⟩
  have hzH0 : z ∈ c.H0 := c.H0.pow_mem hxT.1 (orderOf x / 2)
  have hznotU : z ∉ c.U := by
    intro hzU
    have hzU1 : z = 1 := U_sq_eq_one c hzU hz_sq
    exact hz_ne hzU1
  simpa [z] using ⟨hzInv, ⟨hzH0, hznotU⟩⟩

/-- `t` is the unique involution in `T`. -/
private lemma unique_involution_T (c : Hyp11 G) {z : G} (hz : IsInvolution z)
    (hzT : z ∈ c.T) : z = c.t := by
  rcases H0_eq_U_mul_S0_local c hzT.1 with ⟨u, hu, r, hr, hzdecomp⟩
  have hr1 : r ≠ 1 := by
    intro hr1
    apply hzT.2
    rw [hzdecomp, hr1, mul_one]
    exact hu
  rcases exists_U_mul_pow_S0 c hzdecomp hu hr 2 with ⟨w, hw, hpow⟩
  have hz2 : z ^ 2 = 1 := hz.2
  have hw_eq : w = ((r : G) ^ 2)⁻¹ := by
    calc
      w = w * 1 := by simp
      _ = w * ((r : G) ^ 2 * ((r : G) ^ 2)⁻¹) := by group
      _ = (w * (r : G) ^ 2) * ((r : G) ^ 2)⁻¹ := by group
      _ = 1 * ((r : G) ^ 2)⁻¹ := by
        rw [← hpow, hz2]
      _ = ((r : G) ^ 2)⁻¹ := by simp
  have hcomm_t_u : (c.t : G) * (u : G) = (u : G) * (c.t : G) := by
    have huH : u ∈ c.H := U_le_H c hu
    rw [c.H_eq_centralizer] at huH
    rw [Subgroup.mem_centralizer_iff] at huH
    exact huH c.t (by simp)
  have hr2 : (r : G) ^ 2 = 1 := by
    have hwS : w ∈ (c.S0 : Subgroup G) := by
      rw [hw_eq]
      exact (c.S0 : Subgroup G).inv_mem ((c.S0 : Subgroup G).pow_mem hr 2)
    have hw1 : w = 1 := U_inter_S0_eq_bot c hw hwS
    have h := hpow.symm.trans hz2
    simpa [hw1] using h
  have hr_t : r = c.t := by
    have hsq : (⟨r, hr⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow] using hr2
    rcases (S0_sq_eq_one_iff c (x := ⟨r, hr⟩)).1 hsq with h1 | ht
    · exfalso
      exact hr1 (by simpa using congrArg Subtype.val h1)
    · exact congrArg Subtype.val ht
  have hu1 : u = 1 := by
    have hzsq : (u : G) ^ 2 = 1 := by
      have hzt : z = (u : G) * (c.t : G) := by
        rw [hzdecomp, hr_t]
      have ht2 : (c.t : G) * (c.t : G) = 1 := by
        simpa [pow_two] using c.t_involution.2
      have hreorder : ((u : G) * (c.t : G)) * ((u : G) * (c.t : G)) =
          (u : G) ^ 2 * ((c.t : G) * (c.t : G)) := by
        calc
          ((u : G) * (c.t : G)) * ((u : G) * (c.t : G))
              = (u : G) * ((c.t : G) * (u : G)) * (c.t : G) := by group
          _ = (u : G) * ((u : G) * (c.t : G)) * (c.t : G) := by rw [hcomm_t_u]
          _ = (u : G) * (u : G) * (c.t : G) * (c.t : G) := by group
          _ = (u : G) ^ 2 * ((c.t : G) * (c.t : G)) := by rw [pow_two]; group
      calc
        (u : G) ^ 2 = (u : G) ^ 2 * ((c.t : G) * (c.t : G)) := by
          rw [ht2, mul_one]
        _ = ((u : G) * (c.t : G)) * ((u : G) * (c.t : G)) := by
          rw [← hreorder]
        _ = (z : G) ^ 2 := by
          rw [← hzt, pow_two]
        _ = 1 := hz.2
    exact U_sq_eq_one c hu hzsq
  rw [hzdecomp, hu1, hr_t, one_mul]

/-- An element centralizing `t` lies in `H`. -/
private lemma mem_H_of_conj_t (c : Hyp11 G) {g : G} (hgt : g * c.t * g⁻¹ = c.t) :
    g ∈ c.H := by
  have hgt_comm : g * c.t = c.t * g := by
    calc
      g * c.t = (g * c.t * g⁻¹) * g := by group
      _ = c.t * g := by rw [hgt]
  rw [c.H_eq_centralizer]
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  simp at hh
  rw [hh]
  exact hgt_comm.symm

/-- `H` normalizes `T`. -/
private lemma H_le_normalizer_T (c : Hyp11 G) :
    c.H ≤ Subgroup.normalizer c.T := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  ext x
  constructor
  · intro hxImg
    rcases hxImg with ⟨t, htT, hxeq⟩
    dsimp [Hyp11.T] at htT ⊢
    constructor
    · have htH0 : t ∈ c.H0 := htT.1
      have hh0 : h * t * h⁻¹ ∈ c.H0 := (H0_normal_in_H c).2 h hh t htH0
      rw [← hxeq]
      exact hh0
    · intro hxU
      apply htT.2
      have hxeq' : h * t * h⁻¹ = x := by
        simpa [MulAut.conj_apply] using hxeq
      have hconjU : h * t * h⁻¹ ∈ c.U := by
        rwa [hxeq']
      have hpre : h⁻¹ * (h * t * h⁻¹) * h ∈ c.U :=
        by
          simpa using U_normal_in_H c (c.H.inv_mem hh) hconjU
      have hpre2 : h⁻¹ * (h * t * h⁻¹) * h = t := by group
      rwa [hpre2] at hpre
  · intro hxT
    refine ⟨h⁻¹ * x * h, ?_, ?_⟩
    · dsimp [Hyp11.T]
      constructor
      · simpa using (H0_normal_in_H c).2 h⁻¹ (c.H.inv_mem hh) x hxT.1
      · intro hpreU
        have hxU : x ∈ c.U := by
          have h1 := U_normal_in_H c hh hpreU
          have h2 : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
          rwa [h2] at h1
        exact hxT.2 hxU
    · change h * (h⁻¹ * x * h) * h⁻¹ = x
      group

/-- `t ∈ T`. -/
private lemma t_mem_T (c : Hyp11 G) : c.t ∈ c.T := by
  dsimp [Hyp11.T]
  constructor
  · exact S0_le_H0 c c.t_mem_S0
  · exact t_not_mem_U c

/-- The normalizer of `T` lies in `H`. -/
private lemma N_le_H (c : Hyp11 G) : Subgroup.normalizer c.T ≤ c.H := by
  intro g hg
  have hgtT : g * c.t * g⁻¹ ∈ c.T :=
    ((Subgroup.mem_set_normalizer_iff.mp hg) c.t).1 (t_mem_T c)
  have hgtInv : IsInvolution (g * c.t * g⁻¹) := by
    constructor
    · intro h1
      have ht1 : c.t = 1 := by
        calc
          c.t = g⁻¹ * (g * c.t * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h1]
          _ = 1 := by group
      exact c.t_involution.1 ht1
    · have ht2 : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
      have hsq' : (g * c.t * g⁻¹) ^ 2 = g * (c.t * c.t) * g⁻¹ := by
        rw [pow_two]
        group
      have hsq : (g * c.t * g⁻¹) ^ 2 = 1 := by
        calc
          (g * c.t * g⁻¹) ^ 2 = g * (c.t * c.t) * g⁻¹ := hsq'
          _ = 1 := by rw [ht2]; group
      exact hsq
  have hgt : g * c.t * g⁻¹ = c.t := unique_involution_T c hgtInv hgtT
  exact mem_H_of_conj_t c hgt

/-- `T` is a TI-set. -/
private lemma T_is_TI (c : Hyp11 G) : IsTISet c.T := by
  unfold IsTISet
  intro g
  by_cases hEq : (fun t : G => g * t * g⁻¹) '' c.T = c.T
  · exact Or.inl hEq
  · right
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hx with ⟨hxT, hxImg⟩
    rcases hxImg with ⟨y, hyT, hyEq⟩
    let n := orderOf x / 2
    have hxInv := (T_half_pow c hxT).1
    have hxTpow : x ^ n ∈ c.T := (T_half_pow c hxT).2
    have hyEq' : g * y * g⁻¹ = x := by
      simpa using hyEq
    have hord_eq : orderOf y = orderOf x := by
      have hsc : SemiconjBy g y x := by
        change g * y = x * g
        calc
          g * y = (g * y * g⁻¹) * g := by group
          _ = x * g := by rw [hyEq']
      exact SemiconjBy.orderOf_eq g hsc
    have hyInv : IsInvolution (y ^ n) := by
      simpa [n, hord_eq] using (T_half_pow c hyT).1
    have hyTpow : y ^ n ∈ c.T := by
      simpa [n, hord_eq] using (T_half_pow c hyT).2
    have hxpow_t : x ^ n = c.t := unique_involution_T c hxInv hxTpow
    have hypow_t : y ^ n = c.t := unique_involution_T c hyInv hyTpow
    have hconjpow : g * (y ^ n) * g⁻¹ = (g * y * g⁻¹) ^ n := by
      induction n with
      | zero => simp
      | succ k ih =>
          calc
            g * (y ^ (k + 1)) * g⁻¹ = (g * (y ^ k) * g⁻¹) * (g * y * g⁻¹) := by group
            _ = (g * y * g⁻¹) ^ k * (g * y * g⁻¹) := by rw [ih]
            _ = (g * y * g⁻¹) ^ (k + 1) := by rw [pow_succ]
    have hconjpow' : g * (y ^ n) * g⁻¹ = x ^ n := by
      calc
        g * (y ^ n) * g⁻¹ = (g * y * g⁻¹) ^ n := hconjpow
        _ = x ^ n := by rw [hyEq']
    have hgt : g * c.t * g⁻¹ = c.t := by
      calc
        g * c.t * g⁻¹ = g * (y ^ n) * g⁻¹ := by rw [← hypow_t]
        _ = x ^ n := hconjpow'
        _ = c.t := hxpow_t
    have hgH : g ∈ c.H := mem_H_of_conj_t c hgt
    have hgN : g ∈ Subgroup.normalizer c.T := H_le_normalizer_T c hgH
    have hEq' : (fun t : G => g * t * g⁻¹) '' c.T = c.T :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp hgN
    exact hEq hEq'

/-- `N_G(T) = H`. -/
private lemma T_normalizer (c : Hyp11 G) : Subgroup.normalizer c.T = c.H :=
  le_antisymm (N_le_H c) (H_le_normalizer_T c)

end TISet

/-- The full Hypothesis 1.2 packet constructed from Hypothesis 1.1. -/
public noncomputable def hyp12_of_hyp11 (c : Hyp11 G) : Hyp12 c where
  H0_comm_le_U := H0_comm_le_U c
  U_normal_in_H0 := U_normal_in_H0 c
  H0_normal_in_H := H0_normal_in_H c
  T_is_TI := T_is_TI c
  T_normalizer := T_normalizer c
  Lambda := {lam : ClassFunction (↥c.H0) | IsLinearCharacter lam ∧
    ∀ u : ↥c.H0, (u : G) ∈ c.U → lam u = 1}
  Lambda_eq := rfl

end CFSG.BenderGlauberman
