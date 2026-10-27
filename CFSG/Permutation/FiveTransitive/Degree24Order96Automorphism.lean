module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG

namespace FiveTransitive.Degree24

open Subgroup

private theorem mem_zpowers_of_card_six_of_inverts_order_three
    (K : Type) [Group K] [Fintype K]
    (hKcard : Nat.card K = 6)
    (r t k : K)
    (hrOrder : orderOf r = 3)
    (hinverts : MulAut.conj t r = r⁻¹)
    (hcomm : Commute k r) :
    k ∈ Subgroup.zpowers r := by
  classical
  let R : Subgroup K := Subgroup.zpowers r
  let C : Subgroup K :=
    Subgroup.centralizer ({r} : Set K)
  have hRleC : R ≤ C := by
    apply Subgroup.zpowers_le.mpr
    exact
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Commute.refl r)
  have hRcard : Nat.card R = 3 := by
    rw [Nat.card_zpowers, hrOrder]
  have hRdC : 3 ∣ Nat.card C := by
    rw [← hRcard]
    exact Subgroup.card_dvd_of_le hRleC
  have hCdSix : Nat.card C ∣ 6 := by
    rw [← hKcard]
    exact Subgroup.card_subgroup_dvd_card C
  have hCcases :
      Nat.card C = 3 ∨ Nat.card C = 6 := by
    have hClower : 3 ≤ Nat.card C :=
      Nat.le_of_dvd Nat.card_pos hRdC
    have hCupper : Nat.card C ≤ 6 :=
      Nat.le_of_dvd (by norm_num) hCdSix
    have hvalues :
        Nat.card C = 3 ∨ Nat.card C = 4 ∨
          Nat.card C = 5 ∨ Nat.card C = 6 := by
      omega
    rcases hvalues with hthree | hfour | hfive | hsix
    · exact Or.inl hthree
    · rw [hfour] at hRdC
      norm_num at hRdC
    · rw [hfive] at hRdC
      norm_num at hRdC
    · exact Or.inr hsix
  have hRC : R = C := by
    rcases hCcases with hCthree | hCsix
    · apply Subgroup.eq_of_le_of_card_ge hRleC
      rw [hRcard, hCthree]
    · have hCtop : C = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        exact hCsix.trans hKcard.symm
      have htC : t ∈ C := by
        rw [hCtop]
        exact Subgroup.mem_top t
      have htComm :
          Commute t r :=
        Subgroup.mem_centralizer_singleton_iff.mp
          htC
      have hcentral :
          MulAut.conj t r = r := by
        change t * r * t⁻¹ = r
        rw [mul_inv_eq_iff_eq_mul]
        exact htComm.eq
      have hrInv : r = r⁻¹ :=
        hcentral.symm.trans hinverts
      have hrSquare : r ^ 2 = 1 := by
        calc
          r ^ 2 = r * r := pow_two r
          _ = r⁻¹ * r :=
            congrArg (fun z => z * r) hrInv
          _ = 1 := inv_mul_cancel r
      have horderDvd : orderOf r ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hrSquare
      rw [hrOrder] at horderDvd
      norm_num at horderDvd
  change k ∈ R
  rw [hRC]
  exact
    Subgroup.mem_centralizer_singleton_iff.mpr
      hcomm

noncomputable def centralizerEquivOfMulEquiv
    {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (g : G) :
    Subgroup.centralizer ({g} : Set G) ≃
      Subgroup.centralizer ({e g} : Set H) where
  toFun x :=
    ⟨e x.1, by
      apply
        Subgroup.mem_centralizer_singleton_iff.mpr
      have hx :=
        Subgroup.mem_centralizer_singleton_iff.mp
          x.prop
      simpa only [map_mul] using congrArg e hx⟩
  invFun x :=
    ⟨e.symm x.1, by
      apply
        Subgroup.mem_centralizer_singleton_iff.mpr
      have hx :=
        Subgroup.mem_centralizer_singleton_iff.mp
          x.prop
      simpa only [map_mul, e.symm_apply_apply] using
        congrArg e.symm hx⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact e.apply_symm_apply x.1

private theorem perm_six_mulEquiv_swap_support
    (F B : Type)
    [Fintype F] [DecidableEq F]
    [Fintype B] [DecidableEq B]
    (hFcard : Fintype.card F = 6)
    (hBcard : Fintype.card B = 6)
    (e : Equiv.Perm F ≃* Equiv.Perm B)
    (τ : Equiv.Perm F)
    (hτ : τ.IsSwap) :
    (e τ).support.card = 2 ∨
      (e τ).support.card = 6 := by
  classical
  let g : Equiv.Perm B := e τ
  have hτOrder : orderOf τ = 2 :=
    hτ.orderOf
  have hgOrder : orderOf g = 2 := by
    calc
      orderOf g = orderOf τ :=
        e.orderOf_eq τ
      _ = 2 := hτOrder
  have hgPrime : (orderOf g).Prime := by
    rw [hgOrder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgPrime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgOrder] at hsum
  have hgSupportLe : g.support.card ≤ 6 := by
    calc
      g.support.card ≤ Fintype.card B :=
        Finset.card_le_univ g.support
      _ = 6 := hBcard
  have hmPos : 0 < m + 1 := Nat.succ_pos m
  have hcases :
      g.support.card = 2 ∨
        g.support.card = 4 ∨
          g.support.card = 6 := by
    omega
  rcases hcases with htwo | hfour | hsix
  · exact Or.inl htwo
  · exfalso
    have hmTwo : m + 1 = 2 := by
      omega
    have hτCentralizer :
        Nat.card
            (Subgroup.centralizer
              ({τ} : Set (Equiv.Perm F))) =
          48 := by
      rw [Equiv.Perm.nat_card_centralizer,
        Equiv.Perm.isSwap_iff_cycleType.mp hτ,
        hFcard]
      norm_num
    have hgCentralizer :
        Nat.card
            (Subgroup.centralizer
              ({g} : Set (Equiv.Perm B))) =
          16 := by
      rw [Equiv.Perm.nat_card_centralizer,
        hm, hgOrder, hmTwo, hBcard]
      norm_num
    have hcardEq :
        Nat.card
            (Subgroup.centralizer
              ({τ} : Set (Equiv.Perm F))) =
          Nat.card
            (Subgroup.centralizer
              ({g} : Set (Equiv.Perm B))) := by
      exact
        Nat.card_congr
          (centralizerEquivOfMulEquiv e τ)
    rw [hτCentralizer, hgCentralizer] at hcardEq
    norm_num at hcardEq
  · exact Or.inr hsix

theorem perm_six_bijectiveHom_swap_support
    (F B : Type)
    [Fintype F] [DecidableEq F]
    [Fintype B] [DecidableEq B]
    (hFcard : Fintype.card F = 6)
    (hBcard : Fintype.card B = 6)
    (α : Equiv.Perm F →* Equiv.Perm B)
    (hα : Function.Bijective α)
    (τ : Equiv.Perm F)
    (hτ : τ.IsSwap) :
    (α τ).support.card = 2 ∨
      (α τ).support.card = 6 := by
  let e : Equiv.Perm F ≃* Equiv.Perm B :=
    MulEquiv.ofBijective α hα
  simpa only [e, MulEquiv.ofBijective_apply] using
    perm_six_mulEquiv_swap_support
      F B hFcard hBcard e τ hτ

theorem exists_involution_lift_of_order_two
    (N F B : Type) [Group N] [Fintype N]
    [Fintype F] [DecidableEq F]
    [Fintype B] [DecidableEq B]
    (ρ : N →* Equiv.Perm F)
    (ψ : N →* Equiv.Perm B)
    (hker : ρ.ker ≤ ψ.ker)
    (hKerCard : Nat.card ρ.ker = 6)
    (r t : N)
    (hrKer : ρ r = 1)
    (htKer : ρ t = 1)
    (hrOrder : orderOf r = 3)
    (hinverts : MulAut.conj t r = r⁻¹)
    (α : Equiv.Perm F →* Equiv.Perm B)
    (hcomp : α.comp ρ = ψ)
    (τ : Equiv.Perm F)
    (hτOrder : orderOf τ = 2)
    (n : N)
    (hnρ : ρ n = τ)
    (hnConj :
      MulAut.conj n r = r ∨
        MulAut.conj n r = r⁻¹) :
    ∃ q : N,
      orderOf q = 2 ∧
        Commute q r ∧
        ρ q = τ ∧
        ψ q = α τ := by
  classical
  have hτSq : τ ^ 2 = 1 := by
    rw [← hτOrder]
    exact pow_orderOf_eq_one τ
  have hτNe : τ ≠ 1 := by
    intro hτOne
    rw [hτOne, orderOf_one] at hτOrder
    norm_num at hτOrder
  have hψt : ψ t = 1 := by
    apply MonoidHom.mem_ker.mp
    apply hker
    exact MonoidHom.mem_ker.mpr htKer
  have hψn : ψ n = α τ := by
    calc
      ψ n = (α.comp ρ) n := by rw [hcomp]
      _ = α (ρ n) := rfl
      _ = α τ := by rw [hnρ]
  obtain ⟨c, hcComm, hρc, hψc⟩ :
      ∃ c : N,
        Commute c r ∧
          ρ c = τ ∧
          ψ c = α τ := by
    rcases hnConj with hnCentral | hnInv
    · refine ⟨n, ?_, hnρ, hψn⟩
      exact
        mul_inv_eq_iff_eq_mul.mp
          (by
            simpa only [MulAut.conj_apply] using
              hnCentral)
    · refine ⟨n * t, ?_, ?_, ?_⟩
      · apply mul_inv_eq_iff_eq_mul.mp
        calc
          (n * t) * r * (n * t)⁻¹ =
              n * (t * r * t⁻¹) * n⁻¹ := by
            group
          _ = n * r⁻¹ * n⁻¹ := by
            rw [show t * r * t⁻¹ = r⁻¹ by
              simpa only [MulAut.conj_apply] using
                hinverts]
          _ = (n * r * n⁻¹)⁻¹ := by
            group
          _ = (r⁻¹)⁻¹ := by
            rw [show n * r * n⁻¹ = r⁻¹ by
              simpa only [MulAut.conj_apply] using
                hnInv]
          _ = r := inv_inv r
      · rw [map_mul, hnρ, htKer, mul_one]
      · rw [map_mul, hψn, hψt, mul_one]
  have hcSqKer : ρ (c ^ 2) = 1 := by
    rw [map_pow, hρc, hτSq]
  let rK : ρ.ker := ⟨r, hrKer⟩
  let tK : ρ.ker := ⟨t, htKer⟩
  let kK : ρ.ker := ⟨c ^ 2, hcSqKer⟩
  have hrKOrder : orderOf rK = 3 := by
    calc
      orderOf rK = orderOf (rK : N) :=
        (Subgroup.orderOf_coe _).symm
      _ = orderOf r := by rfl
      _ = 3 := hrOrder
  have hinvertsK :
      MulAut.conj tK rK = rK⁻¹ := by
    apply Subtype.ext
    exact hinverts
  have hcommK : Commute kK rK := by
    apply Subtype.ext
    exact hcComm.pow_left 2
  have hkMem :
      kK ∈ Subgroup.zpowers rK :=
    mem_zpowers_of_card_six_of_inverts_order_three
      ρ.ker hKerCard rK tK kK hrKOrder
        hinvertsK hcommK
  let RK : Subgroup ρ.ker :=
    Subgroup.zpowers rK
  let kR : RK := ⟨kK, hkMem⟩
  have hRKcard : Nat.card RK = 3 := by
    rw [Nat.card_zpowers, hrKOrder]
  have hkRCube : kR ^ 3 = 1 := by
    have hpow := pow_card_eq_one' (x := kR)
    rw [hRKcard] at hpow
    exact hpow
  have hcSqCube : (c ^ 2) ^ 3 = 1 := by
    have hkKCube :
        (kK : ρ.ker) ^ 3 = 1 :=
      congrArg Subtype.val hkRCube
    exact congrArg Subtype.val hkKCube
  let q : N := c ^ 3
  have hqSq : q ^ 2 = 1 := by
    change (c ^ 3) ^ 2 = 1
    calc
      (c ^ 3) ^ 2 = c ^ (3 * 2) :=
        (pow_mul c 3 2).symm
      _ = c ^ (2 * 3) := by norm_num
      _ = (c ^ 2) ^ 3 :=
        pow_mul c 2 3
      _ = 1 := hcSqCube
  have hρq : ρ q = τ := by
    change ρ (c ^ 3) = τ
    rw [map_pow, hρc]
    calc
      τ ^ 3 = τ ^ 2 * τ := pow_succ τ 2
      _ = τ := by rw [hτSq, one_mul]
  have hψq : ψ q = α τ := by
    have hατSq : (α τ) ^ 2 = 1 := by
      rw [← map_pow, hτSq, map_one]
    change ψ (c ^ 3) = α τ
    rw [map_pow, hψc]
    calc
      (α τ) ^ 3 =
          (α τ) ^ 2 * α τ :=
        pow_succ (α τ) 2
      _ = α τ := by rw [hατSq, one_mul]
  have hqNe : q ≠ 1 := by
    intro hqOne
    have := congrArg ρ hqOne
    rw [hρq, map_one] at this
    exact hτNe this
  refine ⟨q, orderOf_eq_prime hqSq hqNe,
    ?_, hρq, hψq⟩
  exact hcComm.pow_left 3

end FiveTransitive.Degree24

end CFSG
