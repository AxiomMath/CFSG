module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.Basic
public import Mathlib.GroupTheory.SpecificGroups.ZGroup

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3
open PFchapter3section1
open PFchapter3section3
open PFchapter4section1
open MulAction Subgroup
open scoped Pointwise

/-!
# Basic interfaces for Peterfalvi, Part II, Chapter IV, Section 2
-/



/-- In characteristic two, a nonzero root of `X^2 + alpha X + 1` satisfies
`alpha = beta + beta⁻¹`. -/
public theorem alpha_eq_beta_add_inv_of_characteristic_root
    {E : Type*} [Field E] [CharP E 2] {alpha beta : E}
    (hbeta : beta ≠ 0)
    (hroot : beta ^ 2 + alpha * beta + 1 = 0) :
    alpha = beta + beta⁻¹ := by
  have hsum : beta ^ 2 + alpha * beta = 1 := by
    exact CharTwo.add_eq_zero.mp (by simpa [add_assoc] using hroot)
  have hmul : alpha * beta = beta ^ 2 + 1 := by
    rw [← hsum]
    rw [CharTwo.add_cancel_left]
  calc
    alpha = (alpha * beta) * beta⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hbeta, mul_one]
    _ = (beta ^ 2 + 1) * beta⁻¹ := by rw [hmul]
    _ = beta + beta⁻¹ := by
      field_simp [hbeta]

/-- In characteristic two, `a |-> a * theta a` is bijective when the field
automorphism `theta` has odd order.  This is the norm permutation whose
inverse is denoted by `tau` in Chapter IV, Section 2. -/
public theorem norm_bijective_of_odd_order
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (theta : F ≃+* F) (hthetaOdd : Odd (orderOf theta)) :
    Function.Bijective (fun x : F => x * theta x) := by
  have hkernel : ∀ z : Fˣ, (z : F) * theta (z : F) = 1 → z = 1 := by
    intro z hz
    have htheta_z : theta (z : F) = (z : F)⁻¹ := by
      calc
        theta (z : F) = (z : F)⁻¹ * ((z : F) * theta (z : F)) := by simp
        _ = (z : F)⁻¹ := by rw [hz, mul_one]
    have htheta_sq_z : (theta ^ 2) (z : F) = (z : F) := by
      simp [pow_two, htheta_z]
    have htheta_even_z : ∀ k : ℕ, (theta ^ (2 * k)) (z : F) = (z : F) := by
      intro k
      rw [pow_mul]
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, RingAut.mul_apply, htheta_sq_z, ih]
    rcases hthetaOdd with ⟨k, hk⟩
    have hz_inv : (z : F) = (z : F)⁻¹ := by
      calc
        (z : F) = (theta ^ orderOf theta) (z : F) := by
          simp
        _ = (theta ^ (2 * k + 1)) (z : F) := by rw [hk]
        _ = theta ((theta ^ (2 * k)) (z : F)) := by
          rw [pow_succ', RingAut.mul_apply]
        _ = theta (z : F) := by rw [htheta_even_z]
        _ = (z : F)⁻¹ := htheta_z
    apply Units.ext
    have hz_sq : (z : F) ^ 2 = 1 := by
      calc
        (z : F) ^ 2 = (z : F) * (z : F) := pow_two _
        _ = (z : F) * (z : F)⁻¹ := congrArg ((z : F) * ·) hz_inv
        _ = 1 := mul_inv_cancel₀ (Units.ne_zero z)
    have hz_add : (z : F) + 1 = 0 := by
      have hfactor : ((z : F) + 1) ^ 2 = 0 := by
        rw [CharTwo.add_sq, hz_sq, one_pow, CharTwo.add_self_eq_zero]
      exact eq_zero_of_pow_eq_zero hfactor
    have hz_neg : (z : F) = -1 := eq_neg_of_add_eq_zero_left hz_add
    change (z : F) = (1 : F)
    simpa only [CharTwo.neg_eq] using hz_neg
  have hinj : Function.Injective (fun x : F => x * theta x) := by
    intro x y hxy
    by_cases hx : x = 0
    · subst x
      simp only [map_zero, zero_mul] at hxy
      rcases mul_eq_zero.mp hxy.symm with hy | hty
      · exact hy.symm
      · exact (theta.injective (by simpa using hty)).symm
    · have hy : y ≠ 0 := by
        intro hy
        subst y
        simp only [map_zero, mul_zero] at hxy
        rcases mul_eq_zero.mp hxy with hx0 | htx
        · exact hx hx0
        · exact hx (theta.injective (by simpa using htx))
      let xu : Fˣ := Units.mk0 x hx
      let yu : Fˣ := Units.mk0 y hy
      let z : Fˣ := xu * yu⁻¹
      have hz : (z : F) * theta (z : F) = 1 := by
        change (x * y⁻¹) * theta (x * y⁻¹) = 1
        rw [map_mul]
        have hmap_inv : theta y⁻¹ = (theta y)⁻¹ := map_inv₀ theta y
        rw [hmap_inv]
        change x * theta x = y * theta y at hxy
        calc
          (x * y⁻¹) * (theta x * (theta y)⁻¹) =
              (x * theta x) * (y * theta y)⁻¹ := by ring
          _ = (y * theta y) * (y * theta y)⁻¹ := by rw [hxy]
          _ = 1 := mul_inv_cancel₀
            (mul_ne_zero hy ((map_ne_zero theta).2 hy))
      have hz_one := hkernel z hz
      have hunit : xu = yu := mul_inv_eq_one.mp hz_one
      exact congrArg Units.val hunit
  exact hinj.bijective_of_nat_card_le le_rfl

/-- In the type-B coordinates, the square of every element of `S` is an
involution (or the identity), hence belongs to the source subgroup `Q0`. -/
public theorem IsSuzukiTwoTypeB.square_mem_Q0
    {G : Type*} [Group G] (H Q Q0 S : Subgroup G)
    (hB : IsSuzukiTwoTypeB S) (hS_le_Q : S ≤ Q) (hQ_le_H : Q ≤ H)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) :
    ∀ x : G, x ∈ S → x ^ 2 ∈ Q0 := by
  rcases hB with ⟨n, hn, theta, epsilon, tripleLift, cocycle, hepsilon,
    hperiod, hnonzero, haddLeft, haddRight, hdiag, hmem, hone,
    hsurj, hinj, hmul⟩
  intro x hxS
  rcases hsurj x hxS with ⟨c, a, b, rfl⟩
  have hsquare :
      tripleLift c a b ^ 2 = tripleLift (cocycle a b a b) 0 0 := by
    rw [pow_two, hmul]
    simp only [CharTwo.add_self_eq_zero, zero_add]
  rw [hsquare]
  by_cases hsq_one : tripleLift (cocycle a b a b) 0 0 = 1
  · rw [hsq_one]
    exact Q0.one_mem
  · apply (hQ0_def _).2
    refine Or.inr ⟨hQ_le_H (hS_le_Q (hmem _ _ _)), hsq_one, ?_⟩
    have hcocycle_zero : cocycle 0 0 0 0 = 0 := by
      simpa using hdiag 0 0
    calc
      tripleLift (cocycle a b a b) 0 0 ^ 2 =
          tripleLift 0 0 0 := by
        rw [pow_two, hmul, hcocycle_zero]
        simp only [CharTwo.add_self_eq_zero]
      _ = 1 := hone

/-- A type-B Suzuki `2`-group has a noncentral coordinate, so its image in
`Q / Q0` is nontrivial. -/
public theorem IsSuzukiTwoTypeB.exists_mem_Q_not_mem_Q0
    {G : Type*} [Group G] (H Q Q0 S : Subgroup G)
    (hB : IsSuzukiTwoTypeB S) (hS_le_Q : S ≤ Q)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) :
    ∃ x : G, x ∈ Q ∧ x ∉ Q0 := by
  rcases hB with ⟨n, hn, theta, epsilon, tripleLift, cocycle, hepsilon,
    hperiod, hnonzero, haddLeft, haddRight, hdiag, hmem, hone,
    hsurj, hinj, hmul⟩
  let x := tripleLift 0 1 0
  have hxS : x ∈ S := hmem 0 1 0
  have hx_ne_one : x ≠ 1 := by
    rw [← hone]
    intro hx
    exact one_ne_zero (hinj 0 1 0 0 0 0 hx).2.1
  have hcocycle_one : cocycle 1 0 1 0 = 1 := by
    simpa using hdiag 1 0
  have hx_sq : x ^ 2 = tripleLift 1 0 0 := by
    dsimp [x]
    rw [pow_two, hmul, hcocycle_one]
    simp only [CharTwo.add_self_eq_zero, zero_add]
  have hx_sq_ne_one : x ^ 2 ≠ 1 := by
    rw [hx_sq, ← hone]
    intro hx
    exact one_ne_zero (hinj 1 0 0 0 0 0 hx).1
  refine ⟨x, hS_le_Q hxS, ?_⟩
  intro hxQ0
  rcases (hQ0_def x).1 hxQ0 with hx_one | hx_involution
  · exact hx_ne_one hx_one
  · exact hx_sq_ne_one hx_involution.2.sq_eq_one

/-- In a finite Z-group, every element annihilated by the order of a normal
subgroup belongs to that subgroup.  This is the Sylow-component argument used
after Claim (18): normality puts a full Sylow component of `N` into the cyclic
Sylow subgroup containing the corresponding component of `x`. -/
public theorem mem_normal_of_pow_card_eq_one_of_isZGroup
    {A : Type*} [Group A] [Finite A] [IsZGroup A]
    (N : Subgroup A) [N.Normal] {x : A}
    (hx : x ^ Nat.card N = 1) : x ∈ N := by
  classical
  let C : Subgroup A := Subgroup.zpowers x
  have hCcard : Nat.card C = orderOf x := Nat.card_zpowers x
  have hC_dvd_N : Nat.card C ∣ Nat.card N := by
    rw [hCcard]
    exact orderOf_dvd_of_pow_eq_one hx
  have hC_le_N : C ≤ N := by
    have hcard_dvd : Nat.card C ∣ Nat.card (C ⊓ N : Subgroup A) := by
      rw [Nat.dvd_iff_prime_pow_dvd_dvd]
      intro p k hp hpkC
      letI : Fact p.Prime := ⟨hp⟩
      let S : Sylow p C := default
      let R : Sylow p N := default
      obtain ⟨PC, hPC⟩ := S.exists_comap_subtype_eq
      obtain ⟨PN, hPN⟩ := R.exists_comap_subtype_eq
      have hSA_le_PC : (S : Subgroup C).map C.subtype ≤ (PC : Subgroup A) := by
        intro a ha
        rcases ha with ⟨c, hcS, rfl⟩
        change (c : A) ∈ PC
        change c ∈ PC.comap C.subtype
        rw [hPC]
        exact hcS
      have hRA_le_PN : (R : Subgroup N).map N.subtype ≤ (PN : Subgroup A) := by
        intro a ha
        rcases ha with ⟨n, hnR, rfl⟩
        change (n : A) ∈ PN
        change n ∈ PN.comap N.subtype
        rw [hPN]
        exact hnR
      obtain ⟨a, ha⟩ := exists_smul_eq A PN PC
      have haSub : (MulAut.conj a) • (PN : Subgroup A) = (PC : Subgroup A) := by
        simpa only [Sylow.coe_subgroup_smul] using congrArg Sylow.toSubgroup ha
      let RA : Subgroup A := (R : Subgroup N).map N.subtype
      let RA' : Subgroup A := (MulAut.conj a) • RA
      have hRA'_le_PC : RA' ≤ (PC : Subgroup A) := by
        change (MulAut.conj a) • RA ≤ (PC : Subgroup A)
        rw [← haSub, Subgroup.pointwise_smul_def,
          Subgroup.pointwise_smul_def]
        exact Subgroup.map_mono hRA_le_PN
      have hRA'_le_N : RA' ≤ N := by
        intro y hy
        change y ∈ (MulAut.conj a) • RA at hy
        rw [Subgroup.pointwise_smul_def] at hy
        rcases hy with ⟨r, hr, rfl⟩
        rcases hr with ⟨r, _hrR, rfl⟩
        exact (inferInstance : N.Normal).conj_mem (r : A) r.property a
      let RinP : Subgroup PC := RA'.subgroupOf PC
      have hRinP_card : Nat.card RinP = Nat.card R := by
        calc
          Nat.card RinP = Nat.card RA' :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRA'_le_PC).toEquiv
          _ = Nat.card RA :=
            Nat.card_congr (Subgroup.equivSMul (MulAut.conj a) RA).symm.toEquiv
          _ = Nat.card R := Subgroup.card_map_of_injective N.subtype_injective
      have hRcard : Nat.card R = p ^ (Nat.card N).factorization p :=
        Sylow.card_eq_multiplicity R
      have hScard : Nat.card S = p ^ (Nat.card C).factorization p :=
        Sylow.card_eq_multiplicity S
      have hScard_dvd_Rcard : Nat.card S ∣ Nat.card R := by
        rw [hScard, hRcard]
        exact pow_dvd_pow p
          ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
            hC_dvd_N p)
      letI : Fintype PC := Fintype.ofFinite PC
      have hroot_card_le :
          {y : (PC : Subgroup A) | y ^ Nat.card R = 1}.ncard ≤ Nat.card R := by
        rw [Set.ncard_eq_toFinset_card']
        simpa [Nat.card_eq_fintype_card] using
          (IsCyclic.card_pow_eq_one_le (α := (PC : Subgroup A))
            (Nat.card_pos (α := R)))
      have hRinP_roots : (RinP : Set PC) ⊆ {y : PC | y ^ Nat.card R = 1} := by
        intro y hy
        let yr : RinP := ⟨y, hy⟩
        have hpow : yr ^ Nat.card RinP = 1 := pow_card_eq_one'
        change y ^ Nat.card R = 1
        rw [← hRinP_card]
        exact congrArg (fun z : RinP => (z : PC)) hpow
      have hroots_le_RinP : {y : PC | y ^ Nat.card R = 1} ⊆ (RinP : Set PC) := by
        have heq : (RinP : Set PC) = {y : PC | y ^ Nat.card R = 1} := by
          apply Set.eq_of_subset_of_ncard_le hRinP_roots
          change {y : PC | y ^ Nat.card R = 1}.ncard ≤ Nat.card RinP
          rw [hRinP_card]
          exact hroot_card_le
        simp [heq]
      have hSA_le_RA' : (S : Subgroup C).map C.subtype ≤ RA' := by
        intro y hy
        have hyPC : y ∈ PC := hSA_le_PC hy
        let yPC : PC := ⟨y, hyPC⟩
        have hyOrder : orderOf yPC ∣ Nat.card S := by
          have hySA : y ∈ (S : Subgroup C).map C.subtype := hy
          let ySA : (S : Subgroup C).map C.subtype := ⟨y, hySA⟩
          have hdvd := orderOf_dvd_natCard ySA
          have horder : orderOf yPC = orderOf ySA := by
            rw [← Subgroup.orderOf_coe yPC, ← Subgroup.orderOf_coe ySA]
          rw [horder]
          simpa only [Subgroup.card_map_of_injective C.subtype_injective] using hdvd
        have hyPow : yPC ^ Nat.card R = 1 :=
          (orderOf_dvd_iff_pow_eq_one).mp (hyOrder.trans hScard_dvd_Rcard)
        have hyRinP : yPC ∈ RinP := hroots_le_RinP hyPow
        exact hyRinP
      have hSA_le_inf :
          (S : Subgroup C).map C.subtype ≤ (C ⊓ N : Subgroup A) := by
        refine le_inf ?_ (hSA_le_RA'.trans hRA'_le_N)
        intro y hy
        rcases hy with ⟨c, _hcS, rfl⟩
        exact c.property
      have hpkS : p ^ k ∣ Nat.card S := by
        rw [hScard]
        exact pow_dvd_pow p
          ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hpkC)
      have hmapcard :
          Nat.card ((S : Subgroup C).map C.subtype) = Nat.card S :=
        Subgroup.card_map_of_injective C.subtype_injective
      rw [← hmapcard] at hpkS
      exact hpkS.trans (Subgroup.card_dvd_of_le hSA_le_inf)
    have hcard_eq : Nat.card (C ⊓ N : Subgroup A) = Nat.card C :=
      Nat.dvd_antisymm (Subgroup.card_dvd_of_le inf_le_left) hcard_dvd
    have hinf_eq : (C ⊓ N : Subgroup A) = C :=
      Subgroup.eq_of_le_of_card_ge inf_le_left hcard_eq.ge
    rw [← hinf_eq]
    exact inf_le_right
  exact hC_le_N (Subgroup.mem_zpowers x)

end PFchapter4section2
end CFSG.BenderSuzuki
