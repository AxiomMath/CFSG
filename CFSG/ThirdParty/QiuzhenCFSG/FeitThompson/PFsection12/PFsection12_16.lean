module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_12
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_14
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_15
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.RealVirtualParity
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1
import Mathlib.GroupTheory.Schreier
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 12: Theorem (12.16)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v

/-! ## (12.16) -/

/-- PF `(1.10.a)` with the ambient primitive root replaced by one whose order
is any common multiple of the orders of the elements under consideration. -/
private theorem theorem_12_16_virtualCharacter_congruent_at_mul_of_order_dvd
    {K0 : Type*} [Group K0] [Finite K0]
    {p M0 : ℕ} {etaRoot eps : ℂ}
    (heps : IsPrimitiveRoot eps p) (hp : p ≠ 0)
    (hetaRoot : IsPrimitiveRoot etaRoot M0) (hM0 : M0 ≠ 0)
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    {chi : K0 → ℂ} (hchi : Theory.Character.IsVirtualCharacter chi)
    {x y : K0}
    (hx_order : orderOf x = p)
    (hy_order_dvd : orderOf y ∣ M0)
    (hcomm : x * y = y * x) :
    ∃ hxy : chi (x * y) ∈ Theory.Character.cyclotomicOrder etaRoot,
      ∃ hy : chi y ∈ Theory.Character.cyclotomicOrder etaRoot,
        Theory.Character.CongruentModOneSub etaRoot eps (chi (x * y)) (chi y)
          hepsMem hxy hy := by
  classical
  rcases hchi with ⟨r, m, n, rho, hchieq⟩
  let A := Theory.Character.cyclotomicOrder etaRoot
  have hrep : ∀ i : Fin r,
      ∃ hxy : (rho i).character (x * y) ∈ A,
        ∃ hy : (rho i).character y ∈ A,
          Theory.Character.CongruentModOneSub etaRoot eps
            ((rho i).character (x * y)) ((rho i).character y) hepsMem hxy hy := by
    intro i
    let N := orderOf y
    have hN : N ≠ 0 := Nat.ne_of_gt (orderOf_pos y)
    have hNM : N ∣ M0 := by
      simpa [N] using hy_order_dvd
    have hxpow : x ^ p = 1 := by
      rw [← hx_order]
      exact pow_orderOf_eq_one x
    have hf : (rho i x) ^ p = 1 := by
      rw [← MonoidHom.map_pow, hxpow, MonoidHom.map_one]
    have hTpow : (rho i y) ^ N = 1 := by
      subst N
      rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
    have hcommEnd : rho i x * rho i y = rho i y * rho i x := by
      calc
        rho i x * rho i y = rho i (x * y) := (map_mul (rho i) x y).symm
        _ = rho i (y * x) := by rw [hcomm]
        _ = rho i y * rho i x := map_mul (rho i) y x
    rcases Theory.Character.finite_order_commuting_trace_mul_congruent
        (η := etaRoot) (ξ := eps) (p := p) (N := N) (M := M0)
        heps hp hetaRoot hM0 hNM hepsMem (f := rho i x) (T := rho i y)
        hN hf hTpow hcommEnd with
      ⟨hmul, hy, hcong⟩
    have hxy : (rho i).character (x * y) ∈ A := by
      simpa [Representation.character, map_mul] using hmul
    refine ⟨hxy, hy, ?_⟩
    simpa [Theory.Character.CongruentModOneSub, Representation.character, map_mul] using hcong
  choose hxyi hyi hcongi using hrep
  have hxy_mem : chi (x * y) ∈ A := by
    rw [hchieq]
    exact A.sum_mem fun i _ =>
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hxyi i)
  have hy_mem : chi y ∈ A := by
    rw [hchieq]
    exact A.sum_mem fun i _ =>
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hyi i)
  refine ⟨hxy_mem, hy_mem, ?_⟩
  let oneSub : A := ⟨1 - eps, A.sub_mem A.one_mem hepsMem⟩
  change Theory.Character.congruentModIn A oneSub
    (⟨chi (x * y), hxy_mem⟩ : A)
    (⟨chi y, hy_mem⟩ : A)
  let zterm : Fin r → A := fun i =>
    ⟨(m i : ℂ) * (rho i).character (x * y),
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hxyi i)⟩
  let wterm : Fin r → A := fun i =>
    ⟨(m i : ℂ) * (rho i).character y,
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hyi i)⟩
  unfold Theory.Character.congruentModIn
  have hdiff :
      (⟨chi (x * y), hxy_mem⟩ : A) - ⟨chi y, hy_mem⟩ =
        ∑ i : Fin r, (zterm i - wterm i) := by
    ext
    change chi (x * y) - chi y = ((∑ i : Fin r, (zterm i - wterm i) : A) : ℂ)
    rw [hchieq]
    simp [Theory.Character.virtualCharacterOfRepresentations, zterm, wterm,
      Finset.sum_sub_distrib]
  rw [hdiff]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hci : Theory.Character.congruentModIn A oneSub
      (⟨(rho i).character (x * y), hxyi i⟩ : A)
      (⟨(rho i).character y, hyi i⟩ : A) := by
    simpa [Theory.Character.CongruentModOneSub, oneSub] using hcongi i
  change Theory.Character.congruentModIn A oneSub (zterm i) (wterm i)
  have hmul := Theory.Character.congruentModIn_mul_left hci
    (⟨(m i : ℂ), Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)⟩ : A)
  simpa [zterm, wterm] using hmul

private theorem theorem_12_16_double_complement_card_le
    {p e : ℕ} (hp : Nat.Prime p) (hoddp : Odd p) (hodde : Odd e)
    (hdiv : e ∣ p - 1 ∨ e ∣ p + 1) :
    2 * e ≤ p + 1 := by
  rcases hoddp with ⟨kp, hkp⟩
  rcases hodde with ⟨ke, hke⟩
  rcases hdiv with hdiv | hdiv
  · rcases hdiv with ⟨c, hc⟩
    have hp2 : 2 ≤ p := hp.two_le
    have hc2 : 2 ≤ c := by
      rcases c with _ | _ | c
      · simp at hc
        omega
      · simp at hc
        omega
      · omega
    have hpc : p = e * c + 1 := by omega
    nlinarith
  · rcases hdiv with ⟨c, hc⟩
    have hp2 : 2 ≤ p := hp.two_le
    have hc2 : 2 ≤ c := by
      rcases c with _ | _ | c
      · simp at hc
      · simp at hc
        omega
      · omega
    nlinarith

private theorem theorem_12_16_abs_int_ge
    {p e : ℕ} {z a : ℤ}
    (hepos : 0 < e) (hpe : 2 * e ≤ p + 1)
    (hz : z - (e : ℤ) = (p : ℤ) * a) :
    (e : ℝ) - 1 ≤ |(z : ℝ)| := by
  by_cases ha : a = 0
  · subst a
    have hz' : z = (e : ℤ) := by omega
    rw [hz']
    simp
  · have haabsZ : (1 : ℤ) ≤ |a| := by
      have := abs_pos.mpr ha
      omega
    have haabs : (1 : ℝ) ≤ |(a : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast haabsZ
    have hzreal : (z : ℝ) = (e : ℝ) + (p : ℝ) * (a : ℝ) := by
      exact_mod_cast (show z = (e : ℤ) + (p : ℤ) * a by omega)
    rw [hzreal]
    have htri : |(p : ℝ) * (a : ℝ)| - |(e : ℝ)| ≤
        |(e : ℝ) + (p : ℝ) * (a : ℝ)| := by
      simpa [abs_neg, add_comm] using
        (abs_sub_abs_le_abs_sub ((p : ℝ) * (a : ℝ)) (-(e : ℝ)))
    have hpnonneg : (0 : ℝ) ≤ p := by positivity
    have henonneg : (0 : ℝ) ≤ e := by positivity
    rw [abs_mul, abs_of_nonneg hpnonneg, abs_of_nonneg henonneg] at htri
    have hpa : (p : ℝ) ≤ (p : ℝ) * |(a : ℝ)| := by nlinarith
    have hpe' : (2 : ℝ) * e ≤ p + 1 := by exact_mod_cast hpe
    nlinarith

private theorem theorem_12_16_congruentModIn_symm
    {A : Subring ℂ} {a z w : A}
    (h : Theory.Character.congruentModIn A a z w) :
    Theory.Character.congruentModIn A a w z := by
  change w - z ∈ Ideal.span ({a} : Set A)
  convert neg_mem h using 1
  ring

private theorem theorem_12_16_congruentModIn_trans
    {A : Subring ℂ} {a z w v : A}
    (hzw : Theory.Character.congruentModIn A a z w)
    (hwv : Theory.Character.congruentModIn A a w v) :
    Theory.Character.congruentModIn A a z v := by
  change z - v ∈ Ideal.span ({a} : Set A)
  convert Ideal.add_mem _ hzw hwv using 1
  ring

private theorem theorem_12_16_primitive_root_package
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p) (hpdvd : p ∣ Nat.card G) :
    ∃ etaRoot eps : ℂ,
      IsPrimitiveRoot etaRoot (Nat.card G) ∧
        IsPrimitiveRoot eps p ∧
        eps ∈ Theory.Character.cyclotomicOrder etaRoot := by
  let etaRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card G))
  let eps : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hGne : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
  have hetaRoot : IsPrimitiveRoot etaRoot (Nat.card G) := by
    dsimp [etaRoot]
    exact Complex.isPrimitiveRoot_exp (Nat.card G) hGne
  have heps : IsPrimitiveRoot eps p := by
    dsimp [eps]
    exact Complex.isPrimitiveRoot_exp p hp.ne_zero
  refine ⟨etaRoot, eps, hetaRoot, heps, ?_⟩
  exact Theory.Character.primitive_root_mem_cyclotomicOrder_of_dvd
    hetaRoot hGne heps hpdvd


private theorem theorem_12_16_value_abs_ge
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {p e : ℕ} {x g : G}
    {chi : Section1.ClassFunction L}
    {psi : Section1.ClassFunction G}
    (hp : Nat.Prime p) (hoddp : Odd p) (hodde : Odd e)
    (hchiVirt : Theory.Character.IsVirtualCharacter chi)
    (hpsiVirt : Theory.Character.IsVirtualCharacter psi)
    (hxL : x ∈ L) (hxorder : orderOf x = p)
    (hcomm : x * g = g * x)
    (hvalue : psi (x * g) = chi ⟨x, hxL⟩)
    (hdegree : Section1.degree chi = (e : ℂ))
    (hzg : psi g ∈ Set.range (fun z : ℤ => (z : ℂ)))
    (hdiv : e ∣ p - 1 ∨ e ∣ p + 1) :
    (e : ℝ) - 1 ≤ ‖psi g‖ := by
  classical
  have hpdvd : p ∣ Nat.card G := by
    rw [← hxorder]
    exact orderOf_dvd_natCard x
  rcases theorem_12_16_primitive_root_package hp hpdvd with
    ⟨etaRoot, eps, hetaRoot, heps, hepsMem⟩
  let A := Theory.Character.cyclotomicOrder etaRoot
  let oneSub : A := ⟨1 - eps, A.sub_mem A.one_mem hepsMem⟩
  rcases theorem_12_16_virtualCharacter_congruent_at_mul_of_order_dvd
      (K0 := G) (p := p) (M0 := Nat.card G)
      (etaRoot := etaRoot) (eps := eps)
      heps hp.ne_zero hetaRoot (Nat.card_pos (α := G)).ne' hepsMem
      hpsiVirt hxorder (orderOf_dvd_natCard g) hcomm with
    ⟨hpsiMulMem, hpsiGMem, hpsiCong⟩
  let xL : L := ⟨x, hxL⟩
  have hxLorder : orderOf xL = p := by
    simpa [xL, Subgroup.orderOf_coe] using hxorder
  rcases theorem_12_16_virtualCharacter_congruent_at_mul_of_order_dvd
      (K0 := L) (p := p) (M0 := Nat.card G)
      (etaRoot := etaRoot) (eps := eps)
      (x := xL) (y := (1 : L))
      heps hp.ne_zero hetaRoot (Nat.card_pos (α := G)).ne' hepsMem
      hchiVirt hxLorder (by simp) (by simp) with
    ⟨hchiMulMem, hchiOneMem, hchiCongRaw⟩
  have hchiXMem : chi xL ∈ A := by
    simpa using hchiMulMem
  have hchiCong :
      Theory.Character.CongruentModOneSub etaRoot eps (chi xL) (chi 1)
        hepsMem hchiXMem hchiOneMem := by
    simpa [Theory.Character.CongruentModOneSub] using hchiCongRaw
  have hpsiCongA : Theory.Character.congruentModIn A oneSub
      (⟨psi (x * g), hpsiMulMem⟩ : A) ⟨psi g, hpsiGMem⟩ := by
    simpa [Theory.Character.CongruentModOneSub, A, oneSub] using hpsiCong
  have hchiCongA : Theory.Character.congruentModIn A oneSub
      (⟨chi xL, hchiXMem⟩ : A) ⟨chi 1, hchiOneMem⟩ := by
    simpa [Theory.Character.CongruentModOneSub, A, oneSub] using hchiCong
  have hpsiSymm := theorem_12_16_congruentModIn_symm hpsiCongA
  have hmulEq :
      (⟨psi (x * g), hpsiMulMem⟩ : A) = ⟨chi xL, hchiXMem⟩ := by
    apply Subtype.ext
    simpa [xL] using hvalue
  rw [hmulEq] at hpsiSymm
  have hpsiGChiOne : Theory.Character.congruentModIn A oneSub
      (⟨psi g, hpsiGMem⟩ : A) ⟨chi 1, hchiOneMem⟩ :=
    theorem_12_16_congruentModIn_trans hpsiSymm hchiCongA
  rcases hzg with ⟨z, hz⟩
  have hchiOne : chi 1 = (e : ℂ) := by
    simpa [Section1.degree] using hdegree
  let zA : A :=
    ⟨(z : ℂ), Theory.Character.intCast_mem_cyclotomicOrder etaRoot z⟩
  have heMem : (e : ℂ) ∈ A := by
    simp
  let eA : A := ⟨(e : ℂ), heMem⟩
  have hpsiGEq : (⟨psi g, hpsiGMem⟩ : A) = zA := by
    apply Subtype.ext
    exact hz.symm
  have hchiOneEq : (⟨chi 1, hchiOneMem⟩ : A) = eA := by
    apply Subtype.ext
    exact hchiOne
  rw [hpsiGEq, hchiOneEq] at hpsiGChiOne
  have hdiffCong : Theory.Character.congruentModIn A oneSub
      (zA - eA) (eA - eA) :=
    Theory.Character.congruentModIn_sub hpsiGChiOne
      (Theory.Character.congruentModIn_refl A oneSub eA)
  have hcongInt :
      Theory.Character.CongruentModOneSub etaRoot eps
        (((z - (e : ℤ) : ℤ) : ℂ)) 0 hepsMem
        (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (z - (e : ℤ)))
        A.zero_mem := by
    unfold Theory.Character.CongruentModOneSub
    convert hdiffCong
    · simp [A, zA, eA]
    · simp [A, eA]
  have hpdiff : (p : ℤ) ∣ z - (e : ℤ) :=
    Theory.Character.prime_dvd_int_of_congruent_zero_mod_one_sub hp heps
      (hetaRoot.isIntegral (Nat.card_pos (α := G))) hepsMem
      (z - (e : ℤ)) hcongInt
  rcases hpdiff with ⟨a, ha⟩
  have hpe : 2 * e ≤ p + 1 :=
    theorem_12_16_double_complement_card_le hp hoddp hodde hdiv
  have hepos : 0 < e := by
    rcases hodde with ⟨k, hk⟩
    omega
  have hzabs : (e : ℝ) - 1 ≤ |(z : ℝ)| :=
    theorem_12_16_abs_int_ge hepos hpe ha
  rw [← hz]
  norm_num at hzabs ⊢
  exact hzabs

private theorem theorem_12_16_subgroup_difference_card
    {G : Type*} [Group G] [Finite G]
    {M K K' : Subgroup G}
    (hKM : K ≤ M) (hK'K : K' ≤ K) :
    Nat.card {m : M // (m : G) ∈ K ∧ (m : G) ∉ K'} =
        Nat.card K - Nat.card K' := by
  classical
  let eKM :
      {m : M // (m : G) ∈ K ∧ (m : G) ∉ K'} ≃
        {k : K // (k : G) ∉ K'} :=
    { toFun := fun m => ⟨⟨(m : G), m.2.1⟩, m.2.2⟩
      invFun := fun k => ⟨⟨(k : G), hKM k.1.2⟩, k.1.2, k.2⟩
      left_inv := by intro m; ext; rfl
      right_inv := by intro k; ext; rfl }
  let eK' : {k : K // (k : G) ∈ K'} ≃ K' :=
    (Subgroup.subgroupOfEquivOfLe hK'K).toEquiv
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr eKM]
  rw [Fintype.card_subtype_compl (fun k : K => (k : G) ∈ K')]
  rw [Fintype.card_congr eK']
  simp [Nat.card_eq_fintype_card]


private theorem theorem_12_16_projection_energy_lower
    {G : Type u} [Group G] [Finite G]
    {M K K' : Subgroup G}
    {RM : G → Subgroup G}
    {psi : Section1.ClassFunction G}
    {psiRhoM : Section1.ClassFunction M}
    {e : ℕ}
    (hKM : K ≤ M) (hK'K : K' ≤ K)
    (hprojection : psiRhoM = Section7.dadeProjection M RM psi)
    (hagrees : ∀ g : M, (g : G) ∈ K → (g : G) ≠ 1 →
      psiRhoM g = psi (g : G))
    (hbound : ∀ g : G, g ∈ K → g ∉ K' →
      (e : ℝ) - 1 ≤ ‖psi g‖)
    (hepos : 0 < e) :
    ((Nat.card K - Nat.card K' : ℕ) : ℝ) / (Nat.card M : ℝ) *
        ((e : ℝ) - 1) ^ 2 ≤
      Section7.weightedProjectionEnergy (Section8.a1Set K) M RM psi := by
  classical
  letI : Fintype M := Fintype.ofFinite M
  let D : Finset M := Finset.univ.filter
    (fun m : M => (m : G) ∈ K ∧ (m : G) ∉ K')
  have hDcard : D.card = Nat.card K - Nat.card K' := by
    rw [← theorem_12_16_subgroup_difference_card hKM hK'K,
      Nat.card_eq_fintype_card]
    simpa [D] using
      (Fintype.card_subtype
        (fun m : M => (m : G) ∈ K ∧ (m : G) ∉ K')).symm
  have heone : 0 ≤ (e : ℝ) - 1 := by
    have heoneNat : 1 ≤ e := by omega
    have heoneReal : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast heoneNat
    linarith
  have hterm : ∀ m ∈ D,
      ((e : ℝ) - 1) ^ 2 ≤
        Complex.normSq
          (Section7.dadeProjectionOn (Section8.a1Set K) M RM psi m) := by
    intro m hmD
    have hm : (m : G) ∈ K ∧ (m : G) ∉ K' := by
      simpa [D] using hmD
    have hmne : (m : G) ≠ 1 := by
      intro hm1
      apply hm.2
      simp [hm1]
    have hmA1 : (m : G) ∈ Section8.a1Set K := by
      simp [Section8.a1Set, section16NonidentityElements, hm.1, hmne]
    have hvalue :
        Section7.dadeProjectionOn (Section8.a1Set K) M RM psi m =
          psi (m : G) := by
      rw [Section7.dadeProjectionOn, if_pos hmA1, ← hprojection]
      exact hagrees m hm.1 hmne
    rw [hvalue, Complex.normSq_eq_norm_sq]
    have hmBound := hbound (m : G) hm.1 hm.2
    nlinarith [sq_nonneg ((e : ℝ) - 1), sq_nonneg ‖psi (m : G)‖]
  have hrestricted :
      (D.card : ℝ) * ((e : ℝ) - 1) ^ 2 ≤
        ∑ m ∈ D,
          Complex.normSq
            (Section7.dadeProjectionOn (Section8.a1Set K) M RM psi m) := by
    calc
      (D.card : ℝ) * ((e : ℝ) - 1) ^ 2 =
          ∑ _m ∈ D, ((e : ℝ) - 1) ^ 2 := by simp
      _ ≤ ∑ m ∈ D,
          Complex.normSq
            (Section7.dadeProjectionOn (Section8.a1Set K) M RM psi m) := by
        exact Finset.sum_le_sum fun m hm => hterm m hm
  have hsum :
      (D.card : ℝ) * ((e : ℝ) - 1) ^ 2 ≤
        ∑ m : M,
          Complex.normSq
            (Section7.dadeProjectionOn (Section8.a1Set K) M RM psi m) := by
    apply hrestricted.trans
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro m hm; simp)
      (by intro m _hm _hmD; exact Complex.normSq_nonneg _)
  rw [Section7.weightedProjectionEnergy,
    Section5.cfNormSq_eq_inv_card_mul_sum_normSq, ← hDcard]
  calc
    (D.card : ℝ) / (Nat.card M : ℝ) * ((e : ℝ) - 1) ^ 2 =
        (Nat.card M : ℝ)⁻¹ *
          ((D.card : ℝ) * ((e : ℝ) - 1) ^ 2) := by ring
    _ ≤ (Nat.card M : ℝ)⁻¹ *
        ∑ m : M,
          Complex.normSq
            (Section7.dadeProjectionOn (Section8.a1Set K) M RM psi m) := by
      exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq rfl)


private theorem theorem_12_16_projection_energy_sum_lt_one
    {G : Type u} [Group G] [Finite G]
    {A B : Set G} {M L : Subgroup G}
    {RM RL : G → Subgroup G}
    {psi : Section1.ClassFunction G}
    (h22M : Section2.Hypothesis2 A M RM)
    (h22L : Section2.Hypothesis2 B L RL)
    (hdisjoint : Disjoint (Section2.dadeSupport A RM)
      (Section2.dadeSupport B RL))
    (hclass : Section1.IsClassFunction psi)
    (hsigned : Section3.IsSignedIrreducibleCharacter psi) :
    Section7.weightedProjectionEnergy A M RM psi +
        Section7.weightedProjectionEnergy B L RL psi < 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let X : Set G := Section2.dadeSupport A RM
  let Y : Set G := Section2.dadeSupport B RL
  have hnotX : (1 : G) ∉ X := by
    simpa [X] using one_not_mem_dadeSupport_of_hypothesis2 h22M
  have hnotY : (1 : G) ∉ Y := by
    simpa [Y] using one_not_mem_dadeSupport_of_hypothesis2 h22L
  have hdisXY : Disjoint X Y := by simpa [X, Y] using hdisjoint
  have hpointwise (g : G) :
      (if g ∈ X then Complex.normSq (psi g) else 0) +
          (if g ∈ Y then Complex.normSq (psi g) else 0) ≤
        Complex.normSq (psi g) := by
    by_cases hgX : g ∈ X
    · have hgY : g ∉ Y := fun hgY => (Set.disjoint_left.mp hdisXY hgX) hgY
      simp [hgX, hgY]
    · by_cases hgY : g ∈ Y
      · simp [hgX, hgY]
      · simp [hgX, hgY, Complex.normSq_nonneg]
  have hpsiOne : psi 1 ≠ 0 := by
    simpa [Section1.degree_apply] using degree_ne_zero_of_signedIrreducible hsigned
  have hstrictAtOne :
      (if (1 : G) ∈ X then Complex.normSq (psi 1) else 0) +
          (if (1 : G) ∈ Y then Complex.normSq (psi 1) else 0) <
        Complex.normSq (psi 1) := by
    simp [hnotX, hnotY, Complex.normSq_pos.mpr hpsiOne]
  have hsumStrict :
      (∑ g : G, (
        (if g ∈ X then Complex.normSq (psi g) else 0) +
          (if g ∈ Y then Complex.normSq (psi g) else 0))) <
        ∑ g : G, Complex.normSq (psi g) := by
    apply Finset.sum_lt_sum
    · intro g _hg
      exact hpointwise g
    · exact ⟨1, Finset.mem_univ _, hstrictAtOne⟩
  have hsupportStrict :
      Section7.supportEnergy X psi + Section7.supportEnergy Y psi <
        ∑ g : G, Complex.normSq (psi g) := by
    simpa [Section7.supportEnergy, Finset.sum_add_distrib] using hsumStrict
  have hinvPos : 0 < (Nat.card G : ℝ)⁻¹ := by
    exact inv_pos.mpr (by exact_mod_cast (Nat.card_pos (α := G)))
  have hnormalizedStrict :
      Section7.normalizedSupportEnergy X psi +
          Section7.normalizedSupportEnergy Y psi <
        Section5.cfNormSq psi := by
    rw [Section7.normalizedSupportEnergy, Section7.normalizedSupportEnergy,
      Section5.cfNormSq_eq_inv_card_mul_sum_normSq]
    calc
      (Nat.card G : ℝ)⁻¹ * Section7.supportEnergy X psi +
          (Nat.card G : ℝ)⁻¹ * Section7.supportEnergy Y psi =
        (Nat.card G : ℝ)⁻¹ *
          (Section7.supportEnergy X psi + Section7.supportEnergy Y psi) := by ring
      _ < (Nat.card G : ℝ)⁻¹ *
          ∑ g : G, Complex.normSq (psi g) :=
        mul_lt_mul_of_pos_left hsupportStrict hinvPos
  have h7M := (Section7.theorem_7_3 A M RM psi) h22M hclass
  have h7L := (Section7.theorem_7_3 B L RL psi) h22L hclass
  have hself : Section5.cfNormSq psi = 1 := by
    unfold Section5.cfNormSq
    rw [scalarProduct_self_of_isSignedIrreducibleCharacter hsigned]
    norm_num
  calc
    Section7.weightedProjectionEnergy A M RM psi +
        Section7.weightedProjectionEnergy B L RL psi ≤
      Section7.normalizedSupportEnergy X psi +
        Section7.normalizedSupportEnergy Y psi := by
      simpa [X, Y, Section7.dadeProjectionSupport] using add_le_add h7M.1 h7L.1
    _ < Section5.cfNormSq psi := hnormalizedStrict
    _ = 1 := hself


private theorem theorem_12_16_projection_energy_lower_frobenius
    {G : Type u} [Group G] [Finite G]
    {L H E : Subgroup G} {e : ℕ}
    {S : Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {tau tau1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {chi : Section1.ClassFunction L}
    {psi : Section1.ClassFunction G}
    {psiRho : Section1.ClassFunction L}
    (hodd : Odd (Nat.card G))
    (hfrob : Section7.frobeniusWithKernel L H)
    (h13 : notation_12_13_data L H E e S R tau tau1 chi psi psiRho) :
    1 - (e : ℝ) / (Nat.card H : ℝ) ≤
      Section7.weightedProjectionEnergy (typeIASet L H) L R psi := by
  classical
  rcases h13 with
    ⟨h12L, hcomp, he, _hchiS, _hdegree, h78pack, _hnotpack,
      _hExt, hpsi, _hpsiclass, _hrho⟩
  rcases h78pack with ⟨T, h76H, _hAgreeH, h78⟩
  rcases h12L with ⟨_hLmax, hHMF, _hTypeIL, _hSL, hDadeL⟩
  rcases hDadeL with ⟨h22R, hALR, hTauR⟩
  have hAgreeR :
      Section7.agreesWithDadeTransform (typeIASet L H) L R tau :=
    ⟨hALR, hTauR⟩
  have h76R : Section7.hypothesis_7_6_statement
      (typeIASet L H) L H R T := by
    rcases h76H with ⟨hHL, hHnormal, _h22H, hAeq, hT⟩
    exact ⟨hHL, hHnormal, h22R, hAeq, hT⟩
  have hrel : H.relIndex L = e := by
    have hHnormal : (H.subgroupOf L).Normal :=
      section16MFSubgroup_subgroupOf_normal hHMF
    have hlocal : (H.subgroupOf L).IsComplement' (E.subgroupOf L) :=
      section12ComplementIn_left_normal_isComplement' hcomp hHnormal
    rw [Subgroup.relIndex, hlocal.symm.index_eq_card,
      natCard_subgroupOf_eq E L hcomp.2.1, he]
  have htwo : 2 * H.relIndex L ≤ Nat.card H - 1 :=
    Section7.theorem_7_11_two_mul_relIndex_le_card_sub_one hodd hfrob
  have hhalf : H.relIndex L ≤ (Nat.card H - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    simpa [Nat.mul_comm] using htwo
  have h78b := Section7.theorem_7_8_b
    (typeIASet L H) L H R T S tau tau1 chi
    h76R hAgreeR h78
    (fun a r hdecomp =>
      Section7.theorem_7_8_b_projectionData_source_bridge
        h76R hAgreeR h78 hdecomp)
    hhalf
  simpa [Section7.weightedProjectionEnergy, hpsi, hrel] using h78b.1

private theorem theorem_12_16_quotient_card_lt_four_arithmetic
    {m k k' h e : ℕ} {energyM energyL : ℝ}
    (hmpos : 0 < m) (hkpos : 0 < k) (_hk'pos : 0 < k') (hhpos : 0 < h)
    (hk'le : k' ≤ k) (hegt : 2 < e) (hmle : m ≤ k * h)
    (hlowerM :
      ((k - k' : ℕ) : ℝ) / (m : ℝ) * ((e : ℝ) - 1) ^ 2 ≤ energyM)
    (hlowerL : 1 - (e : ℝ) / (h : ℝ) ≤ energyL)
    (hupper : energyM + energyL < 1) :
    k < 4 * k' := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hhR : (0 : ℝ) < h := by exact_mod_cast hhpos
  have hk'leR : (k' : ℝ) ≤ k := by exact_mod_cast hk'le
  have hmleR : (m : ℝ) ≤ (k : ℝ) * h := by exact_mod_cast hmle
  have heR : (2 : ℝ) < e := by exact_mod_cast hegt
  have henergy :
      (((k : ℝ) - k') / m) * ((e : ℝ) - 1) ^ 2 < (e : ℝ) / h := by
    rw [Nat.cast_sub hk'le] at hlowerM
    nlinarith
  have henergy' :
      (((k : ℝ) - k') * ((e : ℝ) - 1) ^ 2) / m < (e : ℝ) / h := by
    (convert henergy using 1; ring)
  rw [div_lt_div_iff₀ hmR hhR] at henergy'
  have heNonneg : (0 : ℝ) ≤ e := by
    have : 0 ≤ (e : ℝ) := by exact_mod_cast (Nat.zero_le e)
    exact this
  have hem : (e : ℝ) * m ≤ (e : ℝ) * ((k : ℝ) * h) :=
    mul_le_mul_of_nonneg_left hmleR heNonneg
  have hcancel :
      ((k : ℝ) - k') * ((e : ℝ) - 1) ^ 2 < (e : ℝ) * k := by
    nlinarith
  have hthree : (3 : ℝ) ≤ e := by
    have : 3 ≤ e := by omega
    exact_mod_cast this
  have hratioPoly :
      4 * (e : ℝ) ≤ 3 * ((e : ℝ) - 1) ^ 2 := by
    have hprod :
        0 ≤ (3 * (e : ℝ) - 1) * ((e : ℝ) - 3) :=
      mul_nonneg (by nlinarith) (by nlinarith)
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hcancel (by norm_num : (0 : ℝ) < 4)
  have hratioScaled :
      4 * (e : ℝ) * k ≤ 3 * ((e : ℝ) - 1) ^ 2 * k :=
    mul_le_mul_of_nonneg_right hratioPoly hkR.le
  have hcombined :
      4 * (((k : ℝ) - k') * ((e : ℝ) - 1) ^ 2) <
        3 * ((e : ℝ) - 1) ^ 2 * k :=
    hscaled.trans_le (by nlinarith [hratioScaled])
  have hspos : 0 < ((e : ℝ) - 1) ^ 2 := sq_pos_of_pos (by nlinarith)
  have hfactor :
      0 < ((e : ℝ) - 1) ^ 2 * (4 * (k' : ℝ) - k) := by
    nlinarith
  have hfinalR : (k : ℝ) < 4 * (k' : ℝ) := by
    rcases (mul_pos_iff.mp hfactor) with hpos | hneg
    · nlinarith [hpos.2]
    · exact False.elim (by nlinarith [hspos, hneg.1])
  exact_mod_cast hfinalR


private theorem theorem_12_16_quotient_card_lt_four
    {G : Type u} [Group G] [Finite G]
    {M K K' L H : Subgroup G} {e : ℕ}
    {energyM energyL : ℝ}
    (hKMF : section16MFSubgroup M K)
    (hK' : K' = ambientDerivedSubgroup K)
    (hcompM : section12ComplementIn M K (M ⊓ L))
    (hMLleH : M ⊓ L ≤ H)
    (hegt : 2 < e)
    (hlowerM :
      ((Nat.card K - Nat.card K' : ℕ) : ℝ) / (Nat.card M : ℝ) *
          ((e : ℝ) - 1) ^ 2 ≤ energyM)
    (hlowerL : 1 - (e : ℝ) / (Nat.card H : ℝ) ≤ energyL)
    (hupper : energyM + energyL < 1) :
    Nat.card (K ⧸ K'.subgroupOf K) < 4 := by
  have hK'K : K' ≤ K := by
    rw [hK']
    exact section12_ambientDerivedSubgroup_le
  have hMLcardLe : Nat.card (M ⊓ L : Subgroup G) ≤ Nat.card H := by
    have hsubDvd := Subgroup.card_subgroup_dvd_card ((M ⊓ L).subgroupOf H)
    rw [natCard_subgroupOf_eq (M ⊓ L) H hMLleH] at hsubDvd
    exact Nat.le_of_dvd Nat.card_pos hsubDvd
  have hKnormal : (K.subgroupOf M).Normal :=
    section16MFSubgroup_subgroupOf_normal hKMF
  have hcompLocal :
      (K.subgroupOf M).IsComplement' ((M ⊓ L).subgroupOf M) :=
    section12ComplementIn_left_normal_isComplement' hcompM hKnormal
  have hcardM :
      Nat.card M = Nat.card K * Nat.card (M ⊓ L : Subgroup G) := by
    have hmul := hcompLocal.card_mul
    rw [natCard_subgroupOf_eq K M hcompM.1,
      natCard_subgroupOf_eq (M ⊓ L) M hcompM.2.1] at hmul
    exact hmul.symm
  have hcardMle : Nat.card M ≤ Nat.card K * Nat.card H := by
    rw [hcardM]
    exact Nat.mul_le_mul_left (Nat.card K) hMLcardLe
  have hK'cardLe : Nat.card K' ≤ Nat.card K := by
    have hle := Subgroup.card_le_card_group (K'.subgroupOf K)
    rwa [natCard_subgroupOf_eq K' K hK'K] at hle
  have hcardKlt : Nat.card K < 4 * Nat.card K' :=
    theorem_12_16_quotient_card_lt_four_arithmetic
      Nat.card_pos Nat.card_pos Nat.card_pos Nat.card_pos
      hK'cardLe hegt hcardMle hlowerM hlowerL hupper
  letI : (K'.subgroupOf K).Normal := by
    rw [hK', section12_ambientDerivedSubgroup_subgroupOf_eq]
    infer_instance
  have hK'subCard : Nat.card (K'.subgroupOf K) = Nat.card K' :=
    natCard_subgroupOf_eq K' K hK'K
  have hquotMul :
      Nat.card (K ⧸ K'.subgroupOf K) * Nat.card K' = Nat.card K := by
    have hmul := (Subgroup.card_eq_card_quotient_mul_card_subgroup
      (α := K) (s := K'.subgroupOf K)).symm
    rw [hK'subCard] at hmul
    exact hmul
  have hmulLt :
      Nat.card (K ⧸ K'.subgroupOf K) * Nat.card K' <
        4 * Nat.card K' := by
    rw [hquotMul]
    exact hcardKlt
  exact (Nat.mul_lt_mul_right (Nat.card_pos (α := K'))).mp hmulLt

/-- A prime divisor of a Frobenius complement divides the size of every
proper solvable kernel quotient minus one. -/
private theorem theorem_12_16_prime_dvd_frobenius_kernel_quotient_card_sub_one
    {Q : Type*} [Group Q] [Finite Q]
    {K R N : Subgroup Q} [N.Normal]
    {p : ℕ}
    (hp : Nat.Prime p)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hsolvK : Group.IsSolvable K)
    (hNK : N ≤ K) (hKnN : ¬ K ≤ N)
    (hpR : p ∣ Nat.card R) :
    p ∣ Nat.card (K ⧸ N.subgroupOf K) - 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let q : Q →* Q ⧸ N := QuotientGroup.mk' N
  have hfrobQuot :
      IsFrobeniusGroupWithKernelComplement (K.map q) (R.map q) :=
    lemma_3_2_b (K := K) (R := R) (N := N) hfrob hsolvK hKnN
  have hcardRmap : Nat.card (R.map q) = Nat.card R := by
    simpa [q] using
      natCard_map_mk'_eq_of_le_isComplement' K R N hNK hfrob.isComplement'
  have hpRmap : p ∣ Nat.card (R.map q) := by
    rw [hcardRmap]
    exact hpR
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' p hpRmap
  let zQ : Q ⧸ N := z
  have hzQorder : orderOf zQ = p := by
    dsimp [zQ]
    rw [Subgroup.orderOf_coe z]
    exact hzorder
  let Z : Subgroup (Q ⧸ N) := Subgroup.zpowers zQ
  have hZle : Z ≤ R.map q := Subgroup.zpowers_le.mpr z.property
  have hZcard : Nat.card Z = p := by
    simpa [Z, hzQorder] using Nat.card_zpowers zQ
  have hcentR :
      ∀ r : R.map q, r ≠ 1 →
        Section2.centralizerIn (K.map q) (r : Q ⧸ N) = ⊥ := by
    have hcentElem :
        ∀ r : R.map q, r ≠ 1 →
          elementCentralizerIn (K.map q) (r : Q ⧸ N) = ⊥ :=
      (lemma_3_1 (G := Q ⧸ N) (K := K.map q) (R := R.map q)
        hfrobQuot.kernel_ne_bot hfrobQuot.complement_ne_bot
        hfrobQuot.normal hfrobQuot.isComplement').1 hfrobQuot
    intro r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcentElem r hr
  have hcentZ :
      ∀ z : Z, z ≠ 1 →
        Section2.centralizerIn (K.map q) (z : Q ⧸ N) = ⊥ := by
    intro z hz
    let zR : R.map q := ⟨(z : Q ⧸ N), hZle z.property⟩
    have hzR : zR ≠ 1 := by
      intro hzR
      apply hz
      apply Subtype.ext
      change (z : Q ⧸ N) = 1
      exact congrArg Subtype.val hzR
    simpa [zR] using hcentR zR hzR
  letI : (K.map q).Normal := hfrobQuot.normal
  have hdivZ : Nat.card Z ∣ Nat.card (K.map q) - 1 :=
    Section6.frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (K := K.map q) (R := Z) (N := K.map q) le_rfl hcentZ
  rw [hZcard, show Nat.card (K.map q) = Nat.card (K ⧸ N.subgroupOf K) by
    simpa [q] using natCard_map_mk'_eq K N] at hdivZ
  exact hdivZ


private theorem theorem_12_16_prime_dvd_quotient_card_sub_one
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M K K' P0 L H Ls : Subgroup G} {x : G} {p : ℕ}
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p) :
    p ∣ Nat.card (K ⧸ K'.subgroupOf K) - 1 := by
  classical
  rcases h128 with
    ⟨hp, _hbad, _hmin, hM, hKMF, hTypeIM, _hMs, hK', hquot, hP0Sylow⟩
  rcases h129 with
    ⟨hP0comm, hP0rank, _hL, _hHMF, _hLs, _hP0Ls, _hxL,
      ⟨_hp', hxOmega, hxne⟩, _hcentK, _hnorm, _hcentL⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hP0M : P0 ≤ M := by
    rcases hP0Sylow with ⟨PM, hP0eq⟩
    rw [← hP0eq]
    exact section11_ambientSylow_le M PM
  have hP0p : IsPGroup p P0 := by
    rcases hP0Sylow with ⟨PM, hP0eq⟩
    rw [← hP0eq]
    dsimp [section10AmbientSylowSubgroup]
    exact IsPGroup.map (p := p) (H := (PM : Subgroup M)) PM.isPGroup' M.subtype
  have hxP0 : x ∈ P0 := by
    rcases hxOmega with ⟨y, _hy, rfl⟩
    exact y.property
  let P1 : Subgroup G := section12OmegaOneSubgroup ⟨p, hp⟩ P0
  letI : IsElementaryAbelian p P1 := by
    simpa [P1] using
      (theorem_12_9_omega_one_noncyclic P0 p hp hP0p hP0comm hP0rank).1
  have hxpowP1 : (⟨x, by simpa [P1] using hxOmega⟩ : P1) ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p P1) _
  have hxpow : x ^ p = 1 := congrArg Subtype.val hxpowP1
  have hxorder : orderOf x = p := orderOf_eq_prime hxpow hxne
  rcases hTypeIM with ⟨U, U1, U0, hF, _hAlt⟩
  rcases hF with
    ⟨_hMsolv, _hModd, _hKMF', hKpos, _hKlt, _hUne, hcomp,
      _hU1le, _hU1comm, _hU1norm, _hcent, _hU0le, hExpEq, hfrob0⟩
  have hpK : (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet K :=
    theorem_12_9_prime_not_mem_subgroupPrimeSet_of_quotient_noncyclic
      M K p hp hKMF hquot
  rcases theorem_12_9_exists_conjugate_le_typeF_complement
      M K U P0 p hp hM hKMF hcomp hP0M hP0p hpK with
    ⟨g, hP0gU⟩
  let xg : G := (g : G) * x * (g : G)⁻¹
  have hxgU : xg ∈ U := by
    apply hP0gU
    exact Subgroup.mem_map.mpr
      ⟨x, hxP0, by simp [xg, MulAut.conj_apply]⟩
  have hxgorder : orderOf xg = p := by
    rw [← hxorder]
    simpa [xg, MulAut.conj_apply] using (MulAut.conj (g : G)).orderOf_eq x
  have hpExpU : p ∣ Monoid.exponent U := by
    rw [← hxgorder]
    simpa [Subgroup.orderOf_coe] using
      (Monoid.order_dvd_exponent (⟨xg, hxgU⟩ : U))
  have hpExpU0 : p ∣ Monoid.exponent U0 := by
    rw [hExpEq]
    exact hpExpU
  have hpCardU0 : p ∣ Nat.card U0 :=
    hpExpU0.trans (Group.exponent_dvd_nat_card (G := U0))
  let S : Subgroup G := K ⊔ U0
  let Ksub : Subgroup S := K.subgroupOf S
  let Rsub : Subgroup S := U0.subgroupOf S
  let N : Subgroup S := K'.subgroupOf S
  have hKleS : K ≤ S := le_sup_left
  have hU0leS : U0 ≤ S := le_sup_right
  have hK'K : K' ≤ K := by
    rw [hK']
    exact section12_ambientDerivedSubgroup_le
  have hK'leS : K' ≤ S := hK'K.trans hKleS
  have hfrobS : IsFrobeniusGroupWithKernelComplement Ksub Rsub := by
    simpa [S, Ksub, Rsub, section12FrobeniusJoinWithKernel] using
      hfrob0
  have hSNormK : S ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleS).1 hfrobS.normal
  letI : (derivedSubgroup K).Characteristic := by infer_instance
  have hNormKDer :
      Subgroup.normalizer (K : Set G) ≤
        Subgroup.normalizer ((derivedSubgroup K).map K.subtype : Set G) :=
    section8_normalizer_map_subtype_le_of_characteristic
      (G := G) (H := K) (K := derivedSubgroup K)
  have hDmap : (derivedSubgroup K).map K.subtype = ambientDerivedSubgroup K := rfl
  have hSNormK' : S ≤ Subgroup.normalizer (K' : Set G) := by
    rw [hK', ← hDmap]
    exact hSNormK.trans hNormKDer
  have hNnormal : N.Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hK'leS).2 hSNormK'
  letI : N.Normal := hNnormal
  have hNleKsub : N ≤ Ksub := by
    intro z hz
    exact hK'K hz
  have hKsolv : Group.IsSolvable K := by
    letI : Group.IsNilpotent K := hKMF.1.2.2.1
    exact IsNilpotent.to_isSolvable
  have hKne : K ≠ ⊥ := ne_of_gt hKpos
  have hKnN : ¬ Ksub ≤ N := by
    intro hle
    have hKleK' : K ≤ K' := by
      intro y hy
      let yS : S := ⟨y, hKleS hy⟩
      have hyKsub : yS ∈ Ksub := by simpa [yS, Ksub]
      have hyN := hle hyKsub
      simpa [yS, N] using (Subgroup.mem_subgroupOf.mp hyN)
    have hDlt : ambientDerivedSubgroup K < K := by
      let _ : Group.IsSolvable K := hKsolv
      letI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot (H := K)).2 hKne
      have hcommLt : derivedSubgroup K < (⊤ : Subgroup K) := by
        simpa [derivedSubgroup, derivedSeries_one, commutator] using
          Group.IsSolvable.commutator_lt_top_of_nontrivial (G := K)
      refine lt_of_le_of_ne section12_ambientDerivedSubgroup_le ?_
      intro hEq
      have hDtop : derivedSubgroup K = (⊤ : Subgroup K) := by
        have hsubtop : (ambientDerivedSubgroup K).subgroupOf K = ⊤ := by
          rw [hEq]
          exact Subgroup.subgroupOf_eq_top.2 le_rfl
        simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hsubtop
      exact hcommLt.ne hDtop
    rw [hK'] at hKleK'
    exact (not_le_of_gt hDlt) hKleK'
  have hpRsub : p ∣ Nat.card Rsub := by
    have hcardRsub : Nat.card Rsub = Nat.card U0 := by
      simpa [Rsub] using natCard_subgroupOf_eq U0 S hU0leS
    rw [hcardRsub]
    exact hpCardU0
  have hKsubsolv : Group.IsSolvable Ksub := by
    let _ : Group.IsSolvable K := hKsolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hKleS).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKleS).injective
  have hlocal :=
    theorem_12_16_prime_dvd_frobenius_kernel_quotient_card_sub_one
      hp hfrobS hKsubsolv hNleKsub hKnN hpRsub
  have hcardKsub : Nat.card Ksub = Nat.card K :=
    natCard_subgroupOf_eq K S hKleS
  have hcardN : Nat.card N = Nat.card K' :=
    natCard_subgroupOf_eq K' S hK'leS
  have hcardNsub : Nat.card (N.subgroupOf Ksub) = Nat.card K' := by
    rw [natCard_subgroupOf_eq N Ksub hNleKsub, hcardN]
  have hlocalMul :
      Nat.card (Ksub ⧸ N.subgroupOf Ksub) * Nat.card K' = Nat.card K := by
    have hmul := (Subgroup.card_eq_card_quotient_mul_card_subgroup
      (α := Ksub) (s := N.subgroupOf Ksub)).symm
    rw [hcardNsub, hcardKsub] at hmul
    exact hmul
  letI : (K'.subgroupOf K).Normal := by
    rw [hK', section12_ambientDerivedSubgroup_subgroupOf_eq]
    infer_instance
  have hambientMul :
      Nat.card (K ⧸ K'.subgroupOf K) * Nat.card K' = Nat.card K := by
    have hmul := (Subgroup.card_eq_card_quotient_mul_card_subgroup
      (α := K) (s := K'.subgroupOf K)).symm
    rw [natCard_subgroupOf_eq K' K hK'K] at hmul
    exact hmul
  have hcardQuot :
      Nat.card (Ksub ⧸ N.subgroupOf Ksub) =
        Nat.card (K ⧸ K'.subgroupOf K) :=
    Nat.mul_right_cancel (Nat.card_pos (α := K'))
      (hlocalMul.trans hambientMul.symm)
  rwa [hcardQuot] at hlocal

set_option maxHeartbeats 1000000 in
/-- Construct the notation introduced in PF `(12.13)` from the canonical
Type-I Dade package for the Frobenius subgroup `L`. -/
private theorem theorem_12_16_exists_notation_12_13_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls : Subgroup G) (x : G) (p : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (hfrob : Section7.frobeniusWithKernel L H) :
    ∃ E : Subgroup G, ∃ e : ℕ,
    ∃ S : Finset (Section1.ClassFunction L),
    ∃ R : G → Subgroup G,
    ∃ tau tau1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
    ∃ chi : Section1.ClassFunction L,
    ∃ psi : Section1.ClassFunction G,
    ∃ psiRho : Section1.ClassFunction L,
      notation_12_13_data L H E e S R tau tau1 chi psi psiRho := by
  classical
  have hTypeIL : Section8.typeIDefinitionData L H :=
    theorem_12_10_typeI_reduction_source_leaf
      M K K' P0 L H Ls x p h128 h129
  rcases h129 with
    ⟨_hP0comm, _hP0rank, hLmax, hHMF, _hMsL, _hP0Ls, _hxL,
      _hxOmega, _hcentK, _hNxM, _hCnotL⟩
  rcases hTypeIL with ⟨E, E1, E0, hF, _hTypeICases⟩
  have hTypeILcopy : Section8.typeIDefinitionData L H :=
    ⟨E, E1, E0, hF, _hTypeICases⟩
  rcases hF with
    ⟨_hsolvL, _hoddL, _hHMF', hHne, _hHlt, _hEne, hcomp,
      _hE1le, _hE1comm, _hE1norm, _hcent, _hE0le, _hexp, _hfrobE0⟩
  rcases exists_puncturedInducedFamily (H.subgroupOf L) with ⟨S, hS⟩
  have hMsSource : Section8.msChoiceSource L H H :=
    Section8.msChoiceSource_of_typeIDefinitionData hTypeILcopy
  have hnot10 : Section8.notation_8_10_source_data L H H
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H) :=
    notation_8_10_source_data_of_typeI_msChoice
      L H hLmax hHMF hTypeILcopy hMsSource
  have hA1 : Section8.a1Set H ⊆ typeIASet L H := by
    simpa [Section8.a1Set] using
      nonidentity_kernel_subset_typeIASet L H (section16MFSubgroup_le hHMF)
  rcases Section8.exists_notation_8_14_source_data_of_theorem_8_13
      L H H (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
      (typeIASet L H) inferInstance hnot10 (Or.inl rfl) hA1 with
    ⟨R, tildeA, tildeA0, tildeA1, hnot⟩
  have h815 : Section8.theorem_8_15_source_data L H H
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
      (typeIASet L H) (Section8.section8DSet L (typeIASet L H))
      tildeA tildeA0 tildeA1 R :=
    ⟨hnot10, hnot, Or.inr (Or.inl rfl)⟩
  have h22 : Section2.Hypothesis2 (typeIASet L H) L R :=
    Section8.theorem_8_15_hypothesis2 (inferInstance : IsMinCE G) h815
  let tau : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G :=
    dadeTransformLinear R h22.subset_L
  have hDade : dadeIsometryRelativeToTypeIASet L H R tau := by
    simpa [tau] using
      dadeIsometryRelativeToTypeIASet_of_hypothesis2 L H R h22
  have h12 : hypothesis_12_1_data L H S R tau :=
    ⟨hLmax, hHMF, hTypeILcopy, hS, hDade⟩
  have h126 :
      (∀ chi : Section1.ClassFunction L, chi ∈ S →
        Section1.IsIrreducibleCharacterOnGroup chi) ∧
      Section6.coherentFamily S tau :=
    theorem_12_6 L H S R tau h12 hfrob
  rcases Section6.theorem_6_8_coherentExtension_of_coherentFamily h126.2 with
    ⟨tau1, hExt⟩
  have hHL : H ≤ L := section16MFSubgroup_le hHMF
  rcases hHMF.1 with ⟨_hHL', _hHnormal, hHnil, _hHall⟩
  letI : Group.IsNilpotent H := hHnil
  have _ : Group.IsSolvable H := IsNilpotent.to_isSolvable
  let hEquiv : H.subgroupOf L ≃* H := Subgroup.subgroupOfEquivOfLe hHL
  have hHsubSolv : Group.IsSolvable (H.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective (f := hEquiv.toMonoidHom) hEquiv.injective
  have hHsubNe : H.subgroupOf L ≠ ⊥ := by
    intro hbot
    apply hHne.ne'
    exact (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hHL
  have hSbot :
      Section6.inducedKernelFamily (H.subgroupOf L) (⊥ : Subgroup L) S :=
    theorem_12_6_inducedKernelFamily_bot_of_hypothesis12
      L H S R tau h12
  rcases Section6.inducedKernelFamily_exists_degree_relIndex_of_lt
      hHsubSolv (inferInstance : (⊥ : Subgroup L).Normal)
      (bot_lt_iff_ne_bot.mpr hHsubNe) hSbot with
    ⟨chi, hchiS, hchiDegreeRaw⟩
  have hrelSub :
      (H.subgroupOf L).relIndex (⊤ : Subgroup L) = H.relIndex L := by
    simpa using
      (Subgroup.relIndex_subgroupOf (H := H) (K := L) (L := L) le_rfl)
  have hchiDegree : Section1.degree chi = (H.relIndex L : ℂ) := by
    simpa [hrelSub] using hchiDegreeRaw
  have hchiIrr : Section1.IsIrreducibleCharacterOnGroup chi :=
    h126.1 chi hchiS
  let T : Finset (Section1.ClassFunction L) :=
    insert (Section7.principalInducedCharacter L H) S
  have hT : Section7.inducedFamilyNotation (H.subgroupOf L) T := by
    intro eta
    constructor
    · intro heta
      rw [Finset.mem_insert] at heta
      rcases heta with heta | heta
      · refine ⟨Section1.principalCharacter (H.subgroupOf L),
          Section3.principalCharacter_isIrreducibleCharacterOnGroup, ?_⟩
        simpa [T, Section7.principalInducedCharacter] using heta
      · rcases (hS eta).mp heta with ⟨theta, hthetaIrr, _hthetaNe, rfl⟩
        exact ⟨theta, hthetaIrr, rfl⟩
    · rintro ⟨theta, hthetaIrr, rfl⟩
      rw [Finset.mem_insert]
      by_cases htheta : theta = Section1.principalCharacter (H.subgroupOf L)
      · left
        simp [Section7.principalInducedCharacter, htheta]
      · right
        exact (hS _).mpr ⟨theta, hthetaIrr, htheta, rfl⟩
  have hAeq : typeIASet L H = Section7.puncturedSubgroupSet H := by
    simpa [Section7.puncturedSubgroupSet, section16NonidentityElements] using
      typeIASet_eq_nonidentity_kernel_of_frobenius L H hfrob
  have h76 : Section7.hypothesis_7_6_statement
      (typeIASet L H) L H R T := by
    exact ⟨hHL, section16MFSubgroup_subgroupOf_normal hHMF, h22, hAeq, hT⟩
  have hAgree :
      Section7.agreesWithDadeTransform (typeIASet L H) L R tau := by
    rcases hDade with ⟨_h22, hAL, htau⟩
    exact ⟨hAL, htau⟩
  have h78 : Section7.theorem_7_8_hypothesis
      L H T S tau tau1 chi := by
    refine ⟨hHL, ?_, hS, h126.2, hExt, hchiS, hchiIrr, hchiDegree⟩
    intro eta
    constructor
    · intro heta
      refine ⟨by simp [T, heta], ?_⟩
      intro hetaPrincipal
      have hzero := Section7.theorem_7_8_punctured_member_principal_orthogonal
        hS heta
      rw [hetaPrincipal] at hzero
      have hone := Section7.theorem_7_8_principalInduced_principal_scalar
        (G := G) (L := L) (H := H)
      exact one_ne_zero (hone.symm.trans hzero)
    · rintro ⟨hetaT, hetaNe⟩
      rw [Finset.mem_insert] at hetaT
      exact hetaT.resolve_left hetaNe
  have hrel : H.relIndex L = Nat.card E := by
    have hHnormal : (H.subgroupOf L).Normal :=
      section16MFSubgroup_subgroupOf_normal hHMF
    have hlocal : (H.subgroupOf L).IsComplement' (E.subgroupOf L) :=
      section12ComplementIn_left_normal_isComplement' hcomp hHnormal
    rw [Subgroup.relIndex, hlocal.symm.index_eq_card,
      natCard_subgroupOf_eq E L hcomp.2.1]
  let e : ℕ := Nat.card E
  have hdegreeE : Section1.degree chi = (e : ℂ) := by
    simpa [e, hrel] using hchiDegree
  let psi : Section1.ClassFunction G := tau1 chi
  have hpsiVirt : Theory.Character.IsVirtualCharacter psi := by
    dsimp [psi]
    exact hExt.2.1 chi (Section5.integerSpan_of_mem S hchiS)
  have hpsiClass : Section1.IsClassFunction psi := by
    rcases hpsiVirt with ⟨r, m, n, rho, hpsiEq⟩
    rw [hpsiEq]
    intro y g
    unfold Theory.Character.virtualCharacterOfRepresentations
    refine Finset.sum_congr rfl ?_
    intro i _hi
    have hchar :
        Section1.IsCharacter
          ((rho i).character : Section1.ClassFunction G) :=
      ⟨ULift.{u} (Fin (n i) → ℂ), inferInstance, inferInstance, inferInstance,
        Section1.uliftRepresentation
          (G := G) (V := Fin (n i) → ℂ) (rho i), by
          ext z
          exact (Section1.uliftRepresentation_character
            (G := G) (V := Fin (n i) → ℂ) (rho := rho i) z).symm⟩
    rw [Section1.isCharacter_isClassFunction ((rho i).character) hchar y g]
  let psiRho : Section1.ClassFunction L := Section7.dadeProjection L R psi
  have hRho : dadeProjectionData (typeIASet L H) L R psi psiRho :=
    ⟨h22, rfl⟩
  refine ⟨E, e, S, R, tau, tau1, chi, psi, psiRho, h12, hcomp, rfl,
    hchiS, hdegreeE, ?_, ?_, hExt, rfl, hpsiClass, hRho⟩
  · exact ⟨T, h76, hAgree, h78⟩
  · exact ⟨Section8.section8DSet L (typeIASet L H), tildeA, tildeA0,
      tildeA1, hMsSource, hnot⟩

/-- The noncyclic Sylow subgroup in `M / K` from Hypothesis `(12.8)` rules
out a Frobenius decomposition with kernel `K`. -/
private theorem theorem_12_16_not_frobenius_of_quotient_noncyclic
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K : Subgroup G) (p : ℕ)
    (hp : Nat.Prime p)
    (hquot : quotientHasNoncyclicSylow p K M) :
    ¬ Section7.frobeniusWithKernel M K := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  intro hfrob
  rcases hquot with ⟨_hKM, _hN, P, hPnoncyclic⟩
  rcases hfrob with
    ⟨_hKM', hKnormal, R, hcomp, hKne, hRne, hcentralizer⟩
  have hfrobKR :
      IsFrobeniusGroupWithKernelComplement (K.subgroupOf M) R :=
    (lemma_3_1 (K.subgroupOf M) R hKne hRne hKnormal hcomp).2
      hcentralizer
  have hoddM : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hoddR : Odd (Nat.card R) :=
    odd_of_card_dvd hoddM (Subgroup.card_subgroup_dvd_card R)
  have hZR : IsZGroup R :=
    isZGroup_of_frobenius_complement_of_odd (K.subgroupOf M) R hfrobKR hoddR
  let e : M ⧸ K.subgroupOf M ≃* R := hcomp.symm.QuotientMulEquiv
  let PR : Sylow p R :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPRcyclic : IsCyclic (PR : Subgroup R) :=
    (isZGroup_iff (G := R)).mp hZR p hp PR
  have hPcyclic : IsCyclic (P : Subgroup (M ⧸ K.subgroupOf M)) := by
    let eP :
        (P : Subgroup (M ⧸ K.subgroupOf M)) ≃*
          ((P : Subgroup (M ⧸ K.subgroupOf M)).map e.toMonoidHom) :=
      Subgroup.equivMapOfInjective
        (f := e.toMonoidHom) (P : Subgroup (M ⧸ K.subgroupOf M)) e.injective
    apply eP.isCyclic.mpr
    have hPR_subgroup : (PR : Subgroup R) = Subgroup.map e (P : Subgroup (M ⧸ K.subgroupOf M)) := by
      simp [PR, Sylow.coe_mapSurjective]
    exact hPR_subgroup.symm ▸ hPRcyclic
  exact hPnoncyclic hPcyclic

/-- Construct the canonical `M`-side PF `(8.14)` map and the Dade projection
used in PF `(12.15)`. -/
private theorem theorem_12_16_exists_M_projection_package
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 : Subgroup G) (p : ℕ)
    (psi : Section1.ClassFunction G)
    (h128 : hypothesis_12_8_data M K K' P0 p) :
    ∃ RM : G → Subgroup G, ∃ psiRhoM : Section1.ClassFunction M,
      theorem_12_15_source_data M K RM ∧
        dadeProjectionData (Section8.a1Set K) M RM psi psiRhoM := by
  classical
  rcases h128 with
    ⟨hp, _hbad, _hminp, hMmax, hKMF, hTypeIM, hMsM, _hK', hquot,
      _hP0Sylow⟩
  have hnotfrob : ¬ Section7.frobeniusWithKernel M K :=
    theorem_12_16_not_frobenius_of_quotient_noncyclic M K p hp hquot
  have hnot10M : Section8.notation_8_10_source_data M K K
      (typeIASet M K) (typeIASet M K) (Section8.a1Set K) :=
    notation_8_10_source_data_of_typeI_msChoice
      M K hMmax hKMF hTypeIM hMsM
  have hA1M : Section8.a1Set K ⊆ typeIASet M K := by
    simpa [Section8.a1Set] using
      nonidentity_kernel_subset_typeIASet M K (section16MFSubgroup_le hKMF)
  rcases Section8.exists_notation_8_14_source_data_of_theorem_8_13
      M K K (typeIASet M K) (typeIASet M K) (Section8.a1Set K)
      (typeIASet M K) inferInstance hnot10M (Or.inl rfl) hA1M with
    ⟨RM, tildeAM, tildeA0M, tildeA1M, hnotM⟩
  have h15src : theorem_12_15_source_data M K RM :=
    ⟨inferInstance, hnotfrob, typeIASet M K, typeIASet M K,
      Section8.a1Set K, Section8.section8DSet M (typeIASet M K),
      tildeAM, tildeA0M, tildeA1M, rfl, hMsM, hnot10M, hnotM⟩
  have h815M : Section8.theorem_8_15_source_data M K K
      (typeIASet M K) (typeIASet M K) (Section8.a1Set K)
      (Section8.a1Set K) (Section8.section8DSet M (typeIASet M K))
      tildeAM tildeA0M tildeA1M RM :=
    ⟨hnot10M, hnotM, Or.inr (Or.inr rfl)⟩
  have h22M : Section2.Hypothesis2 (Section8.a1Set K) M RM :=
    Section8.theorem_8_15_hypothesis2 (inferInstance : IsMinCE G) h815M
  let psiRhoM : Section1.ClassFunction M := Section7.dadeProjection M RM psi
  refine ⟨RM, psiRhoM, h15src, h22M, ?_⟩
  rfl

/-- PF `(8.18.c)` in the orientation used by the norm estimate in `(12.16)`.
The opposite orientation is ruled out by the element `x` from `(12.9)`. -/
private theorem theorem_12_16_projection_supports_disjoint
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M K K' P0 L H Ls E : Subgroup G}
    {e : ℕ}
    {S : Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {tau tau1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {chi : Section1.ClassFunction L}
    {RM : G → Subgroup G}
    {psi : Section1.ClassFunction G}
    {psiRho : Section1.ClassFunction L}
    {x : G} {p : ℕ}
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (h13 : notation_12_13_data L H E e S R tau tau1 chi psi psiRho)
    (h15src : theorem_12_15_source_data M K RM) :
    Disjoint (Section2.dadeSupport (Section8.a1Set K) RM)
      (Section2.dadeSupport (typeIASet L H) R) := by
  classical
  rcases h128 with
    ⟨hp, _hbad, _hminp, hMmax, hKMF, hTypeIM, hMsM, _hK', _hquot,
      _hP0Sylow⟩
  rcases h129 with
    ⟨_hP0comm, _hP0rank, hLmax, hHMF, hMsL, hP0Ls, _hxL,
      ⟨_hp', hxOmega, hxne⟩, hcentK, hNxM, _hCnotL⟩
  rcases h13 with
    ⟨h12L, _hcompL, _he, _hchiS, _hdegree, _h78pack, hnotpack,
      _hExt, _hpsi, _hpsiclass, _hRhoL⟩
  rcases hnotpack with
    ⟨DL, tildeAL, tildeA0L, tildeA1L, hMsLSource, hnotL⟩
  rcases h15src with
    ⟨hmin, _hnotfrobM, AM, A0M, A1M, DM, tildeAM, tildeA0M,
      tildeA1M, hA1M, _hMsM', hnot10M, hnotM⟩
  have hTypeIL : Section8.typeIDefinitionData L H := h12L.2.2.1
  have hnotconj : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) M L :=
    not_conj_of_hypothesis_12_8_12_9_typeI M K K' P0 L H Ls x p
      ⟨hp, _hbad, _hminp, hMmax, hKMF, hTypeIM, hMsM, _hK', _hquot,
        _hP0Sylow⟩
      ⟨_hP0comm, _hP0rank, hLmax, hHMF, hMsL, hP0Ls, _hxL,
        ⟨_hp', hxOmega, hxne⟩, hcentK, hNxM, _hCnotL⟩ hTypeIL
  have hTypeIsets : AM = typeIASet M K ∧ A0M = typeIASet M K := by
    rcases hnot10M.2.2.2.2 with hI | hP
    · have hAM : AM = typeIASet M K := by
        rw [typeIASet_eq_section8CentralizerUnion]
        exact hI.2.1
      exact ⟨hAM, hI.2.2.trans hAM⟩
    · rcases hP with ⟨U, W1, W2, hP, _hTypes, _hA, _hA0, _hLate⟩
      exact False.elim
        (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeIM)
  have hnotMtype : Section8.notation_8_14_source_data M
      (typeIASet M K) (typeIASet M K) (Section8.a1Set K)
      DM tildeAM tildeA0M tildeA1M RM := by
    simpa [hTypeIsets.1, hTypeIsets.2, hA1M] using hnotM
  rcases exists_puncturedInducedFamily (K.subgroupOf M) with ⟨SM, hSM⟩
  have h815M : Section8.theorem_8_15_source_data M K K
      (typeIASet M K) (typeIASet M K) (Section8.a1Set K)
      (typeIASet M K) DM tildeAM tildeA0M tildeA1M RM :=
    ⟨by simpa [hTypeIsets.1, hTypeIsets.2, hA1M] using hnot10M,
      hnotMtype, Or.inr (Or.inl rfl)⟩
  have h22M : Section2.Hypothesis2 (typeIASet M K) M RM :=
    Section8.theorem_8_15_hypothesis2 (inferInstance : IsMinCE G) h815M
  let tauM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G :=
    dadeTransformLinear RM h22M.subset_L
  have hDadeM : dadeIsometryRelativeToTypeIASet M K RM tauM := by
    simpa [tauM] using
      dadeIsometryRelativeToTypeIASet_of_hypothesis2 M K RM h22M
  have h12M : hypothesis_12_1_data M K SM RM tauM :=
    ⟨hMmax, hKMF, hTypeIM, hSM, hDadeM⟩
  have hdisjOr : Disjoint tildeA1M tildeAL ∨ Disjoint tildeA1L tildeAM :=
    theorem_8_18_tilde_disjoint_or_of_hypothesis12_notation_8_14
      M K L H SM S RM R tauM tau
      DM tildeAM tildeA0M tildeA1M DL tildeAL tildeA0L tildeA1L
      hmin hnotconj hMsM hMsLSource h12M h12L hnotMtype hnotL
  have hxP0 : x ∈ P0 := by
    rcases hxOmega with ⟨y, _hy, rfl⟩
    exact y.property
  have hLsEq : Ls = H := by
    rcases hMsL with hEarly | hLate
    · exact hEarly.2
    · rcases hLate.1 with hIII | hIV
      · rcases Section8.theorem_8_8_typeIII_to_source_public
          (G := G) hLmax hHMF hIII with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeIL)
      · rcases Section8.theorem_8_8_typeIV_to_source_public
          (G := G) hLmax hHMF hIV with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeIL)
  have hxH : x ∈ H := by
    rw [← hLsEq]
    exact hP0Ls hxP0
  have hxA1L : x ∈ Section8.a1Set H := by
    simp [Section8.a1Set, section16NonidentityElements, hxH, hxne]
  have hxM : x ∈ M := by
    apply hNxM
    apply centralizer_le_normalizer (Subgroup.zpowers x)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let xZ : Subgroup.zpowers x := ⟨x, Subgroup.mem_zpowers x⟩
    let yZ : Subgroup.zpowers x := ⟨y, hy⟩
    have hcomm : Commute (xZ : G) (yZ : G) := by
      have hx_mem : (xZ : G) ∈ Subgroup.zpowers (x : G) := xZ.property
      have hy_mem : (yZ : G) ∈ Subgroup.zpowers (x : G) := yZ.property
      rcases Subgroup.mem_zpowers_iff.mp hx_mem with ⟨m, hm⟩
      rcases Subgroup.mem_zpowers_iff.mp hy_mem with ⟨n, hn⟩
      simpa [hm, hn] using (Commute.refl (x : G)).zpow_zpow m n
    exact hcomm.symm.eq
  rcases Set.not_subset.mp hcentK with ⟨g0, hg0cent, hg0notK'⟩
  have hg0ne : g0 ≠ 1 := by
    intro hg0
    apply hg0notK'
    simp [hg0]
  have hxTypeAM : x ∈ typeIASet M K :=
    ⟨hxM, hxne, g0, hg0cent.1, hg0ne,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hg0cent.2).symm⟩
  have hxAM : x ∈ AM := by simpa [hTypeIsets.1] using hxTypeAM
  have hxTildeA1L : x ∈ tildeA1L := by
    rw [hnotL.2.2.2.2.2.2.2.2]
    refine ⟨x, hxA1L, x, ?_, 1, by simp, by simp⟩
    exact ⟨1, (R x).one_mem, by simp⟩
  have hxTildeAM : x ∈ tildeAM := by
    rw [hnotM.2.2.2.2.2.2.1]
    refine ⟨x, hxAM, x, ?_, 1, by simp, by simp⟩
    exact ⟨1, (RM x).one_mem, by simp⟩
  have hdisj : Disjoint tildeA1M tildeAL := by
    rcases hdisjOr with hgood | hbad
    · exact hgood
    · exact False.elim ((Set.disjoint_left.mp hbad hxTildeA1L) hxTildeAM)
  have hsuppM : Section2.dadeSupport (Section8.a1Set K) RM = tildeA1M :=
    dadeSupport_eq_tildeA1_of_notation_8_14 M
      (typeIASet M K) (typeIASet M K) (Section8.a1Set K)
      DM tildeAM tildeA0M tildeA1M RM hnotMtype
  have hsuppL : Section2.dadeSupport (typeIASet L H) R = tildeAL :=
    dadeSupport_eq_tildeA_of_notation_8_14_source_data L
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
      DL tildeAL tildeA0L tildeA1L R hnotL
  rwa [hsuppM, hsuppL]

/-- The last numerical contradiction in PF `(12.16)`, once the canonical
`(12.13)` and `(12.15)` projection packages have been constructed. -/
private theorem theorem_12_16_contradiction_of_projection_packages
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M K K' P0 L H Ls E : Subgroup G}
    {e : ℕ}
    {S : Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {tau tau1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {chi : Section1.ClassFunction L}
    {RM : G → Subgroup G}
    {psi : Section1.ClassFunction G}
    {psiRho : Section1.ClassFunction L}
    {psiRhoM : Section1.ClassFunction M}
    {x : G} {p : ℕ}
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (hfrob : Section7.frobeniusWithKernel L H)
    (h13 : notation_12_13_data L H E e S R tau tau1 chi psi psiRho)
    (h15src : theorem_12_15_source_data M K RM)
    (hRhoM : dadeProjectionData (Section8.a1Set K) M RM psi psiRhoM) :
    False := by
  classical
  have h128copy := h128
  have h129copy := h129
  have h13copy := h13
  rcases h128 with
    ⟨hp, _hbad, _hmin, _hMmax, hKMF, hTypeIM, _hMsM, hK', _hquot,
      _hP0Sylow⟩
  rcases h129 with
    ⟨hP0comm, hP0rank, _hLmax, _hHMF, _hMsL, _hP0Ls, hxL,
      ⟨_hp', hxOmega, hxne⟩, hcentK, _hNxM, _hCnotL⟩
  rcases h13 with
    ⟨_h12L, hcompL, he, hchiS, hdegree, h78pack, _hnotpack,
      hExt, hpsi, hpsiclass, hRhoL⟩
  rcases h78pack with ⟨_T, _h76, _hAgree, h78⟩
  have hchiIrr : Section1.IsIrreducibleCharacterOnGroup chi :=
    h78.2.2.2.2.2.2.1
  have hchiVirt : Theory.Character.IsVirtualCharacter chi :=
    Section5.isVirtualCharacter_of_isCharacter
      (isCharacter_of_isIrreducibleCharacterOnGroup hchiIrr)
  have hpsiSigned : Section3.IsSignedIrreducibleCharacter psi := by
    rw [hpsi]
    exact Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
      hExt hchiS hchiIrr
  have hpsiVirt : Theory.Character.IsVirtualCharacter psi :=
    Section3.isVirtualCharacter_of_signedIrreducible_pf35 hpsiSigned
  have h15 := theorem_12_15 M K K' P0 L H Ls E e S R tau tau1 chi
    RM psi psiRho psiRhoM x p h15src h128copy h129copy h13copy hRhoM
  have hP0p : IsPGroup p P0 := by
    rcases h128copy.2.2.2.2.2.2.2.2.2 with ⟨PM, hP0eq⟩
    letI : Fact p.Prime := ⟨hp⟩
    rw [← hP0eq]
    dsimp [section10AmbientSylowSubgroup]
    exact IsPGroup.map (p := p) (H := (PM : Subgroup M)) PM.isPGroup' M.subtype
  let P1 : Subgroup G := section12OmegaOneSubgroup ⟨p, hp⟩ P0
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsElementaryAbelian p P1 := by
    simpa [P1] using
      (theorem_12_9_omega_one_noncyclic P0 p hp hP0p hP0comm hP0rank).1
  have hxpowP1 : (⟨x, by simpa [P1] using hxOmega⟩ : P1) ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p P1) _
  have hxpow : x ^ p = 1 := congrArg Subtype.val hxpowP1
  have hxorder : orderOf x = p := orderOf_eq_prime hxpow hxne
  have hpDvdG : p ∣ Nat.card G := by
    rw [← hxorder]
    exact orderOf_dvd_natCard x
  have hoddp : Odd p := Odd.of_dvd_nat IsMinCE.odd_order hpDvdG
  have hodde : Odd e := by
    rw [he]
    exact odd_of_card_dvd IsMinCE.odd_order
      (Subgroup.card_subgroup_dvd_card E)
  have h12 := theorem_12_12 M K K' P0 L H Ls E x p e
    h128copy h129copy hfrob hcompL he
  rcases Set.not_subset.mp hcentK with ⟨g0, hg0cent, hg0notK'⟩
  have hg0K : g0 ∈ K := hg0cent.1
  have hxg0comm : x * g0 = g0 * x := by
    exact (Subgroup.mem_centralizer_singleton_iff.mp hg0cent.2).symm
  have hvalue0 : psi (x * g0) = chi ⟨x, hxL⟩ :=
    (theorem_12_14 M K K' P0 L H Ls E e S R tau tau1 chi psi psiRho
      x g0 p h128copy h129copy h13copy hxL hg0K).1.trans
      (theorem_12_14 M K K' P0 L H Ls E e S R tau tau1 chi psi psiRho
        x g0 p h128copy h129copy h13copy hxL hg0K).2
  have hzg0 : psi g0 ∈ Set.range (fun z : ℤ => (z : ℂ)) :=
    h15.2.2 g0 hg0K hg0notK'
  have hbound0 : (e : ℝ) - 1 ≤ ‖psi g0‖ :=
    theorem_12_16_value_abs_ge hp hoddp hodde hchiVirt hpsiVirt
      hxL hxorder hxg0comm hvalue0 hdegree hzg0 h12.2
  have hbound : ∀ g : G, g ∈ K → g ∉ K' → (e : ℝ) - 1 ≤ ‖psi g‖ := by
    intro g hgK hgnotK'
    have hconst : psi g0 = psi g :=
      h15.2.1 g0 g hg0K hg0notK' hgK hgnotK'
    simpa [hconst] using hbound0
  have hEone : 1 < Nat.card E := by
    rcases hfrob with
      ⟨_hHL, hHnormal, Eloc, hcompLoc, _hHne, hElocne, _hcent⟩
    have hcompELoc : (H.subgroupOf L).IsComplement' (E.subgroupOf L) :=
      section12ComplementIn_left_normal_isComplement' hcompL hHnormal
    have hcardE : Nat.card E = Nat.card Eloc := by
      have hindexE := hcompELoc.symm.index_eq_card
      have hindexEloc := hcompLoc.symm.index_eq_card
      rw [natCard_subgroupOf_eq E L hcompL.2.1] at hindexE
      exact hindexE.symm.trans hindexEloc
    rw [hcardE]
    exact (Subgroup.one_lt_card_iff_ne_bot Eloc).2 hElocne
  have hegt : 2 < e := by
    rw [he]
    rcases hodde with ⟨a, ha⟩
    have := hEone
    omega
  have hK'K : K' ≤ K := by
    rw [hK']
    exact section12_ambientDerivedSubgroup_le
  have hlowerM := theorem_12_16_projection_energy_lower
    (section16MFSubgroup_le hKMF) hK'K hRhoM.2 h15.1 hbound (by omega)
  have hlowerL := theorem_12_16_projection_energy_lower_frobenius
    IsMinCE.odd_order hfrob h13copy
  have hdisjoint := theorem_12_16_projection_supports_disjoint
    h128copy h129copy h13copy h15src
  have hupper := theorem_12_16_projection_energy_sum_lt_one
    hRhoM.1 hRhoL.1 hdisjoint hpsiclass hpsiSigned
  have h11 := theorem_12_11 M K K' P0 L H Ls x p
    h128copy h129copy hfrob
  have hquotLt : Nat.card (K ⧸ K'.subgroupOf K) < 4 :=
    theorem_12_16_quotient_card_lt_four hKMF hK' h11.1 h11.2 hegt
      hlowerM hlowerL hupper
  have hpDvdQuot : p ∣ Nat.card (K ⧸ K'.subgroupOf K) - 1 :=
    theorem_12_16_prime_dvd_quotient_card_sub_one h128copy h129copy
  have hKsolv : Group.IsSolvable K := by
    letI : Group.IsNilpotent K := hKMF.1.2.2.1
    exact IsNilpotent.to_isSolvable
  have hKne : K ≠ ⊥ := by
    rcases hTypeIM with ⟨_U, _U1, _U0, hF, _hAlt⟩
    exact ne_of_gt hF.2.2.2.1
  have hK'lt : K' < K := by
    rw [hK']
    have _ : Group.IsSolvable K := hKsolv
    haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot (H := K)).2 hKne
    have hcommLt : derivedSubgroup K < (⊤ : Subgroup K) := by
      simpa [derivedSubgroup, derivedSeries_one, commutator] using
        Group.IsSolvable.commutator_lt_top_of_nontrivial (G := K)
    refine lt_of_le_of_ne section12_ambientDerivedSubgroup_le ?_
    intro hEq
    have hDtop : derivedSubgroup K = (⊤ : Subgroup K) := by
      have hsubtop : (ambientDerivedSubgroup K).subgroupOf K = ⊤ := by
        rw [hEq]
        exact Subgroup.subgroupOf_eq_top.2 le_rfl
      simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hsubtop
    exact hcommLt.ne hDtop
  letI : (K'.subgroupOf K).Normal := by
    rw [hK', section12_ambientDerivedSubgroup_subgroupOf_eq]
    infer_instance
  have hquotMul :
      Nat.card (K ⧸ K'.subgroupOf K) * Nat.card K' = Nat.card K := by
    have hmul := (Subgroup.card_eq_card_quotient_mul_card_subgroup
      (α := K) (s := K'.subgroupOf K)).symm
    rw [natCard_subgroupOf_eq K' K hK'K] at hmul
    exact hmul
  have hquotNeOne : Nat.card (K ⧸ K'.subgroupOf K) ≠ 1 := by
    intro hcard
    rw [hcard, one_mul] at hquotMul
    apply hK'lt.ne
    exact Subgroup.eq_of_le_of_card_ge hK'K (le_of_eq hquotMul.symm)
  have hquotOneLt : 1 < Nat.card (K ⧸ K'.subgroupOf K) := by
    have hpos := Nat.card_pos (α := K ⧸ K'.subgroupOf K)
    omega
  have hpLe : p ≤ Nat.card (K ⧸ K'.subgroupOf K) - 1 :=
    Nat.le_of_dvd (by omega) hpDvdQuot
  have hpNeTwo : p ≠ 2 :=
    Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpDvdG
  have hpgt : 2 < p := by
    have := hp.two_le
    omega
  omega

/-- Peterfalvi `(12.16)` (Proof of Theorem `(12.7)`).

Under the Hypothesis `(12.8)`, the notation introduced in `(12.9)`–`(12.15)`
leads to a contradiction, thereby proving Theorem `(12.7)`. -/
public theorem theorem_12_16
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 : Subgroup G)
    (p : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p) :
    False := by
  rcases theorem_12_9 M K K' P0 p h128 with ⟨L, H, Ls, x, h129⟩
  have hfrob : Section7.frobeniusWithKernel L H :=
    theorem_12_10 M K K' P0 L H Ls x p h128 h129
  rcases theorem_12_16_exists_notation_12_13_data
      M K K' P0 L H Ls x p h128 h129 hfrob with
    ⟨E, e, S, R, tau, tau1, chi, psi, psiRho, h13⟩
  rcases theorem_12_16_exists_M_projection_package
      M K K' P0 p psi h128 with
    ⟨RM, psiRhoM, h15src, hRhoM⟩
  exact theorem_12_16_contradiction_of_projection_packages
    h128 h129 hfrob h13 h15src hRhoM

end CFSG.Section12
