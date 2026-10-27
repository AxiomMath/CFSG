module

public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Timmesfeld.Bridge.Asc72Local
public import CFSG.Timmesfeld.Bridge.OddLocalDefs
import CFSG.GroupTheory.InvolutionClassDerived
import CFSG.GroupTheory.InvolutionPow
import CFSG.GroupTheory.OddConjInvCommute
import CFSG.GroupTheory.OddInversion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

private theorem commute_mul_of_mem_commSet {X : Type*} [Group X] {S : Set X} (hS : IsOddTransp S)
    {N : Subgroup X} (hN : Odd (Nat.card N))
    (hnorm : ∀ t ∈ S, ∀ n ∈ N, t * n * t⁻¹ ∈ N) {u x : X} (hu : u ∈ S)
    (hwS : u * x ∈ S) (hxN : x ∈ N) :
    ∀ v ∈ commSet S u, Commute (u * x) v := by
  intro v hv
  obtain ⟨hvS, hvu, hvne⟩ := hv
  by_contra hwc
  have hu2 : u * u = 1 := hS.mul_self_eq_one hu
  have hv2 : v * v = 1 := hS.mul_self_eq_one hvS
  set P : X := u * v with hPdef
  set x' : X := v * x * v⁻¹ with hx'def
  have hP2 : P * P = 1 := by
    have hp : P * P = u * (v * u) * v := by rw [hPdef]; group
    rw [hp, hvu.eq]
    rw [show u * (u * v) * v = (u * u) * (v * v) by group, hu2, hv2, one_mul]
  have hPne : P ≠ 1 := fun hP1 => hvne (hS.eq_of_mul_eq_one hu hP1).symm
  have hx'N : x' ∈ N := hnorm v hvS x hxN
  have hPnorm : ∀ q ∈ N, P * q * P⁻¹ ∈ N := by
    intro q hq
    rw [hPdef]
    convert hnorm u hu (v * q * v⁻¹) (hnorm v hvS q hq) using 1
    group
  have hwv : u * x * v = P * x' := by
    have hxv : x * v = v * x' := by
      rw [hx'def, hS.inv_eq hvS,
        show v * (v * x * v) = (v * v) * x * v by group, hv2, one_mul]
    rw [mul_assoc, hxv, hPdef, mul_assoc]
  rcases hS.2 (u * x) hwS v hvS with hdvd | hodd
  · exact hwc ((CFSG.Timmesfeld.commute_iff_mul_sq_eq_one (hS.mul_self_eq_one hwS) hv2).2
      (orderOf_dvd_iff_pow_eq_one.mp hdvd))
  · have hodd' : Odd (orderOf (P * x')) := by rwa [hwv] at hodd
    have hPinv : P⁻¹ = P := inv_eq_of_mul_eq_one_right hP2
    have hconj : (x' * P) ^ orderOf (P * x') ∈ N := by
      rw [show x' * P = P * (P * x') * P⁻¹ by
        rw [hPinv]
        calc x' * P = (P * P) * x' * P := by rw [hP2, one_mul]
          _ = P * (P * x') * P := by group]
      rw [conj_pow]
      exact hPnorm ((P * x') ^ orderOf (P * x')) (by rw [pow_orderOf_eq_one]; exact N.one_mem)
    have hPN : P ∈ N :=
      CFSG.GroupTheory.mem_of_mul_pow_mem_of_conj_mem hx'N (hPnorm x' hx'N) hP2 hodd' hconj
    exact (CFSG.OddInversion.notMem_of_odd_card hN (orderOf_eq_prime (by rwa [pow_two]) hPne)) hPN

theorem commute_of_mem_closure_commSet_of_odd {X : Type*} [Group X] {S : Set X}
    (hS : IsOddTransp S) {N : Subgroup X} (hN : Odd (Nat.card N))
    (hnorm : ∀ t ∈ S, ∀ n ∈ N, t * n * t⁻¹ ∈ N) {u : X} (hu : u ∈ S)
    (hstab : ∀ n ∈ N, n * u * n⁻¹ ∈ S)
    (hgen : u ∈ Subgroup.closure (commSet S u)) : ∀ n ∈ N, Commute u n := by
  classical
  have hu2 : u * u = 1 := hS.mul_self_eq_one hu
  intro n hn
  by_contra hnc
  set x : X := n⁻¹ * (u * n * u⁻¹) with hxdef
  have hxN : x ∈ N := N.mul_mem (N.inv_mem hn) (hnorm u hu n hn)
  have hxne : x ≠ 1 := by
    intro hx1
    apply hnc
    have h : u * n * u⁻¹ = n := by
      have := congrArg (fun z => n * z) hx1
      simpa [hxdef, mul_assoc] using this
    have h2 : u * n = n * u := by
      have := congrArg (fun z => z * u) h
      simpa [mul_assoc, hS.inv_eq hu, hu2] using this
    exact h2
  have hux : u * x * u⁻¹ = x⁻¹ := by
    rw [hxdef]
    simp only [mul_inv_rev, hS.inv_eq hu]
    rw [show u * (n⁻¹ * (u * n * u)) * u = (u * n⁻¹ * u * n) * (u * u) by group,
      hu2, mul_one]
    group
  have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hxN)
  obtain ⟨j, hk⟩ := hxodd
  have hxy : x ^ j * u * (x ^ j)⁻¹ = u * x :=
    CFSG.GroupTheory.conj_pow_eq_mul hux hk (pow_orderOf_eq_one x)
  have hwS : u * x ∈ S := by
    have := hstab (x ^ j) (N.pow_mem hxN j)
    rwa [hxy] at this
  have hwcomm : Commute u (u * x) := by
    have hle : Subgroup.closure (commSet S u) ≤ Subgroup.centralizer ({u * x} : Set X) := by
      rw [Subgroup.closure_le]
      intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_mul_of_mem_commSet hS hN hnorm hu hwS hxN v hv).symm.eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hgen)
  have hxx : x * x = 1 := by
    have h1 : x = x⁻¹ := by
      calc x = u * (u * x) := by rw [← mul_assoc, hu2, one_mul]
        _ = (u * x) * u := hwcomm.eq
        _ = u * x * u⁻¹ := by rw [hS.inv_eq hu]
        _ = x⁻¹ := hux
    simpa [← h1] using mul_inv_cancel x
  exact hxne ((CFSG.GroupTheory.pow_eq_self_of_odd_of_mul_self_eq_one hxx ⟨j, hk⟩).symm.trans
    (pow_orderOf_eq_one x))

theorem mem_closure_commSet_centSet_of_mul_mem {X : Type*} [Group X] {S : Set X} {a c : X}
    (hc : c ∈ S) (hc1 : c ≠ 1) (hac : a ≠ c) (hcomm : Commute a c) (hmul : a * c ∈ S) :
    a ∈ Subgroup.closure (commSet (centSet S c) a) := by
  have hcaS : c * a ∈ S := by
    rw [← hcomm.eq]
    exact hmul
  have hc_mem : c ∈ commSet (centSet S c) a := by
    refine ⟨⟨hc, Commute.refl c⟩, hcomm.symm, fun h => hac h.symm⟩
  have hca_mem : c * a ∈ commSet (centSet S c) a := by
    refine ⟨⟨hcaS, (Commute.refl c).mul_left hcomm⟩, hcomm.symm.mul_left (Commute.refl a), ?_⟩
    intro h
    have h1 : c * a = (1 : X) * a := by rw [one_mul]; exact h
    exact hc1 (mul_right_cancel h1)
  have haeq : a = c⁻¹ * (c * a) := by
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hmem : c⁻¹ * (c * a) ∈ Subgroup.closure (commSet (centSet S c) a) :=
    Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.subset_closure hc_mem))
      (Subgroup.subset_closure hca_mem)
  rwa [← haeq] at hmem

end CFSG.OddTranspositions.PartThree.ElevenThree
