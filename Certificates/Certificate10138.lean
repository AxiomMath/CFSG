module

public import Certificates.Data.M23ThreeKD
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
import CFSG.Certificates.Kernel.M23Three.CentBound
import CFSG.Certificates.Kernel.PermCent.SmallBSound
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
import Certificates.Kernel.M23Three.Checks
public import Certificates.Data.Kernel.PermCent.CV
import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.LocalAnalysis.GLTheoremA.KD264M23
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelM23Three
  CFSG.Certificates.Kernel.M23Three

namespace Certificates

private theorem orbitSize_eq_len {n : Nat} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Q.orbitSize i = (levelV (strongV Q) Q.base i).entries.length := by
  unfold RawSchreierDatum.orbitSize
  rw [orbitSearch_eq Q _ (strongV_map Q)]
  simp [SchreierOrbitState.keys, toSt]

private theorem qf_valid : ValidSchreier QF := check_certificate_of _ _ _ _ _ kQF

private theorem qf_sub : QF.originalSubgroup = CFSG.Blueprint.NativeSporadic.M23 := by
  rw [QF, certificate_originalSubgroup, CFSG.Sporadic.Schreier.m23_eq_closure]
  congr 1
  ext g
  simp [m23S]

private theorem mem_m23 (w : List ℤ) : evalCodes m23S w ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  rw [← qf_sub]
  refine evalCodes_mem _ (fun g hg => ?_) w
  rw [QF, certificate_originalSubgroup]
  exact Subgroup.subset_closure hg

private theorem card_m23 : Nat.card CFSG.Blueprint.NativeSporadic.M23 = 10200960 := by
  rw [← qf_sub, ← QF.orderCertificate_eq_card qf_valid, orderCertificate_eq_orderV]
  unfold orderV
  rw [kOrbits]
  rfl

private theorem card_fix :
    Nat.card ↥(CFSG.Blueprint.NativeSporadic.M23 ⊓ fixingSubgroup (Equiv.Perm (Fin 23))
      (((QF.base.toList.take 5).toFinset : Finset (Fin 23)) : Set (Fin 23))) = 3 := by
  have hi : 5 ≤ QF.baseCount := by decide
  have h := QF.levelSubgroup_eq_pointwise_stabilizer qf_valid 5 hi
  rw [qf_sub] at h
  rw [List.coe_toFinset, ← h, QF.level_card_eq_orbit_product qf_valid 5 hi]
  have hlev : ∀ j, Nat.card (QF.orbitPoints j) = (levelV (strongV QF) QF.base j).entries.length :=
    fun j => by rw [← QF.orbitSize_eq_card, orbitSize_eq_len]
  simp only [hlev]
  rw [List.map_drop, kOrbits]
  rfl

private theorem fix_iff (x : Fin 23) :
    ev zC x = x ↔ x ∈ ((QF.base.toList.take 5).toFinset : Finset (Fin 23)) := by
  have h := List.all_eq_true.1 kFix x (List.mem_finRange x)
  rw [beq_iff_eq, decide_eq_decide] at h
  rw [List.mem_toFinset]
  exact h

private theorem class_bound : 56672 ≤ (conjClass CFSG.Blueprint.NativeSporadic.M23 (ev zC)).ncard := by
  have hR := kRel
  unfold relC at hR
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hR
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hz3, hz1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hw⟩ := hR
  have ew : evalCodes m23S wW = ev wC := (ev_evCodesB m23S wW).symm
  have hwG : ev wC ∈ CFSG.Blueprint.NativeSporadic.M23 := ew ▸ mem_m23 wW
  have hz3' : ev zC ^ 3 = 1 := by rw [ev_pow', hz3, ev_one]
  have hz1' : ev zC ≠ 1 := by
    rw [one_eq_ev, Ne, ev_eq_iff]
    exact hz1
  have hw' : ev wC * ev zC * (ev wC)⁻¹ = ev zC * ev zC := by
    rw [ev_inv', ev_mul', ev_mul', ev_mul', hw]
  have hb := two_mul_card_centralizerIn_le CFSG.Blueprint.NativeSporadic.M23 _ (ev zC) (ev wC) hwG
    hz3' hz1' hw' fix_iff
  have hcard5 : ((QF.base.toList.take 5).toFinset : Finset (Fin 23)).card = 5 := by decide
  rw [card_fix, hcard5] at hb
  have h := ncard_conjClass_mul_card CFSG.Blueprint.NativeSporadic.M23 (ev zC)
  rw [card_m23] at h
  by_contra hlt
  push Not at hlt
  have : (conjClass CFSG.Blueprint.NativeSporadic.M23 (ev zC)).ncard *
      Nat.card (centralizerIn CFSG.Blueprint.NativeSporadic.M23 (ev zC)) ≤ 56671 * 180 :=
    Nat.mul_le_mul (by omega) (by simp [Nat.factorial] at hb; omega)
  omega

open CFSG.Sporadic.Schreier CFSG.LocalAnalysis.GLTheoremA.KD264M23 in
theorem certificate10138 : evalCodes m23S zW ^ 3 = 1 ∧ evalCodes m23S zW ≠ 1 ∧ evalCodes m23S m1W ^ 3 = 1 ∧
    evalCodes m23S m2W ^ 2 = 1 ∧ evalCodes m23S m3W ^ 2 = 1 ∧
    (evalCodes m23S m1W * evalCodes m23S m2W) ^ 3 = 1 ∧
    (evalCodes m23S m2W * evalCodes m23S m3W) ^ 3 = 1 ∧
    (evalCodes m23S m1W * evalCodes m23S m3W) ^ 2 = 1 ∧ evalCodes m23S m1W ≠ 1 ∧
    evalCodes m23S m1W * evalCodes m23S zW = evalCodes m23S zW * evalCodes m23S m1W ∧
    evalCodes m23S m2W * evalCodes m23S zW = evalCodes m23S zW * evalCodes m23S m2W ∧
    evalCodes m23S m3W * evalCodes m23S zW = evalCodes m23S zW * evalCodes m23S m3W ∧
    56672 ≤ (conjClass CFSG.Blueprint.NativeSporadic.M23 (evalCodes m23S zW)).ncard := by
  have hR := kRel
  unfold relC at hR
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hR
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hz3, hz1⟩, h13⟩, h22⟩, h32⟩, h123⟩, h233⟩, h132⟩, hm1⟩, hc1⟩, hc2⟩, hc3⟩,
    -⟩ := hR
  have ez : evalCodes m23S zW = ev zC := (ev_evCodesB m23S zW).symm
  have e1 : evalCodes m23S m1W = ev m1C := (ev_evCodesB m23S m1W).symm
  have e2 : evalCodes m23S m2W = ev m2C := (ev_evCodesB m23S m2W).symm
  have e3 : evalCodes m23S m3W = ev m3C := (ev_evCodesB m23S m3W).symm
  have p1 : ∀ (x : CV 23) (k : ℕ), x ^ k = 1 → ev x ^ k = 1 := fun x k h => by
    rw [ev_pow', h, ev_one]
  have p2 : ∀ (x y : CV 23) (k : ℕ), (x * y) ^ k = 1 → (ev x * ev y) ^ k = 1 := fun x y k h => by
    rw [ev_mul', ev_pow', h, ev_one]
  have p3 : ∀ x : CV 23, ¬x = 1 → ev x ≠ 1 := fun x h => by
    rw [one_eq_ev, Ne, ev_eq_iff]
    exact h
  have p4 : ∀ x y : CV 23, x * y = y * x → ev x * ev y = ev y * ev x := fun x y h => by
    rw [ev_mul', ev_mul', h]
  rw [ez, e1, e2, e3]
  exact ⟨p1 _ _ hz3, p3 _ hz1, p1 _ _ h13, p1 _ _ h22, p1 _ _ h32, p2 _ _ _ h123, p2 _ _ _ h233,
    p2 _ _ _ h132, p3 _ hm1, p4 _ _ hc1, p4 _ _ hc2, p4 _ _ hc3, class_bound⟩

end Certificates
