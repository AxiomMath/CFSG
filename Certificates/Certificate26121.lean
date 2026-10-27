module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21HCommCheck
import Certificates.Certificate2012
import Certificates.Kernel.U42Ten.Checks
import CFSG.Certificates.Kernel.ConjRecSound
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model

namespace CertificateChecks.KernelU42Ten

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ConjRec
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.ComponentClassification.PSL3Four (TabRep)

theorem tabRep_of_all {P : Nat} {g : Equiv.Perm (Fin 45)}
    (h : (List.finRange 45).all (fun i => Nat.beq (pg 6 (mask 6) P i.val) (g i).val) = true) :
    TabRep (unpack 45 6 P) g := by
  refine ⟨by simp [unpack], fun i => ?_⟩
  have e := List.all_eq_true.1 h i (List.mem_finRange i)
  unfold unpack
  rw [getElem!_pos _ _ (by simp), Array.getElem_ofFn]
  exact Nat.eq_of_beq_eq_true e

theorem hX : canonK 45 6 (mask 6) (45 * 6) X = true := by decide +kernel
theorem hXI : canonK 45 6 (mask 6) (45 * 6) XI = true := by decide +kernel
theorem hY : canonK 45 6 (mask 6) (45 * 6) Y = true := by decide +kernel
theorem hYI : canonK 45 6 (mask 6) (45 * 6) YI = true := by decide +kernel

theorem hXr : TabRep (unpack 45 6 X) x45 := tabRep_of_all (by decide +kernel)
theorem hXIr : TabRep (unpack 45 6 XI) x45⁻¹ := tabRep_of_all (by decide +kernel)
theorem hYr : TabRep (unpack 45 6 Y) y45 := tabRep_of_all (by decide +kernel)
theorem hYIr : TabRep (unpack 45 6 YI) y45⁻¹ := tabRep_of_all (by decide +kernel)

theorem y45_pow_five : y45 ^ 5 = 1 := by decide +kernel

theorem y45_ne_one : y45 ≠ 1 := by decide +kernel

theorem orderOf_y45 : orderOf y45 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime y45_pow_five y45_ne_one

theorem okAll : ∀ i < N, ok26121 i = true := by
  have key : ∀ b len, allBlk b ok26121 len = true → ∀ i, b ≤ i → i < b + len →
      ok26121 i = true := fun b len h i h1 h2 => by
    have := allBlk_true h (i - b) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  rw [ch26121N]
  intro i hi
  by_cases h0 : i < 325
  · exact key 0 325 ch26121b0 i (by omega) (by omega)
  by_cases h1 : i < 650
  · exact key 325 325 ch26121b1 i (by omega) (by omega)
  by_cases h2 : i < 975
  · exact key 650 325 ch26121b2 i (by omega) (by omega)
  by_cases h3 : i < 1300
  · exact key 975 325 ch26121b3 i (by omega) (by omega)
  by_cases h4 : i < 1625
  · exact key 1300 325 ch26121b4 i (by omega) (by omega)
  by_cases h5 : i < 1950
  · exact key 1625 325 ch26121b5 i (by omega) (by omega)
  by_cases h6 : i < 2275
  · exact key 1950 325 ch26121b6 i (by omega) (by omega)
  · exact key 2275 318 ch26121b7 i (by omega) (by omega)

theorem no_ten : ∀ z ∈ QP45.originalSubgroup, orderOf z ≠ 10 := by
  obtain ⟨L, hlen, hnd, hmem⟩ := conjRec_sound (n := 45) (w := 6) (cw := 270) (pb := 12)
    (T := T) (N := N) rfl hX hXr hXI hXIr hY hYr hYI hYIr hY hYr okAll
  rw [ch26121N] at hlen
  have hcard : Nat.card QP45.originalSubgroup = 5 * 5184 := by
    rw [CFSG.GH74.KGroups.card_group QP45 QP45_ok, QP45_valid.2]
  have hyP : y45 ∈ QP45.originalSubgroup := by
    rw [QP45_closure]
    exact Subgroup.subset_closure (by simp)
  refine no_orderOf_ten hcard (by norm_num) hyP orderOf_y45 L (fun e he => ?_) hnd
    (by rw [hcard, hlen]; norm_num)
  obtain ⟨g, hg, rfl⟩ := hmem e he
  exact ⟨g, QP45_closure ▸ hg, rfl⟩

end CertificateChecks.KernelU42Ten

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.CatFactsSmall.PSp43

open CFSG.ComponentClassification.CatFactsSmall.PSp43 in
theorem certificate26121 : ∀ u y : Equiv.Perm (Fin 45), u ∈ QP45.originalSubgroup → y ∈ QP45.originalSubgroup →
    u * u = 1 → u ≠ 1 → orderOf y = 5 → u * y ≠ y * u := by
  refine fun u y hu hy hu2 hu1 hy5 hc => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have h10 : orderOf (u * y) = 10 := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hc (by rw [hu2', hy5]; norm_num), hu2', hy5]
  exact KernelU42Ten.no_ten _ (QP45.originalSubgroup.mul_mem hu hy) h10

end Certificates
