
module

public import Certificates.Certificate4008Base2
import all Certificates.Certificate4008Base
import all Certificates.Certificate4008Base1
import all Certificates.Certificate4008Base2

public import CFSG.Sporadic.J4.QT2LocPath
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.J4.Action
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.HOrder
import CFSG.Sporadic.Schreier.J4SNative
import CFSG.Sporadic.Schreier.J4SCols
import CFSG.Sporadic.Schreier.J4SFormData
import CFSG.Sporadic.Schreier.J4SNoCompData
meta import CFSG.Sporadic.Schreier.J4SNoCompData
import CFSG.Sporadic.Schreier.J4SOrbits
meta import CFSG.Sporadic.Schreier.J4SOrbits
import CFSG.Sporadic.J4.QT2LocX0KNative
import CFSG.Sporadic.J4.QTNative
import CFSG.Sporadic.J4.QT2LocX0CheckInputs

public section

namespace Certificates

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.GLQ CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.Native CertificateChecks.KernelJ4Count

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2
open CFSG.Sporadic.J4.Native

open CFSG.Sporadic.GLQ CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.Native CertificateChecks.KernelJ4Count

private theorem orbit_H_eq_Hj (x : Row) : orbit H x = orbit Hj x := by
  ext y
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨⟨g, H_eq_Hj' ▸ hg⟩, rfl⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨⟨g, H_eq_Hj'.symm ▸ hg⟩, rfl⟩


open CFSG.Sporadic.GLQ CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.Native CertificateChecks.KernelJ4Count

private theorem pathElt_eq_signedWord4008 : ∀ p : List ℕ, (∀ l ∈ p, l = 1 ∨ l = 2) →
    pathElt p = signedWord a b (p.map Int.ofNat)
  | [], _ => rfl
  | l :: ls, h => by
    have ih := pathElt_eq_signedWord4008 ls fun x hx => h x (List.mem_cons_of_mem _ hx)
    unfold signedWord at ih ⊢
    rw [pathElt, ih, List.map_cons, List.map_cons, List.prod_cons]
    congr 1
    rcases h l List.mem_cons_self with rfl | rfl
    · simp [letterElt, letter]
    · simp [letterElt, letter]


open CFSG.Sporadic.GLQ CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.Native CertificateChecks.KernelJ4Count

private theorem inv_pathElt_smul_root {l : ℕ} (hl : l < 7) :
    (pathElt (repPaths.getD l []))⁻¹ • toRow rootV.toVec = qv l := by
  have e : pathElt (repPaths.getD l []) = mRep l := by
    rw [pathElt_eq_signedWord4008 _ (repPaths_letters l hl), mRep]
    congr 1
    interval_cases l <;> rfl
  rw [e, qv_eq hl, v_eq_root]

theorem certificate4008 : (∀ g : CFSG.Sporadic.J4.J, ∃ ℓ < 7, ∃ h ∈ Hj, ∃ h' ∈ Hj,
      g = h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') ∧
    ∀ ℓ < 7,
      (MulAction.orbit Hj ((pathElt (repPaths.getD ℓ []))⁻¹ • toRow rootV.toVec)).ncard =
        [1, 32643072, 82575360, 54405120, 3400320, 15180, 28336].getD ℓ 0 := by
    refine ⟨fun g => ?_, fun l hl => ?_⟩
    · obtain ⟨l, hl, ⟨h, hh⟩, e⟩ := cover_qv (w := g • v) ⟨g, rfl⟩
      change h • qv l = g • v at e
      have hhj : h ∈ Hj := by rw [← H_eq_Hj']; exact hh
      have e3 : g • v = (h * (pathElt (repPaths.getD l []))⁻¹) • v := by
        rw [mul_smul, ← e, v_eq_root, inv_pathElt_smul_root hl]
      have e2 : (h * (pathElt (repPaths.getD l []))⁻¹)⁻¹ * g ∈ Hj := by
        rw [← stabilizer_v_eq_Hj', mem_stabilizer_iff, mul_smul, e3, ← mul_smul, inv_mul_cancel,
          one_smul]
      exact ⟨l, hl, h, hhj, _, e2, by group⟩
    · rw [inv_pathElt_smul_root hl, ← orbit_H_eq_Hj, FixCE.hsz l hl]
      rfl


end Certificates
