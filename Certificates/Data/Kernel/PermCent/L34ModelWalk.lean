module

public import Certificates.Data.Kernel.PermCent.L34ModelTwin
public import Certificates.Data.Kernel.PermCent.FlagWalkC

public section

namespace CFSG.Certificates.Kernel.PkCV.L34Mod

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkEnum

@[expose] noncomputable def levA : List (List (CV 42)) :=
  (List.finRange QA.baseCount).map fun i => (transV (levelV (strongV QA) QA.base i)).map toCV

theorem elemsC_QA : elemsC QA = productsC levA := rfl

@[expose] def mskA : List Nat :=
  [4104843689982, 1834945085408, 1834891641856, 692430341120, 940606464, 269484032]

@[expose] noncomputable def bodyC (LP S G : List (CV 42)) (g : CV 42) : Bool :=
  (!(G.all fun s => eq22C g s s g) || decide (g ∈ S)) &&
    (!powOneC g 2 || siftC QP g 0 ||
      !(G.all fun s => decide (g * s * g⁻¹ ∈ S)) ||
      !decide (9 ∣ (LP.filter fun h => eq22C h g g h).length) ||
      gA.all fun a => siftC QP (a * g * a⁻¹ * g⁻¹) 0)

theorem modelC_eq (LA LP S G : List (CV 42)) : modelC LA LP S G = LA.all (bodyC LP S G) := rfl

theorem body_of_not (LP S G : List (CV 42)) (g : CV 42)
    (hGS : (G.all fun s => decide (s ∈ S)) = true)
    (hn : (G.all fun s => decide (g * s * g⁻¹ ∈ S)) = false) : bodyC LP S G g = true := by
  have hc : (G.all fun s => eq22C g s s g) = false := by
    cases h : (G.all fun s => eq22C g s s g)
    · rfl
    · exfalso
      have hN : (G.all fun s => decide (g * s * g⁻¹ ∈ S)) = true := List.all_eq_true.2 fun s hs => by
        have e := List.all_eq_true.1 h s hs
        rw [eq22C_eq, decide_eq_true_iff] at e
        rw [e, mul_inv_cancel_right]
        exact List.all_eq_true.1 hGS s hs
      rw [hn] at hN
      exact Bool.false_ne_true hN
  unfold bodyC
  rw [hc, hn]
  simp only [Bool.not_false, Bool.or_true, Bool.true_or, Bool.and_true]

end CFSG.Certificates.Kernel.PkCV.L34Mod

end
