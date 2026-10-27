module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameBasisFrame
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeter

public section

namespace CFSG.StandardType.SpFrame

open Module CFSG.LieType.Universal CFSG.LieType.RootSystem CoxeterSystem
  CFSG.LieType.Universal.Symplectic

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem exists_frame [FiniteDimensional k V] (h2 : (2 : k) ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (hdim : finrank k V = m + 1)
    (ρ : (coxeterMatrix (isFiniteType_cartanC (m + 1))).Group →* Module.End k V)
    (hρ : Function.Injective ρ)
    (hrefl : ∀ i, IsRefl
      (ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i))) :
    ∃ f : Basis (Fin (m + 1)) k V,
      (∀ (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) (j : Fin (m + 1)),
        ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) (f j) =
          f (Equiv.swap i ⟨i.val + 1, hi⟩ j)) ∧
      (∀ j : Fin (m + 1),
        ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple (Fin.last m))
            (f j) = if j = Fin.last m then -f j else f j) := by
  obtain ⟨εW, hεW, hlast, hcommW, hneW, hconjW, hTneW⟩ := exists_sign_family m hm
  obtain ⟨f, hfT, hfε⟩ := exists_frame_of_family h2 hdim
    (T := fun i => ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i))
    (ε := fun j => ρ (εW j))
    (fun i _ => hrefl i)
    (by show IsRefl (ρ (εW (Fin.last m))); rw [hlast]; exact hrefl (Fin.last m))
    (fun i j => by rw [← map_mul ρ, ← map_mul ρ, hcommW i j])
    (fun i j hij h => hneW i j hij (hρ h))
    (fun i hi j => by rw [← map_mul ρ, ← map_mul ρ, hconjW i hi j])
    (fun i hi j h => hTneW i hi j (hρ h))
  refine ⟨f, ?_, ?_⟩
  · intro i hi j
    exact hfT i hi j
  · intro j
    rw [← hlast]
    exact hfε j

end CFSG.StandardType.SpFrame
