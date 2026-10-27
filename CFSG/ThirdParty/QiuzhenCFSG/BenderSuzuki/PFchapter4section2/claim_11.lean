module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

/-! # Peterfalvi, Part II, Chapter IV, Section 2, equation (11) -/

/--
The three sequences introduced in Peterfalvi IV.2(11), with their initial
values and conditional recursion.  The source stops the recursion at the
first index for which `u i = alpha`; total functions encode this by imposing
the recursion only while `u i ≠ alpha`.
-/
public theorem claim_11
    (E : Type*) [Field E] (zeta alpha : E) (sigma tau : E → E) :
    ∃ u v d : ℕ → E,
      u 1 = 0 ∧ v 1 = alpha ∧ d 1 = zeta ∧
      (∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹) ∧
      (∀ i : ℕ, u i ≠ alpha →
        v (i + 1) = v i + u (i + 1) * (d i * sigma (d i))⁻¹) ∧
      (∀ i : ℕ, u i ≠ alpha →
        d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2)) := by
  classical
  let u : ℕ → E := Nat.rec (motive := fun _ => E) alpha fun i ui =>
    if i = 0 then 0 else if ui = alpha then alpha else (alpha + ui)⁻¹
  let d : ℕ → E := Nat.rec (motive := fun _ => E) zeta fun i di =>
    if i = 0 then zeta
    else if u i = alpha then di else di * zeta * tau ((u (i + 1))⁻¹ ^ 2)
  let v : ℕ → E := Nat.rec (motive := fun _ => E) alpha fun i vi =>
    if i = 0 then alpha
    else if u i = alpha then vi else vi + u (i + 1) * (d i * sigma (d i))⁻¹
  refine ⟨u, v, d, by simp [u], by simp [v], by simp [d], ?_, ?_, ?_⟩
  · intro i hui
    cases i with
    | zero => simp [u] at hui
    | succ i => simp [u, hui]
  · intro i hui
    cases i with
    | zero => simp [u] at hui
    | succ i => simp [v, hui]
  · intro i hui
    cases i with
    | zero => simp [u] at hui
    | succ i => simp [d, hui]

end PFchapter4section2
end CFSG.BenderSuzuki
