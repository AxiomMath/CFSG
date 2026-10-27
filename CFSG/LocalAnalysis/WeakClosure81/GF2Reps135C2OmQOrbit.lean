module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusOrbit
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQOrbitNat
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQOrbitExt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open CFSG.StandardType

theorem exists_four_orbit_omPlus_of_node {n : ℕ} (hn : 5 ≤ n) {j : Fin n} (hj : j.val ≠ 0)
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : OmRealizes n x π s) (hs : SpIsSign s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) :
    ∃ v : Fin n → ℤ,
      (∀ k : Fin n, k ≠ j →
        weylAction (isFiniteType_cartanD n)
          ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k) v = v) ∧
      ∃ u : Fin 4 → Fin n → ℤ,
        (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD n) w v) ∧
        Function.Injective u ∧ ∀ i l, u i ≠ weylAction (isFiniteType_cartanD n) x (u l) := by
  by_cases hj3 : j.val + 3 ≤ n
  · refine ⟨omExtWt n j.val, fun k hk => weylAction_simple_omExtWt (by omega) hj3
      (fun h => hk (Fin.ext h)), ?_⟩
    exact exists_four_orbit_omExtWt hn (by omega) hj3 hxr hs hx
  · refine ⟨omHalfSpin2 n j, fun k hk => weylAction_simple_omHalfSpin2 (by omega) (by omega)
      hk, ?_⟩
    exact exists_four_orbit_omHalfSpin2 hn (by omega) hxr hs hx

end CFSG.LocalAnalysis.WeakClosure81
