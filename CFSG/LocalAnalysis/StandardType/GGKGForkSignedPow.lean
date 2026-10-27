module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLattice

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusLattice_of_innerPow {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (h : GGTorusLattice p r R (Set.range (MulAut.conj : R →* MulAut R))) :
    GGTorusLattice p r R I := by
  intro L' _ _ ψ A hA
  refine h L' ψ A
    ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, ?_,
      hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2⟩
  intro a ha
  obtain ⟨φ, hφI, hφ⟩ := hA.2.2.2.2.1 a ha
  refine ⟨φ, hIp φ hφI ?_, hφ⟩
  have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; simp
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
  refine MulEquiv.ext fun r => ?_
  obtain ⟨l, rfl⟩ := hA.1 r
  rw [hk, hA.2.2.2.1.2 a ha]
  rfl

theorem ggTorusLattice_of_signedEltSC_pow {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) :
    GGTorusLattice p r R I :=
  ggTorusLattice_of_innerPow hIp (ggTorusLattice_of_signedEltSC hp hp2 (fun _ h => h) hZ hcp h)

theorem ggTorusLattice_of_signedElt_pow {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : GGTorusSignedElt p r R) : GGTorusLattice p r R I :=
  ggTorusLattice_of_innerPow hIp (ggTorusLattice_of_signedElt hp hp2 (fun _ h => h) hZ h)

end CFSG.StandardType
