module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeSigned
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticePerm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative UCoord OrthExcEven

section FromElementLevel

theorem ggTorusLattice_of_signedEltSC {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) : GGTorusLattice p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hsc⟩ := hA
  obtain ⟨k, Θ, -, -, -, -, hnorm⟩ :=
    exists_signedModelSC hp hp2 hI hZ hcp h hψ hker hperf hAe hAI h3 hsc
  exact ggTorusLattice_of_signedModel hp hp2 Θ hnorm

theorem ggTorusLattice_of_signedElt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusSignedElt p r R) : GGTorusLattice p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, -⟩ := hA
  obtain ⟨k, Θ, -, -, -, -, hnorm⟩ :=
    exists_signedModel hp hp2 hI hZ h hψ hker hperf hAe hAI hr h3
  exact ggTorusLattice_of_signedModel hp hp2 Θ hnorm

theorem ggTorusLattice_of_evenSignedPermEltSC {p r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {kP : ℕ → Prop} (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedPermEltSC p R kP) :
    GGTorusLattice p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hsc⟩ := hA
  obtain ⟨k, Θ, -, -, -, -, -, -, hnorm⟩ :=
    exists_evenSignedPermModelSC hp hp2 hI hZ hcp h hψ hker hperf hAe hAI h3 hsc
  exact ggTorusLattice_of_signedModel hp hp2 Θ hnorm

theorem ggTorusLattice_of_permEltSC {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d)
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (h : GGTorusPermEltSC p d R) :
    GGTorusLattice p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hsc⟩ := hA
  obtain ⟨Θ, -, -, hnorm⟩ := exists_permModel hp hZ hI hcp h hψ hker hperf hAe hAI h3 hsc
  exact ggTorusLattice_of_permModel hp hp2 hpd h3 Θ hnorm

end FromElementLevel

end CFSG.StandardType
