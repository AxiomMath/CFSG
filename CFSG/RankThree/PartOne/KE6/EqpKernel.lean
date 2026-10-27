module

public import CFSG.RankThree.PartOne.KE6.Phi3Kernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise

structure EqpKernelLayer
    {Ω : Type} [Field Ω] (n : ModGL Tag.E6 Ω) (Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (S : Set (Fin Tag.E6.rank → ℤ)) (K : Type) [Field K] [Algebra K Ω] (ι' : Type) where
  P : ι' → Subgroup (ModGL Tag.E6 Ω)
  fin : ∀ i, Finite (P i)
  quasi : ∀ i, CFSG.IsQuasisimple (P i)
  le_span : ∀ i, P i ≤ rootSpan Tag.E6 Ω S
  le_fixed : ∀ i, P i ≤ twistedFixedPoints n Φ
  norm : ∀ i, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S, y ∈ twistedFixedPoints n Φ →
    ∀ u ∈ P i, y * u * y⁻¹ ∈ P i
  cent : ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S, (∀ i, ∀ u ∈ P i, y * u = u * y) →
    y ∈ torusGroup Tag.E6 Ω ∧ y ∈ Subgroup.centralizer (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω))
  comm : ∀ X : Module.End Ω (RootModule Tag.E6 Ω),
    (∀ i, ∀ u ∈ P i, Commute X (u : Module.End Ω (RootModule Tag.E6 Ω))) →
      ∀ g ∈ rootSpan Tag.E6 Ω S, Commute X (g : Module.End Ω (RootModule Tag.E6 Ω))
  sl2 : (∃ α ∈ S, permLattice e6Rho α = α) →
    ∃ (i₀ : ι') (m : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 Ω), ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω m (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * h₀⁻¹ ∈
        P i₀

variable {Ω : Type} [Field Ω]

def EqpKernelLayer.ofFamily {n : ModGL Tag.E6 Ω}
    {Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω} {S : Set (Fin Tag.E6.rank → ℤ)} {K : Type} [Field K]
    [Algebra K Ω] {ι' : Type} (P : ι' → Subgroup (ModGL Tag.E6 Ω))
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α) {w : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)}
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω J)
    (hfin : ∀ i, Finite (P i)) (hq : ∀ i, CFSG.IsQuasisimple (P i))
    (hspan : ∀ i, P i ≤ rootSpan Tag.E6 Ω S) (hfix : ∀ i, P i ≤ twistedFixedPoints n Φ)
    (hnorm : ∀ i, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S, y ∈ twistedFixedPoints n Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hcomm : e6Commutant (((⨆ i, P i).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom : Subgroup
          (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)))
    (hsl2 : (∃ α ∈ S, permLattice e6Rho α = α) →
      ∃ (i₀ : ι') (m : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 Ω), ∀ B : SL(2, K),
        h₀ * simpleRootSL2 Tag.E6 Ω m (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * h₀⁻¹ ∈
          P i₀) :
    EqpKernelLayer n Φ S K ι' where
  P := P
  fin := hfin
  quasi := hq
  le_span := hspan
  le_fixed := hfix
  norm := hnorm
  cent := fun y hy hc => hPcent_of_std hS hQ hcomm y hy (fun u hu => by
    have hle : (⨆ i, P i) ≤ Subgroup.centralizer ({y} : Set (ModGL Tag.E6 Ω)) :=
      iSup_le fun i u' hu' => Subgroup.mem_centralizer_singleton_iff.2 (hc i u' hu').symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hu)).symm)
  comm := fun X hX g hg => by
    have hP := e6Commutant_eq_of_conj_commutant hQ hcomm
    have hX' : X ∈ e6Commutant (((⨆ i, P i : Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))) := by
      rw [CFSG.RankThree.Lattice.e6Commutant_iSup, Set.mem_iInter]
      exact fun i u hu => hX i u hu
    rw [hP] at hX'
    exact hX' g hg
  sl2 := hsl2

end CFSG.RankThree.PartOne.KE6
