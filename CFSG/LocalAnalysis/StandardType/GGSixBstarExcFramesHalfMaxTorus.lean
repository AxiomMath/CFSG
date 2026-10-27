module

public import CFSG.LieType.SeitzGeneration.ExcTorusUntw
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped Matrix

section Torus


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

theorem twistedTorus_eq_map_fixedCharTuples (w : WeylGroup τ) (Fr : L →+* L) :
    twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr =
      (fixedCharTuples (weylMatrix w) Fr).map (rootDiagUnitHom τ L) := by
  have hw : ∀ u, w • u = (weylMatrix w) *ᵥ u := fun u => (weylMatrix_mulVec w u).symm
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
    refine ⟨a, ?_, rfl⟩
    rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
    exact mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2
  · rintro ⟨a, ha, rfl⟩
    rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr] at ha
    exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a, mem_twistedFixedTuples_iff_conj.1 ha⟩

theorem isMulCommutative_twistedTorus (w : WeylGroup τ) (Fr : L →+* L) :
    IsMulCommutative (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr) := by
  rw [twistedTorus_eq_map_fixedCharTuples]
  exact isMulCommutative_map _ inferInstance

theorem exists_tuple_of_mem_twistedTorus (w : WeylGroup τ) (Fr : L →+* L) {p : ℕ}
    {x : ModGL τ L} (hx : x ∈ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr)
    (hxp : x ^ p = 1) :
    ∃ a ∈ fixedCharTuples (weylMatrix w) Fr, (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a = x := by
  rw [twistedTorus_eq_map_fixedCharTuples] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ha, ?_, rfl⟩
  have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
    have : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
      ((rootDiagUnitHom τ L).map_pow a p)
    rw [this, rootDiagUnit_one]
    exact hxp
  have h2 : a ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
  exact fun i => congrFun h2 i

theorem natCard_twistedTorus_pTorsion {ℓ q p : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ q) (hp : p.Prime) (hpℓ : p ≠ ℓ) (w : WeylGroup τ) :
    Nat.card {x : ModGL τ L //
      x ∈ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr ∧ x ^ p = 1} =
    Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (q : ZMod p) • z} := by
  have hT0 := twistedTorus_eq_map_fixedCharTuples w Fr
  have hcomm := isMulCommutative_twistedTorus w Fr
  have h1 := natCard_torsion_eq (fixedCharTuples (weylMatrix w) Fr)
    (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr) hT0 hcomm p
  rw [natCard_fixedTorsion (weylMatrix w) Fr hℓ hFr hp hpℓ] at h1
  rw [← h1]
  exact Nat.card_congr (Equiv.refl _)

end Torus

end ExcFramesHalf

end CFSG.StandardType
