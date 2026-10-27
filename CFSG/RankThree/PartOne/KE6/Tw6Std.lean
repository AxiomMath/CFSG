module

public import CFSG.RankThree.PartOne.KE6.Tw6Torus
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open scoped Matrix

theorem tw6_torusRootKernel_smul_stable {L : Type} [Field L] [IsAlgClosed L]
    {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {x : ModGL Tag.E6 L}
    (hx : x ∈ twistedTorusOf (tw6N L) (twistE6 L Fr)) :
    ∀ α ∈ torusRootKernel x, e6T3W • α ∈ torusRootKernel x := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hx).1
  have hbker : b ∈ (monomialHom (G := Lˣ) (tw6Matrix q)ᵀ).ker :=
    (mem_twistedTorus_rootDiagUnit_iff6 hFr b).1 (by rw [← hb]; exact hx)
  intro α hα
  rw [hb, torusRootKernel_rootDiagUnit] at hα ⊢
  refine ⟨IsRoot.smul hα.1 e6T3W, ?_⟩
  have h := (mem_ker_monomialHom_iff_forall (tw6Matrix q) b).1 hbker α
  rw [rootChar_tw6Matrix_mulVec, hα.2, one_pow, mul_one] at h
  exact h

end CFSG.RankThree.PartOne.KE6
