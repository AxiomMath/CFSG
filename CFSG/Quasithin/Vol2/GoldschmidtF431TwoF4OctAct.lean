module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctConj
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSpec

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem octAct₁ : OctAct₁ K a := by
  have hw : F4.fixedOrbitElement (⟨1, by decide⟩ : Fin F4.fixedOrbitCount) ∈ F4.relWeylRee :=
    fixedOrbitElement_mem _
  have hn : ((octR1 K a : Gm K a) : ModGL F4.tag K) = canonicalRep (coxeterSystem F4.tag) K
      (F4.fixedOrbitElement (⟨1, by decide⟩ : Fin F4.fixedOrbitCount)) := rfl
  have key : ∀ k ∈ octKeys, CFSG.GH74.BNPair.conjBy (octR1 K a)⁻¹ (octRoot K a k) =
      octRoot K a (octSig₁ k) := fun k hk =>
    conjBy_octRoot hw hn hk (image_smul_octBlock (octL_z₂ k hk))
  refine ⟨?_, ?_, fun i h2 h8 => ⟨?_, ?_⟩⟩
  · simpa [octSig₁] using key 1 (octKeys_of_pos le_rfl (by norm_num))
  · simpa [octSig₁] using key (-1) (octKeys_of_neg le_rfl (by norm_num))
  · rw [key i (octKeys_of_pos (by omega) h8), octSig₁_pos h2]
    congr 1
  · rw [key (-i) (octKeys_of_neg (by omega) h8), octSig₁_neg h2]
    congr 1

theorem octAct₂ : OctAct₂ K a := by
  have hw : F4.fixedOrbitElement (⟨0, by decide⟩ : Fin F4.fixedOrbitCount) ∈ F4.relWeylRee :=
    fixedOrbitElement_mem _
  have hn : ((octR2 K a : Gm K a) : ModGL F4.tag K) = canonicalRep (coxeterSystem F4.tag) K
      (F4.fixedOrbitElement (⟨0, by decide⟩ : Fin F4.fixedOrbitCount)) := rfl
  have key : ∀ k ∈ octKeys, CFSG.GH74.BNPair.conjBy (octR2 K a)⁻¹ (octRoot K a k) =
      octRoot K a (octSig₂ k) := fun k hk =>
    conjBy_octRoot hw hn hk (image_smul_octBlock (octL_z₁ k hk))
  refine ⟨?_, ?_, fun i h1 h7 => ⟨?_, ?_⟩⟩
  · simpa [octSig₂] using key 8 (octKeys_of_pos (by norm_num) le_rfl)
  · simpa [octSig₂] using key (-8) (octKeys_of_neg (by norm_num) le_rfl)
  · have h7' : i ≤ 7 := by push_cast at h7; omega
    rw [key i (octKeys_of_pos h1 (by omega)), octSig₂_pos h7' h1]
    congr 1
  · have h7' : i ≤ 7 := by push_cast at h7; omega
    rw [key (-i) (octKeys_of_neg h1 (by omega)), octSig₂_neg h7' h1]
    congr 1

end CFSG.Quasithin.H13.F431.TwoF4
