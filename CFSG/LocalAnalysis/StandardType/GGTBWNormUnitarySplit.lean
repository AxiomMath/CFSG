module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormSigned
public import CFSG.LocalAnalysis.StandardType.GGTwSUFacts
public import CFSG.LocalAnalysis.StandardType.GGTwSUSigned

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggTorusWNormSC_unitary_split {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 4 ≤ d)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have : CharP K 2 := charP_two_of_card (by rw [hK, ← pow_mul])
  obtain ⟨hZ, hIp, hcp⟩ := unitary_split_torus_recipe_facts hK hn hd hp hp2 hpq
  apply ggTorusWNormSC_of_outdiagPrime hIp
  exact ggTorusWNormSC_of_signedEltSC hp hp2 (fun _ h => h) hZ hcp
    (ggTorusSignedEltSC_unitary_split hK hn hd hp hp2 hpq)

theorem largeEvenLabelAll_wnorm_unitary_split {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ lab.n)
    (ht : lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) (hr : 3 ≤ lab.rank)
    (hpq : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hr hn hpq ⊢
  rcases ht with rfl | ⟨rfl, rfl⟩
  · intro Q hQ
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_unitary_split (d := r + 1) (n := n) hK hn (by omega) hp hp2 hpq
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_unitary_split (d := 4) (n := n) hK hn (by norm_num) hp hp2 hpq

end CFSG.StandardType
