module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormSigned
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinNs
public import CFSG.LocalAnalysis.StandardType.GGK1ScLin
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggTorusWNormSC_linear_nonsplit {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hd : 4 ≤ d)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) := by
  have : CharP K 2 := charP_two_of_card hK
  have hminus : ¬ p ∣ Nat.card K - 1 :=
    SpNS.not_dvd_card_sub_one hp hp2 (by rwa [hK])
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) = ⊥ := by
    have h := Subgroup.map_center_eq (TypeA.recipeEquiv d K)
    rw [SlNsRootGen.center_projectiveSL_eq_bot_charTwo] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (TypeA.recipeEquiv d K).injective).mp h
  apply ggTorusWNormSC_of_outdiagPrime (NbrInnerMore.ggOutdiagPrime_linear hp hminus (by omega))
  exact ggTorusWNormSC_of_signedEltSC hp hp2 (fun _ h => h) hZ
    (ggCenterPrime_linear_gcd (by omega) hp hp2 (fun h => hminus h.2))
    (ggTorusSignedEltSC_linear_nonsplit hK hn (by omega) hp hp2 hpq)

theorem largeEvenLabelAll_wnorm_linear_nonsplit {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ lab.n)
    (htag : lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) (hr : 3 ≤ lab.rank)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at htag hr hn hpq ⊢
  rcases htag with rfl | ⟨rfl, rfl⟩
  · intro Q hQ
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_linear_nonsplit (d := r + 1) (n := n) hK hn (by omega) hp hp2 hpq
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_linear_nonsplit (d := 4) (n := n) hK hn (by norm_num) hp hp2 hpq

end CFSG.StandardType
