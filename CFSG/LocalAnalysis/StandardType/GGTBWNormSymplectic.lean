module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormSigned
public import CFSG.LocalAnalysis.StandardType.GGKGARank
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem SpModel.ggTorusSignedEltSC_sp {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [NeZero m] (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusSignedEltSC p (LargeEvenProj (LargeEvenSpGroup K m)) := by
  intro E hE h3 hsc
  exact SpModel.ggTorusSignedElt_sp hp hp2 hpq E hE
    (KGA.kga_selfCent_split hp hp2 hpq hE hsc) h3


theorem ggTorusWNormSC_symplectic {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  have hT : GGTorusSignedEltSC p (LargeEvenProj (LargeEvenSpGroup K m)) := by
    rcases hpq with hs | hn
    · exact SpModel.ggTorusSignedEltSC_sp hp hp2 hs
    · exact ggSpNonsplitSignedEltInput_holds K m p (by omega) hp hn
  exact ggTorusWNormSC_of_signedEltSC hp hp2 TableBSymp.sp_I_subset_inn
    TableBSymp.center_spProj_eq_bot (ggCenterPrime_sp hp hp2) hT

theorem largeEvenLabelAll_wnorm_symplectic {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hr : 3 ≤ lab.rank) (hpq : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, m, n⟩
  dsimp only at htag hr hpq ⊢
  rcases htag with rfl | rfl
  · intro Q hQ
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_symplectic hr hp hp2 (by rwa [hK])
  · intro Q hQ
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_symplectic hr hp hp2 (by rwa [hK])

end CFSG.StandardType
