module

public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Vol2.Ch3Sec1Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBc12

variable {G : Type} [Group G] [Finite G] {T Mc M H : Subgroup G}

theorem hypE28_of_hstar (hs : Setting152 T Mc M) (h19 : Lemma1519Concl T Mc M)
    (hH : IsHStar T M H) (hV : ¬ V154 T Mc M ≤ pCoreOf 2 H) :
    HypE28 H T (H ⊓ M) (V154 T Mc M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  have hTM : T ≤ M := hs.mf.1.1.2
  have hVT : V154 T Mc M ≤ T := S152N.V154_le_T hs
  have hNV : Subgroup.normalizer (V154 T Mc M : Set G) = M := S152N.normalizer_V154_eq hs
  have hel : IsElemAbelian 2 (V154 T Mc M) := S152N.isElemAbelian_V154 hs
  have hp2 : IsPGroup 2 (V154 T Mc M) := B2F.isPGroup_of_isElemAbelian hel
  have hmin : MinParabolic H T (H ⊓ M) := by
    let S : Sylow 2 G := hs.qtfe.sylow.1.toSylow hs.qtfe.sylow.2
    exact ⟨S152N.isSylowTwoOf_hStar hs hH, hH.not_le_normalizer h19.seven_normalizer,
      IsHStar.isUniqueMaxOver S hH hTM⟩
  refine ⟨hmin, isSQTKSub_of_inH hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian hH.1, hel, hVT,
    by rw [hNV]; exact hTM, ?_, ?_⟩
  · exact le_pCoreOf_of_le_normalizer 2 (le_inf (hVT.trans hTH) (hVT.trans hTM))
      (by rw [hNV]; exact inf_le_right) hp2
  · intro hker
    exact hV (hmin.le_pCoreOf_of_isPGroup_of_le_kerIn hp2 hker)

theorem isTISetIn_of_hstar (hs : Setting152 T Mc M) (hH : IsHStar T M H) :
    IsTISetIn (V154 T Mc M) (H ⊓ M) := by
  have hTM : T ≤ M := hs.mf.1.1.2
  have hVT : V154 T Mc M ≤ T := S152N.V154_le_T hs
  have hNV : Subgroup.normalizer (V154 T Mc M : Set G) = M := S152N.normalizer_V154_eq hs
  refine ⟨le_inf (hVT.trans hH.1.1) (hVT.trans hTM), fun g hg hgn => ?_⟩
  exact absurd (by rw [hNV]; exact hg.2) hgn

end SBc12

end CFSG.Quasithin
