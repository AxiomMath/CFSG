module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsLangCube
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldDescent

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem le_twMatPre_map {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAI : A ≤ twistedE6InndiagGL K σ) :
    A ≤ TwE6RootAs.twMatPre K σ
      ((A.subgroupOf (RecipeExcLang.twInndiagGroup K σ)).map (RecipeExcLang.twConj K σ)) := by
  intro x hx
  have hxΓ := twistedE6InndiagGL_le_twInndiagGroup σ (hAI hx)
  exact ⟨⟨x, hxΓ⟩, ⟨⟨x, hxΓ⟩, hx, rfl⟩, rfl⟩

theorem subfieldLangDatumThree_holds :
    SubfieldLangDatumThree := by
  intro K _ _ σ q hK hσ hchar h3 A hAI hA h5
  classical
  haveI : CharP K 2 := ringChar.of_eq hchar
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hdvd : q ∣ 2 ^ (m : ℕ) := by
    rw [← hm, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨n, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h0 => by
    subst h0
    norm_num at h3
  have hAΓ : A ≤ RecipeExcLang.twInndiagGroup K σ :=
    hAI.trans (twistedE6InndiagGL_le_twInndiagGroup σ)
  set S := (A.subgroupOf (RecipeExcLang.twInndiagGroup K σ)).map (RecipeExcLang.twConj K σ)
    with hS
  have hSel : IsElemAbelian 3 S :=
    (hA.comap (f := (RecipeExcLang.twInndiagGroup K σ).subtype)
      (Subgroup.subtype_injective _)).map _
  have hScard : Nat.card S = Nat.card A := by
    rw [hS, Subgroup.card_map_of_injective (NoOffTwE6Three.twConj_injective hn hK σ hσ)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAΓ).toEquiv
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure K) 2 n c = c ^ 2 ^ n :=
    fun c => iterateFrobenius_def 2 n c
  obtain ⟨g, hg, hgn, hSg⟩ := TwE6DD2.exists_cubeTorus_lang hn hK σ hσ h3 _ hFr hSel
    (Subgroup.map_le_range _ _) (by rw [hScard]; exact h5)
  exact ⟨(TwE6RootAs.langCubeData hn hK σ hσ _ hFr h3 hg hgn hSg).restrict
    (le_twMatPre_map σ hAI), rfl⟩

end CFSG.StandardType.TwE6FieldCore
