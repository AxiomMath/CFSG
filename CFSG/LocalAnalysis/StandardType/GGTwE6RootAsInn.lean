module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsEndAut
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGIOneExcTwE6
import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsLangCube
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldLangThree
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestDefs

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TwE6RootKill


theorem ringChar_eq_two_of_card_sq {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) : ringChar K = 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  refine FiniteField.even_card_iff_char_two.2 ?_
  rw [← Nat.card_eq_fintype_card, hK]
  exact Nat.even_iff.1 (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, two_ne_zero⟩)

theorem exists_twLangData_three {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAI : A ≤ twistedE6InndiagGL K σ) (hA : IsElemAbelian 3 A) (h5 : 3 ^ 5 ≤ Nat.card A) :
    ∃ D : TwLangData K σ (2 ^ n) A, D.c = 1 ∧
      ∀ γ, D.v • permLattice TwistTag.E6.perm γ = -γ := by
  classical
  haveI : CharP K 2 := ringChar.of_eq (ringChar_eq_two_of_card_sq hn hK)
  have hAΓ : A ≤ RecipeExcLang.twInndiagGroup K σ :=
    (TwE6FieldCore.le_twMatPre_map σ hAI).trans (Subgroup.map_subtype_le _)
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
  exact ⟨(langCubeData hn hK σ hσ _ hFr h3 hg hgn hSg).restrict
    (TwE6FieldCore.le_twMatPre_map σ hAI), rfl, langCubeData_v hn hK σ hσ _ hFr h3 hg hgn hSg⟩

theorem ggTwE6RootAsInnThreeInput_of_core (hRK : RootKill) (hCore : TwE6CorootCore) :
    GGTwE6RootAsInnThreeInput := by
  intro K _ _ n hn hK h3
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj hn hK
  haveI := TwE6Delta.finite_recipeR hK
  haveI : Finite (MulAut (TwE6Delta.RecipeR K n)) :=
    Finite.of_injective (fun φ : MulAut (TwE6Delta.RecipeR K n) => (φ : _ → _))
      fun φ ψ h => MulEquiv.ext (congrFun h)
  refine ggEndNodeRootAsInn_of_self (TwE6Delta.center_recipeR_eq_bot hn hK)
    (ggEndNodeRootAsSelf_of_datum hRK hCore hn hK hσ ε Nat.prime_three h3 hε ?_)
  intro A As hA hAAs hAs hAsI hr
  have hAsr : As ≤ (TwE6Transport.recipeConj σ ε).range := fun φ hφ => (hε φ).2 (hAsI hφ)
  have hlt := CFSG.StandardType.mul_card_le_card_of_lt Nat.prime_three hAs hAAs
  have h5 : 3 ^ 5 ≤ Nat.card As := by
    norm_num at hr ⊢
    omega
  obtain ⟨D, hc, hv⟩ := exists_twLangData_three hn hK σ hσ h3 (TwE6Transport.recipeMat_le σ ε As)
    (TwE6Transport.isElemAbelian_recipeMat σ ε hn hK hσ hAs)
    (by rw [TwE6Transport.card_recipeMat σ ε hn hK hσ hAsr]; exact h5)
  exact ⟨D.restrict (TwE6Transport.recipeMat_mono σ ε hAAs.le), hc, hv⟩

theorem ggTwE6RootAsInnInput_of_core (hRK : RootKill) (hCore : TwE6CorootCore)
    (hDat : TwE6FieldCore.SubfieldLangDatumFive) : GGTwE6RootAsInnInput := by
  intro K _ _ n p hn hK hp hpn hp3
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj hn hK
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega : n ≠ 0))).mp hpn
    omega
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    have := hp.two_le
    omega
  refine ggEndNodeRootAsInn_of_self (TwE6Delta.center_recipeR_eq_bot hn hK)
    (ggEndNodeRootAsSelf_of_datum hRK hCore hn hK hσ ε hp hpn hε ?_)
  intro A As hA hAAs _ hAsI hr
  have hAr : A ≤ (TwE6Transport.recipeConj σ ε).range := fun φ hφ =>
    (hε φ).2 (hAsI (hAAs.le hφ))
  rw [if_neg hp3] at hr
  exact hDat K σ (2 ^ n) hK hσ p hp hp5 hpn _ (TwE6Transport.recipeMat_le σ ε A)
    (TwE6Transport.isElemAbelian_recipeMat σ ε hn hK hσ hA)
    (by
      rw [TwE6Transport.card_recipeMat σ ε hn hK hσ hAr]
      exact (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hr)

end CFSG.StandardType.TwE6RootAs

end
