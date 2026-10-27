module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E6ThreeModel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CenterE6Model
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TwE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E8
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelRecipeID
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructE6Diag
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldFixed
public import CFSG.GroupTheory.IsComponentOfMap

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType CFSG.StandardType.S2MathAs51642Interfaces
open CFSG.StandardType.TableB CFSG.StandardType.TableBExc.E6Three
open CFSG.HardMathSupport.Timmesfeld.CrossChar

section Certificates


theorem q1RToral_centerPrimeE6TwE6 :
    Q1RToralTransfer (fun _ _ _ => True)
      (fun p lab => CenterPrimeTo p lab ∧ (lab.tag = .E6 ∨ lab.tag = .twE6))
      (fun _ _ _ => True) := by
  intro p hp hp2 lab hlab hS
  obtain ⟨t, l, n⟩ := lab
  dsimp only [CenterPrimeTo, SmallDerived] at hS
  obtain ⟨⟨hsmall, hcond⟩, htag⟩ := hS
  rcases htag with hE | hT
  ·
    subst t
    have hcondE : ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1) := by
      simpa [CenterPrimeTo, SmallDerived] using hcond
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKfield, hKfinite, hK, hQ⟩ := hQ
    let R : Type := LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)
    let I : Set (MulAut R) := TableBExc.RecipeID .E6 K
    let F : Set (MulAut R) := LargeEvenChevFieldImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false)
    have hQ' : Q R I F := hQ
    refine ⟨K, hKfield, hKfinite, hK, hQ', ?_⟩
    intro A hA hAI hTor u hu horder J hJ
    have : CharP K 2 := charP_two_of_card hK
    have hsh : ¬ (p = 3 ∧ 3 ∣ Nat.card K - 1) := by
      rw [hK]
      exact hcondE
    let e : R ≃* adjointGroup .E6 K := TableBExc.recipeEquiv .E6 K
    let A' : Subgroup (MulAut (adjointGroup .E6 K)) :=
      A.map (MulAut.congr e).toMonoidHom
    have hA' : CFSG.Open.IsElemAbelian p A' :=
      CFSG.Open.IsElemAbelian.map hA (MulAut.congr e).toMonoidHom
    have hA'le : A' ≤ (hatAut .E6 K).range := by
      rintro z hz
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
      exact (E6ThreeModel.recipeID_iff_hatAut a).1 (hAI a ha)
    have hu1 : u ≠ 1 := by
      intro h
      exact hp.ne_one (by simpa [h] using horder.symm)
    have hu' : MulAut.congr e u ∈ A' := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have hu'1 : MulAut.congr e u ≠ 1 := by
      intro h
      have h' : (MulAut.congr e) u = (MulAut.congr e) 1 := by
        rw [h, map_one]
      exact hu1 ((MulAut.congr e).injective h')
    let J' : Subgroup (adjointGroup .E6 K) := J.map e.toMonoidHom
    have hJ' : CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup (MulAut.congr e u)) := by
      have hmap := CFSG.isComponentOf_map_mulEquiv e hJ
      rw [← gdf_fixed_congr e u] at hmap
      exact hmap
    obtain ⟨hInv', hmark'⟩ :=
      Q1CenterE6Model.q1CenterE6Model_split_holds hp hp2 hsh hA' hA'le hu' hu'1
        (CFSG.Assembly.isComponentOf_iff_open.2 hJ')
    have hres := Q1E6ThreeModel.componentMarking_congr_equiv e ⟨hInv', hmark'⟩
    exact CFSG.StandardType.largeEvenMarking_mono
      (fun lab R _ I F θ hh => ⟨trivial, hres.1, hh⟩) hres.2
  ·
    subst t
    have hcondT : ¬ (p = 3 ∧ 3 ∣ 2 ^ n + 1) := by
      simpa [CenterPrimeTo, SmallDerived] using hcond
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKfield, hKfinite, hK, hQ⟩ := hQ
    let R : Type := TwE6Delta.RecipeR K n
    let I : Set (MulAut R) := TwE6Delta.RecipeI K n
    let F : Set (MulAut R) := LargeEvenChevFieldImage (LargeEvenCartanE 6) K
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)
    have hQ' : Q R I F := hQ
    refine ⟨K, hKfield, hKfinite, hK, hQ', ?_⟩
    intro A hA hAI hTor u hu horder J hJ
    have : CharP K 2 :=
      charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
    have hn : 1 ≤ n := hlab.1
    have hsh : ¬ (p = 3 ∧ 3 ∣ 2 ^ n + 1) := hcondT
    let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
    have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobeniusEquiv_def K 2 n c
    obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
    let e : R ≃* twistedE6RootGroup K σ := ε.symm
    let A' : Subgroup (MulAut (twistedE6RootGroup K σ)) :=
      A.map (MulAut.congr e).toMonoidHom
    have hA' : CFSG.Open.IsElemAbelian p A' :=
      CFSG.Open.IsElemAbelian.map hA (MulAut.congr e).toMonoidHom
    have hA'le : A' ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rintro b hb
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      have hcomp : MulAut.congr ε (MulAut.congr ε.symm a) = a := by
        apply MulEquiv.ext
        intro z
        change ε (ε.symm (a (ε (ε.symm z)))) = a z
        simp only [MulEquiv.apply_symm_apply]
      have hφe : MulAut.congr e a ∈ (RecipeExcLang.twConj K σ).range := by
        apply (hε (MulAut.congr ε.symm a)).1
        rw [hcomp]
        exact hAI a ha
      obtain ⟨w, hw⟩ := hφe
      have hw' : (RecipeExcLang.twConj K σ) w = (MulAut.congr e).toMonoidHom a := hw
      rw [← range_twistedE6InndiagConj]
      refine ⟨⟨w.1, NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ w.2⟩, ?_⟩
      rw [← hw']
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rfl
    have hu1 : u ≠ 1 := by
      intro h
      exact hp.ne_one (by simpa [h] using horder.symm)
    have hu' : MulAut.congr e u ∈ A' := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have hu'1 : MulAut.congr e u ≠ 1 := by
      intro h
      have h' : (MulAut.congr e) u = (MulAut.congr e) 1 := by
        rw [h, map_one]
      exact hu1 ((MulAut.congr e).injective h')
    let J' : Subgroup (twistedE6RootGroup K σ) := J.map e.toMonoidHom
    have hJ' : CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup (MulAut.congr e u)) := by
      have hmap := CFSG.isComponentOf_map_mulEquiv e hJ
      rw [← gdf_fixed_congr e u] at hmap
      exact hmap
    obtain ⟨hInv', hmark'⟩ :=
      Q1CenterE6Model.q1CenterE6Model_twist_holds hn hK σ hσ hp hp2 hsh hA' hA'le hu' hu'1
        (CFSG.Assembly.isComponentOf_iff_open.2 hJ')
    have hres := Q1E6ThreeModel.componentMarking_congr_equiv e ⟨hInv', hmark'⟩
    exact CFSG.StandardType.largeEvenMarking_mono
      (fun lab R _ I F θ hh => ⟨trivial, hres.1, hh⟩) hres.2

theorem q1SelectedTransfer_centerPrimeE6TwE6 :
    Q1SelectedTransfer
      (fun p lab => CenterPrimeTo p lab ∧ (lab.tag = .E6 ∨ lab.tag = .twE6))
      (fun _ _ _ => True) := by
  refine q1SelectedTransfer_of_toral
    (q1ToralActionTransfer_of_rToral q1RToral_centerPrimeE6TwE6) ?_
  intro G _ _ p B Bs x L D J hcfg P hP
  exact largeEvenMarking_mono
    (fun lab R _ I F θ hh => ⟨hh, fun _ _ _ => trivial⟩) hP

theorem q1CenterPrimeE6TwE6_holds :
    GGBstarInnerDiagJInputOn
      (fun p lab => CenterPrimeTo p lab ∧ (lab.tag = .E6 ∨ lab.tag = .twE6)) :=
  q1On_of_selectedTransfer q1SelectedTransfer_centerPrimeE6TwE6


theorem ggBstarInnerDiagJInput_of_not_e6Three_twE6Three_centerE6
    (hrest : GGBstarInnerDiagJInputOn
      (fun p lab => (¬ E6Three p lab ∧ ¬ TwE6Three p lab ∧ lab.tag ≠ .E8) ∧
        ¬ (CenterPrimeTo p lab ∧ (lab.tag = .E6 ∨ lab.tag = .twE6)))) :
    GGBstarInnerDiagJInput := by
  apply ggBstarInnerDiagJInput_of_not_e6Three_twE6Three_e8
  intro G _ _ p B Bs x L D J hcfg hmark
  apply (q1On_or hrest q1CenterPrimeE6TwE6_holds) G p B Bs x L D J hcfg
  exact largeEvenMarking_mono (fun lab R _ I F θ h =>
    ⟨by
      by_cases hS : CenterPrimeTo p lab ∧ (lab.tag = .E6 ∨ lab.tag = .twE6)
      · exact Or.inr hS
      · exact Or.inl ⟨h.1, hS⟩, h.2⟩) hmark

end Certificates

end CFSG.StandardType
