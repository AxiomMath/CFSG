module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeNaturalA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.NaturalClassicalQuasisimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.ProdComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaPlusLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Alpha
public import CFSG.GroupTheory.SubgroupConjOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveCases

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem quasisimple_or_isOmegaPlus_of_natural {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (hn : 2 < n)
    (hcase : IsNaturalClassicalModule H n ∨
      (Even n ∧ IsOmegaMinus ↥H 4 (n / 2) ∧ NatOmegaMinus H ⊤ ⊥ 4 (n / 2))) :
    CFSG.Open.IsQuasisimple ↥H ∨ IsOmegaPlus ↥H 4 n := by
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  rcases hcase with hnat | ⟨heven, hom, hnatom⟩
  · by_cases hOP : IsOmegaPlus ↥H 4 n
    · exact Or.inr hOP
    · exact Or.inl
        (isQuasisimple_of_isNaturalClassicalModule_of_not_omegaPlus hnat (by omega) hOP)
  · refine Or.inl (isQuasisimple_of_isNaturalClassicalModule_of_not_omegaPlus
      (Or.inr (Or.inl ⟨hom, hnatom⟩)) ?_ ?_)
    · have h2n : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
      omega
    · intro hOP
      exact not_isOmegaMinus_of_isOmegaPlus (by
        have h2n : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
        omega) hOP hom

private theorem exists_two_components_of_isOmegaPlus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (hn : 2 ≤ n) (hOP : IsOmegaPlus ↥H 4 n) :
    ∃ F₁ F₂ : Subgroup (MulAut W), IsComponentOf F₁ H ∧ IsComponentOf F₂ H ∧
      F₁ ⊔ F₂ = H ∧ Disjoint F₁ F₂ ∧ F₁ ≠ ⊥ ∧ F₂ ≠ ⊥ := by
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨A, B, hAg, hBg, ⟨e⟩, hLA, hLB⟩ := isL2Square_of_isOmegaPlus hn hOP
  letI : Group A := hAg
  letI : Group B := hBg
  haveI : Finite (A × B) := Finite.of_injective (e.symm : A × B → ↥H) e.symm.injective
  haveI : Finite A := Finite.of_surjective (MonoidHom.fst A B) (fun a => ⟨(a, 1), rfl⟩)
  haveI : Finite B := Finite.of_surjective (MonoidHom.snd A B) (fun b => ⟨(1, b), rfl⟩)
  have h₁ := NatParMax.isComponentOf_map_prodFirstFactor e (NatParMax.isQuasisimple_of_isL2 hLA)
  have h₂ := NatParMax.isComponentOf_map_prodSecondFactor e (NatParMax.isQuasisimple_of_isL2 hLB)
  exact ⟨_, _, h₁, h₂, NatParMax.map_prodFirstFactor_sup_map_prodSecondFactor e,
    NatParMax.disjoint_map_prodFirstFactor_map_prodSecondFactor e,
    CFSG.Quasithin.B15P4.ne_bot_of_isComponentOf h₁,
    CFSG.Quasithin.B15P4.ne_bot_of_isComponentOf h₂⟩

private theorem le_and_component_of_eq_iSup {W : Type} [CommGroup W] [Finite W]
    {Y H K : Subgroup (MulAut W)}
    (hH : H = ⨆ g ∈ Y, K.map (MulAut.conj g).toMonoidHom)
    (hcomp : IsComponentOf K Y) :
    K ≤ H ∧ H ≤ Y ∧ IsComponentOf K H := by
  have hKH : K ≤ H := by
    rw [hH]
    calc K = K.map (MulAut.conj (1 : MulAut W)).toMonoidHom := by
          rw [show (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) by
            ext x
            simp [MulAut.conj_apply], Subgroup.map_id]
      _ ≤ ⨆ g ∈ Y, K.map (MulAut.conj g).toMonoidHom :=
          le_iSup₂ (f := fun g (_ : g ∈ Y) => K.map (MulAut.conj g).toMonoidHom)
            (1 : MulAut W) Y.one_mem
  have hHY : H ≤ Y := by
    rw [hH]
    refine iSup₂_le fun g hg => ?_
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    exact Y.mul_mem (Y.mul_mem hg (hcomp.1 hk)) (Y.inv_mem hg)
  exact ⟨hKH, hHY, CFSG.Quasithin.B15P4.isComponentOf_of_le hcomp hKH hHY⟩

private theorem orbit_subset_factors_of_isOmegaPlus {W : Type} [CommGroup W] [Finite W]
    {Y H K : Subgroup (MulAut W)} {n : ℕ} (hOP : IsOmegaPlus H 4 n) (hn : 2 ≤ n)
    (hH : H = ⨆ g ∈ Y, K.map (MulAut.conj g).toMonoidHom)
    (hcomp : IsComponentOf K Y) :
    ∃ F₁ F₂ : Subgroup (MulAut W), IsComponentOf F₁ H ∧ IsComponentOf F₂ H ∧
      F₁ ⊔ F₂ = H ∧ Disjoint F₁ F₂ ∧ F₁ ≠ ⊥ ∧ F₂ ≠ ⊥ ∧
      ∀ X, (∃ y ∈ Y, K.map (MulAut.conj y).toMonoidHom = X) → X = F₁ ∨ X = F₂ := by
  obtain ⟨F₁, F₂, hF₁c, hF₂c, hsup, hd, hF₁ne, hF₂ne⟩ :=
    exists_two_components_of_isOmegaPlus hn hOP
  have hHM : H ≤ Y := (le_and_component_of_eq_iSup hH hcomp).2.1
  refine ⟨F₁, F₂, hF₁c, hF₂c, hsup, hd, hF₁ne, hF₂ne, ?_⟩
  rintro X ⟨y, hy, rfl⟩
  have hXH : K.map (MulAut.conj y).toMonoidHom ≤ H := by
    rw [hH]
    exact le_iSup₂_of_le y hy le_rfl
  exact NatParMax.eq_factor_of_isComponentOf hsup hF₁c hF₂c
    (CFSG.Quasithin.B15P4.isComponentOf_of_le
      (CFSG.Quasithin.B113.isComponentOf_conj hcomp hy) hXH hHM)

private theorem two_le_ncard_conjSet_of_isOmegaPlus {W : Type} [CommGroup W] [Finite W]
    {Y H K : Subgroup (MulAut W)} {n : ℕ} (hOP : IsOmegaPlus H 4 n) (hn : 2 ≤ n)
    (hH : H = ⨆ g ∈ Y, K.map (MulAut.conj g).toMonoidHom)
    (hcomp : IsComponentOf K Y) :
    2 ≤ {B : Subgroup (MulAut W) | ∃ y ∈ Y, K.map (MulAut.conj y).toMonoidHom = B}.ncard := by
  obtain ⟨F₁, F₂, hF₁c, hF₂c, hsup, hd, hF₁ne, hF₂ne, hmemF⟩ :=
    orbit_subset_factors_of_isOmegaPlus hOP hn hH hcomp
  have hKmem : K ∈ {B : Subgroup (MulAut W) | ∃ y ∈ Y,
      K.map (MulAut.conj y).toMonoidHom = B} := by
    refine ⟨1, Y.one_mem, ?_⟩
    rw [show (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) by
      ext x
      simp [MulAut.conj_apply], Subgroup.map_id]
  have hex : ∃ X ∈ {B : Subgroup (MulAut W) | ∃ y ∈ Y,
      K.map (MulAut.conj y).toMonoidHom = B}, X ≠ K := by
    by_contra h
    push Not at h
    have hjoin : (⨆ g ∈ Y, K.map (MulAut.conj g).toMonoidHom) ≤ K :=
      iSup₂_le fun g hg => le_of_eq (h _ ⟨g, hg, rfl⟩)
    have hHK : H ≤ K := hH ▸ hjoin
    rcases hmemF K hKmem with hKF | hKF
    · have hF₂le : F₂ ≤ K := hF₂c.1.trans hHK
      rw [hKF] at hF₂le
      exact hF₂ne (le_bot_iff.mp ((le_inf hF₂le le_rfl).trans hd.le_bot))
    · have hF₁le : F₁ ≤ K := hF₁c.1.trans hHK
      rw [hKF] at hF₁le
      exact hF₁ne (le_bot_iff.mp ((le_inf hF₁le le_rfl).trans hd.symm.le_bot))
  obtain ⟨X, hXmem, hXne⟩ := hex
  have hpair : ({K, X} : Set (Subgroup (MulAut W))).ncard = 2 :=
    Set.ncard_pair hXne.symm
  rw [← hpair]
  refine Set.ncard_le_ncard ?_
  rintro Z (rfl | rfl)
  · exact hKmem
  · exact hXmem

private theorem ncard_conjSet_eq_two_of_isOmegaPlus {W : Type} [CommGroup W] [Finite W]
    {Y H K : Subgroup (MulAut W)} {n : ℕ} (hOP : IsOmegaPlus H 4 n) (hn : 2 ≤ n)
    (hH : H = ⨆ g ∈ Y, K.map (MulAut.conj g).toMonoidHom)
    (hcomp : IsComponentOf K Y) :
    {B : Subgroup (MulAut W) | ∃ y ∈ Y, K.map (MulAut.conj y).toMonoidHom = B}.ncard = 2 := by
  obtain ⟨F₁, F₂, hF₁c, hF₂c, hsup, hd, hF₁ne, hF₂ne, hmemF⟩ :=
    orbit_subset_factors_of_isOmegaPlus hOP hn hH hcomp
  have hF₁F₂ : F₁ ≠ F₂ := by
    intro h
    have hle : F₂ ≤ F₁ ⊓ F₂ := by rw [← h]; exact le_inf le_rfl le_rfl
    exact hF₂ne (le_bot_iff.mp (hle.trans hd.le_bot))
  have hupper : {B : Subgroup (MulAut W) | ∃ y ∈ Y,
      K.map (MulAut.conj y).toMonoidHom = B}.ncard ≤ 2 := by
    calc {B : Subgroup (MulAut W) | ∃ y ∈ Y,
          K.map (MulAut.conj y).toMonoidHom = B}.ncard
        ≤ ({F₁, F₂} : Set (Subgroup (MulAut W))).ncard := Set.ncard_le_ncard
          (fun X hX => by rcases hmemF X hX with h | h <;> simp [h])
      _ = 2 := Set.ncard_pair hF₁F₂
  have hlower : 2 ≤ {B : Subgroup (MulAut W) | ∃ y ∈ Y,
      K.map (MulAut.conj y).toMonoidHom = B}.ncard :=
    two_le_ncard_conjSet_of_isOmegaPlus hOP hn hH hcomp
  exact le_antisymm hupper hlower

private theorem product_barSub_data {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hK : K ∈ calC c.L) {t : G}
    (htT : t ∈ D.T) (hsup : c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA)) :
    (barSub (⊥ : Subgroup G) A hA K ⊔
        barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) =
        barSub (⊥ : Subgroup G) A hA c.L) ∧
      fixV (barSub (⊥ : Subgroup G) A hA c.L) = ⊥ ∧
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ∈
        conjSet (barSub (⊥ : Subgroup G) A hA K) (Mbar c.N (⊥ : Subgroup G) A hA) ∧
      IsComponentOf (barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom))
        (Mbar c.N (⊥ : Subgroup G) A hA) := by
  have hNst : c.N ≤ stabTil (⊥ : Subgroup G) A :=
    N_le_stabTil_of_le_normalizer c hAN
  have hKst : K ≤ stabTil (⊥ : Subgroup G) A :=
    ((CFSG.Quasithin.A3.subnormal_le hK.1).trans (Ctx23L.L_le_N c)).trans hNst
  have hKtL : K.map (MulAut.conj t).toMonoidHom ≤ c.L := by
    rw [hsup]
    exact le_sup_right
  have hKtst : K.map (MulAut.conj t).toMonoidHom ≤ stabTil (⊥ : Subgroup G) A :=
    (hKtL.trans (Ctx23L.L_le_N c)).trans hNst
  have htst : t ∈ stabTil (⊥ : Subgroup G) A := hNst (Ctx23L.T_le_N c htT)
  have hLA : barSub (⊥ : Subgroup G) A hA K ⊔
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) =
      barSub (⊥ : Subgroup G) A hA c.L := by
    calc barSub (⊥ : Subgroup G) A hA K ⊔
        barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom)
        = barSub (⊥ : Subgroup G) A hA (K ⊔ K.map (MulAut.conj t).toMonoidHom) :=
          (s16c7_barSub_sup (⊥ : Subgroup G) A hA hKst hKtst).symm
      _ = barSub (⊥ : Subgroup G) A hA c.L := by rw [hsup]
  have hfix : fixV (barSub (⊥ : Subgroup G) A hA c.L) = ⊥ :=
    fixV_barSub_eq_bot c hA hAV hAN
  let gT : MulAut (Vtil (⊥ : Subgroup G) A hA) := actTil (⊥ : Subgroup G) A hA ⟨t, htst⟩
  have hgT : gT ∈ Mbar c.N (⊥ : Subgroup G) A hA :=
    actTil_mem_barSub (⊥ : Subgroup G) A hA (Ctx23L.T_le_N c htT) htst
  have hKAt_eq : barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) =
      (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj gT).toMonoidHom :=
    TwelveTwentyThree.barSub_map_conj hA hKst htst
  have hKAtmem : barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ∈
      conjSet (barSub (⊥ : Subgroup G) A hA K) (Mbar c.N (⊥ : Subgroup G) A hA) :=
    ⟨gT, hgT, hKAt_eq⟩
  refine ⟨hLA, hfix, hKAtmem, ?_⟩
  rw [hKAt_eq]
  exact CFSG.Quasithin.B113.isComponentOf_conj hcomp hgT

theorem Ctx23L.not_first_case_of_product {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (h1930 : H1930 D) {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hn2 : 2 < c.n)
    (hprod : ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (h1 : (⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      IsDirSumOver (conjSet (barSub (⊥ : Subgroup G) A hA K)
        (Mbar c.N (⊥ : Subgroup G) A hA)) (fun X => commV X) ∧
      ((IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) c.n ∧
          BinaryNaturalSL (barSub (⊥ : Subgroup G) A hA K)
            (commV (barSub (⊥ : Subgroup G) A hA K)) ⊥ 2 c.n) ∨
        (Even c.n ∧ IsOmegaMinus ↥(barSub (⊥ : Subgroup G) A hA K) 4 (c.n / 2) ∧
          NatOmegaMinus (barSub (⊥ : Subgroup G) A hA K)
            (commV (barSub (⊥ : Subgroup G) A hA K)) ⊥ 4 (c.n / 2)))) : False := by
  obtain ⟨t, htT, hne, hsup⟩ := hprod
  have hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA) :=
    isComponentOf_K_Mbar c h208 h1930 hA hAV hAne hAN hK hgen
  obtain ⟨hLA, hfix, hKAtmem, hKAtcomp⟩ :=
    product_barSub_data c hA hAV hAN hK htT hsup hcomp
  by_cases htwo : ∀ X ∈ conjSet (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA),
      X = barSub (⊥ : Subgroup G) A hA K ∨
        X = barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom)
  · exact Ctx23L.not_case_one_of_two_conjugates c h207 h209 h208 h1930 hA hAV hAne hAN
      hK hgen htT hne h1.2.1 htwo hn2 h1.2.2
  · push Not at htwo
    obtain ⟨X, hXmem, hXne1, hXne2⟩ := htwo
    have hXcomp : IsComponentOf X (Mbar c.N (⊥ : Subgroup G) A hA) := by
      obtain ⟨g, hg, rfl⟩ := hXmem
      exact CFSG.Quasithin.B113.isComponentOf_conj hcomp hg
    exact false_of_case_one_of_three_conjugates hcomp hKAtcomp hXcomp hLA hfix
      (fun _ _ hy => MulEquiv.ext fun _ => hy _) h1.2.1 hKAtmem hXmem hXne1 hXne2

private theorem false_of_isOmegaPlus_of_single {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hsingle : K = c.L) {H : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hH : H = ⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
      (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom)
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA))
    (hOP : IsOmegaPlus ↥H 4 c.n) (hn2 : 2 < c.n) : False := by
  have hn2' : 2 ≤ c.n := by omega
  have horbit : {B : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)) |
      ∃ y ∈ Mbar c.N (⊥ : Subgroup G) A hA,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj y).toMonoidHom = B}.ncard = 2 :=
    ncard_conjSet_eq_two_of_isOmegaPlus hOP hn2' hH hcomp
  have hNst : c.N ≤ stabTil (⊥ : Subgroup G) A :=
    N_le_stabTil_of_le_normalizer c hAN
  have hLst : c.L ≤ stabTil (⊥ : Subgroup G) A :=
    (Ctx23L.L_le_N c).trans hNst
  have hTN : barSub (⊥ : Subgroup G) A hA D.T ≤
      Subgroup.normalizer
        (barSub (⊥ : Subgroup G) A hA K : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) := by
    rw [hsingle]
    exact close16_barSub_le_normalizer hLst c.hL.1.1
  have hrel : ((Mbar c.N (⊥ : Subgroup G) A hA) ⊓ Subgroup.normalizer
      (barSub (⊥ : Subgroup G) A hA K : Set (MulAut (Vtil (⊥ : Subgroup G) A hA)))).relIndex
      (Mbar c.N (⊥ : Subgroup G) A hA) = 2 := by
    have h1 := CFSG.GroupTheory.ncard_conj_mul_card_inf_normalizer
      (Mbar c.N (⊥ : Subgroup G) A hA) (barSub (⊥ : Subgroup G) A hA K)
    have h2 : (((Mbar c.N (⊥ : Subgroup G) A hA) ⊓ Subgroup.normalizer
        (barSub (⊥ : Subgroup G) A hA K : Set (MulAut (Vtil (⊥ : Subgroup G) A hA)))).relIndex
        (Mbar c.N (⊥ : Subgroup G) A hA)) * Nat.card ↥((Mbar c.N (⊥ : Subgroup G) A hA) ⊓
          Subgroup.normalizer
            (barSub (⊥ : Subgroup G) A hA K : Set (MulAut (Vtil (⊥ : Subgroup G) A hA)))) =
        Nat.card ↥(Mbar c.N (⊥ : Subgroup G) A hA) := by
      simpa [inf_eq_left.mpr inf_le_left] using
        Subgroup.relIndex_mul_card
          (H := (Mbar c.N (⊥ : Subgroup G) A hA) ⊓ Subgroup.normalizer
            (barSub (⊥ : Subgroup G) A hA K : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))))
          (K := Mbar c.N (⊥ : Subgroup G) A hA)
    rw [horbit] at h1
    exact (Nat.eq_of_mul_eq_mul_right (Nat.card_pos) (h1.trans h2.symm)).symm
  have hodd := odd_relIndex_normalizer_of_isSylowIn (isSylowIn_T_Mbar c hA hAN)
    (barSub_mono (⊥ : Subgroup G) A hA (Ctx23L.T_le_N c)) hTN
  rw [hrel] at hodd
  obtain ⟨k, hk⟩ := hodd
  omega

theorem Ctx23L.LA_eq_H_of_natural_single {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hsingle : K = c.L) (hn2 : 2 < c.n)
    {H : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hH : H = ⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
      (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom)
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA))
    (hcase : IsNaturalClassicalModule H c.n ∨
      (Even c.n ∧ IsOmegaMinus ↥H 4 (c.n / 2) ∧
        NatOmegaMinus H ⊤ ⊥ 4 (c.n / 2))) :
    barSub (⊥ : Subgroup G) A hA c.L = H := by
  obtain ⟨hKH, -, hcompH⟩ := le_and_component_of_eq_iSup hH hcomp
  rcases quasisimple_or_isOmegaPlus_of_natural hn2 hcase with hq | hOP
  · have hKAH : barSub (⊥ : Subgroup G) A hA K = H :=
      eq_of_isQuasisimple_of_isComponentOf hq hKH hcompH
    calc barSub (⊥ : Subgroup G) A hA c.L = barSub (⊥ : Subgroup G) A hA K := by
          rw [hsingle]
      _ = H := hKAH
  · exfalso
    exact false_of_isOmegaPlus_of_single c hA hAV hAN hsingle hH hcomp hOP hn2

private theorem product_H_components {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    {H : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hH : H = ⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
      (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom)
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA)) {t : G} (htT : t ∈ D.T)
    (hsup : c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    (barSub (⊥ : Subgroup G) A hA c.L = barSub (⊥ : Subgroup G) A hA K ⊔
        barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom)) ∧
      IsComponentOf (barSub (⊥ : Subgroup G) A hA K) H ∧
      IsComponentOf (barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom)) H := by
  have hNst : c.N ≤ stabTil (⊥ : Subgroup G) A :=
    N_le_stabTil_of_le_normalizer c hAN
  have hKL : K ≤ c.L := by rw [hsup]; exact le_sup_left
  have hKtL : K.map (MulAut.conj t).toMonoidHom ≤ c.L := by
    rw [hsup]
    exact le_sup_right
  have hKst : K ≤ stabTil (⊥ : Subgroup G) A :=
    (hKL.trans (Ctx23L.L_le_N c)).trans hNst
  have hKtst : K.map (MulAut.conj t).toMonoidHom ≤ stabTil (⊥ : Subgroup G) A :=
    (hKtL.trans (Ctx23L.L_le_N c)).trans hNst
  have htst : t ∈ stabTil (⊥ : Subgroup G) A := hNst (Ctx23L.T_le_N c htT)
  let gT : MulAut (Vtil (⊥ : Subgroup G) A hA) := actTil (⊥ : Subgroup G) A hA ⟨t, htst⟩
  have hgT : gT ∈ Mbar c.N (⊥ : Subgroup G) A hA :=
    actTil_mem_barSub (⊥ : Subgroup G) A hA (Ctx23L.T_le_N c htT) htst
  have hKAt_eq : barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) =
      (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj gT).toMonoidHom :=
    TwelveTwentyThree.barSub_map_conj hA hKst htst
  have hLA : barSub (⊥ : Subgroup G) A hA c.L =
      barSub (⊥ : Subgroup G) A hA K ⊔
        barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) := by
    rw [hsup, s16c7_barSub_sup (⊥ : Subgroup G) A hA hKst hKtst]
  obtain ⟨hKAleH, hHM, hKAcompH⟩ := le_and_component_of_eq_iSup hH hcomp
  have hKAtleH : barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≤ H := by
    calc barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom)
        = (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj gT).toMonoidHom := hKAt_eq
      _ ≤ H := by
          rw [hH]
          exact le_iSup₂_of_le gT hgT le_rfl
  refine ⟨hLA, hKAcompH, ?_⟩
  exact CFSG.Quasithin.B15P4.isComponentOf_of_le
    (hKAt_eq ▸ CFSG.Quasithin.B113.isComponentOf_conj hcomp hgT) hKAtleH hHM

theorem Ctx23L.LA_eq_H_of_product {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hn2 : 2 < c.n)
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA))
    {H : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hH : H = ⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
      (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom)
    (hprod : ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hcase : IsNaturalClassicalModule H c.n ∨
      (Even c.n ∧ IsOmegaMinus ↥H 4 (c.n / 2) ∧
        NatOmegaMinus H ⊤ ⊥ 4 (c.n / 2))) :
    barSub (⊥ : Subgroup G) A hA c.L = H := by
  obtain ⟨t, htT, hne, hsup⟩ := hprod
  obtain ⟨hLA, hKAcompH, hKAtcompH⟩ :=
    product_H_components c hA hAN hH hcomp htT hsup
  obtain ⟨hKAleH, -, -⟩ := le_and_component_of_eq_iSup hH hcomp
  have hKAtleH : barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≤ H :=
    hKAtcompH.1
  rcases quasisimple_or_isOmegaPlus_of_natural hn2 hcase with hq | hOP
  · exfalso
    have h1 := eq_of_isQuasisimple_of_isComponentOf hq hKAleH hKAcompH
    have h2 := eq_of_isQuasisimple_of_isComponentOf hq hKAtleH hKAtcompH
    exact hne (h2.trans h1.symm)
  · obtain ⟨F₁, F₂, hF₁c, hF₂c, hsupF, -, -, -⟩ :=
      exists_two_components_of_isOmegaPlus (by omega : 2 ≤ c.n) hOP
    rcases NatParMax.eq_factor_of_isComponentOf hsupF hF₁c hF₂c hKAcompH with h1 | h1
    · have h2 : barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) = F₂ := by
        rcases NatParMax.eq_factor_of_isComponentOf hsupF hF₁c hF₂c hKAtcompH with h | h
        · exact absurd (h.trans h1.symm) hne
        · exact h
      rw [hLA, h1, h2, hsupF]
    · have h2 : barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) = F₁ := by
        rcases NatParMax.eq_factor_of_isComponentOf hsupF hF₁c hF₂c hKAtcompH with h | h
        · exact h
        · exact absurd (h.trans h1.symm) hne
      rw [hLA, h1, h2, sup_comm, hsupF]

theorem Ctx23L.natural_of_case_two_three_barSub_nat {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hK : K ∈ calC c.L)
    {H : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hH : H = ⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
      (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom)
    (hLA : barSub (⊥ : Subgroup G) A hA c.L = H)
    (hYH : Mbar c.N (⊥ : Subgroup G) A hA ≤
      Subgroup.normalizer
        (((⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
          (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) :
            Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))) :
            Set (MulAut (Vtil (⊥ : Subgroup G) A hA))))
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA))
    (hcase : IsNaturalClassicalModule H c.n ∨
      (Even c.n ∧ IsOmegaMinus ↥H 4 (c.n / 2) ∧
        NatOmegaMinus H ⊤ ⊥ 4 (c.n / 2))) :
    ∃ k, IsNaturalClassicalModule (barSub (⊥ : Subgroup G) A hA c.L) k ∧
      (k = c.n ∨ (2 * k = c.n ∧
        IsOmegaMinus ↥(barSub (⊥ : Subgroup G) A hA c.L) 4 k ∧
        NatOmegaMinus (barSub (⊥ : Subgroup G) A hA c.L) ⊤ ⊥ 4 k)) ∧
      ((barSub (⊥ : Subgroup G) A hA c.L).subgroupOf
        (Mbar c.N (⊥ : Subgroup G) A hA)).Normal := by
  have hHconj : (⨆ X ∈ conjSet (barSub (⊥ : Subgroup G) A hA K)
        (Mbar c.N (⊥ : Subgroup G) A hA), X) =
      ⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun X hX => ?_
      obtain ⟨g, hg, rfl⟩ := hX
      exact le_iSup₂_of_le g hg le_rfl
    · refine iSup₂_le fun g hg => le_iSup₂_of_le _ ⟨g, hg, rfl⟩ le_rfl
  have hH' : H = ⨆ X ∈ conjSet (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA), X := hH.trans hHconj.symm
  have hYH' : Mbar c.N (⊥ : Subgroup G) A hA ≤
      Subgroup.normalizer (H : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) := by
    simpa [hH] using hYH
  rcases hcase with h2 | h3
  · obtain ⟨-, -, -, hnorm⟩ :=
      natural_of_case_two_three_barSub c hA hAV hK hH' hLA hYH' (Or.inl h2) hcomp
    exact ⟨c.n, by rwa [hLA], Or.inl rfl, hnorm⟩
  · obtain ⟨-, -, -, hnorm⟩ :=
      natural_of_case_two_three_barSub c hA hAV hK hH' hLA hYH' (Or.inr h3) hcomp
    refine ⟨c.n / 2, ?_, Or.inr ⟨Nat.two_mul_div_two_of_even h3.1, ?_, ?_⟩, hnorm⟩
    · rw [hLA]
      exact Or.inr (Or.inl h3.2)
    · rw [hLA]
      exact h3.2.1
    · rw [hLA]
      exact h3.2.2

end CFSG.LocalAnalysis.UniquenessCase.UC22
