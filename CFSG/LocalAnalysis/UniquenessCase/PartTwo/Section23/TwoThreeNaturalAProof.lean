module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeNaturalAConfig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeNaturalAParabolic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeNaturalAH
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private local instance instMulVtil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Mul (Vtil V₀ V hV) := inferInstance

private theorem le_normalizer_iSup_map_conj {H : Type} [Group H] (Γ U : Subgroup H) :
    Γ ≤ Subgroup.normalizer
      (((⨆ g ∈ Γ, U.map (MulAut.conj g).toMonoidHom) : Subgroup H) : Set H) := by
  have key : ∀ r ∈ Γ, (⨆ g ∈ Γ, U.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj r).toMonoidHom ≤ ⨆ g ∈ Γ, U.map (MulAut.conj g).toMonoidHom := by
    intro r hr
    simp only [Subgroup.map_iSup, map_map]
    refine iSup₂_le fun g hg => le_iSup₂_of_le (r * g) (mul_mem hr hg) ?_
    have : (MulAut.conj r).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (r * g)).toMonoidHom := by
      ext w
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
  intro r hr
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key r hr ⟨h, hh, rfl⟩
  · intro hh
    have := key r⁻¹ (inv_mem hr) ⟨_, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

private theorem natural_A_single {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (h145 : Inputs1719.W4Thm14_5) (h128 : W4Lem12_8) (hDeg : KMinDegLow)
    (h1A : S23_1A D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (h2010 : S20_10 D) (h1930 : H1930 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    {K : Subgroup G} (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hsingle : K = c.L) (hn2 : 2 < c.n)
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA))
    (hYH : Mbar c.N (⊥ : Subgroup G) A hA ≤ Subgroup.normalizer
      (((⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) :
          Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))) :
        Set (MulAut (Vtil (⊥ : Subgroup G) A hA)))) :
    ∃ k : ℕ, IsNaturalClassicalModule (barSub (⊥ : Subgroup G) A hA c.L) k ∧
      (k = c.n ∨ (2 * k = c.n ∧
        IsOmegaMinus ↥(barSub (⊥ : Subgroup G) A hA c.L) 4 k ∧
        NatOmegaMinus (barSub (⊥ : Subgroup G) A hA c.L) ⊤ ⊥ 4 k)) ∧
      ((barSub (⊥ : Subgroup G) A hA c.L).subgroupOf
        (Mbar c.N (⊥ : Subgroup G) A hA)).Normal := by
  obtain ⟨e, hshape⟩ :=
    Ctx23L.shape_K_A_of_single c hG2 h3D4 h2F4 h207 h208 h209 h1930 h1A hDeg h128 hn2
      hA hAV hAne hAN hmin hK hgen hsingle
  have hnParamL0 := Ctx23L.nParam_barSub_L0 c h208 h1930 hA hAV hAne hAN hmin
  obtain ⟨P, hPle, hPpar, hHinfEq, hHinfPne, hnorm, hcomm, hminPar, hbounds⟩ :=
    Ctx23L.exists_fourteen_five_data_single c h207 h208 h209 h2010 h1930 h1A
      hA hAV hAne hAN hmin hK hgen hsingle hnParamL0
  have hnParamP : NParam (Hinf (barSub (⊥ : Subgroup G) A hA P)) c.n := by
    rw [hHinfEq]
    exact hnParamL0
  have htri := c.fourteen_five h145 h208 h1930 hA hAV hAne hAN hmin hK hgen
    (ncard_conjSet_barSub_K_le_two c hA hAN hK (Or.inl hsingle))
    hPle hPpar hHinfPne hnorm hcomm hnParamP hn2 hshape hminPar hbounds
  rcases htri with h1 | h2 | h3
  · have hKsingle : barSub (⊥ : Subgroup G) A hA K =
        barSub (⊥ : Subgroup G) A hA c.L := by rw [hsingle]
    exfalso
    exact Ctx23L.not_case_one_of_single c h208 h1930 hA hAV hAne hAN hK hgen
      hKsingle h1.1 h1.2.1
  · have hLA : barSub (⊥ : Subgroup G) A hA c.L =
        ⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
          (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom :=
      Ctx23L.LA_eq_H_of_natural_single c h208 h1930 hA hAV hAne hAN hmin hK hgen
        hsingle hn2 rfl hcomp (Or.inl h2)
    exact Ctx23L.natural_of_case_two_three_barSub_nat c hA hAV hK rfl hLA
      hYH hcomp (Or.inl h2)
  · have hLA : barSub (⊥ : Subgroup G) A hA c.L =
        ⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
          (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom :=
      Ctx23L.LA_eq_H_of_natural_single c h208 h1930 hA hAV hAne hAN hmin hK hgen
        hsingle hn2 rfl hcomp (Or.inr h3)
    exact Ctx23L.natural_of_case_two_three_barSub_nat c hA hAV hK rfl hLA
      hYH hcomp (Or.inr h3)

private theorem natural_A_product_trichotomy {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch)
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (h145 : Inputs1719.W4Thm14_5) (h208 : S20_8 D) (h1930 : H1930 D)
    (h1A : S23_1A D Ch) (h207 : S20_7 D) (h209 : S20_9 D) (h2010 : S20_10 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    {K : Subgroup G} (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hprod : ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom) (hn2 : 2 < c.n)
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA)) :
  ((⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
      (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) ≠
      barSub (⊥ : Subgroup G) A hA K ∧
    IsDirSumOver (conjSet (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA)) (fun X => commV X) ∧
    ((IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) c.n ∧
        BinaryNaturalSL (barSub (⊥ : Subgroup G) A hA K)
          (commV (barSub (⊥ : Subgroup G) A hA K)) ⊥ 2 c.n) ∨
      (Even c.n ∧ IsOmegaMinus ↥(barSub (⊥ : Subgroup G) A hA K) 4 (c.n / 2) ∧
        NatOmegaMinus (barSub (⊥ : Subgroup G) A hA K)
          (commV (barSub (⊥ : Subgroup G) A hA K)) ⊥ 4 (c.n / 2)))) ∨
    IsNaturalClassicalModule
      (⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) c.n ∨
    (Even c.n ∧ IsOmegaMinus
        ↥(⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
          (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) 4 (c.n / 2) ∧
      NatOmegaMinus
        (⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
          (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) ⊤ ⊥ 4
          (c.n / 2)) := by
  obtain ⟨t, htT, hne, hsup⟩ := hprod
  have hL0L := Ctx23L.product_L0_eq_L c hG2 h3D4 h2F4 h207 h209 h2010 h1930 hA hAV
    hAne hAN hmin hK hgen ⟨t, htT, hne, hsup⟩
  have hnat := Ctx23L.rankOne_shape_barSub_K_of_product c h208 h1930 hA hAV hAne hAN
    hmin hK hgen ⟨t, htT, hne, hsup⟩ hL0L
  obtain ⟨e, hshape⟩ := Ctx23L.shape_K_A_of_product c hA hnat
  have hnParamK := Ctx23L.nParam_barSub_K_of_product c h208 h1930 hA hAV hAne hAN
    hmin hK hgen ⟨t, htT, hne, hsup⟩ hL0L
  obtain ⟨hPpar, hcomm, hminPar, hbounds⟩ :=
    Ctx23L.exists_fourteen_five_data_product c h207 h208 h209 h1930 h1A
      hA hAV hAne hAN hmin hK hgen ⟨t, htT, hne, hsup⟩ hL0L hnat hnParamK
  have hHinf := Hinf_barSub_K_eq hA hcomp
  have hHinfPne : Hinf (barSub (⊥ : Subgroup G) A hA K) ≠ ⊥ := by
    rw [hHinf]
    exact barSub_K_ne_bot hA hcomp
  have hnParamP : NParam (Hinf (barSub (⊥ : Subgroup G) A hA K)) c.n := by
    rw [hHinf]
    exact hnParamK
  have hnorm : normIn (barSub (⊥ : Subgroup G) A hA D.T)
      (barSub (⊥ : Subgroup G) A hA K) ≤ Subgroup.normalizer
      (barSub (⊥ : Subgroup G) A hA K : Set
        (MulAut (Vtil (⊥ : Subgroup G) A hA))) :=
    inf_le_right
  exact c.fourteen_five h145 h208 h1930 hA hAV hAne hAN hmin hK hgen
    (ncard_conjSet_barSub_K_le_two c hA hAN hK (Or.inr ⟨t, htT, hsup⟩))
    le_rfl hPpar hHinfPne hnorm hcomm hnParamP hn2 hshape hminPar hbounds

private theorem natural_A_product {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (h145 : Inputs1719.W4Thm14_5) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (h2010 : S20_10 D) (h1930 : H1930 D) (h1A : S23_1A D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    {K : Subgroup G} (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hprod : ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom) (hn2 : 2 < c.n)
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA))
    (hYH : Mbar c.N (⊥ : Subgroup G) A hA ≤ Subgroup.normalizer
      (((⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) :
          Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))) :
        Set (MulAut (Vtil (⊥ : Subgroup G) A hA)))) :
    ∃ k : ℕ, IsNaturalClassicalModule (barSub (⊥ : Subgroup G) A hA c.L) k ∧
      (k = c.n ∨ (2 * k = c.n ∧
        IsOmegaMinus ↥(barSub (⊥ : Subgroup G) A hA c.L) 4 k ∧
        NatOmegaMinus (barSub (⊥ : Subgroup G) A hA c.L) ⊤ ⊥ 4 k)) ∧
      ((barSub (⊥ : Subgroup G) A hA c.L).subgroupOf
        (Mbar c.N (⊥ : Subgroup G) A hA)).Normal := by
  obtain ⟨t, htT, hne, hsup⟩ := hprod
  have htri := natural_A_product_trichotomy c hG2 h3D4 h2F4 h145 h208 h1930 h1A
    h207 h209 h2010 hA hAV hAne hAN hmin hK hgen ⟨t, htT, hne, hsup⟩ hn2 hcomp
  rcases htri with h1 | h2 | h3
  · exfalso
    exact Ctx23L.not_first_case_of_product c h207 h208 h209 h1930 hA hAV hAne
      hAN hK hgen hn2 ⟨t, htT, hne, hsup⟩ h1
  · have hLA := Ctx23L.LA_eq_H_of_product c hA hAN hn2 hcomp rfl ⟨t, htT, hne, hsup⟩ (Or.inl h2)
    exact Ctx23L.natural_of_case_two_three_barSub_nat c hA hAV hK rfl hLA hYH hcomp
      (Or.inl h2)
  · have hLA := Ctx23L.LA_eq_H_of_product c hA hAN hn2 hcomp rfl ⟨t, htT, hne, hsup⟩ (Or.inr h3)
    exact Ctx23L.natural_of_case_two_three_barSub_nat c hA hAV hK rfl hLA hYH hcomp
      (Or.inr h3)

theorem Ctx23L.natural_A {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h145 : Inputs1719.W4Thm14_5) (h128 : W4Lem12_8) (hDeg : KMinDegLow)
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (h1A : S23_1A D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (h2010 : S20_10 D) (hE : UC22P20gExcFacts) (h1930 : H1930 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    ∃ k : ℕ, IsNaturalClassicalModule (barSub (⊥ : Subgroup G) A hA c.L) k ∧
      (k = c.n ∨ (2 * k = c.n ∧
        IsOmegaMinus ↥(barSub (⊥ : Subgroup G) A hA c.L) 4 k ∧
        NatOmegaMinus (barSub (⊥ : Subgroup G) A hA c.L) ⊤ ⊥ 4 k)) ∧
      ((barSub (⊥ : Subgroup G) A hA c.L).subgroupOf
        (Mbar c.N (⊥ : Subgroup G) A hA)).Normal := by
  classical
  obtain ⟨K, hK, hgen⟩ := c.hL.1.2.2.2
  have hn2 : 2 < c.n := by
    have h3 := c.three_le_n hE h207 h1930
    omega
  have hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA) :=
    isComponentOf_K_Mbar c h208 h1930 hA hAV hAne hAN hK hgen
  have hYH : Mbar c.N (⊥ : Subgroup G) A hA ≤ Subgroup.normalizer
      (((⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) :
          Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))) :
        Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) :=
    le_normalizer_iSup_map_conj _ _
  rcases Ctx23L.eq_L_or_eq_sup_conj_of_mem_calC c hG2 h3D4 h2F4 h2010 h207 h1930
    hA hAV hAne hAN hK hgen with hsingle | hprod
  · exact natural_A_single c hG2 h3D4 h2F4 h145 h128 hDeg h1A h207 h208 h209 h2010 h1930
      hA hAV hAne hAN hmin hK hgen hsingle hn2 hcomp hYH
  · exact natural_A_product c hG2 h3D4 h2F4 h145 h207 h208 h209 h2010 h1930 h1A
      hA hAV hAne hAN hmin hK hgen hprod hn2 hcomp hYH

end CFSG.LocalAnalysis.UniquenessCase.UC22
