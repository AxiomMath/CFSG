module

public import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFDefs
public import CFSG.LocalAnalysis.StandardType.ZS.DLargeSetting
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtDeg
public import CFSG.LocalAnalysis.StandardType.ZS.TableFactsDefs
import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFPrimCorankOne
import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFDimThreeFive
import CFSG.LocalAnalysis.StandardType.ZS.TableLow
import CFSG.LocalAnalysis.StandardType.ZS.TableMain
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsOrth
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsImp
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsWeyl
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtMain
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH4
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtMain
import CFSG.LocalAnalysis.StandardType.ZS.DLargeInputs
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsModels
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableDegThree
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH3
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelJ34
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelF4
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS



theorem tableFactsAt_of_lt {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ}
    (hU : ∀ m, 3 ≤ m → m < n → UseInputAt m) : ∀ m < n, TableFactsAt p m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases h3 : 3 ≤ m
    · exact tableFactsAt_of_useInputAt hp h3 (hU m h3 hm)
        (propOneEightAt_of_tableFacts hp fun k hk => ih k hk (by omega))
    · have hm2 : m ≤ 2 := by omega
      interval_cases m
      · exact tableFactsAt_of_le_one (m := 0) (by omega)
      · exact tableFactsAt_of_le_one (m := 1) (by omega)
      · exact tableFactsAt_two hp



variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem orderOf_mul_le_four_of_mem_g2mmn_of_orderOf_dvd_two {n : ℕ} (hp : p ≠ 2)
    (b : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hζ : orderOf ζ ∣ 2) {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ g2mmn p b i₀ i₁ ζ)
    (hy : y ∈ g2mmn p b i₀ i₁ ζ) (hxr : IsRefl p x) (hyr : IsRefl p y) :
    orderOf (x * y) ≤ 4 := by
  rcases TableFacts.orderOf_mul_le_four_or_dvd_of_mem_g2mmn hp b hi ζ hx hy hxr hyr with
    h4 | hdvd
  · exact h4
  · have hlcm : Nat.lcm 2 (orderOf ζ) = 2 :=
      Nat.dvd_antisymm (Nat.lcm_dvd_iff.mpr ⟨dvd_rfl, hζ⟩) (Nat.dvd_lcm_left 2 (orderOf ζ))
    rw [hlcm] at hdvd
    exact le_trans (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)



theorem ImpExtSetting.eq_four_of_impExtInputs (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (S : ImpExtSetting G H d)
    (I : ImpExtInputs G H) : d = 4 := by
  obtain ⟨e, j₀, j₁, ζ, hne, hmono⟩ := S.exists_standardBasis hp
  let Std : ImpExtStd G H d e j₀ j₁ ζ := ⟨S, hne, hmono⟩
  obtain ⟨-, hgmmn, hg2mmn⟩ := Std.impExtRowM hp I
  rcases hmono with hm | hm
  · exact ImpExtStd.dmax_eq_four hp Std (hgmmn hm)
  · rcases hg2mmn hm with hζ2 | hζ4
    · have hD : DMax p (movedGroup H) d :=
        (dmax_movedGroup_iff S.splitSupport d).2 S.dmax_H
      obtain ⟨-, x, hx, y, hy, hxr, hyr, hord⟩ := hD
      rw [hm] at hx hy
      have hle : d ≤ 4 := by
        rw [← hord]
        exact orderOf_mul_le_four_of_mem_g2mmn_of_orderOf_dvd_two hp e hne hζ2 hx hy hxr hyr
      exact le_antisymm hle (Nat.succ_le_of_lt S.three_lt)
    · exact ImpExtStd.dmax_eq_four hp Std hζ4

private theorem tableFactsAt_of_lt_four (hp : p ≠ 2) (hU3 : UseInputAt 3) :
    ∀ k < 4, TableFactsAt p k :=
  tableFactsAt_of_lt hp (n := 4) (fun m hm3 hmn => by
    have h : m = 3 := by omega
    rw [h]
    exact hU3)

private theorem primExtSetting_eq_h4BlockMats_of_finrank_four (hp : p ≠ 2)
    [Module.Finite (ZMod p) U]
    {A H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (S : PrimExtSetting A H d)
    (hdim : Module.finrank (ZMod p) U = 4)
    (hpc : TFPrimCorankOne p 3) (hneg : ∀ m < 4, TFNegOrGen p m)
    (hcop : ∀ m < 4, TFCoprimeWitness p m) (h35 : TFDimThreeFive p)
    (hH3 : TFH3Model p) (hpair : TFH3Pair p) (hJ : TFJ34Model p) (hF : TFF4Model p)
    (hH5 : TFH4Model5 p) (hH4 : TFH4Model p) :
    p ≠ 5 ∧ DMax p A 5 ∧ ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) U),
      α ^ 2 = α + 1 ∧ A = basisClosure f (h4BlockMats α) := by
  have hpc' : TFPrimCorankOne p (Module.finrank (ZMod p) U - 1) := by
    simpa [hdim] using hpc
  have hneg' : TFNegOrGen p (Module.finrank (ZMod p) U - 1) := by
    simpa [hdim] using hneg 3 (by norm_num)
  have hdeg : DegenerateInput p A 2 :=
    degenerateInput_of_tableFacts A 2 (fun m hm => hneg m (by omega))
      (fun m hm => hcop m (by omega))
  obtain ⟨-, hd5, hp5, α, f, hα, hAeq⟩ :=
    S.exists_basis_eq_h4BlockMats hp hpc' lemmaOneNineInput_holds hneg' hdeg h35
      (fun h => absurd h (by omega)) hH3 hpair hJ hF hH5 hH4
  exact ⟨hp5, hd5 ▸ S.dmax, α, f, hα, hAeq⟩

private theorem impExtCases_of_finrank_four (hp : p ≠ 2) {A H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}
    (S : ImpExtSetting A H d) (hd4 : d = 4)
    (hcases : (∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p), t ^ 2 = -1 ∧
        A = basisClosure f (weylN4Mats t)) ∨
      (∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p), t ^ 2 = -1 ∧
        A = basisClosure f (weylEN4Mats t)) ∨
      (∃ f : Module.Basis (Fin 4) (ZMod p) U, A = basisClosure f weylF4Mats) ∨
      (p = 3 ∧ ∃ f : Module.Basis (Fin 4) (ZMod p) U, ∀ g, g ∈ A ↔ IsIsom p (phiForm f) g)) :
    IsOrthType p A ∨
      (DMax p A 4 ∧ ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p), t ^ 2 = -1 ∧
        (A = basisClosure f (weylN4Mats t) ∨ A = basisClosure f (weylEN4Mats t))) ∨
      (p ≠ 3 ∧ DMax p A 4 ∧ ∃ f : Module.Basis (Fin 4) (ZMod p) U,
        A = basisClosure f weylF4Mats) ∨
      (p ≠ 5 ∧ DMax p A 5 ∧ ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) U),
        α ^ 2 = α + 1 ∧ A = basisClosure f (h4BlockMats α)) := by
  rcases hcases with ⟨f, t, ht2, hAeq⟩ | ⟨f, t, ht2, hAeq⟩ | ⟨f, hAeq⟩ | ⟨hp3, f, hiff⟩
  · exact Or.inr (Or.inl ⟨hd4 ▸ S.dmax, f, t, ht2, Or.inl hAeq⟩)
  · exact Or.inr (Or.inl ⟨hd4 ▸ S.dmax, f, t, ht2, Or.inr hAeq⟩)
  · by_cases hp3 : p = 3
    · exact Or.inl (hAeq.symm ▸ TableFacts.isOrthType_basisClosure_weylF4_three hp3 f)
    · exact Or.inr (Or.inr (Or.inl ⟨hp3, hd4 ▸ S.dmax, f, hAeq⟩))
  · exact Or.inl (isOrthType_of_forall_isIsom_phiForm hp f hiff)

private theorem impExtSetting_cases_of_finrank_four (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {A H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (S : ImpExtSetting A H d)
    (hdim : Module.finrank (ZMod p) U = 4)
    (hpc : TFPrimCorankOne p 3) (hneg : ∀ m < 4, TFNegOrGen p m)
    (hcop : ∀ m < 4, TFCoprimeWitness p m)
    (hI3 : TFNegOfPrimThree p) (hS3 : TFSmallThree p) (hH3 : TFH3DataModel p) :
    IsOrthType p A ∨
      (DMax p A 4 ∧ ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p), t ^ 2 = -1 ∧
        (A = basisClosure f (weylN4Mats t) ∨ A = basisClosure f (weylEN4Mats t))) ∨
      (p ≠ 3 ∧ DMax p A 4 ∧ ∃ f : Module.Basis (Fin 4) (ZMod p) U,
        A = basisClosure f weylF4Mats) ∨
      (p ≠ 5 ∧ DMax p A 5 ∧ ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) U),
        α ^ 2 = α + 1 ∧ A = basisClosure f (h4BlockMats α)) := by
  have hpc' : TFPrimCorankOne p (Module.finrank (ZMod p) U - 1) := by
    simpa [hdim] using hpc
  have hneg' : ∀ m < Module.finrank (ZMod p) U, TFNegOrGen p m :=
    fun m hm => hneg m (by omega)
  have hcop' : ∀ m < Module.finrank (ZMod p) U, TFCoprimeWitness p m :=
    fun m hm => hcop m (by omega)
  have hT1 : TFPrimCorank p (Module.finrank (ZMod p) U - 1) :=
    tfPrimCorankDim_of_primCorankOne hpc' hH3
  have hT2 : TFDegenerateExt p (Module.finrank (ZMod p) U - 1) :=
    fun W _ _ _ X hp3 hl => absurd hl (by omega)
  have hI : ImpExtInputs A H :=
    impExtInputs_of_impExtSetting hp S hneg' hcop' hT1 hT2 hI3 hS3
  have hd4 : d = 4 := ImpExtSetting.eq_four_of_impExtInputs hp S hI
  obtain ⟨-, hcases⟩ := ImpExtSetting.eq_weylN4_or_weylEN4_or_weylF4_or_orth hp S hI
  exact impExtCases_of_finrank_four hp S hd4 hcases

private theorem dLargeFourModel_case_of_finrank_four (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hU3 : UseInputAt 3)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hdim : Module.finrank (ZMod p) U = 4)
    (hgen : ReflGen p A) (hA : AbsIrred p A) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A)
    (htv : QTwoLin.TransvectionFree A) {d : ℕ} (hd : DMax p A d) (hd3 : 3 < d)
    (hX : ¬ ∃ X ≤ A, IsPrimOrthSub p X)
    {N : Subgroup (U ≃ₗ[ZMod p] U)} (hNle : N ≤ A) (hNgen : ReflGen p N)
    (hNsplit : SplitSupport N (Module.finrank (ZMod p) U - 1)) (hNd : DMax p N d)
    (hfacts : ∀ k < 4, TableFactsAt p k)
    (hpc : TFPrimCorankOne p 3) (h35 : TFDimThreeFive p) :
    IsOrthType p A ∨
      (DMax p A 4 ∧ ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p), t ^ 2 = -1 ∧
        (A = basisClosure f (weylN4Mats t) ∨ A = basisClosure f (weylEN4Mats t))) ∨
      (p ≠ 3 ∧ DMax p A 4 ∧ ∃ f : Module.Basis (Fin 4) (ZMod p) U,
        A = basisClosure f weylF4Mats) ∨
      (p ≠ 5 ∧ DMax p A 5 ∧ ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) U),
        α ^ 2 = α + 1 ∧ A = basisClosure f (h4BlockMats α)) := by
  have hneg : ∀ m < 4, TFNegOrGen p m := fun m hm => (hfacts m hm).1
  have hcop : ∀ m < 4, TFCoprimeWitness p m := fun m hm => (hfacts m hm).2.1
  obtain ⟨H, hH⟩ :=
    exists_primExtSetting_or_impExtSetting (by omega) hgen hA hprim htv hd hd3 hX
      ⟨N, hNle, hNgen, hNsplit, hNd⟩
  rcases hH with hPrim | hImpS
  · exact Or.inr (Or.inr (Or.inr (primExtSetting_eq_h4BlockMats_of_finrank_four hp hPrim hdim hpc
      hneg hcop h35 tfH3Model_holds tfH3Pair_holds tfJ34Model_holds tfF4Model_holds
      tfH4Model5_holds
      tfH4Model_holds)))
  · exact impExtSetting_cases_of_finrank_four hp hImpS hdim hpc hneg hcop
      (tfNegOfPrimThree_of_useInputAt hU3)
      (tfSmallThree_of_useInputAt hU3) TableFacts.tfH3DataModel_holds

private theorem isOrthType_of_exists_isPrimOrthSub_of_finrank_four (hp : p ≠ 2)
    [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hdim : Module.finrank (ZMod p) U = 4)
    (hgen : ReflGen p A) (hA : AbsIrred p A) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A)
    (htv : QTwoLin.TransvectionFree A) (hX : ∃ X ≤ A, IsPrimOrthSub p X)
    (hneg : ∀ m < 4, TFNegOrGen p m) (hT1 : TFOrthOvergroup p 3) (hT5 : TFDegThree p) :
    IsOrthType p A := by
  have hneg' : TFNegOrGen p (Module.finrank (ZMod p) U - 1) := by
    simpa [hdim] using hneg 3 (by norm_num)
  have hT1' : TFOrthOvergroup p (Module.finrank (ZMod p) U - 1) := by
    simpa [hdim] using hT1
  exact isOrthType_of_exists_isPrimOrthSub hp (by omega) hgen hA hprim htv hX hneg' hT1'
    (fun h => absurd h (by omega)) hT5



theorem dLargeFourModel_holds
    (hU3 : UseInputAt 3) :
    DLargeFourModel p := by
  intro U _ _ _ A hp hdim hgen hA hprim htv hpair
  have hfacts : ∀ k < 4, TableFactsAt p k := tableFactsAt_of_lt_four hp hU3
  obtain ⟨d, hd, hd3⟩ := exists_dMax_of_isRefl_pair hpair
  obtain ⟨N, hNle, hNgen, hNsplit, hNd⟩ :=
    (propOneEightAt_of_tableFacts hp (m := 4) hfacts) (by omega) U A hdim ⟨hgen, htv⟩ hA.1 hprim
      d hd hd3
  by_cases hX : ∃ X ≤ A, IsPrimOrthSub p X
  · exact Or.inl (isOrthType_of_exists_isPrimOrthSub_of_finrank_four hp hdim hgen hA hprim htv hX
      (fun m hm => (hfacts m hm).1)
      (tfOrthOvergroup_of_useInputAt hp (m := 3) (by norm_num) hU3) tfDegThree)
  · exact dLargeFourModel_case_of_finrank_four hp hU3 hdim hgen hA hprim htv hd hd3 hX hNle hNgen
      (by simpa [hdim] using hNsplit) hNd hfacts tfPrimCorankOne_three tfDimThreeFive_holds

end CFSG.StandardType.ZS

end
