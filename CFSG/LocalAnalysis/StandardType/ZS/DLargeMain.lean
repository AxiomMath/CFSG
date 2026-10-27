module

public import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFFour
public import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFNFourFive
import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFPrimCorankOne
import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFDimThreeFive
import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFH4Extend
import CFSG.LocalAnalysis.StandardType.ZS.DLargeInputs
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtFamily
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsNeg
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsOrth
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsImp
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtMain
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelF4Weyl
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH4
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsModels
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableDegThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS



theorem family_of_dLargeFourModel
    {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] (hL : DLargeFourModel p) (hp : p ≠ 2)
    (h4 : Module.finrank (ZMod p) U = 4) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hA : AbsIrred p A) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A)
    (htv : QTwoLin.TransvectionFree A)
    (hd : ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) : Family p A := by
  rcases hL U A hp h4 hgen hA hprim htv hd with horth | hB | hC | hD
  · exact family_of_isOrthType horth
  · obtain ⟨-, f, t, ht, hN4 | hEN4⟩ := hB
    · rw [hN4]; exact family_n4 hp f ht
    · rw [hEN4]; exact family_en4 hp f ht
  · obtain ⟨-, -, f, hF4⟩ := hC
    rw [hF4]
    exact Family.weyl (PrimModel.linWeyl_basisClosure_weylF4Mats hp f)
  · obtain ⟨hp5, hd5, α, f, hα, hH4⟩ := hD
    rw [hH4] at hd5 ⊢
    exact Family.h4 hp5 h4 (PrimModel.card_basisClosure_h4BlockMats hp hp5 f hα)
      (PrimModel.neg_mem_basisClosure_h4BlockMats hp hp5 f hα) hd5
      (PrimModel.oneClass_basisClosure_h4BlockMats hp f hα)



theorem family_of_impExtSetting
    {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (S : ImpExtSetting G H d)
    (I : ImpExtInputs G H) : Family p G := by
  obtain ⟨-, hcases⟩ := ImpExtSetting.eq_weylN4_or_weylEN4_or_weylF4_or_orth hp S I
  rcases hcases with ⟨f, t, ht, hN4⟩ | ⟨f, t, ht, hEN4⟩ | ⟨f, hF4⟩ | ⟨-, f, hPhi'⟩
  · rw [hN4]; exact family_n4 hp f ht
  · rw [hEN4]; exact family_en4 hp f ht
  · rw [hF4]
    exact Family.weyl (PrimModel.linWeyl_basisClosure_weylF4Mats hp f)
  · exact family_of_isOrthType (isOrthType_of_forall_isIsom_phiForm hp f hPhi')

private theorem family_of_dLargeFourModel_of_finrank_four
    {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (hL : DLargeFourModel p)
    (hp : p ≠ 2) (h4 : Module.finrank (ZMod p) U = 4) (hgen : ReflGen p A)
    (hA : AbsIrred p A) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A)
    (htv : QTwoLin.TransvectionFree A)
    (hd : ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    Family p A :=
  family_of_dLargeFourModel hL hp h4 hgen hA hprim htv hd

private theorem family_of_primExtSetting_of_large {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    {A H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (hp : p ≠ 2) (hS : PrimExtSetting A H d)
    (hPC : TFPrimCorankOne p (Module.finrank (ZMod p) U - 1))
    (hneg : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hdeg : DegenerateInput p A 2) (h35 : TFDimThreeFive p) (hL : DLargeFourModel p) :
    Family p A :=
  family_of_primExtSetting hp hS hPC lemmaOneNineInput_holds hneg hdeg h35
    (fun _ => tfH4Extend_of_dLargeFourModel hL)

private theorem family_of_impExtSetting_of_useInputAt
    {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] {A H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}
    (hp : p ≠ 2) (hS : ImpExtSetting A H d) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (hU : ∀ m, 3 ≤ m → m < Module.finrank (ZMod p) U → UseInputAt m)
    (htab : ∀ m < Module.finrank (ZMod p) U, TableFactsAt p m)
    (hPC : TFPrimCorankOne p (Module.finrank (ZMod p) U - 1)) :
    Family p A := by
  refine family_of_impExtSetting hp hS ?_
  exact impExtInputs_of_impExtSetting hp hS (fun m hm => (htab m hm).1)
    (fun m hm => (htab m hm).2.1)
    (tfPrimCorankDim_of_primCorankOne hPC TableFacts.tfH3DataModel_holds)
    (tfDegenerateExtThree_of_useInputAt (l := Module.finrank (ZMod p) U - 1)
      (hU _ (by omega) (by omega)))
    (tfNegOfPrimThree_of_useInputAt (hU 3 (by omega) (by omega)))
    (tfSmallThree_of_useInputAt (hU 3 (by omega) (by omega)))

private theorem family_of_orthOfPrimOrthSub_of_large {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hA : AbsIrred p A)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A) (htv : QTwoLin.TransvectionFree A)
    (hX : ∃ X ≤ A, IsPrimOrthSub p X)
    (hU : ∀ m, 3 ≤ m → m < Module.finrank (ZMod p) U → UseInputAt m)
    (hN : TFNFourFive p) (hD3 : TFDegThree p) : Family p A :=
  family_of_exists_isPrimOrthSub hp h4 hgen hA hprim htv hX
    (tfNegOrGen_of_lt hp hU _ (by omega))
    (tfOrthOvergroup_of_useInputAt hp (by omega) (hU _ (by omega) (by omega)))
    (tfOrthCorankOne_of_useInputAt hp (hU _ (by omega) (by omega)) hN) hD3

private theorem family_of_large_settings
    {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (hp : p ≠ 2)
    (hU : ∀ m, 3 ≤ m → m < Module.finrank (ZMod p) U → UseInputAt m)
    (h4 : 4 ≤ Module.finrank (ZMod p) U) (hn5 : 5 ≤ Module.finrank (ZMod p) U)
    (hgen : ReflGen p A) (hA : AbsIrred p A)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A) (htv : QTwoLin.TransvectionFree A)
    (hd : ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hL : DLargeFourModel p) (h35 : TFDimThreeFive p)
    (hno : ¬ ∃ X ≤ A, IsPrimOrthSub p X) :
    Family p A := by
  have htab : ∀ m < Module.finrank (ZMod p) U, TableFactsAt p m := tableFactsAt_of_lt hp hU
  obtain ⟨d, hdmax, hd3⟩ := exists_dMax_of_isRefl_pair hd
  have hprop : PropOneEightAt p (Module.finrank (ZMod p) U) :=
    propOneEightAt_of_tableFacts hp htab
  have hNsub : ∃ N ≤ A, ReflGen p N ∧ SplitSupport N (Module.finrank (ZMod p) U - 1) ∧
      DMax p N d := hprop h4 U A rfl ⟨hgen, htv⟩ hA.1 hprim d hdmax hd3
  have hPC : TFPrimCorankOne p (Module.finrank (ZMod p) U - 1) := by
    by_cases hcase : Module.finrank (ZMod p) U - 1 = 4
    · rw [hcase]; exact tfPrimCorankOne_four hL
    · have hl : 5 ≤ Module.finrank (ZMod p) U - 1 := by omega
      exact tfPrimCorankOne_of_five_le hl (hU _ (by omega) (by omega))
  obtain ⟨H, hS | hS⟩ :=
    exists_primExtSetting_or_impExtSetting h4 hgen hA hprim htv hdmax hd3 hno hNsub
  · exact family_of_primExtSetting_of_large hp hS hPC (tfNegOrGen_of_lt hp hU _ (by omega))
      (degenerateInput_of_tableFacts A 2 (fun m hm => (htab m hm).1)
        (fun m hm => (htab m hm).2.1)) h35 hL
  · exact family_of_impExtSetting_of_useInputAt hp hS h4 hU htab hPC

private theorem family_of_large_of_five_le
    {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (hp : p ≠ 2)
    (hU : ∀ m, 3 ≤ m → m < Module.finrank (ZMod p) U → UseInputAt m)
    (h4 : 4 ≤ Module.finrank (ZMod p) U) (hn5 : 5 ≤ Module.finrank (ZMod p) U)
    (hgen : ReflGen p A) (hA : AbsIrred p A)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV A) (htv : QTwoLin.TransvectionFree A)
    (hd : ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hL : DLargeFourModel p) (hN : TFNFourFive p) (h35 : TFDimThreeFive p)
    (hD3 : TFDegThree p) :
    Family p A := by
  by_cases hX : ∃ X ≤ A, IsPrimOrthSub p X
  · exact family_of_orthOfPrimOrthSub_of_large hp h4 hgen hA hprim htv hX hU hN hD3
  · exact family_of_large_settings hp hU h4 hn5 hgen hA hprim htv hd hL h35 hX



theorem dLargeCase_holds :
    DLargeCase := by
  intro p _ U _ _ _ A hp hU h4 hgen hA hprim htv hd
  have hU3 : UseInputAt 3 := hU 3 (by omega) (by omega)
  have hL : DLargeFourModel p := dLargeFourModel_holds hU3
  by_cases hfin : Module.finrank (ZMod p) U = 4
  · exact family_of_dLargeFourModel_of_finrank_four hL hp hfin hgen hA hprim htv hd
  · have hn5 : 5 ≤ Module.finrank (ZMod p) U := by omega
    have hN : TFNFourFive p := tfNFourFive_of_dLargeFourModel hL
    have h35 : TFDimThreeFive p := tfDimThreeFive_holds
    have hD3 : TFDegThree p := tfDegThree
    exact family_of_large_of_five_le hp hU h4 hn5 hgen hA hprim htv hd hL hN h35 hD3

end CFSG.StandardType.ZS

end
