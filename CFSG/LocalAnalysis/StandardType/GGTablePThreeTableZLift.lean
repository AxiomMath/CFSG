module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6

import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourSc
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.PairAuxSc
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.PartOne.KE.E7FiveBlock

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem tableZ_lift_cube
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (x : ↥(TwistedE6.fixedGroup K σ.toRingHom))
    (w : ModGL Tag.E6 (AlgebraicClosure K)) (hw : w ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (u : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) (hu : ∀ l, u l ^ 3 = 1)
    (hx : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e6IsogenyFixed σ.toRingHom x) =
      w * rootDiagUnit Tag.E6 (e6RootParams u) * w⁻¹) :
    x ^ 3 = 1 := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  set x₀ : CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup K := (x : CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup K) with hx₀
  set y : ModGL Tag.E6 K := e6IsogenyFixed σ.toRingHom x with hy
  have hyK : ((e6Isogeny K x₀ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = y := by
    rw [hy, hx₀]
    rfl
  obtain ⟨S, hS⟩ := exists_finset_descent (τ := Tag.E6) hw
  obtain ⟨E, hEfin, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) (L := L)
    (S ∪ Finset.univ.image (fun l => ((u l : Lˣ) : L)))
  haveI : Finite E := hEfin
  have hSE' : (S : Set L) ⊆ (E : Set L) := fun s hs =>
    hSE (Finset.mem_coe.2 (Finset.mem_union_left _ hs))
  have huE : ∀ l, (u l : L) ∈ E := fun l =>
    hSE (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ l))))
  obtain ⟨wE, hwE, hwEbc⟩ := hS E hSE'
  obtain ⟨uE, huEdef⟩ := exists_units_descent E u huE
  obtain ⟨ιE, hιE⟩ : ∃ ιE : K →+* E, E.subtype.comp ιE = ι :=
    ⟨ι.codRestrict E fun c => by rw [hι]; exact hKE ⟨c, rfl⟩, RingHom.ext fun _ => rfl⟩
  have hbcι : ∀ g : ModGL Tag.E6 K,
      baseChangeGL E.subtype (baseChangeGL ιE g) = baseChangeGL ι g := by
    intro g
    rw [baseChangeGL_baseChangeGL, hιE]
  have hpar : (fun l => Units.map E.subtype.toMonoidHom (e6RootParams uE l)) =
      e6RootParams u := by
    rw [← huEdef]
    funext l
    simp only [e6RootParams, map_prod, map_zpow]
  have hd : baseChangeGL E.subtype (rootDiagUnit Tag.E6 (e6RootParams uE)) =
      rootDiagUnit Tag.E6 (e6RootParams u) := by
    rw [baseChangeGL_rootDiagUnit, hpar]
  have hxE : baseChangeGL ιE y = wE * rootDiagUnit Tag.E6 (e6RootParams uE) * wE⁻¹ := by
    apply baseChangeGL_injective (τ := Tag.E6) E.subtype
    rw [hbcι y, map_mul, map_mul, map_inv, hwEbc, hd]
    exact hx
  obtain ⟨W, hW⟩ := e6Isogeny_surjective E ⟨wE, hwE⟩
  have hW' : ((e6Isogeny E W : adjointGroup Tag.E6 E) : ModGL Tag.E6 E) = wE :=
    congrArg Subtype.val hW
  obtain ⟨T, hT⟩ : ∃ T : CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup E,
      T = CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus CFSG.LieType.Steinberg.Minuscule.e6Data_valid E uE :=
    ⟨_, rfl⟩
  have hπT : ((e6Isogeny E T : adjointGroup Tag.E6 E) : ModGL Tag.E6 E) =
      rootDiagUnit Tag.E6 (e6RootParams uE) := by
    rw [hT]
    exact e6Isogeny_minTorus uE
  set a : CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup E := minBC CFSG.LieType.Steinberg.Minuscule.e6Data_valid ιE x₀ with ha
  set b : CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup E := W * T * W⁻¹ with hb
  have hπa : ((e6Isogeny E a : adjointGroup Tag.E6 E) : ModGL Tag.E6 E) =
      wE * rootDiagUnit Tag.E6 (e6RootParams uE) * wE⁻¹ := by
    rw [ha, e6Isogeny_minBC, hyK, hxE]
  have hπb : ((e6Isogeny E b : adjointGroup Tag.E6 E) : ModGL Tag.E6 E) =
      wE * rootDiagUnit Tag.E6 (e6RootParams uE) * wE⁻¹ := by
    rw [hb]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hW', hπT]
  have hπab : ((e6Isogeny E a : adjointGroup Tag.E6 E) : ModGL Tag.E6 E) =
      ((e6Isogeny E b : adjointGroup Tag.E6 E) : ModGL Tag.E6 E) := hπa.trans hπb.symm
  obtain ⟨z, hz⟩ : ∃ z : CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup E, z = a * b⁻¹ := ⟨_, rfl⟩
  have hzker : ((e6Isogeny E z : adjointGroup Tag.E6 E) : ModGL Tag.E6 E) = 1 := by
    rw [hz]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hπab]
    group
  have hzc : z ∈ Subgroup.center (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup E) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.mem_center_of_isogeny_eq_one hzker
  have hazb : a = z * b := by rw [hz]; group
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨v, hv, hv3⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.exists_minTorus_of_mem_center_E6 hzc
    rw [hv, ← map_pow]
    have hvv : v ^ 3 = 1 := funext fun j => hv3 j
    rw [hvv, map_one]
  have huE3 : uE ^ 3 = 1 := by
    funext l
    change uE l ^ 3 = 1
    apply units_map_subtype_injective E
    rw [map_pow, congrFun huEdef l, hu l, map_one]
  have hT3 : T ^ 3 = 1 := by
    rw [hT, ← map_pow, huE3, map_one]
  have hb3 : b ^ 3 = 1 := by
    rw [hb, conj_pow, hT3, mul_one, mul_inv_cancel]
  have hcomm : Commute z b := (Subgroup.mem_center_iff.1 hzc b).symm
  have ha3 : a ^ 3 = 1 := by
    rw [hazb, hcomm.mul_pow 3, hz3, hb3, mul_one]
  have hx03 : x₀ ^ 3 = 1 := by
    apply CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux.minBC_injective
      CFSG.LieType.Steinberg.Minuscule.e6Data_valid ιE
    rw [map_pow, ← ha, ha3, map_one]
  exact Subtype.ext (by
    rw [Subgroup.coe_pow, OneMemClass.coe_one, ← hx₀]
    exact hx03)

end CFSG.StandardType.TablePThreeKG

end
