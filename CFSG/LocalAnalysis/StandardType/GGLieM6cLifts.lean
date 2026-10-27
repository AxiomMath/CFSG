module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagLift
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType.LieCore.M6c

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

private lemma m6c_rootParams_cube {k K₁ : Type} [Field k] [Field K₁] (ι : k →+* K₁)
    (hroot : ∀ c : kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map ι.toMonoidHom c)
    (b : Fin Tag.E6.rank → kˣ) :
    ∃ u : Fin Tag.E6.rank → K₁ˣ, e6RootParams u = fun l => Units.map ι.toMonoidHom (b l) := by
  choose v hv using fun i => hroot (b i)
  refine ⟨fun l => ∏ i, v i ^ e6CartanAdj i l, funext fun j => ?_⟩
  simp only [e6RootParams, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  simp_rw [← CFSG.LieType.Steinberg.CentralExt.AdjointClosed.zpow_sum_eq_prod, e6CartanAdj_mul]
  rw [Finset.prod_eq_single j (fun i _ hij => by rw [ite_eq_right hij, zpow_zero])
    (fun h => absurd (Finset.mem_univ j) h), ite_eq_left rfl, ← hv j]
  rfl

private lemma m6c_minTorus_mul_comm
    {K : Type} [Field K] (a b : Fin Tag.E6.rank → Kˣ) :
    minTorus e6Data_valid K a * minTorus e6Data_valid K b =
      minTorus e6Data_valid K b * minTorus e6Data_valid K a := by
  rw [← (minTorus e6Data_valid K).map_mul, ← (minTorus e6Data_valid K).map_mul, mul_comm]

private lemma m6c_commutator_formula
    {K : Type} [Field K] (u' vv : Fin Tag.E6.rank → Kˣ) (ω : List (Fin Tag.E6.rank))
    (n₁ : e6Data_valid.minGroup K)
    (hconj : n₁ * minTorus e6Data_valid K vv * n₁⁻¹ =
      minTorus e6Data_valid K (ω.foldr e6StarS vv)) :
    (minTorus e6Data_valid K u' * n₁) * minTorus e6Data_valid K vv *
        (minTorus e6Data_valid K u' * n₁)⁻¹ * (minTorus e6Data_valid K vv)⁻¹ =
      minTorus e6Data_valid K (ω.foldr e6StarS vv * vv⁻¹) := by
  have hcommT : minTorus e6Data_valid K u' * minTorus e6Data_valid K (ω.foldr e6StarS vv) =
      minTorus e6Data_valid K (ω.foldr e6StarS vv) * minTorus e6Data_valid K u' :=
    m6c_minTorus_mul_comm u' (ω.foldr e6StarS vv)
  have e1 : (minTorus e6Data_valid K u' * n₁) * minTorus e6Data_valid K vv *
        (minTorus e6Data_valid K u' * n₁)⁻¹ * (minTorus e6Data_valid K vv)⁻¹ =
      minTorus e6Data_valid K u' * (n₁ * minTorus e6Data_valid K vv * n₁⁻¹) *
        (minTorus e6Data_valid K u')⁻¹ * (minTorus e6Data_valid K vv)⁻¹ := by
    rw [mul_inv_rev]
    simp only [mul_assoc]
  have hconjT : minTorus e6Data_valid K u' *
      minTorus e6Data_valid K (ω.foldr e6StarS vv) *
      (minTorus e6Data_valid K u')⁻¹ =
      minTorus e6Data_valid K (ω.foldr e6StarS vv) := by
    calc minTorus e6Data_valid K u' * minTorus e6Data_valid K (ω.foldr e6StarS vv) *
          (minTorus e6Data_valid K u')⁻¹
        = minTorus e6Data_valid K (ω.foldr e6StarS vv) * minTorus e6Data_valid K u' *
            (minTorus e6Data_valid K u')⁻¹ := by rw [hcommT]
      _ = minTorus e6Data_valid K (ω.foldr e6StarS vv) := by
            rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [e1, hconj, hconjT, ← (minTorus e6Data_valid K).map_inv,
    ← (minTorus e6Data_valid K).map_mul]

private lemma m6c_conj_comm_eq_one {G : Type} [Group G] (S T : G) (h : S * T = T * S) :
    S * T * S⁻¹ * T⁻¹ = 1 := by
  rw [h]
  group

private lemma m6c_eq_one_of_minTorus_eq_one
    {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ)
    (h : minTorus e6Data_valid K a = 1) : a = 1 := by
  rw [← (minTorus_injective e6Data_valid K).eq_iff, h, map_one]

private lemma m6c_zpow_eq_one {K : Type} [Field K] (ζ : Kˣ) (vv : Fin Tag.E6.rank → Kˣ)
    (m : Fin Tag.E6.rank → ℤ) (ω : List (Fin Tag.E6.rank)) (w : WeylGroup Tag.E6)
    (hprod : ω.foldr e6StarS vv * vv⁻¹ = 1)
    (hfold : ω.foldr e6StarS vv = fun l => ζ ^ ((w • m) l))
    (hv : vv = fun l => ζ ^ m l) (l : Fin Tag.E6.rank) :
    ζ ^ ((w • m) l - m l) = 1 := by
  have h1 : (ω.foldr e6StarS vv) l * (vv l)⁻¹ = 1 := by
    have h := congrFun hprod l
    simpa only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply] using h
  rw [hfold] at h1
  rw [hv] at h1
  rw [zpow_sub]
  exact h1

private lemma m6c_orderOf_map {k K : Type} [Field k] [Field K] (ι : k →+* K)
    (hι : Function.Injective ι) (η : kˣ) (hη : orderOf η = 9) :
    orderOf (Units.map ι.toMonoidHom η) = 9 := by
  have h1 : orderOf (Units.map ι.toMonoidHom η) = orderOf η :=
    orderOf_injective (Units.map ι.toMonoidHom) (Units.map_injective hι) η
  rw [h1, hη]

private lemma m6c_dvd_of_orderOf {G : Type} [Group G] {ζ : G} (horder : orderOf ζ = 9)
    {d : ℤ} (h : ζ ^ d = 1) : (9 : ℤ) ∣ d := by
  have h9 := (orderOf_dvd_iff_zpow_eq_one (x := ζ)).2 h
  rwa [horder] at h9

private lemma m6c_orderOf_eq_nine {k K : Type} [Field k] [Field K] (ι : k →+* K)
    (hι : Function.Injective ι) (η : kˣ) (hη : orderOf η = 9) {ζ : Kˣ}
    (hζ : ζ = Units.map ι.toMonoidHom η) : orderOf ζ = 9 := by
  rw [hζ]
  exact m6c_orderOf_map ι hι η hη

private lemma m6c_contradiction {K : Type} [Field K] (ζ : Kˣ) (vv : Fin Tag.E6.rank → Kˣ)
    (m : Fin Tag.E6.rank → ℤ) (ω : List (Fin Tag.E6.rank)) (w : WeylGroup Tag.E6)
    (hprod : ω.foldr e6StarS vv * vv⁻¹ = 1)
    (hv : vv = fun l => ζ ^ m l)
    (hfold : ω.foldr e6StarS vv = fun l => ζ ^ ((w • m) l))
    (horder : orderOf ζ = 9)
    (hm : ∃ l, ¬ ((9 : ℤ) ∣ (w • m) l - m l)) : False := by
  obtain ⟨l, hl⟩ := hm
  exact hl (m6c_dvd_of_orderOf horder (m6c_zpow_eq_one ζ vv m ω w hprod hfold hv l))

private lemma m6c_decompose {k : Type} [Field k]
    (n : ModGL Tag.E6 k) (w : WeylGroup Tag.E6)
    (hnm : n ∈ monomialSubgroup Tag.E6 k) (hnw : MapsRootLines n w) :
    ∃ b : Fin Tag.E6.rank → kˣ, n = rootDiagUnit Tag.E6 b *
      canonicalRep (coxeterSystem Tag.E6) k w := by
  obtain ⟨w₁, t, ht, hgt⟩ := exists_torus_mul_canonicalRep_of_mem_monomial hnm
  have hmaps : MapsRootLines (t * canonicalRep (coxeterSystem Tag.E6) k w₁) w₁ := by
    simpa using (mapsRootLines_of_mem_torusGroup ht).mul (mapsRootLines_canonicalRep w₁)
  have hmaps' : MapsRootLines n w₁ := by rw [hgt]; exact hmaps
  have hw : w = w₁ := MapsRootLines.unique hnw hmaps'
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  refine ⟨b, ?_⟩
  rw [hgt, hb, hw]

private lemma m6c_commutator
    (k : Type) [Field k] [Finite k] (η : kˣ) (hη : orderOf η = 9)
    (w : WeylGroup Tag.E6) (m : Fin Tag.E6.rank → ℤ)
    (hm : ∃ l, ¬ ((9 : ℤ) ∣ (w • m) l - m l))
    {b : Fin Tag.E6.rank → kˣ} (x : e6Data_valid.minGroup k)
    (hx : ((e6Isogeny k x : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) k w) :
    x * minTorus e6Data_valid k (fun l => η ^ m l) ≠
      minTorus e6Data_valid k (fun l => η ^ m l) * x := by
  intro hxy
  obtain ⟨K₁, hK₁fin, hroot⟩ := exists_cubeExt k
  haveI : Finite K₁ := hK₁fin
  let ι : k →+* K₁ := algebraMap k K₁
  have hιinj : Function.Injective ι := (algebraMap k K₁).injective
  obtain ⟨u', hu'⟩ := m6c_rootParams_cube ι hroot b
  obtain ⟨ω, hω, hw⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  set x₁ := minBC e6Data_valid ι x with hx₁
  set yy := minTorus e6Data_valid k (fun l => η ^ m l) with hyy
  set y₁ := minBC e6Data_valid ι yy with hy₁
  set ζ : K₁ˣ := Units.map ι.toMonoidHom η with hζ
  set vv : Fin Tag.E6.rank → K₁ˣ := fun l => ζ ^ m l with hv
  have hy₁T : y₁ = minTorus e6Data_valid K₁ vv := by
    rw [hy₁, hyy, minBC_minTorus_E6]
    congr 1
    funext l
    rw [hv]
    exact map_zpow (Units.map ι.toMonoidHom) η (m l)
  set n₁ := e6NWord K₁ ω with hn₁
  set T := minTorus e6Data_valid K₁ vv with hT
  set S := minTorus e6Data_valid K₁ u' * n₁ with hS
  have hπx : ((e6Isogeny K₁ x₁ : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
      rootDiagUnit Tag.E6 (fun l => Units.map ι.toMonoidHom (b l)) *
        canonicalRep (coxeterSystem Tag.E6) K₁ w := by
    rw [hx₁, e6Isogeny_minBC, hx, map_mul, baseChangeGL_rootDiagUnit,
      baseChangeGL_canonicalRep]
  have hπS : ((e6Isogeny K₁ S : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
      rootDiagUnit Tag.E6 (fun l => Units.map ι.toMonoidHom (b l)) *
        canonicalRep (coxeterSystem Tag.E6) K₁ w := by
    rw [hS, map_mul, Subgroup.coe_mul, e6Isogeny_minTorus, hu',
      e6Isogeny_nWord_eq_canonicalRep hω, hw]
  set z := x₁ * S⁻¹ with hz
  have hzπ : ((e6Isogeny K₁ z : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) = 1 := by
    rw [hz, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hπx, hπS]
    group
  have hzc : z ∈ Subgroup.center (e6Data_valid.minGroup K₁) :=
    mem_center_of_isogeny_eq_one hzπ
  have hx₁_eq : x₁ = z * S := by rw [hz]; group
  have hx₁y₁ : x₁ * y₁ = y₁ * x₁ := by
    rw [hx₁, hy₁, ← map_mul, hxy, map_mul]
  have hST : S * T = T * S := by
    have hzcT := Subgroup.mem_center_iff.1 hzc T
    rw [hx₁_eq, hy₁T] at hx₁y₁
    have h2 : T * (z * S) = z * (T * S) := by
      calc T * (z * S) = (T * z) * S := (mul_assoc T z S).symm
        _ = (z * T) * S := by rw [← hzcT]
        _ = z * (T * S) := mul_assoc z T S
    have h : z * (S * T) = z * (T * S) := by
      calc z * (S * T) = (z * S) * T := (mul_assoc z S T).symm
        _ = T * (z * S) := hx₁y₁
        _ = z * (T * S) := h2
    exact mul_left_cancel h
  have hconj : n₁ * minTorus e6Data_valid K₁ vv * n₁⁻¹ =
      minTorus e6Data_valid K₁ (ω.foldr e6StarS vv) := by
    rw [hn₁, nWord_conj_minTorus]
  have hST'' : S * T * S⁻¹ * T⁻¹ =
      minTorus e6Data_valid K₁ (ω.foldr e6StarS vv * vv⁻¹) := by
    rw [hS, hT]
    exact m6c_commutator_formula u' vv ω n₁ hconj
  have hone : minTorus e6Data_valid K₁ (ω.foldr e6StarS vv * vv⁻¹) = 1 := by
    rw [← hST'']
    exact m6c_conj_comm_eq_one S T hST
  have hprod : ω.foldr e6StarS vv * vv⁻¹ = 1 :=
    m6c_eq_one_of_minTorus_eq_one (ω.foldr e6StarS vv * vv⁻¹) hone
  have hfold : ω.foldr e6StarS vv = fun l => ζ ^ ((w • m) l) := by
    rw [foldr_e6StarS_zpow (k := K₁) ζ ω m]
    congr 1
    funext l
    rw [hw, wordProd_smul_eq_foldr]
  exact m6c_contradiction ζ vv m ω w hprod hv hfold
    (m6c_orderOf_eq_nine ι hιinj η hη hζ) hm

theorem e6_exists_noncommuting_lifts
    (k : Type) [Field k] [Finite k] (η : kˣ) (hη : orderOf η = 9)
    (n : ModGL Tag.E6 k) (w : WeylGroup Tag.E6) (hn : n ∈ adjointGroup Tag.E6 k)
    (hnm : n ∈ monomialSubgroup Tag.E6 k) (hnw : MapsRootLines n w) (m : Fin Tag.E6.rank → ℤ)
    (hcomm : n * rootDiagUnit Tag.E6 (e6RootParams fun l => η ^ m l) =
      rootDiagUnit Tag.E6 (e6RootParams fun l => η ^ m l) * n)
    (hm : ∃ l, ¬ ((9 : ℤ) ∣ (w • m) l - m l)) :
    ∃ x y : ↥(e6Data_valid.minGroup k), (e6Isogeny k x : ModGL Tag.E6 k) = n ∧
      (e6Isogeny k y : ModGL Tag.E6 k) = rootDiagUnit Tag.E6 (e6RootParams fun l => η ^ m l) ∧
      x * y ≠ y * x := by
  obtain ⟨b, hb⟩ := m6c_decompose n w hnm hnw
  obtain ⟨x, hx⟩ := e6Isogeny_surjective k ⟨n, hn⟩
  have hx' : ((e6Isogeny k x : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = n :=
    congrArg Subtype.val hx
  refine ⟨x, minTorus e6Data_valid k (fun l => η ^ m l), hx',
    e6Isogeny_minTorus (fun l => η ^ m l), ?_⟩
  exact m6c_commutator k η hη w m hm x (by rw [hx', hb])

end CFSG.StandardType.LieCore.M6c
