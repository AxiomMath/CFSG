module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEToral
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourLang
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourFusion
import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.RankThree.PartOne.KE.SuzukiDescent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M24
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
import CFSG.RankThree.PartOne.KE.Basic
import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType.E6OutdiagPpd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.LieType.AlgebraicGroups

theorem ggInndiagToral_of_twist_mem_kernelReflectionGroup
    {K : Type} [Field K] [Finite K]
    (D : LangDatum Tag.E6 (AlgebraicClosure K)) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hΦ : D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup Tag.E6} (hn : D.n = canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
    (x : TableBExc.E6Three.hatGroup Tag.E6 K) {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (hda : rootDiagUnit Tag.E6 a =
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) * D.g0)
    (hw : w ∈ kernelReflectionGroup a) :
    LayerSixE.GGInndiagToral Tag.E6 K (Subgroup.zpowers (TableBExc.E6Three.hatAut Tag.E6 K x)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n', hpn, hcard⟩ := FiniteField.card K (ringChar K)
  obtain ⟨p, hp⟩ : ∃ p, p = ringChar K := ⟨_, rfl⟩
  rw [← hp] at hpn hcard
  haveI : Fact p.Prime := ⟨hpn⟩
  haveI : CharP K p := hp ▸ ringChar.charP K
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = (n' : ℕ) := ⟨_, rfl⟩
  have hK : Nat.card K = p ^ e := by rw [Nat.card_eq_fintype_card, hcard, he]
  have he1 : 1 ≤ e := by
    rw [he]
    exact n'.pos
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hFrEq : Fr = iterateFrobenius (AlgebraicClosure K) p e :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def, hK]
  have hFGL : ∀ g : ModGL Tag.E6 (AlgebraicClosure K),
      entrywiseFrobGL Tag.E6 (AlgebraicClosure K) p e g = Units.map (entrywiseHom Fr) g := fun g => by
    rw [hFrEq]
  have hFix : ∀ y : ModGL Tag.E6 K,
      Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) y := by
    intro y
    have hcomp : Fr.comp (algebraMap K (AlgebraicClosure K)) = algebraMap K (AlgebraicClosure K) := by
      refine RingHom.ext fun c => ?_
      change Fr (algebraMap K (AlgebraicClosure K) c) = algebraMap K (AlgebraicClosure K) c
      rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hcomp]
  have hwa : w ∈ rootCharStabilizerSubgroup a := kernelReflectionGroup_le a hw
  have hnC : D.n ∈ toralCentralizer Tag.E6 (AlgebraicClosure K) a := by
    rw [hn]
    exact canonicalRep_mem_toralCentralizer hwa
  have hnd : D.n * rootDiagUnit Tag.E6 a * D.n⁻¹ = rootDiagUnit Tag.E6 a := by
    have h := (mem_toralCentralizer.1 hnC).2
    calc D.n * rootDiagUnit Tag.E6 a * D.n⁻¹
        = (rootDiagUnit Tag.E6 a * D.n * (rootDiagUnit Tag.E6 a)⁻¹) * rootDiagUnit Tag.E6 a *
            D.n⁻¹ := by rw [h]
      _ = rootDiagUnit Tag.E6 a := by group
  have hnM : D.n ∈ toralRootGroup Tag.E6 (AlgebraicClosure K) a := by
    have h := kernelReflectionGroup_le_ker (K := AlgebraicClosure K) a
      (x := ⟨w, hwa⟩) (Subgroup.mem_subgroupOf.2 hw)
    rw [MonoidHom.mem_ker, weylToralQuotientHom_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h
    rw [hn]
    exact h
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a := by
    rw [hda, map_mul, map_mul, map_inv, ← hΦ, D.lang, hΦ, hFix]
    calc (D.g0 * D.n)⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) *
          (D.g0 * D.n)
        = D.n⁻¹ * (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) *
            D.g0) * D.n := by group
      _ = D.n⁻¹ * rootDiagUnit Tag.E6 a * D.n := by rw [← hda]
      _ = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) * D.g0 := by
          rw [← hda]
          calc D.n⁻¹ * rootDiagUnit Tag.E6 a * D.n
              = D.n⁻¹ * (D.n * rootDiagUnit Tag.E6 a * D.n⁻¹) * D.n := by rw [hnd]
            _ = rootDiagUnit Tag.E6 a := by group
  have hFa : (fun i => Units.map Fr.toMonoidHom (a i)) = a := by
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_rootDiagUnit] at hFd
    exact rootDiagUnit_injective hFd
  have hstab : ∀ g ∈ toralRootGroup Tag.E6 (AlgebraicClosure K) a,
      entrywiseFrobGL Tag.E6 (AlgebraicClosure K) p e g ∈ toralRootGroup Tag.E6 (AlgebraicClosure K) a := by
    intro g hg
    have h1 := baseChangeGL_mem_toralRootGroup Fr hg
    rw [hFa] at h1
    rw [hFGL, units_map_entrywiseHom_eq_baseChangeGL]
    exact h1
  obtain ⟨z, hz, hzn⟩ := toralRootGroup_lang p a e he1 hstab D.n hnM
  rw [hFGL] at hzn
  have hzt : z * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * z := by
    have h3 := (mem_toralCentralizer.1 (toralRootGroup_le a hz)).2
    calc z * rootDiagUnit Tag.E6 a
        = (rootDiagUnit Tag.E6 a * z * (rootDiagUnit Tag.E6 a)⁻¹) * rootDiagUnit Tag.E6 a := by
          rw [h3]
      _ = rootDiagUnit Tag.E6 a * z := by group
  obtain ⟨u, hu⟩ : ∃ u, u = D.g0 * z⁻¹ := ⟨_, rfl⟩
  have hFu : Units.map (entrywiseHom Fr) u = u := by
    have hFz : Units.map (entrywiseHom Fr) z = z * D.n := by rw [← hzn]; group
    rw [hu, map_mul, map_inv, ← hΦ, D.lang, hΦ, hFz]
    group
  have hux : u * rootDiagUnit Tag.E6 a * u⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) := by
    rw [hda, hu]
    calc D.g0 * z⁻¹ * (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) *
          D.g0) * (D.g0 * z⁻¹)⁻¹
        = D.g0 * z⁻¹ * rootDiagUnit Tag.E6 a * z * D.g0⁻¹ := by rw [← hda]; group
      _ = D.g0 * z⁻¹ * (z * rootDiagUnit Tag.E6 a) * D.g0⁻¹ := by rw [hzt]; group
      _ = D.g0 * rootDiagUnit Tag.E6 a * D.g0⁻¹ := by group
      _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) := by
          rw [hda]
          group
  have huG : u ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hu]
    exact mul_mem D.g0_mem (inv_mem (toralRootGroup_le a hz).1)
  have hbij : Function.Bijective Fr := by
    rw [hFrEq]
    exact bijective_iterateFrobenius (AlgebraicClosure K) p e
  obtain ⟨b, j, hjC, hbj⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed Fr hFr hbij huG hFu
  have ha' : ∀ i, ∃ c : Kˣ, Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom c = a i := by
    intro i
    have hai : ((a i : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ Nat.card K = (a i : _) := by
      have h := congrArg (fun t : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ =>
        ((t i : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) hFa
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe] at h
      rw [← hFr]
      exact h
    obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq hai
    have hc0 : c ≠ 0 := by
      intro h0
      apply (a i).ne_zero
      rw [← hc, h0, map_zero]
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.val_mk0]
    exact hc
  choose a' ha'' using ha'
  have hda' : baseChangeGL (algebraMap K (AlgebraicClosure K)) (rootDiagUnit Tag.E6 a') =
      rootDiagUnit Tag.E6 a := by
    rw [baseChangeGL_rootDiagUnit]
    congr 1
    funext i
    exact ha'' i
  have hxK : (x : ModGL Tag.E6 K) =
      (rootDiagUnit Tag.E6 b * j) * rootDiagUnit Tag.E6 a' * (rootDiagUnit Tag.E6 b * j)⁻¹ := by
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    rw [map_mul, map_mul, map_inv, ← hbj, hda', hux]
  have hcC : rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹ ∈ adjointGroup Tag.E6 K :=
    conj_rootDiagUnit_mem_adjointGroup b hjC
  set c : adjointGroup Tag.E6 K := ⟨_, hcC⟩ with hc
  have hcx : (c : ModGL Tag.E6 K)⁻¹ * (x : ModGL Tag.E6 K) * (c : ModGL Tag.E6 K) =
      rootDiagUnit Tag.E6 a' := by
    have hdx : rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 a' =
        rootDiagUnit Tag.E6 a' * rootDiagUnit Tag.E6 b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    rw [hc, hxK]
    calc (rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹)⁻¹ *
          ((rootDiagUnit Tag.E6 b * j) * rootDiagUnit Tag.E6 a' * (rootDiagUnit Tag.E6 b * j)⁻¹) *
          (rootDiagUnit Tag.E6 b * j * (rootDiagUnit Tag.E6 b)⁻¹)
        = rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 a' * (rootDiagUnit Tag.E6 b)⁻¹ := by group
      _ = rootDiagUnit Tag.E6 a' := by rw [hdx]; group
  refine ⟨c⁻¹, fun α hα => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hα
  have hconj : MulAut.conj c⁻¹ * TableBExc.E6Three.hatAut Tag.E6 K x * (MulAut.conj c⁻¹)⁻¹ =
      rootDiagAutHom Tag.E6 K a' := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
    change ((c⁻¹ * TableBExc.E6Three.hatAut Tag.E6 K x (c⁻¹⁻¹ * g * c⁻¹) * c⁻¹⁻¹ : adjointGroup Tag.E6 K) :
      ModGL Tag.E6 K) = ((rootDiagAut Tag.E6 K a' g : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)
    rw [coe_rootDiagAut, ← hcx, Subgroup.coe_mul, Subgroup.coe_mul, TableBExc.E6Three.coe_hatAut_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    group
  have hpow : MulAut.conj c⁻¹ * TableBExc.E6Three.hatAut Tag.E6 K x ^ k * (MulAut.conj c⁻¹)⁻¹ =
      (MulAut.conj c⁻¹ * TableBExc.E6Three.hatAut Tag.E6 K x * (MulAut.conj c⁻¹)⁻¹) ^ k := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rw [hpow, hconj]
  exact zpow_mem (MonoidHom.mem_range.2 ⟨a', rfl⟩) k

end CFSG.StandardType.E6OutdiagPpd

end
