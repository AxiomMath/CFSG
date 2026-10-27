module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcField
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
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
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public noncomputable section

namespace CFSG.StandardType.F4ScalarTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit
  [Finite K] [CharP K 2] in
theorem mem_torus_iff_of_neg (D : LangDatum .F4 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .F4} (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u) {x : ModGL .F4 (AlgebraicClosure K)} :
    x ∈ D.torus ↔ ∃ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
      x = rootDiagUnit .F4 a ∧ ∀ i, a i ^ (Nat.card K + 1) = 1 := by
  have hΦ' : D.Φ = Units.map (entrywiseHom Fr) := MonoidHom.ext hΦ
  simpa only [LangDatum.torus, hn, hΦ', twistedTorus] using
    (mem_twistedTorus_of_neg CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup hw hFr (x := x))

omit [CharP K 2] in
theorem exists_rational_of_mem_torus (D : LangDatum .F4 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .F4} (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u)
    {x : ModGL .F4 (AlgebraicClosure K)} (hx : x ∈ D.torus) :
    ∃ y : adjointGroup .F4 K,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .F4 K) =
        D.g0 * x * D.g0⁻¹ := by
  have hxM : x ∈ D.model := D.torus_le_model hx
  have hxF : D.g0 * x * D.g0⁻¹ ∈ D.fix := by
    rw [← D.map_conj_model]
    exact ⟨x, hxM, rfl⟩
  have hxC : D.g0 * x * D.g0⁻¹ ∈ adjointGroup .F4 (AlgebraicClosure K) := hxF.1
  have hfixed : Units.map (entrywiseHom Fr) (D.g0 * x * D.g0⁻¹) =
      D.g0 * x * D.g0⁻¹ := by
    rw [← hΦ]
    exact hxF.2
  obtain ⟨a, rfl, ha⟩ := (mem_torus_iff_of_neg D Fr hFr hΦ hn hw).mp hx
  have hpow : rootDiagUnit .F4 a ^ (Nat.card K + 1) = 1 := by
    rw [rootDiagUnit_pow]
    have ha' : a ^ (Nat.card K + 1) = 1 := funext ha
    rw [ha', rootDiagUnit_one]
  have hmem : D.g0 * rootDiagUnit .F4 a * D.g0⁻¹ ∈
      adjointGroup .F4 (AlgebraicClosure K) ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    exact ⟨hxC, by simp [hfixed]⟩
  have hmap := CFSG.RankThree.Chevalley.frobenius_fixed_eq_map_of_bijective (τ := .F4) (Or.inr rfl) Fr hFr
    (CFSG.LieType.Chevalley.frobenius_bijective (k := K) Fr hFr)
  rw [hmap] at hmem
  obtain ⟨y, hy, heq⟩ := hmem
  exact ⟨⟨y, hy⟩, heq⟩

@[expose] def coordHom (D : LangDatum .F4 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .F4} (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u) :
    (Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) →*
      adjointGroup .F4 K := by
  let f : (Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) →*
      ModGL .F4 (AlgebraicClosure K) :=
    (MulAut.conj D.g0).toMonoidHom.comp ((rootDiagUnitHom .F4 (AlgebraicClosure K)).comp
      ((rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)).subtype.compLeft (Fin Tag.F4.rank)))
  let bc : adjointGroup .F4 K →* ModGL .F4 (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .F4 K).subtype
  have hbc : Function.Injective bc :=
    (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp Subtype.val_injective
  have hrange : ∀ a, f a ∈ bc.range := by
    intro a
    have htor : rootDiagUnit .F4 (fun i => (a i : (AlgebraicClosure K)ˣ)) ∈ D.torus :=
      (mem_torus_iff_of_neg D Fr hFr hΦ hn hw).mpr ⟨_, rfl,
        fun i => (mem_rootsOfUnity _ _).mp (a i).2⟩
    obtain ⟨y, hy⟩ := exists_rational_of_mem_torus D Fr hFr hΦ hn hw htor
    exact ⟨y, hy⟩
  exact (MonoidHom.ofInjective hbc).symm.toMonoidHom.comp (f.codRestrict bc.range hrange)

omit [CharP K 2] in
theorem baseChange_coordHom (D : LangDatum .F4 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .F4} (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u)
    (a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    baseChangeGL (algebraMap K (AlgebraicClosure K))
        (coordHom D Fr hFr hΦ hn hw a : ModGL .F4 K) =
      D.g0 * rootDiagUnit .F4 (fun i => (a i : (AlgebraicClosure K)ˣ)) * D.g0⁻¹ := by
  unfold coordHom
  change ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup .F4 K).subtype) _ = _
  rw [← MonoidHom.ofInjective_apply]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl
  exact (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp Subtype.val_injective

omit [CharP K 2] in
theorem coordHom_injective (D : LangDatum .F4 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .F4} (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u) :
    Function.Injective (coordHom D Fr hFr hΦ hn hw) := by
  intro a b hab
  have h := congrArg (fun y : adjointGroup .F4 K =>
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .F4 K)) hab
  rw [baseChange_coordHom, baseChange_coordHom] at h
  have hd := CFSG.LieType.Chevalley.rootDiagUnit_injective
    (mul_left_cancel (mul_right_cancel h))
  funext i
  exact Subtype.ext (congrFun hd i)

omit [CharP K 2] in
theorem mem_range_coordHom_iff (D : LangDatum .F4 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .F4} (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u) (y : adjointGroup .F4 K) :
    y ∈ (coordHom D Fr hFr hΦ hn hw).range ↔
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .F4 K) * D.g0 ∈
        D.torus := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [baseChange_coordHom]
    have hconj : D.g0⁻¹ *
        (D.g0 * rootDiagUnit .F4 (fun i => (a i : (AlgebraicClosure K)ˣ)) * D.g0⁻¹) * D.g0 =
        rootDiagUnit .F4 (fun i => (a i : (AlgebraicClosure K)ˣ)) := by group
    rw [hconj]
    exact (mem_torus_iff_of_neg D Fr hFr hΦ hn hw).mpr ⟨_, rfl,
      fun i => (mem_rootsOfUnity _ _).mp (a i).2⟩
  · intro hy
    obtain ⟨a, ha, hpow⟩ := (mem_torus_iff_of_neg D Fr hFr hΦ hn hw).mp hy
    let a' : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) :=
      fun i => ⟨a i, (mem_rootsOfUnity _ _).mpr (hpow i)⟩
    refine ⟨a', ?_⟩
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    rw [baseChange_coordHom]
    change D.g0 * rootDiagUnit .F4 a * D.g0⁻¹ = _
    rw [← ha]
    group

@[expose] def corootTupleHom (k : Fin Tag.F4.rank) :
    rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) →*
      (Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) where
  toFun := fun z j => z ^ Tag.F4.cartan k j
  map_one' := by ext j; simp
  map_mul' := fun z u => by ext j; simp [mul_zpow]

@[expose] def corootHom (D : LangDatum .F4 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .F4} (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u) (k : Fin Tag.F4.rank) :
    rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) →* adjointGroup .F4 K :=
  (coordHom D Fr hFr hΦ hn hw).comp (corootTupleHom k)

omit [CharP K 2] in
theorem baseChange_corootHom (D : LangDatum .F4 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .F4} (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u) (k : Fin Tag.F4.rank)
    (z : rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    baseChangeGL (algebraMap K (AlgebraicClosure K))
        (corootHom D Fr hFr hΦ hn hw k z : ModGL .F4 K) =
      D.g0 * torusElt .F4 (AlgebraicClosure K) k (z : (AlgebraicClosure K)ˣ) * D.g0⁻¹ := by
  rw [corootHom, MonoidHom.comp_apply, baseChange_coordHom, torusElt_eq_rootDiagUnit]
  rfl

omit [CharP K 2] in
theorem simple_conj_coordHom (D : LangDatum .F4 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .F4} (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u) (k : Fin Tag.F4.rank)
    (n : adjointGroup .F4 K)
    (hnb : baseChangeGL (algebraMap K (AlgebraicClosure K)) (n : ModGL .F4 K) =
      D.g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) (simple .F4 k) * D.g0⁻¹)
    (a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    n * coordHom D Fr hFr hΦ hn hw a * n⁻¹ =
      coordHom D Fr hFr hΦ hn hw a * (corootHom D Fr hFr hΦ hn hw k (a k))⁻¹ := by
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
    baseChange_coordHom, baseChange_corootHom, hnb]
  rw [canonicalRep_simple]
  have hkey := weylElt_conj_rootDiagUnit (τ := .F4)
    (K := AlgebraicClosure K) (fun j => (a j : (AlgebraicClosure K)ˣ)) k
  have hprod : rootDiagUnit .F4 (fun j => (a j : (AlgebraicClosure K)ˣ) *
        (a k : (AlgebraicClosure K)ˣ) ^ (-Tag.F4.cartan k j)) =
      rootDiagUnit .F4 (fun j => (a j : (AlgebraicClosure K)ˣ)) *
        (torusElt .F4 (AlgebraicClosure K) k (a k : (AlgebraicClosure K)ˣ))⁻¹ := by
    rw [torusElt_eq_rootDiagUnit, rootDiagUnit_inv, ← rootDiagUnit_mul]
    congr 1
    funext j
    simp only [Pi.mul_apply, Pi.inv_apply, zpow_neg]
  calc
    _ = D.g0 * (weylElt .F4 (AlgebraicClosure K) k 1 *
        rootDiagUnit .F4 (fun j => (a j : (AlgebraicClosure K)ˣ)) *
        (weylElt .F4 (AlgebraicClosure K) k 1)⁻¹) * D.g0⁻¹ := by group
    _ = _ := by rw [hkey, hprod]; group

end CFSG.StandardType.F4ScalarTorus
