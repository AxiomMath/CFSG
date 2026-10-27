module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
public import CFSG.LocalAnalysis.StandardType.GGTorusScalar
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
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
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public noncomputable section

namespace CFSG.StandardType.ScalarLangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem exists_rootValue_equiv [Finite K] [CharP K 2] :
    Nonempty (rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) ≃*
      Multiplicative (ZMod (Nat.card K + 1))) := by
  have : Fintype K := Fintype.ofFinite K
  have hEven : Even (Nat.card K) := by
    rw [Nat.even_iff, Nat.card_eq_fintype_card]
    exact FiniteField.even_card_of_char_two (ringChar.eq K 2)
  have hm : Odd (Nat.card K + 1) := hEven.add_one
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hm0 : ((Nat.card K + 1 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro h
    have h2 := (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 (Nat.card K + 1)).mp h
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  have : NeZero (Nat.card K + 1) := ⟨by omega⟩
  have : NeZero ((Nat.card K + 1 : ℕ) : AlgebraicClosure K) := ⟨hm0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (Nat.card K + 1)
  have hcard : Nat.card (rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) = Nat.card K + 1 :=
    hζ.card_rootsOfUnity
  have hcyc : IsCyclic (rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :=
    rootsOfUnity.isCyclic (AlgebraicClosure K) (Nat.card K + 1)
  have he : rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) ≃*
      Multiplicative (ZMod (Nat.card (rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)))) :=
    (zmodCyclicMulEquiv hcyc).symm
  rw [hcard] at he
  exact ⟨he⟩

theorem mem_torus_iff_of_neg (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup τ} (hn : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) {x : ModGL τ (AlgebraicClosure K)} :
    x ∈ D.torus ↔ ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      x = rootDiagUnit τ a ∧ ∀ i, a i ^ (Nat.card K + 1) = 1 := by
  have hΦ' : D.Φ = Units.map (entrywiseHom Fr) := MonoidHom.ext hΦ
  simpa only [LangDatum.torus, hn, hΦ', twistedTorus] using
    (mem_twistedTorus_of_neg CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup hw hFr (x := x))

theorem exists_rational_of_mem_torus_of_pow_eq_one
    (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {m : ℕ} (_hm : 0 < m)
    (hrat : ∀ x : ModGL τ (AlgebraicClosure K), x ∈ adjointGroup τ (AlgebraicClosure K) →
      Units.map (entrywiseHom Fr) x = x → x ^ m = 1 →
        x ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {x : ModGL τ (AlgebraicClosure K)} (hx : x ∈ D.torus) (hxm : x ^ m = 1) :
    ∃ y : adjointGroup τ K,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K) =
        D.g0 * x * D.g0⁻¹ := by
  have hxM : x ∈ D.model := D.torus_le_model hx
  have hxF : D.g0 * x * D.g0⁻¹ ∈ D.fix := by
    rw [← D.map_conj_model]
    exact ⟨x, hxM, rfl⟩
  have hfixed : Units.map (entrywiseHom Fr) (D.g0 * x * D.g0⁻¹) =
      D.g0 * x * D.g0⁻¹ := by
    rw [← hΦ]
    exact hxF.2
  have hpow : (D.g0 * x * D.g0⁻¹) ^ m = 1 := by
    rw [conj_pow, hxm, mul_one, mul_inv_cancel]
  obtain ⟨y, hy, heq⟩ := hrat _ hxF.1 hfixed hpow
  exact ⟨⟨y, hy⟩, heq⟩

@[expose] def coordHomOfFixed {P : Type} [Group P]
    (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {m : ℕ} (hm : 0 < m)
    (c : P →* (Fin τ.rank → (AlgebraicClosure K)ˣ))
    (hc : ∀ a, rootDiagUnit τ (c a) ∈ D.torus) (hp : ∀ a : P, a ^ m = 1)
    (hrat : ∀ x : ModGL τ (AlgebraicClosure K), x ∈ adjointGroup τ (AlgebraicClosure K) →
      Units.map (entrywiseHom Fr) x = x → x ^ m = 1 →
        x ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) :
    P →* adjointGroup τ K := by
  let f : P →* ModGL τ (AlgebraicClosure K) :=
    (MulAut.conj D.g0).toMonoidHom.comp ((rootDiagUnitHom τ (AlgebraicClosure K)).comp c)
  let bc : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype
  have hbc : Function.Injective bc :=
    (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp Subtype.val_injective
  have hrange : ∀ a, f a ∈ bc.range := by
    intro a
    have hpow : rootDiagUnit τ (c a) ^ m = 1 := by
      rw [rootDiagUnit_pow, ← map_pow, hp, map_one, rootDiagUnit_one]
    obtain ⟨y, hy⟩ := exists_rational_of_mem_torus_of_pow_eq_one D Fr hΦ hm hrat (hc a) hpow
    exact ⟨y, hy⟩
  exact (MonoidHom.ofInjective hbc).symm.toMonoidHom.comp (f.codRestrict bc.range hrange)

theorem baseChange_coordHomOfFixed {P : Type} [Group P]
    (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {m : ℕ} (hm : 0 < m)
    (c : P →* (Fin τ.rank → (AlgebraicClosure K)ˣ))
    (hc : ∀ a, rootDiagUnit τ (c a) ∈ D.torus) (hp : ∀ a : P, a ^ m = 1)
    (hrat : ∀ x : ModGL τ (AlgebraicClosure K), x ∈ adjointGroup τ (AlgebraicClosure K) →
      Units.map (entrywiseHom Fr) x = x → x ^ m = 1 →
        x ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    (a : P) :
    baseChangeGL (algebraMap K (AlgebraicClosure K))
        (coordHomOfFixed D Fr hΦ hm c hc hp hrat a : ModGL τ K) =
      D.g0 * rootDiagUnit τ (c a) * D.g0⁻¹ := by
  unfold coordHomOfFixed
  change ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
    (adjointGroup τ K).subtype) _ = _
  rw [← MonoidHom.ofInjective_apply]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl
  exact (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp Subtype.val_injective

theorem coordHomOfFixed_injective {P : Type} [Group P]
    (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {m : ℕ} (hm : 0 < m)
    (c : P →* (Fin τ.rank → (AlgebraicClosure K)ˣ))
    (hc : ∀ a, rootDiagUnit τ (c a) ∈ D.torus) (hp : ∀ a : P, a ^ m = 1)
    (hrat : ∀ x : ModGL τ (AlgebraicClosure K), x ∈ adjointGroup τ (AlgebraicClosure K) →
      Units.map (entrywiseHom Fr) x = x → x ^ m = 1 →
        x ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    (hcinj : Function.Injective c) :
    Function.Injective (coordHomOfFixed D Fr hΦ hm c hc hp hrat) := by
  intro a b hab
  have h := congrArg (fun y : adjointGroup τ K =>
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K)) hab
  rw [baseChange_coordHomOfFixed, baseChange_coordHomOfFixed] at h
  exact hcinj (CFSG.LieType.Chevalley.rootDiagUnit_injective (mul_left_cancel (mul_right_cancel h)))

@[expose] def coordHom (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup τ} (hn : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) :
    (Fin τ.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) →*
      adjointGroup τ K := by
  let c : (Fin τ.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) →*
      (Fin τ.rank → (AlgebraicClosure K)ˣ) :=
    (rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)).subtype.compLeft (Fin τ.rank)
  have hc : ∀ a, rootDiagUnit τ (c a) ∈ D.torus := fun a =>
    (mem_torus_iff_of_neg D Fr hFr hΦ hn hw).mpr ⟨_, rfl,
      fun i => (mem_rootsOfUnity _ _).mp (a i).2⟩
  have hp : ∀ a : Fin τ.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K),
      a ^ (Nat.card K + 1) = 1 := by
    intro a
    funext i
    apply Subtype.ext
    exact (mem_rootsOfUnity _ _).mp (a i).2
  refine coordHomOfFixed D Fr hΦ (Nat.succ_pos _) c hc hp ?_
  intro z hzC hzF hzm
  let : Finite (Subgroup.zpowers z) := finite_zpowers.mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨Nat.card K + 1, Nat.succ_pos _, hzm⟩)
  exact hrat (Subgroup.zpowers z) inferInstance (Subgroup.zpowers_le.mpr hzC)
    (fun y hy => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [map_zpow, hzF]) (Subgroup.mem_zpowers z)

theorem baseChange_coordHom (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup τ} (hn : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    (a : Fin τ.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    baseChangeGL (algebraMap K (AlgebraicClosure K))
        (coordHom D Fr hFr hΦ hn hw hrat a : ModGL τ K) =
      D.g0 * rootDiagUnit τ (fun i => (a i : (AlgebraicClosure K)ˣ)) * D.g0⁻¹ := by
  unfold coordHom
  exact baseChange_coordHomOfFixed D Fr hΦ (Nat.succ_pos _) _ _ _ _ a

theorem coordHom_injective (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup τ} (hn : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) :
    Function.Injective (coordHom D Fr hFr hΦ hn hw hrat) := by
  intro a b hab
  have h := congrArg (fun y : adjointGroup τ K =>
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K)) hab
  rw [baseChange_coordHom, baseChange_coordHom] at h
  have hd := CFSG.LieType.Chevalley.rootDiagUnit_injective
    (mul_left_cancel (mul_right_cancel h))
  funext i
  exact Subtype.ext (congrFun hd i)

theorem mem_range_coordHom_iff (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup τ} (hn : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) (y : adjointGroup τ K) :
    y ∈ (coordHom D Fr hFr hΦ hn hw hrat).range ↔
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K) * D.g0 ∈
        D.torus := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [baseChange_coordHom]
    have hconj : D.g0⁻¹ *
        (D.g0 * rootDiagUnit τ (fun i => (a i : (AlgebraicClosure K)ˣ)) * D.g0⁻¹) * D.g0 =
        rootDiagUnit τ (fun i => (a i : (AlgebraicClosure K)ˣ)) := by group
    rw [hconj]
    exact (mem_torus_iff_of_neg D Fr hFr hΦ hn hw).mpr ⟨_, rfl,
      fun i => (mem_rootsOfUnity _ _).mp (a i).2⟩
  · intro hy
    obtain ⟨a, ha, hpow⟩ := (mem_torus_iff_of_neg D Fr hFr hΦ hn hw).mp hy
    let a' : Fin τ.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) :=
      fun i => ⟨a i, (mem_rootsOfUnity _ _).mpr (hpow i)⟩
    refine ⟨a', ?_⟩
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    rw [baseChange_coordHom]
    change D.g0 * rootDiagUnit τ a * D.g0⁻¹ = _
    rw [← ha]
    group

@[expose] def corootHom (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup τ} (hn : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) (k : Fin τ.rank) :
    rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) →* adjointGroup τ K :=
  (coordHom D Fr hFr hΦ hn hw hrat).comp (corTupleHom τ.cartan k)

theorem baseChange_corootHom (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup τ} (hn : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) (k : Fin τ.rank)
    (z : rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    baseChangeGL (algebraMap K (AlgebraicClosure K))
        (corootHom D Fr hFr hΦ hn hw hrat k z : ModGL τ K) =
      D.g0 * torusElt τ (AlgebraicClosure K) k (z : (AlgebraicClosure K)ˣ) * D.g0⁻¹ := by
  rw [corootHom, MonoidHom.comp_apply, baseChange_coordHom, torusElt_eq_rootDiagUnit]
  rfl

theorem simple_conj_coordHom (D : LangDatum τ (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup τ} (hn : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) (k : Fin τ.rank)
    (n : adjointGroup τ K)
    (hnb : baseChangeGL (algebraMap K (AlgebraicClosure K)) (n : ModGL τ K) =
      D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (simple τ k) * D.g0⁻¹)
    (a : Fin τ.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    n * coordHom D Fr hFr hΦ hn hw hrat a * n⁻¹ =
      coordHom D Fr hFr hΦ hn hw hrat a * (corootHom D Fr hFr hΦ hn hw hrat k (a k))⁻¹ := by
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
    baseChange_coordHom, baseChange_corootHom, hnb]
  rw [canonicalRep_simple]
  have hkey := weylElt_conj_rootDiagUnit (τ := τ)
    (K := AlgebraicClosure K) (fun j => (a j : (AlgebraicClosure K)ˣ)) k
  have hprod : rootDiagUnit τ (fun j => (a j : (AlgebraicClosure K)ˣ) *
        (a k : (AlgebraicClosure K)ˣ) ^ (-τ.cartan k j)) =
      rootDiagUnit τ (fun j => (a j : (AlgebraicClosure K)ˣ)) *
        (torusElt τ (AlgebraicClosure K) k (a k : (AlgebraicClosure K)ˣ))⁻¹ := by
    rw [torusElt_eq_rootDiagUnit, rootDiagUnit_inv, ← rootDiagUnit_mul]
    congr 1
    funext j
    simp only [Pi.mul_apply, Pi.inv_apply, zpow_neg]
  calc
    _ = D.g0 * (weylElt τ (AlgebraicClosure K) k 1 *
        rootDiagUnit τ (fun j => (a j : (AlgebraicClosure K)ˣ)) *
        (weylElt τ (AlgebraicClosure K) k 1)⁻¹) * D.g0⁻¹ := by group
    _ = _ := by rw [hkey, hprod]; group

end CFSG.StandardType.ScalarLangTorus
