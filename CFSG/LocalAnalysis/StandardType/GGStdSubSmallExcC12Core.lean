module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.LieType.Chevalley.SignKernelComponentBorel
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
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
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType.SmallExcC12

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar (componentRootSpan_le_toralCentralizer
  isSubnormal_componentRootSpan isQuasisimple_componentRootSpan_of_sq_ne_one)

section Groups

variable {G : Type*} [Group G]

theorem isComponent_subgroupOf {L X : Subgroup G} (hLX : L ≤ X) (hq : CFSG.IsQuasisimple L)
    (hs : (L.subgroupOf X).IsSubnormal) : CFSG.IsComponent (L.subgroupOf X) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLX).symm hq, hs⟩

theorem commute_of_commutator_subgroupOf_eq_bot {L M X : Subgroup G} (hLX : L ≤ X)
    (hMX : M ≤ X) (h : ⁅L.subgroupOf X, M.subgroupOf X⁆ = ⊥) :
    ∀ x ∈ L, ∀ y ∈ M, x * y = y * x := by
  intro x hx y hy
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    (show (⟨x, hLX hx⟩ : X) ∈ L.subgroupOf X from Subgroup.mem_subgroupOf.2 hx)
  have h2 := Subgroup.mem_centralizer_iff.1 h1 ⟨y, hMX hy⟩ (Subgroup.mem_subgroupOf.2 hy)
  exact (congrArg Subtype.val h2).symm

theorem exists_ne_comm_of_isQuasisimple {D : Subgroup G} (hq : CFSG.IsQuasisimple D) :
    ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x := by
  obtain ⟨-, -, u, v, huv⟩ := hq
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  refine ⟨u, u.2, v, v.2, fun h => huv ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext h)

end Groups

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem torusElt_pow_eq (k : Fin τ.rank) (t : Kˣ) (n : ℕ) :
    torusElt τ K k (t ^ n) = torusElt τ K k t ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, torusElt_one]
  | succ n ih => rw [pow_succ, torusElt_mul, ih, pow_succ]

theorem torusElt_mul_xUnit_ne (k : Fin τ.rank) {ζ : Kˣ} (hζ : ζ ^ 2 ≠ 1) :
    torusElt τ K k ζ * xUnit τ K k 1 ≠ xUnit τ K k 1 * torusElt τ K k ζ := by
  intro h
  have h1 : torusElt τ K k ζ * pinnedX τ K (Pi.single k 1) 1 * (torusElt τ K k ζ)⁻¹ =
      pinnedX τ K (Pi.single k 1) 1 := by
    rw [pinnedX_single, h, mul_inv_cancel_right]
  rw [root_torus_conjugation k (isRoot_single τ k) ζ 1] at h1
  have h2 := pinnedX_injective τ K _ h1
  have hs : ∑ j, τ.cartan k j * (Pi.single k 1 : Fin τ.rank → ℤ) j = 2 := by
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one, Tag.cartan_self]
  rw [hs, mul_one, Units.val_eq_one, zpow_two] at h2
  exact hζ (by rw [sq]; exact h2)


theorem exists_torus_ne_comm {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) {p : ℕ} {ζ : Kˣ} (hζ2 : ζ ^ 2 ≠ 1) (hζp : ζ ^ p = 1) :
    ∃ t ∈ componentTorus K χ i, t ^ p = 1 ∧ ∃ j ∈ componentRootSpan K χ i, t * j ≠ j * t := by
  obtain ⟨⟨α, hαk⟩, rfl⟩ := Quotient.exists_rep i
  obtain ⟨w, k, rfl⟩ := isRoot_iff_exists_smul_single.1 hαk.1
  have hα : w • (Pi.single k 1 : Fin τ.rank → ℤ) ∈ componentRoots χ ⟦⟨_, hαk⟩⟧ := ⟨hαk, rfl⟩
  set n := canonicalRep (coxeterSystem τ) K w with hn
  refine ⟨n * torusElt τ K k ζ * n⁻¹, canonicalRep_conj_torusElt_mem hα ζ, ?_,
    n * xUnit τ K k 1 * n⁻¹, rootSpan_mono (Set.singleton_subset_iff.2 hα)
      (canonicalRep_conj_mem_rootSpan_singleton w (isRoot_single τ k)
        (xUnit_mem_rootSpan_single k 1)), fun h => torusElt_mul_xUnit_ne k hζ2 ?_⟩
  · rw [conj_pow, ← torusElt_pow_eq, hζp, torusElt_one, mul_one, mul_inv_cancel]
  · calc torusElt τ K k ζ * xUnit τ K k 1
        = n⁻¹ * (n * torusElt τ K k ζ * n⁻¹ * (n * xUnit τ K k 1 * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * xUnit τ K k 1 * n⁻¹ * (n * torusElt τ K k ζ * n⁻¹)) * n := by rw [h]
      _ = xUnit τ K k 1 * torusElt τ K k ζ := by group

end Torus

section Centralizer


theorem exists_eq_componentRootSpan (τ : Tag) {K : Type} [Field K] [Finite K] {t : Kˣ}
    (ht : t ^ 2 ≠ 1) {p : ℕ} (hp : p.Prime) (b : Fin τ.rank → Kˣ) (hb : ∀ i, b i ^ p = 1)
    (D : Subgroup (ModGL τ K)) (hD : D ≤ toralCentralizer τ K b)
    (hn : ∀ c ∈ toralCentralizer τ K b, ∀ d ∈ D, c * d * c⁻¹ ∈ D) (hq : CFSG.IsQuasisimple D) :
    ∃ i, D = componentRootSpan K (rootCharHom b) i := by
  haveI : Finite (ModGL τ K) := finite_modGL
  have hU : D ≤ rootSpan τ K (rootCharKernel b) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_rootSpan_kernel hp b hb hD
      (Subgroup.isPerfect_iff.1 hq.1)
  have hiSup : ⨆ i : KernelComponent (rootCharHom b), componentRootSpan K (rootCharHom b) i =
      rootSpan τ K (rootCharKernel b) := iSup_componentRootSpan K
  have hDc : CFSG.IsComponent (D.subgroupOf (toralCentralizer τ K b)) :=
    isComponent_subgroupOf hD hq (Subgroup.Normal.isSubnormal
      ((Subgroup.normal_subgroupOf_iff hD).2 fun d c hd hc => hn c hc d hd))
  by_contra hne
  push Not at hne
  have hcomm : ∀ i, ∀ x ∈ D, ∀ y ∈ componentRootSpan K (rootCharHom b) i, x * y = y * x := by
    intro i
    have hSi := componentRootSpan_le_toralCentralizer b i
    have hSc := isComponent_subgroupOf hSi (isQuasisimple_componentRootSpan_of_sq_ne_one ht i)
      (isSubnormal_componentRootSpan b i)
    refine commute_of_commutator_subgroupOf_eq_bot hD hSi
      ((CFSG.LocalCores.distinct_components_commute hDc hSc).resolve_left fun h => hne i ?_)
    have h' := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hD, inf_eq_left.2 hSi] at h'
  have hcent : rootSpan τ K (rootCharKernel b) ≤ Subgroup.centralizer (D : Set (ModGL τ K)) := by
    rw [← hiSup]
    exact iSup_le fun i y hy => Subgroup.mem_centralizer_iff.2 fun x hx => hcomm i x hx y hy
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_ne_comm_of_isQuasisimple hq
  exact hxy (Subgroup.mem_centralizer_iff.1 (hcent (hU hy)) x hx)

end Centralizer

@[expose] def NonCentralAt {R : Type*} [Group R] (A : Subgroup R) : Prop :=
  ∀ a ∈ A, ∀ D : Subgroup R, D ≤ Subgroup.centralizer ({a} : Set R) →
    (∀ c ∈ Subgroup.centralizer ({a} : Set R), ∀ d ∈ D, c * d * c⁻¹ ∈ D) →
    CFSG.IsQuasisimple D → ∃ t ∈ D, t ∈ A ∧ ∃ j ∈ D, t * j ≠ j * t

theorem nonCentralAt_of_mulEquiv {R R' : Type*} [Group R] [Group R'] (e : R ≃* R')
    {A : Subgroup R} (h : NonCentralAt (A.map e.toMonoidHom)) : NonCentralAt A := by
  intro a ha D hD hn hq
  have hDe : D.map e.toMonoidHom ≤ Subgroup.centralizer ({e a} : Set R') := by
    rintro _ ⟨d, hd, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hD hd)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show e d * e a = e a * e d
    rw [← map_mul, ← map_mul, h1]
  have hne : ∀ c ∈ Subgroup.centralizer ({e a} : Set R'), ∀ d ∈ D.map e.toMonoidHom,
      c * d * c⁻¹ ∈ D.map e.toMonoidHom := by
    rintro c hc _ ⟨d, hd, rfl⟩
    have hc' : e.symm c ∈ Subgroup.centralizer ({a} : Set R) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hc]
    refine ⟨e.symm c * d * (e.symm c)⁻¹, hn _ hc' d hd, ?_⟩
    show e (e.symm c * d * (e.symm c)⁻¹) = c * e d * c⁻¹
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
  have hqe : CFSG.IsQuasisimple (D.map e.toMonoidHom) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (D.equivMapOfInjective e.toMonoidHom e.injective) hq
  obtain ⟨_, ⟨t, htD, rfl⟩, ⟨t', ht'A, ht'⟩, _, ⟨j, hjD, rfl⟩, htj⟩ :=
    h (e a) ⟨a, ha, rfl⟩ (D.map e.toMonoidHom) hDe hne hqe
  obtain rfl : t' = t := e.injective ht'
  refine ⟨t', htD, ht'A, j, hjD, fun h' => htj ?_⟩
  show e t' * e j = e j * e t'
  rw [← map_mul, ← map_mul, h']

section Torsion


theorem rootDiagUnit_pow_eq {τ : Tag} {K : Type} [Field K] (b : Fin τ.rank → Kˣ) (n : ℕ) :
    rootDiagUnit τ (b ^ n) = rootDiagUnit τ b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, CFSG.LieType.Chevalley.rootDiagUnit_one]
  | succ n ih => rw [pow_succ, CFSG.LieType.Chevalley.rootDiagUnit_mul, ih, pow_succ]

theorem nonCentralAt_torusPow (τ : Tag) {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    {ζ : Kˣ} (hζ2 : ζ ^ 2 ≠ 1) (hζp : ζ ^ p = 1) {V : Subgroup (adjointGroup τ K)}
    (hV : ∀ g, g ∈ V ↔ (g : ModGL τ K) ∈ torusGroup τ K ∧ g ^ p = 1) : NonCentralAt V := by
  intro a ha D hD hn hq
  obtain ⟨haH, hap⟩ := (hV a).1 ha
  obtain ⟨b, hab⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup haH
  have hap' : (a : ModGL τ K) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hap, Subgroup.coe_one]
  have hb : ∀ i, b i ^ p = 1 := by
    have h1 : rootDiagUnit τ (b ^ p) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_pow_eq, ← hab, hap', CFSG.LieType.Chevalley.rootDiagUnit_one]
    exact fun i => congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h1) i
  have hD' : D.map (adjointGroup τ K).subtype ≤ toralCentralizer τ K b := by
    rintro _ ⟨d, hd, rfl⟩
    refine Subgroup.mem_inf.2 ⟨d.2, ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hD hd)
    rw [Subgroup.mem_centralizer_singleton_iff, ← hab]
    exact congrArg Subtype.val h1
  have hn' : ∀ c ∈ toralCentralizer τ K b, ∀ d ∈ D.map (adjointGroup τ K).subtype,
      c * d * c⁻¹ ∈ D.map (adjointGroup τ K).subtype := by
    intro c hc' _ hd'
    obtain ⟨hcC, hcz⟩ := Subgroup.mem_inf.1 hc'
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hd'
    have hc : (⟨c, hcC⟩ : adjointGroup τ K) ∈
        Subgroup.centralizer ({a} : Set (adjointGroup τ K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hcz ⊢
      rw [← hab] at hcz
      exact Subtype.ext hcz
    exact ⟨_, hn _ hc d hd, rfl⟩
  have hqe : CFSG.IsQuasisimple (D.map (adjointGroup τ K).subtype) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (D.equivMapOfInjective (adjointGroup τ K).subtype (adjointGroup τ K).subtype_injective) hq
  obtain ⟨i, hi⟩ :=
    exists_eq_componentRootSpan τ hζ2 hp b hb (D.map (adjointGroup τ K).subtype) hD' hn' hqe
  obtain ⟨t, ⟨htS, htH⟩, htp, j, hjS, htj⟩ := exists_torus_ne_comm i hζ2 hζp
  rw [← hi] at htS hjS
  obtain ⟨t₀, ht₀D, rfl⟩ := htS
  obtain ⟨j₀, hj₀D, rfl⟩ := hjS
  refine ⟨t₀, ht₀D, (hV t₀).2 ⟨htH, Subtype.ext ?_⟩, j₀, hj₀D,
    fun h => htj (congrArg Subtype.val h)⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact htp

end Torsion

end CFSG.StandardType.SmallExcC12

end
