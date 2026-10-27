module

public import CFSG.Quasithin.Background.E2KGSz8Cover
public import CFSG.LieType.Multipliers.Sz8
public import Certificates.Certificate7262
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.Lemma311
public import CFSG.GH74.Uniqueness.Prop38
public import CFSG.GH74.Uniqueness.Setup
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.E2TenKG
public import CFSG.Quasithin.Background.F7TwoDefs
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.Quasithin.E2

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8 CFSG.RankThree.PerfectCover
open CFSG.CosetTable TauCeti
open scoped commutatorElement

theorem lift_genSz_centWords {w : List (Fin 2 × Bool)}
    (hw : w ∈ centWords) : FreeGroup.lift genSz (FreeGroup.mk w) = 1 :=
  Certificates.certificate7262.1 w hw

theorem two_dvd_orderOf_invWords {u : List (Fin 2 × Bool)}
    (hu : (u, 2) ∈ invWords) :
    2 ∣ orderOf (PresentedGroup.mk (wordSet (coverWords rels wWord)) (FreeGroup.mk u)) :=
  Certificates.certificate7262.2 u hu

private theorem finite_presentedGroup_congr {ι : Type*} {S T : Set (FreeGroup ι)} (h : S = T)
    [Finite (PresentedGroup S)] : Finite (PresentedGroup T) := by
  subst h; infer_instance

private theorem orderOf_presentedGroup_mk_congr {ι : Type*} {S T : Set (FreeGroup ι)} (h : S = T)
    (x : FreeGroup ι) : orderOf (PresentedGroup.mk S x) = orderOf (PresentedGroup.mk T x) := by
  subst h; rfl

abbrev Sz8Cover : Type := PresentedCover (wordSet rels) fun i => FreeGroup.mk (wWord i)

abbrev sz8Mk (u : List (Fin 2 × Bool)) : Sz8Cover :=
  PresentedGroup.mk _ (FreeGroup.mk u)

private theorem sz8Mk_append (u v : List (Fin 2 × Bool)) : sz8Mk (u ++ v) = sz8Mk u * sz8Mk v := by
  rw [sz8Mk, sz8Mk, sz8Mk, ← FreeGroup.mul_mk, map_mul]

private theorem sz8Mk_invRev (u : List (Fin 2 × Bool)) :
    sz8Mk (FreeGroup.invRev u) = (sz8Mk u)⁻¹ := by
  rw [sz8Mk, sz8Mk, ← FreeGroup.inv_mk, map_inv]

private theorem sz8Mk_commWord (u v : List (Fin 2 × Bool)) :
    sz8Mk (commWord u v) = ⁅sz8Mk u, sz8Mk v⁆ := by
  rw [sz8Mk, mk_commWord, map_commutatorElement]

private theorem sz8Mk_ne_one_of_dvd {u : List (Fin 2 × Bool)}
    (h : 2 ∣ orderOf (PresentedGroup.mk (wordSet (coverWords rels wWord)) (FreeGroup.mk u))) :
    sz8Mk u ≠ 1 := by
  have h' : 2 ∣ orderOf (sz8Mk u) := by
    rw [sz8Mk, orderOf_presentedGroup_mk_congr (coverRelators_wordSet rels wWord)]
    exact h
  intro h1
  rw [h1, orderOf_one] at h'
  norm_num at h'

private theorem sz8Mk_invWords_ne_one {u : List (Fin 2 × Bool)}
    (hu : (u, 2) ∈ invWords) : sz8Mk u ≠ 1 :=
  sz8Mk_ne_one_of_dvd (two_dvd_orderOf_invWords hu)

private theorem sz8Mk_kerWords_ne_one {u : List (Fin 2 × Bool)}
    (hu : (u, 2) ∈ kerWords) : sz8Mk u ≠ 1 :=
  sz8Mk_ne_one_of_dvd (two_dvd_orderOf_kerWords hu)

private theorem coe_genSz_zero :
    ((genSz 0 : suzukiGroup 1) : GL (Fin 4) (GaloisField 2 (2 * 1 + 1))) = toGL (genGL 0) := by
  have h := val_lift_genSz (FreeGroup.of 0)
  rwa [FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at h

private theorem genSz_zero_ne_one : genSz 0 ≠ 1 := by
  intro h
  have h1 := coe_genSz_zero
  rw [h, OneMemClass.coe_one] at h1
  have h2 : genGL 0 = 1 := toGL_injective (h1.symm.trans (map_one _).symm)
  have h3 := congrArg (fun g : GL (Fin 4) F8 => (g : Matrix (Fin 4) (Fin 4) F8) 0 0) h2
  revert h3
  decide

private theorem genSz_zero_mul_self : genSz 0 * genSz 0 = 1 := by
  have h : genGL 0 * genGL 0 = 1 := Units.ext weylMat_mul_self
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_genSz_zero, ← map_mul, h, map_one, OneMemClass.coe_one]

local macro "mem_tac" : tactic =>
  `(tactic| simp only [invWords, kerWords, centWords, List.mem_cons, eq_self_iff_true, true_or,
    or_true])

theorem kgSz8CoverInvolutions_holds :
    KGSz8CoverInvolutions := by
  intro K _ _ hq hZ hSz
  obtain ⟨e'⟩ := nonempty_mulEquiv_suzukiGroup_of_blueprint (X := K ⧸ Subgroup.center K)
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hSz⟩)))
  set e := e'.symm
  have hP := isPresentation e
  have hw : ∀ i, FreeGroup.mk (wWord i) ∈ commutator (FreeGroup (Fin 2)) :=
    fun i => mk_commWords_mem_commutator _
  have hwg : ∀ i, FreeGroup.lift (fun j => e (genSz j)) (FreeGroup.mk (wWord i)) = e (genSz i) :=
    fun i => by rw [lift_mulEquiv, lift_genSz_wWord]
  set π : Sz8Cover →* K ⧸ Subgroup.center K := coverMap hP hwg with hπ
  have hπmk : ∀ u, π (sz8Mk u) = e (FreeGroup.lift genSz (FreeGroup.mk u)) := fun u => by
    rw [hπ, sz8Mk, coverMap_mk, lift_mulEquiv]
  obtain ⟨hfin, -⟩ := card_cover_le
  have : Finite Sz8Cover := finite_presentedGroup_congr (coverRelators_wordSet rels wWord).symm
  have : Group.IsPerfect K := hq.1
  have hqs := QuotientGroup.mk'_surjective (Subgroup.center K)
  have hqk : (QuotientGroup.mk' (Subgroup.center K)).ker ≤ Subgroup.center K :=
    (QuotientGroup.ker_mk' _).le
  let φ : Sz8Cover →* K :=
    (hopfLift _ hqs hqk).comp (presentedCoverEquiv hP hw hwg).toMonoidHom
  have hφ : Function.Surjective φ :=
    (hopfLift_surjective _ hqs hqk).comp (presentedCoverEquiv hP hw hwg).surjective
  have hπφ : ∀ p, (φ p : K ⧸ Subgroup.center K) = π p := fun p => by
    change (QuotientGroup.mk' (Subgroup.center K)) (hopfLift _ hqs hqk
      (presentedCoverEquiv hP hw hwg p)) = π p
    rw [← MonoidHom.comp_apply, comp_hopfLift, hopfCoverMap_presentedCoverEquiv]
  obtain ⟨-, ⟨f⟩⟩ := multiplier_of_mulEquiv e
  let g : π.ker ≃* Multiplicative (ZMod 2 × ZMod 2) :=
    (griessHopfMultiplierEquivKer hP hw hwg).symm.trans
      (f.trans (MulEquiv.prodMultiplicative _ _).symm)
  have hK4 : IsKleinFour π.ker :=
    ⟨by rw [Nat.card_congr g.toEquiv]; exact IsKleinFour.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv g]; exact IsKleinFour.exponent_two⟩
  have hker : ∀ u, FreeGroup.lift genSz (FreeGroup.mk u) = 1 → sz8Mk u ∈ π.ker := fun u hu => by
    rw [MonoidHom.mem_ker, hπmk, hu, map_one]
  have hrel : ∀ s ∈ relStrings, sz8Mk (parseWord s) ∈ π.ker := fun s hs =>
    hker _ (lift_genSz_rels _ (List.mem_map_of_mem (List.mem_map_of_mem hs)))
  have hπx0 : π (sz8Mk [(0, true)]) = e (genSz 0) := by
    rw [hπmk]
    exact congrArg e (FreeGroup.lift_apply_of (f := genSz) (x := 0))
  have hxx : sz8Mk [(0, true)] * sz8Mk [(0, true)] = sz8Mk [(0, true), (0, true)] :=
    (sz8Mk_append _ _).symm
  have hx : sz8Mk [(0, true)] * sz8Mk [(0, true)] = 1 := by
    have hm : sz8Mk [(0, true), (0, true)] ∈ π.ker := by
      rw [← hxx, MonoidHom.mem_ker, map_mul, hπx0, ← map_mul, genSz_zero_mul_self, map_one]
    have h5m := hrel relFive (by simp only [relStrings, List.mem_cons, true_or, or_true])
    have h6m := hrel relSeven (by simp only [relStrings, List.mem_cons, true_or, or_true])
    have hne : ∀ {u v : π.ker}, (u : Sz8Cover) * (v : Sz8Cover)⁻¹ ≠ 1 → u ≠ v :=
      fun h huv => h (by rw [huv, mul_inv_cancel])
    have h5 : (⟨_, h5m⟩ : π.ker) ≠ 1 := fun h =>
      sz8Mk_kerWords_ne_one (u := parseWord relFive) (by mem_tac) (congrArg Subtype.val h)
    have h6 : (⟨_, h6m⟩ : π.ker) ≠ 1 := fun h =>
      sz8Mk_kerWords_ne_one (u := parseWord relSeven) (by mem_tac) (congrArg Subtype.val h)
    have h56 : (⟨_, h5m⟩ : π.ker) ≠ ⟨_, h6m⟩ := hne (by
      change sz8Mk (parseWord relFive) * (sz8Mk (parseWord relSeven))⁻¹ ≠ 1
      rw [← sz8Mk_invRev, ← sz8Mk_append]
      exact sz8Mk_kerWords_ne_one (by mem_tac))
    have hm5 : (⟨_, hm⟩ : π.ker) ≠ ⟨_, h5m⟩ := hne (by
      change sz8Mk [(0, true), (0, true)] * (sz8Mk (parseWord relFive))⁻¹ ≠ 1
      rw [← sz8Mk_invRev, ← sz8Mk_append]
      exact sz8Mk_invWords_ne_one (by mem_tac))
    have hm6 : (⟨_, hm⟩ : π.ker) ≠ ⟨_, h6m⟩ := hne (by
      change sz8Mk [(0, true), (0, true)] * (sz8Mk (parseWord relSeven))⁻¹ ≠ 1
      rw [← sz8Mk_invRev, ← sz8Mk_append]
      exact sz8Mk_invWords_ne_one (by mem_tac))
    have hm56 : (⟨_, hm⟩ : π.ker) ≠ ⟨_, h5m⟩ * ⟨_, h6m⟩ := hne (by
      change sz8Mk [(0, true), (0, true)] *
        (sz8Mk (parseWord relFive) * sz8Mk (parseWord relSeven))⁻¹ ≠ 1
      rw [← sz8Mk_append, ← sz8Mk_invRev, ← sz8Mk_append]
      exact sz8Mk_invWords_ne_one (by mem_tac))
    rw [hxx]
    by_contra hm1
    exact hm56 (IsKleinFour.eq_mul_of_ne_all h5 h6 h56
      (fun h => hm1 (congrArg Subtype.val h)) hm5 hm6)
  have hπx : π (sz8Mk [(0, true)]) ≠ 1 := by
    rw [hπx0]
    exact fun h => genSz_zero_ne_one (e.injective (h.trans (map_one e).symm))
  have hcomm : ∀ t, commWord t [(0, true)] ∈ centWords →
      π (sz8Mk t) * π (sz8Mk [(0, true)]) = π (sz8Mk [(0, true)]) * π (sz8Mk t) := by
    intro t ht
    have h := hker _ (lift_genSz_centWords ht)
    rw [MonoidHom.mem_ker, sz8Mk_commWord, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  refine kgSz8_of_cover hZ hSz π φ hφ hπφ IsKleinFour.card_four hx hπx
    (hcomm tOne (by mem_tac)) (hcomm tTwo (by mem_tac)) ?_ ?_ ?_
  · rw [← sz8Mk_commWord]
    exact sz8Mk_invWords_ne_one (by mem_tac)
  · rw [← sz8Mk_commWord]
    exact sz8Mk_invWords_ne_one (by mem_tac)
  · intro h
    apply sz8Mk_invWords_ne_one (u := commWord tOne [(0, true)] ++
      FreeGroup.invRev (commWord tTwo [(0, true)])) (by mem_tac)
    rw [sz8Mk_append, sz8Mk_invRev, sz8Mk_commWord, sz8Mk_commWord, h, mul_inv_cancel]

end CFSG.Quasithin.E2
