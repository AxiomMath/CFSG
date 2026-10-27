module

public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvSolvable
public import CFSG.LieType.Chevalley.LangWeylInvolutionStrong
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
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
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Chevalley.RootSpace

theorem odd_card_rootCharStabilizerSubgroup_of_familyKernel_empty
    {τ : Tag} {L : Type} [Field L] {m : ℕ} (hm : Odd m) {a : Fin τ.rank → Lˣ}
    (ha : ∀ i, a i ^ m = 1)
    (hKer : familyKernel (fun _ : Unit => a) = ∅) :
    Odd (Nat.card ↥(rootCharStabilizerSubgroup a)) := by
  classical
  refine Nat.not_even_iff_odd.1 ?_
  intro heven
  have hdvd : 2 ∣ Nat.card ↥(rootCharStabilizerSubgroup a) := even_iff_two_dvd.1 heven
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(rootCharStabilizerSubgroup a)) 2 hdvd
  have hw2sub : w ^ 2 = 1 := by
    rw [← hw]
    exact pow_orderOf_eq_one w
  have hw2 : ((w : WeylGroup τ) ^ 2) = 1 := by
    simpa using congrArg Subtype.val hw2sub
  obtain ⟨βs, hlen, hroots, hpair, hprod, hspan, hcomm, hnil⟩ :=
    exceptional_Lang_Weyl_involution_orthogonal_reflections τ (w : WeylGroup τ) hw2
  have hne : βs ≠ [] := by
    rintro rfl
    have hw1 : (w : WeylGroup τ) = 1 := by simpa using hprod
    have hw1' : w = 1 := Subtype.ext hw1
    rw [hw1', orderOf_one] at hw
    omega
  obtain ⟨β, hβmem⟩ := List.exists_mem_of_ne_nil βs hne
  have hβroot : IsRoot τ β := hroots β hβmem
  have hβspan : (ofLattice β : RootSpace τ) ∈
      (Submodule.span ℝ (ofLattice '' {β | β ∈ βs}) : Set (RootSpace τ)) :=
    Submodule.subset_span (Set.mem_image_of_mem _ hβmem)
  rw [hspan] at hβspan
  have hwβR : weylAct τ (w : WeylGroup τ) (ofLattice β) = -ofLattice β := hβspan
  have hwβ : (w : WeylGroup τ) • β = -β := by
    apply ofLattice_injective
    rw [← weylAct_ofLattice, hwβR, ofLattice_neg]
  have hχ : rootChar a β = rootChar a (-β) := by
    have h := (w : ↥(rootCharStabilizerSubgroup a)).2 β
    rw [hwβ] at h
    exact h.symm
  have hχinv : rootChar a β = (rootChar a β)⁻¹ := by
    calc rootChar a β = rootChar a (-β) := hχ
      _ = (rootChar a β)⁻¹ := by
        rw [show -β = (-1 : ℤ) • β by simp, rootChar_zsmul, zpow_neg_one]
  have hχsq : rootChar a β ^ 2 = 1 := by
    have h := congrArg (fun u : Lˣ => u * rootChar a β) hχinv
    simpa [pow_two, mul_assoc] using h
  have hχm : rootChar a β ^ m = 1 := by
    rw [rootChar, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha i, one_zpow]
  have hχ1 : rootChar a β = 1 := by
    have hord : orderOf (rootChar a β) ∣ Nat.gcd 2 m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hχsq) (orderOf_dvd_of_pow_eq_one hχm)
    have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact hord
  have hβker : β ∈ familyKernel (fun _ : Unit => a) := ⟨hβroot, fun _ => hχ1⟩
  rw [hKer] at hβker
  exact hβker

theorem isSolvable_rootCharStabilizerSubgroup_of_familyKernel_empty
    {τ : Tag} {L : Type} [Field L] {m : ℕ} (hm : Odd m) {a : Fin τ.rank → Lˣ}
    (ha : ∀ i, a i ^ m = 1)
    (hKer : familyKernel (fun _ : Unit => a) = ∅) :
    Group.IsSolvable ↥(rootCharStabilizerSubgroup a) := by
  haveI : Finite (WeylGroup τ) :=
    (exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.1
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _
    (odd_card_rootCharStabilizerSubgroup_of_familyKernel_empty hm ha hKer)

theorem isSolvable_centralizer_of_familyKernel_empty_of_odd
    {τ : Tag} {L : Type} [Field L] {m : ℕ} (hm : Odd m) (a : Fin τ.rank → Lˣ)
    (ha : ∀ i, a i ^ m = 1) (hKer : familyKernel (fun _ : Unit => a) = ∅) :
    Group.IsSolvable ↥(familyCentralizer τ L (fun _ : Unit => a)) := by
  classical
  have hker' : rootCharKernel a = ∅ := by
    rw [← hKer]
    ext α
    change (IsRoot τ α ∧ rootChar a α = 1) ↔
      (IsRoot τ α ∧ ∀ _ : Unit, rootChar a α = 1)
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 ()⟩⟩
  have hKR : kernelReflectionGroup a = ⊥ := by
    rw [kernelReflectionGroup, hker']
    simp
  have hNbot : (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) = ⊥ := by
    rw [hKR]
    ext x
    simp [Subgroup.mem_subgroupOf]
  haveI hHs : Group.IsSolvable ↥(rootCharStabilizerSubgroup a) :=
    isSolvable_rootCharStabilizerSubgroup_of_familyKernel_empty hm ha hKer
  have hgroup : familyGroup (K := L) (fun _ : Unit => a) = torusGroup τ L := by
    rw [familyGroup, hKer, rootSpan]
    simp
  have hmono : ∀ g : ↥(familyCentralizer τ L (fun _ : Unit => a)),
      ∃ w ∈ rootCharStabilizerSubgroup a, ∃ m ∈ torusGroup τ L,
        (g : ModGL τ L) = m * canonicalRep (coxeterSystem τ) L w := by
    intro g
    obtain ⟨w, hw, m, hm, hmg⟩ := familyCentralizer_le_mul τ L (fun _ : Unit => a) g.2
    rw [hgroup] at hm
    exact ⟨w, mem_rootCharStabilizerSubgroup.2 (hw ()), m, hm, hmg⟩
  have hmem : ∀ g : ↥(familyCentralizer τ L (fun _ : Unit => a)),
      (g : ModGL τ L) ∈ monomialSubgroup τ L := by
    intro g
    obtain ⟨w, -, m, hm, hmg⟩ := hmono g
    rw [hmg]
    exact mul_mem (Subgroup.mem_sup_left hm)
      (canonicalRep_mem_monomialSubgroup' (K := L) w)
  let ψ : ↥(familyCentralizer τ L (fun _ : Unit => a)) →* monomialSubgroup τ L :=
    MonoidHom.codRestrict (Subgroup.subtype _) _ hmem
  have hψ : Function.Injective ψ := by
    intro g g' h
    exact Subtype.ext (congrArg (fun x : monomialSubgroup τ L => (x : ModGL τ L)) h)
  obtain ⟨ρ, hρmaps, hsolv⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.isSolvable_comap_weylQuotient τ L
      (rootCharStabilizerSubgroup a)
  have hρψ : ∀ g, ρ (ψ g) ∈ rootCharStabilizerSubgroup a := by
    intro g
    obtain ⟨w, hw, m, hm, hmg⟩ := hmono g
    have h1 : MapsRootLines (ψ g : (Module.End L (RootModule τ L))ˣ) (1 * w) := by
      have e : (ψ g : (Module.End L (RootModule τ L))ˣ) =
          m * canonicalRep (coxeterSystem τ) L w := hmg
      rw [e]
      exact (mapsRootLines_of_mem_torusGroup hm).mul (mapsRootLines_canonicalRep w)
    rw [(hρmaps (ψ g)).unique h1, one_mul]
    exact hw
  let ψ' : ↥(familyCentralizer τ L (fun _ : Unit => a)) →*
      ↥((rootCharStabilizerSubgroup a).comap ρ) :=
    ψ.codRestrict ((rootCharStabilizerSubgroup a).comap ρ) hρψ
  haveI := hsolv
  refine Group.isSolvable_of_isSolvable_injective (f := ψ') ?_
  intro g g' h
  exact hψ (congrArg Subtype.val h)

theorem isSolvable_centralizer_of_familyKernel_empty_of_odd_inter
    {τ : Tag} {L : Type} [Field L] {m : ℕ} (hm : Odd m) (a : Fin τ.rank → Lˣ)
    (ha : ∀ i, a i ^ m = 1) (hKer : familyKernel (fun _ : Unit => a) = ∅) :
    Group.IsSolvable ↥(adjointGroup τ L ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
  classical
  have hEq : (adjointGroup τ L ⊓ Subgroup.centralizer {rootDiagUnit τ a}) =
      familyCentralizer τ L (fun _ : Unit => a) := by
    ext g
    simp only [familyCentralizer, Subgroup.mem_inf, Subgroup.mem_iInf]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 ()⟩⟩
  have hfam := isSolvable_centralizer_of_familyKernel_empty_of_odd hm a ha hKer
  let e : ↥(adjointGroup τ L ⊓ Subgroup.centralizer {rootDiagUnit τ a}) →*
      ↥(familyCentralizer τ L (fun _ : Unit => a)) :=
    MonoidHom.codRestrict (Subgroup.subtype _) _ (fun x => hEq ▸ x.2)
  have he : Function.Injective e := fun x y h =>
    Subtype.ext (congrArg
      (fun z : ↥(familyCentralizer τ L (fun _ : Unit => a)) => (z : ModGL τ L)) h)
  haveI : Group.IsSolvable ↥(familyCentralizer τ L (fun _ : Unit => a)) := hfam
  exact Group.isSolvable_of_isSolvable_injective (f := e) he

theorem exists_conj_torusGroup_of_prime_order
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : ModGL Tag.E6 L} (hx : x ∈ adjointGroup Tag.E6 L) (hxp : x ^ p = 1) :
    ∃ g ∈ adjointGroup Tag.E6 L, g⁻¹ * x * g ∈ torusGroup Tag.E6 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmon : MonomialToralAt Tag.E6 p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp hp2
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_conj_torusGroup_of_pow_eq_one
    hp hmon (by omega) halg hx hxp

end CFSG.StandardType
