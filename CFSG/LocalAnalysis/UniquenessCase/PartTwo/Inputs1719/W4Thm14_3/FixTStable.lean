module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.Statement
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem fixV_ne_fixV_sup_of_stable {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L T : Subgroup (MulAut W)} (hT : IsPGroup 2 ↥T)
    {U : Subgroup W} (hU : U ≠ ⊥) (hUT : T ≤ stabSub U) (hUL : U ⊓ fixV L = ⊥) :
    fixV T ≠ fixV (L ⊔ T) := by
  have hU2 : IsPGroup 2 ↥U := (isPGroup_two_of_sq_eq_one hW).to_subgroup U
  obtain ⟨u, huU, hu1, huT⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15_Lin_exists_ne_one_mem_fixV hT hW hU
      fun x hx y hy => (mem_stabSub.mp (hUT hx) y).mpr hy
  intro heq
  have huL : u ∈ fixV L := B1.fixV_le_fixV le_sup_left (heq ▸ huT)
  exact hu1 (Subgroup.mem_bot.mp (hUL ▸ Subgroup.mem_inf.mpr ⟨huU, huL⟩))

private theorem le_stabSub_commSub_fixV {W : Type} [CommGroup W] {L S H T : Subgroup (MulAut W)}
    (hTL : T ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hTS : T ≤ Subgroup.normalizer (S : Set (MulAut W))) (hHL : H ≤ L)
    (hHS : H ≤ Subgroup.normalizer (S : Set (MulAut W)))
    (hB : L ⊓ Subgroup.normalizer (S : Set (MulAut W)) ≤ S ⊔ H) :
    T ≤ stabSub (commSub (fixV S) H) := by
  have hS : ∀ {A : Subgroup (MulAut W)},
      A ≤ Subgroup.normalizer (S : Set (MulAut W)) →
        ∀ a ∈ A, ∀ v ∈ fixV S, a v ∈ fixV S := by
    intro A hA
    exact B1Red.fixV_inv_of_normalizes fun a ha x hx =>
      (Subgroup.mem_normalizer_iff.mp (hA ha) x).mp hx
  refine B1.le_stabSub_of_invariant (A := T) (W := commSub (fixV S) H)
    fun t ht c hc => ?_
  refine Subgroup.closure_induction (p := fun c _ => t c ∈ commSub (fixV S) H) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨h, hh, w, hw, rfl⟩
    rw [map_mul, map_inv]
    have htw : t w ∈ fixV S := hS hTS t ht w hw
    have hpL : t * h * t⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hTL ht) h).mp (hHL hh)
    have hpN : t * h * t⁻¹ ∈ Subgroup.normalizer (S : Set (MulAut W)) :=
      (Subgroup.normalizer (S : Set (MulAut W))).mul_mem
        ((Subgroup.normalizer (S : Set (MulAut W))).mul_mem (hTS ht) (hHS hh))
        ((Subgroup.normalizer (S : Set (MulAut W))).inv_mem (hTS ht))
    have hp : t * h * t⁻¹ ∈
        L ⊓ Subgroup.normalizer (S : Set (MulAut W)) := ⟨hpL, hpN⟩
    have hp' : (t * h * t⁻¹ : MulAut W) ∈
        ((S ⊔ H : Subgroup (MulAut W)) : Set (MulAut W)) := hB hp
    rw [Subgroup.coe_mul_of_right_le_normalizer_left S H hHS] at hp'
    obtain ⟨s, hs, h', hh', hsp⟩ := Set.mem_mul.1 hp'
    have hkey : t (h w) = h' (t w) := by
      have h1 : (t * h * t⁻¹) (t w) = t (h w) := by
        show t (h (t⁻¹ (t w))) = t (h w)
        rw [MulAut.inv_apply_self]
      rw [← hsp] at h1
      have hsfix : s (h' (t w)) = h' (t w) :=
        mem_fixV.mp (hS hHS h' hh' (t w) htw) s hs
      rw [show (s * h') (t w) = s (h' (t w)) from rfl, hsfix] at h1
      exact h1.symm
    refine Subgroup.subset_closure ⟨h', hh', t w, htw, ?_⟩
    rw [← hkey]
  · rw [map_one]
    exact (commSub (fixV S) H).one_mem
  · intro a b _ _ ha hb
    rw [map_mul]
    exact (commSub (fixV S) H).mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact (commSub (fixV S) H).inv_mem ha

private theorem commSub_fixV_inf_fixV_eq_bot {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L S H : Subgroup (MulAut W)} (hHL : H ≤ L)
    (hH : Odd (Nat.card ↥H)) (hHS : H ≤ Subgroup.normalizer (S : Set (MulAut W))) :
    commSub (fixV S) H ⊓ fixV L = ⊥ := by
  have hS : ∀ h ∈ H, ∀ v ∈ fixV S, h v ∈ fixV S :=
    B1Red.fixV_inv_of_normalizes fun h hh x hx =>
      (Subgroup.mem_normalizer_iff.mp (hHS hh) x).mp hx
  have hle : commSub (fixV S) H ≤ fixV S := commSub_le_of_invariant hS
  have hdec := (coprime_decomp hH hW hS).2
  refine le_antisymm (fun x hx => ?_) bot_le
  have hxS : x ∈ fixV S := hle hx.1
  have hxH : x ∈ fixV H := B1.fixV_le_fixV hHL hx.2
  exact Subgroup.mem_bot.mp
    (hdec ▸ Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_inf.mpr ⟨hxS, hxH⟩⟩)

@[expose] def BorelMoves {W : Type} [CommGroup W] (L S : Subgroup (MulAut W)) : Prop :=
  ∃ H : Subgroup (MulAut W), H ≤ L ∧ H ≤ Subgroup.normalizer (S : Set (MulAut W)) ∧
    Odd (Nat.card ↥H) ∧ L ⊓ Subgroup.normalizer (S : Set (MulAut W)) ≤ S ⊔ H ∧
    commSub (fixV S) H ≠ ⊥

theorem borelMoves_map {G : Type} [Group G] {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (ψ : G ≃* ↥L) {U₀ T₀ : Subgroup G}
    (hU₀ : IsSylowIn 2 U₀ ⊤) (hT₀ : Odd (Nat.card ↥T₀))
    (hTN : T₀ ≤ Subgroup.normalizer (U₀ : Set G))
    (hN : Subgroup.normalizer (U₀ : Set G) ≤ U₀ ⊔ T₀) {x : W}
    (hx : ∀ u ∈ U₀, ((ψ u : ↥L) : MulAut W) x = x)
    (ht : ∃ t ∈ T₀, ((ψ t : ↥L) : MulAut W) x ≠ x) :
    IsSylowIn 2 (U₀.map (L.subtype.comp ψ.toMonoidHom)) L ∧
      BorelMoves L (U₀.map (L.subtype.comp ψ.toMonoidHom)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite G := Finite.of_injective (ψ : G → ↥L) ψ.injective
  let ψ' : G →* MulAut W := L.subtype.comp ψ.toMonoidHom
  let S₀ : Subgroup (MulAut W) := U₀.map ψ'
  let H : Subgroup (MulAut W) := T₀.map ψ'
  have hψ'inj : Function.Injective ψ' := by
    intro a b hab
    exact ψ.injective (L.subtype_injective hab)
  have hψ'range : ψ'.range = L := by
    change (L.subtype.comp ψ.toMonoidHom).range = L
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  change IsSylowIn 2 S₀ L ∧ BorelMoves L S₀
  have hcardU : Nat.card U₀ = 2 ^ (Nat.card G).factorization 2 := by
    simpa [Subgroup.card_top] using hU₀.card_eq
  have hS₀syl : IsSylowIn 2 S₀ L := by
    refine isSylowIn_of_card_eq ?_ ?_
    · exact (Subgroup.map_le_range ψ' U₀).trans hψ'range.le
    · rw [Subgroup.card_map_of_injective hψ'inj, hcardU, Nat.card_congr ψ.toEquiv]
  have hHleL : H ≤ L := (Subgroup.map_le_range ψ' T₀).trans hψ'range.le
  have hHcard : Nat.card H = Nat.card T₀ := Subgroup.card_map_of_injective hψ'inj
  have hHodd : Odd (Nat.card H) := by rw [hHcard]; exact hT₀
  have hHN : H ≤ Subgroup.normalizer (S₀ : Set (MulAut W)) := by
    have h := (Subgroup.map_mono (f := ψ') hTN).trans
      (Subgroup.le_normalizer_map (f := ψ') (H := U₀))
    simpa [H, S₀] using h
  have hLH : L ⊓ Subgroup.normalizer (S₀ : Set (MulAut W)) ≤ S₀ ⊔ H := by
    intro g hg
    obtain ⟨hgL, hgN⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨z, hz⟩ : ∃ z, ψ' z = g := by
      have hgr : g ∈ ψ'.range := by
        rw [hψ'range]
        exact hgL
      exact MonoidHom.mem_range.mp hgr
    have hzN : z ∈ Subgroup.normalizer (U₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        have h1 : g * ψ' u * g⁻¹ ∈ S₀ :=
          (Subgroup.mem_normalizer_iff.mp hgN (ψ' u)).mp (Subgroup.mem_map_of_mem ψ' hu)
        have h2 : ψ' (z * u * z⁻¹) = g * ψ' u * g⁻¹ := by
          rw [map_mul, map_mul, map_inv, hz]
        rw [← h2] at h1
        exact (Subgroup.mem_map_iff_mem hψ'inj).mp h1
      · intro hu
        have h2 : ψ' (z * u * z⁻¹) ∈ S₀ := Subgroup.mem_map_of_mem ψ' hu
        have h3 : g * ψ' u * g⁻¹ ∈ S₀ := by
          have heq : ψ' (z * u * z⁻¹) = g * ψ' u * g⁻¹ := by
            rw [map_mul, map_mul, map_inv, hz]
          rwa [heq] at h2
        exact (Subgroup.mem_map_iff_mem hψ'inj).mp
          ((Subgroup.mem_normalizer_iff.mp hgN (ψ' u)).mpr h3)
    have hzB : z ∈ U₀ ⊔ T₀ := hN hzN
    have hmem : ψ' z ∈ S₀ ⊔ H := by
      have h3 : ψ' z ∈ (U₀ ⊔ T₀).map ψ' := Subgroup.mem_map_of_mem ψ' hzB
      simpa [S₀, H, Subgroup.map_sup] using h3
    rwa [hz] at hmem
  have hcomm : commSub (fixV S₀) H ≠ ⊥ := by
    have hxfix : x ∈ fixV S₀ := by
      rw [mem_fixV]
      rintro y ⟨u, hu, rfl⟩
      exact hx u hu
    have hxnot : x ∉ fixV H := by
      rintro hxH
      obtain ⟨t, htT, htne⟩ := ht
      exact htne ((mem_fixV.mp hxH) (ψ' t) (Subgroup.mem_map_of_mem ψ' htT))
    have hfixH : ∀ g ∈ H, ∀ m ∈ fixV S₀, g m ∈ fixV S₀ :=
      B1Red.fixV_inv_of_normalizes fun g hg y hy =>
        (Subgroup.mem_normalizer_iff.mp (hHN hg) y).mp hy
    have hdec := (coprime_decomp hHodd hW hfixH).1
    intro hbot
    have hle : fixV S₀ ≤ fixV H := by
      rw [← hdec, hbot, bot_sup_eq]
      exact inf_le_right
    exact hxnot (hle hxfix)
  exact ⟨hS₀syl, ⟨H, hHleL, hHN, hHodd, hLH, hcomm⟩⟩

theorem fixV_ne_fixV_sup_of_borelMoves {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L S T : Subgroup (MulAut W)} (hT : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hTS : T ≤ Subgroup.normalizer (S : Set (MulAut W))) (h : BorelMoves L S) :
    fixV T ≠ fixV (L ⊔ T) := by
  obtain ⟨H, hHL, hHS, hH, hB, hne⟩ := h
  exact fixV_ne_fixV_sup_of_stable hW hT hne (le_stabSub_commSub_fixV hTL hTS hHL hHS hB)
    (commSub_fixV_inf_fixV_eq_bot hW hHL hH hHS)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
