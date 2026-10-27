module

public import CFSG.RankThree.PartOne.F106.OddRadAt
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.RankThree.PartOne.F106.OddRadSpInner
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlane
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
import CFSG.RankThree.PartOne.S11d.PSpCyclic
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift

public section

namespace CFSG.RankThree.PartOne.F106.OddRadSp

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical
  CFSG.ComponentClassification.PresentationLocal
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.RankThree.PartOne.KCSpComm (solvableRadical_sympFour)
open CFSG.LieType.SteinbergBR (solvableRadical_map_equiv)
open scoped commutatorElement

variable {K : Type} [Field K] {r : ℕ}

theorem perfectResidual_le_ker_of_comm {G A : Type*} [Group G] [CommGroup A] (φ : G →* A) :
    perfectResidual G ≤ φ.ker := by
  refine (iInf_le _ 1).trans ?_
  rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)]

theorem four_le_natDegree_of_nontrivial {x : StatedSp r K}
    (blocks : SpPrimaryBlocks 2 1 5 x (proj r K x)) {h : primaryFactors (spEnd x)}
    (hh : (h : K[X]) ≠ X - 1) : 4 ≤ (h : K[X]).natDegree := by
  have hdeg : 1 ≤ (h : K[X]).natDegree :=
    (irreducible_of_mem_primaryFactors h.2).natDegree_pos
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · obtain ⟨d, hd, hpd, -⟩ := (blocks.selfDual h hh hself).exists_half
    have hd2 : 2 ≤ d := by
      by_contra hlt
      interval_cases d <;> omega
    omega
  · have hdvd := (blocks.paired h (Ne.symm hself)).dvd
    by_contra hlt
    interval_cases hn : (h : K[X]).natDegree <;> omega

variable [Finite K]

theorem eq_one_of_mem_perfectResidual_radical_sp_two (hK : Nat.card K = 2) (hr1 : 1 ≤ r)
    (hr4 : r ≤ 4) (x : StatedSp r K) (hx : orderOf x = 5)
    {y : ↥(Subgroup.centralizer ({x} : Set (StatedSp r K)))}
    (hyD : y ∈ perfectResidual ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))))
    (hyR : y ∈ solvableRadical ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))))
    (hy2 : y ^ 2 = 1) : y = 1 := by
  classical
  have hK' : Nat.card K = 2 ^ 1 := by simpa using hK
  obtain ⟨blocks, hsq⟩ := blocks_of_orderOf_five hK' le_rfl hr1 x hx
  have hnt : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
      ∀ v ∈ primaryComponent (spEnd x) (h : K[X]), spEnd (y : StatedSp r K) v = v := fun h hh =>
    involution_radical_trivial_on_block hK' hsq
      (spBlockFacts_nontrivial (by norm_num) (by norm_num) blocks h hh) hyR hy2
  by_cases hX : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)
  swap
  · apply Subtype.ext
    exact eq_one_of_trivial_on_blocks blocks fun h v hv =>
      hnt h (fun e => hX (e ▸ h.2)) v hv
  have hyF : (y : StatedSp r K) ∈ spFixedFactor x := by
    refine mem_spSupported.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mp y.2, ?_⟩
    intro k hk hkO v hv
    exact hnt ⟨k, hk⟩ (fun e => hkO (Set.mem_singleton_iff.mpr e)) v hv
  obtain ⟨s, hs, -⟩ := blocks.rank
  have hd : spFixedDim x = 2 * s := hs
  have hd0 : 0 < spFixedDim x := by
    have hne := primaryComponent_ne_bot hsq hX
    have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne
    exact Module.finrank_pos
  rcases (by omega : s = 1 ∨ s = 2 ∨ 3 ≤ s) with hs1 | hs2 | hs3
  ·
    have hd2 : spFixedDim x = 2 := by omega
    have hm1 : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
        primaryMultiplicity (spEnd x) (h : K[X]) ≤ 1 := by
      intro h hh
      by_contra hlt
      push Not at hlt
      have h4 := four_le_natDegree_of_nontrivial blocks hh
      have hsum := finrank_eq_sum_degree_mul_multiplicity hsq
      have hV : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by simp [two_mul]
      have hne : h ≠ ⟨X - 1, hX⟩ := fun e => hh (by rw [e])
      have hpair : (h : K[X]).natDegree * primaryMultiplicity (spEnd x) (h : K[X]) +
          (X - 1 : K[X]).natDegree * primaryMultiplicity (spEnd x) (X - 1) ≤
          ∑ a : primaryFactors (spEnd x), (a : K[X]).natDegree *
            primaryMultiplicity (spEnd x) (a : K[X]) := by
        rw [← Finset.sum_pair (f := fun a : primaryFactors (spEnd x) =>
          (a : K[X]).natDegree * primaryMultiplicity (spEnd x) (a : K[X])) hne]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hmX : primaryMultiplicity (spEnd x) (X - 1) = 2 := by
        rw [show (X - 1 : K[X]) = X - C 1 by rw [C_1], primaryMultiplicity_X_sub_C_eq]
        exact hd2
      have hnX : (X - 1 : K[X]).natDegree = 1 := natDegree_X_sub_C 1
      have := Nat.mul_le_mul h4 hlt
      rw [hmX, hnX] at hpair
      omega
    have hDnt : ∀ g ∈ perfectResidual ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))),
        ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
        ∀ v ∈ primaryComponent (spEnd x) (h : K[X]), spEnd (g : StatedSp r K) v = v := by
      intro g hg h hh v hv
      let ψ0 : ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))) →*
          ↥(gl_centralizer (spLin r K x)) :=
        ((spLin r K).comp (Subgroup.centralizer ({x} : Set (StatedSp r K))).subtype).codRestrict _
          (fun g => mem_gl_centralizer.mpr
            (spEnd_comm_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp g.2)))
      let ψ : ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))) →*
          (AdjoinRoot (h : K[X]))ˣ := (blockDetHom (spLin r K x) (h : K[X])).comp ψ0
      have hker := perfectResidual_le_ker_of_comm ψ hg
      have hdet : blockGLDet (spEnd x) (h : K[X])
          (blockRestrict (spLin r K x) (h : K[X]) (ψ0 g)) = 1 := hker
      have h1 : blockRestrict (spLin r K x) (h : K[X]) (ψ0 g) = 1 :=
        eq_one_of_det_eq_one_of_finrank_le_one (E := AdjoinRoot (h : K[X])) (hm1 h hh) _ (by
          have := congrArg Units.val hdet
          simpa [blockGLDet] using this)
      have h2 := blockApply_blockRestrict (spLin r K x) (h : K[X]) (ψ0 g) v hv
      rw [h1, blockApply_one] at h2
      exact h2.symm
    have hDF : ∀ g ∈ perfectResidual ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))),
        (g : StatedSp r K) ∈ spFixedFactor x := fun g hg =>
      mem_spSupported.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mp g.2, fun k hk hkO v hv =>
        hDnt g hg ⟨k, hk⟩ (fun e => hkO (Set.mem_singleton_iff.mpr e)) v hv⟩
    have hF6 : Nat.card ↥(spFixedFactor x) = 6 := by
      rw [card_spFixedFactor_of_dim_two blocks hd2, hK]
      norm_num
    have hFsolv : Group.IsSolvable ↥(spFixedFactor x) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega)
    let ι : ↥(perfectResidual ↥(Subgroup.centralizer ({x} : Set (StatedSp r K)))) →*
        ↥(spFixedFactor x) :=
      (((Subgroup.centralizer ({x} : Set (StatedSp r K))).subtype).comp
        (perfectResidual ↥(Subgroup.centralizer ({x} : Set (StatedSp r K)))).subtype).codRestrict _
        (fun g => hDF g.1 g.2)
    have hDsolv : Group.IsSolvable
        ↥(perfectResidual ↥(Subgroup.centralizer ({x} : Set (StatedSp r K)))) :=
      Group.isSolvable_of_isSolvable_injective (f := ι) (fun a b hab => by
        have h1 := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h1))
    have hperf := CFSG.Wreathed.PrimewisePerfectLift.perfectResidual_isPerfect
      (G := ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))))
    have hsub : Subsingleton
        ↥(perfectResidual ↥(Subgroup.centralizer ({x} : Set (StatedSp r K)))) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable _ hDsolv
    exact congrArg Subtype.val (Subsingleton.elim (⟨y, hyD⟩ : ↥(perfectResidual
      ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))))) 1)
  ·
    have hd4 : spFixedDim x = 4 := by omega
    obtain ⟨φ, -⟩ := blocks.fixedFactor hX
    have hB : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
      fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
    obtain ⟨E⟩ := nonempty_mulEquiv_sympFour hK hB blocks.fixed_nondegenerate hd4
    have hFC : spFixedFactor x ≤ Subgroup.centralizer ({x} : Set (StatedSp r K)) :=
      spFixedFactor_le_centralizer x
    have hFCn : ((spFixedFactor x).subgroupOf
        (Subgroup.centralizer ({x} : Set (StatedSp r K)))).Normal :=
      ⟨fun n hn g => spFixedFactor_normalized x g g.2 n hn⟩
    let e : ↥((spFixedFactor x).subgroupOf
        (Subgroup.centralizer ({x} : Set (StatedSp r K)))) ≃* sympFour :=
      (Subgroup.subgroupOfEquivOfLe hFC).trans (φ.trans E)
    have hradFC : solvableRadical ↥((spFixedFactor x).subgroupOf
        (Subgroup.centralizer ({x} : Set (StatedSp r K)))) = ⊥ := by
      have h := solvableRadical_map_equiv e
      rw [solvableRadical_sympFour] at h
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
    have h1 := (CFSG.RankThree.solvable_radical_subnormal_intersection hFCn.isSubnormal).1
    have h1' : ((solvableRadical ↥((spFixedFactor x).subgroupOf
        (Subgroup.centralizer ({x} : Set (StatedSp r K)))))).map
        ((spFixedFactor x).subgroupOf
          (Subgroup.centralizer ({x} : Set (StatedSp r K)))).subtype = _ ⊓ _ := h1
    rw [hradFC, Subgroup.map_bot] at h1'
    have : y ∈ (spFixedFactor x).subgroupOf (Subgroup.centralizer ({x} : Set (StatedSp r K))) ⊓
        solvableRadical ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))) := ⟨hyF, hyR⟩
    rw [← h1'] at this
    exact Subgroup.mem_bot.mp this
  ·
    have hfacts_fix := spBlockFacts_of_spFixed hsq blocks hX
      (Or.inr (Or.inr ⟨hK, show 6 ≤ spFixedDim x by omega⟩))
    have hfix := involution_radical_trivial_on_block hK' hsq hfacts_fix hyR hy2
    apply Subtype.ext
    refine eq_one_of_trivial_on_blocks blocks fun h v hv => ?_
    by_cases hh : (h : K[X]) = X - 1
    · have : h = ⟨X - 1, hX⟩ := Subtype.ext hh
      subst this
      exact hfix v hv
    · exact hnt h hh v hv

theorem odd_card_radical_perfectResidual_centralizer_sp_two (hK : Nat.card K = 2) (hr1 : 1 ≤ r)
    (hr4 : r ≤ 4) (x : StatedSp r K) (hx : orderOf x = 5) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual
      ↥(Subgroup.centralizer ({x} : Set (StatedSp r K)))))) := by
  by_contra hodd
  obtain ⟨y, hyD, hyR, hy2, hy1⟩ := exists_involution_radical_of_not_odd hodd
  exact hy1 (eq_one_of_mem_perfectResidual_radical_sp_two hK hr1 hr4 x hx hyD hyR hy2)

theorem oddRadConcl_conj_sp_two (hK : Nat.card K = 2) (hr : 3 ≤ r) (hr4 : r ≤ 4)
    (a : StatedProj (StatedSp r K)) (ha : orderOf a = 5) :
    OddRadConcl (StatedProj (StatedSp r K)) (MulAut.conj a) :=
  oddRadConcl_conj_of_centralizer (f := 1) (by simpa using hK) le_rfl (by omega)
    (fun x hx => odd_card_radical_perfectResidual_centralizer_sp_two hK (by omega) hr4 x hx) a ha

end CFSG.RankThree.PartOne.F106.OddRadSp
