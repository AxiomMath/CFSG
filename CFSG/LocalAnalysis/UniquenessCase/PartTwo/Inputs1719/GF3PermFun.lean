module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3PermPieces
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3SL2Normalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFundPairs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenFund
public import CFSG.ClassicalInvolution.Uniform.U3Edge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open
open scoped MatrixGroups
open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver fundPred isFundamentalOver_map_mulEquiv)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.Asc77
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm (PermWitness)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie


private theorem card_sl2_galoisField_three : Nat.card (SL(2, GaloisField 3 1)) = 24 := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card 3 1 one_ne_zero]
  norm_num

private theorem subgroupMap_injective_of_fundamental {X : Type} [Group X] {p : ℕ}
    [Fact p.Prime] {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hA1 : ¬ (t = .PSL ∧ n = 2))
    {ψ : (modelUniv t n p e Fact.out).K →* X}
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K)
    {R : Subgroup (modelUniv t n p e Fact.out).K} (hR : R ∈ ModelFund p t n e) :
    Function.Injective (ψ.subgroupMap R) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxker : ((x : ↥R) : (modelUniv t n p e Fact.out).K) ∈ ψ.ker := by
    have hx' : x ∈ (ψ.subgroupMap R).ker := MonoidHom.mem_ker.mpr hx
    rwa [Subgroup.ker_subgroupMap] at hx'
  have hxZ : ((x : ↥R) : (modelUniv t n p e Fact.out).K) ∈
      Subgroup.center (modelUniv t n p e Fact.out).K := hker hxker
  have hx1 : ((x : ↥R) : (modelUniv t n p e Fact.out).K) = 1 :=
    CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p t n e hfund hadm hA1 R hR x x.2 (by
      intro y
      have hc : ((x : ↥R) : (modelUniv t n p e Fact.out).K) * y =
          y * ((x : ↥R) : (modelUniv t n p e Fact.out).K) :=
        (Subgroup.mem_center_iff.mp hxZ y).symm
      rw [hc]
      have h1 : y * ((x : ↥R) : (modelUniv t n p e Fact.out).K) *
          ((x : ↥R) : (modelUniv t n p e Fact.out).K)⁻¹ * y⁻¹ = 1 := by group
      rw [h1]
      exact Subgroup.one_mem _)
  exact Subtype.ext hx1

private theorem exists_equiv_sl2_of_mem_funSet {X : Type} [Group X] [Finite X] {U : Sylow 2 X}
    {K : Subgroup X} (hK : K ∈ FunSet (fundPred 3) X (U : Subgroup X)) :
    Nonempty (↥K ≃* SL(2, GaloisField 3 1)) ∨
      Nonempty (↥K ≃* SL(2, GaloisField 3 3)) := by
  obtain ⟨hfun, -⟩ := hK
  obtain ⟨t, n, p, e, hp, hp2, hq, hfund, hadm, ψ, hsurj, hker, R, hR, rfl⟩ := hfun
  have he : 1 ≤ e := hadm.2.1
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := by
      rw [hq]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  have he1 : e = 1 := by
    have h3 : 3 ^ e = 3 ^ 1 := by rw [← hq, pow_one]
    exact Nat.pow_right_injective (by norm_num : 1 < 3) h3
  subst he1
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    exact hadm.2.2.2.2 rfl
  have hinj : Function.Injective (ψ.subgroupMap R) :=
    subgroupMap_injective_of_fundamental (by norm_num) hfund hadm hA1 hker hR
  let eRK : ↥R ≃* ↥(R.map ψ) :=
    MulEquiv.ofBijective (ψ.subgroupMap R) ⟨hinj, ψ.subgroupMap_surjective R⟩
  have hshape :=
    CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      (p := 3) (e := 1) (by norm_num) hfund hadm hR
  rcases hshape with h | ⟨-, h⟩
  · obtain ⟨eR⟩ := h
    exact Or.inl ⟨eRK.symm.trans eR⟩
  · obtain ⟨eR⟩ := h
    exact Or.inr ⟨eRK.symm.trans eR⟩

private theorem member_piece_facts {X : Type} [Group X] [Finite X] {U : Sylow 2 X}
    {K : Subgroup X} (hK : K ∈ FunSet (fundPred 3) X (U : Subgroup X)) :
    (∀ x ∈ K ⊓ normalizer (((U : Subgroup X) ⊓ K : Subgroup X) : Set X),
        x ^ 3 ∈ (U : Subgroup X) ⊓ K) ∧
      (∀ x ∈ K ⊓ normalizer (((U : Subgroup X) ⊓ K : Subgroup X) : Set X),
        ∀ y ∈ K ⊓ normalizer (((U : Subgroup X) ⊓ K : Subgroup X) : Set X),
          x * y * x⁻¹ * y⁻¹ ∈ (U : Subgroup X) ⊓ K) ∧
      (∃ a ∈ K ⊓ normalizer (((U : Subgroup X) ⊓ K : Subgroup X) : Set X), orderOf a = 3) ∧
      (∀ c ∈ K, (∀ y ∈ K, c * y = y * c) → c * c = 1) ∧
      ¬ IsMulCommutative ↥K := by
  rcases exists_equiv_sl2_of_mem_funSet hK with h | h
  · obtain ⟨e⟩ := h
    have h3 : Nat.card (GaloisField 3 1) % 8 = 3 := by
      rw [GaloisField.card 3 1 one_ne_zero]
      norm_num
    exact GF3.sl2_mod_eight_three_facts h3 e hK.2
  · obtain ⟨e⟩ := h
    have h27 : Nat.card (GaloisField 3 3) % 8 = 3 := by
      rw [GaloisField.card 3 3 (by norm_num)]
      norm_num
    exact GF3.sl2_mod_eight_three_facts h27 e hK.2

private theorem card_fund_g2 {k : ℕ} (hadm : StatedLieAdmissible .G2 k 3 1)
    {R : Subgroup (modelUniv .G2 k 3 1 Fact.out).K} (hR : R ∈ ModelFund 3 .G2 k 1) :
    Nat.card R = 24 := by
  obtain ⟨eR⟩ : Nonempty (↥R ≃* SL(2, GaloisField 3 1)) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q.nonempty_equiv_sl2_fund_g2
      (p := 3) (e := 1) hR
  exact (Nat.card_congr eR.toEquiv).trans card_sl2_galoisField_three

private theorem card_fund_other {t : StatedLieTag} {k : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t k 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup (modelUniv t k 3 1 Fact.out).K} (hR : R ∈ ModelFund 3 t k 1) :
    Nat.card R = 24 := by
  obtain ⟨eR⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    (p := 3) (e := 1) (by norm_num) hfund hadm hG2 hD4 hR
  rw [Nat.card_congr eR.toEquiv, card_sl2_galoisField_three]

private theorem exists_commuting_fund_trialityD4_long {k : ℕ}
    (hfund : IsFundTag .trialityD4) (hadm : StatedLieAdmissible .trialityD4 k 3 1)
    {i j : Fin (modelUniv .trialityD4 k 3 1 Fact.out).D.rank}
    (hAij : (modelUniv .trialityD4 k 3 1 Fact.out).D.cartan i j = -3)
    (hAji : (modelUniv .trialityD4 k 3 1 Fact.out).D.cartan j i = -1)
    (hj : CFSG.ClassicalInvolution.ModelFacts.IsLongNode .trialityD4 k j.val) :
    ∃ R ∈ ModelFund 3 .trialityD4 k 1, ∃ S ∈ ModelFund 3 .trialityD4 k 1,
      Commutes R S ∧ Nat.card R = 24 := by
  obtain ⟨_, _, _, hext⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum .trialityD4 k 3 1 Fact.out
      (CFSG.ClassicalInvolution.Asc77.ih8_isFundTag_mf hfund) hadm
  have hjl :=
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .trialityD4 k 3 1 Fact.out
      (CFSG.ClassicalInvolution.Asc77.ih8_isFundTag_mf hfund) hadm j hj
  have hA := (modelUniv .trialityD4 k 3 1 Fact.out).D.isFiniteType
  set wi := (coxeterMatrix hA).toCoxeterSystem.simple i with hwi
  set wj := (coxeterMatrix hA).toCoxeterSystem.simple j with hwj
  have hγ : CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot
      (modelUniv .trialityD4 k 3 1 Fact.out).D
      (weylAction hA wj (weylAction hA wi (Pi.single j 1))) :=
    CFSG.ClassicalInvolution.ModelFacts.IsLongest.map_weylAction
      (CFSG.ClassicalInvolution.ModelFacts.IsLongest.map_weylAction hjl wi) wj
  have h1 : weylAction hA wi (Pi.single j 1) = Pi.single j 1 + 3 • Pi.single i 1 := by
    rw [hwi, weylAction_simple, reflection_apply_coroot, coroot_single, hAij]
    module
  have h2 : weylAction hA wj (Pi.single j 1 + 3 • Pi.single i 1) =
      2 • Pi.single j 1 + 3 • Pi.single i 1 := by
    rw [hwj, weylAction_simple, reflection_apply_coroot, map_add, map_nsmul, coroot_single,
      coroot_single, hAji, hA.apply_self]
    module
  rw [h1, h2] at hγ
  have hc0 : coroot (modelUniv .trialityD4 k 3 1 Fact.out).D.cartan i
      (2 • Pi.single j 1 + 3 • Pi.single i 1) = 0 := by
    rw [map_add, map_nsmul, map_nsmul, coroot_single, coroot_single, hAij, hA.apply_self]
    norm_num
  have hδ : (Pi.single i 1 : Fin (modelUniv .trialityD4 k 3 1 Fact.out).D.rank → ℤ) ∈
      (modelUniv .trialityD4 k 3 1 Fact.out).D.roots :=
    (isCTRootSystem hA (modelUniv .trialityD4 k 3 1 Fact.out).D.divisible).single_mem i
  have horth := form_toRat_single_eq_zero (modelUniv .trialityD4 k 3 1 Fact.out).D i _ hc0
  have hc := commutes_fund_of_orthogonal_of_longest (modelUniv .trialityD4 k 3 1 Fact.out).D
    hext hγ.1 hδ hγ.2 horth
  let R₀ : Subgroup (modelUniv .trialityD4 k 3 1 Fact.out).K :=
    (modelUniv .trialityD4 k 3 1 Fact.out).D.rootGroup
        (2 • Pi.single j 1 + 3 • Pi.single i 1) ⊔
      (modelUniv .trialityD4 k 3 1 Fact.out).D.rootGroup
        (-(2 • Pi.single j 1 + 3 • Pi.single i 1))
  have hR₀ : R₀ ∈ ModelFund 3 .trialityD4 k 1 := ⟨1, _, Or.inl hγ, (conjSub_one _).symm⟩
  have hcard : Nat.card R₀ = 24 := by
    obtain ⟨eR⟩ : Nonempty (↥R₀ ≃* SL(2, GaloisField 3 1)) :=
      (conjSub_one R₀) ▸ CFSG.ClassicalInvolution.ModelFacts.fundamentalSL2_of_isFundTag
        (p := 3) (e := 1) (by norm_num) hfund hadm
        (1 : (modelUniv .trialityD4 k 3 1 Fact.out).K) _ hγ
    rw [Nat.card_congr eR.toEquiv, card_sl2_galoisField_three]
  exact ⟨R₀, hR₀, _,
    ⟨1, Pi.single i 1, Or.inr (Or.inr (And.intro rfl hδ)), (conjSub_one _).symm⟩, hc, hcard⟩

private theorem exists_commuting_pair_of_lie_three {t : StatedLieTag} {n : ℕ}
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (hA1 : ¬ (t = .PSL ∧ n = 2))
    (h3 : ¬ ((t = .PSL ∧ n = 3) ∨ (t = .PSU ∧ n = 3))) :
    ∃ R ∈ ModelFund 3 t n 1, ∃ S ∈ ModelFund 3 t n 1,
      Commutes R S ∧ Nat.card R = 24 := by
  by_cases hG2 : t = .G2
  · subst hG2
    obtain ⟨R, hR, S, hS, hRS⟩ := exists_commuting_fund_g2 (p := 3) (e := 1) (k := n) hadm
    exact ⟨R, hR, S, hS, hRS, card_fund_g2 hadm hR⟩
  by_cases hD4 : t = .trialityD4
  · subst hD4
    exact exists_commuting_fund_trialityD4_long trivial hadm
      (i := (1 : Fin 2)) (j := (0 : Fin 2))
      (by show CFSG.Blueprint.Chevalley.Tag.cartan .G2 (1 : Fin 2) (0 : Fin 2) = -3; decide)
      (by show CFSG.Blueprint.Chevalley.Tag.cartan .G2 (0 : Fin 2) (1 : Fin 2) = -1; decide)
      rfl
  · obtain ⟨γ, hγ⟩ := exists_isLongestRoot _
      (CFSG.LieType.HighestRoot.rank_pos_modelUniv t n 3 1 Nat.prime_three hfund hadm)
    have hR0 : (modelUniv t n 3 1 Fact.out).D.rootGroup γ ⊔
        (modelUniv t n 3 1 Fact.out).D.rootGroup (-γ) ∈ ModelFund 3 t n 1 :=
      ⟨1, γ, Or.inl hγ, (conjSub_one _).symm⟩
    obtain ⟨R, hR, S, hS, hRS⟩ :=
      CFSG.ClassicalInvolution.Uniform.exists_commuting_fund (p := 3) (e := 1) (k := n)
        (by norm_num) hfund hadm hG2 hD4 hA1 h3 hR0
    exact ⟨R, hR, S, hS, hRS, card_fund_other hfund hadm hG2 hD4 hR⟩

theorem permWitness_of_lie_three (hFC : K_FunCommuteThree) {X : Type} [Group X] [Finite X]
    (hqs : CFSG.Open.IsQuasisimple X) (hZ : Subgroup.center X = ⊥)
    {t : StatedLieTag} {n : ℕ} (hadm : StatedLieAdmissible t n 3 1)
    (hX : LieModel (X ⧸ Subgroup.center X) t n 3 1)
    (hL3 : ¬ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.IsL3EpsOdd17
      (X ⧸ Subgroup.center X) 3) : PermWitness X := by
  have hodd : Odd (Nat.card (Subgroup.center X)) := by
    rw [hZ, Subgroup.card_bot]
    exact odd_one
  have hL2 : ¬ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.IsL2Over17
      (X ⧸ Subgroup.center X) 3 := by
    rintro ⟨r, f, hr, hr2, hq, hf, hLM⟩
    exact (LieModel.admissible hLM).2.2.2.2 (by rw [← hq])
  have hRee : ¬ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.IsReeOver17 X 3 := by
    rintro ⟨k, hq, hLM⟩
    have h3 : 3 ≤ 2 * k + 1 := (LieModel.admissible hLM).2.2.2.2.2
    have hk : 2 * k + 1 = 1 := by
      have h : 3 ^ (2 * k + 1) = 3 ^ 1 := by rw [← hq, pow_one]
      exact Nat.pow_right_injective (by norm_num : 1 < 3) h
    omega
  have hfund : IsFundTag t := by
    cases t
    case twistedB2 => exact absurd hadm.2.2.2.1 (by norm_num)
    case twistedF4 => exact absurd hadm.2.2.2.1 (by norm_num)
    case Tits => exact absurd hadm.2.2.2.1 (by norm_num)
    case twistedG2 => exact absurd hadm.2.2.2.2.2 (by norm_num)
    all_goals trivial
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    exact hadm.2.2.2.2 rfl
  have h3 : ¬ ((t = .PSL ∧ n = 3) ∨ (t = .PSU ∧ n = 3)) := by
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hL3 (Or.inl hX)
    · exact hL3 (Or.inr hX)
  intro U
  refine GF3.permWitnessAt_of_commuting_pieces U (FunSet (fundPred 3) X (U : Subgroup X))
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro φ hφ K hK
    have hmap := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.funSet_map_mulEquiv (q := 3) φ hK
    rwa [hφ] at hmap
  · intro K₁ h₁ K₂ h₂ hne x hx y hy
    have hc := hFC X 3 3 Nat.prime_three (by norm_num) ⟨t, n, 1, hadm, rfl, hX⟩ hqs hodd
      hL2 hL3 hRee rfl U K₁ h₁ K₂ h₂ hne
    have hx' : x ∈ Subgroup.centralizer (K₂ : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc) hx
    exact (Subgroup.mem_centralizer_iff.mp hx' y hy).symm
  · intro K hK x hx
    exact (member_piece_facts hK).1 x hx
  · intro K hK x hx y hy
    exact (member_piece_facts hK).2.1 x hx y hy
  · intro K hK c hc hcent
    exact (member_piece_facts hK).2.2.2.1 c hc hcent
  · have h3c : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
      rw [hZ, Subgroup.card_bot]
      norm_num
    obtain ⟨ψ, hψs, hψk⟩ := exists_cover_of_lieModel (r := 3) (f := 1) Nat.prime_three
      (by norm_num) hfund hadm hqs hX (Or.inr ⟨rfl, rfl, h3c⟩)
    obtain ⟨R, hR, S, hS, hRS, hcardR⟩ := exists_commuting_pair_of_lie_three hfund hadm hA1 h3
    have hRf : IsFundamentalOver 3 (R.map ψ) :=
      ⟨t, n, 3, 1, Nat.prime_three, by norm_num, rfl, hfund, hadm, ψ, hψs, hψk, R, hR, rfl⟩
    have hSf : IsFundamentalOver 3 (S.map ψ) :=
      ⟨t, n, 3, 1, Nat.prime_three, by norm_num, rfl, hfund, hadm, ψ, hψs, hψk, S, hS, rfl⟩
    have hR2 : ∀ c ∈ R, (∀ y ∈ R, c * y = y * c) → c * c = 1 :=
      (fund_facts (p := 3) (by norm_num) hfund hadm hR).2
    have hS2 : ∀ c ∈ S, (∀ y ∈ S, c * y = y * c) → c * c = 1 :=
      (fund_facts (p := 3) (by norm_num) hfund hadm hS).2
    obtain ⟨⟨a, ha, hao⟩, -⟩ := fund_facts (p := 3) (by norm_num) hfund hadm hR
    obtain ⟨⟨b, hb, hbo⟩, -⟩ := fund_facts (p := 3) (by norm_num) hfund hadm hS
    have hc : ⁅R.map ψ, S.map ψ⁆ = ⊥ := by
      rw [← Subgroup.map_commutator]
      have hbot : ⁅R, S⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hRS x hx y hy).symm
      rw [hbot, Subgroup.map_bot]
    obtain ⟨g, hg1, hg2⟩ := exists_conj_pair_mem_funSet (𝔉 := fundPred 3)
      (fun g _ hK => isFundamentalOver_map_mulEquiv (MulAut.conj g) hK) hRf hSf hc U
    obtain ⟨E, hE, hEc, hEle⟩ := exists_elemAbelian_sq_of_commutes ψ hψk hRS hR2 hS2
      Nat.prime_three (by norm_num) ha hb hao hbo
    have hinjR : Function.Injective (ψ.subgroupMap R) :=
      subgroupMap_injective_of_fundamental (by norm_num) hfund hadm hA1 hψk hR
    let eRK : ↥R ≃* ↥(R.map ψ) :=
      MulEquiv.ofBijective (ψ.subgroupMap R) ⟨hinjR, ψ.subgroupMap_surjective R⟩
    have hcardK₁ : Nat.card ((R.map ψ).map (MulAut.conj g).toMonoidHom) = 24 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        ← Nat.card_congr eRK.toEquiv, hcardR]
    refine ⟨(R.map ψ).map (MulAut.conj g).toMonoidHom, hg1,
      (S.map ψ).map (MulAut.conj g).toMonoidHom, hg2, ?_, ?_, ?_⟩
    · intro hEq
      have hEle' : E.map (MulAut.conj g).toMonoidHom ≤
          (R.map ψ).map (MulAut.conj g).toMonoidHom := by
        have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hEle
        rw [Subgroup.map_sup, ← hEq, sup_idem] at h
        exact h
      have h9 : 9 ∣ Nat.card ((R.map ψ).map (MulAut.conj g).toMonoidHom) := by
        have hdvd := Subgroup.card_dvd_of_le hEle'
        have hcardE' : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 9 := by
          rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]
          norm_num
        rwa [hcardE'] at hdvd
      rw [hcardK₁] at h9
      exact absurd h9 (by norm_num)
    · exact (member_piece_facts hg1).2.2.1
    · exact (member_piece_facts hg2).2.2.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
