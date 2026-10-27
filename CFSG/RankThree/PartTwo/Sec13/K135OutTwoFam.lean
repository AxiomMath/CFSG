module

public import CFSG.RankThree.PartTwo.Sec13.K135OutTwoAbs
public import CFSG.RankThree.PartTwo.Sec13.K135OutTwoHom
public import CFSG.RankThree.PartTwo.Sec13.K135OutTwoLin
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LieType.Automorphisms.SteinbergBLCompleteIndexTwo
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.OutStructure
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outTwoGen_of_card_le_four {X : Type} [Group X] [Finite X]
    (h : Nat.card (Outer X) ≤ 4) : OutTwoGen X := by
  intro V _
  obtain ⟨α, hα, β, hβ, hle⟩ := ot_two_gen_of_card_le_four
    (V.map (QuotientGroup.mk' (inner X))) ((Subgroup.card_le_card_group _).trans h)
  exact ot_lift_two_gen V α β hα hβ hle

theorem outTwoGen_projectiveSL_odd {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (hdiag : ¬ 2 ∣ Nat.gcd n (Nat.card K - 1)) : OutTwoGen (projectiveSL n K) := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, hDn, hEn, -, hbE, hcE, -, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL n
  haveI hDnorm : (linearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  haveI hEnorm : (semilinearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hEn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  refine outTwoGen_of_tower (linearAutGroup n K) (semilinearAutGroup n K)
    (fun δ hδ k hk => linear_D2 Nat.prime_two hn hdiag δ hδ k hk) hbE ?_
  obtain ⟨g, -, hgx⟩ := hcE
  exact ⟨g, fun x => hgx x (hgenTop ▸ Subgroup.mem_top x)⟩

theorem outTwoGen_projectiveSL_prime {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (hK : Subsingleton (K ≃+* K)) : OutTwoGen (projectiveSL n K) := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, hDn, -, -, -, hcE, -, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL n
  haveI hDnorm : (linearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  haveI : ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  refine outTwoGen_of_tower (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
    (linearAutGroup n K) (fun δ hδ _ _ => hδ) (ot_linear_D_cyclic_mod_inner (by omega)) ?_
  obtain ⟨g, -, hgx⟩ := hcE
  refine ⟨g, fun x => ?_⟩
  obtain ⟨k, hk⟩ := hgx x (hgenTop ▸ Subgroup.mem_top x)
  exact ⟨k, ot_semilinear_le_linear hK hk⟩

theorem tg_psl {X : Type} [Group X] [Finite X] {n ℓ f : ℕ} (hn : 3 ≤ n)
    (h : StatedClassicalModel X .PSL n ℓ f) (hc : ¬ 2 ∣ Nat.gcd n (ℓ ^ f - 1) ∨ f = 1) :
    OutTwoGen X := by
  obtain ⟨⟨hℓ, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : X ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  refine outTwoGen_of_mulEquiv e' ?_
  rcases hc with hc | rfl
  · exact outTwoGen_projectiveSL_odd hn (by rwa [hK])
  · have hring := card_ringAut_and_isCyclic hℓ K (by rwa [pow_one] at hK ⊢)
    have h1 : Nat.card (K ≃+* K) = 1 := hring.1
    haveI : Subsingleton (K ≃+* K) := by
      haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [h1]; omega)
      exact (Nat.card_eq_one_iff_unique.mp h1).1
    exact outTwoGen_projectiveSL_prime hn inferInstance

theorem outTwoGen_primeFormP {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {n : ℕ}
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    [Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))] :
    OutTwoGen (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨-, hDcyc, -, -, -, -⟩ := unitary_full_diagonal_outer_order h hn hq
  have hring := card_ringAut_and_isCyclic h.prime K h.card
  haveI : IsCyclic (RingAut K) := hring.2
  refine outTwoGen_of_hom_cyclic (primeFormFieldFactor h hC hn hq) ?_
  rw [hFker]
  exact ot_cyclic_mod_of_isCyclic_quotient _ _ hDcyc

theorem tg_psu {X : Type} [Group X] [Finite X] {n r m : ℕ}
    (h : StatedClassicalModel X .PSU n r m) : OutTwoGen X := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData r m K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ r ^ m = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn3 hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  haveI : Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv X e'.toEquiv
  exact outTwoGen_of_mulEquiv e' (outTwoGen_primeFormP hU hn3 hq)

theorem tg_psp_two_odd {T : Type} [Group T] [Finite T] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hcl : StatedClassicalModel T .PSp 2 ℓ 1) : OutTwoGen T := by
  obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := hcl
  letI : Field K := hF
  haveI : Finite K := hFin
  have hdvd := (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.outer_card_dvd (K := K)
    (r := 2) hℓ le_rfl hK le_rfl).1
  have hcard : Nat.card (Outer T) =
      Nat.card (Outer (StatedProj (StatedSp 2 K))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
  refine outTwoGen_of_card_dvd (m := 1) (by decide) ?_
  rw [hcard]
  refine hdvd.trans ?_
  have hg : Nat.gcd 2 (ℓ ^ 1 - 1) ∣ 2 := Nat.gcd_dvd_left _ _
  calc 2 * 1 * Nat.gcd 2 (ℓ ^ 1 - 1) ∣ 2 * 1 * 2 := Nat.mul_dvd_mul_left _ hg
    _ = 4 * 1 := by norm_num

section PSL2

open CFSG.GorensteinWalter

theorem outTwoGen_PSL2_field (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hKcard : Nat.card K = ℓ ^ f) (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    OutTwoGen (PSL2 K) := by
  classical
  have hinj := pGammaL2ToMulAutPSL2_injective K hK hcard
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard
  let Ψe : PGammaL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 K hK hcard) ⟨hinj, hsurj⟩
  have : Finite (PGammaL2 K) := Finite.of_equiv (MulAut (PSL2 K)) Ψe.symm.toEquiv
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (PSL2 K) := inferInstance
  let N : Subgroup (PGammaL2 K) := (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range
  haveI hcyc : IsCyclic (PGammaL2 K ⧸ N) := pGammaL2_quotient_pgl_isCyclic K hK
  let Θ : MulAut (PSL2 K) →* PGammaL2 K ⧸ N :=
    (QuotientGroup.mk' N).comp Ψe.symm.toMonoidHom
  have hΨinl : ∀ g : PGL2 K, Ψe (SemidirectProduct.inl g) = pgl2InnerAutPSL2 K hK hcard g :=
    fun g => pGammaL2ToMulAutPSL2_inl K hK hcard g
  have hker : ∀ δ ∈ Θ.ker, ∃ g : PGL2 K, δ = pgl2InnerAutPSL2 K hK hcard g := by
    intro δ hδ
    have h1 : Ψe.symm δ ∈ N := (QuotientGroup.eq_one_iff _).mp hδ
    obtain ⟨g, hg⟩ := h1
    refine ⟨g, ?_⟩
    rw [← hΨinl, hg, MulEquiv.apply_symm_apply]
  have hHidx : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index = 2 :=
    pgl2_psl2Range_index_eq_two K hK
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : PGL2 K,
      g₀ ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    by_contra hall
    push Not at hall
    have htop : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range = ⊤ :=
      eq_top_iff.2 fun x _ => hall x
    rw [htop, Subgroup.index_top] at hHidx
    omega
  refine outTwoGen_of_hom_cyclic Θ ⟨pgl2InnerAutPSL2 K hK hcard g₀, ?_, ?_⟩
  · rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' N) (Ψe.symm (pgl2InnerAutPSL2 K hK hcard g₀)) = 1
    rw [← hΨinl, MulEquiv.symm_apply_apply]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
  · intro x hx
    obtain ⟨g, rfl⟩ := hker x hx
    by_cases hg : g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
    · refine ⟨0, ?_⟩
      obtain ⟨y, rfl⟩ := hg
      rw [zpow_zero, one_mul, pgl2InnerAutPSL2_toPGL]
      exact ⟨y, rfl⟩
    · refine ⟨1, ?_⟩
      have hmem : g₀ * g ∈
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
        (Subgroup.mul_mem_iff_of_index_two hHidx).mpr (iff_of_false hg₀ hg)
      obtain ⟨y, hy⟩ := hmem
      rw [zpow_one, ← map_mul, ← hy, pgl2InnerAutPSL2_toPGL]
      exact ⟨y, rfl⟩

theorem tg_psl_two_odd {X : Type} [Group X] {ℓ f : ℕ} (hℓ2 : ℓ ≠ 2)
    (h : StatedClassicalModel X .PSL 2 ℓ f) : OutTwoGen X := by
  obtain ⟨⟨hℓ, hf, -, hne2, hne3⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hK' : IsOddPrimePower (Nat.card K) := ⟨ℓ, f, hℓ, hodd, hf, hK⟩
  have hcard : 3 < Nat.card K := by
    rw [hK]
    have h1 : 3 ≤ ℓ ^ f := by
      calc 3 ≤ ℓ := by
            have := hℓ.two_le
            omega
        _ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
    have h2 : ℓ ^ f ≠ 3 := fun h3 => hne3 (by rw [h3])
    have h4 : ℓ ^ f ≠ 4 := fun h4 => by
      have := (hodd.pow (n := f))
      rw [h4] at this
      exact absurd this (by decide)
    omega
  have e' : X ≃* PSL2 K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  exact outTwoGen_of_mulEquiv e' (outTwoGen_PSL2_field K hK hK' hcard)

end PSL2

end CFSG.RankThree.PartTwo.Sec13.F135Last
