module

public import CFSG.RankThree.PartTwo.Sec13.F135LastDefs
public import CFSG.RankThree.PartTwo.Sec13.F135LastLemmaF
public import CFSG.RankThree.PartTwo.Sec13.F135LastLemma5
public import CFSG.RankThree.PartTwo.Sec13.F135LastLift
public import CFSG.RankThree.PartTwo.Sec13.F135LastSylow
public import CFSG.RankThree.PartTwo.Sec13.F135LastCover
public import CFSG.RankThree.PartTwo.Sec13.F135LastKernel
public import CFSG.RankThree.PartTwo.Sec13.F135LastThree
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnUT3
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.LiftSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

theorem last_step {M : Type*} [Group M] [Finite M]
    (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (c : M) (hc : orderOf c = 3)
    (E P₀ : Subgroup M) (hE : IsPGroup p E) (hP₀ : IsPGroup p P₀) (hEP₀ : E ≤ P₀)
    (hP₀C : P₀ ≤ centralizer ({c} : Set M))
    (hP₀N : ∀ g ∈ centralizer ({c} : Set M), g ∈ normalizer (P₀ : Set M))
    (R : Subgroup M) [R.Normal] (hR : Nat.Coprime (Nat.card R) (2 * p))
    (J : Subgroup (M ⧸ R)) (hJ : CFSG.IsQuasisimple J)
    (hJE : ∀ e ∈ E, (e : M ⧸ R) ∈ normalizer (J : Set (M ⧸ R)))
    (hJc : (c : M ⧸ R) ∈ normalizer (J : Set (M ⧸ R)))
    (hJnt : ∃ e ∈ E, ∃ j ∈ J, ⁅(e : M ⧸ R), j⁆ ≠ 1)
    (hrank3 : ∀ t : M, t ≠ 1 → t * t = 1 → ∀ X : Subgroup M, IsPGroup 3 X →
      X ≤ centralizer ({t} : Set M) → CFSG.pRank 3 X ≤ 3)
    (hZ : Nat.Coprime (Nat.card (center J)) (2 * p))
    (hK3 : ∀ g ∈ normalizer (J : Set (M ⧸ R)), g ^ 3 = 1 →
      (∀ e ∈ E, g * (e : M ⧸ R) = (e : M ⧸ R) * g) → ∀ j ∈ J, ∀ k ∈ J, ⁅⁅j, g⁆, k⁆ = 1)
    (hS : HasTwoSix (J ⧸ center J) ∨
      ∃ (A : Subgroup (J ⧸ center J)) (x : J ⧸ center J), FourCubeSeven A x ∧ p = 7) :
    False := by
  classical
  have hpp : p.Prime := Fact.out
  have hp3 : p ≠ 3 := by omega
  set π : M →* M ⧸ R := QuotientGroup.mk' R with hπ
  have hJperf : ⁅J, J⁆ = J := comm_eq_self_of_isPerfect J hJ.1
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hcE : ∀ e ∈ E, e * c = c * e := fun e he => by
    have h := hP₀C (hEP₀ he)
    rw [Subgroup.mem_centralizer_iff] at h
    exact (h c rfl).symm
  have hcJ : ∀ j ∈ J, ⁅j, (c : M ⧸ R)⁆ = 1 := by
    refine commute_of_trivial_mod_center J hJperf (c : M ⧸ R) hJc ?_
    refine hK3 (c : M ⧸ R) hJc ?_ ?_
    · rw [← QuotientGroup.mk_pow, hc3, QuotientGroup.mk_one]
    · intro e he
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcE e he]
  set I : Subgroup M := J.comap π with hI
  have hmemI : ∀ x : M, x ∈ I ↔ π x ∈ J := fun x => Iff.rfl
  have hRI : R ≤ I := fun r hr => by
    rw [hmemI, show π r = 1 from (QuotientGroup.eq_one_iff r).2 hr]
    exact J.one_mem
  have hIc : ∀ x ∈ I, x * c * x⁻¹ * c⁻¹ ∈ R := by
    intro x hx
    have h1 := hcJ (π x) hx
    rw [commutatorElement_def] at h1
    have h1' : (x : M ⧸ R) * (c : M ⧸ R) * (x : M ⧸ R)⁻¹ * (c : M ⧸ R)⁻¹ = 1 := h1
    refine (QuotientGroup.eq_one_iff _).1 ?_
    simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h1'
  have hRp : ¬ p ∣ Nat.card R := by
    have h : Nat.Coprime p (Nat.card R) :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_left p 2) hR.symm
    exact (Nat.Prime.coprime_iff_not_dvd hpp).1 h
  obtain ⟨S, hSle, hS3, hSidx, hcS, hES⟩ := exists_sigma hpp hp3 c hc E hE R hcE hRp
  have hcover := frattini_cover R I S c hRI hIc hSle hS3 hSidx hcS
  set Nσ : Subgroup M := I ⊓ normalizer (S : Set M) with hNσ
  have hEI : ∀ e ∈ E, e ∈ normalizer (I : Set M) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmemI, hmemI, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hJE e he) (π h)
  have hEN : ∀ e ∈ E, e ∈ normalizer (Nσ : Set M) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hNσ, Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (hEI e he) h)
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hES he)) h)
  have hmapI : I.map π = J := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) J
  obtain ⟨K, hKN, hEK, hKcover, hKperf⟩ :=
    exists_minimal_cover R I Nσ E hRI inf_le_left hcover hEN (by rw [hmapI]; exact hJperf)
  have hKI : K ≤ I := hKN.trans inf_le_left
  have hKS : ∀ k ∈ K, k ∈ normalizer (S : Set M) := fun k hk => (hKN hk).2
  have hKJ : K.map π = J := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hKI hk
    · intro j hj
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R j
      obtain ⟨r, hr, k, hk, hgk⟩ := hKcover g hj
      refine ⟨k, hk, ?_⟩
      rw [hgk, map_mul, show π r = 1 from (QuotientGroup.eq_one_iff r).2 hr, one_mul]
  have hRn : ∀ k : M, k ∈ normalizer (R : Set M) := fun k => by
    rw [Subgroup.normalizer_eq_top_iff.2 ‹R.Normal›]; exact Subgroup.mem_top k
  have hKSR : ∀ k ∈ K, ∀ s ∈ S ⊓ R, k * s = s * k := by
    by_contra hnot
    push_neg at hnot
    obtain ⟨k₀, hk₀, s₀, hs₀, hne⟩ := hnot
    have hKnormSR : K ≤ normalizer ((S ⊓ R : Subgroup M) : Set M) := fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKS k hk, hRn k⟩
    have hφne : conjAction K (S ⊓ R) hKnormSR ≠ 1 := by
      intro h
      apply hne
      have h' := congrArg (fun f : ↥K →* MulAut ↥(S ⊓ R) =>
        ((f ⟨k₀, hk₀⟩ ⟨s₀, hs₀⟩ : ↥(S ⊓ R)) : M)) h
      simp only [conjAction_apply, MonoidHom.one_apply, MulAut.one_apply] at h'
      calc k₀ * s₀ = k₀ * s₀ * k₀⁻¹ * k₀ := by group
        _ = s₀ * k₀ := by rw [h']
    have hP3 : IsPGroup 3 ↥(S ⊓ R) := hS3.to_le inf_le_left
    have hrank := hrank_of_hrank3 K (S ⊓ R) hKnormSR hP3 hrank3
    have hKperf' := commutator_top_of_comm_eq_self K hKperf
    obtain ⟨πK, hπK, hcop⟩ := exists_surjection_coprime R K J hKJ (2 * p) hR hZ
    haveI : πK.ker.Normal := MonoidHom.normal_ker πK
    have hNodd : Odd (Nat.card πK.ker) :=
      Nat.coprime_two_right.1 (Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 p) hcop)
    have hSsimple : IsSimpleGroup (↥K ⧸ πK.ker) := by
      haveI : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.2.1
      exact (QuotientGroup.quotientKerEquivOfSurjective πK hπK).isSimpleGroup
    have hstruct : (∃ T : Subgroup ↥K, (∀ t ∈ T, t * t = 1) ∧ Nat.card T = 2 ^ 6) ∨
        ∃ (A : Subgroup ↥K) (x : ↥K), FourCubeSeven A x := by
      rcases hS with h2 | ⟨A, x, hAx, hp7'⟩
      · exact Or.inl (hasTwoSix_lift πK hπK hNodd h2)
      · refine Or.inr (fourCubeSeven_lift πK hπK ?_ hAx)
        rw [hp7'] at hcop
        simpa using hcop
    exact lemma5_abstract hP3 (conjAction K (S ⊓ R) hKnormSR) hφne hrank hKperf' πK.ker hNodd
      hSsimple hstruct
  have hKc : ∀ k ∈ K, k * c = c * k :=
    K_centralizes_of_centralizes_sylow R K S c hKperf hKS hcS (fun k hk => hIc k (hKI hk)) hKSR
  have hq : CFSG.IsQuasisimple ↥(K.map π) := by rw [hKJ]; exact hJ
  have hF := lemmaF hpp R K E P₀ hKperf hEK hP₀ hEP₀
    (fun k hk => hP₀N k (Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]; exact (hKc k hk).symm)) hq
  obtain ⟨e, he, j, hj, hne⟩ := hJnt
  rw [← hKJ] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  exact hne (hF e he k hk)

end CFSG.RankThree.PartTwo.Sec13.F135Last
