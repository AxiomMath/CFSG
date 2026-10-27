module

public import CFSG.LocalAnalysis.StandardType.GGPairResidualE7Plus
import CFSG.LocalAnalysis.StandardType.ExcPay.TwE6
import CFSG.LocalAnalysis.StandardType.GGPairConjugation
import CFSG.LocalAnalysis.StandardType.GGRankOneShared
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem ggTwE6Plus_exists_model
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp5 : 5 ≤ p)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hE6 : GGInnerDiagOnLabel (fun p lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) p Bs X) :
    ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      GGExcPlusWeylModel .E6 p (ggGamma X hN).range := by
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hE6
  obtain ⟨hN, hM, -⟩ := ggX_exists_overGamma_lift ggLabelRigidInput_holds hcfg hX hInn hΛ hhas
    (fun _ _ A => GGExcPlusWeylModel .E6 p A) (largeEvenLabelAll_excPlusModel_ETwE6 hp hp5 hΛ hS)
  exact ⟨hN, hM⟩

theorem ggPairConcl_of_selected_TwE6_plus_of_ne_three
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp3 : p ≠ 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (_hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (_hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) (_hXns : ¬ GGSplitLie p X)
    (_hXnu : ¬ GGMemberUnitary p Bs X)
    (hE6 : GGInnerDiagOnLabel (fun p lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) p Bs X)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e)
    {r' : MulAut ↥Bs} (hr' : r' ∈ ggAutomizer X Bs) (hr'C : r' ∈ ggCoxRefl M e)
    (hne : r ≠ r') :
    GGPairConcl Bs X r r' := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  have hXn : X = L ∨ ∃ y, GGNbr p B x D J y X :=
    (hX.imp_right (GGSecFiveWeakNbr.of_mem hcfg)).imp_right fun hw => hw.1
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.1.1.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hcfg.1.1.2.1.2.2.2
  obtain ⟨hN, hM⟩ := ggTwE6Plus_exists_model hp5 hcfg hXn hE6
  have hrR : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  have hr'R : GGIsReflection p r' := ggCoxRefl_isReflection hpres.2 hr'C
  have hE6' : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨⟨hP.1,
      two_le_of_prime_dvd_two_pow_add_one hp hp2 hp3 hP.1.2⟩, hP.2⟩) hE6
  obtain ⟨-, -, -, -, -, hZ3, -⟩ := ExcPay.exists_twE6Cover_of_marking hp hp3 hBs hE6'
  have hZ : ∀ z ∈ Subgroup.center ↥X, (z : G) ∈ Bs → z = 1 := by
    intro z hz hzB
    have h3 : orderOf z ∣ 3 := by
      have h := (orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center ↥X))).trans hZ3
      rwa [Subgroup.orderOf_mk] at h
    have hzp : orderOf z ∣ p := by
      refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
      simpa using hBs.2 _ hzB
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)) h3 hzp)
  obtain ⟨f, -, -, s, hs, F, _, _, _, hF, -, hcomm2, hpair3⟩ :=
    ExcPay.exists_excPhanPayload_of_marking_TwE6 hp hp3 hBs hSC hE6'
  exact ggPairConcl_of_excPlusModel_base (Or.inl rfl) hp hp2 hBs hSC hN hM hZ
    (N := CoxeterMatrix.E₆) (i₀ := 0) (i₁ := 1) (i₂ := 2) (i₃ := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs hF hcomm2 hpair3 hr hrR hr' hr'R hne

end CFSG.StandardType

end
