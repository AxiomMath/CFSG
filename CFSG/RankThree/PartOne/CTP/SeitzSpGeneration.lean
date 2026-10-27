module

public import CFSG.RankThree.PartOne.CTP.SeitzSpMixing
public import CFSG.RankThree.PartOne.CTP.SeitzSpPlane

public section

namespace CFSG.RankThree.PartOne.CTP

open Polynomial CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {ℓ f p r : ℕ} {K : Type} [Field K] {Ahat : Subgroup (StatedSp r K)}

theorem exists_mixed_transCenter (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    {L N : Subgroup ↥Ahat} (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hVL : spLineSpace L ≠ ⊥) (hVN : spLineSpace N ≠ ⊥) :
    ∃ u ∈ spLineSpace L, ∃ w ∈ spLineSpace N, u ≠ 0 ∧ w ≠ 0 ∧
      TransCenter (centralizerSpan Ahat) (u + w) := by
  classical
  obtain ⟨x, hxA, hx1, h, hmem, hh1, hm2, ⟨v, hvL, hvh, hv0⟩, ⟨w, hwN, hwh, hw0⟩⟩ :=
    S.exists_mixing_factor D hL hN hLN hVL hVN
  have hpureN : ∀ c ∈ spLineSpace N, TransCenter (centralizerSpan Ahat) c := fun c hc =>
    transCenter_of_mem_summand S D (some ⟨N, hN⟩) hc
  by_cases hself : reciprocalPolynomial h = h
  · obtain ⟨g, hg, w₀, hw₀N, hw₀0, u', hu'L, w', hw'N, hu'0, hw'0, hgw⟩ :=
      exists_mixing_element_of_selfDual S D hL hN hLN hxA hx1 (h := ⟨h, hmem⟩) hh1 hself
        hvL hvh hv0 hwN hwh hw0
    refine ⟨u', hu'L, w', hw'N, hu'0, hw'0, ?_⟩
    rw [← hgw]
    exact (hpureN w₀ hw₀N).map (mem_centralizerSpan hxA hx1 hg)
  · have hne : h ≠ reciprocalPolynomial h := fun h' => hself h'.symm
    have hstabL : ∀ s ∈ spLineSpace L, spEnd x s ∈ spLineSpace L := fun s hs =>
      S.spLineSpace_stable ⟨x, hxA⟩ hs
    have hstabN : ∀ s ∈ spLineSpace N, spEnd x s ∈ spLineSpace N := fun s hs =>
      S.spLineSpace_stable ⟨x, hxA⟩ hs
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hmem⟩
    have hind := CFSG.RankThree.PartOne.KCUnitaryMixing.linearIndependent_pair_of_disjoint hstabL
      hstabN (D.disjoint_lineSpace hL hN hLN) hvL hwN hvh hwh hv0 hw0
    obtain ⟨g, hg, hgw⟩ := exists_mixing_element_of_paired S hxA hx1 (h := ⟨h, hmem⟩) hne hvh hwh
      hind
    refine ⟨v, hvL, w, hwN, hv0, hw0, ?_⟩
    rw [add_comm, ← hgw]
    exact (hpureN w hwN).map (mem_centralizerSpan hxA hx1 hg)

theorem transCenter_pair (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    (i j : Option {M : Subgroup ↥Ahat // Nat.card M = p}) (hij : i ≠ j)
    {y y' : Fin r ⊕ Fin r → K} (hy : y ∈ spInnerSummand p Ahat i)
    (hy' : y' ∈ spInnerSummand p Ahat j) (hy0 : y ≠ 0) (hy'0 : y' ≠ 0) :
    TransCenter (centralizerSpan Ahat) (y + y') := by
  rcases i with _ | ⟨L, hL⟩ <;> rcases j with _ | ⟨N, hN⟩
  · exact absurd rfl hij
  · exact transCenter_add_of_mem_summands S D hN hy hy'
  · rw [add_comm]
    exact transCenter_add_of_mem_summands S D hL hy' hy
  · have hLN : L ≠ N := fun h' => hij (by subst h'; rfl)
    have hVL : spLineSpace L ≠ ⊥ := fun h' => hy0 (by
      have : y ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy
      exact (Submodule.mem_bot K).mp this)
    have hVN : spLineSpace N ≠ ⊥ := fun h' => hy'0 (by
      have : y' ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy'
      exact (Submodule.mem_bot K).mp this)
    obtain ⟨u₀, hu₀, w₀, hw₀, hu₀0, hw₀0, hmix⟩ := exists_mixed_transCenter S D hL hN hLN hVL hVN
    have hne : (some ⟨L, hL⟩ : Option {M : Subgroup ↥Ahat // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
      fun h' => hLN (congrArg Subtype.val (Option.some.inj h'))
    have horth : ∀ a ∈ spLineSpace L, ∀ b ∈ spLineSpace N, spForm r K a b = 0 :=
      fun a ha b hb => D.orth _ _ hne a ha b hb
    have horth' : ∀ b ∈ spLineSpace N, ∀ a ∈ spLineSpace L, spForm r K b a = 0 :=
      fun b hb a ha => by rw [← spForm_isAlt.neg_eq, horth a ha b hb, neg_zero]
    obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ := exists_mem_fixing_eq (U := spLineSpace L)
      (D.nondeg (some ⟨L, hL⟩)) (fun c hc => transCenter_of_mem_summand S D (some ⟨L, hL⟩) hc)
      hu₀ hy hu₀0 hy0
    obtain ⟨g₂, hg₂, hg₂w, hg₂fix⟩ := exists_mem_fixing_eq (U := spLineSpace N)
      (D.nondeg (some ⟨N, hN⟩)) (fun c hc => transCenter_of_mem_summand S D (some ⟨N, hN⟩) hc)
      hw₀ hy' hw₀0 hy'0
    have h2 : spEnd g₂ u₀ = u₀ := hg₂fix u₀ (fun c hc => horth u₀ hu₀ c hc)
    have h1 : spEnd g₁ y' = y' := hg₁fix y' (fun c hc => horth' y' hy' c hc)
    have := hmix.map ((centralizerSpan Ahat).mul_mem hg₁ hg₂)
    rwa [spEnd_mul, Module.End.mul_apply, map_add, h2, hg₂w, map_add, hg₁u, h1] at this

theorem closure_centralizers_spPlane (S : SpPlaneSetup ℓ f p r K Ahat) :
    Subgroup.closure {g : StatedSp r K | ∃ x ∈ Ahat, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  classical
  have D := S.decomp
  refine eq_top_of_transCenter (transCenter_of_pairs (Vs := spInnerSummand p Ahat) ?_ ?_ D.nondeg
    (fun i c hc => transCenter_of_mem_summand S D i hc)
    (fun i j hij y hy y' hy' hy0 hy'0 => transCenter_pair S D i j hij hy hy' hy0 hy'0))
  · exact D.internal.submodule_iSup_eq_top
  · exact D.orth

end CFSG.RankThree.PartOne.CTP
