module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
public import CFSG.LocalAnalysis.StandardType.GGQTwoReduction
public import CFSG.LocalAnalysis.StandardType.GGQTwoCor81
public import CFSG.LocalAnalysis.StandardType.GGQTwoTrivial
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1Model
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssembleNondeg
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssembleDeg
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssembleCaseII
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteQTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2_pThree {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) :
    p = 3 := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  by_contra hne
  refine FrameRoute.ggFrameQTwo_qTwoLabel
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hS.2.1) ?_
  exact largeEvenMarking_mono
    (fun _ _ _ _ _ _ h hc => hne (FrameRoute.ggFrameQTwo_eq_three_of_split hp h.1 hc))
    hS.1.1.1.2.2.2.2.2.2.2.1

@[expose] def GGQ2GammaXInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers x → GGGammaAt p B Bs x L D J u

@[expose] def GGQ2GammaNbrInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L →
    ∀ {u : ↥Bs}, GGNbrLine p B x D J u → GGGammaAt p B Bs x L D J u

@[expose] def GGQ2GammaXInLInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∈ L →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers x → GGGammaAt p B Bs x L D J u

@[expose] def GGQ2GammaNbrInLInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∈ L →
    ∀ {u : ↥Bs}, GGNbrLine p B x D J u → GGGammaAt p B Bs x L D J u

@[expose] def GGQ2TwoNodeInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K)) →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2DependentOtherInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K → ∀ (M : GGQTwoModel p Bs x y D L J K),
        ¬ GGQTwoBasis M → ¬ M.toLin.CaseII →
        Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) →
        (∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGGammaAt p B Bs x L D J u) →
          Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2I1FailInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
      Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2NoModelInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        ¬ Nonempty (GGQTwoModel p Bs x y D L J K)) →
      ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ¬ GGQTwoTwoNodeRowAt p L J → ¬ GGQTwoTwoNodeRowAt p K J →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) →
      (∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGGammaAt p B Bs x L D J u) →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem ggQ2_reflGenerated_of_model {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) :
    GGReflGenerated p (ggAutomizer K Bs) := by
  have hα : ∀ i, M.root i (M.coroot i) = 2 := fun i => by
    rw [M.pairing, M.isCartan.1 i]
    norm_num
  have hrefl : ∀ i, M.simple i = 1 ∨ GGIsReflection p (M.simple i) := by
    intro i
    by_cases h1 : M.simple i = 1
    · exact Or.inl h1
    right
    have hlin : ggLin (p := p) M.model (M.simple i) = Module.reflection (hα i) :=
      LinearEquiv.ext fun w => by rw [M.simple_apply, Module.reflection_apply]
    have hα0 : M.root i ≠ 0 := by
      intro h0
      apply h1
      apply ggLin_injective (p := p) M.model
      rw [map_one]
      refine LinearEquiv.ext fun w => ?_
      rw [M.simple_apply, h0]
      simp
    have hh0 : M.coroot i ≠ 0 := by
      intro h0
      apply h1
      apply ggLin_injective (p := p) M.model
      rw [map_one]
      refine LinearEquiv.ext fun w => ?_
      rw [M.simple_apply, h0]
      simp
    refine ⟨?_, ?_⟩
    · apply ggLin_injective (p := p) M.model
      rw [map_pow, hlin, map_one]
      refine LinearEquiv.ext fun w => ?_
      rw [pow_two]
      exact Module.involutive_reflection (hα i) w
    · rw [card_fixed_ggLin (p := p) M.model, card_eq_of_ggLin M.model]
      have hsurj : Function.Surjective (M.root i) := by
        obtain ⟨v, hv⟩ := not_forall.mp (fun h : ∀ v, M.root i v = 0 => hα0 (LinearMap.ext h))
        intro c
        refine ⟨(c * (M.root i v)⁻¹) • v, ?_⟩
        rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hv, mul_one]
      have hcard := AddSubgroup.card_ker_mul_card_of_surjective
        (f := (M.root i).toAddMonoidHom) hsurj
      have hker : Nat.card {v : M.V // ggLin (p := p) M.model (M.simple i) v = v} =
          Nat.card (AddMonoidHom.ker (M.root i).toAddMonoidHom) := by
        refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
        rw [AddMonoidHom.mem_ker, M.simple_apply]
        constructor
        · intro h
          have h' : M.root i v • M.coroot i = 0 := by
            have := sub_eq_self.mp h
            exact this
          rcases smul_eq_zero.mp h' with h'' | h''
          · exact h''
          · exact absurd h'' hh0
        · intro h
          show v - M.root i v • M.coroot i = v
          rw [show M.root i v = 0 from h, zero_smul, sub_zero]
      rw [hker, Nat.card_zmod] at *
      exact hcard
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun φ hφ => hφ.1)
  calc ggAutomizer K Bs = Subgroup.closure (M.simple '' {k | k ≠ M.b}) := M.automizer_K
    _ ≤ Subgroup.closure {φ | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ} := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      rcases hrefl i with h | h
      · rw [h]
        exact one_mem _
      · exact Subgroup.subset_closure
          ⟨by rw [M.automizer_K]; exact Subgroup.subset_closure ⟨i, hi, rfl⟩, h⟩

theorem ggQ2_gamma_all {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (h2 : GGQTwoLemma895Prime) (hgx : GGQ2GammaXInput)
    (hgn : GGQ2GammaNbrInput) (hgxL : GGQ2GammaXInLInput) (hgnL : GGQ2GammaNbrInLInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) (hK1 : GGQTwoK1 p B Bs x D J) (hI1 : GGQTwoI1 Bs D J) :
    ∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGGammaAt p B Bs x L D J u := by
  intro u hu hu1
  by_cases hx : Subgroup.zpowers (u : G) = Subgroup.zpowers x
  · by_cases hxL : x ∈ L
    · exact hgxL hS hp hI1 hxL hx
    · exact hgx hS hp hI1 hxL hx
  by_cases hn : GGNbrLine p B x D J u
  · by_cases hxL : x ∈ L
    · exact hgnL hS hp hI1 hxL hn
    · exact hgn hS hp hI1 hxL hn
  have htr : GGTrivialLine p B x D J u := ⟨hx, hn⟩
  by_cases h4 : 4 ∣ Nat.card (ggAutomizer J Bs)
  · exact ggQ2_gammaTrivial hLB hP hS hp hK1 hI1 hu hu1 htr h4
  · exact h2 G p B Bs x L D J hS u hu hu1 htr h4

theorem ggCorFiveTwentyInputQTwoOffE6Dep_of_layers
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h1 : GGQTwoModelInput) (h1b : GGQTwoNoTwoNodeIndInput) (h2 : GGQTwoLemma895Prime)
    (h3 : GGQTwoNoWeylA3) (h5 : GGQTwoCentralizerInput) (hgx : GGQ2GammaXInput)
    (hgn : GGQ2GammaNbrInput) (hgxL : GGQ2GammaXInLInput) (hgnL : GGQ2GammaNbrInLInput)
    (hnode : GGQ2TwoNodeInput) (hdep : GGQ2DependentOtherInput) (hi1 : GGQ2I1FailInput)
    (hnm : GGQ2NoModelInput) :
    GGCorFiveTwentyInputQTwoOffE6Dep := by
  intro G _ _ p B Bs x L D J hH hLQ hnoE
  have hS : GGQTwoSetting p B Bs x L D J := ⟨hH, hLQ, hnoE⟩
  have hp : p = 3 := ggQ2_pThree hS
  haveI : Fact p.Prime := ⟨hH.1.tableB_facts.1⟩
  have hC : Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
    obtain ⟨hI, hBs, hDJsub⟩ := hH.1
    have hSst : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
    have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
      have h := ggLNoncyclicInput_holds
      unfold GGLNoncyclicInput at h
      exact h G p B x L hI
    exact (Subgroup.centralizer_le hBs.1).trans
      (centralizer_le_normalizer_ggG0 hSst hnc hDJsub.1)
  by_cases hI : GGQTwoI1 Bs D J
  swap
  · exact hi1 hS hp hI
  by_cases hrow : ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K))
  · obtain ⟨y, K, hnb, h⟩ := hrow
    exact hnode hp hS hI hnb h
  have hnr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) := by
    intro y K hnb h
    obtain ⟨hL, hK⟩ := h1b G p B Bs x L D J hS hI y K hnb
    rcases h with h | h
    · exact hrow ⟨y, K, hnb, Or.inl ⟨h, hL h⟩⟩
    · exact hrow ⟨y, K, hnb, Or.inr ⟨h, hK h⟩⟩
  have hcases : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Nonempty (GGQTwoModel p Bs x y D L J K) ∨
        (GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∧
          GGReflGenerated p (ggAutomizer K Bs)) := by
    intro y K hnb
    rcases h1 G p B Bs x L D J hS hI y K hnb with h | h | hM | hW
    · exact absurd (Or.inl h) (hnr y K hnb)
    · exact absurd (Or.inr h) (hnr y K hnb)
    · exact Or.inl hM
    · exact Or.inr hW
  have hRG : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) := by
    intro y K hnb
    rcases hcases y K hnb with hM | ⟨-, hrg⟩
    · obtain ⟨M⟩ := hM
      exact ggQ2_reflGenerated_of_model M
    · exact hrg
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 p B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI
  have hΓ := ggQ2_gamma_all hLB hP h2 hgx hgn hgxL hgnL hS hp hK1 hI
  obtain ⟨y, K, hnb⟩ := exists_ggNbr hH.1.1.2.2.2.2.2.2.2 hH.1.2.2
  by_cases hmodnb : ∃ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' ∧
      Nonempty (GGQTwoModel p Bs x y' D L J K')
  swap
  · have hnomod : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
        ¬ Nonempty (GGQTwoModel p Bs x y' D L J K') :=
      fun y' K' h hM => hmodnb ⟨y', K', h, hM⟩
    rcases hcases y K hnb with hM | ⟨hW, -⟩
    · exact absurd hM (hnomod y K hnb)
    · exact hnm hp hS hI hnomod hnb (fun h => hnr y K hnb (Or.inl h))
        (fun h => hnr y K hnb (Or.inr h)) hW hC hΓ
  obtain ⟨y', K', hnb', ⟨M⟩⟩ := hmodnb
  have key : GGQ2Orbit p B Bs x D J ∨
      Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
    by_cases hbas : GGQTwoBasis M
    · by_cases hdeg : (M.cartan.det : ZMod p) = 0
      · exact Or.inl (ggQ2_caseI_deg_of_lin hp hS hnb' M hbas hdeg)
      · exact Or.inl (ggQ2_caseI_nondeg_of_lin hp ggLNoncyclicInput_holds h3 hS hnb' M hbas hdeg)
    · by_cases hII : M.toLin.CaseII
      · exact Or.inl (ggQ2_caseII_orbit hp ggLNoncyclicInput_holds hS hnb' M hII)
      · exact Or.inr (hdep hp hS hnb' M hbas hII hC hΓ)
  rcases key with (hPo | hX) | hfin
  · exact ggQ2_reduction hS hC hΓ hPo
  · exact ggQ2_lemmaX hLB hP hS hAJS hK1 hΓ hX
  · exact hfin

end CFSG.StandardType

end
