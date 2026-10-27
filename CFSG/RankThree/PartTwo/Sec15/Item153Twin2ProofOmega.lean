module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofCQ
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec14.Item1417

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof153Twin2

theorem omegaA_eq_or_facts_of_data156
    (h134 : Item134) (h48 : Sec4.Item4_8) {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G}
    (h₀ : Sec14Std G A c₀ L₀) {LB : Subgroup G → Subgroup G} {Y X₁ : Subgroup G} {d : G}
    (D : Data156 A LB Y c₀ L₀ d X₁) :
    omegaA A = {Subgroup.zpowers c₀} ∨
      (Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
        Subgroup.zpowers d ∉ omegaA A ∧
        ∀ b ∈ Subgroup.zpowers d, Subgroup.zpowers (c₀ * b) ∈ omegaA A) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA := h₀.isE27
  obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp D.omega
  have hc1 : c₀ ≠ 1 := by
    intro hc1
    rw [hc1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    exact absurd hc3 (by norm_num)
  have hdc : d ∉ Subgroup.zpowers c₀ := not_mem_zpowers_of_data156 h₀ D
  obtain ⟨hdL, S3, hdS, hSd⟩ := D.central_d
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L₀) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 D.hj hdL D.ne_d S3 hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h₀.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h₀.isSimpleGroup h₀.nonabelian D.ne_d)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs D.hj hdL D.ne_d
    ⟨S3, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA D.mem_d hc1 D.mem_lA.1 hJq
  rcases h134 G A c₀ L₀ h₀.toSec13Data D.hj d D.mem_d D.ne_d ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, hWd, hab, h9, -, hΩ⟩ | ⟨-, hWd, hΩ, h12⟩
  · exact Or.inl h1
  · refine Or.inr ⟨hWd, Proof152ResW.omegaA_facts_of_case2 hA hcA hc1 D.mem_d D.ne_d hdc hWd
      hab h9 ?_⟩
    rcases hΩ with h3 | ⟨I, -, -, -, a, haAK, had, hΩe, h6, -⟩
    · exact Or.inl h3
    · exact Or.inr ⟨a, haAK.1, had, hΩe, h6⟩
  · exact Or.inr ⟨hWd, Proof152ResW.omegaA_facts_of_case3 hA hcA hc1 D.mem_d D.ne_d hdc hWd hΩ
      h12⟩

end Proof153Twin2

open Proof153Twin2

theorem step156CQOmega_of
    (h134 : Item134)
    (h48 : Sec4.Item4_8) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {LB : Subgroup G → Subgroup G} : Step156CQOmega A LB := by
  intro Y _ _ c₀ L₀ d X₁ D hΩ F hF hF3 hFd
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  obtain ⟨-, -, hpts⟩ := (omegaA_eq_or_facts_of_data156 h134 h48 h₀ D).resolve_left hΩ
  have hA := h₀.isE27
  obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp D.omega
  have hc1 : c₀ ≠ 1 := by
    intro hc1
    rw [hc1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    exact absurd hc3 (by norm_num)
  have hdc : d ∉ Subgroup.zpowers c₀ := not_mem_zpowers_of_data156 h₀ D
  have hcd := Proof152ResW.not_mem_zpowers_symm hA hc1 D.mem_d hdc
  have hcl : Subgroup.closure ({c₀, d} : Set G) = Subgroup.zpowers c₀ ⊔ Subgroup.zpowers d := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  obtain ⟨b, hb, rfl⟩ :=
    Proof152ResW.exists_eq_zpowers_mul hA hcA D.mem_d D.ne_d hcd (hcl ▸ hF) hF3 hFd
  exact hpts b hb

theorem step156CQOmegaR_of
    (h134 : Item134)
    (h48 : Sec4.Item4_8) : Step156CQOmegaR :=
  fun _ _ _ _ _ _ hR => step156CQOmega_of h134 h48 hR.toSec14Std

end CFSG.RankThree.PartTwo.Sec15
