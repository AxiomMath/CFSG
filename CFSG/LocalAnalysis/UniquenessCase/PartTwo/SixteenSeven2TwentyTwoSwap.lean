module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentySwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyIrrThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_twenty_two_swap (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)}
    (hA : Choice1613 D ⊥ V hV L A) (hAel : IsElemAbelian 2 A)
    (hΔ : Concl1617 D ⊥ V hV L A g Δ) (hS : Case168_2Small D ⊥ V hV L) :
    ∃ (I₀ I₁ : Subgroup G) (a : G), Swap20 A V I₀ I₁ a ∧
      (∀ x ∈ A, conjSubgroup I₀ x = I₀ ↔
        x ∈ preBarSub D.M ⊥ V hV (centralizer ((oddBar D.M ⊥ V hV :
          Subgroup (MulAut (Vtil ⊥ V hV))) : Set (MulAut (Vtil ⊥ V hV))))) ∧
      (∀ b ∈ A, conjSubgroup I₀ b = I₀ → ∀ I ∈ Δ, conjSubgroup I b = I) ∧
      (∀ B' : Subgroup G, B' ≤ A → (∀ b ∈ B', conjSubgroup I₀ b = I₀) → ∀ I ∈ Δ,
        Nat.card ↥(I ⊓ centralizer (B' : Set G)) = Nat.card ↥(I₀ ⊓ centralizer (B' : Set G))) := by
  obtain ⟨F, π, -, hrange, hact, hcomm, htrans⟩ := s16c167_irr_three D hC hS
  have hM : D.M ≤ normalizer (V : Set G) := hC.setting.hyp16.hyp125.normalizer_eq.ge
  have hAM : A ≤ D.M := hA.1.1.trans D.sylowM.le
  have hmem : ∀ i, F i ∈ irrSet (barSub ⊥ V hV L) := fun i => by
    have h : F i ∈ irrBar L ⊥ V hV := by rw [hrange]; exact Set.mem_range_self i
    exact h
  have hFne : ∀ i, F i ≠ ⊥ := by
    intro i hi
    have hlt := (hmem i).2.1
    simp [hi] at hlt
  have hΔF : ∀ J ∈ Δ, ∃ i, imgTil ⊥ V hV J = F i := by
    intro J hJ
    have h : imgTil ⊥ V hV J ∈ irrBar L ⊥ V hV := hΔ.2.2.2.2.1 hS.case168_2 J hJ
    rw [hrange] at h
    exact h.imp fun i hi => hi.symm
  obtain ⟨⟨j₁, j₂, hj, hinf, hsup⟩, hΔI⟩ :=
    s16c167_twenty_two_delta hV hΔ.1 hΔ.2.1 hΔ.2.2.1 hΔ.2.2.2.1 hΔF
  have hpair := s16c167_twenty_two_pairs hact
    (fun i j => (htrans i j).imp fun y hy => hy.2) hj hinf hsup
  obtain ⟨hIne, hIpair, hIconj⟩ := s16c167_twenty_two_family hV hM hact hFne hpair
  have hcne : ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV A⁆ ≠ ⊥ := by
    rcases hA.2 with h | ⟨h9, -⟩
    · exact h
    · exfalso
      have h7 : D.sig = {7} := h9.2.2.2.2
      have h3 : D.sig = {3} := hS.2.2
      have h73 : (7 : ℕ) ∈ ({3} : Set ℕ) := by rw [← h3, h7]; exact Set.mem_singleton 7
      simp at h73
  obtain ⟨I₀, I₁, a, i₀, hI₀, hSw, ha, hρb, hb⟩ := s16c167_twenty_two_core
    (I := fun i => preTil ⊥ V hV (F i)) (ρ := π.comp (s16c167_barHom hV hM))
    (P := preBarSub D.M ⊥ V hV (centralizer ((oddBar D.M ⊥ V hV :
      Subgroup (MulAut (Vtil ⊥ V hV))) : Set (MulAut (Vtil ⊥ V hV)))))
    (Δ := Δ) hAM hAel (fun i => preTil_le ⊥ V hV (F i)) hIne hIpair hIconj
    (fun m hm => s16c167_twenty_two_centralizer hV hM hcomm m hm)
    (s16c167_twenty_two_nontrivial hV hM hAM hAel hcomm hcne) hΔI
  refine ⟨I₀, I₁, a, hSw, ha, hb, ?_⟩
  intro B' hB'A hB' J hJ
  obtain ⟨i, rfl⟩ := hΔI J hJ
  subst hI₀
  exact s16c167_twenty_two_card_family (ρ := π.comp (s16c167_barHom hV hM))
    (fun i => preTil_le ⊥ V hV (F i)) hIconj
    (s16c167_twenty_two_transitive hV hM hcomm htrans) (hB'A.trans hAM)
    (fun b hb => hAel.2 b (hB'A hb)) (fun b hbB' => hρb b (hB'A hbB') (hB' _ hbB')) i₀ i

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
