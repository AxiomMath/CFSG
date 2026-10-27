module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourInputs
public import CFSG.ClassicalInvolution.RouteD.TypeERecog
import CFSG.ClassicalInvolution.WeakCT.DLDiagrams
import CFSG.ClassicalInvolution.WeakCT.Standard
import CFSG.ClassicalInvolution.Balance.QNineStandard
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.RouteD.LocalTwin
import CFSG.ClassicalInvolution.LBalance.Main
import CFSG.ClassicalInvolution.ModelFacts.OddCover
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.ClassicalInvolution.Models.Transfer
import CFSG.ClassicalInvolution.Models.UnitaryFrames
import CFSG.ClassicalInvolution.Models.UnitaryPairs
import CFSG.ClassicalInvolution.WeakCT.DoublyLaced

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

theorem ggStdChain_map_of_ker_le_center {F : Type} [Field F] {n : ℕ} {G : Type} [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* G) (hψ : ψ.ker ≤ Subgroup.center _) :
    (∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W : Subgroup G, LinearBlockStandardPair F W
        ((CFSG.ClassicalInvolution.WeakCT.blockSL2 F n i).range.map ψ)
        ((CFSG.ClassicalInvolution.WeakCT.blockSL2 F n j).range.map ψ)) ∧
      (∀ i j : Fin n, (i : ℕ) + 1 < j →
        ∀ a ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL2 F n i).range.map ψ,
        ∀ b ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL2 F n j).range.map ψ, a * b = b * a) ∧
      ⨆ i, (CFSG.ClassicalInvolution.WeakCT.blockSL2 F n i).range.map ψ = ψ.range := by
  have hW := CFSG.ClassicalInvolution.WeakCT.weakCTSystem_standard (K := F) n
  refine ⟨fun i j hj => ⟨_, CFSG.ClassicalInvolution.Balance.linearBlockStandardPair_map_of_ker_le_center
    (hW.pair i j hj) ψ hψ⟩, ?_, ?_⟩
  · rintro i j hij _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hW.comm i j hij x hx y hy]
  · rw [← Subgroup.map_iSup, hW.gen, ← MonoidHom.range_eq_map]

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal in
theorem ggE6Psi_of_chain {G : Type} [Group G] {X : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (U : Fin 6 → Subgroup G) (hgen : ⨆ k, U k = X)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 6, edgeE 6 i j →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j)) :
    ∃ Ψ : (modelUniv .E6 0 2 f Fact.out).K →* G, Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = X ∧
      ∀ k, (CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Minuscule.e6Datum (GaloisField 2 f)).rootGroup k).map Ψ = U k := by
  have hadm : StatedLieAdmissible .E6 0 2 f := ⟨Nat.prime_two, by omega, rfl⟩
  obtain ⟨Ψ, hker, hrange, hroot⟩ := CFSG.ClassicalInvolution.RouteD.exists_psi_E6 hadm
    (le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)) U hcomm hpair
  exact ⟨Ψ, hker, hrange.trans hgen, hroot⟩

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal in
theorem ggE6Psi_of_branchChains {G : Type} [Group G] {X : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    {U₁ U₂ U₃ U₄ U₅ U₆ : Subgroup G} (hgen : U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ ⊔ U₅ ⊔ U₆ = X)
    (h12 : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 2 f) W U₁ U₂)
    (h23 : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 2 f) W U₂ U₃)
    (h34 : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 2 f) W U₃ U₄)
    (h45 : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 2 f) W U₄ U₅)
    (h36 : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 2 f) W U₃ U₆)
    (c13 : ∀ a ∈ U₁, ∀ b ∈ U₃, a * b = b * a) (c14 : ∀ a ∈ U₁, ∀ b ∈ U₄, a * b = b * a)
    (c15 : ∀ a ∈ U₁, ∀ b ∈ U₅, a * b = b * a) (c24 : ∀ a ∈ U₂, ∀ b ∈ U₄, a * b = b * a)
    (c25 : ∀ a ∈ U₂, ∀ b ∈ U₅, a * b = b * a) (c35 : ∀ a ∈ U₃, ∀ b ∈ U₅, a * b = b * a)
    (c16 : ∀ a ∈ U₁, ∀ b ∈ U₆, a * b = b * a) (c26 : ∀ a ∈ U₂, ∀ b ∈ U₆, a * b = b * a)
    (c46 : ∀ a ∈ U₄, ∀ b ∈ U₆, a * b = b * a) (c56 : ∀ a ∈ U₅, ∀ b ∈ U₆, a * b = b * a) :
    ∃ Ψ : (modelUniv .E6 0 2 f Fact.out).K →* G, Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = X ∧
      ∀ k, (CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Minuscule.e6Datum (GaloisField 2 f)).rootGroup k).map Ψ =
        (![U₁, U₆, U₂, U₃, U₄, U₅] : Fin 6 → Subgroup G) k := by
  have cs : ∀ {A C : Subgroup G}, (∀ a ∈ A, ∀ b ∈ C, a * b = b * a) →
      ∀ b ∈ C, ∀ a ∈ A, b * a = a * b := fun h b hb a ha => (h a ha b hb).symm
  let U : Fin 6 → Subgroup G := ![U₁, U₆, U₂, U₃, U₄, U₅]
  have hU : ⨆ k, U k = X := by
    rw [← hgen]
    apply le_antisymm
    · refine iSup_le fun k => ?_
      fin_cases k
      · exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))
      · exact le_sup_right
      · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))
      · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
      · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
      · exact le_sup_right.trans le_sup_left
    · refine sup_le (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_
      · exact le_iSup U 0
      · exact le_iSup U 2
      · exact le_iSup U 3
      · exact le_iSup U 4
      · exact le_iSup U 5
      · exact le_iSup U 1
  refine ggE6Psi_of_chain hf U hU ?_ ?_
  · intro i j hij h1 h2
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact absurd (by decide) h1
      | exact absurd (by decide) h2
      | exact c13 | exact cs c13 | exact c14 | exact cs c14 | exact c15 | exact cs c15
      | exact c24 | exact cs c24 | exact c25 | exact cs c25 | exact c35 | exact cs c35
      | exact c16 | exact cs c16 | exact c26 | exact cs c26 | exact c46 | exact cs c46
      | exact c56 | exact cs c56
  · intro i j h
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd h (by decide)
      | exact h12 | exact h23 | exact h34 | exact h45
      | exact (let ⟨W, hW⟩ := h36; ⟨W, hW.symm⟩)

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal in
theorem ggE6Psi_of_twoSL6Charts {G : Type} [Group G] {f : ℕ} (hf : 2 ≤ f)
    (ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 f) →* G)
    (h₁ : ψ₁.ker ≤ Subgroup.center _) (h₂ : ψ₂.ker ≤ Subgroup.center _)
    (hJ : ψ₁.comp (CFSG.ClassicalInvolution.WeakCT.blockSL (GaloisField 2 f) 6 4 0 (by norm_num)) =
      ψ₂.comp (CFSG.ClassicalInvolution.WeakCT.blockSL (GaloisField 2 f) 6 4 0 (by norm_num)))
    (hM : ∀ a ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL (GaloisField 2 f) 6 3 3 (by norm_num)).range.map ψ₁,
      ∀ b ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL (GaloisField 2 f) 6 3 3 (by norm_num)).range.map ψ₂,
        a * b = b * a) :
    ∃ Ψ : (modelUniv .E6 0 2 f Fact.out).K →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ψ₁.range ⊔ (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 3).range.map ψ₂ ∧
      ∀ k, (CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Minuscule.e6Datum (GaloisField 2 f)).rootGroup k).map Ψ =
        (![(CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 0).range.map ψ₁, (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 3).range.map ψ₂,
          (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 1).range.map ψ₁, (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 2).range.map ψ₁,
          (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 3).range.map ψ₁, (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 4).range.map ψ₁] : Fin 6 → Subgroup G) k := by
  open CFSG.ClassicalInvolution.WeakCT in
  have hc : ∀ (j : ℕ) (hj : j + 2 ≤ 4), blockSL (GaloisField 2 f) 6 2 j (by omega) =
      (blockSL (GaloisField 2 f) 6 4 0 (by norm_num)).comp (blockSL (GaloisField 2 f) 4 2 j hj) := by
    intro j hj
    rw [blockSL_comp]
    congr 1
    omega
  open CFSG.ClassicalInvolution.WeakCT in
  have e : ∀ j : Fin 5, (j : ℕ) ≤ 2 → (blockSL2 (GaloisField 2 f) 5 j).range.map ψ₂ =
      (blockSL2 (GaloisField 2 f) 5 j).range.map ψ₁ := by
    intro j hj
    have h' : blockSL2 (GaloisField 2 f) 5 j = (blockSL (GaloisField 2 f) 6 4 0 (by norm_num)).comp
        (blockSL (GaloisField 2 f) 4 2 j (by omega)) := hc j (by omega)
    rw [← MonoidHom.range_comp, ← MonoidHom.range_comp, h', ← MonoidHom.comp_assoc,
      ← MonoidHom.comp_assoc, hJ]
  open CFSG.ClassicalInvolution.WeakCT in
  have hU4 : (blockSL2 (GaloisField 2 f) 5 3).range ≤ (blockSL (GaloisField 2 f) 6 3 3 (by norm_num)).range := by
    have h' : blockSL2 (GaloisField 2 f) 5 3 = (blockSL (GaloisField 2 f) 6 3 3 (by norm_num)).comp
        (blockSL (GaloisField 2 f) 3 2 0 (by norm_num)) := by
      rw [blockSL_comp]
      rfl
    rw [h', MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  open CFSG.ClassicalInvolution.WeakCT in
  have hU5 : (blockSL2 (GaloisField 2 f) 5 4).range ≤ (blockSL (GaloisField 2 f) 6 3 3 (by norm_num)).range := by
    have h' : blockSL2 (GaloisField 2 f) 5 4 = (blockSL (GaloisField 2 f) 6 3 3 (by norm_num)).comp
        (blockSL (GaloisField 2 f) 3 2 1 (by norm_num)) := by
      rw [blockSL_comp]
      rfl
    rw [h', MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  obtain ⟨p₁, c₁, g₁⟩ := ggStdChain_map_of_ker_le_center ψ₁ h₁
  obtain ⟨p₂, c₂, -⟩ := ggStdChain_map_of_ker_le_center ψ₂ h₂
  set V : Fin 5 → Subgroup G :=
    fun i => (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 i).range.map ψ₁ with hV
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have hgen : V 0 ⊔ V 1 ⊔ V 2 ⊔ V 3 ⊔ V 4 ⊔
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 3).range.map ψ₂ =
      ψ₁.range ⊔ (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 3).range.map ψ₂ := by
    rw [← g₁]
    congr 1
    apply le_antisymm
    · exact sup_le (sup_le (sup_le (sup_le (le_iSup V 0) (le_iSup V 1)) (le_iSup V 2)) (le_iSup V 3))
        (le_iSup V 4)
    · refine iSup_le fun k => ?_
      fin_cases k
      · exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
      · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
      · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
  refine ggE6Psi_of_branchChains hf hgen (p₁ 0 1 rfl) (p₁ 1 2 rfl) (p₁ 2 3 rfl) (p₁ 3 4 rfl)
    ?_ (c₁ 0 2 (by decide)) (c₁ 0 3 (by decide)) (c₁ 0 4 (by decide)) (c₁ 1 3 (by decide))
    (c₁ 1 4 (by decide)) (c₁ 2 4 (by decide)) ?_ ?_ ?_ ?_
  · have := p₂ 2 3 rfl
    rwa [e2] at this
  · have := c₂ 0 3 (by decide)
    rwa [e0] at this
  · have := c₂ 1 3 (by decide)
    rwa [e1] at this
  · intro a ha b hb
    exact hM a (Subgroup.map_mono hU4 ha) b (Subgroup.map_mono hU4 hb)
  · intro a ha b hb
    exact hM a (Subgroup.map_mono hU5 ha) b (Subgroup.map_mono hU4 hb)

theorem ggCentralImage_E6_of_twoSL6Charts {G : Type} [Group G] {f : ℕ} (hf : 2 ≤ f)
    (ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 f) →* G)
    (h₁ : ψ₁.ker ≤ Subgroup.center _) (h₂ : ψ₂.ker ≤ Subgroup.center _)
    (hJ : ψ₁.comp (CFSG.ClassicalInvolution.WeakCT.blockSL (GaloisField 2 f) 6 4 0 (by norm_num)) =
      ψ₂.comp (CFSG.ClassicalInvolution.WeakCT.blockSL (GaloisField 2 f) 6 4 0 (by norm_num)))
    (hM : ∀ a ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL (GaloisField 2 f) 6 3 3 (by norm_num)).range.map ψ₁,
      ∀ b ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL (GaloisField 2 f) 6 3 3 (by norm_num)).range.map ψ₂,
        a * b = b * a) :
    GGCentralImage .E6 0 f
      (ψ₁.range ⊔ (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 f) 5 3).range.map ψ₂) := by
  obtain ⟨Ψ, hker, hrange, -⟩ := ggE6Psi_of_twoSL6Charts hf ψ₁ ψ₂ h₁ h₂ hJ hM
  exact ⟨Ψ, ⟨Nat.prime_two, by omega, rfl⟩, hker, hrange⟩

end CFSG.StandardType

end
