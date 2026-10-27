module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.ClassicalInvolution.WeakCT.FieldTwo
import CFSG.ClassicalInvolution.WeakCT.Amalgam
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.ClassicalInvolution.WeakCT.SpPair

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
open scoped MatrixGroups

private def pathAdj (m : ℕ) (i j : Fin m) : Prop := (i : ℕ) + 1 = j

private def pathPar (m : ℕ) (k : Fin m) : Fin m := ⟨k.val - 1, by have := k.isLt; omega⟩

private theorem rootedTree_pathAdj {m : ℕ} (hm : 0 < m) :
    RootedTree (pathAdj m) (pathPar m) (fun k => k.val) ⟨0, hm⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    have h1 : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp only [pathPar]
    omega
  · intro k hk
    have h1 : k.val ≠ 0 := fun h => hk (Fin.ext h)
    left
    simp only [pathAdj, pathPar]
    omega
  · intro i j hij hji
    simp only [pathAdj] at hij hji
    omega
  · intro i j hij
    simp only [pathAdj] at hij
    have hj : j ≠ (⟨0, hm⟩ : Fin m) := by
      intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    exact Or.inl ⟨hj, Fin.ext (by simp only [pathPar]; omega)⟩

theorem exists_marking_of_a2System_linear (m : ℕ) (hm : 3 ≤ m) (X : Type) [Group X]
    (U : Fin m → Subgroup X) (hU : A2System adjA U ⊤) :
    ∃ ψ : SL(m + 1, ZMod 2) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(m + 1, ZMod 2) ∧
      (∀ i, (blockSL2 (ZMod 2) m i).range.map ψ = U i) ∧
      CFSG.IsQuasisimple X ∧ CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (m + 1) 2 1 := by
  classical
  obtain ⟨-, hgen, hcommA, hpairA⟩ := hU
  have hm0 : 0 < m := by omega
  have hT : RootedTree (pathAdj m) (pathPar m) (fun k => k.val) ⟨0, hm0⟩ :=
    rootedTree_pathAdj hm0
  have hroot : ∃ c : Fin m, pathAdj m ⟨0, hm0⟩ c ∨ pathAdj m c ⟨0, hm0⟩ :=
    ⟨⟨1, by omega⟩, Or.inl rfl⟩
  have hcomm' : ∀ i j : Fin m, i ≠ j → ¬ pathAdj m i j → ¬ pathAdj m j i →
      ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x := by
    intro i j hne h1 h2 x hx y hy
    have hnot : ¬ adjA i j := by
      intro h
      rcases h with h | h
      · exact h1 h
      · exact h2 h
    exact hcommA i j hne hnot x hx y hy
  have hpair' : ∀ i j : Fin m, pathAdj m i j → ∃ W : Subgroup X,
      LinearBlockStandardPair (ZMod 2) W (U i) (U j) :=
    fun i j h => hpairA i j (Or.inl h)
  obtain ⟨ρ, hρ, hψ⟩ := exists_frame_of_tree_two (K := ZMod 2) (X := X) (r := m)
    (adj := pathAdj m) (par := pathPar m) (dep := fun k => k.val) (k₀ := ⟨0, hm0⟩) (U := U)
    (by rw [Nat.card_eq_fintype_card, ZMod.card]) hT hroot hcomm' hpair'
  have hρinj : ∀ k, Function.Injective (ρ k) := fun k => (hρ k).1
  have hρrange : ∀ k, (ρ k).range = U k := fun k => (hρ k).2
  let θ : Fin m → SL(3, ZMod 2) →* X := fun i =>
    if h : (i : ℕ) + 1 < m then
      (hψ i ⟨i + 1, h⟩ (by simp only [pathAdj])).choose
    else 1
  have hθ_spec : ∀ (i : Fin m) (h : (i : ℕ) + 1 < m),
      (θ i).comp (blockSL (ZMod 2) 3 2 0 (by omega)) = ρ i ∧
      (θ i).comp (blockSL (ZMod 2) 3 2 1 (by omega)) = ρ ⟨i + 1, h⟩ := by
    intro i h
    have hθ : θ i = (hψ i ⟨i + 1, h⟩ (by simp only [pathAdj])).choose := by
      dsimp only [θ]
      rw [dif_pos h]
    rw [hθ]
    exact (hψ i ⟨i + 1, h⟩ (by simp only [pathAdj])).choose_spec
  have hcommF : ∀ i j : Fin m, (i : ℕ) + 1 < j → ∀ a b : SL(2, ZMod 2),
      ρ i a * ρ j b = ρ j b * ρ i a := by
    intro i j hij a b
    have hne : i ≠ j := by intro h; subst h; omega
    have hnot : ¬ adjA i j := by
      intro h
      rcases h with h | h
      · omega
      · omega
    exact hcommA i j hne hnot (ρ i a) (hρrange i ▸ ⟨a, rfl⟩) (ρ j b) (hρrange j ▸ ⟨b, rfl⟩)
  let F : CTFamily (ZMod 2) X m :=
    { ι := ρ
      θ := θ
      left := fun i h => (hθ_spec i h).1
      right := fun i h => (hθ_spec i h).2
      comm := hcommF }
  have hgenF : ⨆ i, (F.ι i).range = ⊤ := by
    have h1 : (⨆ i, (ρ i).range) = ⨆ i, U i := iSup_congr fun i => hρrange i
    change (⨆ i, (ρ i).range) = ⊤
    rw [h1]
    exact hgen
  have hntF : ∃ i, ∃ A, F.ι i A ≠ 1 := by
    refine ⟨⟨0, hm0⟩, tv 0 1 (1 : ZMod 2), fun h => ?_⟩
    exact tv01_ne_one (hρinj ⟨0, hm0⟩ (h.trans (map_one (ρ ⟨0, hm0⟩)).symm))
  obtain ⟨ψ, hψblk, hsurj, hker, hqs, -, hmodel⟩ :=
    exists_recognition (K := ZMod 2) (n := m) (Y := X) (p := 2) (f := 1)
      hm Nat.prime_two le_rfl (by rw [Nat.card_eq_fintype_card, ZMod.card, pow_one]) F hgenF hntF
  refine ⟨ψ, hsurj, hker, fun i => ?_, hqs, hmodel⟩
  rw [MonoidHom.map_range, ← hρrange i]
  congr 1
  exact MonoidHom.ext fun A => hψblk i A

theorem curtisA2_linear (m : ℕ) (hm : 3 ≤ m) (X : Type) [Group X] (U : Fin m → Subgroup X)
    (hU : A2System adjA U ⊤) :
    CFSG.IsQuasisimple X ∧ CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
      CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (m + 1) 2 1 := by
  obtain ⟨-, -, -, -, hqs, hmodel⟩ := exists_marking_of_a2System_linear m hm X U hU
  exact ⟨hqs, hmodel⟩

end CFSG.StandardType.FF81
