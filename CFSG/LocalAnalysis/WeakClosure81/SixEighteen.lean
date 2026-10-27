module

public import CFSG.LocalAnalysis.WeakClosure81.SixSixteen
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22tb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_centerOf_of_twoResidual_le {V S H : Subgroup G}
    (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j : ℕ} (hij : i ≤ j)
    (hj : j < rk ↥V) (h : twoResidual H ≤ centralizer (E3.cClos V i S : Set G)) :
    H ≤ normalizer (centerOf (E3.wClos V j S) : Set G) := by
  rw [← sup_twoResidual_eq hS]
  refine sup_le ?_ ?_
  · exact le_normalizer.trans ((E3.normalizer_le_normalizer_wClos (V := V) (i := j) S).trans
      (E3.normalizer_le_normalizer_centerOf _))
  · exact h.trans ((centralizer_le (centerOf_wClos_le_cClos hV hij hj S)).trans
      (centralizer_le_normalizer _))

theorem six_eighteen_tri {V S H₁ H₂ : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS₁ : IsSylowIn 2 S H₁) (hF₁ : InFSq 1 H₁) (hS₂ : IsSylowIn 2 S H₂) (hF₂ : InFSq 1 H₂)
    {i : ℕ} (hi : i + 2 < E3.sParam hV) :
    H₁ ⊔ H₂ ≤ normalizer (E3.wClos V i S : Set G) ∨
      H₁ ⊔ H₂ ≤ normalizer (centerOf (E3.wClos V (i + 1) S) : Set G) ∨
      ∀ j : ℕ, i + 2 ≤ j → j < rk ↥V →
        H₁ ⊔ H₂ ≤ normalizer (centerOf (E3.wClos V j S) : Set G) := by
  have hsV : E3.sParam hV ≤ rk ↥V := E3.sParam_le_rk hV
  have hcases : ∀ {K : Subgroup G}, IsSylowIn 2 S K → InFSq 1 K →
      (K ≤ normalizer (E3.wClos V i S : Set G) ∧
          K ≤ normalizer (centerOf (E3.wClos V (i + 1) S) : Set G)) ∨
      (K ≤ normalizer (E3.wClos V i S : Set G) ∧ ∀ j : ℕ, i + 2 ≤ j → j < rk ↥V →
          K ≤ normalizer (centerOf (E3.wClos V j S) : Set G)) ∨
      (K ≤ normalizer (centerOf (E3.wClos V (i + 1) S) : Set G) ∧ ∀ j : ℕ, i + 2 ≤ j →
          j < rk ↥V → K ≤ normalizer (centerOf (E3.wClos V j S) : Set G)) := by
    intro K hSK hFK
    rcases UC22.uc22p22tb_dich hV hSK (i := i + 1) (j := 1) hFK (by omega) with h1 | h1
    · exact Or.inl ⟨h1.trans (normalizer_wClos_anti hV (by omega) (by omega)),
        h1.trans (E3.normalizer_le_normalizer_centerOf _)⟩
    · rw [Subgroup.commutator_comm] at h1
      have hR2 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
      have hγ : ∀ j : ℕ, i + 2 ≤ j → j < rk ↥V →
          K ≤ normalizer (centerOf (E3.wClos V j S) : Set G) := fun j hj hjr =>
        le_normalizer_centerOf_of_twoResidual_le hV hSK (i := i + 1 + 1) (by omega) hjr hR2
      rcases UC22.uc22p22tb_dich hV hSK (i := i) (j := 1) hFK (by omega) with h0 | h0
      · exact Or.inr (Or.inl ⟨h0, hγ⟩)
      · rw [Subgroup.commutator_comm] at h0
        have hR1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0
        exact Or.inr (Or.inr ⟨le_normalizer_centerOf_of_twoResidual_le hV hSK
          (i := i + 1) le_rfl (by omega) hR1, hγ⟩)
  rcases hcases hS₁ hF₁ with ⟨a1, b1⟩ | ⟨a1, c1⟩ | ⟨b1, c1⟩ <;>
    rcases hcases hS₂ hF₂ with ⟨a2, b2⟩ | ⟨a2, c2⟩ | ⟨b2, c2⟩
  · exact Or.inl (sup_le a1 a2)
  · exact Or.inl (sup_le a1 a2)
  · exact Or.inr (Or.inl (sup_le b1 b2))
  · exact Or.inl (sup_le a1 a2)
  · exact Or.inl (sup_le a1 a2)
  · exact Or.inr (Or.inr fun j hj hjr => sup_le (c1 j hj hjr) (c2 j hj hjr))
  · exact Or.inr (Or.inl (sup_le b1 b2))
  · exact Or.inr (Or.inr fun j hj hjr => sup_le (c1 j hj hjr) (c2 j hj hjr))
  · exact Or.inr (Or.inl (sup_le b1 b2))

theorem six_eighteen {V M H S H₁ H₂ : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : IsSylowIn 2 S H) {k : ℕ} (hH : E1.InE k H)
    (hS₁ : IsSylowIn 2 S H₁) (hF₁ : InFSq 1 H₁) (hS₂ : IsSylowIn 2 S H₂) (hF₂ : InFSq 1 H₂)
    (hU : InCalU M (H₁ ⊔ H₂)) (hW0 : E3.wClos V 0 S ≠ ⊥) (hgt : k + 2 < E3.sParam hV) :
    H ≤ M := by
  by_contra hHM
  have hsV : E3.sParam hV ≤ rk ↥V := E3.sParam_le_rk hV
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have key : ∀ i : ℕ, i ≤ 2 → normalizer (E3.wClos V i S : Set G) ≤ M →
      centralizer (E3.cClos V (i + k) S : Set G) ≤ M → False := by
    intro i hi hN hC
    apply hHM
    rw [← e3_19_of_inE hV hS (i := i) (j := k) hH (by omega)]
    exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hN)
  have hZ : ∀ j : ℕ, j < rk ↥V →
      H₁ ⊔ H₂ ≤ normalizer (centerOf (E3.wClos V j S) : Set G) →
      normalizer (E3.wClos V j S : Set G) ≤ M ∧ centralizer (E3.cClos V j S : Set G) ≤ M := by
    intro j hj hX
    have hWj2 : IsPGroup 2 (E3.wClos V j S) := hS2.to_le (E3.wClos_le j S)
    have hNZ := normalizer_le_of_inCalU hU hX
      (E3.centerOf_ne_bot_of_isPGroup hWj2 (wClos_ne_bot_of_zero hV hW0 hj))
      (hWj2.to_le inf_le_left)
    exact ⟨(E3.normalizer_le_normalizer_centerOf _).trans hNZ,
      (centralizer_le (centerOf_wClos_le_cClos_self j S)).trans
        ((centralizer_le_normalizer _).trans hNZ)⟩
  have hW : ∀ i : ℕ, i < rk ↥V → H₁ ⊔ H₂ ≤ normalizer (E3.wClos V i S : Set G) →
      ∀ j : ℕ, j ≤ i →
      normalizer (E3.wClos V j S : Set G) ≤ M ∧ centralizer (E3.cClos V j S : Set G) ≤ M :=
    fun i hi hX j hji => hZ j (by omega)
      (hX.trans ((normalizer_wClos_anti hV hji hi).trans (E3.normalizer_le_normalizer_centerOf _)))
  have hN1 : normalizer (E3.wClos V 1 S : Set G) ≤ M := by
    rcases six_eighteen_tri hV hS₁ hF₁ hS₂ hF₂ (i := 0) (by omega) with h | h | h
    · exact (normalizer_wClos_anti hV (Nat.zero_le 1) (by omega)).trans
        (hW 0 (by omega) h 0 le_rfl).1
    · exact (hZ 1 (by omega) h).1
    · exact (key 2 le_rfl (hZ 2 (by omega) (h 2 (by omega) (by omega))).1
        (hZ (2 + k) (by omega) (h (2 + k) (by omega) (by omega))).2).elim
  rcases six_eighteen_tri hV hS₁ hF₁ hS₂ hF₂ (i := k) (by omega) with h | h | h
  · have h' := hW k (by omega) h
    exact key 0 (by omega) (h' 0 (Nat.zero_le k)).1 (by simpa using (h' k le_rfl).2)
  · exact key 1 (by omega) hN1 (by rw [Nat.add_comm]; exact (hZ (k + 1) (by omega) h).2)
  · exact key 2 le_rfl ((normalizer_wClos_anti hV (by omega : 1 ≤ 2) (by omega)).trans hN1)
      (by rw [Nat.add_comm]; exact (hZ (k + 2) (by omega) (h (k + 2) le_rfl (by omega))).2)

end CFSG.LocalAnalysis.WeakClosure81
