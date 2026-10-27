module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Tail
public import CFSG.Milestones.ASVolI.C61.PBasic245Single

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

open CFSG.Open CFSG.Quasithin Subgroup

namespace C56
open CFSG.QuasithinUnique.C56

section

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem c61_single_bound (hN : NaturalModuleStructure)
    (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) :
    (IsAltType L 3 → Nat.card (blockD S L) ≤ 2 ^ 1) ∧
      ∀ n : ℕ, 1 < n → IsLin2Type L n → Nat.card (blockD S L) ≤ 2 ^ n := by
  have hLsh := isShort hcs
  obtain ⟨M₀, hSM, hMT, h2⟩ := exists_index_two hcs
  obtain ⟨q, W, hq2, hidxQ, hidxW, hZ, hcent, hcomm, hmain, hUeq⟩ :=
    single_rank1 hN hcs hj hL hSM hMT h2
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  have hxinvS : x₀⁻¹ ∉ S := fun h => hx₀S (by simpa using inv_mem h)
  obtain ⟨hidx, o1, -, o3, -, o5, -, -, o8, -, -, o11⟩ := hmain x₀ hx₀ hx₀S
  obtain ⟨-, -, -, -, -, -, -, -, o8', -, -, -⟩ := hmain x₀⁻¹ (inv_mem hx₀) hxinvS
  set Q := baum S ⊓ centralizer (blockU L : Set G) with hQdef
  set D := Q ⊓ centralizer (L : Set G) with hDdef
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le L)
  have hUQ : blockU L ≤ Q := by
    rw [o1]
    exact le_sup_left
  have hD : Nat.card (blockD S L) ≤ q := by
    have hblockD : blockD S L = D := by
      show S ⊓ centralizer ((conjJoin S L : Subgroup G) : Set G) = _
      rw [hj]
      exact o11
    rw [hblockD]
    have hUD : blockU L ⊓ D = blockZ L := by
      refine le_antisymm (fun g hg => ⟨hg.1, hg.2.2⟩) fun g hg => ⟨hg.1, hUQ hg.1, hg.2⟩
    have hUZ : Nat.card (blockU L) = Nat.card (blockZ L) * q ^ 2 := by
      have := C5.card_eq_card_mul_relIndex (inf_le_left : blockU L ⊓ centralizer (L : Set G) ≤
        blockU L)
      rw [hZ] at this
      exact this
    have hD2 : conjSubgroup D x₀ ≤ Q := by
      have hDle : D ≤ conjSubgroup Q x₀⁻¹ := by
        rw [o8']
        exact le_sup_left
      have := C5.conjSubgroup_mono hDle x₀
      rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at this
    exact card_le_of_rank1_data (x := x₀) o1 (fun u hu d hd =>
      Subgroup.mem_centralizer_iff.mp hd.2 u (hUL hu)) hUD hUZ o3 o5.1
      (by rw [o8]; exact le_sup_left) hD2 hidx
  refine ⟨fun h3 => ?_, fun n hn hlin => ?_⟩
  · have h4 := relIndex_blockZ_isAltType3 (G := G) (L := L) h3
    have hq : q = 2 := by
      have : q ^ 2 = 2 ^ 2 := hZ.symm.trans (h4.trans (by norm_num))
      exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) this
    rw [hq] at hD
    exact hD
  · have h1 := relIndex_blockZ_isLin2Type (G := G) (L := L) hlin
    have hq : q = 2 ^ n :=
      Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hZ.symm.trans h1 :
        (fun m : ℕ => m ^ 2) q = (fun m : ℕ => m ^ 2) (2 ^ n))
    rw [hq] at hD
    exact hD

end

end C56

end CFSG.QuasithinUnique.burnsideC56_P
