module

public import CFSG.Quasithin.EmptyFaithful.S153YSPortB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Tail

public section

namespace CFSG.QuasithinUnique.C56W

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

theorem card_eq_of_rank1_data {G : Type*} [Group G] [Finite G] {Q U D Z : Subgroup G} {q : ℕ}
    (hQ : Q = U ⊔ D) (hDc : ∀ u ∈ U, ∀ d ∈ D, u * d = d * u) (hUD : U ⊓ D = Z)
    (hUZ : Nat.card U = Nat.card Z * q ^ 2) : Nat.card Q = q ^ 2 * Nat.card D := by
  have h1 : Nat.card Q * Nat.card Z = Nat.card U * Nat.card D := by
    have := C5.card_sup_mul_card_inf_of_le_normalizer (A := U) (B := D)
      (C5.le_normalizer_of_commute hDc)
    rw [← hQ, hUD] at this
    exact this
  have hz : 0 < Nat.card Z := Nat.card_pos
  have : Nat.card Q * Nat.card Z = (q ^ 2 * Nat.card D) * Nat.card Z := by
    rw [h1, hUZ]; ring
  exact Nat.eq_of_mul_eq_mul_right hz this

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

namespace WSet1

variable (hcs : WSet1 H S L)
include hcs

theorem single_card_data (hN : NaturalModuleStructure)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3)
    {M₀ : Subgroup G} (hC : C5.NoCommonNormal S H M₀) (hSM : S ≤ M₀) (h2 : S.relIndex M₀ = 2) :
    ∃ q : ℕ, 2 ≤ q ∧
      (blockU L ⊓ centralizer (L : Set G)).relIndex (blockU L) = q ^ 2 ∧
      (∀ x ∈ pCoreOf 2 H, ∀ y ∈ pCoreOf 2 H, x * y = y * x) ∧
      Nat.card (pCoreOf 2 H) = q ^ 2 * Nat.card (blockD S L) ∧ Nat.card (blockD S L) ≤ q := by
  have hLsh := hcs.isShort
  have hj := hcs.conjJoin_eq
  obtain ⟨q, _, hq2, -, -, hZ, -, -, hmain, -⟩ :=
    hcs.single_rank1 hN hL hC hSM h2
  obtain ⟨x₀, hx₀, hx₀S⟩ := exists_mem_diff_of_relIndex_two h2
  have hxinvS : x₀⁻¹ ∉ S := fun h => hx₀S (by simpa using inv_mem h)
  obtain ⟨hidx, o1, -, o3, o4, o5, -, -, o8, -, -, o11⟩ := hmain x₀ hx₀ hx₀S
  obtain ⟨-, -, -, -, -, -, -, -, o8', -, -, -⟩ := hmain x₀⁻¹ (inv_mem hx₀) hxinvS
  set Q := baum S ⊓ centralizer (blockU L : Set G) with hQdef
  set D := Q ⊓ centralizer (L : Set G) with hDdef
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le L)
  have hUQ : blockU L ≤ Q := by
    rw [o1]
    exact le_sup_left
  have hblockD : blockD S L = D := by
    show S ⊓ centralizer ((conjJoin S L : Subgroup G) : Set G) = _
    rw [hj]
    exact o11
  have hUD : blockU L ⊓ D = blockZ L := by
    refine le_antisymm (fun g hg => ⟨hg.1, hg.2.2⟩) fun g hg => ⟨hg.1, hUQ hg.1, hg.2⟩
  have hUZ : Nat.card (blockU L) = Nat.card (blockZ L) * q ^ 2 := by
    have := C5.card_eq_card_mul_relIndex (inf_le_left : blockU L ⊓ centralizer (L : Set G) ≤
      blockU L)
    rw [hZ] at this
    exact this
  have hDc : ∀ u ∈ blockU L, ∀ d ∈ D, u * d = d * u := fun u hu d hd =>
    Subgroup.mem_centralizer_iff.mp hd.2 u (hUL hu)
  refine ⟨q, hq2, hZ, ?_, ?_, ?_⟩
  · rw [o4]
    exact o5.1
  · rw [o4, hblockD]
    exact card_eq_of_rank1_data o1 hDc hUD hUZ
  · have hD2 : conjSubgroup D x₀ ≤ Q := by
      have hDle : D ≤ conjSubgroup Q x₀⁻¹ := by
        rw [o8']
        exact le_sup_left
      have := C5.conjSubgroup_mono hDle x₀
      rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at this
    rw [hblockD]
    exact C56.card_le_of_rank1_data (x := x₀) o1 hDc hUD hUZ o3 o5.1
      (by rw [o8]; exact le_sup_left) hD2 hidx

end WSet1

end CFSG.QuasithinUnique.C56W
