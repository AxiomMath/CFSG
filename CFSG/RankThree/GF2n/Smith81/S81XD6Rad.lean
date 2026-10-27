module

public import CFSG.RankThree.GF2n.Smith81.S81XD6Def
public import CFSG.RankThree.GF2n.Smith81.S81XE7Pf
public import CFSG.RankThree.GF2n.Smith81.S81E7Roots
public import CFSG.RankThree.GF2n.Smith81.S81XD6Fin

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.D6Spin


variable {K : Type} [Field K] [CharP K 2]

private theorem d6rad_presPiece_of_mem_LamG {g : Gp K} (hg : g ∈ LamG K) :
    PresPiece (endoE g) := by
  have h : (g : (Module.End K (V K))ˣ) ∈ GG K := Lam_le_GG (mem_LamG.1 hg)
  have h' : PresPiece ((g : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
      PresPiece (((g : (Module.End K (V K))ˣ)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := h
  exact h'.1

theorem coef_zero_off_perp {a : Fin e7Data.d} {c : (Fin (Tag.rank .E7) → ℤ) → K}
    (hu : prodX (Phi a).toList c ∈ LamG K) {δ : Fin (Tag.rank .E7) → ℤ} (hδ : δ ∈ Phi a)
    (hnp : δ ∉ Perp) : c δ = 0 := by
  have hδr : IsRoot .E7 δ := (mem_Phi.1 hδ).1
  obtain ⟨b, hb⟩ := exists_pr_eq_neg_one hδr
  have h1 := coef_prodX a c b hδr hb
  rw [if_pos hδ] at h1
  have hP := d6rad_presPiece_of_mem_LamG hu
  have hv : endoE (prodX (Phi a).toList c) (Finsupp.single b 1) ∈ Piece K (pr b theta) :=
    hP (pr b theta) _ (single_mem_Piece b)
  have hne0 : MinData.toWeight δ ⬝ᵥ theta ≠ 0 := fun h =>
    hnp (show IsRoot .E7 δ ∧ MinData.toWeight δ ⬝ᵥ theta = 0 from ⟨hδr, h⟩)
  have hne : pr (shift δ b) theta ≠ pr b theta := by
    rw [pr_shift hδr hb theta]
    omega
  have h2 : endoE (prodX (Phi a).toList c) (Finsupp.single b 1) (shift δ b) = 0 :=
    mem_Piece_iff.1 hv (shift δ b) hne
  exact h1.symm.trans h2

theorem UA_inf_UA_V0 {a a' : Fin e7Data.d}
    (hU : ∀ γ γ' : Fin (Tag.rank .E7) → ℤ, γ ∈ Phi a → γ ∈ Phi a' → γ' ∈ Phi a → γ' ∈ Phi a' → γ = γ')
    {y y' : Gp K} (hy : y ∈ UA K a) (hy' : y' ∈ UA K a') (hyL : y ∈ LamG K) (hy'L : y' ∈ LamG K)
    (hV : ∀ b : Fin e7Data.d, pr b theta = 0 →
      endoE y (Finsupp.single b 1) = endoE y' (Finsupp.single b 1)) :
    y = 1 ∨ ∃ (δ : Fin (Tag.rank .E7) → ℤ) (c : K), δ ∈ Perp ∧ c ≠ 0 ∧ y = xE δ c := by
  obtain ⟨c, hc⟩ := mem_UA_iff.1 hy
  obtain ⟨c', hc'⟩ := mem_UA_iff.1 hy'
  have hLc : prodX (Phi a).toList c ∈ LamG K := by
    rw [← hc]
    exact hyL
  have key : ∀ γ ∈ Phi a, γ ∉ Phi a' → c γ = 0 := by
    intro γ hγ hγ'
    by_cases hP : γ ∈ Perp
    · have hPr : IsRoot .E7 γ ∧ MinData.toWeight γ ⬝ᵥ theta = 0 := hP
      obtain ⟨b, hb0, hb⟩ := exists_idx0_move γ hPr.1 hPr.2
      have h1 := coef_prodX a c b hPr.1 hb
      have h2 := coef_prodX a' c' b hPr.1 hb
      rw [← hc, if_pos hγ] at h1
      rw [← hc', if_neg hγ'] at h2
      rw [hV b hb0] at h1
      exact h1.symm.trans h2
    · exact coef_zero_off_perp hLc hγ hP
  by_cases hex : ∃ δ₀, δ₀ ∈ Phi a ∧ δ₀ ∈ Phi a'
  · obtain ⟨δ₀, hδa, hδa'⟩ := hex
    have hz : ∀ γ ∈ (Phi a).toList, γ ≠ δ₀ → c γ = 0 := by
      intro γ hγ hne
      apply key γ (Finset.mem_toList.1 hγ)
      intro hγ'
      exact hne (hU γ δ₀ (Finset.mem_toList.1 hγ) hγ' hδa hδa')
    have hu' : y = xE δ₀ (c δ₀) := by
      rw [hc]
      exact prodX_eq_single (Finset.nodup_toList _) (Finset.mem_toList.2 hδa) hz
    by_cases hc0 : c δ₀ = 0
    · left
      rw [hu', hc0]
      exact e7Data_valid.xm_zero K δ₀
    · right
      have hPerp : δ₀ ∈ Perp := by
        by_contra hnp
        exact hc0 (coef_zero_off_perp hLc hδa hnp)
      exact ⟨δ₀, c δ₀, hPerp, hc0, hu'⟩
  · left
    rw [hc]
    apply prodX_eq_one
    intro γ hγ
    exact key γ (Finset.mem_toList.1 hγ) (fun hγ' => hex ⟨γ, Finset.mem_toList.1 hγ, hγ'⟩)

end CFSG.RankThree.GF2n.Smith81.D6X
