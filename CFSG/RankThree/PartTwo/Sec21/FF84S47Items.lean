module

public import CFSG.RankThree.PartTwo.Sec21.FF84S47
public import CFSG.RankThree.PartTwo.Sec21.FF84S48Final

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

@[expose] def A_swap_stmt : Prop := ∃ g ∈ Nor Pm ⊓ A8s, conjBy g Ua = Ub

variable {G : Type} [Group G] [Finite G] {b : G} {L B K : Subgroup G} {b₁ b₂ : G}

theorem swap_of_moved (h : FF84Post b L B K b₁ b₂) (e : ↥L ≃* ↥A8s)
    (he₁ : ∀ x : ↥L, (x : G) = b₁ → ((e x : A8s) : P8) = cc)
    (he₂ : ∀ x : ↥L, (x : G) = b₂ → ((e x : A8s) : P8) = dd) {g : P8} (hgA : g ∈ A8s)
    (hgP : g ∈ Nor Pm) {U : Subgroup G} (hU : U ≤ L) (hmove : g ∉ Nor (trX e U)) :
    ∃ ℓ ∈ Nor B ⊓ Cen b, conjBy ℓ U ≠ U := by
  have hBP := trX_inf_B_L h e he₁ he₂
  set ℓ : ↥L := e.symm ⟨g, hgA⟩ with hℓ
  have hℓg : ((e ℓ : A8s) : P8) = g := by simp [hℓ]
  have hℓL : (ℓ : G) ∈ L := ℓ.2
  have hBLn : (ℓ : G) ∈ Nor (B ⊓ L) := by
    rw [mem_nor_trX_iff e hℓL inf_le_right, hBP]
    have : e ⟨(ℓ : G), hℓL⟩ = e ℓ := rfl
    rw [this, hℓg]
    exact hgP
  refine ⟨ℓ, ⟨?_, h.sec.hyp.hLC hℓL⟩, ?_⟩
  ·
    have hZ : Nor (B ⊓ L) ⊓ L ≤ Nor B := by
      apply le_nor_of_conj
      intro z hz x hx
      have hxC : x ∈ Cen b := h.sec.sylB.1 hx
      obtain ⟨i, l, hl, rfl⟩ := cen_decomp h hxC
      have hbB : b ∈ B := mem_b h.sec
      have hlB : l ∈ B := by
        have := mul_mem (inv_mem (zpow_mem hbB i)) hx
        simpa using this
      have hzl : z * l * z⁻¹ ∈ B ⊓ L := conj_mem_of_le_nor (le_refl _) hz.1 ⟨hlB, hl⟩
      have hzc : z ∈ Cen b := h.sec.hyp.hLC hz.2
      have hc := zpow_comm_of_mem_cen hzc i
      have e1 : z * (b ^ i * l) * z⁻¹ = b ^ i * (z * l * z⁻¹) := by
        calc z * (b ^ i * l) * z⁻¹ = (z * b ^ i) * l * z⁻¹ := by group
          _ = (b ^ i * z) * l * z⁻¹ := by rw [← hc]
          _ = b ^ i * (z * l * z⁻¹) := by group
      rw [e1]
      exact mul_mem (zpow_mem hbB i) hzl.1
    exact hZ ⟨hBLn, hℓL⟩
  · intro hc
    apply hmove
    have : (ℓ : G) ∈ Nor U := mem_nor_iff_conjBy.2 hc
    rw [mem_nor_trX_iff e hℓL hU] at this
    have h2 : e ⟨(ℓ : G), hℓL⟩ = e ℓ := rfl
    rw [h2, hℓg] at this
    exact this

theorem s47TransportItem_of
    (hP : A_PiStar_stmt)
    (hmax : A_U_max_stmt) : S47TransportItem := by
  intro G _ _ b L B K b₁ b₂ hpost
  exact S47_transport (a8Model_of_hyp hpost.sec.hyp) hP hmax hpost

theorem s47SwapItem_of
    (hP : A_PiStar_stmt)
    (hsw : A_swap_stmt) : S47SwapItem := by
  intro G _ _ b L B K b₁ b₂ hpost U hU
  have hA : A8Model L := a8Model_of_hyp hpost.sec.hyp
  obtain ⟨e, he₁, he₂⟩ := M0_model hA hpost
  have hBP := trX_inf_B_L hpost e he₁ he₂
  have hUL : U ≤ L := ((S47_PiStar_eq hpost U).1 hU).1
  have hTU : trX e U ∈ PiStar A8s Pm 2 := by
    have := (trX_piStar_iff e (inf_le_right : B ⊓ L ≤ L) hUL).1 ((S47_PiStar_eq hpost U).1 hU)
    rwa [hBP] at this
  obtain ⟨g, ⟨hgP, hgA⟩, hg⟩ := hsw
  rw [hP] at hTU
  have hne : Ua ≠ Ub := A_U_data_basic.1.1
  rcases hTU with hTU | hTU
  · refine swap_of_moved hpost e he₁ he₂ hgA hgP hUL ?_
    rw [hTU]
    intro hn
    apply hne
    rw [← hg, mem_nor_iff_conjBy.1 hn]
  · refine swap_of_moved hpost e he₁ he₂ (inv_mem hgA) (inv_mem hgP) hUL ?_
    rw [hTU]
    intro hn
    apply hne
    have h1 := mem_nor_iff_conjBy.1 hn
    have h2 : conjBy g⁻¹ Ub = Ua := by
      rw [← hg]; exact conjBy_inv_conjBy g Ua
    rw [← h2, h1]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
