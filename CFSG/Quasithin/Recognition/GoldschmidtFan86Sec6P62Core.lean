module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Dd2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Dd1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Dih

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

variable {L : ZLab Γ G} (F : FanTree Γ G) (H : LabHyp L)
include F H

theorem noncomm_false (h40 : Fan40 F) {α : V} (hα : valence Γ α = 5) (hN : NoncommAt L α) :
    False := by
  obtain ⟨l₁, l₂, hl₁, hl₂, hnc⟩ := hN
  obtain ⟨μ₁, h₁⟩ := exists_br F hl₁
  obtain ⟨μ₂, h₂⟩ := exists_br F hl₂
  have hμ : μ₁ ≠ μ₂ := br_ne_of_nc F H hα h₁ h₂ hnc
  obtain ⟨s, hs, hsμ₁, hsμ₂, hss, κ, hκ, hsκ⟩ := exists_swap F hα h₁.1 h₂.1
  obtain ⟨δ, hκδ, hδα⟩ := F.exists_adj_ne κ α
  have hb : Br Γ α κ δ := ⟨hκ, hκδ, hδα⟩
  have hvδ : valence Γ δ = 5 := (Br.valence F hα hb).2
  have hbδ : Br Γ δ κ α := Br.symm hb
  have hdist : Γ.dist δ α = 2 := Br.dist_two F hbδ
  have hNδ : NoncommAt L δ := noncomm_all F hα hvδ ⟨l₁, l₂, hl₁, hl₂, hnc⟩
  have hy2 := nc_sq F H hα hl₁ hl₂ hnc
  have hyK : L.z l₁ * L.z l₂ ∈ nbrStab Γ G α :=
    (nbrStab Γ G α).mul_mem (H.ker α l₁ hα hl₁) (H.ker α l₂ hα hl₂)
  have hyκ : (L.z l₁ * L.z l₂) • κ = κ := mem_nbrStab.1 hyK κ hκ
  have hyδ := prod_fix_delta F H hα h₁ h₂ hs hsμ₁ hsκ hb
  have hnK : L.z l₁ * L.z l₂ ∉ nbrStab Γ G δ :=
    lemma_A F h40 H hvδ hNδ hdist (MulAction.mem_stabilizer_iff.2 hyδ) hy2
  obtain ⟨ν, η, hbη, hνκ, hncη⟩ := exists_commuting_other_branch F H h40 hvδ hNδ hbδ
  have hdη := Br.dist_two F hbη
  have hvη := (Br.valence F hvδ hbη).2
  have hfix : L.z η • α = α := by
    by_contra hne
    exact hncη ((nc_iff F H hvδ hbδ hdη).2 hne)
  have hηK := H.ker δ η hvδ hdη
  have hηκ : L.z η • κ = κ := mem_nbrStab.1 hηK κ hbδ.1
  have hkk := z_sq (L := L) hvη
  have hcase : L.z η ∈ nbrStab Γ G α ∨ L.z η * s ∈ nbrStab Γ G α := by
    by_cases hK : L.z η ∈ nbrStab Γ G α
    · exact Or.inl hK
    · refine Or.inr (mul_mem_nbrStab_of_sq_mem F hκ
        ⟨MulAction.mem_stabilizer_iff.2 hfix, MulAction.mem_stabilizer_iff.2 hηκ⟩
        ⟨hs, MulAction.mem_stabilizer_iff.2 hsκ⟩ (by rw [hkk]; exact one_mem _) hss hK ?_)
      intro hsK
      exact hμ ((mem_nbrStab.1 hsK μ₁ h₁.1).symm.trans hsμ₁)
  have hmem := conj_y_mem F H hα h₁ h₂ hnc hs hsμ₁ hsμ₂ hkk hcase
  exact step_end F H hα hvδ hbδ hbη hνκ hyδ hyκ hnK hmem

end P62

end CFSG.Quasithin.Fan86
