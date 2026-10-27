module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSExcl
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSSplitB
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSSp42

public section

namespace CFSG.Quasithin.F6.GoldAmS

open CFSG.Open CFSG.QuasithinUnique

theorem goldCaseSp42_of_amalgam {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : IsGoldschmidtAmalgam G₁ G₂) (c₁ : CharTwo G₁) (c₂ : CharTwo G₂)
    (hT : Nat.card ↥(G₁ ⊓ G₂) = 16) : IsGoldCaseSp42 G₁ G₂ := by
  have hT' : Nat.card ↥(G₂ ⊓ G₁) = 16 := by rw [inf_comm]; exact hT
  obtain ⟨e₁, e₂⟩ := both_elementary h c₁ c₂ hT
  obtain ⟨N₁, ε₁, v₁⟩ := vtxB_of_vertex h.toIsGoldschmidtTriple c₁ hT e₁
  obtain ⟨N₂, ε₂, v₂⟩ := vtxB_of_vertex (amalgam_symm h).toIsGoldschmidtTriple c₂ hT' e₂
  have G : Glob G₁ G₂ N₁ N₂ ε₁ ε₂ := ⟨h, hT, v₁, v₂⟩
  obtain ⟨Dd⟩ := G.typeB
  obtain ⟨W, gW, fW, K₁, K₂, hW, hK, ⟨D'⟩⟩ := exists_model_Sp42
  refine ⟨⟨W, gW, fW, K₁, K₂, hW, hK, Dd.isAmalgamIso D'⟩, ?_, Dd.vertexIso₁, Dd.vertexIso₂⟩
  unfold F112Convention
  intro hor x hx
  rcases hor with h1 | h2
  · exact h1 hx
  · exfalso
    have hε : ε₁ ∈ centerOf (G₁ ⊓ G₂) :=
      ⟨G.ε₁_mem_inf, Subgroup.mem_centralizer_iff.2 fun t ht => G.v₁.ε_central t ht.1⟩
    have hεc : ε₁ ∈ Subgroup.centralizer (G₂ : Set D) := h2 hε
    exact G.v₁.ε_ne (central_trivial h G.ε₁_mem_inf (fun g hg => G.v₁.ε_central g hg)
      (fun g hg => Subgroup.mem_centralizer_iff.1 hεc g hg))

end CFSG.Quasithin.F6.GoldAmS
