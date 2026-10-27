module

public import CFSG.Milestones.ASVolI.A2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ASVolI.ChA

namespace P22w

variable {S S' M : Type} [Group S] [Group S'] [Group M]

theorem congr_symm_trans_congr (e : S ≃* S') (e₀ : S ≃* M) (θ : MulAut S) :
    MulAut.congr (e.symm.trans e₀) (MulAut.congr e θ) = MulAut.congr e₀ θ := by
  ext x
  simp

theorem congr_conj (e : S ≃* S') (s : S) : MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext x
  simp

theorem congr_symm_congr (e : S ≃* S') (θ : MulAut S) : MulAut.congr e.symm (MulAut.congr e θ) = θ := by
  ext x
  simp

end P22w

theorem uc22p22wi_isFieldAut_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {θ : MulAut S}
    (h : CFSG.ASVolI.ChA.IsFieldAut S θ) : CFSG.ASVolI.ChA.IsFieldAut S' (MulAut.congr e θ) := by
  rcases h with ⟨n, K, hF, hK, e₀, σ, hn, hθ⟩ | ⟨n, K, hF, hK, e₀, σ, hn, hθ⟩ |
    ⟨n, K, hF, hK, e₀, σ, hn, ho, hθ⟩ | ⟨n, K, hF, hK, e₀, σ, hn, hθ⟩ | ⟨a, K, hF, hK, e₀, σ, hn, hθ⟩ |
    ⟨n, K, hF, hK, e₀, σ, hn, hθ⟩ | ⟨n, K, hF, hK, σq, e₀, σ, hn, hq, ho, hθ⟩ | ⟨a, K, hF, hK, e₀, σ, hn, hθ⟩ |
    ⟨rfl, hs⟩
  · exact Or.inl ⟨n, K, hF, hK, e.symm.trans e₀, σ, hn, by rwa [P22w.congr_symm_trans_congr]⟩
  · exact Or.inr <| Or.inl
      ⟨n, K, hF, hK, e.symm.trans e₀, σ, hn, by rwa [P22w.congr_symm_trans_congr]⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨n, K, hF, hK, e.symm.trans e₀, σ, hn, ho, by rwa [P22w.congr_symm_trans_congr]⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨n, K, hF, hK, e.symm.trans e₀, σ, hn, by rwa [P22w.congr_symm_trans_congr]⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨a, K, hF, hK, e.symm.trans e₀, σ, hn, by rwa [P22w.congr_symm_trans_congr]⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨n, K, hF, hK, e.symm.trans e₀, σ, hn, by rwa [P22w.congr_symm_trans_congr]⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨n, K, hF, hK, σq, e.symm.trans e₀, σ, hn, hq, ho, by rwa [P22w.congr_symm_trans_congr]⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨a, K, hF, hK, e.symm.trans e₀, σ, hn, by rwa [P22w.congr_symm_trans_congr]⟩
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨map_one _, ?_⟩
    rcases hs with hs | hs | hs | hs | hs
    · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm hs)
    · exact Or.inr <| Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm hs)
    · exact Or.inr <| Or.inr <| Or.inl (CFSG.SectionRank.reeTitsModel_of_mulEquiv e.symm hs)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (hs.map e.symm.trans)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm hs)

theorem uc22p22wi_isInnDiagAut_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {ψ : MulAut S}
    (h : CFSG.ASVolI.ChA.IsInnDiagAut S ψ) : CFSG.ASVolI.ChA.IsInnDiagAut S' (MulAut.congr e ψ) := by
  rcases h with ⟨s, rfl⟩ | ⟨n, K, hF, hK, e₀, c, hn, hψ⟩ | ⟨n, K, hF, hK, e₀, c, hn, hψ⟩
  · exact Or.inl ⟨e s, (P22w.congr_conj e s).symm⟩
  · exact Or.inr <| Or.inl
      ⟨n, K, hF, hK, e.symm.trans e₀, c, hn, by rwa [P22w.congr_symm_trans_congr]⟩
  · exact Or.inr <| Or.inr
      ⟨n, K, hF, hK, e.symm.trans e₀, c, hn, by rwa [P22w.congr_symm_trans_congr]⟩

theorem uc22p22wi_isInnDiagFieldAut_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (θ : MulAut S) :
    CFSG.ASVolI.ChA.IsInnDiagFieldAut S' (MulAut.congr e θ) ↔ CFSG.ASVolI.ChA.IsInnDiagFieldAut S θ := by
  have fwd : ∀ {T T' : Type} [Group T] [Group T'] (f : T ≃* T') (φ : MulAut T),
      IsInnDiagFieldAut T φ → IsInnDiagFieldAut T' (MulAut.congr f φ) := by
    rintro T T' _ _ f φ ⟨ψ₁, ψ₂, h₁, h₂, rfl⟩
    exact ⟨MulAut.congr f ψ₁, MulAut.congr f ψ₂, uc22p22wi_isInnDiagAut_congr f h₁, uc22p22wi_isFieldAut_congr f h₂,
      map_mul _ _ _⟩
  refine ⟨fun h => ?_, fwd e θ⟩
  have := fwd e.symm _ h
  rwa [P22w.congr_symm_congr] at this

end CFSG.LocalAnalysis.UniquenessCase.UC22
