module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsConj

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggDk_orbPair_of_member {G : Type} [Group G] {L Bs : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {t t' : M.Group}
    (ht : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (ht' : ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    (GGDSameSupp k (φ t) (φ t') →
      GGOrbPair L Bs 𝒦 M e (σ ⟨k - 2, by omega⟩) (σ ⟨k - 1, by omega⟩)) ∧
    (5 ≤ k → GGDDisjSupp k (φ t) (φ t') → ∀ {a b : Fin k}, a ≠ b →
      ggCoxeterMatrixD k a b = 2 → ¬ (a.val + 2 = k ∧ b.val + 1 = k) →
      ¬ (a.val + 1 = k ∧ b.val + 2 = k) → GGOrbPair L Bs 𝒦 M e (σ a) (σ b)) := by
  have key : ∀ {a b : Fin k} (w : ggWeylD k),
      w * (coxeterMatrix (isFiniteType_cartanD k)).simple a * w⁻¹ = φ t →
      w * (coxeterMatrix (isFiniteType_cartanD k)).simple b * w⁻¹ = φ t' →
      GGOrbPair L Bs 𝒦 M e (σ a) (σ b) := by
    intro a b w hwa hwb
    have hc : ∀ (c : Fin k) (u : M.Group),
        w * (coxeterMatrix (isFiniteType_cartanD k)).simple c * w⁻¹ = φ u →
          φ.symm w * M.simple (σ c) * (φ.symm w)⁻¹ = u := fun c u h => by
      apply φ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hφ, h]
    refine ⟨φ.symm w, X, hX, ?_, ?_⟩
    · rw [hc a t hwa]
      exact ht
    · rw [hc b t' hwb]
      exact ht'
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨w, hw1, hw2⟩ := ggDk_sameSupp_conj hk h
    exact key w hw1 hw2
  · intro h5 h a b hab h2 hf hf'
    obtain ⟨w, hw1, hw2⟩ := ggDk_disjSupp_conj h5 h hab h2 hf hf'
    exact key w hw1 hw2

end CFSG.StandardType

end
