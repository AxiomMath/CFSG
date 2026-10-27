module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitLabelTwo
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrthA
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrthE
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedTits

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem

private theorem false_of_big_label {ι κ : Type} {M : CoxeterMatrix ι} {N : CoxeterMatrix κ}
    {σ : κ ≃ ι} (hM : M = N.reindex σ) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {a b : κ}
    (hab : a ≠ b) (h4 : 3 < N.M a b) : False := by
  have h := h3 (σ a) (σ b) (σ.injective.ne hab)
  rw [hM, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
  omega

private theorem false_of_B_label_four {ι : Type} {M : CoxeterMatrix ι} {n : ℕ} {σ : Fin n ≃ ι}
    (hn : 2 ≤ n) (hM : M = (CoxeterMatrix.B n).reindex σ)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) : False := by
  have hne : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_mk] at this
    omega
  refine false_of_big_label hM h3 hne ?_
  rw [show (CoxeterMatrix.B n).M ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ = 4 by
    simp [CoxeterMatrix.B, Matrix.of_apply, hne]]
  omega

private theorem orth_conj_of_not_D {ι : Type} {M : CoxeterMatrix ι} (hW : GGIsWeylMatrix M)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hD : ¬ ∃ (k : ℕ) (σ : Fin k ≃ ι), 4 ≤ k ∧ M = (ggCoxeterMatrixD k).reindex σ)
    {t t' : M.Group} (ht : ∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹)
    (ht' : ∃ (w : M.Group) (i : ι), t' = w * M.simple i * w⁻¹) (hne : t ≠ t')
    (hcomm : t * t' = t' * t) {i j : ι} (h2 : M.M i j = 2) :
    ∃ w : M.Group, w * M.simple i * w⁻¹ = t ∧ w * M.simple j * w⁻¹ = t' := by
  rcases hW with ⟨n, σ, -, hA | ⟨hn, hB⟩ | ⟨hn, hDn⟩⟩ | ⟨σ, hE⟩ | ⟨σ, hE⟩ | ⟨σ, hE⟩ | ⟨σ, hF⟩ |
      ⟨σ, hG⟩
  · exact ggOrth_conj_A hA ht ht' hne hcomm h2
  · exact (false_of_B_label_four hn hB h3).elim
  · exact absurd ⟨n, σ, hn, hDn⟩ hD
  · exact ggOrth_conj_E6 hE ht ht' hne hcomm h2
  · exact ggOrth_conj_E7 hE ht ht' hne hcomm h2
  · exact ggOrth_conj_E8 hE ht ht' hne hcomm h2
  · exact (false_of_big_label hF h3 (a := 1) (b := 2) (by decide) (by decide)).elim
  · exact (false_of_big_label hG h3 (a := 0) (b := 1) (by decide) (by decide)).elim

theorem ggOrbPair_of_label_two
    (hpos : GGSecFiveKGPosInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {i j : ι} (h2 : M.M i j = 2)
    (hD : ¬ ∃ (k : ℕ) (σ : Fin k ≃ ι), 4 ≤ k ∧ M = (ggCoxeterMatrixD k).reindex σ) :
    GGOrbPair L Bs 𝒦 M e i j := by
  obtain ⟨tg, n, f, ψ, hadm, hrk, -, -, htag, -, ε, hεr, -⟩ :=
    hpos G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres h3 L (Or.inl rfl) hsplit
  obtain ⟨a, b, hab, hab2⟩ := ggWeylMatrix_exists_label_two (ggTag_weylMatrix htag hadm).1 (by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, show (ggU tg n f).D.rank = bnRank tg n from
      lieUniversal_rank_eq_bnRank tg n 2 f Nat.prime_two hadm hrk]
    exact hrk)
  have hτ : ∀ c, ∃ τ : M.Group, (∃ (w : M.Group) (k : ι), τ = w * M.simple k * w⁻¹) ∧
      ((e τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((ε ((coxeterMatrix (ggU tg n f).D.isFiniteType).simple c) : ↥(ggAutomizer L Bs)) :
          MulAut ↥Bs) := fun c => by
    obtain ⟨w, k, hwk⟩ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) (ε _).2) (hεr c)
    exact ⟨_, ⟨w, k, rfl⟩, hwk.symm⟩
  obtain ⟨t₁, ht₁, he₁⟩ := hτ a
  obtain ⟨t₂, ht₂, he₂⟩ := hτ b
  have hsi : Function.Injective (coxeterMatrix (ggU tg n f).D.isFiniteType).simple := by
    rw [← CoxeterMatrix.toCoxeterSystem_simple]
    exact CoxeterSystem.simple_injective _
  have hne : t₁ ≠ t₂ := fun h =>
    hab (hsi (ε.injective (Subtype.ext (by rw [← he₁, ← he₂, h]))))
  have hcomm : t₁ * t₂ = t₂ * t₁ := by
    have h1 := congrArg (fun g => ((ε g : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
      (ggSimplyLaced_simple_comm hab2)
    simp only [map_mul, Subgroup.coe_mul, ← he₁, ← he₂] at h1
    exact e.injective (Subtype.ext (by simp only [map_mul, Subgroup.coe_mul, h1]))
  obtain ⟨w, hw₁, hw₂⟩ := orth_conj_of_not_D hpres.1 h3 hD ht₁ ht₂ hne hcomm h2
  refine ⟨w, L, Or.inl rfl, ?_, ?_⟩
  · rw [hw₁, he₁]
    exact (ε _).2
  · rw [hw₂, he₂]
    exact (ε _).2

end CFSG.StandardType

end
