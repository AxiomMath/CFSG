module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBlockHubDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m N : ℕ} {G : Type} [Group G]
  {H : Subgroup G}

namespace QTwoCanonBlocks

theorem blk_le_of_swaps (B : QTwoCanonBlocks K m N H) {E : Subgroup G}
    (hswap : ∀ i j : Fin N, (j : ℕ) = (i : ℕ) + 1 → B.blk {i, j} ≤ E) {I₀ : Finset (Fin N)}
    (hI₀ : I₀.card = 4) (h₀ : B.blk I₀ ≤ E) {I : Finset (Fin N)} (hI : I.card = 4) :
    B.blk I ≤ E := by
  have hN : N ≠ 0 := by
    intro hN
    have hle := Finset.card_le_univ I₀
    rw [hI₀, hN, Fintype.card_fin] at hle
    omega
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := Nat.exists_eq_add_one_of_ne_zero hN
  have hgen : ∀ σ : Equiv.Perm (Fin (M + 1)),
      σ ∈ Submonoid.closure (Set.range fun k : Fin M => Equiv.swap k.castSucc k.succ) →
      ∀ J : Finset (Fin (M + 1)), J.card = 4 → B.blk J ≤ E →
        B.blk (J.map σ.toEmbedding) ≤ E := by
    intro σ hσ
    induction hσ using Submonoid.closure_induction with
    | mem σ hσ =>
      obtain ⟨k, rfl⟩ := hσ
      intro J hJ hJle
      have hk : ((k.succ : Fin (M + 1)) : ℕ) = ((k.castSucc : Fin (M + 1)) : ℕ) + 1 := by
        simp
      obtain ⟨s, hsB, hsmap⟩ := B.swap k.castSucc k.succ hk
      have hsE : s ∈ E := hswap k.castSucc k.succ hk hsB
      have hconj : E.map (MulAut.conj s).toMonoidHom = E :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hsE)
      calc
        B.blk (J.map (Equiv.swap k.castSucc k.succ).toEmbedding)
            = (B.blk J).map (MulAut.conj s).toMonoidHom :=
              (hsmap J (by omega) (by omega)).symm
        _ ≤ E.map (MulAut.conj s).toMonoidHom := Subgroup.map_mono hJle
        _ = E := hconj
    | one =>
      intro J _ hJle
      have hone : (1 : Equiv.Perm (Fin (M + 1))) = Equiv.refl (Fin (M + 1)) := rfl
      rw [hone, Equiv.refl_toEmbedding, Finset.map_refl]
      exact hJle
    | mul σ τ hσ hτ ihσ ihτ =>
      intro J hJ hJle
      rw [Equiv.Perm.mul_def, Equiv.trans_toEmbedding, ← Finset.map_map]
      exact ihσ (J.map τ.toEmbedding) (by simpa using hJ) (ihτ J hJ hJle)
  have htop := Equiv.Perm.mclosure_swap_castSucc_succ M
  obtain ⟨σ, hσmap⟩ := Equiv.Perm.exists_map_finset_eq I₀ I (hI₀.trans hI.symm)
  rw [← hσmap]
  exact hgen σ (by rw [htop]; exact Submonoid.mem_top σ) I₀ hI₀ h₀

end QTwoCanonBlocks

end CFSG.StandardType.QTwo

end
