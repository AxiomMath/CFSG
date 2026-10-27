module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBTw
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
import CFSG.LocalAnalysis.StandardType.GGStdPosC13PermConv
import CFSG.LocalAnalysis.StandardType.GGFrameClassicalNum
import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1U
import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidReflModel

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly UCoord

theorem mem_ggAutomizer_iff_sumZeroPerm {L' : Type} [Group L'] {d : ℕ}
    {A : Subgroup (MulAut L')} (Θ : ↥(sumZero d 3) ≃* ↥A)
    (hperm : ∀ σ : Equiv.Perm (Fin d), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAutV σ))
    (hN : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ∃ π : Equiv.Perm (Fin d), ggConjAut A hn = MulAut.congr Θ (permAutV π))
    (φ : MulAut ↥A) :
    φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A ↔
      ∃ π : Equiv.Perm (Fin d), (MulAut.congr Θ).symm φ = permAutV π := by
  set H : Subgroup (MulAut L') := (MulAut.conj : L' →* MulAut L').range with hH
  constructor
  · intro hφ
    rw [mem_ggAutomizer_iff] at hφ
    obtain ⟨g, hgH, hgN, hgapply⟩ := hφ
    rw [hH, MonoidHom.mem_range] at hgH
    obtain ⟨n, rfl⟩ := hgH
    have hEq : φ = ggConjAut A hgN := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [ggConjAut_apply, hgapply]
    rw [hEq]
    obtain ⟨π, hπ⟩ := hN n hgN
    exact ⟨π, by rw [hπ, MulEquiv.symm_apply_apply]⟩
  · rintro ⟨π, hπ⟩
    obtain ⟨n, hn, hEq⟩ := hperm π
    have hφeq : φ = ggConjAut A hn := by
      rw [hEq, ← hπ, MulEquiv.apply_symm_apply]
    rw [hφeq]
    exact ggConjAut_mem_ggAutomizer (H := H) (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn

theorem frameTB_of_permElt {d : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} (hd : 3 ≤ d)
    (hZ : Subgroup.center R = ⊥) (hIp : GGOutdiagPrime 3 R I) (hcp : GGCenterPrime 3 R)
    (h : GGTorusPermEltSC 3 d R) :
    FrameTBRow (d * (d - 1) / 2) (some (2 * (d - 2))) R I := by
  intro r
  refine ⟨ggTorusReflGenW_of_permEltSC Nat.prime_three (by decide) hZ hIp hcp h,
    fun L' _ _ ψ A hA => ?_⟩
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hsc⟩ := hA
  obtain ⟨Θ, -, hP, hN⟩ :=
    exists_permModel Nat.prime_three hZ hIp hcp h hψ hker hperf hAe hAI h3 hsc
  exact ⟨frameNumIs_frameConn_of_sumZeroPerm hd Θ
      (mem_ggAutomizer_iff_sumZeroPerm Θ hP hN),
    exists_noncyclic_three_of_forall_conj hAe (le_trans (by norm_num) h3)
      (exists_mulAut_conj_of_mem hψ hker hperf hIp hAe hAI)⟩


theorem frameTBBody_suCoprime {m : ℕ} (hm : 3 ≤ m) (h3 : ¬ 3 ∣ m + 1) :
    LargeEvenLabelAll ⟨.twA, m, 1⟩ (frameTBBody ⟨.twA, m, 1⟩) := by
  refine frameTBBody_of_row (N := (m + 1) * (m + 1 - 1) / 2)
    (d := some (2 * (m + 1 - 2))) ?_ ?_
  · simp only [frameLabNum, frameTagNum]
    refine Prod.ext ?_ ?_
    · rw [Nat.add_sub_cancel, Nat.mul_comm m (m + 1)]
    · rw [show m + 1 - 2 = m - 1 by omega]
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
    have hdq : (m + 1, 2 ^ 1) ≠ (3, 2) := by
      rintro h
      have h1 : m + 1 = 3 := congrArg Prod.fst h
      omega
    have hZ := TableBUE.center_proj_eq_bot hK (by omega) hdq
    have hIp := InndiagSU.ggOutdiagPrime_unitary hK le_rfl (by omega) hdq
      Nat.prime_three (by norm_num) h3
    have hcp := StdSubRestU.ggCenterPrime_unitary hK le_rfl (by omega) hdq
      Nat.prime_three (by norm_num) h3
    have hmodel := UModel.ggTorusPermEltSC_unitary hK le_rfl (by omega)
      Nat.prime_three (by norm_num) (by norm_num) h3
    exact frameTB_of_permElt (d := m + 1) (by omega) hZ hIp hcp hmodel

end CFSG.StandardType.FrameRoute

end
