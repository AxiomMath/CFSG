module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBBody
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
import CFSG.LocalAnalysis.StandardType.GGFrameClassicalNum
import CFSG.LocalAnalysis.StandardType.GGFrameClassicalAut
import CFSG.LocalAnalysis.StandardType.GGStdPosC24Signed
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpLift
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
import CFSG.LocalAnalysis.StandardType.GGKGARank
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly SpCoord Multiplicative


theorem frameTB_recipeSymplectic {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ∣ 2 ^ n + 1)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeSymplectic m (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic m (2 ^ n) false fun R _ I F => Q R I F ∧ ∀ r : ℕ,
      GGTorusReflGenW 3 r R I ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup 3 r R I L' ψ A →
            (FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) (m ^ 2) none ∧
              FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) ∧
            ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rwa [← Nat.card_eq_fintype_card])
  have : NeZero m := ⟨by omega⟩
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]; exact hn
  have hT := ggSpNonsplitTorusInput_holds K m 3 (by omega) Nat.prime_three hpq
  have hZ := TableBSymp.center_spProj_eq_bot (K := K) (m := m)
  have hI := TableBSymp.sp_I_subset_inn (K := K) (m := m)
  have hsc := ggTorusSCRank_sp (K := K) (by omega : 1 ≤ m) Nat.prime_three hpq
  have key : ∀ (r : ℕ) (L' : Type) [Group L'] [Finite L']
      (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K m)) (A : Subgroup (MulAut L')),
      GGTorusTBGroup 3 r (LargeEvenProj (LargeEvenSpGroup K m))
        (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m)) L' ψ A →
      (FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) (m ^ 2) none ∧
          FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) ∧
        ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S := by
    intro r L' _ _ ψ A hA
    obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hself⟩ := hA
    obtain ⟨k, Θ, hk, -, hS, hP, hN⟩ := exists_signedModelSC Nat.prime_three (by decide) hI hZ
      hT.2 hT.1 hψ hker hperf hAe hAI h3 hself
    have hlow : 3 ^ m ≤ Nat.card A := hsc L' ψ hψ hker hperf A hAe hAI hself
    have hup : Nat.card A ≤ 3 ^ m :=
      KGA.kga_card_le_sp Nat.prime_three (by decide) hψ hker hperf hAe hAI
    have hcard : Nat.card A = 3 ^ k := by
      rw [← Nat.card_congr Θ.toEquiv, Nat.card_fun, Nat.card_fin]
      congr 1
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card 3
    have hkm : k = m :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hcard.symm.trans (le_antisymm hup hlow))
    subst hkm
    refine ⟨frameNumIs_frameConn_of_signedPerm hk Θ
      (mem_ggAutomizer_iff_isSignedPerm Θ hS hP hN), ?_⟩
    obtain ⟨-, E, -, -, -, hE, hEc, -⟩ := TableBSymp.ggTorusLift_symplecticNs_of_lt (k := 2)
      Nat.prime_three (by decide) hpq (by omega) L' ψ hψ hker hperf
    refine ⟨E, fun y => ⟨1, Subtype.ext ?_⟩, TableB.not_isCyclic_of_card (by norm_num) hE.2
      (by rw [hEc])⟩
    simpa using hE.2 y.1 y.2
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun r => ⟨ggTorusReflGenW_of_signedEltSC
    Nat.prime_three (by decide) hZ (fun φ hφ _ => hI hφ) hT.2 hT.1, key r⟩⟩

theorem frameTBBody_sp {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hn : lab.n = 1)
    (ht : lab.tag = .B ∨ lab.tag = .C) : LargeEvenLabelAll lab (frameTBBody lab) := by
  obtain ⟨t, m, n⟩ := lab
  dsimp only at hn ht
  subst hn
  have hm : 3 ≤ m := by
    obtain ⟨-, h⟩ := hlab
    rcases ht with rfl | rfl <;>
    · obtain ⟨h2, h22⟩ := h
      dsimp only at h2 h22
      by_contra hlt
      have := h22 (by omega)
      omega
  intro Q hQ
  rcases ht with rfl | rfl <;> dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢ <;>
  · obtain ⟨K, i1, i2, hK, hQ', hP⟩ := frameTB_recipeSymplectic hm (by norm_num) hQ
    exact ⟨K, i1, i2, hK, hQ', fun r _ _ => hP r⟩

end CFSG.StandardType.FrameRoute

end
