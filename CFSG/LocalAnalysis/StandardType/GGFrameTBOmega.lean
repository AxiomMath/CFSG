module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBTw
public import CFSG.LocalAnalysis.StandardType.GGTBRowDSignedFrameSC
public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumD
import CFSG.LocalAnalysis.StandardType.GGFrameClassicalNum
import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidReflModel
import CFSG.LocalAnalysis.StandardType.GGNbrTableBOrthPlus
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEvenLabels
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameOmega
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameTransport
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
import CFSG.LocalAnalysis.StandardType.GGTwOmPlusHolds

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly SpCoord Multiplicative

theorem mem_ggAutomizer_iff_evenSignedPerm {L' : Type} [Group L'] {k : ℕ} (hk : 1 ≤ k)
    {A : Subgroup (MulAut L')} (Θ : (Fin k → Multiplicative (ZMod 3)) ≃* ↥A)
    (hd : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hev : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      (MulAut.congr Θ).symm (ggConjAut A hn) ∈ evenSignedPermSet k)
    (φ : MulAut ↥A) :
    φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A ↔
      (MulAut.congr Θ).symm φ ∈ evenSignedPermSet k := by
  set ΘA : MulAut (Fin k → Multiplicative (ZMod 3)) ≃* MulAut ↥A := MulAut.congr Θ with hΘA
  set H : Subgroup (MulAut L') := (MulAut.conj : L' →* MulAut L').range with hH
  have hfwd : ∀ χ : MulAut ↥A, χ ∈ ggAutomizer H A → ΘA.symm χ ∈ evenSignedPermSet k := by
    intro χ hχ
    rw [mem_ggAutomizer_iff] at hχ
    obtain ⟨g, hgH, hgN, hgapply⟩ := hχ
    rw [hH, MonoidHom.mem_range] at hgH
    obtain ⟨n, rfl⟩ := hgH
    have hEq : χ = ggConjAut A hgN := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [ggConjAut_apply, hgapply]
    rw [hEq]
    exact hev n hgN
  refine ⟨hfwd φ, fun hφe => ?_⟩
  have hind : ∀ u : MulAut (Fin k → Multiplicative (ZMod 3)),
      (∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = ΘA u) → u ∈ (ggAutomizer H A).comap ΘA.toMonoidHom := by
    rintro u ⟨n, hn, hEq⟩
    rw [Subgroup.mem_comap]
    change ΘA u ∈ ggAutomizer H A
    rw [← hEq]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have hsigned : IsSignedPerm ⇑(ΘA.symm φ) := by
    obtain ⟨π, ε, hε, -, hu⟩ := hφe
    exact ⟨π, ε, hε, hu⟩
  rcases OrthExcEven.mem_or_mul_mem_of_isSignedPerm
      (H := (ggAutomizer H A).comap ΘA.toMonoidHom) (fun i j hij => hind _ (hd i j hij))
      (fun a b _ => hind _ (hperm (Equiv.swap a b))) ⟨0, hk⟩ hsigned with hmem | hmem
  · rw [Subgroup.mem_comap] at hmem
    change ΘA (ΘA.symm φ) ∈ ggAutomizer H A at hmem
    rwa [MulEquiv.apply_symm_apply] at hmem
  · rw [Subgroup.mem_comap] at hmem
    change ΘA (ΘA.symm φ * sgnAut ⟨0, hk⟩) ∈ ggAutomizer H A at hmem
    have hodd := hfwd _ hmem
    rw [MulEquiv.symm_apply_apply] at hodd
    exact absurd hodd (mul_sgnAut_not_mem_evenSignedPermSet hφe ⟨0, hk⟩)

theorem frameTB_of_evenFrame {ℓ : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime 3 R) (hE : GGTorusEvenSignedPermEltSC 3 R fun k => k = ℓ)
    (hF : GGTorusOrthFrameSC 3 R ℓ) :
    FrameTBRow (ℓ * (ℓ - 1)) (some (4 * (ℓ - 2))) R I := by
  have hOf := ggTorusEvenSignedPermEltSCOf_of_orthFrameSC Nat.prime_three hF hE
  intro r
  refine ⟨ggTorusReflGenW_of_evenSignedPermEltSC Nat.prime_three (by decide) hI hZ hcp hE,
    fun L' _ _ ψ A hA => ?_⟩
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hsc⟩ := hA
  obtain ⟨k, Θ, hk3, hk, -, hd, hP, -, hN⟩ := OrthExcEven.exists_evenSignedPermModelSCOf
    Nat.prime_three (by decide) hI hZ hcp hOf hψ hker hperf hAe hAI h3 hsc
  have hkℓ : k = ℓ := hk
  subst hkℓ
  exact ⟨frameNumIs_frameConn_of_evenSignedPerm hk3 Θ
      (mem_ggAutomizer_iff_evenSignedPerm (by omega) Θ hd hP hN),
    exists_noncyclic_three_of_forall_conj hAe (le_trans (by norm_num) h3)
      (exists_mulAut_conj_of_mem hψ hker hperf (fun φ hφ _ => hI hφ) hAe hAI)⟩


theorem frameTB_omegaPlusFull {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hK : Nat.card K = 2 ^ 1) (hm : 4 ≤ m) (hme : Even m) :
    FrameTBRow (m * (m - 1)) (some (4 * (m - 2)))
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _) := by
  have hpq : 3 ∣ Nat.card K + 1 := by
    rw [hK]
    norm_num
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) Nat.prime_three (by decide)
    (by omega : 3 ≤ m)
  have hfin : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card (R := K) (η := Fin m ⊕ Fin m)]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hfrQ := HdRo7D.d_frameOmega_holds K (Fin m ⊕ Fin m → K) (TableBOrth.qPlusForm K m)
    (TableBOrth.nondegenerate_qPlusForm m) 3 Nat.prime_three (by decide) hpq m hfin hm
  have hF : GGTorusOrthFrameSC 3 (OrthRest.RPlus K m) m :=
    ggTorusOrthFrameSC_of_mulEquiv (OrthTorus.rPlusEquiv K (by omega)).symm hfrQ
  have hE := ggOrthEvenTorusInput_holds.1 K m 3 hm Nat.prime_three (Or.inr ⟨hme, hpq⟩)
  exact frameTB_of_evenFrame (fun _ h => h) hZ hcp hE hF

theorem frameTB_omegaMinusFull {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} {b c : K}
    (hK : Nat.card K = 2 ^ 1) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hm : 4 ≤ m)
    (hme : Even m) :
    FrameTBRow ((m + 1) * (m + 1 - 1)) (some (4 * (m + 1 - 2)))
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) (LargeEvenInnSet _) := by
  have hpq : 3 ∣ Nat.card K + 1 := by
    rw [hK]
    norm_num
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) Nat.prime_three (by decide)
    (by omega : 3 ≤ m) hbc
  have hfin : Module.finrank K (LargeEvenMinusIdx m → K) = 2 * (m + 1) := by
    rw [Module.finrank_fintype_fun_eq_card (R := K) (η := LargeEvenMinusIdx m)]
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    omega
  have hfrQ := HdRo7D.d_frameOmega_holds K (LargeEvenMinusIdx m → K)
    (TableBOrth.qMinusForm K m b c) (TableBOrth.nondegenerate_qMinusForm m hbc) 3
    Nat.prime_three (by decide) hpq (m + 1) hfin (by omega)
  have hF : GGTorusOrthFrameSC 3 (OrthRest.RMinus K m b c) (m + 1) :=
    ggTorusOrthFrameSC_of_mulEquiv (OrthTorus.rMinusEquiv K m b c).symm hfrQ
  have hE := ggOrthEvenTorusInput_holds.2 K m 3 b c hm hme hbc Nat.prime_three hpq
  exact frameTB_of_evenFrame (fun _ h => h) hZ hcp hE hF

theorem frameTBBody_omPlusFull {r : ℕ} (hr : 3 ≤ r) (hodd : Odd r) :
    LargeEvenLabelAll ⟨.D, r + 1, 1⟩ (frameTBBody ⟨.D, r + 1, 1⟩) := by
  have h0 : (r + 1) % 2 = 0 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  refine frameTBBody_of_row (N := (r + 1) * (r + 1 - 1)) (d := some (4 * (r + 1 - 2)))
    (by simp only [frameLabNum, frameTagNum, h0, ↓reduceIte]) ?_
  exact ggTwOmPlus_label_of_rec (f := 1)
    (P := FrameTBRow ((r + 1) * (r + 1 - 1)) (some (4 * (r + 1 - 2)))) hr fun K _ _ _ hK =>
    frameTB_omegaPlusFull hK (by omega) hodd.add_one

theorem frameTBBody_omMinusFull {r : ℕ} (hr : 4 ≤ r) (hev : Even r) :
    LargeEvenLabelAll ⟨.twD, r + 1, 1⟩ (frameTBBody ⟨.twD, r + 1, 1⟩) := by
  have h1 : (r + 1) % 2 = 1 := by
    obtain ⟨k, hk⟩ := hev
    omega
  refine frameTBBody_of_row (N := (r + 1) * (r + 1 - 1)) (d := some (4 * (r + 1 - 2)))
    (by simp only [frameLabNum, frameTagNum, h1, ↓reduceIte]) ?_
  exact ggTwOm_label_of_rec (f := 1)
    (P := FrameTBRow ((r + 1) * (r + 1 - 1)) (some (4 * (r + 1 - 2)))) (by omega)
    fun K _ _ _ hK b c hbc =>
    frameTB_omegaMinusFull (m := r + 1 - 1) hK hbc (by omega) (by simpa using hev)

end CFSG.StandardType.FrameRoute

end
