module

public import CFSG.LocalAnalysis.StandardType.GGKG3Setup
public import CFSG.LocalAnalysis.StandardType.GGKG3ZE
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality

theorem k3_commute_torus
    {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 7) {z : ModGL .E6 L}
    (hz : z ∈ adjointGroup .E6 L) (hcomm : ∀ y ∈ k3Ex, Commute z (k3Diag ζ y)) :
    z ∈ torusGroup .E6 L := by
  have h7 : ζ ^ 7 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hfam : z ∈ familyCentralizer .E6 L
      (fun y : ↥k3Ex => k3Tor ζ (y : Fin 6 → ZMod 7)) := by
    rw [mem_familyCentralizer]
    refine ⟨hz, fun y => ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact (hcomm y y.2).eq.symm
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul .E6 L
    (fun y : ↥k3Ex => k3Tor ζ (y : Fin 6 → ZMod 7)) hfam
  have hw1 : w = 1 := by
    have hinv : w⁻¹ = 1 := by
      refine k3_ZE w⁻¹ fun y hy => ?_
      funext i
      have hchar := hw ⟨y, hy⟩ (Pi.single i 1 : Fin Tag.E6.rank → ℤ)
      rw [rootChar_k3Tor h7, rootChar_k3Tor h7] at hchar
      have hpair := k3Chi_injective hζ hchar
      have h1 := k3Star_apply w⁻¹ y i
      rw [inv_inv] at h1
      rw [h1, hpair]
      exact k3Pair_single y i
    exact inv_eq_one.mp hinv
  have hker : familyKernel (fun y : ↥k3Ex => k3Tor ζ (y : Fin 6 → ZMod 7)) =
      (∅ : Set (Fin Tag.E6.rank → ℤ)) := by
    refine Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_
    obtain ⟨hγr, hall⟩ := hγ
    refine k3_Ex_ne (k3_mem_k3Roots hγr) fun y hy => ?_
    have h1 : k3Chi ζ (k3Pair y γ) = 1 := by
      have h := hall ⟨y, hy⟩
      rw [rootChar_k3Tor h7] at h
      exact h
    exact k3Chi_injective hζ (by rw [h1, k3Chi_zero])
  have hmT : m ∈ torusGroup .E6 L := by
    have hm' : m ∈ torusGroup .E6 L ⊔
        rootSpan .E6 L (familyKernel (fun y : ↥k3Ex => k3Tor ζ (y : Fin 6 → ZMod 7))) := hm
    rw [hker] at hm'
    have hbot : rootSpan .E6 L (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  rw [hw1, canonicalRep_one, mul_one]
  exact hmT

end CFSG.StandardType.GGKG3
