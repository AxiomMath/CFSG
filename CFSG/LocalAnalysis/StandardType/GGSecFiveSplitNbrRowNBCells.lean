module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneTransfer

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTorusFrame_of_signedElt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : GGTorusSignedElt p r R) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, -⟩ := hA
  obtain ⟨k, Θ, hk, hW, hS, hP, -⟩ :=
    exists_signedModel hp hp2 hI hZ h hψ hker hperf hAe hAI hr h3
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  obtain ⟨n₁, hn₁, he₁⟩ := hS i
  obtain ⟨n₂, hn₂, he₂⟩ := hP (Equiv.swap i j)
  have h4 : orderOf (SpCoord.sgnAut i * SpCoord.permAut (Equiv.swap i j) :
      MulAut (Fin k → Multiplicative (ZMod p))) = 4 := by
    have h := NbrFrameOne.orderOf_negAut_mul_swapAut hp hp2 hij
    rwa [NbrFrameOne.negAut, NbrFrameOne.swapAut, ← map_mul, MulEquiv.orderOf_eq] at h
  refine ⟨_, ⟨n₁, hn₁, hW n₁ hn₁, rfl, ?_⟩, _, ⟨n₂, hn₂, hW n₂ hn₂, rfl, ?_⟩, ?_⟩
  · rw [he₁]
    exact ggIsReflection_congr Θ (SpCoord.sgnAut_sq i) (SpCoord.card_fix_sgnAut hp hp2 i)
  · rw [he₂]
    exact ggIsReflection_congr Θ (SpCoord.permAut_swap_sq i j)
      (SpCoord.card_fix_permAut_swap hp hp2 hij)
  · rw [he₁, he₂, ← map_mul, MulEquiv.orderOf_eq, h4]

theorem largeEvenLabelAll_frame_symplectic {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpq⟩ := h
  dsimp only at ht hpq
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hlab.1 hpq
  have key : 2 ≤ l → ∀ {Q : LargeEvenRawCont}, LargeEvenRecipeSymplectic l (2 ^ n) false Q →
      LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧ ∃ r,
        GGTorusLift p r R ∧ ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R)
          (A : Subgroup (MulAut L')), GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
    rintro hl Q ⟨K, _, _, hK, hQ⟩
    have := charP_two_of_card hK
    have : NeZero l := ⟨by omega⟩
    have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
    exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
      TableBSymp.ggTorusLift_symplectic hp hp2 hpK (by omega),
      ggTorusFrame_of_signedElt hp hp2 TableBSymp.sp_I_subset_inn TableBSymp.center_spProj_eq_bot
        (SpModel.ggTorusSignedElt_sp hp hp2 hpK)⟩
  intro Q hQ
  rcases ht with rfl | rfl
  · exact key hlab.2.1 hQ
  · exact key hlab.2.1 hQ

theorem largeEvenLabelAll_frame_symplecticNs
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpq⟩ := h
  dsimp only at ht hpq
  have key : 2 ≤ l → ∀ {Q : LargeEvenRawCont}, LargeEvenRecipeSymplectic l (2 ^ n) false Q →
      LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧ ∃ r,
        GGTorusLift p r R ∧ ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R)
          (A : Subgroup (MulAut L')), GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
    rintro hl Q ⟨K, _, _, hK, hQ⟩
    have := charP_two_of_card hK
    have : NeZero l := ⟨by omega⟩
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
    have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpK
    have : Finite (LargeEvenSpGroup K l) := Subtype.finite
    have : Finite (LargeEvenProj (LargeEvenSpGroup K l)) :=
      Finite.of_equiv _ (TableBSymp.spProjEquivSp (K := K) (m := l)).symm.toEquiv
    have h2 : 2 ∣ Nat.card (LargeEvenProj (LargeEvenSpGroup K l)) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let i₀ : Fin l := ⟨0, by omega⟩
      rcases (TableBSymp.spRootGroup_isPGroup (K := K) i₀).card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) (TableBSymp.spRootGroup_ne_bot i₀)
      · exact h1.trans (Subgroup.card_subgroup_dvd_card _)
    exact ⟨K, inferInstance, inferInstance, hK, hQ, 0, TypeA.ggTorusLift_zero h2,
      ggTorusFrame_of_frameEltSC hp hp2 TableBSymp.center_spProj_eq_bot
        (fun _ hφ _ => TableBSymp.sp_I_subset_inn hφ) (ggCenterPrime_sp hp hp2)
        (ggTorusFrameEltSC_of_signedEltSC hp
          (ggSpNonsplitSignedEltInput_holds K l p hl hp hpK))⟩
  intro Q hQ
  rcases ht with rfl | rfl
  · exact key hlab.2.1 hQ
  · exact key hlab.2.1 hQ

end CFSG.StandardType

end
