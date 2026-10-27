module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransfer

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly

theorem ggStdSubTwoTorusNormSmallR_three_of_odd {r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (hcenR : Subgroup.center R = ⊥)
    (h : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Odd (Nat.card ψ.ker) →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
        3 ^ r ≤ Nat.card A → 3 ^ 3 ≤ Nat.card A → GGNormTwoR ψ A →
        ∀ a ∈ A, a ≠ 1 → IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) →
          (∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)) →
          GGStdSubSmallHyp 3 A a → False) :
    GGStdSubTwoTorusNormSmallR 3 r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hnorm a ha ha1 hcomp hcent hsm _
  exfalso
  have hZ2 : USixTwo.zTwo L' ≤ ψ.ker := USixTwo.zTwo_le_ker hψ hcenR
  have hinj := USixTwo.qAutHom_injective hperf
  have hcard : Nat.card (A.map (USixTwo.qAutHom L')) = Nat.card A :=
    Subgroup.card_map_of_injective hinj
  have hAb : IsElemAbelian 3 (A.map (USixTwo.qAutHom L')) := TableB.isElemAbelian_map hA _
  refine h (USixTwo.Qt L') (USixTwo.qLift ψ hZ2) (USixTwo.qLift_surjective hZ2 hψ)
    (USixTwo.qLift_ker_le_center hZ2 hker) (USixTwo.qmk_perfect hperf)
    (USixTwo.qLift_odd_ker hZ2 hker) (A.map (USixTwo.qAutHom L')) hAb ?_
    (by rw [hcard]; exact hr) (by rw [hcard]; exact h3) ?_ _ ⟨a, ha, rfl⟩ ?_
    (USixTwo.isComponentOf_layer_down USixTwo.qmk_surjective USixTwo.qmk_ker_le_center
      (USixTwo.qAutHom_compat a) hcomp) ?_ (USixTwo.smallHyp_down hperf hA ha hsm)
  · rintro _ ⟨a', ha', rfl⟩
    obtain ⟨φ, hφ, hφa⟩ := hAI a' ha'
    exact ⟨φ, hφ, USixTwo.qLift_qAut hZ2 a' φ hφa⟩
  ·
    obtain ⟨U, hU1, hU2, hUA⟩ := hnorm
    refine ⟨U, hU1, hU2, ?_⟩
    rintro _ ⟨a', ha', rfl⟩ lb hlb
    obtain ⟨l, rfl⟩ := USixTwo.qmk_surjective lb
    rw [USixTwo.qLift_mk] at hlb
    rw [USixTwo.qAutHom_compat, USixTwo.qLift_mk]
    exact hUA a' ha' l hlb
  · intro h1
    exact ha1 (hinj (by rw [h1, map_one]))
  · rintro _ ⟨a', ha', rfl⟩
    exact (USixTwo.cent_iff hperf a a').mp (hcent a' ha')

end CFSG.StandardType.SmallExc

end
