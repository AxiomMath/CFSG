module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDCommute
public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueToralA

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckCM_lifts_PSL
    {X : Type} [Group X] [Finite X] {m f : ℕ} {ψ : (ggU .PSL (m + 1) f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (h : RCKCompConfig .PSL (m + 1) f ψ p G₀ A B₁ D J L K e)
    (hID : ∀ a ∈ A, GGPsiInnerDiag (ggU .PSL (m + 1) f).D ψ a) :
    (∀ a ∈ A, ∃ s : GL (Fin (m + 1)) (GaloisField 2 f),
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ s a) ∧
    ∀ a ∈ A, ∀ a' ∈ A, ∀ s s' : GL (Fin (m + 1)) (GaloisField 2 f),
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ s a →
        IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' a' → Commute s s' := by
  unfold RCKCompConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6, heD, he1, hKcomp, hJK, hOddK⟩
  have hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hGG.2.1.2
  have hadm : CFSG.Open.StatedLieAdmissible .PSL (m + 1) 2 f := hGG.1.1
  have hrange : ψ.range = G₀ := hGG.2.1.1
  have hf : 1 ≤ f := hadm.2.1
  have hAN : A ≤ Subgroup.normalizer (ψ.range : Set X) := by rwa [hrange]
  constructor
  · intro a ha
    exact exists_isGLLift_PSL m (GaloisField 2 f) ψ hker (hAN ha) (hID a ha)
  · intro a ha a' ha' s s' hs hs'
    have h4 : p ^ 4 ≤ Nat.card A := le_trans hp4 (Subgroup.card_le_of_le hB1A)
    have hHN : p ∣ 2 ^ f - 1 →
        A ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ ∧
          p ^ ((m + 1) - 3) ≤ Nat.card A := by
      intro hpdiv
      constructor
      · rw [hrange]
        exact hAc
      · by_cases hm : m = 0
        · subst hm
          simp
          exact Nat.card_pos
        · have hm1 : 1 ≤ m := by omega
          have hψ'mem : ∀ x, ψ x ∈ A ⊔ G₀ := fun x => by
            have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
            rw [hrange] at hx
            exact Subgroup.mem_sup_right hx
          have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by
            rw [GaloisField.card 2 f (by omega : f ≠ 0)]
            exact hpdiv
          let ψ' : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X := ψ
          have hrank : m - 1 ≤ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) := by
            refine RootPlaneA.sub_one_le_twoLocalRank (G := ↥(A ⊔ G₀))
              (ψ := ψ'.codRestrict (A ⊔ G₀) hψ'mem) hp hpK hm1 ?_
            intro x hx
            have h1 : ψ' x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
            exact hker (MonoidHom.mem_ker.mpr h1)
          have hle_exp : (m + 1) - 3 ≤ m - 1 := by omega
          have hpow_le : p ^ ((m + 1) - 3) ≤ p ^ (m - 1) :=
            Nat.pow_le_pow_right hp.pos hle_exp
          have hpow_rank : p ^ (m - 1) ≤ p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) :=
            Nat.pow_le_pow_right hp.pos hrank
          exact le_trans hpow_le (le_trans hpow_rank hrank2)
    exact isGLLift_commute_PSL m f ψ hker hadm hp hp2 (B₁ := A) hAN hID hAel h4 hHN ha ha' hs hs'

end CFSG.StandardType.RCKRP
