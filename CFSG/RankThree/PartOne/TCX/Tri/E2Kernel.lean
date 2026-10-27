module

public import CFSG.RankThree.PartOne.TCX.Tri.E2Frame

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Kernel


theorem tri_kernel_e2 {f : ℕ} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ f + 1)
    (L : Type) [Field L] [CharP L 2] [IsAlgClosed L]
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hbT : rootDiagUnit TwistTag.D4.tag b ∈
      twistedTorusOf (triNeg L) (twistHom TwistTag.D4 L (iterateFrobenius L 2 f)))
    (hbo : orderOf (rootDiagUnit TwistTag.D4.tag b) = p) :
    rootCharKernel b = ∅ ∨
      (∃ w ∈ relWeylTwist TwistTag.D4, ∀ α, α ∈ rootCharKernel b ↔
        ∃ β ∈ threeRootSet d4Qr₁ d4Qr₂ d4Qr₃, α = w • β) ∨
      (∃ w ∈ relWeylTwist TwistTag.D4, ∀ α, α ∈ rootCharKernel b ↔
        ∃ β ∈ ({Pi.single i2 1, -Pi.single i2 1} :
          Set (Fin TwistTag.D4.tag.rank → ℤ)), α = w • β) := by
  classical
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  have hbap := CFSG.RankThree.Chevalley.pow_eq_one_of_orderOf_rootDiagUnit hbo
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbo
  have hbfix : b ∈ fixedCharTuples d4QM Fr := by
    have hh' := hbT
    rw [hFrdef, triNeg_twistedTorus] at hh'
    obtain ⟨b', hb', hbb'⟩ := hh'
    have : b' = b := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) hbb'
    exact this ▸ hb'
  obtain ⟨hb1', hb3'⟩ := d4Q_eq_of_pow_eq_one hFr hpq hbfix hbap
  have hAB : ¬ (b i0 = 1 ∧ b i2 = 1) := by
    rintro ⟨h0, h2⟩
    apply hb1
    funext j
    fin_cases j
    · exact h0
    · rw [show (⟨1, by decide⟩ : Fin TwistTag.D4.tag.rank) = i1 from rfl, hb1', h0]
      rfl
    · exact h2
    · rw [show (⟨3, by decide⟩ : Fin TwistTag.D4.tag.rank) = i3 from rfl, hb3', h0]
      rfl
  rcases rootCharKernel_cases (a := b) (A := b i0) (B := b i2) rfl hb1' rfl hb3' hp hp3
    (hbap i0) (hbap i2) hAB with hempty | ⟨α, hαr, -, hker⟩
  · exact Or.inl hempty
  · right
    obtain ⟨w, hw, a₀, hdiag, -, -⟩ := (diagram_root_orbit_reduction TwistTag.D4).1 α hαr
    have hsurv_gen : ∀ S₀ : Set (Fin TwistTag.D4.tag.rank → ℤ),
        (∀ β, β ∈ S₀ ↔ ((∃ i ∈ TwistTag.D4.orbit a₀,
            (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = β) ∨
          (∃ i ∈ TwistTag.D4.orbit a₀,
            (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = -β))) →
        ∀ α', α' ∈ rootCharKernel b ↔ ∃ β ∈ S₀, α' = w • β := by
      intro S₀ hS₀ α'
      rw [hker, hdiag]
      simp only [Set.mem_union, Set.mem_neg, Finset.mem_coe, Finset.mem_image]
      constructor
      · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, h⟩)
        · exact ⟨_, (hS₀ _).2 (Or.inl ⟨i, hi, rfl⟩), rfl⟩
        · refine ⟨-Pi.single i 1, (hS₀ _).2 (Or.inr ⟨i, hi, by rw [neg_neg]⟩), ?_⟩
          rw [smul_neg, h, neg_neg]
      · rintro ⟨β, hβ, rfl⟩
        rcases (hS₀ β).1 hβ with ⟨i, hi, rfl⟩ | ⟨i, hi, h⟩
        · exact Or.inl ⟨i, hi, rfl⟩
        · right
          refine ⟨i, hi, ?_⟩
          rw [h, smul_neg]
    rcases (show a₀ = ⟨0, by decide⟩ ∨ a₀ = ⟨1, by decide⟩ by fin_cases a₀ <;> simp) with
      rfl | rfl
    · exact Or.inl ⟨w, hw, hsurv_gen _ fun β => by
        rw [d4Q_orbit_zero]
        exact (d4Q_S₀_zero β).symm⟩
    · exact Or.inr ⟨w, hw, hsurv_gen _ fun β => by
        rw [d4Q_orbit_one]
        exact (d4Q_S₀_one β).symm⟩

end Kernel

end CFSG.RankThree.PartOne.TCX.Tri
