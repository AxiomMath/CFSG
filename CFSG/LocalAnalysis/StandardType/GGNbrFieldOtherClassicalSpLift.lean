module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpLiftModel
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

theorem ggTorusLift_symplecticNs_of_lt {K : Type} [Field K] [Finite K] [CharP K 2] {m k p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hk : k < m) :
    GGTorusLift p k (LargeEvenProj (LargeEvenSpGroup K m)) := by
  obtain ⟨Φ, Y, hΦ, hΦH, hYH, hY1, hY2, hΦY⟩ := exists_nsSpModelFin (K := K) hk
  obtain ⟨τ, X, hτH, hτs, hinv, hXH, hX1, hX2, hτX⟩ :=
    exists_matrixTorus_of_sl2Pi hp hp2 hpq (H := LargeEvenSpGroup K m) Φ Y hΦ hΦH hYH hY1 hY2
      hΦY
  exact ggTorusLift_of_matrixTorus hp hp2 τ hτH hτs hinv X hXH hX1 hX2 hτX

theorem ggTorusLift_symplecticNsTwo {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hm : 3 ≤ m) :
    GGTorusLift p 2 (LargeEvenProj (LargeEvenSpGroup K m)) :=
  ggTorusLift_symplecticNs_of_lt hp hp2 hpq hm

end TableBSymp

private theorem recipeSymplectic_innLiftNsTwo {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n + 1) (hl : 3 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ((∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift p 2 R) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    fun g => RecipeFieldSp.mem_conjImage_iff_inn.mpr ⟨g, rfl⟩,
    TableBSymp.ggTorusLift_symplecticNsTwo hp hp2 hpq hl⟩

theorem largeEvenLabelAll_innLift_spNsTwo {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift p 2 R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn⟩ := h
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h hl hpn <;> subst h <;>
    exact recipeSymplectic_innLiftNsTwo hp hp2 hpn hl hQ

end CFSG.StandardType

end
