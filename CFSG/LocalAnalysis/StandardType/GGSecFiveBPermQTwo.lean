module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSp
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
open scoped MatrixGroups

section Inputs


@[expose] def GGSecFiveBPermQTwoRecInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        B = Bs → GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLinLabel n p lab) p Bs L →
      ∀ (m : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermQTwoCell p Bs L 𝒦 n eta m K i0 →
        ∃ Ψ : SL(m + 2, ZMod 2) →* G, Function.Injective Ψ ∧ Ψ.range = L ⊔ K

theorem ggSecFiveBPermQTwoDataInput_of_rec (hJ : BMaxJoinInput)
    (hR : GGSecFiveBPermQTwoRecInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
        ¬ GGSecFiveTier1Region p B Bs x L D J →
        ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
          GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
        ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
          (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
          (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
          (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
            ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
          ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
          B = Bs → GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLinLabel n p lab) p Bs L →
        ∀ (m : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermQTwoCell p Bs L 𝒦 n eta m K i0 →
          GGSecFiveData p B x L D J := by
  intro G _ _ p B Bs x L D J 𝒦 hRt hT1 n e hP hn eta h𝒦 hLeta hRM hG0 hB hlab m K i0 hc
  have hLK : ggG0 p B x L D J = L ⊔ K :=
    ggG0_eq_sup_of_bCoordinateBlock hJ hRt e hP (by omega) hRM eta h𝒦 hLeta hc.2.2.1
      hc.2.2.2.2.2
  obtain ⟨Ψ, hΨ, hrange⟩ :=
    hR G p B Bs x L D J 𝒦 hRt hT1 n e hP hn eta h𝒦 hLeta hRM hG0 hB hlab m K i0 hc
  have hm : 6 ≤ m := by rcases hc.2.1 with h | h <;> omega
  let φ : GaloisField 2 1 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  let μ : SL(m + 2, GaloisField 2 1) →* SL(m + 2, ZMod 2) :=
    Matrix.SpecialLinearGroup.map φ.toRingHom
  have hμinj : Function.Injective μ := by
    intro A A' h
    apply Subtype.ext
    ext i j
    have h' := congrArg (fun X : SL(m + 2, ZMod 2) => (X : Matrix (Fin (m + 2)) (Fin (m + 2))
      (ZMod 2)) i j) h
    exact φ.injective (by simpa [μ] using h')
  have hμsurj : Function.Surjective μ := by
    intro A
    refine ⟨Matrix.SpecialLinearGroup.map φ.symm.toRingHom A, ?_⟩
    apply Subtype.ext
    ext i j
    simp [μ]
  let Φ : SL(m + 2, GaloisField 2 1) →* G := Ψ.comp μ
  have hΦrange : Φ.range = ggG0 p B x L D J := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hμsurj, Subgroup.map_top, hrange, hLK]
  have hadm : StatedLieAdmissible .PSL (m + 2) 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, fun h => by simp at h; omega, fun h => by simp at h⟩
  refine Or.inr (Or.inr ⟨.PSL, m + 2, 1, ggSecFivePres_of_psi_PSL hadm ?_ Φ ?_ hΦrange⟩)
  · simp only [bnRank]
    omega
  · intro k hk
    have hk' : Ψ (μ k) = Ψ (μ 1) := by
      rw [map_one, map_one]
      exact hk
    rw [hΨ.comp hμinj hk']
    exact Subgroup.one_mem _

end Inputs

end CFSG.StandardType

end
