module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOffSpCaseDefs
public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.WeakCT (blockSL2)
open scoped MatrixGroups

@[expose] def GGSecFiveBPermOmCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (f : ℕ)
    (K : Subgroup G) (i0 : Fin n) : Prop :=
  2 ≤ f ∧ K ∈ 𝒦 ∧
    (∃ ψ : SL(n, GaloisField 2 f) →* G,
      ψ.ker ≤ Subgroup.center SL(n, GaloisField 2 f) ∧ ψ.range = L) ∧
    Nonempty (↥K ≃*
      spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ∧
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0

@[expose] def GGSecFiveBPermQTwoCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (m : ℕ)
    (K : Subgroup G) (i0 : Fin n) : Prop :=
  p = 3 ∧ (m = 2 * n - 2 ∨ m = 2 * n - 1) ∧ K ∈ 𝒦 ∧
    (∃ ψ : SL(n, GaloisField 2 2) →* G,
      ψ.ker ≤ Subgroup.center SL(n, GaloisField 2 2) ∧ ψ.range = L) ∧
    Nonempty (↥K ≃* SL(m, ZMod 2)) ∧
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0

@[expose] def GGSecFiveBPermSUCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (a : ℕ)
    (K : Subgroup G) (i0 : Fin n) : Prop :=
  n = 4 ∧ 2 ≤ a ∧ p ∣ 2 ^ a - 1 ∧ K ∈ 𝒦 ∧
    (∃ ψ : SL(n, GaloisField 2 (2 * a)) →* G,
      ψ.ker ≤ Subgroup.center SL(n, GaloisField 2 (2 * a)) ∧ ψ.range = L) ∧
    Nonempty (↥K ≃*
      ↥(Unitary.SU (BorelTits.unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6)) ∧
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0

section Inputs


@[expose] def GGSecFiveBPermLinNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        B = Bs → GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLinLabel n p lab) p Bs L →
          (∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n),
              GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) ∨
            (∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n),
              GGSecFiveBPermOmCell p Bs L 𝒦 n eta f K i0) ∨
            (∃ (m : ℕ) (K : Subgroup G) (i0 : Fin n),
              GGSecFiveBPermQTwoCell p Bs L 𝒦 n eta m K i0) ∨
            ∃ (a : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSUCell p Bs L 𝒦 n eta a K i0

@[expose] def GGSecFiveBPermOmChartInput : Prop :=
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
      ∀ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermOmCell p Bs L 𝒦 n eta f K i0 →
        ∃ r : ℕ, n = r + 2 ∧ ∃ (σ : SL(r + 2, GaloisField 2 f) →* G)
          (κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
            (minusCoeffs 2 f).2) →* G),
          σ.ker ≤ Subgroup.center SL(r + 2, GaloisField 2 f) ∧ σ.range = L ∧
          Function.Injective κ ∧ κ.range = K ∧
          (∀ k : Fin r, (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) k.succ)).range =
            (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
              k.castSucc).map κ) ∧
          ∀ a ∈ (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range,
            ∀ b ∈ (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
              (Fin.last r)).map κ, a * b = b * a

@[expose] def GGSecFiveBPermSUDataInput : Prop :=
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
      ∀ (a : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSUCell p Bs L 𝒦 n eta a K i0 →
        GGSecFiveData p B x L D J

@[expose] def GGSecFiveBPermSURecInput : Prop :=
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
      ∀ (a : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSUCell p Bs L 𝒦 n eta a K i0 →
        ∃ Ψ : (ggU .PSU 8 a).K →* G,
          Ψ.ker ≤ Subgroup.center (ggU .PSU 8 a).K ∧ Ψ.range = L ⊔ K

end Inputs

end CFSG.StandardType

end
