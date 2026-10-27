module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Datum
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGResE6DepRank
import CFSG.LocalAnalysis.StandardType.GGTBRowDCartan

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem

theorem ggR1AD_det
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag} {n f : ℕ}
    (ht : (t = .PSL ∧ ¬ p ∣ n) ∨ (t = .POmegaPlus ∧ 3 ≤ n)) :
    ∀ C : Matrix (Fin (ggU t n f).D.rank) (Fin (ggU t n f).D.rank) ℤ,
      GGIntCartan (coxeterMatrix (ggU t n f).D.isFiniteType) C → ((C.det : ℤ) : ZMod p) ≠ 0 := by
  rcases ht with ⟨rfl, hpn⟩ | ⟨rfl, hn⟩
  · have hn0 : n ≠ 0 := fun h => hpn (h ▸ dvd_zero p)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    change ∀ C : Matrix (Fin m) (Fin m) ℤ,
      GGIntCartan (coxeterMatrix (SpecialLinear.isFiniteType_A m)) C →
        ((C.det : ℤ) : ZMod p) ≠ 0
    intro C hC
    have h1 : GGIntCartan (CoxeterMatrix.A m) (CartanMatrix.A m) := ggIntCartan_A m
    have hM : coxeterMatrix (SpecialLinear.isFiniteType_A m) = CoxeterMatrix.A m :=
      coxeterMatrix_eq_of_ggIntCartan (SpecialLinear.isFiniteType_A m) h1
    rw [hM] at hC
    have hle : ∀ i j : Fin m, i ≠ j → CoxeterMatrix.A m i j ≤ 3 := by
      intro i j hij
      rw [TauCeti.coxeterMatrixA_apply]
      split_ifs <;> omega
    have hCA : C = CartanMatrix.A m := GGIntCartan.eq_of_le_three hC h1 hle
    rw [hCA, CartanMatrix.A_det]
    have hcast : (((m : ℤ) + 1 : ℤ) : ZMod p) = ((m + 1 : ℕ) : ZMod p) := by
      push_cast
      ring
    rw [hcast]
    exact fun h => hpn ((ZMod.natCast_eq_zero_iff (m + 1) p).mp h)
  · have hU : ggU .POmegaPlus n f =
        ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
          Spin.plusDatum n (GaloisField 2 f) hn⟩ := by
      simp only [ggU, lieUniversal, hn, ↓reduceDIte]
    rw [hU]
    change ∀ C : Matrix (Fin n) (Fin n) ℤ,
      GGIntCartan (coxeterMatrix (Spin.isFiniteType_cartanD n)) C →
        ((C.det : ℤ) : ZMod p) ≠ 0
    intro C hC
    have h1 : GGIntCartan (ggCoxeterMatrixD n) (CartanMatrix.D n) := ggIntCartan_D n
    have hM : coxeterMatrix (Spin.isFiniteType_cartanD n) = ggCoxeterMatrixD n := by
      refine coxeterMatrix_eq_of_ggIntCartan (Spin.isFiniteType_cartanD n) ?_
      rw [Spin.cartanD_eq]
      exact h1
    rw [hM] at hC
    have hle : ∀ i j : Fin n, i ≠ j → ggCoxeterMatrixD n i j ≤ 3 := by
      intro i j hij
      rw [ggCoxeterMatrixD_apply]
      split_ifs <;> omega
    have hCD : C = CartanMatrix.D n := GGIntCartan.eq_of_le_three hC h1 hle
    rw [hCD]
    exact ggCartanD_det_ne_zero hp2 (by omega)

end CFSG.StandardType

end
