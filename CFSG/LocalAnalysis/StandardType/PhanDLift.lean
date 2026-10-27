module

public import CFSG.ClassicalInvolution.Phan.PhanDn.WeakPhan
public import CFSG.LocalAnalysis.StandardType.PhanELiftOfFamily

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal
open CFSG.Timmesfeld (edgeD)

private theorem edgeD_of_lt_of_three {n : ℕ} (hn : 4 ≤ n) {i j : Fin n} (hij : i < j)
    (hMij : CFSG.StandardType.ggCoxeterMatrixD n i j = 3) : edgeD n i j := by
  rcases (ggCoxeterMatrixD_eq_three_iff hn i j).1 hMij with h | h
  · exact h
  · exact absurd hij (not_lt.2 (le_of_lt (edgeD_lt hn h)))

section Generic

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def PhanFamilyD.toPhanFamilyE {n : ℕ} (hn : 4 ≤ n) {Y : Type} [Group Y]
    (F : PhanFamilyD K p f n Y) :
    CFSG.ClassicalInvolution.Phan.PhanE.PhanFamilyE K p f
      (CFSG.StandardType.ggCoxeterMatrixD n) Y where
  ι := F.ι
  θ i j := if h : edgeD n i j then F.θ i j h else 1
  left i j hij hMij := by
    have hE : edgeD n i j := edgeD_of_lt_of_three hn hij hMij
    rw [dif_pos hE]
    exact F.left i j hE
  right i j hij hMij := by
    have hE : edgeD n i j := edgeD_of_lt_of_three hn hij hMij
    rw [dif_pos hE]
    exact F.right i j hE
  comm i j hMij a b := by
    obtain ⟨hij, h1, h2⟩ := (ggCoxeterMatrixD_eq_two_iff hn i j).1 hMij
    exact F.comm i j hij h1 h2 a b

@[simp] theorem toPhanFamilyE_ι {n : ℕ} (hn : 4 ≤ n) {Y : Type} [Group Y]
    (F : PhanFamilyD K p f n Y) :
    (F.toPhanFamilyE hn).ι = F.ι := rfl

theorem exists_phanFamilyE {n : ℕ} (hn : 4 ≤ n) (hK : Nat.card K = (p ^ f) ^ 2) {X : Type}
    [Group X] {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X}
    (hW : WeakPhanSL K p f (CFSG.StandardType.ggCoxeterMatrixD n) U W) :
    ∃ F : CFSG.ClassicalInvolution.Phan.PhanE.PhanFamilyE K p f
        (CFSG.StandardType.ggCoxeterMatrixD n) X,
      (∀ i, (F.ι i).range = U i) ∧ ∀ i, Function.Injective (F.ι i) := by
  obtain ⟨F, hrange, hinj, -⟩ := hW.exists_phanFamilyD hn hK
  exact ⟨F.toPhanFamilyE hn, by simpa only [toPhanFamilyE_ι] using hrange, hinj⟩

end Generic

theorem phanELiftAt_D {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ} (hn : 4 ≤ n) {Y : LieUniversal}
    (hY : CFSG.IsQuasisimple Y.K) :
    CFSG.ClassicalInvolution.Phan.PhanE.PhanELiftAt K f
      (CFSG.StandardType.ggCoxeterMatrixD n) Y :=
  CFSG.ClassicalInvolution.Phan.PhanE.phanELiftAt_of_family hK (by omega) hY
    (fun U W hW => exists_phanFamilyE hn hK hW)

theorem isQuasisimple_lieUniversal_POmegaPlus
    {n f : ℕ} (hn : 4 ≤ n) :
    CFSG.IsQuasisimple (lieUniversal .POmegaPlus n 2 f Nat.prime_two).K := by
  rw [show lieUniversal .POmegaPlus n 2 f Nat.prime_two =
      ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) (by omega : 3 ≤ n)⟩ from
    dite_eq_left (by omega : 3 ≤ n)]
  exact CFSG.LieType.Universal.Spin.isQuasisimple_spinGroup_quadPlus (by omega)

theorem isQuasisimple_lieUniversal_POmegaMinus
    {n f : ℕ} (hn : 4 ≤ n) :
    CFSG.IsQuasisimple (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K := by
  rw [show lieUniversal .POmegaMinus n 2 f Nat.prime_two =
      ⟨spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2), Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ from rfl]
  exact CFSG.LieType.Universal.Spin.isQuasisimple_spinGroup_quadMinus hn (minusCoeffs_irr 2 f)

@[expose] def PhanDUniversal :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2],
    Nat.card K = (2 ^ f) ^ 2 → 4 ≤ 2 ^ f → ∀ n : ℕ, 4 ≤ n →
      (Even n → ∃ S : CFSG.ClassicalInvolution.Phan.PhanE.PhanFamilyE K 2 f
          (CFSG.StandardType.ggCoxeterMatrixD n)
          (lieUniversal .POmegaPlus n 2 f Nat.prime_two).K, S.IsUniversal) ∧
      (Odd n → ∃ S : CFSG.ClassicalInvolution.Phan.PhanE.PhanFamilyE K 2 f
          (CFSG.StandardType.ggCoxeterMatrixD n)
          (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K, S.IsUniversal)

theorem phanDInput2_of_phanDUniversal
    (h : PhanDUniversal) : CFSG.ClassicalInvolution.Phan.PhanDInput2 := by
  intro K _ _ f _ hK hq n hn X _ U W hW
  obtain ⟨hEven, hOdd⟩ := h K f hK hq n hn
  constructor
  · intro hev
    obtain ⟨S, hS⟩ := hEven hev
    exact phanELiftAt_D hK hn
      (isQuasisimple_lieUniversal_POmegaPlus hn) ⟨S, hS⟩ U W hW
  · intro hodd
    obtain ⟨S, hS⟩ := hOdd hodd
    exact phanELiftAt_D hK hn
      (isQuasisimple_lieUniversal_POmegaMinus hn) ⟨S, hS⟩ U W hW

end CFSG.ClassicalInvolution.PhanDn

end
