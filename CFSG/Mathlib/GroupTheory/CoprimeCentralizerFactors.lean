module

public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.GroupTheory

open CFSG.SignalizerFunctor.Helpers

theorem le_of_coprime_centralizer_factors {G : Type*} [Group G] [Finite G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {E F Y O H : Subgroup G}
    (hE : IsPGroup p E) (hF : IsPGroup q F)
    (hEY : E ≤ Subgroup.normalizer (Y : Set G))
    (hFcomm : F ≤ Subgroup.normalizer ((⁅Y,E⁆ : Subgroup G) : Set G))
    (hpY : Nat.Coprime p (Nat.card Y)) (hqY : Nat.Coprime q (Nat.card Y))
    (hCE : Y ⊓ Subgroup.centralizer (E : Set G) ≤ H)
    (hCF : ⁅Y,E⁆ ⊓ Subgroup.centralizer (F : Set G) ≤ H)
    (hmixed : ⁅⁅Y,E⁆,F⁆ ≤ O)
    (hOF : ⁅O,F⁆ ≤ H) : Y ≤ H := by
  let Z : Subgroup G := ⁅Y,E⁆
  have hZ_le_Y : Z ≤ Y := commutator_le_of_normalizing Y E hEY
  have hZcard : Nat.card Z ∣ Nat.card Y := Subgroup.card_dvd_of_le hZ_le_Y
  have hqZ : Nat.Coprime q (Nat.card Z) := Nat.Coprime.of_dvd_right hZcard hqY
  have hFcomm' : F ≤ Subgroup.normalizer (Z : Set G) := hFcomm
  have hYfac := coprime_normalized_commutator_factorization p hp E Y hE hEY hpY
  have hZfac := coprime_normalized_commutator_factorization q hq F Z hF hFcomm' hqZ
  have hZidem := coprime_normalized_commutator_idempotent q hq F Z hF hFcomm' hqZ
  have hU_le_H : ⁅Z,F⁆ ≤ H := by
    rw [← hZidem]
    exact (Subgroup.commutator_mono hmixed le_rfl).trans hOF
  have hZ_le_H : Z ≤ H := by
    calc
      Z = ⁅Z,F⁆ ⊔ (Z ⊓ Subgroup.centralizer (F : Set G)) := hZfac.symm
      _ ≤ H := sup_le hU_le_H hCF
  calc
    Y = ⁅Y,E⁆ ⊔ (Y ⊓ Subgroup.centralizer (E : Set G)) := hYfac.symm
    _ ≤ H := sup_le hZ_le_H hCE

end CFSG.GroupTheory
