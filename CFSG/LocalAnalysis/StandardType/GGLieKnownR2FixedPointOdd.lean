module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Filtration
public import CFSG.GroupTheory.CoprimeCosetFixed

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Open
open scoped commutatorElement

theorem noCentral_of_fixedPoint_odd {X : Type} [Group X] [Finite X] {K R : Subgroup X} {h : X}
    (hodd : Odd (orderOf h)) (hhN : h ∈ K ⊓ Subgroup.normalizer (R : Set X))
    (hfix : ∀ y ∈ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set X)), h * y = y * h → y ∈ R) :
    GGRootNoCentralAt K R := by
  intro A B' hRA hAB hBp hNA hNB hcomm
  intro b hb
  have hA2 : IsPGroup 2 A :=
    ((GGRootNorm.isPGroup_pCoreOf (K ⊓ Subgroup.normalizer (R : Set X))).to_le
      (hAB.trans hBp))
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  have hcop : Nat.Coprime (orderOf h) (Nat.card A) := by
    rw [hk]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp
    · exact (Nat.coprime_pow_right_iff hkpos _ _).mpr hodd.coprime_two_right
  have hbh : ⁅b, h⁆ ∈ A := hcomm (Subgroup.commutator_mem_commutator hb hhN)
  have hbN : b ∈ K ⊓ Subgroup.normalizer (R : Set X) :=
    GGRootNorm.pCoreOf_le _ (hBp hb)
  have hhnorm : h ∈ Subgroup.normalizer (A : Set X) := hNA hhN
  have hbnorm : b⁻¹ ∈ Subgroup.normalizer (A : Set X) := inv_mem (hNA hbN)
  have hN : ∀ n ∈ A, h * n * h⁻¹ ∈ A := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp hhnorm n).mp hn
  have hg : b⁻¹ * (h * b * h⁻¹) ∈ A := by
    have hconj : b⁻¹ * ⁅b, h⁆⁻¹ * b ∈ A := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp hbnorm ⁅b, h⁆⁻¹).mp (A.inv_mem hbh)
    have e : b⁻¹ * (h * b * h⁻¹) = b⁻¹ * ⁅b, h⁆⁻¹ * b := by
      simp only [commutatorElement_def]
      group
    rwa [e]
  obtain ⟨n, hnA, hnh⟩ := CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime A hN hg hcop
  have hyh : h * (b * n) = (b * n) * h := by
    calc h * (b * n) = (h * (b * n) * h⁻¹) * h := by group
      _ = (b * n) * h := by rw [hnh]
  have hyQ : b * n ∈ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set X)) :=
    Subgroup.mul_mem _ (hBp hb) (hBp (hAB hnA))
  have hyR : b * n ∈ R := hfix _ hyQ hyh
  have : b = (b * n) * n⁻¹ := by group
  rw [this]
  exact A.mul_mem (hRA hyR) (A.inv_mem hnA)

end CFSG.StandardType.LieKnownR2
