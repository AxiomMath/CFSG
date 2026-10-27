module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Defs
public import CFSG.Blueprint.Catalog
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.Models.PGL
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Star863

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
  (mem_centralizer_of_isSylowOf_of_pow_mem_centralizer)

theorem fixOmega_of_lieModel_PSU_five {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSU 5 2 2) {S : Subgroup X} (hS : IsPGroup 3 S)
    (hSi : ¬ 3 ∣ S.index) (hSc : IsMulCommutative S) : FixOmega X S := by
  classical
  intro α hα hαS s hs hs3
  obtain ⟨k, hk⟩ := hα
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      (CFSG.Blueprint.LieModel.admissible hX) (MulEquiv.refl _))
  have h3 : ¬ 3 ∣ Nat.card (Outer X) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.RankThree.PartTwo.Sec4.outU54_holds
  have hdvd : orderOf (α : Outer X) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one])
  have hcop : Nat.Coprime (orderOf (α : Outer X)) (Nat.card (Outer X)) :=
    Nat.Coprime.coprime_dvd_left hdvd
      (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3))
  have hinner : α ∈ inner X := by
    rw [← QuotientGroup.eq_one_iff, ← orderOf_eq_one_iff]
    exact hcop.eq_one_of_dvd (orderOf_dvd_natCard _)
  obtain ⟨g, rfl⟩ := hinner
  have hnorm : g ∈ Subgroup.normalizer (S : Set X) := by
    refine Subgroup.mem_normalizer_fintype (fun y hy => ?_)
    simpa [MulAut.conj_apply] using hαS y hy
  have hpow : MulAut.conj (g ^ (3 ^ k)) = 1 := by
    rw [map_pow, hk]
  have hcentpow : g ^ (3 ^ k) ∈ Subgroup.centralizer (S : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun f : MulAut X => f y) hpow
    rw [MulAut.conj_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp (by simpa using h)).symm
  have hA : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, hS, by rwa [Subgroup.relIndex_top_right]⟩
  have hAab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hSc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcent : g ∈ Subgroup.centralizer (S : Set X) :=
    mem_centralizer_of_isSylowOf_of_pow_mem_centralizer
      (p := 3) (L := ⊤) (A := S) hA hAab (x := g) (by simp) hnorm (k := k) hcentpow
  have hcomm : s * g = g * s := (Subgroup.mem_centralizer_iff.mp hcent) s hs
  rw [MulAut.conj_apply]
  exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3
