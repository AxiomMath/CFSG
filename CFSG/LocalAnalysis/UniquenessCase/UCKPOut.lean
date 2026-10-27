module

public import CFSG.LocalAnalysis.UniquenessCase.UCKU3
public import CFSG.LocalAnalysis.UniquenessCase.UCKP1
public import CFSG.LocalAnalysis.UniquenessCase.UCKPAutQuot
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem u3OutShape : U3OutShape := by
  classical
  intro X _ _ n hX
  have hn2 : 2 ≤ n := u3Range X n hX
  obtain ⟨e, hB⟩ := CFSG.SeitzReduction.RankOne.exists_benderType_of_lieModel_psu3 hn2 hX.2
  obtain ⟨Dd, hDn, -, hDcard, hcyc, -⟩ := CFSG.GH74.Uniqueness.Bender.BenderType.outer_unitary hB
  let ψ : MulAut X →* (Outer (X ⧸ center X) ⧸ Dd) :=
    (QuotientGroup.mk' Dd).comp ((QuotientGroup.mk' (inner (X ⧸ center X))).comp autQuot)
  have hP : commutator X = ⊤ := hX.1.1
  have hψ : ∀ φ : MulAut X, ψ φ = 1 → ∃ d ∈ Dd, d = QuotientGroup.mk' (inner (X ⧸ center X)) (autQuot φ) := by
    intro φ hφ
    have h1 : (QuotientGroup.mk' Dd) (QuotientGroup.mk' (inner (X ⧸ center X)) (autQuot φ)) = 1 := hφ
    exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  have hd3 : ∀ d ∈ Dd, d ^ 3 = 1 := by
    intro d hd
    have h1 : orderOf (⟨d, hd⟩ : Dd) ∣ Nat.card Dd := orderOf_dvd_natCard _
    have h2 : Nat.card Dd ∣ 3 := hDcard ▸ Nat.gcd_dvd_left 3 _
    have h3 : (⟨d, hd⟩ : Dd) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 (h1.trans h2)
    simpa using congrArg Subtype.val h3
  have hinner : ∀ φ : MulAut X, autQuot φ ∈ inner (X ⧸ center X) →
      φ ∈ (MulAut.conj : X →* MulAut X).range := by
    intro φ hφ
    obtain ⟨x, hx⟩ := exists_conj_autQuot (X := X) hφ
    exact ⟨x, (autQuot_injective hP hx).symm.symm ▸ rfl⟩
  refine ⟨ψ.ker, inferInstance, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨x, rfl⟩
    show ψ (MulAut.conj x) = 1
    have h1 : QuotientGroup.mk' (inner (X ⧸ center X)) (autQuot (MulAut.conj x)) = 1 := by
      rw [autQuot_conj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨_, rfl⟩
    show (QuotientGroup.mk' Dd) ((QuotientGroup.mk' (inner (X ⧸ center X))) (autQuot (MulAut.conj x))) = 1
    rw [h1, map_one]
  ·
    have hcyc' : IsCyclic (Outer (X ⧸ center X) ⧸ Dd) := hcyc
    have : IsCyclic ψ.range := Subgroup.isCyclic ψ.range
    exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange ψ).symm.surjective
  ·
    intro φ hφ
    obtain ⟨d, hd, hdφ⟩ := hψ φ hφ
    have h3 : QuotientGroup.mk' (inner (X ⧸ center X)) (autQuot (φ ^ 3)) = 1 := by
      rw [map_pow, map_pow, ← hdφ]
      exact hd3 d hd
    apply hinner
    exact (QuotientGroup.eq_one_iff _).1 h3
  ·
    intro hev φ hφ
    obtain ⟨d, hd, hdφ⟩ := hψ φ hφ
    have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := by
      obtain ⟨k, rfl⟩ := hev
      have h4 : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
      have h41 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
      have hnd : ¬ 3 ∣ 2 ^ (k + k) + 1 := by omega
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd
    have hDd1 : Nat.card Dd = 1 := hDcard.trans hgcd
    have hd1 : d = 1 := by
      have hsub : Subsingleton Dd := Finite.card_le_one_iff_subsingleton.1 hDd1.le
      have := Subsingleton.elim (⟨d, hd⟩ : Dd) 1
      simpa using congrArg Subtype.val this
    have h3 : QuotientGroup.mk' (inner (X ⧸ center X)) (autQuot φ) = 1 := by rw [← hdφ, hd1]
    exact hinner φ ((QuotientGroup.eq_one_iff _).1 h3)

end CFSG.LocalAnalysis.UniquenessCase.UCK
