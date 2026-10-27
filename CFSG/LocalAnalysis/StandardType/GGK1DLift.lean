module

public import CFSG.LocalAnalysis.StandardType.GGK1DCentreless

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial)
open CFSG.RankThree.Classical (IsReciprocalTransversal)

private lemma ggK1Dl_odd_prime_dvd {nf : ℕ} (hnf : 1 ≤ nf) :
    ∃ p' : ℕ, p'.Prime ∧ p' ≠ 2 ∧ p' ∣ 2 ^ nf + 1 := by
  have hN1 : 2 ^ nf + 1 ≠ 1 := by
    have h2 : 1 < 2 ^ nf :=
      Nat.one_lt_pow (by omega : nf ≠ 0) (by norm_num : (1 : ℕ) < 2)
    omega
  obtain ⟨p', hp'prime, hp'dvd⟩ := Nat.exists_prime_and_dvd hN1
  refine ⟨p', hp'prime, ?_, hp'dvd⟩
  have hodd : Odd (2 ^ nf + 1) :=
    ((Nat.even_pow' (by omega : nf ≠ 0)).mpr even_two).add_one
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hp'dvd)

theorem ggK1D_exists_lift_plus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (h2 : 2 ≤ r)
    (φ : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))))
    (hφ : φ ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))))
    (hφp : φ ^ p = 1) :
    ∃ x : ↥(LargeEvenOmega (LargeEvenQPlus K r)),
      x ^ p = 1 ∧ MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x) = φ := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  obtain ⟨p', hp'prime, hp'2, hp'dvd⟩ := ggK1Dl_odd_prime_dvd hnf
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))) = ⊥ :=
    ggK1D_centreless_plus (p := p') hp'prime hp'2 (Or.inr hp'dvd) hnf hK h2
  have hscal : (LargeEvenScalars (Fin r ⊕ Fin r) K).subgroupOf
      (LargeEvenOmega (LargeEvenQPlus K r)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := K) (m := r) (by omega)
  obtain ⟨r₀, hr₀⟩ := hφ
  obtain ⟨x, hxr⟩ := (QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin r ⊕ Fin r) K).subgroupOf
      (LargeEvenOmega (LargeEvenQPlus K r)))) r₀
  refine ⟨x, ?_, ?_⟩
  · have hconj : MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x) = φ := by
      rw [hxr]; exact hr₀
    have hpow : MulAut.conj
        ((LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x) ^ p) = 1 := by
      rw [map_pow, hconj, hφp]
    have hpowπ : MulAut.conj (LargeEvenProjMk
        (LargeEvenOmega (LargeEvenQPlus K r)) (x ^ p)) = 1 := by
      rw [map_pow]; exact hpow
    have hmem : LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) (x ^ p) ∈
        Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))) =>
        f g) hpowπ
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) (x ^ p)) =
          ((LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) (x ^ p)) * g *
            (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) (x ^ p))⁻¹) *
            (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) (x ^ p)) := by rw [hg]
        _ = (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) (x ^ p)) * g := by group
    have hπ1 : LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) (x ^ p) = 1 := by
      have := hmem
      rw [hZ] at this
      exact Subgroup.mem_bot.mp this
    have hxpk : x ^ p ∈ (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r))).ker := by
      rw [MonoidHom.mem_ker]; exact hπ1
    rw [LargeEvenProjMk, QuotientGroup.ker_mk'] at hxpk
    rw [hscal] at hxpk
    exact Subgroup.mem_bot.mp hxpk
  · rw [hxr, hr₀]

theorem ggK1D_exists_lift_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (h2 : 2 ≤ r) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (φ : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))))
    (hφ : φ ∈ LargeEvenInnSet
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))))
    (hφp : φ ^ p = 1) :
    ∃ x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c)),
      x ^ p = 1 ∧
        MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x) = φ := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  obtain ⟨p', hp'prime, hp'2, hp'dvd⟩ := ggK1Dl_odd_prime_dvd hnf
  have hZ : Subgroup.center
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))) = ⊥ :=
    ggK1D_centreless_minus (p := p') (nf := nf) (r := r) (b := b) (c := c)
      hp'prime hp'2 (Or.inr hp'dvd) hnf hK h2 hirr
  have hscal : (LargeEvenScalars (LargeEvenMinusIdx (r - 1)) K).subgroupOf
      (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := r - 1) b c
  obtain ⟨r₀, hr₀⟩ := hφ
  obtain ⟨x, hxr⟩ := (QuotientGroup.mk'_surjective
    ((LargeEvenScalars (LargeEvenMinusIdx (r - 1)) K).subgroupOf
      (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))) r₀
  refine ⟨x, ?_, ?_⟩
  · have hconj : MulAut.conj
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x) = φ := by
      rw [hxr]; exact hr₀
    have hpow : MulAut.conj
        ((LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x) ^ p) = 1 := by
      rw [map_pow, hconj, hφp]
    have hpowπ : MulAut.conj (LargeEvenProjMk
        (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) (x ^ p)) = 1 := by
      rw [map_pow]; exact hpow
    have hmem : LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) (x ^ p) ∈
        Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun f : MulAut
        (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))) => f g) hpowπ
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) (x ^ p)) =
          ((LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) (x ^ p)) * g *
            (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) (x ^ p))⁻¹) *
            (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) (x ^ p)) := by
              rw [hg]
        _ = (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) (x ^ p)) * g := by
              group
    have hπ1 : LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) (x ^ p) = 1 := by
      have := hmem
      rw [hZ] at this
      exact Subgroup.mem_bot.mp this
    have hxpk : x ^ p ∈
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))).ker := by
      rw [MonoidHom.mem_ker]; exact hπ1
    rw [LargeEvenProjMk, QuotientGroup.ker_mk'] at hxpk
    rw [hscal] at hxpk
    exact Subgroup.mem_bot.mp hxpk
  · rw [hxr, hr₀]

end CFSG.StandardType

end
