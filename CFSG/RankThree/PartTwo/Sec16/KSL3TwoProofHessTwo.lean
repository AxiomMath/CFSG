module

public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessConj
import CFSG.RankThree.PartTwo.Sec15.Item15Res5ProofHess
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofFusX
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKSL3Two

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open CFSG.RankThree.PartTwo.Sec14.Res8Hess
open CFSG.RankThree.PartTwo.Sec15.Proof15Res5
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)

theorem eq_bot_of_le_normalizer_hessian {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : 1 ≤ f) (hiso : Sec4.IsoLThreePi X 2 f) {E : Subgroup X}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {T : Subgroup X} (hT : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set X)) : T = ⊥ := by
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, -, -, -, -, Φ, hΦE⟩ :=
    exists_hessian_equiv hf hiso hE hE9 htr
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set Ê := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hÊ
  have hcent_model : ∀ e' ∈ Ê, e' ≠ 1 → ∀ z' : projImage (slPi π 3 (2 ^ f) K),
      z' * e' = e' * z' → ∀ k : ℕ, z' ^ 2 ^ k = 1 → z' = 1 := by
    obtain ⟨a, b, hav, hbv, -, -, hcentab⟩ :=
      hessian_pair (π := π) (f := f) (K := K) hK hq hτ hτ1 (h := 1) (one_mem _)
    have haD : a = dM := by
      apply Subtype.ext
      rw [hav, hdM]
      simp
    have hbC : b = cM := by
      apply Subtype.ext
      rw [hbv, hcM]
      simp
    rw [haD, hbC] at hcentab
    simpa only [hÊ] using hcentab
  have hcent : ∀ e ∈ E, e ≠ 1 → ∀ z : X, z * e = e * z → ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
    intro e he he1 z hze k hzk
    have hemap : e ∈ Ê.map Φ.toMonoidHom := by
      rw [hΦE]
      exact he
    obtain ⟨e', he', rfl⟩ := hemap
    have he'1 : e' ≠ 1 := fun h => he1 (by rw [h, map_one])
    have hze' : Φ.symm z * e' = e' * Φ.symm z := by
      simpa using congrArg Φ.symm hze
    have hzk' : (Φ.symm z) ^ 2 ^ k = 1 := by
      simpa using congrArg Φ.symm hzk
    have hz1 := hcent_model e' he' he'1 (Φ.symm z) hze' k hzk'
    calc z = Φ (Φ.symm z) := (Φ.apply_symm_apply z).symm
      _ = 1 := by rw [hz1, map_one]
  have hT3 : ¬ 3 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := T)).mp hT
    rw [hn]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have hTodd : ¬ 2 ∣ Nat.card T :=
    not_two_dvd_card_of_hessian hE hE9 hcent hET hT3
  have hcard : Nat.card T = 1 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := T)).mp hT
    have hn0 : n = 0 := by
      by_contra h
      exact hTodd (hn ▸ dvd_pow_self 2 h)
    rw [hn, hn0, pow_zero]
  exact Subgroup.card_eq_one.mp hcard

theorem eq_bot_of_le_normalizer_of_le {X : Type} [Group X] [Finite X] {f n : ℕ}
    (hf : 1 ≤ f) (hiso : Sec4.IsoLThreePi X 2 f) {L : Subgroup X} (hn : 1 ≤ n) (hn3 : ¬ 3 ∣ n)
    (hL : Sec4.IsoLThreePi ↥L 2 n) {E : Subgroup X} (hEL : E ≤ L)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    {T : Subgroup X} (hT : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set X)) : T = ⊥ := by
  have htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁ := by
    have hEsub : CFSG.Assembly.IsElemAbelian 3 (E.subgroupOf L) :=
      CFSG.Open.IsElemAbelian.subgroupOf hE L
    have hEsub9 : Nat.card (E.subgroupOf L) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE9]
    intro y₀ hy₀ hy₀1 y₁ hy₁ hy₁1
    have hy₀L : y₀ ∈ L := hEL hy₀
    have hy₁L : y₁ ∈ L := hEL hy₁
    have hy₀'1 : (⟨y₀, hy₀L⟩ : ↥L) ≠ 1 := fun h => hy₀1 (by simpa using congrArg Subtype.val h)
    have hy₁'1 : (⟨y₁, hy₁L⟩ : ↥L) ≠ 1 := fun h => hy₁1 (by simpa using congrArg Subtype.val h)
    obtain ⟨w, hw, hwy⟩ := kS1617FusX ↥L n hn hn3 hL (E.subgroupOf L) hEsub hEsub9
      ⟨y₀, hy₀L⟩ hy₀ hy₀'1 ⟨y₁, hy₁L⟩ hy₁ hy₁'1
    refine ⟨(w : X), ?_, ?_⟩
    · have hwmap : (w : X) ∈ (Subgroup.normalizer
          (((E.subgroupOf L : Subgroup ↥L) : Set ↥L))).map L.subtype := ⟨w, hw, rfl⟩
      have hle := Subgroup.le_normalizer_map (H := (E.subgroupOf L : Subgroup ↥L))
        L.subtype hwmap
      rwa [Subgroup.map_subgroupOf_eq_of_le hEL] at hle
    · have := congrArg Subtype.val hwy
      simpa using this
  exact eq_bot_of_le_normalizer_hessian hf hiso hE hE9 htr hT hET

end ProofKSL3Two

end CFSG.RankThree.PartTwo.Sec16
