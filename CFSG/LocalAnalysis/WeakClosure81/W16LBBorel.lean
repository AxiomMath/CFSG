module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelData
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymNorm
import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapBase
import CFSG.CGT.Timmesfeld75.Sec4CaseIIIRel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.LocalAnalysis.WeakClosure81.SevenK

private theorem w16l_one_le_of_sympTransvection {k : ℕ} {F : Type} [Field F]
    {t : ↥(CFSG.Open.StatedSp k F)} (ht : IsSymplecticTransvectionIn k t) : 1 ≤ k := by
  unfold IsSymplecticTransvectionIn at ht
  have hle := Matrix.rank_le_card_height
    ((((t : GL (Fin k ⊕ Fin k) F)) :
      Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) - 1)
  rw [ht] at hle
  have hcard : Fintype.card (Fin k ⊕ Fin k) = k + k := by simp
  omega

private theorem w16l_false_of_borel {X : Type} [Group X] [Finite X] {B P : Subgroup X}
    (hB2 : Nat.card B = 2) (hcore : CFSG.pCore 2 X = ⊥)
    (hP2 : IsPGroup 2 P) (hPsyl : ¬ 2 ∣ P.index)
    (hM : ∀ d ∈ Subgroup.normalizer (P : Set X), d ∈ Subgroup.normalizer (B : Set X))
    (hs : ∀ s ∈ B, s ≠ 1 →
      BorelLieFacts (X ⧸ Subgroup.center X) (QuotientGroup.mk s)) :
    False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup X := Subgroup.center X
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  obtain ⟨s, hsB, hsne⟩ : ∃ s : X, s ∈ B ∧ s ≠ 1 := by
    obtain ⟨y, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : B)).1 hB2
    exact ⟨y, y.2, fun h => hy1 (Subtype.ext h)⟩
  have hcentral : ∀ p ∈ P, p * s = s * p := by
    intro p hp
    have hpN : p ∈ Subgroup.normalizer (P : Set X) := Subgroup.le_normalizer hp
    have hpB : p ∈ Subgroup.normalizer (B : Set X) := hM p hpN
    have hconj : p * s * p⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hpB s).mp hsB
    have hconj_ne : p * s * p⁻¹ ≠ 1 := by
      intro h1
      apply hsne
      calc s = p⁻¹ * (p * s * p⁻¹) * p := by group
        _ = p⁻¹ * 1 * p := by rw [h1]
        _ = 1 := by group
    have h_eq : p * s * p⁻¹ = s :=
      CFSG.CGT.Timmesfeld75.eq_of_card_two_subgroup hB2 hconj hsB hconj_ne hsne
    calc p * s = p * s * p⁻¹ * p := by group
      _ = s * p := by rw [h_eq]
  let P_syl : Sylow 2 X := hP2.toSylow hPsyl
  let P' : Sylow 2 (X ⧸ Z) := P_syl.mapSurjective (QuotientGroup.mk'_surjective Z)
  have hP'_coe : (P' : Subgroup (X ⧸ Z)) = P.map π := rfl
  have hcentral' : ∀ p ∈ (P' : Subgroup (X ⧸ Z)),
      p * QuotientGroup.mk s = QuotientGroup.mk s * p := by
    intro p hp
    rw [hP'_coe] at hp
    obtain ⟨p0, hp0, rfl⟩ := Subgroup.mem_map.mp hp
    change QuotientGroup.mk' Z p0 * QuotientGroup.mk' Z s =
      QuotientGroup.mk' Z s * QuotientGroup.mk' Z p0
    rw [← map_mul, ← map_mul, hcentral p0 hp0]
  obtain ⟨dbar, hdbar, hdbar_ne⟩ := (hs s hsB hsne).borel P' hcentral'
  have hodd : Odd (Nat.card π.ker) := by
    rw [show π.ker = Z from QuotientGroup.ker_mk' Z]
    exact odd_card_center_of_pCore_eq_bot hcore
  have hmap := map_normalizer_eq_of_odd_ker π (QuotientGroup.mk'_surjective Z) hodd hP2
  have hdbar' : dbar ∈ (Subgroup.normalizer (P : Set X)).map π := by
    rw [hmap, ← hP'_coe]
    exact hdbar
  obtain ⟨d, hd, hd_eq⟩ := Subgroup.mem_map.mp hdbar'
  have hdB : d ∈ Subgroup.normalizer (B : Set X) := hM d hd
  have hconj : d * s * d⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hdB s).mp hsB
  have hconj_ne : d * s * d⁻¹ ≠ 1 := by
    intro h1
    apply hsne
    calc s = d⁻¹ * (d * s * d⁻¹) * d := by group
      _ = d⁻¹ * 1 * d := by rw [h1]
      _ = 1 := by group
  have h_eq : d * s * d⁻¹ = s :=
    CFSG.CGT.Timmesfeld75.eq_of_card_two_subgroup hB2 hconj hsB hconj_ne hsne
  have hkey : QuotientGroup.mk' Z (d * s * d⁻¹) =
      QuotientGroup.mk' Z d * QuotientGroup.mk s * (QuotientGroup.mk' Z d)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rfl
  refine hdbar_ne ?_
  calc dbar * QuotientGroup.mk s * dbar⁻¹
      = QuotientGroup.mk' Z d * QuotientGroup.mk' Z s * (QuotientGroup.mk' Z d)⁻¹ := by
        rw [← hd_eq]
        rfl
    _ = QuotientGroup.mk' Z (d * s * d⁻¹) := hkey.symm
    _ = QuotientGroup.mk' Z s := by rw [h_eq]
    _ = QuotientGroup.mk s := rfl

theorem w16l_false_of_borel_sp {X : Type} [Group X] [Finite X] {B P : Subgroup X} {m n : ℕ}
    (hn : 1 < n) (hB2 : Nat.card B = 2) (hcore : CFSG.pCore 2 X = ⊥) (hBP : B ≤ P)
    (hP2 : IsPGroup 2 P) (hPsyl : ¬ 2 ∣ P.index)
    (hM : ∀ d ∈ Subgroup.normalizer (P : Set X), d ∈ Subgroup.normalizer (B : Set X))
    (hs : ∀ s ∈ B, s ≠ 1 → IsSymplecticTransvection X m n s) :
    False := by
  refine w16l_false_of_borel hB2 hcore hP2 hPsyl hM ?_
  intro s hsB hsne
  obtain ⟨k, _, F, hField, hFinite, hF, e, ht⟩ := hs s hsB hsne
  exact BorelLieFacts.of_mulEquiv e
    (borelLieFacts_sp hF hn (w16l_one_le_of_sympTransvection ht) ht)

theorem w16l_false_of_borel_psu {X : Type} [Group X] [Finite X] {B P : Subgroup X} {m n : ℕ}
    (hn : 1 < n) (hm : 3 ≤ m) (hB2 : Nat.card B = 2) (hcore : CFSG.pCore 2 X = ⊥) (hBP : B ≤ P)
    (hP2 : IsPGroup 2 P) (hPsyl : ¬ 2 ∣ P.index)
    (hM : ∀ d ∈ Subgroup.normalizer (P : Set X), d ∈ Subgroup.normalizer (B : Set X))
    (hs : ∀ s ∈ B, s ≠ 1 → IsUnitaryTransvection X m n s) :
    False := by
  refine w16l_false_of_borel hB2 hcore hP2 hPsyl hM ?_
  intro s hsB hsne
  obtain ⟨F, hField, hFinite, hF, e, ht⟩ := hs s hsB hsne
  exact BorelLieFacts.of_mulEquiv e (borelLieFacts_psu hF hn hm ht)

end CFSG.LocalAnalysis.WeakClosure81

end
