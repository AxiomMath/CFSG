module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.RankThree.PartTwo.KFacts.K426RestMcL
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125Eng
import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestMcL
import CFSG.Sporadic.SmallOddCore.McLAut
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Schreier.PairMcLFaithful
public import CFSG.Sporadic.Schreier.PairOuter
public import Certificates.Data.K426McL

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.RankThree.PartTwo.KFacts.K426Rest
  CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem mcl3_O_exp :
    closure (permsA 275 mcl3OGens) ≤ closure (permsA 275 mcl3CAGens) ∧
      ((closure (permsA 275 mcl3OGens)).subgroupOf (closure (permsA 275 mcl3CAGens))).Normal ∧
      Nat.card (closure (permsA 275 mcl3OGens)) = 243 ∧
      Monoid.exponent (closure (permsA 275 mcl3OGens)) = 3 := by
  obtain ⟨-, -, hle, hnorm, -, hcard, hexp⟩ := normal_p Nat.prime_three mcl3Keys_lt
    (centOKP_enum mcl3_caseA_check.2.1) mcl3_caseA_check.2.2 mem_mclP_of_sift (by norm_num)
  exact ⟨hle, hnorm, hcard, hexp⟩

private theorem l125McL_map_conj_le_centralizer {G : Type*} [Group G] {P : Subgroup G} {y k : G}
    (hk : k ∈ P) (e : ℕ) {T : Subgroup G} (hT : T ≤ centralizer {y} ⊓ P) :
    T.map (MulAut.conj k).toMonoidHom ≤ centralizer {k * y ^ e * k⁻¹} ⊓ P := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hwc, hwP⟩ := mem_inf.1 (hT hw)
  have hwy : w * y ^ e = y ^ e * w :=
    (Commute.pow_right (show Commute w y from mem_centralizer_singleton_iff.1 hwc) e).eq
  refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · change k * w * k⁻¹ * (k * y ^ e * k⁻¹) = k * y ^ e * k⁻¹ * (k * w * k⁻¹)
    calc k * w * k⁻¹ * (k * y ^ e * k⁻¹) = k * (w * y ^ e) * k⁻¹ := by group
      _ = k * (y ^ e * w) * k⁻¹ := by rw [hwy]
      _ = k * y ^ e * k⁻¹ * (k * w * k⁻¹) := by group
  · exact P.mul_mem (P.mul_mem hk hwP) (P.inv_mem hk)

private theorem l125McL_rows_mclP
    {x : Equiv.Perm (Fin 275)} (hx : x ∈ mclP)
    (hxo : orderOf x = 3) :
    Nat.card (centralizer {x} ⊓ mclP : Subgroup (Equiv.Perm (Fin 275))) = 972 ∨
      ∃ T : Subgroup (Equiv.Perm (Fin 275)), T ≤ centralizer {x} ⊓ mclP ∧
        (∀ t ∈ T, t ^ 3 = 1) ∧ Nat.card T = 243 := by
  obtain ⟨k, hk, j, hj, e, he, rfl⟩ := exists_conj_rep mcl3Q_le card_mcl3Q
    (fun j => permOfArr 275 mcl3Lines[j]!) (fun c => permOfArr 275 mcl3Lines[c]!)
    (fun j => permOfArr 275 mcl3Trans[j]!) (fun j => mcl3Rec.getD j 0) (r := 148)
    (fun g hg hg3 => mcl3_lines hg hg3) (fun j hj => mcl3_trans hj) hx hxo
  have hrec : mcl3Rec.getD j 0 < 2 := of_decide_eq_true (allLt_spec mcl3_lines_check.2.2.2 hj)
  have hcube := (linesOK3_line mcl3_lines_check.1 (lt_trans hrec (by norm_num : 2 < 148))).2
  rcases (by omega : mcl3Rec.getD j 0 = 0 ∨ mcl3Rec.getD j 0 = 1) with h | h
  · right
    obtain ⟨hle, -, hcard, hexp⟩ := mcl3_O_exp
    have hO : closure (permsA 275 mcl3OGens) ≤
        centralizer {permOfArr 275 mcl3Lines[mcl3Rec.getD j 0]!} ⊓ mclP := by
      rw [h, ← mcl3_caseA.1]
      exact hle
    refine ⟨(closure (permsA 275 mcl3OGens)).map (MulAut.conj k).toMonoidHom,
      l125McL_map_conj_le_centralizer hk e hO, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hw3 : w ^ 3 = 1 := by
        have := Monoid.pow_exponent_eq_one (⟨w, hw⟩ : closure (permsA 275 mcl3OGens))
        rw [hexp] at this
        exact congrArg Subtype.val this
      change (k * w * k⁻¹) ^ 3 = 1
      rw [← MulAut.conj_apply, ← map_pow, hw3, map_one]
    · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hcard]
  · left
    rw [card_centralizer_conj hk hcube he, h, ← mcl3_caseB.1]
    exact mcl3_caseB.2

private theorem l125McL_rows_of_mulEquiv {G G' : Type*} [Group G] [Group G'] {P : Subgroup G'}
    (e : G ≃* P)
    (h : ∀ x ∈ P, orderOf x = 3 →
      Nat.card (centralizer {x} ⊓ P : Subgroup G') = 972 ∨
        ∃ T : Subgroup G', T ≤ centralizer {x} ⊓ P ∧ (∀ t ∈ T, t ^ 3 = 1) ∧ Nat.card T = 243) :
    ∀ x : G, orderOf x = 3 → Nat.card (centralizer {x}) = 972 ∨
      ∃ T : Subgroup G, T ≤ centralizer {x} ∧ (∀ t ∈ T, t ^ 3 = 1) ∧ Nat.card T = 243 := by
  intro x hx
  have hXo : orderOf ((e x : P) : G') = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hx
  have hι : Function.Injective (P.subtype.comp e.toMonoidHom) :=
    Subtype.val_injective.comp e.injective
  rcases h _ (e x).2 hXo with hc | ⟨T, hTC, hT3, hTcard⟩
  · left
    rw [card_centralizer_of_mulEquiv e x]
    exact hc
  · right
    refine ⟨T.comap (P.subtype.comp e.toMonoidHom), ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨hzc, -⟩ := mem_inf.1 (hTC hz)
      rw [mem_centralizer_singleton_iff] at hzc ⊢
      apply hι
      change ((e (z * x) : P) : G') = ((e (x * z) : P) : G')
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact hzc
    · intro t ht
      apply hι
      rw [map_pow, map_one]
      exact hT3 _ ht
    · rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self ?_]
      · exact hTcard
      · intro w hw
        obtain ⟨-, hwP⟩ := mem_inf.1 (hTC hw)
        exact ⟨e.symm ⟨w, hwP⟩, by simp⟩

theorem res3L125_rows_McL :
    ∀ x : Blueprint.NativeSporadic.McL, orderOf x = 3 →
      (¬ 5 ∣ Nat.card (Subgroup.centralizer {x}) ∧ ¬ 7 ∣ Nat.card (Subgroup.centralizer {x})) ∨
        ∃ T : Subgroup Blueprint.NativeSporadic.McL, T ≤ Subgroup.centralizer {x} ∧
          (∀ t ∈ T, t ^ 3 = 1) ∧ 243 ≤ Nat.card T := by
  intro x hx
  have hrows := l125McL_rows_of_mulEquiv (G := Blueprint.NativeSporadic.McL) (P := mclP)
    mclPermEquiv (fun _ hx hxo => l125McL_rows_mclP hx hxo)
  rcases hrows x hx with h | ⟨T, hTC, hT3, hT⟩
  · left
    rw [h]
    exact ⟨by norm_num, by norm_num⟩
  · exact Or.inr ⟨T, hTC, hT3, hT.ge⟩

theorem res3L125_isPGroup_two_outer_McL :
    IsPGroup 2 (Outer Blueprint.NativeSporadic.McL) := by
  haveI : Finite Blueprint.NativeSporadic.McL := CFSG.Sporadic.McL.fam_mcl_simplicity.1
  haveI : Finite (MulAut Blueprint.NativeSporadic.McL) := MulEquiv.finite_left
  exact res3L125_isPGroup_two_outer_of_card_le_two
    (outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.mcl_outer_card_le mclPermEquiv)

theorem res3L125_three_mul_card_center_lt_McL
    {J : Type} [Group J] [Finite J] (hq : CFSG.IsQuasisimple J)
    (hZ : IsPGroup 3 (Subgroup.center J))
    (e : J ⧸ Subgroup.center J ≃* Blueprint.NativeSporadic.McL) :
    3 * Nat.card (Subgroup.center J) < 243 := by
  have h := Nat.le_of_dvd (by norm_num)
    (CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.card_center_dvd_three_of_McL hq hZ e)
  omega

theorem res3NoDatumMcL_holds :
    Res3NoDatumMcL := by
  rintro J _ _ _ hq ⟨e⟩ c g V U hd
  haveI : Finite Blueprint.NativeSporadic.McL := Finite.of_equiv _ e.toEquiv
  refine @res3L125_false_of_rows J _ _ hq Blueprint.NativeSporadic.McL
    (inferInstance : Group Blueprint.NativeSporadic.McL) this e
    res3L125_isPGroup_two_outer_McL ?_ c g V U hd
  intro x hx
  rcases res3L125_rows_McL x hx with hA | ⟨T, hTC, hT3, hT⟩
  · exact Or.inl hA
  · exact Or.inr (Or.inl ⟨T, hTC, hT3,
      lt_of_lt_of_le (res3L125_three_mul_card_center_lt_McL hq hd.center_pGroup e) hT⟩)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
