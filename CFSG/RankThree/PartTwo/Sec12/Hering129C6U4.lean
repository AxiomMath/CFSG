module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam6
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamE9
import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425U4

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThree.PartOne.KFU (torusSU)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace Hering129C

section Gen

variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb}

theorem center_eq_bot_of_simple_of_isQuasisimple {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hq : CFSG.IsQuasisimple S) : Subgroup.center S = ⊥ := by
  rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a', b', hab⟩ := hq.2.2
    induction a' using QuotientGroup.induction_on with
    | H x =>
      induction b' using QuotientGroup.induction_on with
      | H y =>
        apply hab
        have hx : x ∈ Subgroup.center S := by rw [h]; trivial
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp hx y).symm]

theorem isSimpleGroup_projSL_two_gf2 {m : ℕ} (hm : 2 ≤ m) :
    IsSimpleGroup (projSL 2 (GaloisField 2 m)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 2 m) le_rfl
    (Or.inr (by rw [hcard]; omega)) (Or.inr (by rw [hcard]; omega))

theorem census_false_of_projSU_four_even (hD : Census129 c a I X f) {n : ℕ} (hn : 0 < n)
    (he : Even n) (e : Q ≃* projSU 4 2 n) : False := by
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := he
    omega
  have hℓ : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hD.orderOf_c]
  have hJ := Sec21.ks222U4Even Q ⊤ (Subgroup.zpowers c) n hn he
    ⟨Subgroup.topEquiv.trans e⟩ le_top hℓ
  have hC : (⊤ : Subgroup Q) ⊓
      Subgroup.centralizer ((Subgroup.zpowers c : Subgroup Q) : Set Q) =
        Subgroup.centralizer {c} := by
    rw [top_inf_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hC] at hJ
  set C := Subgroup.centralizer ({c} : Set Q) with hCdef
  set J := inSubgroup perfectResidual C with hJdef
  have hJs : IsSimpleGroup J := by
    rcases hJ with ⟨⟨eJ⟩⟩ | ⟨⟨eJ⟩⟩
    · haveI := isSimpleGroup_projSL_two_gf2 hn2
      exact eJ.isSimpleGroup
    · haveI := isSimpleGroup_projSL_two_gf2 (m := 2 * n) (by omega)
      exact eJ.isSimpleGroup
  have hperf : ⁅I, I⁆ = I := Subgroup.isPerfect_iff.mp hD.isPerfect
  have hIJ : I ≤ J := le_inSubgroup_perfectResidual_of_isPerfect hD.le_centralizer hD.isPerfect
  have hJC : J ≤ C := Subgroup.map_subtype_le _
  have hc1 := c_ne_one hD
  haveI := hJs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with hZ | hZ
  · apply hc1
    have hcZ : (⟨c, hIJ hD.c_mem⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hJC y.2)
    rw [hZ, Subgroup.mem_bot] at hcZ
    exact congrArg Subtype.val hcZ
  · apply hc1
    have hIab : ⁅I, I⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyZ : (⟨y, hIJ hy⟩ : J) ∈ Subgroup.center J := hZ ▸ Subgroup.mem_top _
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hyZ ⟨x, hIJ hx⟩)).symm
    rw [hperf] at hIab
    have := hD.c_mem
    rw [hIab, Subgroup.mem_bot] at this
    exact this

theorem census_false_of_projSU_four_odd (hD : Census129 c a I X f) {n : ℕ} (hn : 1 ≤ n)
    (ho : Odd n) (e : Q ≃* projSU 4 2 n) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 4 2 n :=
    ⟨Nat.prime_two, hn, by norm_num, by simp⟩
  haveI := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible hadm
  haveI : IsSimpleGroup Q := e.isSimpleGroup
  have hZ : Subgroup.center Q = ⊥ := center_eq_bot_of_simple_of_isQuasisimple ‹_› hD.quasisimple
  have hK : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]
  have hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
  have hpq : 3 ∣ 2 ^ n + 1 := Sec4.Ronan148H.three_dvd_two_pow_add_one ho
  obtain ⟨eS⟩ := Sec4.Ronan148H.nonempty_quotCenter_mulEquiv hZ e
  set A : Subgroup Q := Subgroup.zpowers a ⊔ Subgroup.zpowers c with hA
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := census_abar_isElemAbelian hD
  have hA9 : Nat.card A = 9 := census_card_abar hD
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    haveI := hAel.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  obtain ⟨ψ, hψ⟩ := CFSG.RankThree.PartOne.KFU.exists_diag_iso_le hn hK Nat.prime_three hpq hZ eS
    A (fun x hx => hAel.2 x hx) hAc
  have hle : torusSU 3 4 (GaloisField 2 (2 * n)) ≤ unitarySU 2 n (GaloisField 2 (2 * n)) 4 :=
    CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU hU hpq
  set T : Subgroup (unitarySU 2 n (GaloisField 2 (2 * n)) 4) :=
    (torusSU 3 4 (GaloisField 2 (2 * n))).subgroupOf (unitarySU 2 n (GaloisField 2 (2 * n)) 4)
    with hT
  have hTel : CFSG.Assembly.IsElemAbelian 3 T :=
    Sec4.Ronan148S.isElemAbelian_comap _ (unitarySU 2 n (GaloisField 2 (2 * n)) 4).subtype_injective
      (Sec4.Ronan148H.isElemAbelian_torusSU _)
  have hT27 : Nat.card T = 27 := by
    rw [hT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Sec4.Ronan148H.card_torusSU_three_four (Sec4.Ronan148H.exists_unit_cube_root hU hpq)]
  set E : Subgroup Q := T.map ψ.toMonoidHom with hE
  have hEel : CFSG.Assembly.IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.map hTel _
  have hE27 : Nat.card E = 27 := by
    rw [hE, Subgroup.card_map_of_injective ψ.injective, hT27]
  have hAE : A ≤ E := by
    intro x hx
    refine ⟨ψ.symm x, ?_, by simp⟩
    exact hψ (ψ.symm x) (by simpa using hx)
  obtain ⟨t, htE, htA⟩ : ∃ t ∈ E, t ∉ A := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (fun x hx => h x hx : E ≤ A)
    omega
  have ht3 : t ^ 3 = 1 := hEel.2 t htE
  have htc : t ∈ Subgroup.centralizer (A : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    haveI := hEel.1
    exact congrArg Subtype.val (mul_comm' (⟨d, hAE hd⟩ : E) ⟨t, htE⟩)
  have htX := hD.beta t htc ht3
  have htA' : t ∈ A := by
    have := hD.X_le htX
    rwa [hZ, sup_bot_eq] at this
  exact htA htA'

end Gen

theorem kFCensus46SixU4_holds : KFCensus46SixU4 := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨n, hn, ⟨e⟩⟩ := hQ
  rcases Nat.even_or_odd n with he | ho
  · exact census_false_of_projSU_four_even hD (by omega) he e
  · exact census_false_of_projSU_four_odd hD hn ho e

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
