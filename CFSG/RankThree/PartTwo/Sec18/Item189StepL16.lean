module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepL16Omega
import CFSG.RankThree.PartTwo.Sec18.Item189StepL16Dickson
import CFSG.RankThree.PartTwo.Sec18.Item189StepL16Out
import CFSG.RankThree.PartTwo.Sec18.Item189StepL16SL2
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofOddL2
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec18.Item189StepsProof

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups


variable {G : Type} [Group G] [Finite G]

theorem imAlpha189_omegaOneTwo189_le (M H : Subgroup G) (c : G) :
    imAlpha189 M H c (omegaOneTwo189 (s189 M H)) ≤
      Subgroup.closure {z | z ∈ sAlpha189 M H c ∧ z * z = 1} := by
  have key : ∀ x : G, ∀ hx : x ∈ omegaOneTwo189 (s189 M H), ∀ hxSK : x ∈ sk189 M H c,
      alpha189 M H c ⟨x, hxSK⟩ ∈ Subgroup.closure {z | z ∈ sAlpha189 M H c ∧ z * z = 1} := by
    have hle : omegaOneTwo189 (s189 M H) ≤ sk189 M H c := (omegaOneTwo189_le _).trans le_sup_left
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      intro hySK
      refine Subgroup.subset_closure
        ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy.1), ?_⟩
      have hyy : (⟨y, hySK⟩ : ↥(sk189 M H c)) * ⟨y, hySK⟩ = 1 :=
        Subtype.ext (by simpa [pow_two] using hy.2)
      rw [← map_mul, hyy, map_one]
    | one =>
      intro h1
      have he : (⟨1, h1⟩ : ↥(sk189 M H c)) = 1 := rfl
      rw [he, map_one]
      exact Subgroup.one_mem _
    | mul y z hy hz ihy ihz =>
      intro _
      rw [show (⟨y * z, _⟩ : ↥(sk189 M H c)) = ⟨y, hle hy⟩ * ⟨z, hle hz⟩ from rfl, map_mul]
      exact Subgroup.mul_mem _ (ihy (hle hy)) (ihz (hle hz))
    | inv y hy ihy =>
      intro _
      rw [show (⟨y⁻¹, _⟩ : ↥(sk189 M H c)) = (⟨y, hle hy⟩)⁻¹ from rfl, map_inv]
      exact Subgroup.inv_mem _ (ihy (hle hy))
  rintro _ ⟨g, hg, rfl⟩
  exact key g hg g.2

theorem step189L16_of (h186 : Item186H) (h187 : Item187)
    (hO2B : Step189O2Bound) : Step189L16 := by
  intro G _ _ A M H c hset _ ⟨e⟩ hcard
  exfalso
  apply hset.not_le
  have h := hset.toSec18H
  have h7 := hset.hyp187
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := kAlpha189_normal M H c
  have hO2ne : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) ≠ ⊥ := by
    intro hbot
    have := hO2B G A M H c h h7 hbot
    omega
  have hcN := normalizer_zpowers_le189 h7 hO2ne
  have hθN := theta189_le_n189 h187 h h7
  let φ : ↥(kAlpha189 M H c) ≃* SL₂ (GaloisField 2 4) :=
    (e.trans (Sec4.projSLEquivPSL (GaloisField 2 4))).trans (slEquivPSL (GaloisField 2 4)).symm
  let ψ : ↥(kAlpha189 M H c) ≃* PSL(2, GaloisField 2 4) := φ.trans (slEquivPSL (GaloisField 2 4))
  have hZ : Subgroup.center ↥(kAlpha189 M H c) = ⊥ := by
    have hmap := center_map_equiv φ
    rw [sl2_center_eq_bot] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
  have hC := centralizer_eq_bot_of_sup189 (kAlpha189_sup_sAlpha189 M H c)
    (isPGroup_sAlpha189 M H c) (aschbacherSolvableCore_sKAlpha189 M H c) hZ
  set J := ((normalClosureIn M c ⊓ n189 H).subgroupOf (sk189 M H c)).map (alpha189 M H c)
    with hJdef
  have hJc : kAlpha189 M H c ⊓ Subgroup.normalizer
      (imAlpha189 M H c (Subgroup.zpowers c) : Set (SKAlpha189 M H c)) ≤ J :=
    kAlpha_inf_normalizer_le189 fun x hx => mem_n189_of_mem_normalizer_cAlpha h187 h h7 hcN hx
  have hJΩ : kAlpha189 M H c ⊓ Subgroup.normalizer
      (imAlpha189 M H c (omegaOneTwo189 (s189 M H)) : Set (SKAlpha189 M H c)) ≤ J :=
    kAlpha_inf_normalizer_le189 fun x hx =>
      mem_n189_of_mem_normalizer_omegaAlpha189 h186 h187 h h7 (hset.three 1 2 (by decide)) hx
  refine le_n189_of_kAlpha_le189 hθN ?_
  have hcK : c ∈ normalClosureIn M c := Sec20.self_mem_normalClosureIn M c
  have hcSK : c ∈ sk189 M H c := (le_sup_right : normalClosureIn M c ≤ sk189 M H c) hcK
  set cb := alpha189 M H c ⟨c, hcSK⟩ with hcbdef
  have hcbK : cb ∈ kAlpha189 M H c :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcK)
  have hc3 := pow_three_of_sec18H189 h
  have hc1 : c ≠ 1 := ne_one_of_pRank_eq_one189 hset.pRank_eq
  have hcb3 : cb ^ 3 = 1 := by
    rw [hcbdef, ← map_pow]
    have : (⟨c, hcSK⟩ : ↥(sk189 M H c)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hcb1 : cb ≠ 1 := by
    intro h1
    rw [hcbdef, alpha189, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hord : orderOf (⟨⟨c, hcSK⟩, h1⟩ : aschbacherSolvableCore 3 ↥(sk189 M H c)) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hc3 hc1
    have hdvd := orderOf_dvd_natCard
      (⟨⟨c, hcSK⟩, h1⟩ : aschbacherSolvableCore 3 ↥(sk189 M H c))
    rw [hord] at hdvd
    exact (solvable_prime_complement_core_characterization (H := ↥(sk189 M H c))
      Nat.prime_three).2.2.1 hdvd
  have hzc := imAlpha189_zpowers M H c hcSK
  rw [← hcbdef] at hzc
  set c' : ↥(kAlpha189 M H c) := ⟨cb, hcbK⟩ with hc'def
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using hcb3)
  have hc'1 : c' ≠ 1 := fun h1 => hcb1 (congrArg Subtype.val h1)
  set x₀ : SL₂ (GaloisField 2 4) := φ c' with hx₀def
  have hx₀3 : x₀ ^ 3 = 1 := by rw [hx₀def, ← map_pow, hc'3, map_one]
  have hx₀1 : x₀ ≠ 1 := fun h1 => hc'1 (φ.injective (by rw [← hx₀def, h1, map_one]))
  have hx₀c : φ.symm x₀ = c' := φ.symm_apply_apply c'
  obtain ⟨w, hww, hwx⟩ := exists_involution_inv_sl2_189 hx₀3 hx₀1
  obtain ⟨y, hyx, hy5⟩ := exists_orderOf_five_commute_sl2_sixteen189 hx₀3 hx₀1
  set w' : ↥(kAlpha189 M H c) := φ.symm w with hw'def
  set y' : ↥(kAlpha189 M H c) := φ.symm y with hy'def
  have hw'w' : w' * w' = 1 := by rw [hw'def, ← map_mul, hww, map_one]
  have hw'c : w' * c' * w'⁻¹ = c'⁻¹ := by
    rw [hw'def, ← hx₀c, ← map_inv, ← map_mul, ← map_mul, hwx, map_inv]
  have hy'c : y' * c' = c' * y' := by
    rw [hy'def, ← hx₀c, ← map_mul, ← map_mul, hyx]
  have hcbJ : cb ∈ J :=
    hJc ⟨hcbK, by rw [hzc]; exact Subgroup.le_normalizer (Subgroup.mem_zpowers cb)⟩
  have hw'J : (w' : SKAlpha189 M H c) ∈ J := by
    refine hJc ⟨w'.2, ?_⟩
    rw [hzc]
    have hinv : w'⁻¹ = w' := inv_eq_of_mul_eq_one_left hw'w'
    have h1 : (w' : SKAlpha189 M H c) * cb * (w' : SKAlpha189 M H c)⁻¹ = cb⁻¹ := by
      have := congrArg Subtype.val hw'c
      simpa [hc'def] using this
    have h2 : (w' : SKAlpha189 M H c)⁻¹ * cb * (w' : SKAlpha189 M H c) = cb⁻¹ := by
      have hinv' : (w' : SKAlpha189 M H c)⁻¹ = w' := by
        rw [← Subgroup.coe_inv, hinv]
      rw [hinv']
      rw [hinv'] at h1
      exact h1
    exact mem_normalizer_zpowers189 (by rw [h1]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
      (by rw [h2]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
  have hy'J : (y' : SKAlpha189 M H c) ∈ J := by
    refine hJc ⟨y'.2, ?_⟩
    rw [hzc]
    have hcomm : (y' : SKAlpha189 M H c) * cb = cb * (y' : SKAlpha189 M H c) := by
      have := congrArg Subtype.val hy'c
      simpa [hc'def] using this
    have h1 : (y' : SKAlpha189 M H c) * cb * (y' : SKAlpha189 M H c)⁻¹ = cb := by
      rw [hcomm, mul_inv_cancel_right]
    have h2 : (y' : SKAlpha189 M H c)⁻¹ * cb * (y' : SKAlpha189 M H c) = cb := by
      rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    exact mem_normalizer_zpowers189 (by rw [h1]; exact Subgroup.mem_zpowers _)
      (by rw [h2]; exact Subgroup.mem_zpowers _)
  obtain ⟨E, hEK, hEC, hE4, hE2⟩ :=
    exists_le_centralizer_omega_sl2_sixteen189 φ hC (isPGroup_sAlpha189 M H c)
  have hEJ : E ≤ J := fun x hx =>
    hJΩ ⟨hEK hx, mem_normalizer_of_mem_centralizer189 (imAlpha189_omegaOneTwo189_le M H c)
      (hEC hx)⟩
  set H' : Subgroup PSL(2, GaloisField 2 4) :=
    (J.subgroupOf (kAlpha189 M H c)).map ψ.toMonoidHom with hH'def
  have hmem : ∀ k : ↥(kAlpha189 M H c), (k : SKAlpha189 M H c) ∈ J → ψ k ∈ H' := fun k hk =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
  have hψ : ∀ k : ↥(kAlpha189 M H c), ψ k = slEquivPSL (GaloisField 2 4) (φ k) := fun _ => rfl
  have htop : H' = ⊤ := by
    refine eq_top_of_psl2_sixteen189 H' (x := ψ c') (y := ψ y') (w := ψ w')
      (hmem c' hcbJ) (hmem y' hy'J) (hmem w' hw'J) ?_ ?_ ?_ ?_ ?_
      (E := (E.subgroupOf (kAlpha189 M H c)).map ψ.toMonoidHom) ?_ ?_ ?_
    · rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hc'3 hc'1
    · rw [MulEquiv.orderOf_eq, hy'def, MulEquiv.orderOf_eq]
      exact hy5
    · rw [← map_mul, ← map_mul, hy'c]
    · rw [← map_mul, hw'w', map_one]
    · rw [← map_inv, ← map_mul, ← map_mul, hw'c, map_inv]
    · exact Subgroup.map_mono fun x hx => hEJ hx
    · rintro _ ⟨x, hx, rfl⟩
      have hxx : x * x = 1 := Subtype.ext (by simpa using hE2 _ hx)
      rw [← map_mul]
      change ψ (x * x) = 1
      rw [hxx, map_one]
    · rw [Subgroup.card_map_of_injective ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv]
      exact hE4
  intro k hk
  have hk' : ψ ⟨k, hk⟩ ∈ H' := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [hH'def, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hk'
  exact hk'

end CFSG.RankThree.PartTwo.Sec18
