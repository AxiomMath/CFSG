module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusInner
import CFSG.Milestones.ASVolI.A3OddFacts
import CFSG.Mathlib.Decide.Bounded
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusTools
public import Certificates.Certificate291400
import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
import CFSG.Walter.J1Props

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open Equiv

@[expose] def finsetSubgroup {G : Type*} [Group G] (F : Finset G) (h1 : (1 : G) ∈ F)
    (hmul : ∀ a ∈ F, ∀ b ∈ F, a * b ∈ F) (hinv : ∀ a ∈ F, a⁻¹ ∈ F) : Subgroup G where
  carrier := F
  one_mem' := h1
  mul_mem' := fun ha hb => hmul _ ha _ hb
  inv_mem' := fun ha => hinv _ ha

theorem card_finsetSubgroup {G : Type*} [Group G] {F : Finset G} {h1 hmul hinv} :
    Nat.card (finsetSubgroup F h1 hmul hinv) = F.card := by
  rw [← Nat.card_eq_finsetCard F]
  rfl

theorem exists_innerCfg_of_sylow {S : Type} [Group S] [Finite S]
    (h9 : (Nat.card S).factorization 3 = 2) {B V : Subgroup S} (hc : InnerCfg B V)
    (B₀ : Subgroup S) (hB₀ : Nat.card B₀ = 9) : ∃ V₀ : Subgroup S, InnerCfg B₀ V₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let SB : Sylow 3 S := Sylow.ofCard B (by rw [hc.card, h9]; norm_num)
  let SB₀ : Sylow 3 S := Sylow.ofCard B₀ (by rw [hB₀, h9]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S SB SB₀
  have hBg : B.map (MulAut.conj g).toMonoidHom = B₀ := by
    have h1 : ((g • SB : Sylow 3 S) : Subgroup S) = B₀ := by rw [hg]; rfl
    rw [Sylow.coe_subgroup_smul] at h1
    rw [← h1]
    rfl
  exact ⟨_, hBg ▸ hc.map (MulAut.conj g)⟩

theorem olRow_alt_le_four {n : ℕ} (hn : n ≤ 4) :
    OLRow (fun T _ => Nonempty (T ≃* alternatingGroup (Fin n))) := by
  intro X _ _ P L Q hcfg ⟨e⟩
  have hsol : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by simpa using hn)
  have hsolL : Group.IsSolvable L := Group.isSolvable_of_surjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  have hnt : Nontrivial L := by
    have hq := CFSG.LocalCores.isQuasisimple_nontrivial hcfg.qsL
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hs : Subsingleton (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      (QuotientGroup.mk_surjective :
        Function.Surjective (QuotientGroup.mk : ↥L → ↥L ⧸ aschbacherSolvableCore 3 ↥L)).subsingleton
    exact not_subsingleton _ hs
  haveI := hcfg.perfL
  exact Group.IsPerfect.not_isSolvable _ hsolL

section Rows

set_option linter.unusedSectionVars false

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h : 2 * Nat.card (alternatingGroup (Fin 5)) = 120 := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]; rfl
  omega

theorem noncomm_alt_five : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a :=
  ⟨⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨swap 0 1 * swap 1 3, Perm.mem_alternatingGroup.mpr (by decide)⟩, by decide⟩

theorem olRow_alt_five : OLRow (fun T _ => Nonempty (T ≃* alternatingGroup (Fin 5))) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  refine olRow_of_inner _ noncomm_alt_five
    (fun α hα => CFSG.ASVolI.burnsideA315x_alt_odd_inner (Or.inl rfl) hα)
    (fun B V => not_innerCfg_of_not_dvd (by rw [card_alt_five]; norm_num) B V)

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h : 2 * Nat.card (alternatingGroup (Fin 6)) = 720 := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]; rfl
  omega

theorem noncomm_alt_six : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a :=
  ⟨⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨swap 0 1 * swap 1 3, Perm.mem_alternatingGroup.mpr (by decide)⟩, by decide⟩

@[expose] def b0Six : Finset (Perm (Fin 6)) :=
  let a : Perm (Fin 6) := swap 0 1 * swap 1 2
  let b : Perm (Fin 6) := swap 3 4 * swap 4 5
  {1, a, a ^ 2, b, b ^ 2, a * b, a ^ 2 * b, a * b ^ 2, a ^ 2 * b ^ 2}

theorem b0Six_one : (1 : Perm (Fin 6)) ∈ b0Six := by decide +kernel
open scoped CFSG.Decide.Bounded in
theorem b0Six_mul : ∀ x ∈ b0Six, ∀ y ∈ b0Six, x * y ∈ b0Six := by decide +kernel
open scoped CFSG.Decide.Bounded in
theorem b0Six_inv : ∀ x ∈ b0Six, x⁻¹ ∈ b0Six := by decide +kernel
open scoped CFSG.Decide.Bounded in
theorem b0Six_sign : ∀ x ∈ b0Six, Perm.sign x = 1 := by decide +kernel
theorem b0Six_even : ∀ x ∈ b0Six, x ∈ alternatingGroup (Fin 6) := fun x hx =>
  Perm.mem_alternatingGroup.mpr (b0Six_sign x hx)
theorem b0Six_card : b0Six.card = 9 := by decide +kernel

open scoped CFSG.Decide.Bounded in
theorem b0Six_noInv : ∀ x ∈ b0Six, x ≠ 1 → ∀ v : Perm (Fin 6), Perm.sign v = 1 → v ^ 2 = 1 →
    v * x = x * v → v = 1 := by decide +kernel

theorem olRow_alt_six : OLRow (fun T _ => Nonempty (T ≃* alternatingGroup (Fin 6))) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine olRow_of_inner _ noncomm_alt_six
    (fun α hα => CFSG.ASVolI.burnsideA315x_alt6_odd_inner hα) (fun B V hc => ?_)
  set B₀' := finsetSubgroup b0Six b0Six_one b0Six_mul b0Six_inv with hB₀'
  have hB₀A : B₀' ≤ alternatingGroup (Fin 6) := fun x hx => b0Six_even x hx
  set B₀ := B₀'.subgroupOf (alternatingGroup (Fin 6)) with hB₀
  have hB₀card : Nat.card B₀ = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀A).toEquiv, card_finsetSubgroup,
      b0Six_card]
  have h9 : (Nat.card (alternatingGroup (Fin 6))).factorization 3 = 2 := by
    rw [card_alt_six, show (360 : ℕ) = 3 ^ 2 * 40 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨V₀, hc₀⟩ := exists_innerCfg_of_sylow h9 hc B₀ hB₀card
  obtain ⟨b, hbB, hb1, hVb⟩ := hc₀.pt
  obtain ⟨⟨v, hv⟩, hv1⟩ : ∃ v : V₀, v ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton V₀ := ⟨fun x y => (h x).trans (h y).symm⟩
    have := hc₀.klein.card_four
    rw [Nat.card_unique] at this
    omega
  have hv2 : v ^ 2 = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : V₀)
    rw [hc₀.klein.exponent_two] at this
    exact congrArg Subtype.val this
  have hvb : v * b = b * v := Subgroup.mem_centralizer_singleton_iff.mp (hVb hv)
  have key := b0Six_noInv (b : Perm (Fin 6)) hbB (fun h => hb1 (Subtype.ext h)) (v : Perm (Fin 6))
    (Perm.mem_alternatingGroup.mp v.2) (congrArg Subtype.val hv2) (congrArg Subtype.val hvb)
  exact hv1 (Subtype.ext (Subtype.ext key))

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h : 2 * Nat.card (alternatingGroup (Fin 7)) = 5040 := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]; rfl
  omega

theorem noncomm_alt_seven : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a :=
  ⟨⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨swap 0 1 * swap 1 3, Perm.mem_alternatingGroup.mpr (by decide)⟩, by decide⟩

@[expose] def b0Seven : Finset (Perm (Fin 7)) :=
  let a : Perm (Fin 7) := swap 0 1 * swap 1 2
  let b : Perm (Fin 7) := swap 3 4 * swap 4 5
  {1, a, a ^ 2, b, b ^ 2, a * b, a ^ 2 * b, a * b ^ 2, a ^ 2 * b ^ 2}

@[expose] def v1Seven : Finset (Perm (Fin 7)) :=
  {1, swap 3 4 * swap 5 6, swap 3 5 * swap 4 6, swap 3 6 * swap 4 5}

@[expose] def v2Seven : Finset (Perm (Fin 7)) :=
  {1, swap 0 1 * swap 2 6, swap 0 2 * swap 1 6, swap 0 6 * swap 1 2}

set_option maxRecDepth 100000 in
theorem b0Seven_one : (1 : Perm (Fin 7)) ∈ b0Seven := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem b0Seven_mul : ∀ x ∈ b0Seven, ∀ y ∈ b0Seven, x * y ∈ b0Seven := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem b0Seven_inv : ∀ x ∈ b0Seven, x⁻¹ ∈ b0Seven := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem b0Seven_sign : ∀ x ∈ b0Seven, Perm.sign x = 1 := by decide +kernel
theorem b0Seven_even : ∀ x ∈ b0Seven, x ∈ alternatingGroup (Fin 7) := fun x hx =>
  Perm.mem_alternatingGroup.mpr (b0Seven_sign x hx)
set_option maxRecDepth 100000 in
theorem b0Seven_card : b0Seven.card = 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem v1Seven_one : (1 : Perm (Fin 7)) ∈ v1Seven := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem v1Seven_mul : ∀ x ∈ v1Seven, ∀ y ∈ v1Seven, x * y ∈ v1Seven := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem v1Seven_inv : ∀ x ∈ v1Seven, x⁻¹ ∈ v1Seven := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem v1Seven_sign : ∀ x ∈ v1Seven, Perm.sign x = 1 := by decide +kernel
theorem v1Seven_even : ∀ x ∈ v1Seven, x ∈ alternatingGroup (Fin 7) := fun x hx =>
  Perm.mem_alternatingGroup.mpr (v1Seven_sign x hx)
set_option maxRecDepth 100000 in
theorem v1Seven_card : v1Seven.card = 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem v2Seven_one : (1 : Perm (Fin 7)) ∈ v2Seven := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem v2Seven_mul : ∀ x ∈ v2Seven, ∀ y ∈ v2Seven, x * y ∈ v2Seven := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem v2Seven_inv : ∀ x ∈ v2Seven, x⁻¹ ∈ v2Seven := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem v2Seven_sign : ∀ x ∈ v2Seven, Perm.sign x = 1 := by decide +kernel
theorem v2Seven_even : ∀ x ∈ v2Seven, x ∈ alternatingGroup (Fin 7) := fun x hx =>
  Perm.mem_alternatingGroup.mpr (v2Seven_sign x hx)
set_option maxRecDepth 100000 in
theorem v2Seven_card : v2Seven.card = 4 := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem v1Seven_norm : ∀ b ∈ b0Seven, ∀ v ∈ v1Seven, b * v * b⁻¹ ∈ v1Seven := by decide +kernel
set_option maxRecDepth 100000 in
open scoped CFSG.Decide.Bounded in
theorem v2Seven_norm : ∀ b ∈ b0Seven, ∀ v ∈ v2Seven, b * v * b⁻¹ ∈ v2Seven := by decide +kernel
set_option maxRecDepth 100000 in
theorem v1Seven_ne : swap 3 4 * swap 5 6 ∉ v2Seven := by decide +kernel
set_option maxRecDepth 100000 in
theorem v1Seven_mem : swap 3 4 * swap 5 6 ∈ v1Seven := by decide +kernel

theorem mem_invariant_seven {F : Finset (Perm (Fin 7))} (h1 : (1 : Perm (Fin 7)) ∈ F)
    (hmul : ∀ a ∈ F, ∀ b ∈ F, a * b ∈ F) (hinv : ∀ a ∈ F, a⁻¹ ∈ F)
    (heven : ∀ x ∈ F, x ∈ alternatingGroup (Fin 7)) (hcard : F.card = 4)
    (hnorm : ∀ b ∈ b0Seven, ∀ v ∈ F, b * v * b⁻¹ ∈ F) :
    (finsetSubgroup F h1 hmul hinv).subgroupOf (alternatingGroup (Fin 7)) ∈
      invariantPiSubgroups ⊤
        ((finsetSubgroup b0Seven b0Seven_one b0Seven_mul b0Seven_inv).subgroupOf
          (alternatingGroup (Fin 7))) (piCompl 3) := by
  have hle : finsetSubgroup F h1 hmul hinv ≤ alternatingGroup (Fin 7) := fun x hx => heven x hx
  refine ⟨le_top, isPiSubgroup_of_not_dvd ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_finsetSubgroup, hcard]
    norm_num
  · refine le_normalizer_of_conj_mem' fun b hb v hv => ?_
    show ((b * v * b⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ F
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hnorm _ hb _ hv

theorem olRow_alt_seven : OLRow (fun T _ => Nonempty (T ≃* alternatingGroup (Fin 7))) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  refine olRow_of_inner _ noncomm_alt_seven
    (fun α hα => CFSG.ASVolI.burnsideA315x_alt_odd_inner (Or.inr le_rfl) hα) (fun B V hc => ?_)
  set B₀' := finsetSubgroup b0Seven b0Seven_one b0Seven_mul b0Seven_inv with hB₀'
  have hB₀A : B₀' ≤ alternatingGroup (Fin 7) := fun x hx => b0Seven_even x hx
  set B₀ := B₀'.subgroupOf (alternatingGroup (Fin 7)) with hB₀
  have hB₀card : Nat.card B₀ = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀A).toEquiv, card_finsetSubgroup,
      b0Seven_card]
  have h9 : (Nat.card (alternatingGroup (Fin 7))).factorization 3 = 2 := by
    rw [card_alt_seven, show (2520 : ℕ) = 3 ^ 2 * 280 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨V₀, hc₀⟩ := exists_innerCfg_of_sylow h9 hc B₀ hB₀card
  set V₁ := (finsetSubgroup v1Seven v1Seven_one v1Seven_mul v1Seven_inv).subgroupOf
    (alternatingGroup (Fin 7)) with hV₁
  set V₂ := (finsetSubgroup v2Seven v2Seven_one v2Seven_mul v2Seven_inv).subgroupOf
    (alternatingGroup (Fin 7)) with hV₂
  have h1 := hc₀.inv V₁ (mem_invariant_seven v1Seven_one v1Seven_mul v1Seven_inv v1Seven_even
    v1Seven_card v1Seven_norm)
  have h2 := hc₀.inv V₂ (mem_invariant_seven v2Seven_one v2Seven_mul v2Seven_inv v2Seven_even
    v2Seven_card v2Seven_norm)
  have hV₁card : Nat.card V₁ = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun x hx => v1Seven_even x hx)).toEquiv,
      card_finsetSubgroup, v1Seven_card]
  have hV₂card : Nat.card V₂ = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun x hx => v2Seven_even x hx)).toEquiv,
      card_finsetSubgroup, v2Seven_card]
  have he1 : V₁ = V₀ := Subgroup.eq_of_le_of_card_ge h1 (by rw [hc₀.klein.card_four, hV₁card])
  have he2 : V₂ = V₀ := Subgroup.eq_of_le_of_card_ge h2 (by rw [hc₀.klein.card_four, hV₂card])
  have hx : (⟨swap 3 4 * swap 5 6, Perm.mem_alternatingGroup.mpr (by decide)⟩ :
      alternatingGroup (Fin 7)) ∈ V₁ := by
    show swap 3 4 * swap 5 6 ∈ v1Seven
    exact v1Seven_mem
  rw [he1, ← he2] at hx
  exact v1Seven_ne hx

end Rows

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
