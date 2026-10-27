module

public import CFSG.Quasithin.Recognition.St84.Gen.CobCore
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
public import CFSG.Timmesfeld.RankOne.SL2
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

public section

namespace CFSG.Quasithin.St84

open scoped commutatorElement Matrix MatrixGroups

variable {G : Type} [Group G]

private lemma upperElt_conj_apply_one_zero {F : Type} [Field F] [CharP F 2]
    (M : SL(2, F))
    (hU : M * CFSG.Timmesfeld.RankOne.upperElt F 1 * M⁻¹ ∈
      CFSG.Timmesfeld.upperUnipotent F) :
    (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨t, ht⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff F).1 hU
  have h1 : (((M * CFSG.Timmesfeld.RankOne.upperElt F 1 * M⁻¹ :
      SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 1 0 =
      -((M : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [CFSG.Timmesfeld.RankOne.upperElt, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [ht] at h1
  have h2 : -((M : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 = 0 := by
    simpa [CFSG.Timmesfeld.RankOne.upperElt] using h1
  have h3 : ((M : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 = 0 := neg_eq_zero.mp h2
  exact mul_self_eq_zero.mp (by simpa [pow_two] using h3)

private lemma alpha_apply_one_zero_eq_zero {L S T : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)}
    (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hS : (S.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F)
    {k : ↥L} (hkT : (k : G) ∈ T) :
    (α k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have hmemU : CFSG.Timmesfeld.RankOne.upperElt F 1 ∈
      (S.subgroupOf L).map α := by
    rw [hS]
    exact (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff F).2 ⟨1, rfl⟩
  obtain ⟨s, hsS, hαs⟩ := Subgroup.mem_map.mp hmemU
  have hks : k * s * k⁻¹ ∈ S.subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    have hsG : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hsS
    have hconj : (k : G) * (s : G) * (k : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hTS hkT) (s : G)).mp hsG
    simpa using hconj
  have hU' : α (k * s * k⁻¹) ∈ CFSG.Timmesfeld.upperUnipotent F := by
    rw [← hS]
    exact Subgroup.mem_map_of_mem α hks
  have heq : α (k * s * k⁻¹) = α k * CFSG.Timmesfeld.RankOne.upperElt F 1 * (α k)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hαs]
  rw [heq] at hU'
  exact upperElt_conj_apply_one_zero (α k) hU'

private lemma alpha_apply_zero_zero_ne_zero {L S T : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)}
    (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hS : (S.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F)
    {k : ↥L} (hkT : (k : G) ∈ T) :
    (α k : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
  have h10 := alpha_apply_one_zero_eq_zero hTS hS hkT
  have hdet : (α k : Matrix (Fin 2) (Fin 2) F).det = 1 := (α k).2
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact left_ne_zero_of_mul_eq_one hdet

private lemma alpha_apply_zero_zero_mul {L S T : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)}
    (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hS : (S.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F)
    {k l : ↥L} (hkT : (k : G) ∈ T) (hlT : (l : G) ∈ T) :
    (α (k * l) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (α k : Matrix (Fin 2) (Fin 2) F) 0 0 * (α l : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  have h10l := alpha_apply_one_zero_eq_zero hTS hS hlT
  rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [h10l]

private lemma upper_inv_apply {F : Type} [Field F] (A : SL(2, F))
    (h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        ((A : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ ∧
      ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  constructor
  · rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [h10, neg_zero]
    exact eq_inv_of_mul_eq_one_right hdet
  · rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [h10]

private noncomputable def torusChar {L S T : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)}
    (hTL : T ≤ L) (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hS : (S.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F) :
    ↥T →* Fˣ where
  toFun k := Units.mk0 ((α (Subgroup.inclusion hTL k) : Matrix (Fin 2) (Fin 2) F) 0 0)
    (alpha_apply_zero_zero_ne_zero hTS hS (by simpa using k.2))
  map_one' := by
    apply Units.ext
    simp
  map_mul' k l := by
    apply Units.ext
    change (α (Subgroup.inclusion hTL (k * l)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (α (Subgroup.inclusion hTL k) : Matrix (Fin 2) (Fin 2) F) 0 0 *
        (α (Subgroup.inclusion hTL l) : Matrix (Fin 2) (Fin 2) F) 0 0
    rw [map_mul (Subgroup.inclusion hTL)]
    exact alpha_apply_zero_zero_mul hTS hS (by simpa using k.2) (by simpa using l.2)

private lemma torusChar_eq_one {L Q S T : Subgroup G} [Finite ↥L]
    {F : Type} [Field F] [CharP F 2] {n : ℕ} {α : ↥L →* SL(2, F)}
    (hker : α.ker = Q.subgroupOf L) (hTL : T ≤ L) (hTQ : T ⊓ Q = ⊥)
    (hT : Nat.card ↥T = 2 ^ n - 1)
    (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hS : (S.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F)
    (k : ↥T)
    (h00 : (α (Subgroup.inclusion hTL k) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1) : k = 1 := by
  classical
  haveI : Finite ↥T := Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  haveI : Nonempty ↥T := ⟨1⟩
  have h10 : (α (Subgroup.inclusion hTL k) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    alpha_apply_one_zero_eq_zero hTS hS (by simpa using k.2)
  have h11 : (α (Subgroup.inclusion hTL k) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have hdet : (α (Subgroup.inclusion hTL k) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
      (α (Subgroup.inclusion hTL k)).2
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero, h00, one_mul] at hdet
    exact hdet
  have hα : α (Subgroup.inclusion hTL k) =
      CFSG.Timmesfeld.RankOne.upperElt F
        ((α (Subgroup.inclusion hTL k) : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.Timmesfeld.RankOne.upperElt, h00, h10, h11]
  have hsq : (α (Subgroup.inclusion hTL k)) ^ 2 = 1 := by
    rw [hα, pow_two, CFSG.Timmesfeld.RankOne.upperElt_mul,
      CharTwo.add_self_eq_zero, CFSG.Timmesfeld.RankOne.upperElt_zero]
  have hm_odd : Odd (Nat.card ↥T) := by
    rw [hT]
    have hpos : 0 < 2 ^ n - 1 := by
      have h := Nat.card_pos (α := ↥T)
      rwa [hT] at h
    have hn0 : n ≠ 0 := by
      intro hn
      rw [hn, pow_zero] at hpos
      omega
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow).mpr ⟨even_two, hn0⟩) odd_one
  have hkpowT : (k : ↥T) ^ Nat.card ↥T = 1 := pow_card_eq_one'
  have hkpowL : (Subgroup.inclusion hTL k) ^ Nat.card ↥T = 1 := by
    rw [← map_pow, hkpowT, map_one]
  have hαpow : (α (Subgroup.inclusion hTL k)) ^ Nat.card ↥T = 1 := by
    rw [← map_pow, hkpowL, map_one]
  have hα1 : α (Subgroup.inclusion hTL k) = 1 := by
    have hpow : (α (Subgroup.inclusion hTL k)) ^ Nat.card ↥T =
        α (Subgroup.inclusion hTL k) := by
      obtain ⟨r, hr⟩ := hm_odd
      rw [hr, pow_add, pow_mul, hsq, one_pow, one_mul, pow_one]
    exact hpow.symm.trans hαpow
  have hkQ : ((Subgroup.inclusion hTL k : ↥L) : G) ∈ Q := by
    have hmem : Subgroup.inclusion hTL k ∈ α.ker := by
      rw [MonoidHom.mem_ker]
      exact hα1
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hkbot : (k : G) ∈ (⊥ : Subgroup G) := by
    have hmem : (k : G) ∈ T ⊓ Q :=
      ⟨by simpa using k.2, by simpa using hkQ⟩
    rwa [hTQ] at hmem
  exact Subtype.ext (Subgroup.mem_bot.mp hkbot)

private lemma torusChar_injective {L Q S T : Subgroup G} [Finite ↥L]
    {F : Type} [Field F] [CharP F 2] {n : ℕ} {α : ↥L →* SL(2, F)}
    (hker : α.ker = Q.subgroupOf L) (hTL : T ≤ L) (hTQ : T ⊓ Q = ⊥)
    (hT : Nat.card ↥T = 2 ^ n - 1)
    (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hS : (S.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F) :
    Function.Injective (torusChar hTL hTS hS) := by
  classical
  intro k l hkl
  have h00 : (α (Subgroup.inclusion hTL k) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (α (Subgroup.inclusion hTL l) : Matrix (Fin 2) (Fin 2) F) 0 0 :=
    congrArg Units.val hkl
  have h10l : (α (Subgroup.inclusion hTL l) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    alpha_apply_one_zero_eq_zero hTS hS (by simpa using l.2)
  have hinv := upper_inv_apply (α (Subgroup.inclusion hTL l)) h10l
  let m : ↥T := k * l⁻¹
  have hm00 : (α (Subgroup.inclusion hTL m) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have hmul : Subgroup.inclusion hTL m =
        Subgroup.inclusion hTL k * (Subgroup.inclusion hTL l)⁻¹ := by
      simp [m, map_mul]
    rw [hmul, map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, hinv.1, hinv.2, mul_zero, add_zero, h00,
      mul_inv_cancel₀]
    · exact (alpha_apply_zero_zero_ne_zero hTS hS (by simpa using l.2))
  have hm1 : m = 1 :=
    torusChar_eq_one hker hTL hTQ hT hTS hS m hm00
  exact mul_inv_eq_one.mp hm1

theorem exists_mem_upper_diag_eq {L Q T S : Subgroup G} [Finite ↥L]
    {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* SL(2, F)} (hker : α.ker = Q.subgroupOf L) (hTL : T ≤ L) (hSL : S ≤ L)
    (hTQ : T ⊓ Q = ⊥) (hT : Nat.card ↥T = 2 ^ n - 1)
    (hS : (S.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) :
    ∀ c : F, c ≠ 0 → ∃ k : ↥L, (k : G) ∈ T ∧
      (α k : Matrix (Fin 2) (Fin 2) F) 0 0 = c ∧ (α k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  classical
  haveI : Finite ↥T := Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  haveI : Fintype ↥T := Fintype.ofFinite _
  haveI : Fintype Fˣ := Fintype.ofFinite _
  let φ : ↥T →* Fˣ := torusChar hTL hTS hS
  have hφ_inj : Function.Injective φ := torusChar_injective hker hTL hTQ hT hTS hS
  have hcardT : Nat.card ↥T = 2 ^ n - 1 := hT
  have hcardU : Nat.card Fˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hF]
  have hcard : Fintype.card ↥T = Fintype.card Fˣ := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardT, hcardU]
  let e : ↥T ≃ Fˣ := Fintype.equivOfCardEq hcard
  have hφ_surj : Function.Surjective φ :=
    (Finite.injective_iff_surjective_of_equiv e).mp hφ_inj
  intro c hc
  obtain ⟨k, hk⟩ := hφ_surj (Units.mk0 c hc)
  refine ⟨Subgroup.inclusion hTL k, by simpa using k.2, ?_, ?_⟩
  · have := congrArg Units.val hk
    simpa [φ, torusChar, Units.val_mk0] using this
  · exact alpha_apply_one_zero_eq_zero hTS hS (by simpa using k.2)

open Multiplicative

private def line (F : Type) [Field F] : AddSubgroup (Fin 2 → F) where
  carrier := {w | w 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    show a 1 + b 1 = 0
    rw [ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    show -a 1 = 0
    rw [ha, neg_zero]

private noncomputable def lineEquiv (F : Type) [Field F] :
    {w : Fin 2 → F // w 1 = 0} ≃ F where
  toFun w := w.1 0
  invFun a := ⟨![a, 0], by simp⟩
  left_inv w := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simp
    · exact w.2.symm
  right_inv a := by simp

private lemma natCard_line (F : Type) [Field F] :
    Nat.card ↥(line F) = Nat.card F :=
  Nat.card_congr (lineEquiv F)

private lemma upperElt_mulVec {F : Type} [Field F] (t : F) (w : Fin 2 → F) :
    (CFSG.Timmesfeld.RankOne.upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ w =
      ![w 0 + t * w 1, w 1] := by
  ext i
  fin_cases i <;>
    simp [CFSG.Timmesfeld.RankOne.upperElt, Matrix.mulVec, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail]

private lemma one_add_upperElt_mulVec {F : Type} [Field F] [CharP F 2]
    (t : F) (w : Fin 2 → F) :
    ((1 : Matrix (Fin 2) (Fin 2) F) +
        (CFSG.Timmesfeld.RankOne.upperElt F t : Matrix (Fin 2) (Fin 2) F)) *ᵥ w =
      ![t * w 1, 0] := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, upperElt_mulVec]
  ext i
  fin_cases i
  · show w 0 + (w 0 + t * w 1) = t * w 1
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · show w 1 + w 1 = 0
    exact CharTwo.add_self_eq_zero (w 1)

private lemma eq_line_of_card_of_invariant {F : Type} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hF : Fintype.card F = 2 ^ n) (W : AddSubgroup (Fin 2 → F))
    (hcard : Nat.card ↥W = 2 ^ n)
    (hinv : ∀ w ∈ W, ∀ t : F,
      (CFSG.Timmesfeld.RankOne.upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ w ∈ W) :
    W = line F := by
  classical
  haveI : Finite F := Finite.of_fintype F
  haveI : Finite ↥W := Finite.of_injective (fun w : ↥W => (w : Fin 2 → F))
    Subtype.val_injective
  have hline_card : Nat.card ↥(line F) = 2 ^ n := by
    rw [natCard_line, Nat.card_eq_fintype_card, hF]
  have hle : W ≤ line F := by
    intro w hw
    by_contra hwline
    have hw1 : w 1 ≠ 0 := by simpa [line] using hwline
    let f : F → ↥W := fun t =>
      ⟨(CFSG.Timmesfeld.RankOne.upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ w,
        hinv w hw t⟩
    have hf_inj : Function.Injective f := by
      intro s t hst
      have hst' : (CFSG.Timmesfeld.RankOne.upperElt F s : Matrix (Fin 2) (Fin 2) F) *ᵥ w =
          (CFSG.Timmesfeld.RankOne.upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ w :=
        congrArg Subtype.val hst
      have h0 := congrFun hst' 0
      rw [upperElt_mulVec, upperElt_mulVec] at h0
      change w 0 + s * w 1 = w 0 + t * w 1 at h0
      have h : s * w 1 = t * w 1 := by linear_combination h0
      exact mul_right_cancel₀ hw1 h
    haveI : Fintype ↥W := Fintype.ofFinite _
    have hcardW : Fintype.card ↥W = 2 ^ n := by
      rw [Fintype.card_eq_nat_card, hcard]
    have hcardF : Fintype.card F = Fintype.card ↥W := by
      rw [hcardW, hF]
    let e : F ≃ ↥W := Fintype.equivOfCardEq hcardF
    have hf_surj : Function.Surjective f :=
      (Finite.injective_iff_surjective_of_equiv e).mp hf_inj
    obtain ⟨t, ht⟩ := hf_surj 0
    have h1 : w 1 = 0 := by
      have hvec : (CFSG.Timmesfeld.RankOne.upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ w = 0 :=
        congrArg Subtype.val ht
      have h := congrFun hvec 1
      rw [upperElt_mulVec] at h
      simpa using h
    exact hw1 h1
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [hline_card, hcard])

private noncomputable def conjQ {L Q : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (a : ↥L) (x : ↥Q) : ↥Q :=
  ⟨(a : G) * (x : G) * (a : G)⁻¹, by
    have hnormal : (Q.subgroupOf L).Normal := hker ▸ MonoidHom.normal_ker α
    have hmem : a * (⟨(x : G), hQL x.2⟩ : ↥L) * a⁻¹ ∈ Q.subgroupOf L :=
      hnormal.conj_mem ⟨(x : G), hQL x.2⟩ x.2 a
    exact Subgroup.mem_subgroupOf.mp (by simpa using hmem)⟩

private lemma conjQ_coe {L Q : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (a : ↥L) (x : ↥Q) :
    (conjQ hQL hker a x : G) = (a : G) * (x : G) * (a : G)⁻¹ := rfl

private noncomputable def commQ {L Q : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (a : ↥L) (x : ↥Q) : ↥Q :=
  ⟨⁅(x : G), (a : G)⁆, by
    have hconj : (a : G) * (x : G) * (a : G)⁻¹ ∈ Q := (conjQ (L := L) (Q := Q) hQL hker a x).2
    have h : (x : G) * ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ ∈ Q :=
      Q.mul_mem x.2 (Q.inv_mem hconj)
    simpa [commutatorElement_def, mul_assoc] using h⟩

private lemma commQ_coe {L Q : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (a : ↥L) (x : ↥Q) :
    (commQ (L := L) (Q := Q) hQL hker a x : G) = ⁅(x : G), (a : G)⁆ := rfl

private lemma b2_eq_zero_iff {Q V : Subgroup G} {F : Type} [Field F]
    {β₂ : ↥Q →* Multiplicative (Fin 2 → F)} (hker : β₂.ker = V.subgroupOf Q)
    (x : ↥Q) : toAdd (β₂ x) = 0 ↔ (x : G) ∈ V := by
  rw [toAdd_eq_zero, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

private lemma b1_eq_zero_iff {V Z : Subgroup G} {F : Type} [Field F]
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)} (hker : β₁.ker = Z.subgroupOf V)
    (x : ↥V) : toAdd (β₁ x) = 0 ↔ (x : G) ∈ Z := by
  rw [toAdd_eq_zero, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

private lemma b2_conj {L Q : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (a : ↥L) (x : ↥Q) :
    toAdd (β₂ (conjQ hQL hker a x)) =
      (α a : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ x) :=
  hβ₂eq a x (conjQ hQL hker a x) (by rw [conjQ_coe]; rfl)

private lemma b1_conj {L V : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (a : ↥L) (x : ↥V) (hx : (a : G) * (x : G) * (a : G)⁻¹ ∈ V) :
    toAdd (β₁ ⟨(a : G) * (x : G) * (a : G)⁻¹, hx⟩) =
      (α a : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ x) :=
  hβ₁eq a x ⟨_, hx⟩ rfl

private lemma neg_mulVec_eq_self {F : Type} [Field F] [CharP F 2]
    (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) : -(A *ᵥ v) = A *ᵥ v := by
  rw [← Matrix.neg_mulVec]
  congr 1
  ext i j
  simp [CharTwo.neg_eq]

private lemma b2_comm {L Q : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (a : ↥L) (x : ↥Q) :
    toAdd (β₂ (commQ (L := L) (Q := Q) hQL hker a x)) =
      ((1 : Matrix (Fin 2) (Fin 2) F) + (α a : Matrix (Fin 2) (Fin 2) F)) *ᵥ
        toAdd (β₂ x) := by
  have hconj := b2_conj (L := L) (Q := Q) hQL hker hβ₂eq a x
  have hprod : commQ (L := L) (Q := Q) hQL hker a x = x * (conjQ hQL hker a x)⁻¹ := by
    apply Subtype.ext
    rw [commQ_coe]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjQ_coe, commutatorElement_def]
    group
  rw [hprod, map_mul, map_inv, toAdd_mul, toAdd_inv, hconj,
    Matrix.add_mulVec, Matrix.one_mulVec, neg_mulVec_eq_self]

private noncomputable def commOf {L E : Subgroup G}
    (hE : ∀ a : ↥L, ∀ x : ↥E, (a : G) * (x : G) * (a : G)⁻¹ ∈ E)
    (a : ↥L) (x : ↥E) : ↥E :=
  ⟨⁅(x : G), (a : G)⁆, by
    have hconj := hE a x
    have h : (x : G) * ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ ∈ E :=
      E.mul_mem x.2 (E.inv_mem hconj)
    simpa [commutatorElement_def, mul_assoc] using h⟩

private lemma commOf_coe {L E : Subgroup G}
    (hE : ∀ a : ↥L, ∀ x : ↥E, (a : G) * (x : G) * (a : G)⁻¹ ∈ E)
    (a : ↥L) (x : ↥E) : (commOf hE a x : G) = ⁅(x : G), (a : G)⁆ := rfl

private noncomputable def conjOf {L E : Subgroup G}
    (hE : ∀ a : ↥L, ∀ x : ↥E, (a : G) * (x : G) * (a : G)⁻¹ ∈ E)
    (a : ↥L) (x : ↥E) : ↥E :=
  ⟨(a : G) * (x : G) * (a : G)⁻¹, hE a x⟩

private lemma conjOf_coe {L E : Subgroup G}
    (hE : ∀ a : ↥L, ∀ x : ↥E, (a : G) * (x : G) * (a : G)⁻¹ ∈ E)
    (a : ↥L) (x : ↥E) :
    (conjOf hE a x : G) = (a : G) * (x : G) * (a : G)⁻¹ := rfl

private lemma b1_comm {L V : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (a : ↥L) (x : ↥V) :
    toAdd (β₁ (commOf (L := L) (E := V) hVconj a x)) =
      ((1 : Matrix (Fin 2) (Fin 2) F) + (α a : Matrix (Fin 2) (Fin 2) F)) *ᵥ
        toAdd (β₁ x) := by
  have hconj := b1_conj hβ₁eq a x (hVconj a x)
  have hprod : commOf (L := L) (E := V) hVconj a x =
      x * (⟨(a : G) * (x : G) * (a : G)⁻¹, hVconj a x⟩ : ↥V)⁻¹ := by
    apply Subtype.ext
    rw [commOf_coe]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [hprod, map_mul, map_inv, toAdd_mul, toAdd_inv, hconj,
    Matrix.add_mulVec, Matrix.one_mulVec, neg_mulVec_eq_self]

private noncomputable def PImage {Q P : Subgroup G} {F : Type} [Field F]
    (β₂ : ↥Q →* Multiplicative (Fin 2 → F)) : AddSubgroup (Fin 2 → F) where
  carrier := {w | ∃ x : ↥Q, (x : G) ∈ P ∧ toAdd (β₂ x) = w}
  zero_mem' := ⟨1, by simpa using P.one_mem, by simp⟩
  add_mem' := by
    rintro w₁ w₂ ⟨x, hxP, rfl⟩ ⟨y, hyP, rfl⟩
    refine ⟨x * y, ?_, ?_⟩
    · simpa using P.mul_mem hxP hyP
    · rw [map_mul, toAdd_mul]
  neg_mem' := by
    rintro w ⟨x, hxP, rfl⟩
    refine ⟨x⁻¹, ?_, ?_⟩
    · simpa using P.inv_mem hxP
    · rw [map_inv, toAdd_inv]

private lemma natCard_map_P {Q P V : Subgroup G} {F : Type} [Field F]
    {β₂ : ↥Q →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hVP : V ≤ P) (hPQ : P ≤ Q) :
    Nat.card ↥((P.subgroupOf Q).map β₂) = V.relIndex P := by
  classical
  let f : ↥(P.subgroupOf Q) →* Multiplicative (Fin 2 → F) :=
    β₂.comp (P.subgroupOf Q).subtype
  have hker : f.ker = (V.subgroupOf Q).subgroupOf (P.subgroupOf Q) := by
    ext x
    change β₂ (x : ↥Q) = 1 ↔ ((x : ↥Q) : G) ∈ V
    rw [← MonoidHom.mem_ker, hβ₂ker, Subgroup.mem_subgroupOf]
  have hrange : f.range = (P.subgroupOf Q).map β₂ := by
    rw [show f = β₂.comp (P.subgroupOf Q).subtype from rfl, MonoidHom.range_comp,
      Subgroup.range_subtype]
  have hsub : (V.subgroupOf Q).subgroupOf (P.subgroupOf Q) =
      (V.subgroupOf P).comap (Subgroup.subgroupOfEquivOfLe hPQ).toMonoidHom := by
    ext x
    exact Iff.rfl
  have hindex : f.ker.index = (V.subgroupOf P).index := by
    simpa [hker, hsub] using (Subgroup.index_comap_of_surjective (H := V.subgroupOf P)
      (f := (Subgroup.subgroupOfEquivOfLe hPQ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPQ).surjective)
  calc
    Nat.card ↥((P.subgroupOf Q).map β₂) = Nat.card ↥f.range := by rw [hrange]
    _ = f.ker.index := (Subgroup.index_ker f).symm
    _ = (V.subgroupOf P).index := hindex
    _ = V.relIndex P := rfl

private lemma natCard_PImage {Q P V : Subgroup G} {F : Type} [Field F]
    {β₂ : ↥Q →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hVP : V ≤ P) (hPQ : P ≤ Q) :
    Nat.card ↥(PImage (P := P) β₂) = V.relIndex P := by
  classical
  let Wm : Subgroup (Multiplicative (Fin 2 → F)) := (P.subgroupOf Q).map β₂
  calc
    Nat.card ↥(PImage (P := P) β₂) = Nat.card ↥Wm :=
      Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun w => by
        constructor
        · rintro ⟨x, hxP, rfl⟩
          exact ⟨x, hxP, rfl⟩
        · rintro ⟨x, hxP, hxw⟩
          exact ⟨x, hxP, by rw [hxw, toAdd_ofAdd]⟩))
    _ = V.relIndex P := natCard_map_P hβ₂ker hVP hPQ

private lemma PImage_eq_line {L Q V P A : Subgroup G} {F : Type}
    [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hVP : V ≤ P) (hPQ : P ≤ Q) (hPV : V.relIndex P = 2 ^ n)
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hsurjA : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t) :
    PImage (P := P) β₂ = line F := by
  classical
  have hcard : Nat.card ↥(PImage (P := P) β₂) = 2 ^ n := by
    rw [natCard_PImage hβ₂ker hVP hPQ, hPV]
  refine eq_line_of_card_of_invariant hF (PImage (P := P) β₂) hcard ?_
  intro w hw t
  obtain ⟨x, hxP, rfl⟩ := hw
  obtain ⟨a, haα⟩ := hsurjA t
  have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp a.2
  have hconjP : (a : G) * (x : G) * (a : G)⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hAP haA) (x : G)).mp hxP
  let y : ↥Q := conjQ hQL hker a x
  have hyP : (y : G) ∈ P := by
    rw [conjQ_coe]
    exact hconjP
  have hβy : toAdd (β₂ y) =
      (α a : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ x) :=
    b2_conj (L := L) (Q := Q) hQL hker hβ₂eq a x
  have hmem : (CFSG.Timmesfeld.RankOne.upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ
      toAdd (β₂ x) ∈ PImage (P := P) β₂ := by
    rw [← haα, ← hβy]
    exact ⟨y, hyP, rfl⟩
  simpa using hmem

private lemma b2_coord_zero_of_mem_P {Q P V : Subgroup G} {F : Type} [Field F]
    {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hW : PImage (P := P) β₂ = line F) {x : ↥Q} (hxP : (x : G) ∈ P) :
    toAdd (β₂ x) 1 = 0 := by
  have hmem : toAdd (β₂ x) ∈ PImage (P := P) β₂ := ⟨x, hxP, rfl⟩
  rw [hW] at hmem
  exact hmem

private lemma mem_P_of_b2_coord_zero {Q P V : Subgroup G} {F : Type} [Field F]
    {β₂ : ↥Q →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hVP : V ≤ P) (hW : PImage (P := P) β₂ = line F) {x : ↥Q}
    (hx : toAdd (β₂ x) 1 = 0) : (x : G) ∈ P := by
  have hline : toAdd (β₂ x) ∈ line F := hx
  rw [← hW] at hline
  obtain ⟨y, hyP, hyx⟩ := hline
  have hzero : toAdd (β₂ (y⁻¹ * x)) = 0 := by
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hyx, neg_add_cancel]
  have hV : ((y⁻¹ * x : ↥Q) : G) ∈ V :=
    (b2_eq_zero_iff hβ₂ker (y⁻¹ * x)).mp hzero
  have hP : ((y⁻¹ * x : ↥Q) : G) ∈ P := hVP hV
  have hxeq : (x : G) = (y : G) * ((y⁻¹ * x : ↥Q) : G) := by
    simp [mul_assoc]
  rw [hxeq]
  exact P.mul_mem hyP hP

private lemma alpha_inj_on_A {L Q A : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} (hker : α.ker = Q.subgroupOf L) (hAQ : A ⊓ Q = ⊥) :
    Function.Injective (fun a : A.subgroupOf L => α a) := by
  intro a b hab
  have hab' : α (a : ↥L) = α (b : ↥L) := hab
  have hmem : ((a * b⁻¹ : A.subgroupOf L) : ↥L) ∈ α.ker := by
    rw [MonoidHom.mem_ker]
    change α ((a : ↥L) * (b : ↥L)⁻¹) = 1
    rw [map_mul, map_inv, hab', mul_inv_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  have hA : ((a * b⁻¹ : A.subgroupOf L) : G) ∈ A := (a * b⁻¹).2
  have hbot : ((a * b⁻¹ : A.subgroupOf L) : G) ∈ (⊥ : Subgroup G) := by
    have : ((a * b⁻¹ : A.subgroupOf L) : G) ∈ A ⊓ Q := ⟨hA, hmem⟩
    rwa [hAQ] at this
  have h1 : ((a * b⁻¹ : A.subgroupOf L) : G) = 1 := Subgroup.mem_bot.mp hbot
  have h1L : (a * b⁻¹ : A.subgroupOf L) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  exact mul_inv_eq_one.mp h1L

private lemma map_alpha_A_eq_upperUnipotent {L Q A : Subgroup G} {F : Type}
    [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* SL(2, F)} (hker : α.ker = Q.subgroupOf L) (hAL : A ≤ L)
    (hAQ : A ⊓ Q = ⊥) (hA : Nat.card ↥A = 2 ^ n)
    (hAU : (A.subgroupOf L).map α ≤ CFSG.Timmesfeld.upperUnipotent F) :
    (A.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F := by
  have hinj : Function.Injective (fun a : A.subgroupOf L => α a) :=
    alpha_inj_on_A hker hAQ
  have hinj' : Function.Injective (α.domRestrict (A.subgroupOf L)) := by
    intro a b hab
    exact hinj hab
  have hcard_map : Nat.card ↥((A.subgroupOf L).map α) = Nat.card ↥(A.subgroupOf L) := by
    rw [← MonoidHom.domRestrict_range (f := α)]
    rw [← Subgroup.map_top (α.domRestrict (A.subgroupOf L))]
    rw [Subgroup.card_map_of_injective (K := ⊤) hinj']
    exact Nat.card_congr (Subgroup.topEquiv).toEquiv
  have hcard_A : Nat.card ↥(A.subgroupOf L) = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA]
  have hcard_U : Nat.card ↥(CFSG.Timmesfeld.upperUnipotent F) = 2 ^ n := by
    rw [CFSG.Timmesfeld.RankOne.card_upperUnipotent, Nat.card_eq_fintype_card, hF]
  exact Subgroup.eq_of_le_of_card_ge hAU (by rw [hcard_U, hcard_map, hcard_A])

private noncomputable def zeta {L A : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)}
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t) (t : F) : A.subgroupOf L :=
  Classical.choose (hsurj t)

private lemma zeta_spec {L A : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)}
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t) (t : F) :
    α (zeta hsurj t) = CFSG.Timmesfeld.RankOne.upperElt F t :=
  Classical.choose_spec (hsurj t)

private lemma zeta_add {L A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)}
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t) (s t : F) :
    zeta hsurj (s + t) = zeta hsurj s * zeta hsurj t := by
  apply hinj
  change α (zeta hsurj (s + t)) = α (zeta hsurj s * zeta hsurj t)
  rw [zeta_spec, map_mul, zeta_spec, zeta_spec,
    CFSG.Timmesfeld.RankOne.upperElt_mul]

private lemma zeta_zero {L A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)}
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t) :
    zeta hsurj 0 = 1 := by
  apply hinj
  change α (zeta hsurj 0) = α 1
  rw [zeta_spec, CFSG.Timmesfeld.RankOne.upperElt_zero, map_one]

private lemma zeta_surj {L A : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)}
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hAU_eq : (A.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F)
    (a : A.subgroupOf L) : ∃ t : F, zeta hsurj t = a := by
  have hmem : α a ∈ CFSG.Timmesfeld.upperUnipotent F := by
    rw [← hAU_eq]
    exact Subgroup.mem_map_of_mem α a.2
  obtain ⟨t, ht⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff F).1 hmem
  refine ⟨t, ?_⟩
  apply hinj
  change α (zeta hsurj t) = α a
  rw [zeta_spec, ht]

private lemma mem_V_conj {L Q V : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L) (hVQ : V ≤ Q)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (a : ↥L) (v : ↥V) : (a : G) * (v : G) * (a : G)⁻¹ ∈ V := by
  let vQ : ↥Q := ⟨(v : G), hVQ v.2⟩
  have hvQ : toAdd (β₂ vQ) = 0 := (b2_eq_zero_iff hβ₂ker vQ).mpr v.2
  have hconjQ : (a : G) * (v : G) * (a : G)⁻¹ ∈ Q := (conjQ hQL hker a vQ).2
  have hzero : toAdd (β₂ (conjQ hQL hker a vQ)) = 0 := by
    rw [b2_conj hQL hker hβ₂eq a vQ, hvQ, Matrix.mulVec_zero]
  exact (b2_eq_zero_iff hβ₂ker (conjQ hQL hker a vQ)).mp hzero

private lemma add_neg_mulVec_eq_one_add {F : Type} [Field F] [CharP F 2]
    (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    v + -(A *ᵥ v) = ((1 : Matrix (Fin 2) (Fin 2) F) + A) *ᵥ v := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, neg_mulVec_eq_self]

private lemma commPV_mem_V {L Q V P A : Subgroup G} {F : Type}
    [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    {x : ↥Q} (hxP : (x : G) ∈ P) {a : ↥L} (t : F)
    (ha : α a = CFSG.Timmesfeld.RankOne.upperElt F t) :
    ⁅(x : G), (a : G)⁆ ∈ V := by
  have hconjQ : (a : G) * (x : G) * (a : G)⁻¹ ∈ Q := (conjQ (L := L) (Q := Q) hQL hker a x).2
  have hmemQ : ⁅(x : G), (a : G)⁆ ∈ Q := by
    have h : (x : G) * ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ ∈ Q :=
      Q.mul_mem x.2 (Q.inv_mem hconjQ)
    simpa [commutatorElement_def, mul_assoc] using h
  let c : ↥Q := ⟨⁅(x : G), (a : G)⁆, hmemQ⟩
  have hcomm_eq : c = x * (⟨(a : G) * (x : G) * (a : G)⁻¹, hconjQ⟩ : ↥Q)⁻¹ := by
    apply Subtype.ext
    simp only [c, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  have hconj_val : (⟨(a : G) * (x : G) * (a : G)⁻¹, hconjQ⟩ : ↥Q) =
      conjQ (L := L) (Q := Q) hQL hker a x := by
    apply Subtype.ext
    rfl
  have hmem : (c : G) ∈ V := (b2_eq_zero_iff (Q := Q) (V := V) hβ₂ker c).mp (by
    rw [hcomm_eq, map_mul, map_inv, toAdd_mul, toAdd_inv, hconj_val,
      b2_conj (L := L) (Q := Q) hQL hker hβ₂eq a x, ha,
      add_neg_mulVec_eq_one_add, one_add_upperElt_mulVec,
      b2_coord_zero_of_mem_P (Q := Q) (P := P) (V := V) hW hxP]
    simp)
  simpa [c] using hmem

private noncomputable def commPV {L Q V P A : Subgroup G} {F : Type}
    [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (x : ↥Q) (hxP : (x : G) ∈ P) (t : F) : ↥V :=
  (⟨⁅(x : G), ((zeta hsurj t : A.subgroupOf L) : G)⁆,
    commPV_mem_V (A := A) hQL hker hβ₂ker hβ₂eq hW hxP t (zeta_spec hsurj t)⟩ : ↥V)

private lemma commPV_coe {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (x : ↥Q) (hxP : (x : G) ∈ P) (t : F) :
    (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t : G) =
      ⁅(x : G), ((zeta hsurj t : A.subgroupOf L) : G)⁆ := rfl

private noncomputable def cocycleG {L Q V P A : Subgroup G} {F : Type}
    [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (x : ↥Q) (hxP : (x : G) ∈ P) (t : F) : Fin 2 → F :=
  toAdd (β₁ (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t))

private noncomputable def fCocycle {L Q V P A : Subgroup G} {F : Type}
    [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (x : ↥Q) (hxP : (x : G) ∈ P) (t : F) : F :=
  cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t 0

private lemma b1_conjOf {L V : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (a : ↥L) (x : ↥V) :
    toAdd (β₁ (conjOf (L := L) (E := V) hVconj a x)) =
      (α a : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ x) :=
  b1_conj hβ₁eq a x (hVconj a x)

private lemma cocycleG_add {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    {x : ↥Q} (hxP : (x : G) ∈ P) (s t : F) :
    cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP (s + t) =
      cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP s +
        (CFSG.Timmesfeld.RankOne.upperElt F s : Matrix (Fin 2) (Fin 2) F) *ᵥ
          cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t := by
  have ha_st : ((zeta hsurj (s + t) : A.subgroupOf L) : ↥L) =
      ((zeta hsurj s : A.subgroupOf L) : ↥L) *
        ((zeta hsurj t : A.subgroupOf L) : ↥L) := by
    rw [zeta_add hinj hsurj s t]
    rfl
  have hconj : commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP (s + t) =
      commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP s *
        conjOf (L := L) (E := V) hVconj
          ((zeta hsurj s : A.subgroupOf L) : ↥L)
          (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t) := by
    apply Subtype.ext
    rw [commPV_coe]
    simp only [Subgroup.coe_mul]
    rw [commPV_coe, conjOf_coe, commPV_coe, ha_st]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [cocycleG, hconj, map_mul, toAdd_mul]
  congr 1
  rw [b1_conjOf (L := L) (V := V) hβ₁eq hVconj
    ((zeta hsurj s : A.subgroupOf L) : ↥L)
    (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t), zeta_spec]
  rfl

private lemma cocycleG_zero {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    {x : ↥Q} (hxP : (x : G) ∈ P) :
    cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP 0 = 0 := by
  rw [cocycleG]
  have hz : ((zeta hsurj 0 : A.subgroupOf L) : G) = 1 := by
    rw [zeta_zero hinj hsurj]
    rfl
  have hcomm : commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP 0 = 1 := by
    apply Subtype.ext
    show (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP 0 : G) = 1
    rw [commPV_coe, hz]
    simp [commutatorElement_def]
  rw [hcomm, map_one]
  rfl

private lemma cocycleG_second_zero {L Q V P A : Subgroup G} {F : Type}
    [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    {x : ↥Q} (hxP : (x : G) ∈ P) (t : F) :
    cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t 1 = 0 := by
  have h := cocycleG_add hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq hVconj hxP t t
  rw [CharTwo.add_self_eq_zero, cocycleG_zero (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hxP] at h
  have h' : ((1 : Matrix (Fin 2) (Fin 2) F) +
      (CFSG.Timmesfeld.RankOne.upperElt F t : Matrix (Fin 2) (Fin 2) F)) *ᵥ
      cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t = 0 := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    exact h.symm
  have h0 : t * (cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t 1) = 0 := by
    have h'' : ![t * (cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t 1), 0] = 0 := by
      rwa [one_add_upperElt_mulVec] at h'
    exact congrFun h'' 0
  by_cases ht : t = 0
  · rw [ht, cocycleG_zero (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hxP]
    rfl
  · exact (mul_eq_zero.mp h0).resolve_left ht

private lemma fCocycle_add {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    {x : ↥Q} (hxP : (x : G) ∈ P) (s t : F) :
    fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP (s + t) =
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP s +
        fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t := by
  have h := cocycleG_add hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq hVconj hxP s t
  have hsec := cocycleG_second_zero hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq
    hVconj hxP t
  have hU : (CFSG.Timmesfeld.RankOne.upperElt F s : Matrix (Fin 2) (Fin 2) F) *ᵥ
      cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t =
      cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t := by
    rw [upperElt_mulVec]
    ext i
    fin_cases i <;> simp [hsec]
  unfold fCocycle
  rw [h, hU]
  rfl

private lemma alpha_eq_one_of_mem_Q {L Q : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (x : ↥Q) : α (⟨(x : G), hQL x.2⟩ : ↥L) = 1 := by
  have hx : (⟨(x : G), hQL x.2⟩ : ↥L) ∈ α.ker := by
    rw [hker]
    exact x.2
  exact MonoidHom.mem_ker.mp hx

private lemma fCocycle_mul {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    {x y : ↥Q} (hxP : (x : G) ∈ P) (hyP : (y : G) ∈ P) (t : F) :
    fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (x * y)
        (by simpa using P.mul_mem hxP hyP) t =
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t +
        fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj y hyP t := by
  have hxL : α (⟨(x : G), hQL x.2⟩ : ↥L) = 1 := alpha_eq_one_of_mem_Q hQL hker x
  have hcomm : commPV hQL hker hβ₂ker hβ₂eq hW hsurj (x * y)
      (by simpa using P.mul_mem hxP hyP) t =
      conjOf (L := L) (E := V) hVconj (⟨(x : G), hQL x.2⟩ : ↥L)
        (commPV hQL hker hβ₂ker hβ₂eq hW hsurj y hyP t) *
      commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t := by
    apply Subtype.ext
    rw [commPV_coe]
    simp only [Subgroup.coe_mul]
    rw [conjOf_coe, commPV_coe, commPV_coe]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  unfold fCocycle
  unfold cocycleG
  rw [hcomm, map_mul, toAdd_mul]
  rw [b1_conjOf (L := L) (V := V) hβ₁eq hVconj (⟨(x : G), hQL x.2⟩ : ↥L)
    (commPV hQL hker hβ₂ker hβ₂eq hW hsurj y hyP t), hxL]
  simp only [Pi.add_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  abel

private lemma b1_commOf {L V : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (a : ↥L) (x : ↥V) :
    toAdd (β₁ (commOf (L := L) (E := V) hVconj a x)) =
      ((1 : Matrix (Fin 2) (Fin 2) F) + (α a : Matrix (Fin 2) (Fin 2) F)) *ᵥ
        toAdd (β₁ x) :=
  b1_comm hβ₁eq hVconj a x

private noncomputable def cocycleGV {L V A : Subgroup G} {F : Type}
    [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (v : ↥V) (t : F) : Fin 2 → F :=
  toAdd (β₁ (commOf (L := L) (E := V) hVconj
    ((zeta hsurj t : A.subgroupOf L) : ↥L) v))

private lemma cocycleGV_eq {L V A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (v : ↥V) (t : F) :
    cocycleGV (β₁ := β₁) hsurj hVconj v t =
      ![t * (toAdd (β₁ v)) 1, 0] := by
  unfold cocycleGV
  rw [show commOf hVconj ((zeta hsurj t : A.subgroupOf L) : ↥L) v =
    commOf (L := L) (E := V) hVconj ((zeta hsurj t : A.subgroupOf L) : ↥L) v from rfl]
  rw [b1_commOf (L := L) (V := V) hβ₁eq hVconj
    ((zeta hsurj t : A.subgroupOf L) : ↥L) v, zeta_spec,
    one_add_upperElt_mulVec]

private noncomputable def fV {L V A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (v : ↥V) (t : F) : F :=
  cocycleGV (β₁ := β₁) hsurj hVconj v t 0

private lemma fV_eq {L V A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (v : ↥V) (t : F) :
    fV (β₁ := β₁) hsurj hβ₁eq hVconj v t = t * (toAdd (β₁ v)) 1 := by
  rw [fV, cocycleGV_eq hsurj hβ₁eq hVconj]
  rfl

private lemma fCocycle_eq_zero_iff {L Q V Z P A : Subgroup G} {F : Type}
    [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hAU_eq : (A.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F)
    (hβ₁ker : β₁.ker = Z.subgroupOf V)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    {x : ↥Q} (hxP : (x : G) ∈ P) :
    (∀ t : F, fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t = 0) ↔
      ∀ a : A.subgroupOf L, ⁅(x : G), (a : G)⁆ ∈ Z := by
  constructor
  · intro hf a
    obtain ⟨t, rfl⟩ := zeta_surj hinj hsurj hAU_eq a
    have hsec := cocycleG_second_zero hQL hker hβ₂ker hβ₂eq hW hsurj hinj
      hβ₁eq hVconj hxP t
    have hzero : cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t = 0 := by
      ext i
      fin_cases i
      · exact hf t
      · exact hsec
    have hβ0 : toAdd (β₁ (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t)) = 0 := by
      rw [cocycleG] at hzero
      exact hzero
    have hV : (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t : G) ∈ Z :=
      (b1_eq_zero_iff hβ₁ker (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t)).mp hβ0
    simpa [commPV_coe] using hV
  · intro hZ t
    have hmem : ⁅(x : G), ((zeta hsurj t : A.subgroupOf L) : G)⁆ ∈ Z :=
      hZ (zeta hsurj t)
    have hV : (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t : G) ∈ Z := by
      simpa [commPV_coe] using hmem
    have hβ0 : toAdd (β₁ (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t)) = 0 :=
      (b1_eq_zero_iff hβ₁ker (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t)).mpr hV
    rw [fCocycle, cocycleG, hβ0]
    rfl

private lemma exists_xP {L Q V P A : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hW : PImage (P := P) β₂ = line F) (p : F) :
    ∃ x : ↥Q, (x : G) ∈ P ∧ toAdd (β₂ x) = ![p, 0] := by
  have hmem : (![p, 0] : Fin 2 → F) ∈ PImage (P := P) β₂ := by
    rw [hW]
    simp [line]
  obtain ⟨x, hxP, hx⟩ := hmem
  exact ⟨x, hxP, hx⟩

private lemma fCocycle_of_mem_V {L Q V P A : Subgroup G} {F : Type}
    [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (hVP : V ≤ P) {v : ↥Q} (hv : (v : G) ∈ V) (t : F) :
    fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj v (hVP hv) t =
      fV (β₁ := β₁) hsurj hβ₁eq hVconj (⟨(v : G), hv⟩ : ↥V) t := rfl

private noncomputable def fCanon {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (x : ↥Q) (t : F) : F := by
  classical
  exact if h : (x : G) ∈ P then
    fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x h t
  else 0

private lemma fCanon_eq {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    {x : ↥Q} (hxP : (x : G) ∈ P) (t : F) :
    fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x t =
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t := by
  unfold fCanon
  rw [dif_pos hxP]

private lemma conj_upperElt_eq {F : Type} [Field F] [CharP F 2]
    (M : SL(2, F)) (c b t : F) (hc : c ≠ 0)
    (h00 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = c)
    (h01 : (M : Matrix (Fin 2) (Fin 2) F) 0 1 = b)
    (h10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h11 : (M : Matrix (Fin 2) (Fin 2) F) 1 1 = c⁻¹) :
    M * CFSG.Timmesfeld.RankOne.upperElt F t * M⁻¹ =
      CFSG.Timmesfeld.RankOne.upperElt F (c ^ 2 * t) := by
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Timmesfeld.RankOne.upperElt, Matrix.mul_apply, Fin.sum_univ_two,
      h00, h01, h10, h11, hcc, inv_mul_cancel₀ hc, CharTwo.add_self_eq_zero]
  ring

private lemma conj_zeta_eq {L Q A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} (hker : α.ker = Q.subgroupOf L) (hAQ : A ⊓ Q = ⊥)
    (hAL : A ≤ L)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (k : ↥L) (c : F) (hc : c ≠ 0)
    (hk00 : (α k : Matrix (Fin 2) (Fin 2) F) 0 0 = c)
    (hk10 : (α k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (t : F)
    (hA : (k : G) * ((zeta hsurj t : A.subgroupOf L) : G) * (k : G)⁻¹ ∈ A) :
    (⟨⟨(k : G) * ((zeta hsurj t : A.subgroupOf L) : G) * (k : G)⁻¹, hAL hA⟩,
      hA⟩ : A.subgroupOf L) = zeta hsurj (c ^ 2 * t) := by
  have h11 : (α k : Matrix (Fin 2) (Fin 2) F) 1 1 = c⁻¹ := by
    have hdet : (α k : Matrix (Fin 2) (Fin 2) F).det = 1 := (α k).2
    rw [Matrix.det_fin_two, hk10, mul_zero, sub_zero, hk00] at hdet
    exact eq_inv_of_mul_eq_one_right hdet
  let aA : A.subgroupOf L :=
    ⟨⟨(k : G) * ((zeta hsurj t : A.subgroupOf L) : G) * (k : G)⁻¹, hAL hA⟩, hA⟩
  change aA = zeta hsurj (c ^ 2 * t)
  apply hinj
  change α (aA : ↥L) = α (zeta hsurj (c ^ 2 * t))
  rw [zeta_spec]
  have hval : (aA : ↥L) = k * ((zeta hsurj t : A.subgroupOf L) : ↥L) * k⁻¹ := by
    apply Subtype.ext
    rfl
  rw [hval, map_mul, map_mul, map_inv, zeta_spec]
  exact conj_upperElt_eq (α k) c ((α k : Matrix (Fin 2) (Fin 2) F) 0 1) t hc hk00 rfl hk10 h11

private lemma upper_mulVec_line {F : Type} [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) (c b p : F)
    (h00 : M 0 0 = c) (h01 : M 0 1 = b) (h10 : M 1 0 = 0) :
    M *ᵥ ![p, 0] = ![c * p, 0] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail, h00, h01, h10]

private lemma fCanon_conj {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hAL : A ≤ L) (hAQ : A ⊓ Q = ⊥)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (k : ↥L) (hkA : (k : G) ∈ Subgroup.normalizer (A : Set G))
    (hkP : (k : G) ∈ Subgroup.normalizer (P : Set G))
    (c : F) (hc : c ≠ 0)
    (hk00 : (α k : Matrix (Fin 2) (Fin 2) F) 0 0 = c)
    (hk10 : (α k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    {x : ↥Q} (hxP : (x : G) ∈ P) (t : F) :
    fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (conjQ hQL hker k x) (c ^ 2 * t) =
      c * fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x t := by
  have hkxP : (conjQ hQL hker k x : G) ∈ P := by
    rw [conjQ_coe]
    exact (Subgroup.mem_normalizer_iff.mp hkP (x : G)).mp hxP
  have hζA : ((zeta hsurj t : A.subgroupOf L) : G) ∈ A :=
    Subgroup.mem_subgroupOf.mp (zeta hsurj t).2
  have hA : (k : G) * ((zeta hsurj t : A.subgroupOf L) : G) * (k : G)⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hkA ((zeta hsurj t : A.subgroupOf L) : G)).mp hζA
  have hζ_eq := conj_zeta_eq hker hAQ hAL hinj hsurj k c hc hk00 hk10 t hA
  have hζ_eq_G : (k : G) * ((zeta hsurj t : A.subgroupOf L) : G) * (k : G)⁻¹ =
      ((zeta hsurj (c ^ 2 * t) : A.subgroupOf L) : G) := by
    rw [← congrArg (fun a : A.subgroupOf L => (a : G)) hζ_eq]
  have hcomm : commPV hQL hker hβ₂ker hβ₂eq hW hsurj (conjQ hQL hker k x) hkxP (c ^ 2 * t) =
      conjOf (L := L) (E := V) hVconj k
        (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t) := by
    apply Subtype.ext
    rw [commPV_coe, conjOf_coe, commPV_coe, conjQ_coe, ← hζ_eq_G]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hkxP (c ^ 2 * t),
    fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hxP t]
  unfold fCocycle cocycleG
  rw [hcomm, b1_conjOf (L := L) (V := V) hβ₁eq hVconj k
    (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t)]
  have hsec := cocycleG_second_zero hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq
    hVconj hxP t
  have hβ : toAdd (β₁ (commPV hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t)) =
      ![(cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t) 0, 0] := by
    ext i
    fin_cases i
    · rfl
    · exact hsec
  rw [hβ, upper_mulVec_line (α k : Matrix (Fin 2) (Fin 2) F) c
    ((α k : Matrix (Fin 2) (Fin 2) F) 0 1)
    ((cocycleG (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj x hxP t) 0) hk00 rfl hk10]
  rfl

private lemma Phi_mod_v {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (xp : F → ↥Q) (hxp_coord : ∀ p, toAdd (β₂ (xp p)) = ![p, 0]) (p p' : F) :
    ∃ v : ↥Q, (v : G) ∈ V ∧ xp (p + p') = xp p * xp p' * v := by
  let x : ↥Q := xp p
  let y : ↥Q := xp p'
  have hxy_coord : toAdd (β₂ (x * y)) = ![p + p', 0] := by
    rw [map_mul, toAdd_mul, hxp_coord p, hxp_coord p']
    ext i
    fin_cases i <;> simp
  have hz_coord : toAdd (β₂ (xp (p + p'))) = ![p + p', 0] := hxp_coord (p + p')
  let v : ↥Q := (x * y)⁻¹ * xp (p + p')
  have hvV : (v : G) ∈ V := by
    apply (b2_eq_zero_iff hβ₂ker v).mp
    have hv_eq : toAdd (β₂ v) = -toAdd (β₂ (x * y)) + toAdd (β₂ (xp (p + p'))) := by
      simp only [v, map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [hv_eq, hxy_coord, hz_coord]
    simp
  have hz_eq : xp (p + p') = x * y * v := by
    apply Subtype.ext
    simp only [v, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact ⟨v, hvV, hz_eq⟩

private lemma Phi_mod {L Q V P A : Subgroup G} {F : Type} [Field F] [Fintype F]
    [CharP F 2] {n : ℕ}
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (hVP : V ≤ P)
    (xp : F → ↥Q) (hxpP : ∀ p, (xp p : G) ∈ P)
    (hxp_coord : ∀ p, toAdd (β₂ (xp p)) = ![p, 0]) (p p' : F) :
    ∃ w : F, ∀ t : F,
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp (p + p'))
          (hxpP (p + p')) t =
        fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp p) (hxpP p) t +
          fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp p') (hxpP p') t +
            t * w := by
  obtain ⟨v, hvV, hz_eq⟩ := Phi_mod_v (L := L) (Q := Q) (V := V) (P := P) (A := A) (α := α) hβ₂ker xp hxp_coord p p'
  have hvP : (v : G) ∈ P := hVP hvV
  refine ⟨(toAdd (β₁ (⟨(v : G), hvV⟩ : ↥V))) 1, fun t => ?_⟩
  rw [← fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (hxpP (p + p')) t,
    ← fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (hxpP p) t,
    ← fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (hxpP p') t]
  rw [hz_eq]
  rw [fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
    (by simpa using P.mul_mem (P.mul_mem (hxpP p) (hxpP p')) hvP) t]
  rw [fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (hxpP p) t,
    fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (hxpP p') t]
  rw [fCocycle_mul (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq hVconj
    (x := xp p * xp p') (y := v) (by simpa using P.mul_mem (hxpP p) (hxpP p')) hvP t]
  rw [fCocycle_mul (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq hVconj
    (x := xp p) (y := xp p') (hxpP p) (hxpP p') t]
  rw [fCocycle_of_mem_V (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hβ₁eq hVconj hVP hvV t]
  rw [fV_eq (β₁ := β₁) hsurj hβ₁eq hVconj (⟨(v : G), hvV⟩ : ↥V) t]

private lemma Phi_tor_v {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (k : ↥L) (hkP : (k : G) ∈ Subgroup.normalizer (P : Set G))
    (c : F) (hk00 : (α k : Matrix (Fin 2) (Fin 2) F) 0 0 = c)
    (hk10 : (α k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (xp : F → ↥Q) (hxpP : ∀ p, (xp p : G) ∈ P)
    (hxp_coord : ∀ p, toAdd (β₂ (xp p)) = ![p, 0]) (p : F) :
    ∃ v : ↥Q, (v : G) ∈ V ∧ conjQ hQL hker k (xp p) = xp (c * p) * v := by
  let x : ↥Q := xp p
  let z : ↥Q := xp (c * p)
  let kx : ↥Q := conjQ hQL hker k x
  have hβkx : toAdd (β₂ kx) = ![c * p, 0] := by
    rw [show kx = conjQ hQL hker k x from rfl,
      b2_conj (L := L) (Q := Q) hQL hker hβ₂eq k x, hxp_coord p,
      upper_mulVec_line (α k : Matrix (Fin 2) (Fin 2) F) c
        ((α k : Matrix (Fin 2) (Fin 2) F) 0 1) p hk00 rfl hk10]
  let v : ↥Q := z⁻¹ * kx
  have hvV : (v : G) ∈ V := by
    apply (b2_eq_zero_iff (Q := Q) (V := V) hβ₂ker v).mp
    have hv_eq : toAdd (β₂ v) = -toAdd (β₂ z) + toAdd (β₂ kx) := by
      simp only [v, map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [hv_eq, hxp_coord (c * p), hβkx]
    simp
  have hz_eq : kx = z * v := by
    apply Subtype.ext
    simp only [v, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact ⟨v, hvV, hz_eq⟩

private lemma Phi_tor {L Q V P A : Subgroup G} {F : Type} [Field F] [Fintype F]
    [CharP F 2] {n : ℕ}
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hAL : A ≤ L) (hAQ : A ⊓ Q = ⊥) (hVP : V ≤ P)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (k : ↥L) (hkA : (k : G) ∈ Subgroup.normalizer (A : Set G))
    (hkP : (k : G) ∈ Subgroup.normalizer (P : Set G))
    (c : F) (hc : c ≠ 0)
    (hk00 : (α k : Matrix (Fin 2) (Fin 2) F) 0 0 = c)
    (hk10 : (α k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (xp : F → ↥Q) (hxpP : ∀ p, (xp p : G) ∈ P)
    (hxp_coord : ∀ p, toAdd (β₂ (xp p)) = ![p, 0]) (p : F) :
    ∃ w : F, ∀ t : F,
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp (c * p))
          (hxpP (c * p)) (c ^ 2 * t) =
        c * fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp p) (hxpP p) t +
          t * w := by
  obtain ⟨v, hvV, hz_eq⟩ := Phi_tor_v (L := L) (Q := Q) (V := V) (P := P) (A := A)
    (α := α) (β₂ := β₂) hQL hker hβ₂ker hβ₂eq k hkP c hk00 hk10 xp hxpP hxp_coord p
  have hvP : (v : G) ∈ P := hVP hvV
  refine ⟨c ^ 2 * (toAdd (β₁ (⟨(v : G), hvV⟩ : ↥V))) 1, fun t => ?_⟩
  rw [← fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (hxpP (c * p)) (c ^ 2 * t),
    ← fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (hxpP p) t]
  have hconj := fCanon_conj (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hAL hAQ
    hβ₁eq hVconj k hkA hkP c hc hk00 hk10 (hxpP p) t
  have hkx_eq : fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (conjQ hQL hker k (xp p)) (c ^ 2 * t) =
      fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp (c * p)) (c ^ 2 * t) +
        fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj v (c ^ 2 * t) := by
    rw [hz_eq]
    rw [fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
      (by simpa using P.mul_mem (hxpP (c * p)) hvP) (c ^ 2 * t)]
    rw [fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (hxpP (c * p)) (c ^ 2 * t),
      fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hvP (c ^ 2 * t)]
    rw [fCocycle_mul (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq hVconj
      (x := xp (c * p)) (y := v) (hxpP (c * p)) hvP (c ^ 2 * t)]
  have hfv : fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj v (c ^ 2 * t) =
      c ^ 2 * t * (toAdd (β₁ (⟨(v : G), hvV⟩ : ↥V))) 1 := by
    rw [fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hvP (c ^ 2 * t),
      fCocycle_of_mem_V (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hβ₁eq hVconj hVP hvV
        (c ^ 2 * t),
      fV_eq (β₁ := β₁) hsurj hβ₁eq hVconj (⟨(v : G), hvV⟩ : ↥V) (c ^ 2 * t)]
  have hz_eq' : fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp (c * p)) (c ^ 2 * t) =
      fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (conjQ hQL hker k (xp p)) (c ^ 2 * t) +
        fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj v (c ^ 2 * t) := by
    rw [hkx_eq, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hz_eq', hconj, hfv]
  ring

private lemma commutatorElement_mul_right_expand (y a b : G) :
    ⁅y, a * b⁆ = ⁅y, a⁆ * ⁅a, ⁅y, b⁆⁆ * ⁅y, b⁆ := by
  simp only [commutatorElement_def]
  group

private lemma comm_comm_mul_inv_mem {Q Z : Subgroup G} (hQQ : ⁅Q, Q⁆ ≤ Z) {y a b : G}
    (hab : a * b = b * a) (hu : ⁅y, a⁆ ∈ Q) (hw : ⁅y, b⁆ ∈ Q) (hc : ⁅⁅y, b⁆, a⁆ ∈ Q) :
    ⁅⁅y, b⁆, a⁆ * ⁅⁅y, a⁆, b⁆⁻¹ ∈ Z := by
  set u := ⁅y, a⁆
  set w := ⁅y, b⁆
  have h : u * ⁅a, w⁆ * w = w * ⁅b, u⁆ * u := by
    rw [← commutatorElement_mul_right_expand, hab, commutatorElement_mul_right_expand]
  have h2 : ⁅b, u⁆ = w⁻¹ * (u * ⁅a, w⁆ * w) * u⁻¹ := by
    rw [h]
    group
  have key : ⁅w, a⁆ * ⁅u, b⁆⁻¹ = ⁅⁅w, a⁆, w⁻¹ * u⁆ * ⁅w⁻¹, u⁆ := by
    rw [commutatorElement_inv, h2]
    simp only [commutatorElement_def]
    group
  rw [key]
  exact Z.mul_mem (hQQ (Subgroup.commutator_mem_commutator hc (Q.mul_mem (Q.inv_mem hw) hu)))
    (hQQ (Subgroup.commutator_mem_commutator (Q.inv_mem hw) hu))

private lemma zeta_comm_sub {L A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)}
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t) (s t : F) :
    (zeta hsurj s : A.subgroupOf L) * zeta hsurj t =
      zeta hsurj t * zeta hsurj s := by
  rw [← zeta_add hinj hsurj s t, ← zeta_add hinj hsurj t s, add_comm]

private lemma commQ_mem_P {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F) (hVP : V ≤ P)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (y : ↥Q) (hy : toAdd (β₂ y) = ![0, 1]) (s : F) :
    (commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y : G) ∈ P := by
  apply mem_P_of_b2_coord_zero (Q := Q) (P := P) (V := V) hβ₂ker hVP hW
  have hb2 : toAdd (β₂ (commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y)) =
      ![s, 0] := by
    rw [b2_comm (L := L) (Q := Q) hQL hker hβ₂eq
      ((zeta hsurj s : A.subgroupOf L) : ↥L) y, zeta_spec,
      one_add_upperElt_mulVec, hy]
    simp
  rw [hb2]
  simp

private lemma hsym_comm_mem_Z {L Q A Z : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (y : ↥Q) (hQQ : ⁅Q, Q⁆ ≤ Z) (s t : F) :
    (commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L)
        (commQ hQL hker ((zeta hsurj t : A.subgroupOf L) : ↥L) y) : G) *
      ((commQ hQL hker ((zeta hsurj t : A.subgroupOf L) : ↥L)
        (commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y) : G))⁻¹ ∈ Z := by
  let H_s : ↥Q := commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y
  let H_t : ↥Q := commQ hQL hker ((zeta hsurj t : A.subgroupOf L) : ↥L) y
  let Aq : ↥Q := commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) H_t
  let Bq : ↥Q := commQ hQL hker ((zeta hsurj t : A.subgroupOf L) : ↥L) H_s
  have h := comm_comm_mul_inv_mem (Q := Q) (Z := Z) hQQ
    (y := (y : G)) (a := ((zeta hsurj s : A.subgroupOf L) : G))
    (b := ((zeta hsurj t : A.subgroupOf L) : G))
    (by exact congrArg (fun z : A.subgroupOf L => (z : G)) (zeta_comm_sub hinj hsurj s t))
    H_s.2 H_t.2 (by
      change (Aq : G) ∈ Q
      exact Aq.2)
  change (Aq : G) * (Bq : G)⁻¹ ∈ Z
  exact h

private lemma hsym_cocycle {L Q V P A Z : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hVP : V ≤ P) (hVQ : V ≤ Q)
    (hβ₁ker : β₁.ker = Z.subgroupOf V)
    (hQQ : ⁅Q, Q⁆ ≤ Z)
    (y : ↥Q) (hy : toAdd (β₂ y) = ![0, 1]) (s t : F) :
    fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
        (commQ hQL hker ((zeta hsurj t : A.subgroupOf L) : ↥L) y)
        (commQ_mem_P (L := L) (Q := Q) (V := V) (P := P) (A := A) hQL hker hβ₂ker
          hβ₂eq hW hVP hsurj y hy t) s =
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
        (commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y)
        (commQ_mem_P (L := L) (Q := Q) (V := V) (P := P) (A := A) hQL hker hβ₂ker
          hβ₂eq hW hVP hsurj y hy s) t := by
  let H_s : ↥Q := commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y
  let H_t : ↥Q := commQ hQL hker ((zeta hsurj t : A.subgroupOf L) : ↥L) y
  have hHsP : (H_s : G) ∈ P :=
    commQ_mem_P (L := L) (Q := Q) (V := V) (P := P) (A := A) hQL hker hβ₂ker hβ₂eq
      hW hVP hsurj y hy s
  have hHtP : (H_t : G) ∈ P :=
    commQ_mem_P (L := L) (Q := Q) (V := V) (P := P) (A := A) hQL hker hβ₂ker hβ₂eq
      hW hVP hsurj y hy t
  let AqV : ↥V := commPV hQL hker hβ₂ker hβ₂eq hW hsurj H_t hHtP s
  let BqV : ↥V := commPV hQL hker hβ₂ker hβ₂eq hW hsurj H_s hHsP t
  have hZ : (AqV : G) * (BqV : G)⁻¹ ∈ Z := by
    have h := hsym_comm_mem_Z (L := L) (Q := Q) (A := A) (Z := Z) hQL hker hinj hsurj
      y hQQ s t
    simpa [AqV, BqV, H_s, H_t, commPV_coe, commQ_coe] using h
  have h0 : toAdd (β₁ (AqV * BqV⁻¹)) = 0 :=
    (b1_eq_zero_iff hβ₁ker (AqV * BqV⁻¹)).mpr hZ
  have hβeq : toAdd (β₁ AqV) = toAdd (β₁ BqV) := by
    rw [map_mul, toAdd_mul, map_inv, toAdd_inv] at h0
    exact add_neg_eq_zero.mp h0
  rw [← fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hHtP s,
    ← fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hHsP t]
  unfold fCanon
  rw [dif_pos hHtP, dif_pos hHsP]
  unfold fCocycle cocycleG
  rw [hβeq]

private lemma hfun_v {L Q V P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (y : ↥Q) (hy : toAdd (β₂ y) = ![0, 1])
    (xp : F → ↥Q) (hxp_coord : ∀ p, toAdd (β₂ (xp p)) = ![p, 0]) (s : F) :
    ∃ v : ↥Q, (v : G) ∈ V ∧
      commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y = xp s * v := by
  let x : ↥Q := xp s
  let H : ↥Q := commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y
  have hH_coord : toAdd (β₂ H) = ![s, 0] := by
    rw [show H = commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y from rfl,
      b2_comm (L := L) (Q := Q) hQL hker hβ₂eq
        ((zeta hsurj s : A.subgroupOf L) : ↥L) y, zeta_spec,
      one_add_upperElt_mulVec, hy]
    simp
  let v : ↥Q := x⁻¹ * H
  have hvV : (v : G) ∈ V := by
    apply (b2_eq_zero_iff (Q := Q) (V := V) hβ₂ker v).mp
    have hv_eq : toAdd (β₂ v) = -toAdd (β₂ x) + toAdd (β₂ H) := by
      simp only [v, map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [hv_eq, hxp_coord s, hH_coord]
    simp
  have hveq : H = x * v := by
    apply Subtype.ext
    simp only [v, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact ⟨v, hvV, hveq⟩

private lemma Phi_sym {L Q V P A Z : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hVP : V ≤ P) (hVQ : V ≤ Q)
    (hβ₁ker : β₁.ker = Z.subgroupOf V)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (hQQ : ⁅Q, Q⁆ ≤ Z)
    (y : ↥Q) (hy : toAdd (β₂ y) = ![0, 1])
    (xp : F → ↥Q) (hxpP : ∀ p, (xp p : G) ∈ P)
    (hxp_coord : ∀ p, toAdd (β₂ (xp p)) = ![p, 0]) :
    ∃ w : F → F, ∀ s t : F,
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp s) (hxpP s) t +
          t * w s =
        fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp t) (hxpP t) s +
          s * w t := by
  let v : F → ↥Q := fun s => Classical.choose
    (hfun_v (L := L) (Q := Q) (V := V) (P := P) (A := A) (α := α) (β₂ := β₂)
      hQL hker hβ₂ker hβ₂eq hsurj y hy xp hxp_coord s)
  have hvV : ∀ s, (v s : G) ∈ V := fun s =>
    (Classical.choose_spec
      (hfun_v (L := L) (Q := Q) (V := V) (P := P) (A := A) (α := α) (β₂ := β₂)
        hQL hker hβ₂ker hβ₂eq hsurj y hy xp hxp_coord s)).1
  have hveq : ∀ s, commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y = xp s * v s :=
    fun s => (Classical.choose_spec
      (hfun_v (L := L) (Q := Q) (V := V) (P := P) (A := A) (α := α) (β₂ := β₂)
        hQL hker hβ₂ker hβ₂eq hsurj y hy xp hxp_coord s)).2
  let w : F → F := fun s => (toAdd (β₁ (⟨(v s : G), hvV s⟩ : ↥V))) 1
  have hfcanon : ∀ s t, fCanon (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
      (commQ hQL hker ((zeta hsurj s : A.subgroupOf L) : ↥L) y) t =
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp s) (hxpP s) t + t * w s := by
    intro s t
    rw [hveq s]
    rw [fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
      (by simpa using P.mul_mem (hxpP s) (hVP (hvV s))) t]
    rw [fCocycle_mul (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq hVconj
      (x := xp s) (y := v s) (hxpP s) (hVP (hvV s)) t]
    rw [fCocycle_of_mem_V (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hβ₁eq hVconj hVP
      (hvV s) t, fV_eq (β₁ := β₁) hsurj hβ₁eq hVconj (⟨(v s : G), hvV s⟩ : ↥V) t]
  refine ⟨w, fun s t => ?_⟩
  have h := hsym_cocycle (L := L) (Q := Q) (V := V) (P := P) (A := A) (Z := Z)
    hQL hker hβ₂ker hβ₂eq hW hsurj hinj hVP hVQ hβ₁ker hQQ y hy s t
  rw [← fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
      (commQ_mem_P (L := L) (Q := Q) (V := V) (P := P) (A := A) hQL hker hβ₂ker
        hβ₂eq hW hVP hsurj y hy t) s,
    ← fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
      (commQ_mem_P (L := L) (Q := Q) (V := V) (P := P) (A := A) hQL hker hβ₂ker
        hβ₂eq hW hVP hsurj y hy s) t] at h
  rw [hfcanon t s, hfcanon s t] at h
  exact h.symm

private lemma Phi_exists {L Q V Z P A : Subgroup G} {F : Type} [Field F] [Fintype F]
    [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hAL : A ≤ L) (hAQ : A ⊓ Q = ⊥) (hVP : V ≤ P) (hVQ : V ≤ Q)
    (hβ₁ker : β₁.ker = Z.subgroupOf V)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (hQQ : ⁅Q, Q⁆ ≤ Z)
    (htor : ∀ c : F, c ≠ 0 → ∃ k : ↥L, (k : G) ∈ Subgroup.normalizer (A : Set G) ∧
      (k : G) ∈ Subgroup.normalizer (P : Set G) ∧
      (α k : Matrix (Fin 2) (Fin 2) F) 0 0 = c ∧ (α k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (y : ↥Q) (hy : toAdd (β₂ y) = ![0, 1]) :
    ∀ p : F, ∃ w : F, ∀ t : F,
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
        (Classical.choose (exists_xP (L := L) (Q := Q) (P := P) (V := V) (A := A) (n := n) (β₂ := β₂) hW p))
        (Classical.choose_spec (exists_xP (L := L) (Q := Q) (P := P) (V := V) (A := A) (n := n)
          (β₂ := β₂) hW p)).1 t = t * w := by
  let xp : F → ↥Q := fun p => Classical.choose
    (exists_xP (L := L) (Q := Q) (P := P) (V := V) (A := A) (n := n) (β₂ := β₂) hW p)
  have hxpP : ∀ p, (xp p : G) ∈ P := fun p =>
    (Classical.choose_spec (exists_xP (L := L) (Q := Q) (P := P) (V := V) (A := A) (n := n)
      (β₂ := β₂) hW p)).1
  have hxp_coord : ∀ p, toAdd (β₂ (xp p)) = ![p, 0] := fun p =>
    (Classical.choose_spec (exists_xP (L := L) (Q := Q) (P := P) (V := V) (A := A) (n := n)
      (β₂ := β₂) hW p)).2
  change ∀ p : F, ∃ w : F, ∀ t : F,
    fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp p) (hxpP p) t = t * w
  let Phi : F → F → F := fun p t =>
    fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp p) (hxpP p) t
  have hadd : ∀ p s t, Phi p (s + t) = Phi p s + Phi p t := fun p s t =>
    fCocycle_add (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq hVconj
      (hxpP p) s t
  have hmod : ∀ p p', ∃ w, ∀ t, Phi (p + p') t = Phi p t + Phi p' t + t * w :=
    fun p p' => Phi_mod (β₁ := β₁) (n := n) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq
      hVconj hVP xp hxpP hxp_coord p p'
  have htor' : ∀ c : F, c ≠ 0 → ∀ p, ∃ w, ∀ t,
      Phi (c * p) (c ^ 2 * t) = c * Phi p t + t * w := by
    intro c hc p
    obtain ⟨k, hkA, hkP, hk00, hk10⟩ := htor c hc
    exact Phi_tor (β₁ := β₁) (n := n) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hAL hAQ hVP
      hβ₁eq hVconj k hkA hkP c hc hk00 hk10 xp hxpP hxp_coord p
  have hsym : ∃ w : F → F, ∀ s t, Phi s t + t * w s = Phi t s + s * w t :=
    Phi_sym (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hVP hVQ hβ₁ker
      hβ₁eq hVconj hQQ y hy xp hxpP hxp_coord
  exact coboundary_of_torus_symm (K := F) hn (by rw [Nat.card_eq_fintype_card, hF])
    Phi hadd hmod htor' hsym

private lemma final_step_f {L Q V Z P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hAU_eq : (A.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F)
    (hAL : A ≤ L)
    (hVP : V ≤ P) (hPQ : P ≤ Q) (hVQ : V ≤ Q)
    (hβ₁ker : β₁.ker = Z.subgroupOf V)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (hβ₁surj : Function.Surjective β₁)
    (xp : F → ↥Q) (hxpP : ∀ p, (xp p : G) ∈ P)
    (hxp_coord : ∀ p, toAdd (β₂ (xp p)) = ![p, 0])
    (hcob : ∀ p : F, ∃ w : F, ∀ t : F,
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp p) (hxpP p) t = t * w)
    (xq : ↥Q) (hxqP : (xq : G) ∈ P) :
    ∃ (v' : ↥Q) (W : F), (v' : G) ∈ V ∧
      ∀ t, fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj xq hxqP t = t * W := by
  let p : F := (toAdd (β₂ xq)) 0
  have hxq_coord : toAdd (β₂ xq) = ![p, 0] := by
    ext i
    fin_cases i
    · rfl
    · exact b2_coord_zero_of_mem_P (Q := Q) (P := P) (V := V) hW hxqP
  let v' : ↥Q := (xp p)⁻¹ * xq
  have hv'V : (v' : G) ∈ V := by
    apply (b2_eq_zero_iff hβ₂ker v').mp
    have hv'_eq : toAdd (β₂ v') = -toAdd (β₂ (xp p)) + toAdd (β₂ xq) := by
      simp only [v', map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [hv'_eq, hxp_coord p, hxq_coord]
    simp
  have hxq_eq : xq = xp p * v' := by
    apply Subtype.ext
    simp only [v', Subgroup.coe_mul, Subgroup.coe_inv]
    group
  obtain ⟨w, hw⟩ := hcob p
  let W : F := w + (toAdd (β₁ (⟨(v' : G), hv'V⟩ : ↥V))) 1
  have hfx : ∀ t, fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj xq hxqP t = t * W := by
    intro t
    rw [← fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hxqP t, hxq_eq]
    rw [fCanon_eq (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
      (by simpa using P.mul_mem (hxpP p) (hVP hv'V)) t]
    rw [fCocycle_mul (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq hVconj
      (x := xp p) (y := v') (hxpP p) (hVP hv'V) t]
    rw [hw t]
    rw [fCocycle_of_mem_V (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hβ₁eq hVconj hVP
      hv'V t, fV_eq (β₁ := β₁) hsurj hβ₁eq hVconj (⟨(v' : G), hv'V⟩ : ↥V) t]
    simp only [W]; ring
  exact ⟨v', W, hv'V, hfx⟩

private lemma final_step {L Q V Z P A : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥L →* SL(2, F)} {β₂ : ↥Q →* Multiplicative (Fin 2 → F)}
    {β₁ : ↥V →* Multiplicative (Fin 2 → F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (hβ₂ker : β₂.ker = V.subgroupOf Q)
    (hβ₂eq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (hW : PImage (P := P) β₂ = line F)
    (hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t)
    (hinj : Function.Injective (fun a : A.subgroupOf L => α a))
    (hAU_eq : (A.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F)
    (hAL : A ≤ L)
    (hVP : V ≤ P) (hPQ : P ≤ Q) (hVQ : V ≤ Q)
    (hβ₁ker : β₁.ker = Z.subgroupOf V)
    (hβ₁eq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    (hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V)
    (hβ₁surj : Function.Surjective β₁)
    (xp : F → ↥Q) (hxpP : ∀ p, (xp p : G) ∈ P)
    (hxp_coord : ∀ p, toAdd (β₂ (xp p)) = ![p, 0])
    (hcob : ∀ p : F, ∃ w : F, ∀ t : F,
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp p) (hxpP p) t = t * w) :
    ∀ x ∈ P, ∃ v ∈ V, ∀ a ∈ A, ⁅x * v, a⁆ ∈ Z := by
  intro x hxP
  let xq : ↥Q := ⟨x, hPQ hxP⟩
  have hxqP : (xq : G) ∈ P := hxP
  obtain ⟨v', W, hv'V, hfx⟩ := final_step_f (β₁ := β₁) (β₂ := β₂) hQL hker hβ₂ker hβ₂eq
    hW hsurj hinj hAU_eq hAL hVP hPQ hVQ hβ₁ker hβ₁eq hVconj hβ₁surj xp hxpP hxp_coord
    hcob xq hxqP
  obtain ⟨v, hv⟩ := hβ₁surj (Multiplicative.ofAdd ![0, W])
  have hv_coord : toAdd (β₁ v) = ![0, W] := by
    rw [hv, toAdd_ofAdd]
  let vq : ↥Q := ⟨(v : G), hVQ v.2⟩
  have hvqP : (vq : G) ∈ P := hVP v.2
  have hvqV : (vq : G) ∈ V := by simpa [vq] using v.2
  have hzero : ∀ t, fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj
      (xq * vq) (by simpa using P.mul_mem hxqP hvqP) t = 0 := by
    intro t
    rw [fCocycle_mul (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hβ₁eq hVconj
      (x := xq) (y := vq) hxqP hvqP t]
    rw [hfx t]
    rw [fCocycle_of_mem_V (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hβ₁eq hVconj hVP
      hvqV t]
    have hvq_eq : (⟨(vq : G), hvqV⟩ : ↥V) = v := by
      apply Subtype.ext
      rfl
    rw [hvq_eq, fV_eq (β₁ := β₁) hsurj hβ₁eq hVconj v t, hv_coord]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]; rw [← add_mul, CharTwo.add_self_eq_zero, zero_mul]
  have hZ : ∀ a : A.subgroupOf L,
      ⁅((xq * vq : ↥Q) : G), (a : G)⁆ ∈ Z :=
    (fCocycle_eq_zero_iff (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hAU_eq
      hβ₁ker hβ₁eq hVconj (x := xq * vq)
      (by simpa using P.mul_mem hxqP hvqP)).mp hzero
  refine ⟨v, v.2, fun a ha => ?_⟩
  have hZa := hZ ⟨⟨a, hAL ha⟩, ha⟩
  simpa [xq, vq] using hZa

theorem exists_mul_commutator_mem_of_isNatSecOf {L Q V Z P A : Subgroup G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n) {α : ↥L →* SL(2, F)}
    (hQL : Q ≤ L) (hker : α.ker = Q.subgroupOf L)
    (h₂ : CFSG.Quasithin.F112R.St84.IsNatSecOf L Q V α)
    (h₁ : CFSG.Quasithin.F112R.St84.IsNatSecOf L V Z α)
    (hVP : V ≤ P) (hPQ : P ≤ Q) (hPV : V.relIndex P = 2 ^ n)
    (hAL : A ≤ L) (hAQ : A ⊓ Q = ⊥) (hA : Nat.card ↥A = 2 ^ n)
    (hAU : (A.subgroupOf L).map α ≤ CFSG.Timmesfeld.upperUnipotent F)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hQQ : ⁅Q, Q⁆ ≤ Z)
    (htor : ∀ c : F, c ≠ 0 → ∃ k : ↥L, (k : G) ∈ Subgroup.normalizer (A : Set G) ∧
      (k : G) ∈ Subgroup.normalizer (P : Set G) ∧
      (α k : Matrix (Fin 2) (Fin 2) F) 0 0 = c ∧ (α k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ∀ x ∈ P, ∃ v ∈ V, ∀ a ∈ A, ⁅x * v, a⁆ ∈ Z := by
  classical
  obtain ⟨β₂, hβ₂surj, hβ₂ker, hβ₂eq⟩ := h₂
  obtain ⟨β₁, hβ₁surj, hβ₁ker, hβ₁eq⟩ := h₁
  have hVQ : V ≤ Q := hVP.trans hPQ
  have hAU_eq : (A.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F :=
    map_alpha_A_eq_upperUnipotent hF hker hAL hAQ hA hAU
  have hinj : Function.Injective (fun a : A.subgroupOf L => α a) :=
    alpha_inj_on_A hker hAQ
  have hsurj : ∀ t : F, ∃ a : A.subgroupOf L, α a =
      CFSG.Timmesfeld.RankOne.upperElt F t := by
    intro t
    have hmem : CFSG.Timmesfeld.RankOne.upperElt F t ∈ (A.subgroupOf L).map α := by
      rw [hAU_eq]
      exact (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff F).2 ⟨t, rfl⟩
    obtain ⟨a, ha, hα⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨a, ha⟩, hα⟩
  have hW : PImage (P := P) β₂ = line F :=
    PImage_eq_line hF hQL hker hβ₂ker hβ₂eq hVP hPQ hPV hAP hsurj
  have hVconj : ∀ a : ↥L, ∀ x : ↥V, (a : G) * (x : G) * (a : G)⁻¹ ∈ V :=
    fun a x => mem_V_conj hQL hker hVQ hβ₂ker hβ₂eq a x
  obtain ⟨y, hy⟩ := hβ₂surj (Multiplicative.ofAdd ![0, 1])
  have hy_coord : toAdd (β₂ y) = ![0, 1] := by
    rw [hy, toAdd_ofAdd]
  let xp : F → ↥Q := fun p => Classical.choose
    (exists_xP (L := L) (Q := Q) (P := P) (V := V) (A := A) (n := n) (β₂ := β₂) hW p)
  have hxpP : ∀ p, (xp p : G) ∈ P := fun p =>
    (Classical.choose_spec (exists_xP (L := L) (Q := Q) (P := P) (V := V) (A := A)
      (n := n) (β₂ := β₂) hW p)).1
  have hxp_coord : ∀ p, toAdd (β₂ (xp p)) = ![p, 0] := fun p =>
    (Classical.choose_spec (exists_xP (L := L) (Q := Q) (P := P) (V := V) (A := A)
      (n := n) (β₂ := β₂) hW p)).2
  have hcob : ∀ p : F, ∃ w : F, ∀ t : F,
      fCocycle (β₁ := β₁) hQL hker hβ₂ker hβ₂eq hW hsurj (xp p) (hxpP p) t = t * w := by
    have h := Phi_exists (β₁ := β₁) (β₂ := β₂) hn hF hQL hker hβ₂ker hβ₂eq hW hsurj
      hinj hAL hAQ hVP hVQ hβ₁ker hβ₁eq hVconj hQQ htor y hy_coord
    simpa [xp, hxpP] using h
  exact final_step (β₁ := β₁) (β₂ := β₂) hQL hker hβ₂ker hβ₂eq hW hsurj hinj hAU_eq
    hAL hVP hPQ hVQ hβ₁ker hβ₁eq hVconj hβ₁surj xp hxpP hxp_coord hcob

end CFSG.Quasithin.St84
