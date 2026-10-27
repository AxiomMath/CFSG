module

public import CFSG.Quasithin.EmptyFaithful.S143NE
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Quasithin.EmptyFaithful.S143KO
public import CFSG.Quasithin.EmptyFaithful.S143NA2
public import CFSG.Quasithin.EmptyFaithful.S143JB
public import CFSG.Quasithin.EmptyFaithful.S143KP
public import CFSG.Quasithin.EmptyFaithful.S143IG
public import CFSG.Quasithin.EmptyFaithful.S143HD
public import CFSG.Quasithin.EmptyFaithful.S143FF
public import CFSG.Quasithin.EmptyFaithful.S143Final
public import Certificates.Kernel.J4Count.FixCPairBase1
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.Background.B3ThreeModel
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.B3ThreeStruct
public import CFSG.Quasithin.Background.G2Omega4PlusModule
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Quasithin.Background.A1cTransferVariants
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143

section Irreducible

variable {G : Type*} [Group G] [Finite G]

theorem eq_bot_or_eq_of_order_five {A B : Subgroup G} {y : G} (hA : Nat.card A = 16) (hBA : B ≤ A)
    (hy5 : orderOf y = 5) (hyB : ∀ b ∈ B, y * b * y⁻¹ ∈ B)
    (hfix : ∀ a ∈ A, y * a * y⁻¹ = a → a = 1) : B = ⊥ ∨ B = A := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f : Function.End ↥B := fun b => ⟨y * b * y⁻¹, hyB b b.2⟩
  have key : ∀ n : ℕ, ∀ b : ↥B, (((f ^ n) b : ↥B) : G) = y ^ n * b * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro b
      have : (f ^ 0) b = b := rfl
      rw [this]
      simp
    | succ n ih =>
      intro b
      rw [pow_succ]
      show (((f ^ n) (f b) : ↥B) : G) = _
      rw [ih]
      show y ^ n * (y * ↑b * y⁻¹) * (y ^ n)⁻¹ = _
      rw [pow_succ]
      group
  have hf5 : f ^ 5 = 1 := by
    funext b
    apply Subtype.ext
    rw [key]
    have h5 : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
    have h1 : (1 : Function.End ↥B) b = b := rfl
    rw [h5, h1]
    simp
  have : Fintype ↥B := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) (by simpa using hf5)
  have hfixcard : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, by
      show f 1 = 1
      apply Subtype.ext
      simp [f]⟩, fun ⟨b, hb⟩ => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hb' : (f b : ↥B) = b := hb
    have h1 : y * (b : G) * y⁻¹ = b := congrArg Subtype.val hb'
    exact hfix b (hBA b.2) h1
  rw [hfixcard] at hmod
  have hBcard : Nat.card B ∣ 2 ^ 4 := by
    have := Subgroup.card_dvd_of_le hBA
    rw [hA] at this
    simpa using this
  have hmod' : Nat.card B ≡ 1 [MOD 5] := by
    rw [Nat.card_eq_fintype_card]
    exact hmod
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hBcard
  have hmod2 : 2 ^ m % 5 = 1 % 5 := by
    have h := hmod'
    rw [hmeq] at h
    exact h
  interval_cases m
  · left
    exact Subgroup.eq_bot_of_card_eq B (by simpa using hmeq)
  · exact absurd hmod2 (by norm_num)
  · exact absurd hmod2 (by norm_num)
  · exact absurd hmod2 (by norm_num)
  · right
    exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hA, hmeq]; norm_num)

end Irreducible

section Block

variable {Y Γ : Type*} [Group Y] [Finite Y] [Group Γ]

structure BlockData (φ : Y →* Γ) (Â : Subgroup Y) (y : Y) : Prop where
  normal : Â.Normal
  comm : ∀ a ∈ Â, ∀ b ∈ Â, a * b = b * a
  card : Nat.card Â = 16
  ker : φ.ker = Â
  simple : IsSimpleGroup φ.range
  card_range : Nat.card φ.range = 60
  order : orderOf y = 5
  fix : ∀ a ∈ Â, y * a * y⁻¹ = a → a = 1

variable {φ : Y →* Γ} {Â : Subgroup Y} {y : Y}

theorem BlockData.irred (h : BlockData φ Â y) {B : Subgroup Y} (hB : B ≤ Â)
    (hinv : ∀ x : Y, ∀ b ∈ B, x * b * x⁻¹ ∈ B) : B = ⊥ ∨ B = Â :=
  eq_bot_or_eq_of_order_five h.card hB h.order (fun b hb => hinv y b hb) h.fix

theorem BlockData.normal_cases (h : BlockData φ Â y) {H : Subgroup Y} (hH : H.Normal) :
    H ≤ Â ∨ H = ⊤ := by
  classical
  have hn := h.normal
  have hψ : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hker : φ.rangeRestrict.ker = Â := by rw [MonoidHom.ker_rangeRestrict]; exact h.ker
  have := h.simple
  have hmap : (H.map φ.rangeRestrict).Normal := hH.map φ.rangeRestrict hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.map φ.rangeRestrict) with h0 | h1
  · left
    intro x hx
    have : φ.rangeRestrict x ∈ H.map φ.rangeRestrict := ⟨x, hx, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    rw [← hker]
    exact this
  · right
    have hdec : ∀ x : Y, ∃ h' ∈ H, x * h'⁻¹ ∈ Â := by
      intro x
      have : φ.rangeRestrict x ∈ H.map φ.rangeRestrict := by rw [h1]; exact Subgroup.mem_top _
      obtain ⟨h', hh', hψ'⟩ := this
      refine ⟨h', hh', ?_⟩
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hψ', mul_inv_cancel]
    have hBn : (Â ⊓ H).Normal := inferInstance
    rcases h.irred (inf_le_left : Â ⊓ H ≤ Â) (fun x b hb => hBn.conj_mem b hb x) with hB | hB
    · exfalso
      have hcomm : ∀ a ∈ Â, ∀ h' ∈ H, a * h' = h' * a := by
        intro a ha h' hh'
        have h2 : a * h' * a⁻¹ * h'⁻¹ ∈ Â ⊓ H := by
          constructor
          · have h4 : a * (h' * a⁻¹ * h'⁻¹) ∈ Â :=
              Â.mul_mem ha (hn.conj_mem a⁻¹ (Â.inv_mem ha) h')
            have e : a * h' * a⁻¹ * h'⁻¹ = a * (h' * a⁻¹ * h'⁻¹) := by group
            rw [e]
            exact h4
          · have h3 := hH.conj_mem h' hh' a
            exact H.mul_mem h3 (H.inv_mem hh')
        rw [hB, Subgroup.mem_bot] at h2
        calc a * h' = (a * h' * a⁻¹ * h'⁻¹) * (h' * a) := by group
          _ = h' * a := by rw [h2, one_mul]
      obtain ⟨h', hh', hmem⟩ := hdec y
      have hy : ∀ a ∈ Â, y * a * y⁻¹ = a := by
        intro a ha
        have hy1 : y = (y * h'⁻¹) * h' := by group
        set a₀ := y * h'⁻¹ with ha₀
        calc y * a * y⁻¹ = a₀ * (h' * a * h'⁻¹) * a₀⁻¹ := by rw [hy1]; group
          _ = a₀ * a * a₀⁻¹ := by
            rw [← hcomm a ha h' hh']
            group
          _ = a := by
            rw [h.comm a₀ hmem a ha]
            group
      have hbot : Â = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        exact Subgroup.mem_bot.mpr (h.fix a ha (hy a ha))
      have := h.card
      rw [hbot] at this
      simp at this
    · have hAH : Â ≤ H := by
        rw [← hB]
        exact inf_le_right
      rw [eq_top_iff]
      intro x _
      obtain ⟨h', hh', hmem⟩ := hdec x
      have e : x = (x * h'⁻¹) * h' := by group
      rw [e]
      exact H.mul_mem (hAH hmem) hh'

theorem BlockData.perfect (h : BlockData φ Â y) : commutator Y = ⊤ := by
  have := h.simple
  rcases h.normal_cases (inferInstance : (commutator Y).Normal) with hle | htop
  · exfalso
    have hψ := φ.rangeRestrict_surjective
    have hker : φ.rangeRestrict.ker = Â := by rw [MonoidHom.ker_rangeRestrict]; exact h.ker
    have hcomm : ∀ s₁ s₂ : ↥φ.range, s₁ * s₂ = s₂ * s₁ := by
      intro s₁ s₂
      obtain ⟨y₁, rfl⟩ := hψ s₁
      obtain ⟨y₂, rfl⟩ := hψ s₂
      have hc : ⁅y₁, y₂⁆ ∈ commutator Y :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have h1 : φ.rangeRestrict ⁅y₁, y₂⁆ = 1 := by
        have := hle hc
        rw [← hker] at this
        exact this
      rw [map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    let _ : CommGroup ↥φ.range := { (inferInstance : Group ↥φ.range) with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := ↥φ.range)
    rw [h.card_range] at hp
    norm_num at hp
  · exact htop

theorem BlockData.pCore_le (h : BlockData φ Â y) {P : Subgroup Y} (hP : P.Normal)
    (hP2 : IsPGroup 2 P) : P ≤ Â := by
  rcases h.normal_cases hP with hle | htop
  · exact hle
  · exfalso
    subst htop
    have hY2 : IsPGroup 2 Y := hP2.of_equiv Subgroup.topEquiv
    have hR : IsPGroup 2 ↥φ.range := hY2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    have : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [h.card_range] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem BlockData.subnormal_cases (h : BlockData φ Â y) {H K : Subgroup Y} (hH : IsSubnormal H K)
    (hK : K = ⊤) : H ≤ Â ∨ H = ⊤ := by
  induction hH with
  | refl H => right; exact hK
  | @step H M K hle hN hMK ih =>
    rcases ih hK with hM | hM
    · left
      exact hle.trans hM
    · subst hM
      have hnorm : H.Normal :=
        ⟨fun n hn g => (Subgroup.normal_subgroupOf_iff hle).mp hN n g hn (Subgroup.mem_top g)⟩
      exact h.normal_cases hnorm

end Block


end S143

end CFSG.Quasithin
