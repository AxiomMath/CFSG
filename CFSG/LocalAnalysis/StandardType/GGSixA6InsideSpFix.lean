module

public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpComp
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpPull

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

namespace CFSG.StandardType

namespace A6InsideSp

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType.ChoiceTwo

section Centralizer

variable {G : Type*} [Group G]

theorem mem_centralizer_closure_pair {a b g : G} :
    g ∈ Subgroup.centralizer (Subgroup.closure {a, b} : Set G) ↔
      g * a = a * g ∧ g * b = b * g := by
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h a (by simp)).symm, (h b (by simp)).symm⟩
  · rintro ⟨ha, hb⟩ x (rfl | rfl)
    · exact ha.symm
    · exact hb.symm

end Centralizer

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type}
  [Field L] [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)}
  (F : ChoiceTwo.SpFrame K n ζ E)

section JFIX

variable [NeZero n] [Module.Finite K L]

theorem le_spFixedFactor_of_isComponentOf (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (hL : Module.finrank K L = 2) {f : Fin F.s → ZMod 3} {D Q : Subgroup (StatedSp n K)}
    (hDw : D ≤ Subgroup.centralizer {F.tor f})
    (hCw : Subgroup.centralizer (D : Set (StatedSp n K)) ≤ Subgroup.centralizer {F.tor f})
    (hSD : spSupported (F.tor f) {phi3 K} ≤
      Subgroup.centralizer (D : Set (StatedSp n K)))
    (hQ : IsComponentOf Q (Subgroup.centralizer (D : Set (StatedSp n K))))
    (h27 : ¬ 27 ∣ Nat.card Q) : Q ≤ spFixedFactor (F.tor f) := by
  rcases le_spFixedFactor_or_le_spSupported F hK hζo hDw hCw hQ with h | h
  · exact h
  · exfalso
    have hQ' : IsComponentOf Q (Subgroup.centralizer {F.tor f}) :=
      isComponentOf_of_le_normalized hQ h hSD
        (SevSpNs.spSupported_le_centralizer (F.tor f) {phi3 K})
        (SevSpNs.spSupported_normalized (F.tor f) {phi3 K})
    exact false_of_le_spSupported_phi3 F hK hζo hL hQ' h h27

end JFIX

theorem exists_eq_closure_pair (hζo : IsPrimitiveRoot ζ 3) {D : Subgroup (StatedSp n K)}
    (hDE : D ≤ E) (hD : Nat.card D = 9) {c : Fin F.s → ZMod 3} (hcD : F.tor c ∈ D)
    {i₀ : Fin F.s} (hc : c i₀ ≠ 0) :
    ∃ d : Fin F.s → ZMod 3, F.tor d ∈ D ∧ d i₀ = 0 ∧
      (∀ α β : ZMod 3, α • c + β • d = 0 → α = 0 ∧ β = 0) ∧
      D = Subgroup.closure {F.tor c, F.tor d} := by
  classical
  have hζ : ζ ^ 3 = 1 := hζo.pow_eq_one
  have hc0 : c ≠ 0 := fun h => hc (by rw [h]; rfl)
  have htor_ne : F.tor c ≠ 1 := by
    intro h1
    apply hc0
    apply F.tor_injective hζo
    rw [h1, F.tor_zero]
  have hord : orderOf (F.tor c) = 3 :=
    orderOf_eq_prime (F.tor_pow_three hζ c) htor_ne
  have hcard3 : Nat.card (Subgroup.zpowers (F.tor c)) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hex : ∃ y ∈ D, y ∉ Subgroup.zpowers (F.tor c) := by
    by_contra h
    push Not at h
    haveI : Finite ↥(Subgroup.zpowers (F.tor c)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard3]; norm_num)
    have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers (F.tor c)) :=
      Subgroup.card_le_of_le h
    rw [hD, hcard3] at hle
    omega
  obtain ⟨y, hyD, hyNot⟩ := hex
  obtain ⟨d₀, hd0⟩ := F.mem_tor y (hDE hyD)
  have hd0D : F.tor d₀ ∈ D := by rw [hd0]; exact hyD
  have hd0Not : F.tor d₀ ∉ Subgroup.zpowers (F.tor c) := by rw [hd0]; exact hyNot
  set κ : ZMod 3 := d₀ i₀ * (c i₀)⁻¹ with hκ
  set d : Fin F.s → ZMod 3 := d₀ - κ • c with hd_def
  have hdi : d i₀ = 0 := by
    rw [hd_def]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hκ]
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one, sub_self]
  have hdD : F.tor d ∈ D := by
    have heq : F.tor d = F.tor d₀ * (F.tor c) ^ (-κ).val := by
      rw [hd_def, sub_eq_add_neg, ← neg_smul, F.tor_add hζ]
      rw [tor_smul F hζ]
    rw [heq]
    exact Subgroup.mul_mem D hd0D (Subgroup.pow_mem D hcD _)
  have hind : ∀ α β : ZMod 3, α • c + β • d = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    have hα : α = 0 := by
      have h1 := congrFun h i₀
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hdi, mul_zero,
        add_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_right hc
    have hβ : β = 0 := by
      by_contra hβ
      have hdzero : d = 0 := by
        funext i
        have h1 : β * d i = 0 := by
          have h2 := congrFun h i
          rw [hα, zero_smul, zero_add] at h2
          simpa only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using h2
        exact (mul_eq_zero.mp h1).resolve_left hβ
      have hd0eq : d₀ = κ • c := by
        rw [hd_def, sub_eq_zero] at hdzero
        exact hdzero
      apply hd0Not
      have hpow : F.tor d₀ = (F.tor c) ^ κ.val := by
        rw [hd0eq, tor_smul F hζ κ c]
      rw [hpow]
      exact Subgroup.pow_mem (Subgroup.zpowers (F.tor c)) (Subgroup.mem_zpowers _) _
    exact ⟨hα, hβ⟩
  exact ⟨d, hdD, hdi, hind, eq_closure_pair F hζo hind hD hcD hdD⟩

end Frame

end A6InsideSp

end CFSG.StandardType
