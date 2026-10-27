module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSetup
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.RankThree.PartOne.KCSpFull
open CFSG.RankThree.Classical
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras

variable {k n : ℕ} {F : Type} [Field F]

private theorem borel86_spn_ext {g h : ↥(StatedSp k F)}
    (H : ∀ y : Fin k ⊕ Fin k → F, spEnd g y = spEnd h y) : g = h :=
  spLin_injective (Units.ext (LinearMap.ext H))

private theorem borel86_spn_spForm_eq_form (u v : Fin k ⊕ Fin k → F) :
    spForm k F u v = form u v := by
  rw [spForm_apply]
  rfl

theorem borel86_spn_eq_spTransvection {t₀ : ↥(StatedSp k F)}
    (ht : IsSymplecticTransvectionIn k t₀) :
    ∃ (a : Fin k ⊕ Fin k → F) (c : F), a ≠ 0 ∧ c ≠ 0 ∧ t₀ = spTransvection a c := by
  obtain ⟨u, c, hu, hc, hM⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.exists_transvection_form t₀ ht
  refine ⟨u, -c, hu, neg_ne_zero.mpr hc, ?_⟩
  apply borel86_spn_ext
  intro y
  rw [spEnd_spTransvection]
  have hleft : spEnd t₀ y = (c * form u y) • u + y := by
    rw [spEnd_apply, ← mat_apply]
    have hsub : mat k F t₀ = (mat k F t₀ - 1) + 1 := (sub_add_cancel _ _).symm
    rw [hsub, Matrix.add_mulVec, Matrix.one_mulVec, hM y]
  rw [hleft]
  rw [show (-c) * spForm k F y u = c * form u y by
    rw [borel86_spn_spForm_eq_form, form_antisymm u y]
    ring]
  exact add_comm _ _

theorem borel86_spn_spTransvection_param_zero (a : Fin k ⊕ Fin k → F) :
    spTransvection a (0 : F) = 1 := by
  apply borel86_spn_ext
  intro y
  rw [spEnd_spTransvection, spEnd_one, Module.End.one_apply]
  simp

theorem borel86_spn_exists_smul_of_spTransvection_eq {a b : Fin k ⊕ Fin k → F} {s t : F}
    (ha : a ≠ 0) (ht : t ≠ 0) (h : spTransvection b s = spTransvection a t) :
    ∃ μ : F, μ ≠ 0 ∧ b = μ • a ∧ μ * μ * s = t := by
  have hkey : ∀ y : Fin k ⊕ Fin k → F,
      (s * spForm k F y b) • b = (t * spForm k F y a) • a := by
    intro y
    have h1 := congrArg (fun g => spEnd g y) h
    rw [spEnd_spTransvection, spEnd_spTransvection] at h1
    exact add_left_cancel h1
  obtain ⟨y₀, hy₀⟩ : ∃ y : Fin k ⊕ Fin k → F, spForm k F y a ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    exact ha (spForm_nondegenerate.2 a fun y => not_not.mp (hcon y))
  have hEq := hkey y₀
  have hRHS : (t * spForm k F y₀ a) • a ≠ 0 :=
    smul_ne_zero (mul_ne_zero ht hy₀) ha
  have hsB : s * spForm k F y₀ b ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hEq
    exact hRHS hEq.symm
  have hb : b = ((s * spForm k F y₀ b)⁻¹ * (t * spForm k F y₀ a)) • a := by
    have h2 := congrArg (fun w => (s * spForm k F y₀ b)⁻¹ • w) hEq
    rw [inv_smul_smul₀ hsB, smul_smul] at h2
    exact h2
  refine ⟨(s * spForm k F y₀ b)⁻¹ * (t * spForm k F y₀ a),
    mul_ne_zero (inv_ne_zero hsB) (mul_ne_zero ht hy₀), hb, ?_⟩
  have hconj : spTransvection a ((s * spForm k F y₀ b)⁻¹ * (t * spForm k F y₀ a) *
      ((s * spForm k F y₀ b)⁻¹ * (t * spForm k F y₀ a)) * s) = spTransvection a t := by
    rw [← CFSG.RankThree.PartOne.CTP.spTransvection_smul
      ((s * spForm k F y₀ b)⁻¹ * (t * spForm k F y₀ a)) a s, ← hb]
    exact h
  have h2 := congrArg (fun g => spEnd g y₀) hconj
  rw [spEnd_spTransvection, spEnd_spTransvection] at h2
  have h3 : ((s * spForm k F y₀ b)⁻¹ * (t * spForm k F y₀ a) *
      ((s * spForm k F y₀ b)⁻¹ * (t * spForm k F y₀ a)) * s) * spForm k F y₀ a =
      t * spForm k F y₀ a :=
    smul_left_injective F ha (add_left_cancel h2)
  exact mul_right_cancel₀ hy₀ h3

private theorem borel86_spn_mul_iff (y : ↥(StatedSp k F)) (a : Fin k ⊕ Fin k → F) {c : F}
    (hc : c ≠ 0) :
    y * spTransvection a c = spTransvection a c * y ↔
      ∀ z : Fin k ⊕ Fin k → F,
        spForm k F z a • spEnd y a = spForm k F (spEnd y z) a • a := by
  constructor
  · intro h z
    have h1 := congrArg (fun g => spEnd g z) h
    rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply,
      spEnd_spTransvection, spEnd_spTransvection, map_add, map_smul] at h1
    have h2 : (c * spForm k F z a) • spEnd y a =
        (c * spForm k F (spEnd y z) a) • a := add_left_cancel h1
    rw [mul_smul, mul_smul] at h2
    exact smul_right_injective (Fin k ⊕ Fin k → F) hc h2
  · intro h
    apply borel86_spn_ext
    intro z
    rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply,
      spEnd_spTransvection, spEnd_spTransvection, map_add, map_smul, mul_smul, mul_smul, h z]

theorem borel86_spn_commute_spTransvection_iff {a : Fin k ⊕ Fin k → F} {c s : F} (hc : c ≠ 0)
    (hs : s ≠ 0) (y : ↥(StatedSp k F)) :
    y * spTransvection a c = spTransvection a c * y ↔
      y * spTransvection a s = spTransvection a s * y :=
  (borel86_spn_mul_iff y a hc).trans (borel86_spn_mul_iff y a hs).symm

theorem borel86_spn_exists_conj_spTransvection [Finite F] (hF : Nat.card F = 2 ^ n)
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) {c s : F} (hc : c ≠ 0) (hs : s ≠ 0) :
    ∃ h : ↥(StatedSp k F), h * spTransvection a c * h⁻¹ = spTransvection a s := by
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, pow_zero] at hF
      exact absurd hF.symm (Finite.one_lt_card (α := F)).ne
    · exact h
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hF
  have hring : ringChar F = 2 := ringChar.eq_iff.mpr hchar
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hring (s / c)
  have hr0 : r ≠ 0 := by
    intro h0
    exact (div_ne_zero hs hc) (by rw [hr, h0, mul_zero])
  obtain ⟨h, hh⟩ := exists_spEnd_eq ha (smul_ne_zero hr0 ha)
  exact ⟨h, by
    rw [CFSG.RankThree.PartOne.CTP.spTransvection_conj, hh,
      CFSG.RankThree.PartOne.CTP.spTransvection_smul]
    rw [show r * r * c = s by rw [← hr, div_mul_cancel₀ s hc]]⟩

theorem borel86_spn_exists_conj_ne [Finite F] (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {t₀ : ↥(StatedSp k F)} (ht : IsSymplecticTransvectionIn k t₀) :
    ∃ d₀ t₁ : ↥(StatedSp k F), d₀ * t₀ * d₀⁻¹ = t₁ ∧ t₁ ≠ t₀ ∧
      ∀ y : ↥(StatedSp k F), y * t₀ = t₀ * y ↔ y * t₁ = t₁ * y := by
  obtain ⟨a, c, ha, hc, rfl⟩ := borel86_spn_eq_spTransvection ht
  have hex : ∃ s : F, s ≠ 0 ∧ s ≠ c := by
    by_contra hcon
    rw [not_exists] at hcon
    have hcon' : ∀ s : F, s = 0 ∨ s = c := fun s => by
      rcases not_and_or.mp (hcon s) with h | h
      · exact Or.inl (not_not.mp h)
      · exact Or.inr (not_not.mp h)
    have hsurj : Function.Surjective (fun b : Bool => if b then c else 0) := by
      intro x
      rcases hcon' x with h | h
      · exact ⟨false, by simp [h]⟩
      · exact ⟨true, by simp [h]⟩
    have hcard : Nat.card F ≤ 2 := by
      have := Nat.card_le_card_of_surjective (fun b : Bool => if b then c else 0) hsurj
      rwa [show Nat.card Bool = 2 by simp [Nat.card_eq_fintype_card]] at this
    have hlt : 2 < Nat.card F := by
      rw [hF]
      exact lt_of_le_of_lt hn Nat.lt_two_pow_self
    omega
  obtain ⟨s, hs0, hsc⟩ := hex
  obtain ⟨d₀, hd₀⟩ := borel86_spn_exists_conj_spTransvection hF ha hc hs0
  refine ⟨d₀, spTransvection a s, hd₀, ?_, fun y =>
    borel86_spn_commute_spTransvection_iff hc hs0 y⟩
  intro heq
  obtain ⟨μ, _hμ0, hμa, hμs⟩ :=
    borel86_spn_exists_smul_of_spTransvection_eq ha hc heq
  have hμ1 : μ = 1 := by
    apply smul_left_injective F ha
    simpa using hμa.symm
  exact hsc (by rw [hμ1] at hμs; simpa using hμs)

theorem borel86_spn_exists_conj_commute [Finite F] (hF : Nat.card F = 2 ^ n)
    {a : Fin k ⊕ Fin k → F} {c : F} (ha : a ≠ 0) (hc : c ≠ 0) {g : ↥(StatedSp k F)}
    (hg : g * spTransvection a c = spTransvection a c * g) {s : F} (hs : s ≠ 0) :
    ∃ h : ↥(StatedSp k F), h * spTransvection a c * h⁻¹ = spTransvection a s ∧
      g * spTransvection a s = spTransvection a s * g := by
  obtain ⟨h, hh⟩ := borel86_spn_exists_conj_spTransvection hF ha hc hs
  exact ⟨h, hh, (borel86_spn_commute_spTransvection_iff hc hs g).mp hg⟩

end CFSG.LocalAnalysis.WeakClosure81

end
