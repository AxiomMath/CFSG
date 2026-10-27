module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Shape
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSetup
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KOut
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229U3E9
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
import CFSG.RankThree.PartTwo.KFacts.K72FixL2
import CFSG.RankThree.PartTwo.KFacts.K72Invert
import CFSG.RankThree.PartTwo.KFacts.K72L3Omega
import CFSG.RankThree.PartTwo.KFacts.K72Omega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out

open CFSG.RankThree.PartTwo.KFacts
open CFSG.GorensteinWalter (PSL2)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

private theorem isCyclic_sylow {X : Type} [Group X] [Finite X]
    (h1 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1) (S : Sylow 3 X) : IsCyclic S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one (by norm_num) h1.le S

private theorem shape_cases {X : Type} [Group X] [Finite X]
    (hX : R8107Shape.ThinShape X ∨ ∃ n : ℕ, IsU3 X n)
    (h1 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1) :
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nonempty (X ≃* PSL2 K)) ∨
      (∃ (f : ℕ) (K : Type) (_ : Field K) (_ : CharP K 2) (h : UnitaryFieldData 2 f K),
        2 ^ f % 3 = 1 ∧ 2 < 2 ^ f ∧ Nonempty (X ≃* unitaryPSU h 3)) ∨
      ∀ α : MulAut X, α ^ 3 = 1 → IsInnerAut α := by
  have hodd : ∀ α : MulAut X, α ^ 3 = 1 → Odd (orderOf α) := fun α hα =>
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hα)
  rcases hX with (⟨n, hn⟩ | ⟨q, hq, hq5, hL⟩ | hJ) | ⟨n, hU⟩
  · obtain ⟨F, _, _, _, -, he⟩ := P22y.exists_equiv_psl2 (P22fin.isL2Ev_of_isL2 hn).1
    exact Or.inl ⟨F, inferInstance, inferInstance, inferInstance, he⟩
  · exact Or.inr (Or.inr fun α hα =>
      KBridge.kOddOutInner_holds X (Or.inr (Or.inl ⟨q, hq, hq5, hL⟩)) α (hodd α hα))
  · exact Or.inr (Or.inr fun α hα =>
      KBridge.kOddOutInner_holds X (Or.inr (Or.inr hJ)) α (hodd α hα))
  · obtain ⟨-, hne, K, _, h, he⟩ :=
      SeitzReduction.UnitaryPilot.exists_mulEquiv_unitaryPSU_of_lieModel hU
    have h3 : ¬ 3 ∣ 2 ^ n + 1 := fun h3 => by
      have := uc22ine229u3e9_two_le_pRank hU h3
      omega
    have h3' : ¬ 3 ∣ 2 ^ n := fun h3 => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    have h2 : 2 ^ n ≠ 2 := fun h2 => hne (by rw [h2])
    have h4 : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h.one_le)
    haveI := h.charP
    refine Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance, h, ?_, by omega, he⟩)
    omega

private theorem three_ne_zero_fixedField {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) :
    (3 : GH74.GLS.IVK.fixedField σ) ≠ 0 := by
  intro h
  have h1 : ((3 : GH74.GLS.IVK.fixedField σ) : K) = 3 :=
    map_ofNat (GH74.GLS.IVK.fixedField σ).subtype 3
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h3 : (3 : K) = 1 := by linear_combination h2
  rw [h, ZeroMemClass.coe_zero, h3] at h1
  exact zero_ne_one h1

private theorem fixedData_psl2 {X : Type} [Group X] {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : X ≃* PSL2 K) {α : MulAut X} (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (∃ M : ℕ, (∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card X) ∧
      ∀ x : X, x ^ 3 = 1 → x ≠ 1 → α x = x → ∃ y : X, α y = y ∧ y * x * y⁻¹ = x⁻¹ := by
  set β := MulAut.congr e α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  obtain ⟨σ, hσ3, ⟨φ⟩⟩ :=
    exists_eqLocus_mulEquiv_psl2 hβ3 (fun h => hout ((isInnerAut_congr e α).mp h))
  have hβe : ∀ x : X, β (e x) = e (α x) := fun x => by
    rw [hβ]
    exact congrArg (fun z => e (α z)) (e.symm_apply_apply x)
  have hfix : ∀ x : X, α x = x → e x ∈ β.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K)) :=
    fun x hx => (hβe x).trans (congrArg e hx)
  refine ⟨⟨Nat.card (PSL2 (GH74.GLS.IVK.fixedField σ)), fun T hT => ?_, ?_⟩,
    fun x hx3 hx1 hx => ?_⟩
  · have hle : T.map e.toMonoidHom ≤ β.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K)) := by
      rintro _ ⟨t, ht, rfl⟩
      exact hfix t (hT t ht)
    rw [← Nat.card_congr φ.toEquiv,
      ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact Subgroup.card_dvd_of_le hle
  · have hK : Nat.card K = Nat.card (GH74.GLS.IVK.fixedField σ) ^ 3 := by
      have h := GH74.GLS.IVK.fixedField_card_pow σ
      rw [hσ3] at h
      exact h.symm
    rw [Nat.card_congr e.toEquiv]
    exact three_mul_card_psl2_subfield_dvd _ rfl hK
  · set x' : β.toMonoidHom.eqLocus (MonoidHom.id (PSL2 K)) := ⟨e x, hfix x hx⟩ with hx'
    have hd3 : φ x' ^ 3 = 1 := by
      rw [← map_pow]
      have : x' ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        show (e x) ^ 3 = 1
        rw [← map_pow, hx3, map_one])
      rw [this, map_one]
    have hd1 : φ x' ≠ 1 := fun h1 => hx1 (e.injective (by
      have h2 : x' = 1 := φ.injective (h1.trans (map_one φ).symm)
      rw [map_one]
      exact congrArg Subtype.val h2))
    obtain ⟨y₀, hy₀⟩ := exists_mul_mul_inv_eq_inv_psl2 (three_ne_zero_fixedField σ) hd3 hd1
    have hy₁ : β ((φ.symm y₀ : β.toMonoidHom.eqLocus _) : PSL2 K) = φ.symm y₀ := (φ.symm y₀).2
    refine ⟨e.symm (φ.symm y₀), e.injective ?_, e.injective ?_⟩
    · rw [← hβe, MulEquiv.apply_symm_apply]
      exact hy₁
    · have h := congrArg (fun z => ((φ.symm z : β.toMonoidHom.eqLocus _) : PSL2 K)) hy₀
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
      exact h

private theorem fixedData_psu {X : Type} [Group X] {f : ℕ} {K : Type} [Field K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (hq : 2 ^ f % 3 = 1) (hq2 : 2 < 2 ^ f)
    (e : X ≃* unitaryPSU h 3) {α : MulAut X} (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (∃ M : ℕ, (∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card X) ∧
      ∃ x₀ y₀ : X, α x₀ = x₀ ∧ α y₀ = y₀ ∧ x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hD : MulAut.congr e α ∉ (psuConj h).range := fun hm =>
    hout ((isInnerAut_congr e α).mp (isInnerAut_of_mem_psuConj_range h hq hm))
  obtain ⟨σ, hσ, H, hβH⟩ := unitary_order_three_field_descent hq2 (MulAut.congr e α) hβ3 hD
  have hτ : MulAut.congr (e.trans (psuConj h H)⁻¹) α = psuField h σ := by
    rw [congr_trans_mulAut, hβH]
    group
  obtain ⟨h₁, h₂⟩ := fixedData_unitary h hq hσ
  rw [← hτ] at h₁ h₂
  exact fixedData_of_congr _ α h₁ h₂

private theorem fixedData {X : Type} [Group X] [Finite X]
    (hX : R8107Shape.ThinShape X ∨ ∃ n : ℕ, IsU3 X n)
    (h1 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1) {α : MulAut X} (hα3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) :
    (∃ M : ℕ, (∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card X) ∧
      ∀ x : X, x ^ 3 = 1 → x ≠ 1 → α x = x → ∃ y : X, α y = y ∧ y * x * y⁻¹ = x⁻¹ := by
  rcases shape_cases hX h1 with ⟨K, _, _, _, ⟨e⟩⟩ | ⟨f, K, _, _, h, hq, hq2, ⟨e⟩⟩ | hinn
  · exact fixedData_psl2 e hα3 hout
  · obtain ⟨h₁, x₀, y₀, hx₀, hy₀, hx₀3, hx₀1, hinv⟩ := fixedData_psu h hq hq2 e hα3 hout
    refine ⟨h₁, fun x hx3 hx1 hx => ?_⟩
    obtain ⟨y, hy, hyx⟩ := exists_conj_eq_inv_of_isCyclic_sylow
      (α.toMonoidHom.eqLocus (MonoidHom.id X)) (isCyclic_sylow h1) (x₀ := x₀) hx₀ hy₀ hx₀3
      hx₀1 hinv (x := x) hx hx3 hx1
    exact ⟨y, hy, hyx⟩
  · exact absurd (hinn α hα3) hout

theorem exists_ne_of_sylow {X : Type} [Group X] [Finite X]
    (hX : R8107Shape.ThinShape X ∨ ∃ n : ℕ, IsU3 X n)
    (h1 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1) {α : MulAut X} (hα3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) (P : Sylow 3 X) : ∃ y ∈ (P : Subgroup X), α y ≠ y := by
  obtain ⟨⟨M, hM, h3M⟩, -⟩ := fixedData hX h1 hα3 hout
  exact exists_ne_of_sylow_of_card_dvd α hM h3M P

theorem exists_inverting_of_fixed {X : Type} [Group X] [Finite X]
    (hX : R8107Shape.ThinShape X ∨ ∃ n : ℕ, IsU3 X n)
    (h1 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1) {α : MulAut X} (hα3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) {x : X} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hx : α x = x) :
    ∃ y : X, α y = y ∧ y * x * y⁻¹ = x⁻¹ :=
  (fixedData hX h1 hα3 hout).2 x hx3 hx1 hx

theorem commute_of_pow_three_eq_one {X : Type} [Group X] [Finite X]
    (hX : R8107Shape.ThinShape X ∨ ∃ n : ℕ, IsU3 X n)
    (h1 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1) {P : Subgroup (MulAut X)}
    (hP : IsPGroup 3 P) {σ τ : MulAut X} (hσP : σ ∈ P) (hτP : τ ∈ P) (hσ : σ ^ 3 = 1)
    (hτ : τ ^ 3 = 1) : σ * τ = τ * σ := by
  refine commute_of_pow_three_eq_one_of_isPGroup (isCyclic_sylow h1) hP ?_ hσP hτP hσ hτ
  intro σ hσP τ hτP hσ3 hτ3 hσout
  rcases shape_cases hX h1 with ⟨K, _, _, _, ⟨e⟩⟩ | ⟨f, K, _, _, h, hq, hq2, ⟨e⟩⟩ | hinn
  · exact exists_pow_mul_isInnerAut_of_mulEquiv_psl2 e hP hσP hτP hσ3 hσout hτ3
  · by_cases hτi : IsInnerAut τ
    · exact ⟨0, by rwa [pow_zero, one_mul]⟩
    · exact exists_pow_mul_isInnerAut_of_mulEquiv_unitaryPSU h hq hq2 e hσ3 hσout hτ3 hτi
  · exact absurd (hinn σ hσ3) hσout

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out
