module

public import CFSG.RankThree.PartOne.KLC.Transport
public import CFSG.RankThree.PartOne.KLC.PRankTwo
public import CFSG.RankThree.PartOne.KE.CTStatement
import CFSG.Blueprint.LieModelAPI
public import CFSG.RankThree.PartOne.S11c.Sec66TModels

public section

namespace CFSG.RankThree.PartOne.KLC

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedLieTag)

open CFSG.RankThree.Chevalley (exhaustionPhi)

open CFSG.RankThree.PartOne.KE (CyclicSylowConclusion')


section Generic

theorem not_commute_involution_of_cyclicSylow {C : Type} [Group C] {p n₀ d : ℕ}
    (h : CyclicSylowConclusion' C p n₀ d) (hn₀ : Odd n₀) {x y : C} (hx : orderOf x = p)
    (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) : False := by
  obtain ⟨T, -, hTn, -, -, -, -, hcent⟩ := h
  obtain ⟨g, -, hg⟩ := hcent x hx
  have hy' : g * y * g⁻¹ ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set C) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hxy]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  rw [hg] at hy'
  have hord : orderOf (g * y * g⁻¹) = 2 := by
    have h1 : (g * y * g⁻¹) ^ 2 = 1 := by
      calc (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := conj_pow
        _ = 1 := by rw [hy2]; group
    have h2 : g * y * g⁻¹ ≠ 1 := fun h => hy1 (by
      have := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using this)
    exact orderOf_eq_prime h1 h2
  have h3 := orderOf_dvd_natCard (⟨g * y * g⁻¹, hy'⟩ : T)
  rw [Subgroup.orderOf_mk, hord] at h3
  exact (Nat.not_even_iff_odd.2 hn₀) (even_iff_two_dvd.2 (h3.trans hTn))

end Generic

section Sectors


@[expose] def LayerSectorY (τ : Tag) (e : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f₀ : ℕ), p.Prime → 5 ≤ p → 1 ≤ f₀ →
    Nat.card K = 2 ^ (p * f₀) → ∀ σ : K ≃+* K, orderOf σ = p →
    (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) → CFSG.pRank p (adjointGroup τ K) = 1 →
    ∀ x : adjointGroup τ K, x ^ p = 1 → x ≠ 1 → entrywiseAdjointAut τ σ x = x →
    ∀ y : adjointGroup τ K, y ^ 2 = 1 → y ≠ 1 → x * y = y * x →
      LieLayerData p (entrywiseAdjointAut τ σ)
        (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))

theorem LayerSector.toY {τ : Tag} {e : ℕ} (h : LayerSector τ e) : LayerSectorY τ e :=
  fun K _ _ p f₀ hp hp5 hf₀ hKcard σ hσ hpe hpr x hx hx1 hxσ _ _ _ _ =>
    h K p f₀ hp hp5 hf₀ hKcard σ hσ hpe hpr x hx hx1 hxσ

theorem not_dvd_of_eq_two_pow {p f n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n = 2 ^ f) :
    ¬ p ∣ n := by
  intro h
  rw [hn] at h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem LayerSectorY.of_two_le {τ : Tag} {e : ℕ}
    (h : ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → ¬ p ∣ Nat.card K →
      (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) → 2 ≤ CFSG.pRank p (adjointGroup τ K)) :
    LayerSectorY τ e := by
  intro K _ _ p f₀ hp hp5 hf₀ hKcard σ hσ hpe hpr
  exfalso
  have := h K p hp hp5 (not_dvd_of_eq_two_pow hp hp5 hKcard) hpe
  omega

theorem LayerSectorY.of_no_commuting {τ : Tag} {e : ℕ}
    (h : ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → Even (Nat.card K) →
      (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) → ∀ x y : adjointGroup τ K,
        orderOf x = p → y ^ 2 = 1 → y ≠ 1 → x * y = y * x → False) :
    LayerSectorY τ e := by
  intro K _ _ p f₀ hp hp5 hf₀ hKcard σ hσ hpe hpr x hx hx1 hxσ y hy2 hy1 hxy
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hK2 : Even (Nat.card K) := by
    rw [hKcard]
    exact Nat.even_pow.2 ⟨even_two, Nat.pos_iff_ne_zero.1 (Nat.mul_pos hp.pos hf₀)⟩
  exact h K p hp hp5 hK2 hpe x y (orderOf_eq_prime hx hx1) hy2 hy1 hxy

end Sectors

section Descent


@[expose] def StdForm (t : StatedLieTag) (τ : Tag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p f₀ : ℕ), p.Prime → 5 ≤ p → 1 ≤ f₀ →
    LieModel T t 0 2 (p * f₀) → ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T →
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K) (φ : T ≃* adjointGroup τ K),
      Nat.card K = 2 ^ (p * f₀) ∧ orderOf σ = p ∧
        MulAut.congr φ α = entrywiseAdjointAut τ σ

theorem chevalleyModel_of_lieModel {T : Type} [Group T] {t : StatedLieTag} {n f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (hM : LieModel T t n 2 f) :
    n = 0 ∧ ChevalleyExceptionalModel T t 2 f :=
  (CFSG.Blueprint.LieModel.chevalleyExceptional_iff ht).1 hM

theorem lieGood_of_sectors {t : StatedLieTag} {τ : Tag} (ht : untwistedTag t = some τ)
    (hdesc : StdForm t τ) (row : Finset ℕ)
    (hex : ∀ {T : Type} [Group T] [Finite T] {p f : ℕ}, p.Prime → 5 ≤ p →
      ChevalleyExceptionalModel T t 2 f → p ∣ Nat.card T →
      ∃ m ∈ row, (p : ℤ) ∣ (exhaustionPhi m).eval ((2 ^ f : ℕ) : ℤ))
    (hsec : ∀ m ∈ row, LayerSectorY τ m) : LieGoodComponentFixT t := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx y hy2 hy1 hxy
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : n = 0 := ((lieModel_untwisted_iff ht).mp hM).1
  subst hn0
  have htag : t ∈ chevalleyExceptionalTags := by
    cases t <;> simp only [untwistedTag, reduceCtorEq, Option.some.injEq] at ht <;> decide
  obtain ⟨-, hCEM⟩ := chevalleyModel_of_lieModel htag hM
  have hdvd : p ∣ Nat.card T := by
    have := orderOf_dvd_natCard x
    rwa [orderOf_eq_prime hxp hx1] at this
  obtain ⟨m, hm, hpm⟩ := hex hp hp5 hCEM hdvd
  obtain ⟨K, _, _, σ, φ, hKcard, hσord, hφα⟩ := hdesc T p f₀ hp hp5 hf₀ hM α hαp hαinn
  rw [← hKcard] at hpm
  have hx' : (φ x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hx1' : φ x ≠ 1 := fun h => hx1 (φ.injective (by rw [h, map_one]))
  have hxσ : entrywiseAdjointAut τ σ (φ x) = φ x := by
    rw [← hφα]
    simp [MulAut.congr_apply, hαx]
  have hy2' : (φ y) ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hy1' : φ y ≠ 1 := fun h => hy1 (φ.injective (by rw [h, map_one]))
  have hxy' : φ x * φ y = φ y * φ x := by rw [← map_mul, ← map_mul, hxy]
  have hpr' : CFSG.pRank p (adjointGroup τ K) = 1 := by
    rw [← pRank_congr_mulEquiv φ hp.one_lt]
    exact hpr
  have hld := hsec m hm K p f₀ hp hp5 hf₀ hKcard σ hσord hpm hpr' (φ x) hx' hx1' hxσ (φ y) hy2'
    hy1' hxy'
  rw [← hφα] at hld
  exact LieLayerData.conclusion_of_mulEquiv φ α x hld

end Descent

end CFSG.RankThree.PartOne.KLC
