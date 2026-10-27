module

public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockOrth
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
public import CFSG.LieType.Chevalley.RankOneGaussian

public noncomputable section

namespace CFSG.OddTranspositions.PartFour

open Matrix Module QuadraticMap CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Plane

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private abbrev planeSet (γ : K) : Set (K × K) :=
  {p | p.1 * p.1 + p.2 * p.2 + p.1 * p.2 * γ = 1}

private theorem ncard_planeSet_le_succ (γ : K) : (planeSet γ).ncard ≤ Nat.card K + 1 := by
  classical
  let φ : K × K → Option K := fun p => if p.2 = 0 then none else some (p.1 / p.2)
  have hφ : Set.InjOn φ (planeSet γ) := by
    rintro ⟨α, δ⟩ hp ⟨α', δ'⟩ hp' h
    simp only [planeSet, Set.mem_setOf_eq] at hp hp'
    by_cases hδ : δ = 0 <;> by_cases hδ' : δ' = 0
    · subst hδ hδ'
      have h1 : α ^ 2 = α' ^ 2 := by linear_combination hp - hp'
      rw [CharTwo.sq_inj.mp h1]
    · simp [φ, hδ, hδ'] at h
    · simp [φ, hδ, hδ'] at h
    · simp only [φ, hδ, hδ', if_false, Option.some.injEq] at h
      obtain ⟨ρ, rfl, rfl⟩ : ∃ ρ : K, α = ρ * δ ∧ α' = ρ * δ' :=
        ⟨α / δ, (div_mul_cancel₀ α hδ).symm, by rw [h]; exact (div_mul_cancel₀ α' hδ').symm⟩
      have h1 : (δ * δ) * (ρ * ρ + 1 + ρ * γ) = 1 := by linear_combination hp
      have h2 : (δ' * δ') * (ρ * ρ + 1 + ρ * γ) = 1 := by linear_combination hp'
      have hg : ρ * ρ + 1 + ρ * γ ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at h1
        exact zero_ne_one h1
      have h3 : δ ^ 2 = δ' ^ 2 := by
        have := mul_right_cancel₀ hg (h1.trans h2.symm)
        linear_combination this
      rw [CharTwo.sq_inj.mp h3]
  calc (planeSet γ).ncard ≤ (Set.univ : Set (Option K)).ncard :=
        Set.ncard_le_ncard_of_injOn φ (fun _ _ => Set.mem_univ _) hφ Set.finite_univ
    _ = Nat.card K + 1 := by rw [Set.ncard_univ, Finite.card_option]

private theorem ncard_planeSet_le_pred {γ t : K} (hγ : γ ≠ 0) (ht : t * t + γ * t + 1 = 0) :
    (planeSet γ).ncard ≤ Nat.card K - 1 := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  let φ : K × K → K := fun p => p.1 + t * p.2
  have hprod : ∀ p ∈ planeSet γ, (p.1 + t * p.2) * (p.1 + (γ + t) * p.2) = 1 := by
    rintro ⟨α, δ⟩ hp
    simp only [planeSet, Set.mem_setOf_eq] at hp
    linear_combination hp + δ ^ 2 * ht + (t * α * δ - δ ^ 2) * h22
  have hne : ∀ p ∈ planeSet γ, φ p ≠ 0 := by
    intro p hp h0
    have h1 := hprod p hp
    simp only [φ] at h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hinj : Set.InjOn φ (planeSet γ) := by
    rintro ⟨α, δ⟩ hp ⟨α', δ'⟩ hp' h
    have e1 := hprod _ hp
    have e2 := hprod _ hp'
    simp only [φ] at h e1 e2
    have hu : α + t * δ ≠ 0 := hne _ hp
    have hw : α + (γ + t) * δ = α' + (γ + t) * δ' := by
      rw [← h] at e2
      exact mul_left_cancel₀ hu (e1.trans e2.symm)
    have h5 : γ * δ = γ * δ' := by linear_combination hw - h
    have h6 : δ = δ' := mul_left_cancel₀ hγ h5
    have h7 : α = α' := by
      rw [h6] at h
      linear_combination h
    rw [h6, h7]
  calc (planeSet γ).ncard ≤ (Set.univ \ {0} : Set K).ncard :=
        Set.ncard_le_ncard_of_injOn φ
          (fun p hp => ⟨Set.mem_univ _, fun h0 => hne p hp (Set.mem_singleton_iff.mp h0)⟩)
          hinj (Set.toFinite _)
    _ = Nat.card K - 1 := by
        rw [Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]

end Plane

section DoublePerp

variable {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

private theorem exists_smul_add_smul_map_eq_one (hω : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1) {r u : V}
    (hru : polar Q r u = 1) : ∃ a e : K, a ≠ 0 ∧ Q (a • u + e • r) = 1 := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨t, ht⟩ : ∃ t : K, Q r * (t * t) + t + Q u ≠ 0 := by
    by_contra! h
    obtain ⟨ω, hω0, hω1⟩ := hω
    have hQu : Q u = 0 := by simpa using h 0
    have hQr : Q r = 1 := by
      have h1 := h 1
      linear_combination h1 - hQu - h22
    have hω' := h ω
    rw [hQr, hQu, one_mul, add_zero] at hω'
    have h3 : ω * (ω + 1) = 0 := by linear_combination hω'
    rcases mul_eq_zero.mp h3 with h0 | h0
    · exact hω0 h0
    · exact hω1 (CharTwo.add_eq_zero.mp h0)
  obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
    (Q r * (t * t) + t + Q u)⁻¹
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero, inv_eq_zero] at ha
    exact ht ha
  have hur : polar Q u r = 1 := by rw [polar_comm]; exact hru
  refine ⟨a, a * t, ha0, ?_⟩
  have hg : (a * a) * (Q r * (t * t) + t + Q u) = 1 := by
    rw [← ha]
    exact inv_mul_cancel₀ ht
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
    polar_smul_right, hur]
  simp only [smul_eq_mul]
  linear_combination hg

theorem exists_eq_smul_add_smul_of_forall_map_eq_one [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) (hω : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1) {b c x : V}
    (hbc : polar Q b c ≠ 0)
    (h : ∀ w, Q w = 1 → polar Q w b = 0 → polar Q w c = 0 → polar Q x w = 0) :
    ∃ α β : K, x = α • b + β • c := by
  have hbb : polar Q b b = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hcc : polar Q c c = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hcb : polar Q c b = polar Q b c := polar_comm Q c b
  obtain ⟨xP, hxP⟩ : ∃ xP : V,
      xP = (polar Q x c / polar Q b c) • b + (polar Q x b / polar Q b c) • c := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : V, r = x - xP := ⟨_, rfl⟩
  have hxPb : polar Q xP b = polar Q x b := by
    rw [hxP, polar_add_left, polar_smul_left, polar_smul_left, hbb, hcb, smul_eq_mul,
      smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hbc]
  have hxPc : polar Q xP c = polar Q x c := by
    rw [hxP, polar_add_left, polar_smul_left, polar_smul_left, hcc, smul_eq_mul, smul_eq_mul,
      mul_zero, add_zero, div_mul_cancel₀ _ hbc]
  have hrb : polar Q r b = 0 := by rw [hr, polar_sub_left, hxPb, sub_self]
  have hrc : polar Q r c = 0 := by rw [hr, polar_sub_left, hxPc, sub_self]
  have hbr : polar Q b r = 0 := by rw [polar_comm]; exact hrb
  have hcr : polar Q c r = 0 := by rw [polar_comm]; exact hrc
  have hxPr : polar Q xP r = 0 := by
    rw [hxP, polar_add_left, polar_smul_left, polar_smul_left, hbr, hcr, smul_zero, smul_zero,
      add_zero]
  have hrr : polar Q r r = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hxr : polar Q x r = 0 := by
    have hx : x = xP + r := by rw [hr]; abel
    rw [hx, polar_add_left, hxPr, hrr, add_zero]
  refine exists_eq_smul_add_smul_of_forall_polar_eq_zero hQ ?_
  intro w hwb hwc
  by_contra hxw
  obtain ⟨u, hub, huc, hxu⟩ : ∃ u, polar Q u b = 0 ∧ polar Q u c = 0 ∧ polar Q x u = 1 :=
    ⟨(polar Q x w)⁻¹ • w, by rw [polar_smul_left, hwb, smul_zero],
      by rw [polar_smul_left, hwc, smul_zero],
      by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hxw]⟩
  have hxPu : polar Q xP u = 0 := by
    rw [hxP, polar_add_left, polar_smul_left, polar_smul_left, polar_comm Q b u, polar_comm Q c u,
      hub, huc, smul_zero, smul_zero, add_zero]
  have hru : polar Q r u = 1 := by
    rw [hr, polar_sub_left, hxPu, sub_zero]
    exact hxu
  obtain ⟨a, e, ha, hy⟩ := exists_smul_add_smul_map_eq_one hω hru
  have hyb : polar Q (a • u + e • r) b = 0 := by
    rw [polar_add_left, polar_smul_left, polar_smul_left, hub, hrb, smul_zero, smul_zero,
      add_zero]
  have hyc : polar Q (a • u + e • r) c = 0 := by
    rw [polar_add_left, polar_smul_left, polar_smul_left, huc, hrc, smul_zero, smul_zero,
      add_zero]
  have h0 := h _ hy hyb hyc
  rw [polar_add_right, polar_smul_right, polar_smul_right, hxu, hxr, smul_eq_mul, smul_eq_mul,
    mul_one, mul_zero, add_zero] at h0
  exact ha h0

end DoublePerp

section Model

variable {X : Type} [Group X] {K : Type} [Field K] [CharP K 2] {m : ℕ}
  {Q : QuadraticForm K (Fin m → K)}

private theorem polar_self_eq_zero' {V : Type*} [AddCommGroup V] [Module K V]
    (R : QuadraticForm K V) (x : V) : polar R x x = 0 := by
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

omit [CharP K 2] in
private theorem ne_zero_of_map_eq_one' {V : Type*} [AddCommGroup V] [Module K V]
    {R : QuadraticForm K V} {x : V} (hx : R x = 1) : x ≠ 0 := fun h => by
  rw [h, QuadraticMap.map_zero] at hx
  exact zero_ne_one hx

private theorem commute_symmetryGL_iff (hQ : Q.polarBilin.Nondegenerate) {x y : Fin m → K}
    (hx : Q x = 1) (hy : Q y = 1) :
    Commute (symmetryGL Q x) (symmetryGL Q y) ↔ polar Q x y = 0 := by
  have h1 : Commute (symmetryGL Q x) (symmetryGL Q y) ↔
      symmetryGL Q x ∈ Subgroup.centralizer {symmetryGL Q y} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Iff.rfl
  rw [h1, mem_centralizer_symmetryGL_iff hQ hy (symmetryGL_mem Q x),
    symmetryGL_mulVec_of_charTwo hx, add_eq_left, smul_eq_zero]
  simp [ne_zero_of_map_eq_one' hx]

private theorem commute_iff_of_symmetryGL (hQ : Q.polarBilin.Nondegenerate)
    {ψ : X →* GL (Fin m) K} (hψ : Function.Injective ψ) {t t' : X} {x y : Fin m → K}
    (hx : Q x = 1) (hy : Q y = 1) (ht : ψ t = symmetryGL Q x) (ht' : ψ t' = symmetryGL Q y) :
    Commute t t' ↔ polar Q x y = 0 := by
  rw [← commute_symmetryGL_iff hQ hx hy, ← ht, ← ht']
  exact ⟨fun h => h.map ψ, fun h => hψ (by rw [map_mul, map_mul]; exact h.eq)⟩

omit [CharP K 2] in
private theorem exists_vec_of_isConj {ψ : X →* GL (Fin m) K}
    (hrange : ψ.range = matrixIsometries Q) {s : X} {v : Fin m → K} (hv : Q v = 1)
    (hψs : ψ s = symmetryGL Q v) {t : X} (ht : IsConj s t) :
    ∃ x, Q x = 1 ∧ ψ t = symmetryGL Q x := by
  have hψmem : ∀ g, ψ g ∈ matrixIsometries Q := fun g => hrange ▸ ⟨g, rfl⟩
  obtain ⟨c, rfl⟩ := isConj_iff.mp ht
  refine ⟨(ψ c : Matrix (Fin m) (Fin m) K) *ᵥ v, ?_, ?_⟩
  · rw [← hv]
    exact (mem_matrixIsometries_iff Q _).mp (hψmem c) v
  · rw [map_mul, map_mul, map_inv, hψs, conj_symmetryGL (hψmem c)]

private theorem exists_map_eq_one_polar_eq [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hm : 4 ≤ m) {v : Fin m → K} (hv : Q v = 1) (γ : K) :
    ∃ c, Q c = 1 ∧ polar Q v c = γ := by
  have hdim : 3 ≤ finrank K (Fin m → K) := by
    rw [Module.finrank_fin_fun]
    omega
  obtain ⟨z, hvz⟩ : ∃ z, polar Q v z ≠ 0 := by
    by_contra! h0
    exact ne_zero_of_map_eq_one' hv
      (hQ.1 v fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h0 y)
  obtain ⟨c, hcv, -, hc⟩ := exists_polar_eq_map_eq_of_polar_ne_zero hQ hdim hvz γ 0 1
  exact ⟨c, hc, by rw [polar_comm]; exact hcv⟩

private theorem exists_ne_zero_ne_one_of_two_le {F : Type} [Field F] [Finite F] {f : ℕ}
    (hf : 2 ≤ f) (hcard : Nat.card F = 2 ^ f) : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
  by_contra! h
  have hsurj : Function.Surjective (![0, 1] : Fin 2 → F) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [h x hx]⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

end Model

section TwoByTwo

variable {K : Type} [Field K]

private def powCoeff (τ : K) : ℕ → K × K
  | 0 => (0, 1)
  | n + 1 => (τ * (powCoeff τ n).1 + (powCoeff τ n).2, -(powCoeff τ n).1)

private theorem pow_eq_powCoeff {M : Matrix (Fin 2) (Fin 2) K} {τ : K}
    (hM : M ^ 2 = τ • M - 1) (n : ℕ) :
    M ^ n = (powCoeff τ n).1 • M + (powCoeff τ n).2 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  induction n with
  | zero => simp [powCoeff]
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [powCoeff, add_mul, smul_mul_assoc, one_mul]
    rw [← _root_.sq, hM]
    simp only [smul_sub, smul_smul, add_smul, neg_smul]
    rw [mul_comm (powCoeff τ n).1 τ]
    abel

private theorem pow_eq_one_iff_powCoeff {M : Matrix (Fin 2) (Fin 2) K} {τ : K}
    (hM : M ^ 2 = τ • M - 1) (hns : ∀ c : K, M ≠ c • 1) (n : ℕ) :
    M ^ n = 1 ↔ (powCoeff τ n).1 = 0 ∧ (powCoeff τ n).2 = 1 := by
  rw [pow_eq_powCoeff hM n]
  generalize (powCoeff τ n).1 = α
  generalize (powCoeff τ n).2 = β
  constructor
  · intro h
    by_cases hα : α = 0
    · subst hα
      refine ⟨rfl, ?_⟩
      have h00 := congrFun (congrFun h 0) 0
      simpa using h00
    · exfalso
      refine hns (α⁻¹ * (1 - β)) ?_
      have h' : α • M = (1 - β) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [sub_smul, one_smul, eq_sub_iff_add_eq]
        exact h
      calc M = α⁻¹ • (α • M) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
        _ = α⁻¹ • ((1 - β) • (1 : Matrix (Fin 2) (Fin 2) K)) := by rw [h']
        _ = (α⁻¹ * (1 - β)) • 1 := by rw [smul_smul]
  · rintro ⟨rfl, rfl⟩
    simp

variable [CharP K 2]

private def planeMat (γ : K) : Matrix (Fin 2) (Fin 2) K := !![1 + γ ^ 2, γ; γ, 1]

private theorem planeMat_sq (γ : K) : planeMat γ ^ 2 = γ ^ 2 • planeMat γ - 1 := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeMat, _root_.sq, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (1 + γ * γ) * h22
  · linear_combination γ * h22
  · linear_combination γ * h22
  · linear_combination h22

omit [CharP K 2] in
private theorem planeMat_ne_smul {γ : K} (hγ : γ ≠ 0) (c : K) : planeMat γ ≠ c • 1 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [planeMat] at h01
  exact hγ h01

private theorem orderOf_planeMat_eq {A : CFSG.LieType.Chevalley.SL2 K} {γ : K} (hγ : γ ≠ 0)
    (hτ : γ * γ = Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) :
    orderOf (planeMat γ) = orderOf A := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hMsq : (A : Matrix (Fin 2) (Fin 2) K) ^ 2 =
      (γ * γ) • (A : Matrix (Fin 2) (Fin 2) K) - 1 := by
    have := CFSG.SeitzReduction.F4Pilot.sq_eq_trace_smul_sub_one A
    rw [Matrix.SpecialLinearGroup.coe_pow] at this
    rw [hτ]
    exact this
  have hns : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • 1 := by
    intro c hc
    apply hγ
    apply mul_self_eq_zero.mp
    rw [hτ, hc]
    simp
    exact Or.inr h22
  have hN : planeMat γ ^ 2 = (γ * γ) • planeMat γ - 1 := by rw [planeMat_sq, _root_.sq]
  refine orderOf_eq_orderOf_iff.2 fun n => ?_
  rw [pow_eq_one_iff_powCoeff hN (planeMat_ne_smul hγ) n,
    ← pow_eq_one_iff_powCoeff hMsq hns n, ← Matrix.SpecialLinearGroup.coe_pow,
    ← Matrix.SpecialLinearGroup.coe_one]
  exact Subtype.coe_inj

private theorem exists_planeMat_orderOf_succ [Finite K] :
    ∃ γ : K, γ ≠ 0 ∧ orderOf (planeMat γ) = Nat.card K + 1 := by
  obtain ⟨A, hA⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := K)
  obtain ⟨τ, hτ⟩ : ∃ τ : K, τ = Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) := ⟨_, rfl⟩
  have hτ0 : τ ≠ 0 := by
    intro h0
    have hMsq := CFSG.SeitzReduction.F4Pilot.sq_eq_trace_smul_sub_one A
    rw [← hτ, h0, zero_smul, zero_sub] at hMsq
    have hA2 : A ^ 2 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one, hMsq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]
    have h2 := orderOf_dvd_of_pow_eq_one hA2
    rw [hA] at h2
    have h3 := CFSG.SeitzReduction.F4Pilot.three_le_natCard_add_one (K := K)
    have h4 := Nat.le_of_dvd two_pos h2
    omega
  obtain ⟨γ, hγ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) τ
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    exact hτ0 (by rw [hγ]; ring)
  exact ⟨γ, hγ0, (orderOf_planeMat_eq hγ0 (by rw [← hγ, hτ])).trans hA⟩

private theorem exists_planeMat_orderOf_pred [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ γ t : K, γ ≠ 0 ∧ t * t + γ * t + 1 = 0 ∧ orderOf (planeMat γ) = Nat.card K - 1 := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨l, hl⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hl
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hl
    omega
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (l : K)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact l.ne_zero (by rw [hμ, mul_zero])
  have hμ1 : μ * μ ≠ 1 := fun h => hl1 (Units.ext (by rw [hμ, h, Units.val_one]))
  have hμμ : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ0
  have hγ0 : μ + μ⁻¹ ≠ 0 := by
    intro h
    apply hμ1
    have h1 : μ * μ + 1 = 0 := by
      have := congrArg (μ * ·) h
      simp only [mul_add, mul_zero, hμμ] at this
      exact this
    exact CharTwo.add_eq_zero.mp h1
  refine ⟨μ + μ⁻¹, μ, hγ0, ?_, ?_⟩
  · have e : (μ + μ⁻¹) * μ = μ * μ + 1 := by rw [add_mul, inv_mul_cancel₀ hμ0]
    linear_combination e + (μ * μ + 1) * h22
  · have htr : Matrix.trace ((CFSG.LieType.Chevalley.HSL l : CFSG.LieType.Chevalley.SL2 K) :
        Matrix (Fin 2) (Fin 2) K) = (l : K) + (l : K)⁻¹ := by
      rw [CFSG.LieType.Chevalley.coe_HSL, Matrix.trace_fin_two]
      simp
    have hsq : (μ + μ⁻¹) * (μ + μ⁻¹) =
        Matrix.trace ((CFSG.LieType.Chevalley.HSL l : CFSG.LieType.Chevalley.SL2 K) :
          Matrix (Fin 2) (Fin 2) K) := by
      rw [htr, hμ, mul_inv]
      linear_combination (μ * μ⁻¹) * h22
    rw [orderOf_planeMat_eq hγ0 hsq, CFSG.SeitzReduction.F4Pilot.orderOf_HSL, hl]

end TwoByTwo

section Order

variable {K : Type} [Field K] [CharP K 2] {m : ℕ} {Q : QuadraticForm K (Fin m → K)}

private theorem mulVec_symmetryGL_mul {a b : Fin m → K} (ha : Q a = 1) (hb : Q b = 1) {γ : K}
    (hab : polar Q a b = γ) (z : Fin m → K) :
    ((symmetryGL Q a * symmetryGL Q b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ z =
      z + polar Q b z • b + (polar Q a z + polar Q b z * γ) • a := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, symmetryGL_mulVec_of_charTwo hb,
    symmetryGL_mulVec_of_charTwo ha, polar_add_right, polar_smul_right, hab, smul_eq_mul]

private theorem pow_symmetryGL_mul_eq_one_iff {a b : Fin m → K} (ha : Q a = 1) (hb : Q b = 1)
    {γ : K} (hγ : γ ≠ 0) (hab : polar Q a b = γ) (n : ℕ) :
    (symmetryGL Q a * symmetryGL Q b) ^ n = 1 ↔ planeMat γ ^ n = 1 := by
  have haa := polar_self_eq_zero' Q a
  have hbb := polar_self_eq_zero' Q b
  have hba : polar Q b a = γ := by rw [polar_comm]; exact hab
  have hTz := mulVec_symmetryGL_mul ha hb hab
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin m) (Fin m) K,
      T = ((symmetryGL Q a * symmetryGL Q b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    ⟨_, rfl⟩
  rw [← hT] at hTz
  let lam : (Fin 2 → K) → Fin m → K := fun c => c 0 • a + c 1 • b
  let phi : (Fin m → K) → Fin 2 → K := fun z => ![γ⁻¹ * polar Q b z, γ⁻¹ * polar Q a z]
  have hphilam : ∀ c, phi (lam c) = c := by
    intro c
    ext i
    fin_cases i
    · simp only [phi, lam, polar_add_right, polar_smul_right, hba, hbb, smul_eq_mul]
      simp
      field_simp
    · simp only [phi, lam, polar_add_right, polar_smul_right, hab, haa, smul_eq_mul]
      simp
      field_simp
  have hTlam : ∀ c, T *ᵥ lam c = lam (planeMat γ *ᵥ c) := by
    intro c
    rw [hTz]
    simp only [lam, planeMat, polar_add_right, polar_smul_right, hba, hbb, hab, haa, smul_eq_mul]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    module
  have hphisub : ∀ z w, phi (z - w) = phi z - phi w := by
    intro z w
    ext i
    fin_cases i <;> simp [phi, polar_sub_right, mul_sub]
  have hfix : ∀ z, phi z = 0 → T *ᵥ z = z := by
    intro z hz
    have h0 : γ⁻¹ * polar Q b z = 0 := by simpa [phi] using congrFun hz 0
    have h1 : γ⁻¹ * polar Q a z = 0 := by simpa [phi] using congrFun hz 1
    have h0' : polar Q b z = 0 := (mul_eq_zero.mp h0).resolve_left (inv_ne_zero hγ)
    have h1' : polar Q a z = 0 := (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hγ)
    rw [hTz, h0', h1']
    simp
  have hpow : ∀ (k : ℕ) (z : Fin m → K),
      (T ^ k) *ᵥ z = lam ((planeMat γ ^ k) *ᵥ phi z) + (z - lam (phi z)) := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      have hz : phi (z - lam (phi z)) = 0 := by rw [hphisub, hphilam, sub_self]
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih z, Matrix.mulVec_add, hTlam,
        hfix _ hz, pow_succ', ← Matrix.mulVec_mulVec]
  rw [← Units.val_eq_one, Units.val_pow_eq_pow_val, ← hT]
  constructor
  · intro h
    rw [Matrix.ext_iff_mulVec]
    intro c
    have h1 := hpow n (lam c)
    rw [h, Matrix.one_mulVec, hphilam, sub_self, add_zero] at h1
    have h2 := congrArg phi h1
    rw [hphilam, hphilam] at h2
    rw [Matrix.one_mulVec]
    exact h2.symm
  · intro h
    rw [Matrix.ext_iff_mulVec]
    intro z
    rw [hpow n z, h, Matrix.one_mulVec, Matrix.one_mulVec, add_sub_cancel]

end Order

section Assembly

variable {X : Type} [Group X] {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
  {Q : QuadraticForm K (Fin m → K)} {ψ : X →* GL (Fin m) K}

private theorem ncard_line_le {s : X} {v : Fin m → K} (hQ : Q.polarBilin.Nondegenerate)
    (hψ : Function.Injective ψ) (hrange : ψ.range = matrixIsometries Q) (hv : Q v = 1)
    (hψs : ψ s = symmetryGL Q v) (hω : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1)
    (hrefl : ∀ x : Fin m → K, Q x = 1 → ∃ t, IsConj s t ∧ ψ t = symmetryGL Q x)
    {tb tc : X} {b c : Fin m → K} (hb : Q b = 1) (hc : Q c = 1) (hγ : polar Q b c ≠ 0)
    (htb : ψ tb = symmetryGL Q b) (htc : ψ tc = symmetryGL Q c) :
    {z | z ∈ {x | IsConj s x} ∧ ∀ y ∈ {x | IsConj s x}, Commute y tb → Commute y tc →
      Commute y z}.ncard ≤ (planeSet (polar Q b c)).ncard := by
  classical
  have hplane : ∀ α δ : K, Q (α • b + δ • c) = α * α + δ * δ + α * δ * polar Q b c := by
    intro α δ
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
      polar_smul_right, hb, hc]
    simp only [smul_eq_mul]
    ring
  set ι : K × K → GL (Fin m) K := fun p => symmetryGL Q (p.1 • b + p.2 • c) with hι
  have hsub : ∀ z ∈ {z | z ∈ {x | IsConj s x} ∧ ∀ y ∈ {x | IsConj s x}, Commute y tb →
      Commute y tc → Commute y z}, ψ z ∈ ι '' planeSet (polar Q b c) := by
    rintro z ⟨hzE, hz⟩
    obtain ⟨x, hx, hψz⟩ := exists_vec_of_isConj hrange hv hψs hzE
    obtain ⟨α, δ, hαδ⟩ := exists_eq_smul_add_smul_of_forall_map_eq_one hQ hω hγ
      fun w hw hwb hwc => by
        obtain ⟨y, hyE, hψy⟩ := hrefl w hw
        have hyb : Commute y tb := (commute_iff_of_symmetryGL hQ hψ hw hb hψy htb).mpr hwb
        have hyc : Commute y tc := (commute_iff_of_symmetryGL hQ hψ hw hc hψy htc).mpr hwc
        rw [polar_comm]
        exact (commute_iff_of_symmetryGL hQ hψ hw hx hψy hψz).mp (hz y hyE hyb hyc)
    refine ⟨(α, δ), ?_, ?_⟩
    · show α * α + δ * δ + α * δ * polar Q b c = 1
      rw [← hplane, ← hαδ]
      exact hx
    · show symmetryGL Q (α • b + δ • c) = ψ z
      rw [← hαδ, hψz]
  calc _ ≤ (ι '' planeSet (polar Q b c)).ncard :=
        Set.ncard_le_ncard_of_injOn ψ hsub hψ.injOn (Set.toFinite _)
    _ ≤ (planeSet (polar Q b c)).ncard := Set.ncard_image_le (Set.toFinite _)

private theorem exists_line_of_model {s : X} {v : Fin m → K} (hQ : Q.polarBilin.Nondegenerate)
    (hm : 4 ≤ m) (hψ : Function.Injective ψ) (hrange : ψ.range = matrixIsometries Q)
    (hv : Q v = 1) (hψs : ψ s = symmetryGL Q v) (hω : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1)
    (hrefl : ∀ x : Fin m → K, Q x = 1 → ∃ t, IsConj s t ∧ ψ t = symmetryGL Q x) {γ : K}
    (hγ : γ ≠ 0) :
    ∃ w ∈ {x | IsConj s x}, ¬ Commute s w ∧ orderOf (s * w) = orderOf (planeMat γ) ∧
      {z | z ∈ {x | IsConj s x} ∧ ∀ y ∈ {x | IsConj s x}, Commute y s → Commute y w →
        Commute y z}.ncard ≤ (planeSet γ).ncard := by
  obtain ⟨c, hc, hvc⟩ := exists_map_eq_one_polar_eq hQ hm hv γ
  obtain ⟨w, hwE, hψw⟩ := hrefl c hc
  refine ⟨w, hwE, ?_, ?_, ?_⟩
  · intro hcomm
    exact hγ (by rw [← hvc]; exact (commute_iff_of_symmetryGL hQ hψ hv hc hψs hψw).mp hcomm)
  · rw [← orderOf_injective ψ hψ (s * w), map_mul, hψs, hψw]
    exact orderOf_eq_orderOf_iff.2 (pow_symmetryGL_mul_eq_one_iff hv hc hγ hvc)
  · have := ncard_line_le hQ hψ hrange hv hψs hω hrefl hv hc (by rw [hvc]; exact hγ) hψs hψw
    rwa [hvc] at this

end Assembly

theorem exists_hypLine_succ_of_isOrthReflection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hf : 2 ≤ f)
    (hs : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) :
    ∃ v ∈ {x | IsConj s x}, ∃ w ∈ {x | IsConj s x}, ¬ Commute v w ∧
      orderOf (v * w) = 2 ^ f + 1 ∧
      {z | z ∈ {x | IsConj s x} ∧ ∀ y ∈ {x | IsConj s x}, Commute y v → Commute y w →
        Commute y z}.ncard ≤ 2 ^ f + 1 := by
  have hm := four_le_of_isOrthReflection hs
  obtain ⟨K, _, _, _, Q, ψ, v, hcard, hQ, hψ, hrange, hv, hψs, hrefl⟩ :=
    exists_symmetry_model_of_isOrthReflection hZ hs
  have hq : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨γ, hγ0, hord⟩ := exists_planeMat_orderOf_succ (K := K)
  obtain ⟨w, hwE, hnc, hordw, hline⟩ := exists_line_of_model hQ hm hψ hrange hv hψs
    (exists_ne_zero_ne_one_of_two_le hf hq) hrefl hγ0
  refine ⟨s, IsConj.refl s, w, hwE, hnc, ?_, ?_⟩
  · rw [hordw, hord, hq]
  · calc _ ≤ (planeSet γ).ncard := hline
      _ ≤ Nat.card K + 1 := ncard_planeSet_le_succ γ
      _ = 2 ^ f + 1 := by rw [hq]

theorem exists_hypLine_pred_of_isOrthReflection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hf : 2 ≤ f)
    (hs : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) :
    ∃ v ∈ {x | IsConj s x}, ∃ w ∈ {x | IsConj s x}, ¬ Commute v w ∧
      orderOf (v * w) = 2 ^ f - 1 ∧
      {z | z ∈ {x | IsConj s x} ∧ ∀ y ∈ {x | IsConj s x}, Commute y v → Commute y w →
        Commute y z}.ncard ≤ 2 ^ f - 1 := by
  have hm := four_le_of_isOrthReflection hs
  obtain ⟨K, _, _, _, Q, ψ, v, hcard, hQ, hψ, hrange, hv, hψs, hrefl⟩ :=
    exists_symmetry_model_of_isOrthReflection hZ hs
  have hq : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card]; exact hcard
  have h4 : 4 ≤ Nat.card K := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨γ, t, hγ0, ht, hord⟩ := exists_planeMat_orderOf_pred (K := K) h4
  obtain ⟨w, hwE, hnc, hordw, hline⟩ := exists_line_of_model hQ hm hψ hrange hv hψs
    (exists_ne_zero_ne_one_of_two_le hf hq) hrefl hγ0
  refine ⟨s, IsConj.refl s, w, hwE, hnc, ?_, ?_⟩
  · rw [hordw, hord, hq]
  · calc _ ≤ (planeSet γ).ncard := hline
      _ ≤ Nat.card K - 1 := ncard_planeSet_le_pred hγ0 ht
      _ = 2 ^ f - 1 := by rw [hq]

end CFSG.OddTranspositions.PartFour

end
