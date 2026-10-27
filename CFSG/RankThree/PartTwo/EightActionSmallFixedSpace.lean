module

public import CFSG.RankThree.LocalRank.ElementaryTwoWeights
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Polynomial.Basic
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo

open CFSG.RankThree.LocalRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {A : Type*} [CommGroup A] [Module (ZMod 2) (Additive A)]
  {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem signWeightSpace_le_eigenspace_one (ρ : Representation K A V)
    {χ : Module.Dual (ZMod 2) (Additive A)} {a : A} (ha : χ (Additive.ofMul a) = 0) :
    signWeightSpace ρ χ ≤ Module.End.eigenspace (ρ a) 1 := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff, (mem_signWeightSpace ρ χ v).mp hv a, ha, ZMod.val_zero,
    pow_zero]

theorem finrank_sup_le_add [FiniteDimensional K V] (s t : Submodule K V) :
    Module.finrank K (s ⊔ t : Submodule K V) ≤ Module.finrank K s + Module.finrank K t := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq s t
  omega

theorem finrank_sup_of_disjoint [FiniteDimensional K V] {s t : Submodule K V}
    (h : Disjoint s t) :
    Module.finrank K (s ⊔ t : Submodule K V) = Module.finrank K s + Module.finrank K t := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq s t
  rw [disjoint_iff.mp h, finrank_bot, add_zero] at h1
  exact h1

variable [Finite A]

theorem exists_ne_one_dual_apply_eq_zero (hA : Nat.card A = 8)
    (χ ψ : Module.Dual (ZMod 2) (Additive A)) :
    ∃ a : A, a ≠ 1 ∧ χ (Additive.ofMul a) = 0 ∧ ψ (Additive.ofMul a) = 0 := by
  classical
  let := Fintype.ofFinite A
  have hdim : Module.finrank (ZMod 2) (Additive A) = 3 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [ZMod.card] at h
    have h8 : Fintype.card (Additive A) = 2 ^ 3 := by
      rw [show Fintype.card (Additive A) = Nat.card A from (Nat.card_eq_fintype_card).symm, hA]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans h8)
  have : FiniteDimensional (ZMod 2) (Additive A) := Module.Finite.of_finite
  have hker : LinearMap.ker (χ.prod ψ) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt
      (by rw [Module.finrank_prod, Module.finrank_self, hdim]; norm_num)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero] at hx
  refine ⟨Additive.toMul x, fun h => hx0 ?_, hx.1, hx.2⟩
  simpa using congrArg Additive.ofMul h

theorem finrank_two_weights_le [FiniteDimensional K V] (hK : (2 : K) ≠ 0)
    (ρ : Representation K A V) {χ ψ : Module.Dual (ZMod 2) (Additive A)} (h12 : χ ≠ ψ) {a : A}
    (h1 : χ (Additive.ofMul a) = 0) (h2 : ψ (Additive.ofMul a) = 0) :
    Module.finrank K (signWeightSpace ρ χ) + Module.finrank K (signWeightSpace ρ ψ) ≤
      Module.finrank K (Module.End.eigenspace (ρ a) 1) := by
  let := Fintype.ofFinite A
  have hind := iSupIndep_signWeightSpace ρ hK
  rw [← finrank_sup_of_disjoint (hind.pairwiseDisjoint h12)]
  exact Submodule.finrank_mono (sup_le (signWeightSpace_le_eigenspace_one ρ h1)
    (signWeightSpace_le_eigenspace_one ρ h2))

theorem finrank_three_weights_le [FiniteDimensional K V] (hK : (2 : K) ≠ 0)
    (ρ : Representation K A V) {χ ψ φ : Module.Dual (ZMod 2) (Additive A)} (h12 : χ ≠ ψ)
    (h13 : χ ≠ φ) (h23 : ψ ≠ φ) {a : A} (h1 : χ (Additive.ofMul a) = 0)
    (h2 : ψ (Additive.ofMul a) = 0) (h3 : φ (Additive.ofMul a) = 0) :
    Module.finrank K (signWeightSpace ρ χ) + Module.finrank K (signWeightSpace ρ ψ) +
      Module.finrank K (signWeightSpace ρ φ) ≤
      Module.finrank K (Module.End.eigenspace (ρ a) 1) := by
  let := Fintype.ofFinite A
  have hind := iSupIndep_signWeightSpace ρ hK
  have d3 : Disjoint (signWeightSpace ρ χ ⊔ signWeightSpace ρ ψ) (signWeightSpace ρ φ) :=
    ((hind φ).mono_right (sup_le (le_iSup₂_of_le χ h13 le_rfl)
      (le_iSup₂_of_le ψ h23 le_rfl))).symm
  rw [← finrank_sup_of_disjoint (hind.pairwiseDisjoint h12), ← finrank_sup_of_disjoint d3]
  exact Submodule.finrank_mono (sup_le (sup_le (signWeightSpace_le_eigenspace_one ρ h1)
    (signWeightSpace_le_eigenspace_one ρ h2)) (signWeightSpace_le_eigenspace_one ρ h3))

theorem eight_action_small_fixed_space (hA : Nat.card A = 8) (hK : (2 : K) ≠ 0)
    [FiniteDimensional K V] (ρ : Representation K A V) (hinj : Function.Injective ρ)
    (hfix : ∀ a : A, a ≠ 1 → Module.finrank K (Module.End.eigenspace (ρ a) 1) ≤ 2) :
    ∃ χ : Fin 3 → Module.Dual (ZMod 2) (Additive A),
      LinearIndependent (ZMod 2) χ ∧ Submodule.span (ZMod 2) (Set.range χ) = ⊤ ∧
      (∀ i, Module.finrank K (signWeightSpace ρ (χ i)) = 1) ∧
      (∀ ψ, signWeightSpace ρ ψ ≠ ⊥ → (∃ i, ψ = χ i) ∨ ψ = χ 0 + χ 1 + χ 2) ∧
      Module.finrank K (signWeightSpace ρ (χ 0 + χ 1 + χ 2)) ≤ 1 ∧
      (Module.finrank K V = 3 ∨ Module.finrank K V = 4) ∧
      (∃! a₀ : A, ρ a₀ = -1) ∧ ∀ a₀ : A, ρ a₀ = -1 → a₀ ≠ 1 := by
  classical
  let := Fintype.ofFinite A
  have : Finite (Module.Dual (ZMod 2) (Additive A)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive A) => (f : Additive A → ZMod 2))
      DFunLike.coe_injective
  let := Fintype.ofFinite (Module.Dual (ZMod 2) (Additive A))
  have : FiniteDimensional (ZMod 2) (Additive A) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) (Additive A) = 3 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [ZMod.card] at h
    have h8 : Fintype.card (Additive A) = 2 ^ 3 := by
      rw [show Fintype.card (Additive A) = Nat.card A from (Nat.card_eq_fintype_card).symm, hA]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans h8)
  have hdimD : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Additive A)) = 3 := by
    rw [Subspace.dual_finrank_eq, hdim]
  set W := {χ : Module.Dual (ZMod 2) (Additive A) | signWeightSpace ρ χ ≠ ⊥} with hW_def
  have hspan : Submodule.span (ZMod 2) W = ⊤ :=
    (injective_iff_span_signWeightSpace ρ hK).mp hinj
  obtain ⟨b, hbW, hbspan, hbli⟩ := exists_linearIndependent (ZMod 2) W
  rw [hspan] at hbspan
  let := Fintype.ofFinite b
  have hcard : Fintype.card b = 3 := by
    have h := finrank_span_eq_card hbli
    rw [Subtype.range_coe, hbspan, finrank_top, hdimD] at h
    exact h.symm
  let e := Fintype.equivFinOfCardEq hcard
  set χ : Fin 3 → Module.Dual (ZMod 2) (Additive A) := fun i => (e.symm i : _) with hχ_def
  have hχli : LinearIndependent (ZMod 2) χ := hbli.comp e.symm e.symm.injective
  have hχrange : Set.range χ = b := by
    ext φ
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hφ
      exact ⟨e ⟨φ, hφ⟩, by simp [hχ_def]⟩
  have hχspan : Submodule.span (ZMod 2) (Set.range χ) = ⊤ := by rw [hχrange, hbspan]
  have hχW : ∀ i, signWeightSpace ρ (χ i) ≠ ⊥ := fun i => hbW (e.symm i).2
  have hχinj : Function.Injective χ := hχli.injective
  have hχ0 : ∀ i, χ i ≠ 0 := fun i => hχli.ne_zero i
  have hpos : ∀ ψ, signWeightSpace ρ ψ ≠ ⊥ → 1 ≤ Module.finrank K (signWeightSpace ρ ψ) := by
    intro ψ hψ
    by_contra h
    push Not at h
    exact hψ (Submodule.finrank_eq_zero.mp (by omega))
  have hvanish : ∀ x : Additive A, (∀ i, χ i x = 0) → x = 0 := by
    intro x hx
    refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) x).mp fun φ => ?_
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp
      (hχspan ▸ Submodule.mem_top : φ ∈ Submodule.span (ZMod 2) (Set.range χ))
    rw [← hc, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [LinearMap.smul_apply, hx i, smul_zero]
  have hval : ∀ y : ZMod 2, y ≠ 0 → y = 1 := by decide
  have hdual : ∀ k : Fin 3, ∃ x : Additive A,
      χ k x = 1 ∧ χ (k + 1) x = 0 ∧ χ (k + 2) x = 0 := by
    intro k
    obtain ⟨a, ha, h1, h2⟩ := exists_ne_one_dual_apply_eq_zero hA (χ (k + 1)) (χ (k + 2))
    refine ⟨Additive.ofMul a, hval _ fun hk => ha ?_, h1, h2⟩
    have : Additive.ofMul a = 0 := hvanish _ fun i => by
      have : i = k ∨ i = k + 1 ∨ i = k + 2 := by fin_cases i <;> fin_cases k <;> simp
      rcases this with rfl | rfl | rfl
      · exact hk
      · exact h1
      · exact h2
    simpa using congrArg Additive.toMul this
  have hW0 : signWeightSpace ρ 0 = ⊥ := by
    by_contra h0
    obtain ⟨a, ha, h1, h2⟩ := exists_ne_one_dual_apply_eq_zero hA (χ 0) (χ 1)
    have := finrank_three_weights_le hK ρ (Ne.symm (hχ0 0)) (Ne.symm (hχ0 1))
      (fun h => absurd (hχinj h) (by decide)) (LinearMap.zero_apply _) h1 h2
    have := hfix a ha
    have := hpos 0 h0
    have := hpos _ (hχW 0)
    have := hpos _ (hχW 1)
    omega
  have hone : ∀ ψ, signWeightSpace ρ ψ ≠ ⊥ → Module.finrank K (signWeightSpace ρ ψ) = 1 := by
    intro ψ hψ
    obtain ⟨i, hi⟩ : ∃ i, χ i ≠ ψ := by
      by_cases h : χ 0 = ψ
      · exact ⟨1, fun h1 => absurd (hχinj (h1.trans h.symm)) (by decide)⟩
      · exact ⟨0, h⟩
    obtain ⟨a, ha, h1, h2⟩ := exists_ne_one_dual_apply_eq_zero hA ψ (χ i)
    have := finrank_two_weights_le hK ρ (Ne.symm hi) h1 h2
    have := hfix a ha
    have := hpos ψ hψ
    have := hpos _ (hχW i)
    omega
  set σ := χ 0 + χ 1 + χ 2 with hσ_def
  have hweights : ∀ ψ, signWeightSpace ρ ψ ≠ ⊥ → (∃ i, ψ = χ i) ∨ ψ = σ := by
    intro ψ hψ
    by_cases hψr : ∃ i, ψ = χ i
    · exact Or.inl hψr
    right
    push Not at hψr
    have hψk : ∀ k : Fin 3, ∀ x : Additive A, χ k x = 1 → χ (k + 1) x = 0 → χ (k + 2) x = 0 →
        ψ x = 1 := by
      intro k x hk h1 h2
      refine hval _ fun h0 => ?_
      have hx0 : x ≠ 0 := fun h => by rw [h, map_zero] at hk; exact zero_ne_one hk
      have ha : Additive.toMul x ≠ (1 : A) := fun h =>
        hx0 (by simpa using congrArg Additive.ofMul h)
      have hne : χ (k + 1) ≠ χ (k + 2) := fun h => absurd (hχinj h) (by fin_cases k <;> decide)
      have := finrank_three_weights_le hK ρ (hψr (k + 1)) (hψr (k + 2)) hne
        (a := Additive.toMul x) h0 h1 h2
      have := hfix _ ha
      have := hpos ψ hψ
      have := hpos _ (hχW (k + 1))
      have := hpos _ (hχW (k + 2))
      omega
    obtain ⟨x₀, h00, h01, h02⟩ := hdual 0
    obtain ⟨x₁, h11, h12, h10⟩ := hdual 1
    obtain ⟨x₂, h22, h20, h21⟩ := hdual 2
    have p0 := hψk 0 x₀ h00 h01 h02
    have p1 := hψk 1 x₁ h11 h12 h10
    have p2 := hψk 2 x₂ h22 h20 h21
    have e01 : χ 1 x₀ = 0 := h01
    have e02 : χ 2 x₀ = 0 := h02
    have e12 : χ 2 x₁ = 0 := h12
    have e10 : χ 0 x₁ = 0 := h10
    have e20 : χ 0 x₂ = 0 := h20
    have e21 : χ 1 x₂ = 0 := h21
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp
      (hχspan ▸ Submodule.mem_top : ψ - σ ∈ Submodule.span (ZMod 2) (Set.range χ))
    have ev : ∀ x, ψ x - (χ 0 x + χ 1 x + χ 2 x) = c 0 * χ 0 x + c 1 * χ 1 x + c 2 * χ 2 x := by
      intro x
      have h := congrArg (fun φ : Module.Dual (ZMod 2) (Additive A) => φ x) hc
      simp only [LinearMap.smul_apply, Fin.sum_univ_three, smul_eq_mul, LinearMap.sub_apply,
        LinearMap.add_apply] at h
      exact h.symm
    have hc0 : c 0 = 0 := by
      have h := ev x₀
      rw [h00, e01, e02, p0] at h
      simpa using h.symm
    have hc1 : c 1 = 0 := by
      have h := ev x₁
      rw [h11, e12, e10, p1] at h
      simpa using h.symm
    have hc2 : c 2 = 0 := by
      have h := ev x₂
      rw [h22, e20, e21, p2] at h
      simpa using h.symm
    have hdiff : ψ - σ = 0 := by
      rw [← hc, Fin.sum_univ_three, hc0, hc1, hc2, zero_smul, zero_smul, zero_smul, add_zero,
        add_zero]
    exact sub_eq_zero.mp hdiff
  have hσ1 : Module.finrank K (signWeightSpace ρ σ) ≤ 1 := by
    by_cases h : signWeightSpace ρ σ = ⊥
    · rw [h, finrank_bot]
      exact zero_le_one
    · exact (hone σ h).le
  have hdimV : Module.finrank K V = 3 ∨ Module.finrank K V = 4 := by
    have hind := iSupIndep_signWeightSpace ρ hK
    have hlow : 3 ≤ Module.finrank K V := by
      have d3 : Disjoint (signWeightSpace ρ (χ 0) ⊔ signWeightSpace ρ (χ 1))
          (signWeightSpace ρ (χ 2)) :=
        ((hind (χ 2)).mono_right (sup_le
          (le_iSup₂_of_le (χ 0) (fun h => absurd (hχinj h) (by decide)) le_rfl)
          (le_iSup₂_of_le (χ 1) (fun h => absurd (hχinj h) (by decide)) le_rfl))).symm
      have h := finrank_sup_of_disjoint d3
      rw [finrank_sup_of_disjoint (hind.pairwiseDisjoint
        (fun h => absurd (hχinj h) (by decide) : χ 0 ≠ χ 1)), hone _ (hχW 0), hone _ (hχW 1),
        hone _ (hχW 2)] at h
      have := Submodule.finrank_le (signWeightSpace ρ (χ 0) ⊔ signWeightSpace ρ (χ 1) ⊔
        signWeightSpace ρ (χ 2))
      omega
    have hup : Module.finrank K V ≤ 4 := by
      have htop : (⊤ : Submodule K V) ≤ signWeightSpace ρ (χ 0) ⊔ signWeightSpace ρ (χ 1) ⊔
          signWeightSpace ρ (χ 2) ⊔ signWeightSpace ρ σ := by
        rw [← iSup_signWeightSpace_eq_top ρ hK]
        refine iSup_le fun ψ => ?_
        by_cases hψ : signWeightSpace ρ ψ = ⊥
        · rw [hψ]
          exact bot_le
        rcases hweights ψ hψ with ⟨i, rfl⟩ | rfl
        · fin_cases i
          · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
          · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
          · exact le_sup_right.trans le_sup_left
        · exact le_sup_right
      have h := Submodule.finrank_mono htop
      rw [finrank_top] at h
      refine h.trans ?_
      refine (finrank_sup_le_add _ _).trans ?_
      have h3 := (finrank_sup_le_add (signWeightSpace ρ (χ 0) ⊔ signWeightSpace ρ (χ 1))
        (signWeightSpace ρ (χ 2)))
      have h2 := finrank_sup_le_add (signWeightSpace ρ (χ 0)) (signWeightSpace ρ (χ 1))
      rw [hone _ (hχW 0), hone _ (hχW 1)] at h2
      rw [hone _ (hχW 2)] at h3
      omega
    omega
  obtain ⟨x₀, h00, h01, h02⟩ := hdual 0
  obtain ⟨x₁, h11, h12, h10⟩ := hdual 1
  obtain ⟨x₂, h22, h20, h21⟩ := hdual 2
  set s := x₀ + x₁ + x₂ with hs_def
  have hs : ∀ i, χ i s = 1 := by
    intro i
    have e01 : χ 1 x₀ = 0 := h01
    have e02 : χ 2 x₀ = 0 := h02
    have e12 : χ 2 x₁ = 0 := h12
    have e10 : χ 0 x₁ = 0 := h10
    have e20 : χ 0 x₂ = 0 := h20
    have e21 : χ 1 x₂ = 0 := h21
    fin_cases i
    · simp [hs_def, h00, e10, e20]
    · simp [hs_def, e01, h11, e21]
    · simp [hs_def, e02, e12, h22]
  have hsσ : σ s = 1 := by
    rw [hσ_def, LinearMap.add_apply, LinearMap.add_apply, hs 0, hs 1, hs 2]
    decide
  set a₀ := Additive.toMul s with ha₀_def
  have hneg : ρ a₀ = -1 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ ⨆ ψ, signWeightSpace ρ ψ := by
      rw [iSup_signWeightSpace_eq_top ρ hK]
      exact Submodule.mem_top
    rw [LinearMap.neg_apply, Module.End.one_apply]
    refine Submodule.iSup_induction (signWeightSpace ρ) (motive := fun w => ρ a₀ w = -w) hv
      (fun ψ w hw => ?_) (by rw [map_zero, neg_zero]) (fun x y hx hy => by
        rw [map_add, hx, hy, neg_add])
    by_cases hψ : signWeightSpace ρ ψ = ⊥
    · have hw0 : w = 0 := by
        rw [hψ] at hw
        exact (Submodule.mem_bot K).mp hw
      rw [hw0, map_zero, neg_zero]
    have hψa : ψ (Additive.ofMul a₀) = 1 := by
      rcases hweights ψ hψ with ⟨i, rfl⟩ | rfl
      · exact hs i
      · exact hsσ
    rw [(mem_signWeightSpace ρ ψ w).mp hw a₀, hψa, ZMod.val_one, pow_one, neg_one_smul]
  have hunique : ∀ a : A, ρ a = -1 → a = a₀ := by
    intro a ha
    have hχa : ∀ i, χ i (Additive.ofMul a) = 1 := by
      intro i
      refine hval _ fun h0 => ?_
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hχW i)
      have h1 := (mem_signWeightSpace ρ (χ i) v).mp hv a
      rw [h0, ZMod.val_zero, pow_zero, one_smul, ha, LinearMap.neg_apply,
        Module.End.one_apply] at h1
      apply hv0
      have h2 : (2 : K) • v = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h1]
        exact neg_add_cancel v
      exact (smul_eq_zero.mp h2).resolve_left hK
    have hx : Additive.ofMul a - s = 0 := hvanish _ fun i => by
      rw [map_sub, hχa i, hs i, sub_self]
    have : Additive.ofMul a = Additive.ofMul a₀ := by
      rw [ha₀_def, ofMul_toMul]
      exact sub_eq_zero.mp hx
    simpa using this
  refine ⟨χ, hχli, hχspan, fun i => hone _ (hχW i), hweights, hσ1, hdimV,
    ⟨a₀, hneg, fun a ha => hunique a ha⟩, fun a ha ha1 => ?_⟩
  have h := (hunique a ha)
  rw [ha1] at h
  have h0 : s = 0 := by
    have := congrArg Additive.ofMul h
    rw [ha₀_def, ofMul_toMul] at this
    simpa using this.symm
  have := hs 0
  rw [h0, map_zero] at this
  exact zero_ne_one this

end CFSG.RankThree.PartTwo
