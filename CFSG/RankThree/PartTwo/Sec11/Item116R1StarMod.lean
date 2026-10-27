module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankModules
public import CFSG.RankThree.GroupTheory.SteinbergBMExtraspecialThirtyTwoFive
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionModule
public import CFSG.RankThree.PartTwo.Sec3.TwoGroupPrimeFiveAction
public import CFSG.RankThree.PartOne.S9.Defs

public section

section

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.FixedRank36
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem h6_mem_center_equiv {S : Type*} [Group S] (φ : S ≃* S) {x : S}
    (hx : x ∈ Subgroup.center S) : φ x ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro g
  have h := congrArg φ (hx (φ.symm g))
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
  exact h

theorem h6_scalar {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {S : Type*} [Group S] (ρ : Representation K S V) {Y : Submodule K V} (hY : IsMinInv ρ Y)
    (hcomm : ∀ a b : S, ⁅a, b⁆ ∈ Subgroup.center S) (hsq : ∀ a : S, a * a ∈ Subgroup.center S)
    (hcen : ∀ c ∈ Subgroup.center S, ∀ y ∈ Y, ρ c y = y) (g : S) :
    (∀ y ∈ Y, ρ g y = y) ∨ (∀ y ∈ Y, ρ g y = -y) := by
  have hcommY : ∀ h : S, ∀ w ∈ Y, ρ g (ρ h w) = ρ h (ρ g w) := by
    intro h w hw
    have hc : (g * h)⁻¹ * (h * g) ∈ Subgroup.center S := by
      have e : (g * h)⁻¹ * (h * g) = ⁅h⁻¹, g⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact hcomm _ _
    have key : h * g = (g * h) * ((g * h)⁻¹ * (h * g)) := by group
    have h1 : ρ (h * g) w = ρ (g * h) w := by
      rw [key, map_mul ρ (g * h) ((g * h)⁻¹ * (h * g)), Module.End.mul_apply, hcen _ hc w hw]
    have e1 : ρ g (ρ h w) = ρ (g * h) w := by rw [map_mul, Module.End.mul_apply]
    have e2 : ρ h (ρ g w) = ρ (h * g) w := by rw [map_mul, Module.End.mul_apply]
    rw [e1, e2, h1]
  have hsqY : ∀ w ∈ Y, ρ g (ρ g w) = w := by
    intro w hw
    have e : ρ g (ρ g w) = ρ (g * g) w := by rw [map_mul, Module.End.mul_apply]
    rw [e]
    exact hcen _ (hsq g) w hw
  have hinv : IsInv ρ (Y ⊓ Module.End.eigenspace (ρ g) 1) := by
    intro h w hw
    obtain ⟨hwY, hwe⟩ := Submodule.mem_inf.1 hw
    rw [Module.End.mem_eigenspace_iff, one_smul] at hwe
    refine Submodule.mem_inf.2 ⟨hY.1 h w hwY, ?_⟩
    rw [Module.End.mem_eigenspace_iff, one_smul, hcommY h w hwY, hwe]
  rcases hY.2.2 _ inf_le_left hinv with h | h
  · right
    intro y hy
    have hu : y + ρ g y ∈ Y ⊓ Module.End.eigenspace (ρ g) 1 := by
      refine Submodule.mem_inf.2 ⟨Y.add_mem hy (hY.1 g y hy), ?_⟩
      rw [Module.End.mem_eigenspace_iff, one_smul, map_add, hsqY y hy]
      exact add_comm _ _
    rw [h, Submodule.mem_bot] at hu
    exact eq_neg_of_add_eq_zero_right hu
  · left
    intro y hy
    have hmem : y ∈ Y ⊓ Module.End.eigenspace (ρ g) 1 := by
      rw [h]
      exact hy
    have h3 := (Submodule.mem_inf.1 hmem).2
    rw [Module.End.mem_eigenspace_iff, one_smul] at h3
    exact h3

theorem h6_fix_plus {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {V : Type*} [AddCommGroup V]
    [Module K V] {S : Type*} [Group S] (γ : MulAut S) (hγ5 : γ ^ 5 = 1)
    (hfpf : ∀ s : S, γ s * s⁻¹ ∈ Subgroup.center S → s ∈ Subgroup.center S)
    (ρ : Representation K S V) {Y : Submodule K V} (hY : IsMinInv ρ Y)
    (hcomm : ∀ a b : S, ⁅a, b⁆ ∈ Subgroup.center S) (hsq : ∀ a : S, a * a ∈ Subgroup.center S)
    (hcen : ∀ c ∈ Subgroup.center S, ∀ y ∈ Y, ρ c y = y)
    (s₀ : S) (hs₀c : s₀ ∉ Subgroup.center S) (hs₀o : orderOf s₀ = 2) :
    ∃ s : S, s ∉ Subgroup.center S ∧ orderOf s = 2 ∧ ∀ y ∈ Y, ρ s y = y := by
  classical
  have hnc : ∀ φ : S ≃* S, φ s₀ ∉ Subgroup.center S ∧ orderOf (φ s₀) = 2 := by
    intro φ
    constructor
    · intro h
      apply hs₀c
      have h' := h6_mem_center_equiv φ.symm h
      rwa [MulEquiv.symm_apply_apply] at h'
    · rw [MulEquiv.orderOf_eq]
      exact hs₀o
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ → S, ∀ i, a i = (γ ^ i) s₀ :=
    ⟨fun i => (γ ^ i) s₀, fun i => rfl⟩
  have ha : ∀ i, γ (a i) = a (i + 1) := by
    intro i
    rw [ha_def, ha_def, pow_succ', MulAut.mul_apply]
  have ha5 : a 5 = a 0 := by
    simp only [ha_def, hγ5, pow_zero, MulAut.one_apply]
  have e0 : γ (a 0) = a 1 := ha 0
  have e1 : γ (a 1) = a 2 := ha 1
  have e2 : γ (a 2) = a 3 := ha 2
  have e3 : γ (a 3) = a 4 := ha 3
  have e4 : γ (a 4) = a 0 := (ha 4).trans ha5
  have hγu : γ (a 0 * a 1 * a 2 * a 3 * a 4) = a 1 * a 2 * a 3 * a 4 * a 0 := by
    rw [map_mul, map_mul, map_mul, map_mul, e0, e1, e2, e3, e4]
  have hu_mem : a 0 * a 1 * a 2 * a 3 * a 4 ∈ Subgroup.center S := by
    apply hfpf
    have e : γ (a 0 * a 1 * a 2 * a 3 * a 4) * (a 0 * a 1 * a 2 * a 3 * a 4)⁻¹
        = ⁅a 1 * a 2 * a 3 * a 4, a 0⁆ := by
      rw [hγu, commutatorElement_def]
      group
    rw [e]
    exact hcomm _ _
  have hfound : ∀ i : ℕ, (∀ y ∈ Y, ρ (a i) y = y) →
      ∃ s : S, s ∉ Subgroup.center S ∧ orderOf s = 2 ∧ ∀ y ∈ Y, ρ s y = y := by
    intro i hi
    refine ⟨a i, ?_, ?_, hi⟩
    · rw [ha_def]
      exact (hnc (γ ^ i)).1
    · rw [ha_def]
      exact (hnc (γ ^ i)).2
  by_cases h0 : ∀ y ∈ Y, ρ (a 0) y = y
  · exact hfound 0 h0
  by_cases h1 : ∀ y ∈ Y, ρ (a 1) y = y
  · exact hfound 1 h1
  by_cases h2' : ∀ y ∈ Y, ρ (a 2) y = y
  · exact hfound 2 h2'
  by_cases h3 : ∀ y ∈ Y, ρ (a 3) y = y
  · exact hfound 3 h3
  by_cases h4 : ∀ y ∈ Y, ρ (a 4) y = y
  · exact hfound 4 h4
  exfalso
  have n0 := (h6_scalar ρ hY hcomm hsq hcen (a 0)).resolve_left h0
  have n1 := (h6_scalar ρ hY hcomm hsq hcen (a 1)).resolve_left h1
  have n2 := (h6_scalar ρ hY hcomm hsq hcen (a 2)).resolve_left h2'
  have n3 := (h6_scalar ρ hY hcomm hsq hcen (a 3)).resolve_left h3
  have n4 := (h6_scalar ρ hY hcomm hsq hcen (a 4)).resolve_left h4
  obtain ⟨y, hyY, hy0⟩ := (Submodule.ne_bot_iff Y).1 hY.2.1
  have hu := hcen _ hu_mem y hyY
  have hchain : ρ (a 0 * a 1 * a 2 * a 3 * a 4) y = -y := by
    simp only [map_mul, Module.End.mul_apply]
    rw [n4 y hyY, map_neg, n3 y hyY, neg_neg, n2 y hyY, map_neg, n1 y hyY, neg_neg, n0 y hyY]
  have hyy : y = -y := hu.symm.trans hchain
  have h2y : (2 : K) • y = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.2 hyy
  rcases smul_eq_zero.1 h2y with h | h
  · exact h2 h
  · exact hy0 h

theorem finrank_eq_four_of_fixed_two {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {S : Type*} [Group S] [Finite S]
    (hS : IsExtraspecialPGroup 2 S) (hcard : Nat.card S = 32) (γ : MulAut S) (hγ5 : γ ^ 5 = 1)
    (hfpf : ∀ s : S, γ s * s⁻¹ ∈ Subgroup.center S → s ∈ Subgroup.center S)
    (ρ : Representation K S V) (hρ : Function.Injective ρ)
    (hfix : ∀ s : S, s ≠ 1 → Module.finrank K (Module.End.eigenspace (ρ s) 1) ≤ 2) :
    Module.finrank K V = 4 := by
  classical
  have hNZ : NeZero (Nat.card S : K) := by
    refine ⟨?_⟩
    rw [hcard]
    have h32 : ((32 : ℕ) : K) = 2 ^ 5 := by norm_num
    rw [h32]
    exact pow_ne_zero _ h2
  obtain ⟨z, hzc_eq, hz1, hzz⟩ := CFSG.RankThree.PartOne.FixedRank36.exists_center_generator hS
  have hzc : z ∈ Subgroup.center S := by
    rw [hzc_eq]
    exact Subgroup.mem_zpowers z
  have hcen : ∀ c ∈ Subgroup.center S, c = 1 ∨ c = z := fun c hc =>
    CFSG.RankThree.PartOne.FixedRank36.eq_one_or_eq_of_mem_center hzc_eq hz1 hzz hc
  have hcomm : ∀ a b : S, ⁅a, b⁆ ∈ Subgroup.center S := fun a b =>
    CFSG.RankThree.PartOne.FixedRank36.commutator_mem_center hS a b
  have hsq : ∀ a : S, a * a ∈ Subgroup.center S := fun a => by
    rw [← pow_two]
    exact CFSG.RankThree.PartOne.FixedRank36.sq_mem_center hS a
  have hT1 : ρ z ≠ 1 := fun h => hz1 (hρ (h.trans (map_one ρ).symm))
  have hTsq : ∀ v, ρ z (ρ z v) = v := by
    intro v
    have e : ρ z (ρ z v) = ρ (z * z) v := by rw [map_mul, Module.End.mul_apply]
    rw [e, hzz, map_one, Module.End.one_apply]
  have hTc : ∀ g v, ρ z (ρ g v) = ρ g (ρ z v) := by
    intro g v
    have e : ρ z (ρ g v) = ρ (z * g) v := by rw [map_mul, Module.End.mul_apply]
    have e' : ρ g (ρ z v) = ρ (g * z) v := by rw [map_mul, Module.End.mul_apply]
    rw [e, e', Subgroup.mem_center_iff.1 hzc g]
  have hVinv : IsInv ρ (Module.End.eigenspace (ρ z) (-1)) := by
    intro g w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    rw [hTc g w, hw, map_smul]
  have hV0 : Module.End.eigenspace (ρ z) (-1) ≠ ⊥ := by
    obtain ⟨v, hv⟩ : ∃ v, ρ z v ≠ v := by
      by_contra h
      push Not at h
      exact hT1 (LinearMap.ext h)
    have hmem : v - ρ z v ∈ Module.End.eigenspace (ρ z) (-1) := by
      rw [Module.End.mem_eigenspace_iff, map_sub, hTsq, neg_one_smul, neg_sub]
    intro h
    rw [h, Submodule.mem_bot] at hmem
    exact hv (sub_eq_zero.1 hmem).symm
  obtain ⟨W, hWle, hW⟩ := exists_isMinInv_le hVinv hV0
  have hzW : ∀ y ∈ W, ρ z y = -y := by
    intro y hy
    have h := hWle hy
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at h
    exact h
  obtain ⟨s₀, hs₀c, hs₀o⟩ :=
    CFSG.RankThree.PartOne.FixedRank36.exists_noncentral_involution hS hcard
  have hs₀1 : s₀ ≠ 1 := fun h => hs₀c (h ▸ Subgroup.one_mem _)
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW.2.1
  have hρzW : restrictRep ρ W hW.1 z = -1 := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    show ρ z y = -(y : V)
    exact hzW y y.2
  obtain ⟨h4W, hsW⟩ := extraspecial_two_minus_module_bound (n := 2) hS
    (by rw [hcard]; norm_num) hzc_eq h2 (restrictRep ρ W hW.1) hρzW
  have hW4 : 4 ≤ Module.finrank K W := by
    have h := h4W
    norm_num at h
    exact h
  have hWs : ∀ s : S, s ∉ Subgroup.center S → orderOf s = 2 →
      2 * Module.finrank K ↥(Module.End.eigenspace (ρ s) 1 ⊓ W) = Module.finrank K W := by
    intro s hs1 hs2
    have h := (hsW s hs1 hs2).1
    rwa [finrank_eigenspace_restrict] at h
  have hWC : ∀ s : S, s ∉ Subgroup.center S → orderOf s = 2 →
      2 ≤ Module.finrank K ↥(Module.End.eigenspace (ρ s) 1 ⊓ W) := by
    intro s hs1 hs2
    have h := hWs s hs1 hs2
    omega
  have hWtop : W = ⊤ := by
    by_contra hne
    obtain ⟨W', hW'inv, hW'compl⟩ := exists_isInv_isCompl hW.1
    have hW'0 : W' ≠ ⊥ := by
      intro h
      have h' := codisjoint_iff.1 hW'compl.2
      rw [h, sup_bot_eq] at h'
      exact hne h'
    obtain ⟨Y, hYle, hY⟩ := exists_isMinInv_le hW'inv hW'0
    have hdisj : W ⊓ Y = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_left W hYle).trans (disjoint_iff.1 hW'compl.1).le)
    haveI : Nontrivial Y := Submodule.nontrivial_iff_ne_bot.2 hY.2.1
    have hY1 : 0 < Module.finrank K Y := Module.finrank_pos
    rcases eq_or_neg_of_isMinInv hY (T := ρ z) hTsq hTc (fun y hy => hY.1 z y hy) with
      hzY | hzY
    ·
      have hcenY : ∀ c ∈ Subgroup.center S, ∀ y ∈ Y, ρ c y = y := by
        intro c hc y hy
        rcases hcen c hc with h | h
        · simp [h]
        · rw [h]
          exact hzY y hy
      obtain ⟨s, hsc, hso, hsY⟩ :=
        h6_fix_plus h2 γ hγ5 hfpf ρ hY hcomm hsq hcenY s₀ hs₀c hs₀o
      have hs1 : s ≠ 1 := fun h => hsc (h ▸ Subgroup.one_mem _)
      have hYsub : Y ≤ Module.End.eigenspace (ρ s) 1 := fun y hy => by
        rw [Module.End.mem_eigenspace_iff, one_smul]
        exact hsY y hy
      have hdisj' : (Module.End.eigenspace (ρ s) 1 ⊓ W) ⊓ Y = ⊥ :=
        le_bot_iff.1 (le_trans (inf_le_inf inf_le_right le_rfl) hdisj.le)
      have hsum := finrank_add_le_of_inf_eq_bot
        (inf_le_left : Module.End.eigenspace (ρ s) 1 ⊓ W ≤ Module.End.eigenspace (ρ s) 1)
        hYsub hdisj'
      have hC := hWC s hsc hso
      have hf := hfix s hs1
      omega
    ·
      have hρzY : restrictRep ρ Y hY.1 z = -1 := by
        refine LinearMap.ext fun y => Subtype.ext ?_
        show ρ z y = -(y : V)
        exact hzY y y.2
      obtain ⟨h4Y, hsY⟩ := extraspecial_two_minus_module_bound (n := 2) hS
        (by rw [hcard]; norm_num) hzc_eq h2 (restrictRep ρ Y hY.1) hρzY
      have hY4 : 4 ≤ Module.finrank K Y := by
        have h := h4Y
        norm_num at h
        exact h
      have hYs : 2 * Module.finrank K ↥(Module.End.eigenspace (ρ s₀) 1 ⊓ Y) =
          Module.finrank K Y := by
        have h := (hsY s₀ hs₀c hs₀o).1
        rwa [finrank_eigenspace_restrict] at h
      have hdisj' : (Module.End.eigenspace (ρ s₀) 1 ⊓ W) ⊓
          (Module.End.eigenspace (ρ s₀) 1 ⊓ Y) = ⊥ :=
        le_bot_iff.1 (le_trans (inf_le_inf inf_le_right inf_le_right) hdisj.le)
      have hsum := finrank_add_le_of_inf_eq_bot
        (inf_le_left : Module.End.eigenspace (ρ s₀) 1 ⊓ W ≤ Module.End.eigenspace (ρ s₀) 1)
        (inf_le_left : Module.End.eigenspace (ρ s₀) 1 ⊓ Y ≤ Module.End.eigenspace (ρ s₀) 1)
        hdisj'
      have hC := hWC s₀ hs₀c hs₀o
      have hf := hfix s₀ hs₀1
      omega
  have hdim : Module.finrank K W = 4 := by
    have h1 := hWs s₀ hs₀c hs₀o
    have h2' : Module.finrank K ↥(Module.End.eigenspace (ρ s₀) 1 ⊓ W) ≤ 2 :=
      (Submodule.finrank_mono (inf_le_left : Module.End.eigenspace (ρ s₀) 1 ⊓ W ≤
        Module.End.eigenspace (ρ s₀) 1)).trans (hfix s₀ hs₀1)
    omega
  rw [hWtop, finrank_top] at hdim
  exact hdim

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem h7_orbit_pow_five {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 16)
    (f : MulAut V) {k : ℕ} (hf : f ^ (5 ^ k) = 1) (hfix : ∀ q : V, f q = q → q = 1) :
    f ^ 5 = 1 := by
  letI : Fintype V := Fintype.ofFinite V
  have hcard : Fintype.card V = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact hV
  have hit : ∀ (n : ℕ) (x : V), (f ^ n) x = (⇑f)^[n] x := by
    intro n
    induction n with
    | zero => intro x; simp [MulAut.one_apply]
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih]
      exact (Function.iterate_succ_apply _ _ _).symm
  have hper : ∀ q : V, Function.IsPeriodicPt (⇑f) (5 ^ k) q := by
    intro q
    show (⇑f)^[5 ^ k] q = q
    rw [← hit, hf, MulAut.one_apply]
  have h5 : ∀ q : V, (⇑f)^[5] q = q := by
    intro q
    by_cases hq : q = 1
    · rw [hq]
      exact Function.iterate_fixed (map_one f) 5
    · obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
        (hper q).minimalPeriod_dvd
      have hle : Function.minimalPeriod (⇑f) q ≤ 16 := by
        have h : Function.minimalPeriod (⇑f) q ≤ Fintype.card V :=
          Function.minimalPeriod_le_card
        omega
      have hne : Function.minimalPeriod (⇑f) q ≠ 1 := by
        intro h1
        exact hq (hfix q (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1))
      have hn5 : Function.minimalPeriod (⇑f) q = 5 := by
        rcases m with _ | _ | m
        · rw [pow_zero] at hm
          exact absurd hm hne
        · simpa using hm
        · exfalso
          rw [hm, pow_succ, pow_succ] at hle
          have h1 : 0 < 5 ^ m := pow_pos (by norm_num) m
          omega
      have h6 := Function.isPeriodicPt_minimalPeriod (⇑f) q
      rw [hn5] at h6
      exact h6
  refine MulEquiv.ext fun q => ?_
  rw [MulAut.one_apply, hit]
  exact h5 q

theorem h7_center_gen {S : Type*} [Group S] [Finite S] (hS : IsExtraspecialPGroup 2 S) :
    ∃ z : S, Subgroup.center S = Subgroup.zpowers z := by
  obtain ⟨z, hzc, hz1⟩ : ∃ z ∈ Subgroup.center S, z ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : Subgroup.center S = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    have h2 := hS.2.2.2
    rw [h1, Subgroup.card_bot] at h2
    omega
  have hle : Subgroup.zpowers z ≤ Subgroup.center S := Subgroup.zpowers_le.2 hzc
  have hdvd : orderOf z ∣ 2 := by
    rw [← Nat.card_zpowers, ← hS.2.2.2]
    exact Subgroup.card_dvd_of_le hle
  have hord : orderOf z = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  refine ⟨z, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Nat.card_zpowers, hord, hS.2.2.2]

theorem pow_five_eq_one_of_fpf {S : Type*} [Group S] [Finite S] (hS : IsExtraspecialPGroup 2 S)
    (hcard : Nat.card S = 32) (γ : MulAut S) {k : ℕ} (hγ : γ ^ (5 ^ k) = 1)
    (hfpf : ∀ s : S, γ s * s⁻¹ ∈ Subgroup.center S → s ∈ Subgroup.center S) : γ ^ 5 = 1 := by
  haveI : Finite (S ⧸ Subgroup.center S) := Finite.of_surjective _ QuotientGroup.mk_surjective
  let ψ := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (Subgroup.center S)
  have hψg : ∀ (β : MulAut S) (s : S), ψ β (s : S ⧸ Subgroup.center S) =
      ((β s : S) : S ⧸ Subgroup.center S) :=
    fun β s => CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ β s
  have hcardV : Nat.card (S ⧸ Subgroup.center S) = 16 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
    rw [hcard, hS.2.2.2] at h
    omega
  have hfixV : ∀ q : S ⧸ Subgroup.center S, ψ γ q = q → q = 1 := by
    intro q hq
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hψg, QuotientGroup.eq] at hq
    rw [QuotientGroup.eq_one_iff]
    apply hfpf
    have h2 : γ s * s⁻¹ = s * ((γ s)⁻¹ * s)⁻¹ * s⁻¹ := by group
    rw [h2]
    exact Subgroup.Normal.conj_mem inferInstance _ (inv_mem hq) s
  have hpow : ψ γ ^ (5 ^ k) = 1 := by
    rw [← map_pow, hγ, map_one]
  have h5 : ψ γ ^ 5 = 1 := h7_orbit_pow_five hcardV (ψ γ) hpow hfixV
  have hψd : ψ (γ ^ 5) = 1 := by
    rw [map_pow, h5]
  have hdV : ∀ s : S, ((γ ^ 5 : MulAut S) s : S ⧸ Subgroup.center S) =
      (s : S ⧸ Subgroup.center S) := by
    intro s
    have h1 : ψ (γ ^ 5) (s : S ⧸ Subgroup.center S) = (s : S ⧸ Subgroup.center S) := by
      rw [hψd, MulAut.one_apply]
    rw [hψg] at h1
    exact h1
  have hdK : γ ^ 5 ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini S)).ker := by
    refine (CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel
      (frattini S) (γ ^ 5)).mpr ?_
    intro s
    show ((γ ^ 5 : MulAut S) s : S ⧸ frattini S) = (s : S ⧸ frattini S)
    rw [QuotientGroup.eq, hS.2.2.1]
    exact QuotientGroup.eq.mp (hdV s)
  have hK : IsPGroup 2 (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini S)).ker :=
    CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup 2 hS.1
  have hK' : ∀ g : (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini S)).ker, ∃ j : ℕ, g ^ 2 ^ j = 1 := hK
  obtain ⟨n, hn⟩ := hK' ⟨γ ^ 5, hdK⟩
  have h2n : (γ ^ 5) ^ 2 ^ n = 1 := by
    simpa using congrArg Subtype.val hn
  have h5k : (γ ^ 5) ^ 5 ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hγ, one_pow]
  have hcop : Nat.Coprime (2 ^ n) (5 ^ k) := Nat.Coprime.pow n k (by norm_num)
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨h2n, h5k⟩

theorem qd32_of_fpf {S : Type*} [Group S] [Finite S] (hS : IsExtraspecialPGroup 2 S)
    (hcard : Nat.card S = 32) (γ : MulAut S) {k : ℕ} (hγ : γ ^ (5 ^ k) = 1)
    (hfpf : ∀ s : S, γ s * s⁻¹ ∈ Subgroup.center S → s ∈ Subgroup.center S) :
    Nonempty (S ≃* QD32) := by
  have h5 : γ ^ 5 = 1 := pow_five_eq_one_of_fpf hS hcard γ hγ hfpf
  obtain ⟨z, hz⟩ := h7_center_gen hS
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hγ1 : γ ≠ 1 := by
    intro h
    have hall : ∀ s : S, s ∈ Subgroup.center S := fun s => hfpf s (by simp [h])
    have htop : Subgroup.center S = ⊤ := eq_top_iff.mpr fun s _ => hall s
    have h2 := hS.2.2.2
    rw [htop, Subgroup.card_top, hcard] at h2
    omega
  have hα : orderOf γ = 5 := orderOf_eq_prime h5 hγ1
  have hfix : ∀ s : S, ((γ s : S) : S ⧸ Subgroup.center S) = (s : S ⧸ Subgroup.center S) →
      s ∈ Subgroup.center S := by
    intro s h
    rw [QuotientGroup.eq] at h
    apply hfpf
    have h2 : γ s * s⁻¹ = γ s * ((γ s)⁻¹ * s)⁻¹ * (γ s)⁻¹ := by group
    rw [h2]
    exact Subgroup.Normal.conj_mem inferInstance _ (inv_mem h) _
  exact (CFSG.RankThree.GroupTheory.SteinbergBM.extraspecial_thirty_two_five_recognition
    hS hcard hz γ hα hfix).1

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.FixedRank36
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11

theorem ext32_module_data {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {D : Type*} [Group D] [Finite D]
    (hD : IsPGroup p D) (hexp : ∀ x : D, x ^ p = 1) (hclass : commutator D ≤ Subgroup.center D)
    {S : Type*} [Group S] [Finite S] (hS : IsExtraspecialPGroup 2 S) (hcard : Nat.card S = 32)
    (γ : MulAut S) (hγ5 : γ ^ 5 = 1)
    (hγfix : ∀ s : S, γ s * s⁻¹ ∈ Subgroup.center S → s ∈ Subgroup.center S)
    (ρ : S →* MulAut D) (hρ : Function.Injective ρ)
    (hfix : ∀ s : S, s ≠ 1 → CFSG.pRank p ↥(fixedSub (ρ s)) ≤ 2) :
    Nat.card (D ⧸ frattini D) = p ^ 4 ∧ 3 ≤ CFSG.pRank p D := by
  have hel : IsElementaryAbelian p (D ⧸ frattini D) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hD).2.2.2.1
  have hfd : FiniteDimensional (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  have hinj : Function.Injective (frattiniRep p ρ) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : ρ s = 1 :=
      frattiniRep_eq_one hD hp2 ρ s
        (CFSG.RankThree.PartOne.Torsion37.isPGroup_zpowers_map hS.1 ρ s) hs
    exact hρ (h1.trans (map_one ρ).symm)
  have hfixV : ∀ s : S, s ≠ 1 →
      Module.finrank (ZMod p) (Module.End.eigenspace (frattiniRep p ρ s) 1) ≤ 2 := fun s hs1 =>
    finrank_fixed_le hD hp2 hexp hclass ρ s
      (CFSG.RankThree.PartOne.Torsion37.isPGroup_zpowers_map hS.1 ρ s) (hfix s hs1)
  have hfin : Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) = 4 :=
    finrank_eq_four_of_fixed_two (K := ZMod p)
      (CFSG.RankThree.PartOne.Torsion37.two_ne_zero_zmod hp.out hp2) hS hcard γ hγ5 hγfix
      (frattiniRep p ρ) hinj hfixV
  have hcardV : Nat.card (D ⧸ frattini D) = p ^ 4 := by
    have h2 : Nat.card (Additive (D ⧸ frattini D)) = p ^ 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, hfin]
    exact (Nat.card_congr Additive.toMul).symm.trans h2
  have hfrat : frattini D = commutator D :=
    CFSG.RankThree.PartTwo.frattini_eq_commutator hD hexp
  have hcardC : Nat.card (D ⧸ commutator D) = p ^ 4 := by
    rw [← hfrat]
    exact hcardV
  have hrank4 : CFSG.pRank p (D ⧸ commutator D) = 4 :=
    (CFSG.RankThree.PartTwo.quotient_commutator_rank hp.out hexp hcardC).2
  refine ⟨hcardV, ?_⟩
  by_contra hlt
  have hle2 : CFSG.pRank p D ≤ 2 := by omega
  have h2' := (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hD hexp hclass).1 hle2
  rw [hrank4] at h2'
  omega

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FixedRank36 CFSG.RankThree.PartTwo.Sec3
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11

theorem irr_to_module {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {D L : Subgroup G}
    (hD : IsPGroup p D) (hLD : L ≤ Subgroup.normalizer (D : Set G))
    [IsElementaryAbelian p (↥D ⧸ frattini ↥D)] (hirr : IsFrattiniIrreducibleFor L D) :
    ∀ W : Submodule (ZMod p) (Additive (↥D ⧸ frattini ↥D)),
      (∀ (l : ↥L) (w : Additive (↥D ⧸ frattini ↥D)), w ∈ W →
        frattiniRep p (conjAction D L hLD) l w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  obtain ⟨-, -, hmax⟩ := hirr
  let Y₀ : Subgroup ↥D :=
    { carrier := {d : ↥D | Additive.ofMul ((d : ↥D ⧸ frattini ↥D)) ∈ W}
      mul_mem' := by
        intro a b ha hb
        have ha' : Additive.ofMul ((a : ↥D ⧸ frattini ↥D)) ∈ W := ha
        have hb' : Additive.ofMul ((b : ↥D ⧸ frattini ↥D)) ∈ W := hb
        show Additive.ofMul (((a * b : ↥D) : ↥D ⧸ frattini ↥D)) ∈ W
        rw [QuotientGroup.mk_mul, ofMul_mul]
        exact W.add_mem ha' hb'
      one_mem' := by
        show Additive.ofMul (((1 : ↥D) : ↥D ⧸ frattini ↥D)) ∈ W
        rw [QuotientGroup.mk_one, ofMul_one]
        exact W.zero_mem
      inv_mem' := by
        intro a ha
        have ha' : Additive.ofMul ((a : ↥D ⧸ frattini ↥D)) ∈ W := ha
        show Additive.ofMul (((a⁻¹ : ↥D) : ↥D ⧸ frattini ↥D)) ∈ W
        rw [QuotientGroup.mk_inv, ofMul_inv]
        exact W.neg_mem ha' }
  have hY₀mem : ∀ d : ↥D, d ∈ Y₀ ↔ Additive.ofMul ((d : ↥D ⧸ frattini ↥D)) ∈ W :=
    fun d => Iff.rfl
  let Y : Subgroup G := Y₀.map D.subtype
  have hmemY : ∀ x : G, x ∈ Y ↔ ∃ d ∈ Y₀, (d : G) = x :=
    fun x => Subgroup.mem_map
  have hinv : ∀ (u : ↥L) (d : ↥D), d ∈ Y₀ → conjAction D L hLD u d ∈ Y₀ := by
    intro u d hd
    have h1 := hW u (Additive.ofMul ((d : ↥D ⧸ frattini ↥D))) ((hY₀mem d).1 hd)
    rw [frattiniRep_apply (q := p)] at h1
    exact (hY₀mem _).2 h1
  have hΦ₀ : frattini ↥D ≤ Y₀ := by
    intro x hx
    rw [hY₀mem, (QuotientGroup.eq_one_iff x).2 hx, ofMul_one]
    exact W.zero_mem
  have hΦY : inSubgroup frattini D ≤ Y := by
    change (frattini ↥D).map D.subtype ≤ Y₀.map D.subtype
    exact Subgroup.map_mono hΦ₀
  have hYD : Y ≤ D := Subgroup.map_subtype_le Y₀
  have hconj : ∀ (u : ↥L) (x : G), x ∈ Y → (u : G) * x * (u : G)⁻¹ ∈ Y := by
    intro u x hx
    obtain ⟨d, hd, rfl⟩ := (hmemY x).1 hx
    rw [← conjAction_apply_coe D L hLD u d]
    exact (hmemY _).2 ⟨conjAction D L hLD u d, hinv u d hd, rfl⟩
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconj ⟨l, hl⟩ h hh
    · intro hh
      have h2 : (l⁻¹ : G) * (l * h * l⁻¹) * (l⁻¹)⁻¹ ∈ Y :=
        hconj ⟨l⁻¹, inv_mem hl⟩ (l * h * l⁻¹) hh
      have key : (l⁻¹ : G) * (l * h * l⁻¹) * (l⁻¹)⁻¹ = h := by group
      rw [key] at h2
      exact h2
  rcases hmax Y hΦY hYD hLY with hY | hY
  · left
    rw [Submodule.eq_bot_iff]
    intro w hw
    obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hwd : w = Additive.ofMul ((d : ↥D ⧸ frattini ↥D)) := by
      rw [hd]
      rfl
    have hdY₀ : d ∈ Y₀ := (hY₀mem d).2 (by rw [← hwd]; exact hw)
    have hdY : (d : G) ∈ Y := (hmemY _).2 ⟨d, hdY₀, rfl⟩
    rw [hY] at hdY
    change (d : G) ∈ (frattini ↥D).map D.subtype at hdY
    obtain ⟨z, hz, hzd⟩ := Subgroup.mem_map.mp hdY
    have hzd' : z = d := Subtype.ext hzd
    have hd1 : ((d : ↥D) : ↥D ⧸ frattini ↥D) = 1 :=
      (QuotientGroup.eq_one_iff d).2 (by rw [← hzd']; exact hz)
    rw [hwd, hd1, ofMul_one]
  · right
    rw [Submodule.eq_top_iff']
    intro w
    obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hwd : w = Additive.ofMul ((d : ↥D ⧸ frattini ↥D)) := by
      rw [hd]
      rfl
    have hdY : (d : G) ∈ Y := by
      rw [hY]
      exact d.2
    obtain ⟨d', hd'Y₀, hd'⟩ := (hmemY _).1 hdY
    have hdd : d' = d := Subtype.ext hd'
    rw [hwd]
    have h3 := (hY₀mem d').1 hd'Y₀
    rw [hdd] at h3
    exact h3

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FixedRank36
  CFSG.RankThree.PartOne.Torsion37 CFSG.RankThree.PartTwo.Sec3 Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11

theorem frattini_irreducible_of_normalizer {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {D R : Subgroup G} (hRN : R ≤ normalizer (D : Set G)) (hD : IsPGroup q D)
    (hrel : (inSubgroup frattini D).relIndex D = q ^ 4) (hR : IsExtraspecialPGroup 2 R)
    (hR32 : Nat.card R = 32) (hRD : R ⊓ Subgroup.centralizer (D : Set G) = ⊥) :
    IsFrattiniIrreducibleFor R D := by
  classical
  unfold IsFrattiniIrreducibleFor
  have : Fact q.Prime := ⟨hq⟩
  have hel : IsElementaryAbelian q (↥D ⧸ frattini ↥D) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hD).2.2.2.1
  have hfd : FiniteDimensional (ZMod q) (Additive (↥D ⧸ frattini ↥D)) := Module.Finite.of_finite
  have hR2 : IsPGroup 2 R := hR.1
  have hdim : Module.finrank (ZMod q) (Additive (↥D ⧸ frattini ↥D)) = 4 := by
    have h1 : Nat.card (↥D ⧸ frattini ↥D) = q ^ 4 := by
      rw [← relIndex_inSubgroup_frattini_eq_card, hrel]
    have h2 : Nat.card (Additive (↥D ⧸ frattini ↥D)) = q ^ 4 := by
      rw [← h1]
      exact Nat.card_congr Additive.toMul
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod] at h2
    exact Nat.pow_right_injective hq.two_le h2
  have hinj : Function.Injective (frattiniRep q (conjAction D R hRN)) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : conjAction D R hRN r = 1 :=
      frattiniRep_eq_one hD hq2 (conjAction D R hRN) r
        (isPGroup_zpowers_map hR2 (conjAction D R hRN) r) hr
    have hmem : (r : G) ∈ R ⊓ Subgroup.centralizer (D : Set G) := by
      refine ⟨r.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h := congrArg (fun f : MulAut ↥D => ((f ⟨g, hg⟩ : ↥D) : G)) h1
      simp only [conjAction_apply_coe, MulAut.one_apply] at h
      calc g * (r : G) = ((r : G) * g * (r : G)⁻¹) * r := by rw [h]
        _ = r * g := by group
    rw [hRD, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨-, hirr, -⟩ := minimal_module_facts (two_ne_zero_zmod hq hq2) hR hR32
    (frattiniRep q (conjAction D R hRN)) hinj hdim
  refine ⟨hRN, ?_, fun X hΦX hXD hRX => ?_⟩
  ·
    refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    · intro h
      have h1 : (inSubgroup frattini D).relIndex D = 1 :=
        Subgroup.relIndex_eq_one.2 (le_of_eq h.symm)
      rw [hrel] at h1
      have h2 : 1 < q ^ 4 := one_lt_pow₀ hq.one_lt (by norm_num)
      rw [h1] at h2
      exact lt_irrefl _ h2
  ·
    set E := ↥D ⧸ frattini ↥D with hE
    let Xq : Subgroup E := (X.subgroupOf D).map (QuotientGroup.mk' (frattini ↥D))
    let U : Submodule (ZMod q) (Additive E) :=
      { carrier := {v | Additive.toMul v ∈ Xq}
        add_mem' := fun {a b} ha hb => by
          change Additive.toMul (a + b) ∈ Xq
          rw [toMul_add]
          exact Xq.mul_mem ha hb
        zero_mem' := by
          change Additive.toMul (0 : Additive E) ∈ Xq
          rw [toMul_zero]
          exact Xq.one_mem
        smul_mem' := fun c v hv => by
          change Additive.toMul (c • v) ∈ Xq
          have hc : c • v = c.val • v := by
            rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_zmod_val]
          rw [hc, toMul_nsmul]
          exact Xq.pow_mem hv _ }
    have hmemU : ∀ x : ↥D, Additive.ofMul (x : E) ∈ U ↔ (x : G) ∈ X := by
      intro x
      change (x : E) ∈ Xq ↔ _
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hy' : (y : G) ∈ X := hy
        have h1 : y⁻¹ * x ∈ frattini ↥D := QuotientGroup.eq.1 hyx
        have h2 : (((y⁻¹ * x : ↥D)) : G) ∈ inSubgroup frattini D := ⟨_, h1, rfl⟩
        have h3 : (((y⁻¹ * x : ↥D)) : G) ∈ X := hΦX h2
        have h4 : (x : G) = (y : G) * ((y⁻¹ * x : ↥D) : G) := by simp
        rw [h4]
        exact X.mul_mem hy' h3
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hUinv : ∀ r : ↥R, ∀ v ∈ U, frattiniRep q (conjAction D R hRN) r v ∈ U := by
      intro r v hv
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      have hvx : v = Additive.ofMul (x : E) := by rw [hx]; rfl
      rw [hvx] at hv ⊢
      rw [frattiniRep_apply]
      rw [hmemU] at hv ⊢
      have h1 := (Subgroup.mem_normalizer_iff.1 (hRX r.2) (x : G)).1 hv
      rw [conjAction_apply_coe]
      exact h1
    rcases hirr U hUinv with hU | hU
    · left
      refine le_antisymm (fun x hx => ?_) hΦX
      have hxD := hXD hx
      have h1 : Additive.ofMul ((⟨x, hxD⟩ : ↥D) : E) ∈ U := (hmemU ⟨x, hxD⟩).2 hx
      rw [hU, Submodule.mem_bot, ofMul_eq_zero] at h1
      exact ⟨⟨x, hxD⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
    · right
      refine le_antisymm hXD (fun d hd => ?_)
      have h1 : Additive.ofMul ((⟨d, hd⟩ : ↥D) : E) ∈ U := by rw [hU]; exact Submodule.mem_top
      exact (hmemU ⟨d, hd⟩).1 h1

end CFSG.RankThree.PartTwo.Sec11

end
