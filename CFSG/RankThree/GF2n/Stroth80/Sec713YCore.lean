module

public import CFSG.RankThree.GF2n.Stroth80.Sec85CommOdd
public import CFSG.RankThree.GF2n.Stroth80.Sec79OmegaFixed

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.CGT.Timmesfeld75
  QuadraticMap
open scoped commutatorElement Matrix

section Braid

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

theorem exists_lift_LomGL (E : ElemMatrixIso Q X) {u : ι → K} {g : Gom Q} (hg : g ∈ Lom Q u) :
    ∃ A : X, E.equiv A = g ∧ (A : GL ι K) ∈ E.LomGL u := by
  refine ⟨E.equiv.symm g, MulEquiv.apply_symm_apply E.equiv g, ?_⟩
  unfold ElemMatrixIso.LomGL
  rw [mem_matrixOf_iff]
  refine ⟨(E.equiv.symm g).2, ?_⟩
  have h1 : E.equiv ⟨((E.equiv.symm g : X) : GL ι K), (E.equiv.symm g).2⟩ = g :=
    MulEquiv.apply_symm_apply E.equiv g
  rw [h1]
  exact hg

theorem exists_braid_pair (E : ElemMatrixIso Q X) (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Fintype.card ι) {Y : Type*} [Group Y] (φ : Y →* GL ι K) {L₁ L₂ : Subgroup Y}
    {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    (hL₁ : L₁.map φ = E.LomGL u) (hL₂ : L₂.map φ = E.LomGL u') :
    ∃ a ∈ L₁, ∃ b ∈ L₂, φ a * φ a = 1 ∧ φ b * φ b = 1 ∧ (φ a * φ b) ^ 3 = 1 ∧
      φ a * φ b ≠ 1 ∧ (∃ v : ι → K, polar Q v ((φ a : Matrix ι ι K) *ᵥ v) ≠ 0) ∧
      (∃ v : ι → K, polar Q v ((φ b : Matrix ι ι K) *ᵥ v) ≠ 0) := by
  classical
  have hu'0 : u' ≠ 0 := by
    rintro rfl
    exact huu' (by simp)
  obtain ⟨w, hw1, hw2⟩ := exists_nonsingular_perp hQ (by simpa using h4) hu'0
  obtain ⟨w', hew, hfw, hQw, -⟩ :=
    exists_perp_eichlerG_eq (e := u) (f := u') (w := w) hu' huu' hw1
  have hc : Q w' ≠ 0 := by rw [hQw]; exact hw2
  obtain ⟨t, ht⟩ : ∃ t : K, polar Q u u' = t := ⟨_, rfl⟩
  have htne : t ≠ 0 := by rw [← ht]; exact huu'
  have hct : Q w' * t ≠ 0 := mul_ne_zero hc htne
  have hew₀ : polar Q u ((Q w' * t)⁻¹ • w') = 0 := by
    rw [polar_smul_right_eq, hew, mul_zero]
  have hQw₀ : Q ((Q w' * t)⁻¹ • w') ≠ 0 := by
    rw [map_smul_eq_sq]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hct)) hc
  have hgyL : eichlerG Q u ((Q w' * t)⁻¹ • w') ∈ Lom Q u := eichlerG_mem_Lom hew₀
  have hgbL : eichlerG Q u' w' ∈ Lom Q u' := eichlerG_mem_Lom hfw
  have hyy : eichlerG Q u ((Q w' * t)⁻¹ • w') * eichlerG Q u ((Q w' * t)⁻¹ • w') = 1 :=
    eichlerG_mul_self hew₀
  have hbb : eichlerG Q u' w' * eichlerG Q u' w' = 1 := eichlerG_mul_self hfw
  have hbraid := eichlerG_braid hu hu' ht htne hew hfw hc
  have hpair := eichlerG_pair_app_left hu hu' ht htne hew hfw hc
  obtain ⟨gy, hgy⟩ : ∃ gy : Gom Q, gy = eichlerG Q u ((Q w' * t)⁻¹ • w') := ⟨_, rfl⟩
  obtain ⟨gb, hgb⟩ : ∃ gb : Gom Q, gb = eichlerG Q u' w' := ⟨_, rfl⟩
  rw [← hgy] at hgyL hyy hbraid hpair
  rw [← hgb] at hgbL hbb hbraid hpair
  have hcube : (gy * gb) ^ 3 = 1 := by
    have e1 : (gy * gb) ^ 3 = (gy * gb * gy) * (gb * gy * gb) := by
      rw [pow_succ, pow_succ, pow_one]
      group
    rw [e1, hbraid]
    have e2 : gb * gy * gb * (gb * gy * gb) = gb * gy * (gb * gb) * gy * gb := by group
    rw [e2, hbb, mul_one]
    have e3 : gb * gy * gy * gb = gb * (gy * gy) * gb := by group
    rw [e3, hyy, mul_one, hbb]
  obtain ⟨Ay, hAy, hAyL⟩ := exists_lift_LomGL E hgyL
  obtain ⟨Ab, hAb, hAbL⟩ := exists_lift_LomGL E hgbL
  rw [← hL₁] at hAyL
  rw [← hL₂] at hAbL
  obtain ⟨a, ha, haφ⟩ := Subgroup.mem_map.mp hAyL
  obtain ⟨b, hb, hbφ⟩ := Subgroup.mem_map.mp hAbL
  have hAyy : Ay * Ay = 1 := E.equiv.injective (by rw [map_mul, hAy, hyy, map_one])
  have hAbb : Ab * Ab = 1 := E.equiv.injective (by rw [map_mul, hAb, hbb, map_one])
  have hAcube : (Ay * Ab) ^ 3 = 1 :=
    E.equiv.injective (by rw [map_pow, map_mul, hAy, hAb, hcube, map_one])
  have hAne : Ay * Ab ≠ 1 := by
    intro h1
    have h2 : gy * gb = 1 := by
      have := congrArg E.equiv h1
      rwa [map_mul, hAy, hAb, map_one] at this
    have h3 := hpair
    rw [h2, Gom.app_one] at h3
    apply htne
    have h4' : polar Q u u' = polar Q ((Q w' * t) • u') u' := by rw [← h3]
    rw [← ht, h4', polar_smul_left_eq, polar_self_eq_zero hu', mul_zero]
  refine ⟨a, ha, b, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [haφ]
    have := congrArg Subtype.val hAyy
    simpa using this
  · rw [hbφ]
    have := congrArg Subtype.val hAbb
    simpa using this
  · rw [haφ, hbφ]
    have := congrArg Subtype.val hAcube
    simpa using this
  · rw [haφ, hbφ]
    intro h1
    apply hAne
    exact Subtype.ext (by simpa using h1)
  · refine ⟨u', ?_⟩
    rw [haφ, ← E.app Ay, hAy, hgy]
    have h2 : (eichlerG Q u ((Q w' * t)⁻¹ • w')).app u' =
        eichler Q u ((Q w' * t)⁻¹ • w') u' := rfl
    rw [h2, polar_apply_eichler_self hu hew₀, CharTwo.two_eq_zero, zero_mul, zero_sub]
    refine neg_ne_zero.mpr (mul_ne_zero hQw₀ (pow_ne_zero 2 ?_))
    rw [polar_comm]
    exact huu'
  · refine ⟨u, ?_⟩
    rw [hbφ, ← E.app Ab, hAb, hgb]
    have h2 : (eichlerG Q u' w').app u = eichler Q u' w' u := rfl
    rw [h2, polar_apply_eichler_self hu' hfw, CharTwo.two_eq_zero, zero_mul, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hc (pow_ne_zero 2 huu'))

end Braid

section Core

variable {G : Type} [Group G] [Finite G] {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
  {R N P I L₁ L₂ A₁ A₂ : Subgroup G}

theorem exists_fpf_of_hom (E : ElemMatrixIso Q X) (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Fintype.card ι) (φ : ↥R →* GL ι K) (hφ : φ.range = X)
    (hNφ : φ.ker = N.subgroupOf R)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hI : ∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I)
    (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R)
    (h₂ : L₂ ≤ R) {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = E.LomGL u) (hL₂ : (L₂.subgroupOf R).map φ = E.LomGL u') :
    ∃ g : ↥R, g ^ 3 ∈ N.subgroupOf R ∧ g ∉ N.subgroupOf R ∧
      ∀ s : ℕ, s % 3 = 1 → ∀ c ∈ P, ⁅((g ^ s : ↥R) : G), c⁆ ∈ I → c ∈ I := by
  classical
  have hsec := SecHyp.of_isOppDecomp hd hP hI
  obtain ⟨M, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsec hN
  haveI : Finite M := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hd h₁ h₂
  have huu'' : polar Q u' u ≠ 0 := by rwa [polar_comm]
  obtain ⟨a, ha, b, hb, haa, hbb, hab3, hab1, hna, hnb⟩ :=
    exists_braid_pair E hQ h4 φ hu hu' huu' hL₁ hL₂
  obtain ⟨ha1, -, -⟩ := stroth_2_1_ii_omega_fixed_of_hom E φ hφ hQ hκ.two hker hu' hu huu'' hL₂ hL₁
    hdec.symm h4 ha hna
  obtain ⟨hb1, -, -⟩ := stroth_2_1_ii_omega_fixed_of_hom E φ hφ hQ hκ.two hker hu hu' huu' hL₁ hL₂
    hdec h4 hb hnb
  have hinf : fixedSub M {a} ⊓ fixedSub M {b} = ⊥ := by
    rw [ha1, hb1]
    exact hdec.inf_eq_bot
  have hker_mem : ∀ x : ↥R, φ x = 1 → ∀ m : M, x • m = m := fun x hx m =>
    hker x (MonoidHom.mem_ker.mpr hx) m
  have haa' : ∀ m : M, a • a • m = m := fun m => by
    rw [← mul_smul]
    exact hker_mem _ (by rw [map_mul]; exact haa) m
  have hbb' : ∀ m : M, b • b • m = m := fun m => by
    rw [← mul_smul]
    exact hker_mem _ (by rw [map_mul]; exact hbb) m
  have hgfix : fixedSub M {a * b} = ⊥ := fixedSub_mul_eq_bot_of_smul_sq hκ.two haa' hbb' hinf
  set g : ↥R := a * b with hg
  have hg3 : g ^ 3 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hg, map_mul]
    exact hab3
  refine ⟨g, by rw [← hNφ]; exact hg3, ?_, ?_⟩
  · rw [← hNφ, MonoidHom.mem_ker, hg, map_mul]
    exact hab1
  · intro s hs c hcP hcomm
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s = 3 * k + 1 := ⟨s / 3, by omega⟩
    have hacty : ∀ m : M, (g ^ s) • m = g • m := by
      intro m
      rw [hk, pow_add, pow_mul, mul_smul, pow_one]
      exact hker _ (Subgroup.pow_mem _ hg3 k) _
    set y : ↥R := g ^ s with hy
    have hcP' : (y : G) * c * (y : G)⁻¹ ∈ P := hP (y : G) y.2 c hcP
    have hact := hκ.act y ⟨c, hcP⟩ ⟨(y : G) * c * (y : G)⁻¹, hcP'⟩ rfl
    have heq : κ ⟨(y : G) * c * (y : G)⁻¹, hcP'⟩ = κ ⟨c, hcP⟩ := by
      rw [hκ.eq_iff]
      have e : (y : G) * c * (y : G)⁻¹ * c⁻¹ = ⁅(y : G), c⁆ := by
        simp [commutatorElement_def]
      show (y : G) * c * (y : G)⁻¹ * c⁻¹ ∈ I
      rw [e]
      exact hcomm
    rw [heq] at hact
    have hfix : Multiplicative.toAdd (κ ⟨c, hcP⟩) ∈ fixedSub M {g} := by
      refine mem_fixedSub.mpr fun x hx => ?_
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have h1 := congrArg Multiplicative.toAdd hact
      rw [toAdd_ofAdd, hacty] at h1
      exact h1.symm
    rw [hgfix] at hfix
    have h0 : κ ⟨c, hcP⟩ = 1 :=
      Multiplicative.toAdd.injective (show Multiplicative.toAdd (κ ⟨c, hcP⟩) = 0 from hfix)
    exact (hκ.ker ⟨c, hcP⟩).mp h0

end Core

end CFSG.RankThree.GF2n.Stroth80
