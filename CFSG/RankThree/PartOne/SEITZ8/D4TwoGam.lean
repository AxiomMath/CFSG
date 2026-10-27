module

public import CFSG.RankThree.PartOne.SEITZ8.D4TwoRad

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.CTP
open scoped commutatorElement Matrix

variable {K : Type} [Field K] {σ : K →+* K}

local notation "SL2F" => Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)

theorem eq_zero_or_one_of_card_two {L : Type} [Field L] {k : Subfield L} (hk : Nat.card k = 2)
    {c : L} (hc : c ∈ k) : c = 0 ∨ c = 1 := by
  by_contra h
  push Not at h
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : k)).1 hk
  have h1 : (⟨1, k.one_mem⟩ : k) = y := huniq _ (fun h' => one_ne_zero (congrArg Subtype.val h'))
  have h2 : (⟨c, hc⟩ : k) = y := huniq _ (fun h' => h.1 (congrArg Subtype.val h'))
  exact h.2 (congrArg Subtype.val (h2.trans h1.symm))

variable (σ) in
@[expose] noncomputable def Gam (k : Subfield K) (τ : K → fixedField σ) (t₁ μ : fixedField σ) :
    Subgroup (adjointGroup d4 K) :=
  Subgroup.closure ({xB 1, xd 8 (μ : K), xH 1 * xB (t₁ : K)} ∪
    {b | ∃ κ ∈ k, b = xAB σ κ * xB (τ κ : K)})

section Basic

variable {k : Subfield K} {τ : K → fixedField σ} {t₁ μ : fixedField σ}

theorem xB1_mem_Gam : xB (1 : K) ∈ Gam σ k τ t₁ μ :=
  Subgroup.subset_closure (Or.inl (by simp))

theorem x8_mem_Gam : xd 8 (μ : K) ∈ Gam σ k τ t₁ μ :=
  Subgroup.subset_closure (Or.inl (by simp))

theorem b1_mem_Gam : xH (1 : K) * xB (t₁ : K) ∈ Gam σ k τ t₁ μ :=
  Subgroup.subset_closure (Or.inl (by simp))

theorem b2_mem_Gam {κ : K} (hκ : κ ∈ k) : xAB σ κ * xB (τ κ : K) ∈ Gam σ k τ t₁ μ :=
  Subgroup.subset_closure (Or.inr ⟨κ, hκ, rfl⟩)

variable [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem Gam_le_PL : Gam σ k τ t₁ μ ≤ (rhoB σ).range ⊔ Qb σ := by
  have hL : ∀ c : fixedField σ, xB (c : K) ∈ (rhoB σ).range ⊔ Qb σ := fun c =>
    Subgroup.mem_sup_left (⟨u2 c, rhoB_u2 c⟩ : xB (c : K) ∈ (rhoB σ).range)
  refine (Subgroup.closure_le _).2 ?_
  rintro g (hg | ⟨κ, -, rfl⟩)
  · rcases hg with rfl | rfl | rfl
    · simpa using hL 1
    · exact Subgroup.mem_sup_left (⟨l2 μ, rhoB_l2 μ⟩ : xd 8 (μ : K) ∈ (rhoB σ).range)
    · exact mul_mem (Subgroup.mem_sup_right (xH_mem_Qb hσ (map_one σ))) (hL t₁)
  · exact mul_mem (Subgroup.mem_sup_right (xAB_mem_Qb hσ κ)) (hL (τ κ))

end Basic

variable (σ) in
@[expose] def lev (H : Subgroup (adjointGroup d4 K)) : Subgroup SL2F where
  carrier := {A | ∃ g ∈ H, ActsAs g A}
  mul_mem' := by
    rintro A B ⟨g, hg, hA⟩ ⟨g', hg', hB⟩
    exact ⟨g * g', mul_mem hg hg', hA.mul hB⟩
  one_mem' := ⟨1, one_mem _, ActsAs.one⟩
  inv_mem' := by
    rintro A ⟨g, hg, hA⟩
    exact ⟨g⁻¹, inv_mem hg, hA.inv⟩

theorem mem_lev {H : Subgroup (adjointGroup d4 K)} {A : SL2F} :
    A ∈ lev σ H ↔ ∃ g ∈ H, ActsAs g A := Iff.rfl

theorem exists_sq_eq' {L : Type} [Field L] [Finite L] [CharP L 2] (a : L) : ∃ s : L, s ^ 2 = a := by
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.1 (frobenius_inj L 2)) a
  exact ⟨s, by simpa [frobenius_def] using hs⟩

section Dickson

variable {k : Subfield K} {τ : K → fixedField σ} {t₁ μ : fixedField σ}
  [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c)
  {k₂ : Subfield (fixedField σ)}
include hσ

theorem lev_eq_top (hk₂ : Nat.card k₂ = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hF : Nat.card (fixedField σ) = Nat.card k₂ ^ d) (hμ : μ ≠ 0)
    (ht : ¬ (t₁ ∈ k₂ ∧ ∀ κ ∈ k, τ κ ∈ k₂)) : lev σ (Gam σ k τ t₁ μ) = ⊤ := by
  have hu1 : u2 (1 : fixedField σ) ∈ lev σ (Gam σ k τ t₁ μ) :=
    ⟨xB 1, xB1_mem_Gam, actsAs_xB 1⟩
  have hl : l2 μ ∈ lev σ (Gam σ k τ t₁ μ) := ⟨xd 8 (μ : K), x8_mem_Gam, actsAs_x8 μ⟩
  have hut1 : u2 t₁ ∈ lev σ (Gam σ k τ t₁ μ) :=
    ⟨xH 1 * xB (t₁ : K), b1_mem_Gam, (actsAs_xB t₁).Qb_mul hσ (xH_mem_Qb hσ (map_one σ))⟩
  have hut2 : ∀ κ ∈ k, u2 (τ κ) ∈ lev σ (Gam σ k τ t₁ μ) := fun κ hκ =>
    ⟨xAB σ κ * xB (τ κ : K), b2_mem_Gam hκ, (actsAs_xB (τ κ)).Qb_mul hσ (xAB_mem_Qb hσ κ)⟩
  obtain ⟨c, huc, hck⟩ : ∃ c : fixedField σ, u2 c ∈ lev σ (Gam σ k τ t₁ μ) ∧ c ∉ k₂ := by
    by_cases h1 : t₁ ∈ k₂
    · by_contra hcon
      push Not at hcon
      exact ht ⟨h1, fun κ hκ => by
        by_contra hτ
        exact hτ (hcon _ (hut2 κ hκ))⟩
    · exact ⟨t₁, hut1, h1⟩
  refine sl2_eq_top_of_root_groups hd hd2 hF (a₁ := 1) (a₂ := c) (b₀ := μ) one_ne_zero
    (by simpa using hck) hμ ?_ hl
  intro c₁ hc₁ c₂ hc₂
  rcases eq_zero_or_one_of_card_two hk₂ hc₁ with rfl | rfl <;>
    rcases eq_zero_or_one_of_card_two hk₂ hc₂ with rfl | rfl
  · simp only [zero_mul, add_zero, u2_zero]
    exact one_mem _
  · simpa using huc
  · simpa using hu1
  · rw [show (1 : fixedField σ) * 1 + 1 * c = 1 + c by ring, u2_add]
    exact mul_mem hu1 huc

end Dickson

section Facts

variable [CharP K 2]

theorem xB_inv' (c : K) : (xB c)⁻¹ = xB c := xd_inv 2 c

theorem xAB_mul_self' (c : K) : xAB σ c * xAB σ c = 1 := by
  unfold xAB
  d4coll

theorem xAB_inv' (c : K) : (xAB σ c)⁻¹ = xAB σ c := inv_eq_of_mul_eq_one_right (xAB_mul_self' c)

omit [CharP K 2] in
theorem ordT_zero_one (x0 x4 x8 x3 x7 : K) :
    ordT σ (mkT x0 0 x4 x8 x3 x7) = xB x0 * xAB σ x4 * xAAB σ x8 * xN x3 * xH x7 := by
  rw [ordT_mkT]
  simp only [xA, map_zero, xd_zero, mul_one]

omit [CharP K 2] in
theorem xB_mem_Uhat (hσ : ∀ c, σ (σ (σ c)) = c) {c : K} (hc : σ c = c) : xB c ∈ Uhat σ :=
  le_iSup₂_of_le (f := fun p (_ : p ∈ posT) => twistedRootSubgroupD4 σ (rt p)) 0
    (by simp [posT]) le_rfl ((mem_XB hσ _).2 ⟨c, hc, rfl⟩)

end Facts

section Nontriv

variable {k : Subfield K} {τ : K → fixedField σ} {t₁ μ : fixedField σ}
  [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c)
  {k₂ : Subfield (fixedField σ)}
include hσ

theorem exists_nontriv (hk₂ : Nat.card k₂ = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hF : Nat.card (fixedField σ) = Nat.card k₂ ^ d) (hμ : μ ≠ 0)
    (ht : ¬ (t₁ ∈ k₂ ∧ ∀ κ ∈ k, τ κ ∈ k₂)) :
    ∃ n ∈ Gam σ k τ t₁ μ, n ∈ Uhat σ ∧ ActsAs n (1 : SL2F) ∧ n ≠ 1 := by
  have htop := lev_eq_top hσ hk₂ hd hd2 hF hμ ht
  have hb2 : xAB σ 1 * xB (τ 1 : K) ∈ Gam σ k τ t₁ μ := b2_mem_Gam k.one_mem
  have hq1 : xAB σ (1 : K) ∈ Qb σ := xAB_mem_Qb hσ 1
  have hb2A : ActsAs (xAB σ 1 * xB (τ 1 : K)) (u2 (τ 1)) :=
    (actsAs_xB (τ 1)).Qb_mul hσ hq1
  have hb2U : xAB σ 1 * xB (τ 1 : K) ∈ Uhat σ :=
    mul_mem (Qb_le_Uhat hq1) (xB_mem_Uhat hσ (τ 1).2)
  by_cases h2 : τ 1 = 0
  · refine ⟨xAB σ 1 * xB (τ 1 : K), hb2, hb2U, ?_, ?_⟩
    · simpa [h2, u2_zero] using hb2A
    · intro h1
      rw [h2] at h1
      have h3 : xAB σ (1 : K) = ordT σ (mkT 0 0 1 0 0 0) := by
        rw [ordT_zero_one]
        simp [xB, xAAB, xN, xH, xd_zero]
      have h4 : (1 : adjointGroup d4 K) = ordT σ (mkT 0 0 0 0 0 0) := by
        rw [ordT_zero_one]
        simp [xB, xAB, xAAB, xN, xH, xd_zero]
      simp only [ZeroMemClass.coe_zero, xB, xd_zero, mul_one] at h1
      rw [h3, h4] at h1
      have := (ordT_inj σ h1).2.2.1
      simp [mkT] at this
  · obtain ⟨r, hr⟩ := exists_sq_eq' (τ 1)
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply h2
      rw [← hr]
      ring
    obtain ⟨γ, hγ, hγA⟩ :=
      (mem_lev (H := Gam σ k τ t₁ μ) (A := dgm r hr0)).1 (htop ▸ Subgroup.mem_top _)
    obtain ⟨A', q, hq, hγeq, hγA'⟩ := exists_actsAs_of_mem_PL hσ (Gam_le_PL hσ hγ)
    have hAA : A' = dgm r hr0 := hγA'.unique hγA
    have hu2 : A' * u2 1 * A'⁻¹ = u2 (τ 1) := by
      rw [hAA, dgm_mul_u2_mul_dgm_inv, mul_one, hr]
    have e1 : rhoB σ A' * xB (1 : K) * (rhoB σ A')⁻¹ = xB (τ 1 : K) := by
      have h1 := rhoB_u2 (σ := σ) 1
      calc rhoB σ A' * xB (1 : K) * (rhoB σ A')⁻¹ = rhoB σ (A' * u2 1 * A'⁻¹) := by
            rw [map_mul, map_mul, map_inv, h1]
            rfl
        _ = xB (τ 1 : K) := by rw [hu2, rhoB_u2]
    set q' : adjointGroup d4 K := rhoB σ A' * q * (rhoB σ A')⁻¹ with hq'
    have hq'Qb : q' ∈ Qb σ := rhoB_conj_Qb hσ A' hq
    have hconj : γ * xB (1 : K) * γ⁻¹ = q' * xB (τ 1 : K) * q'⁻¹ := by
      calc γ * xB (1 : K) * γ⁻¹ = (rhoB σ A' * q * (rhoB σ A')⁻¹) *
            (rhoB σ A' * xB (1 : K) * (rhoB σ A')⁻¹) * (rhoB σ A' * q * (rhoB σ A')⁻¹)⁻¹ := by
            rw [hγeq]
            group
        _ = q' * xB (τ 1 : K) * q'⁻¹ := by rw [e1]
    have hγact : ActsAs (γ * xB (1 : K) * γ⁻¹) (u2 (τ 1)) := by
      have := (hγA.mul (actsAs_xB (1 : fixedField σ))).mul hγA.inv
      rwa [show dgm r hr0 * u2 1 * (dgm r hr0)⁻¹ = u2 (τ 1) by rw [← hAA]; exact hu2] at this
    refine ⟨(xAB σ 1 * xB (τ 1 : K)) * (γ * xB (1 : K) * γ⁻¹),
      mul_mem hb2 (mul_mem (mul_mem hγ xB1_mem_Gam) (inv_mem hγ)), mul_mem hb2U ?_, ?_, ?_⟩
    · rw [hconj]
      exact mul_mem (mul_mem (Qb_le_Uhat hq'Qb) (xB_mem_Uhat hσ (τ 1).2))
        (inv_mem (Qb_le_Uhat hq'Qb))
    · rw [← u2_mul_self (τ 1)]
      exact hb2A.mul hγact
    · intro h1
      rw [hconj] at h1
      have h3 : q' * xB (τ 1 : K) * q'⁻¹ = (xAB σ 1 * xB (τ 1 : K))⁻¹ :=
        eq_inv_of_mul_eq_one_right h1
      obtain ⟨c, -, -, -, hc⟩ := exists_ordT hσ (Qb_le_Uhat hq'Qb)
      rw [hc, conj_xB σ hσ c _ (τ 1).2, mul_inv_rev, xAB_inv', xB_inv'] at h3
      rw [show xB (τ 1 : K) * xAB σ 1 =
        xB (τ 1 : K) * xAB σ 1 * xAAB σ 0 * xN 0 * xH 0 by simp [xAAB, xN, xH, xd_zero]] at h3
      rw [← ordT_zero_one, ← ordT_zero_one] at h3
      obtain ⟨-, -, h41, h81, -, -⟩ := ordT_inj σ h3
      simp only [mkT] at h41 h81
      norm_num at h41 h81
      rcases h81 with h | h
      · exact h2 h
      · rw [h, mul_zero] at h41
        exact zero_ne_one h41

end Nontriv

end CFSG.RankThree.PartOne.SEITZ8
