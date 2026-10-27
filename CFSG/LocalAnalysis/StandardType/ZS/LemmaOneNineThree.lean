module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNinePlane

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

private lemma mul_div_not_mem_four {τ x y z : ZMod p} (h4 : orderOf τ = 4)
    (hx : x = -τ ∨ x = τ ^ 2 - τ + 1) (hy : y = -τ ∨ y = τ ^ 2 - τ + 1)
    (hz : z * (τ - 1) ^ 2 = x * y) : z ≠ -τ ∧ z ≠ τ ^ 2 - τ + 1 := by
  have hτ4 : τ ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one τ
  have hlt : ∀ m < 4, 0 < m → τ ^ m ≠ 1 := ((orderOf_eq_iff (by norm_num : 0 < 4)).mp h4).2
  have hsq : τ ^ 2 = -1 := by
    have h2 : (τ ^ 2) ^ 2 = 1 := by rw [← pow_mul]; norm_num; exact hτ4
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact absurd h (hlt 2 (by norm_num) (by norm_num))
    · exact h
  have hq : τ ^ 2 - τ + 1 = -τ := by linear_combination hsq
  have hx' : x = -τ := hx.elim id (fun h => h.trans hq)
  have hy' : y = -τ := hy.elim id (fun h => h.trans hq)
  constructor
  · intro hzneg
    rw [hzneg, hx', hy'] at hz
    have h1 : (1 : ZMod p) = 0 := by linear_combination (-1) * hz + (1 - τ) * hsq
    exact one_ne_zero h1
  · rw [hq]
    intro hzneg
    rw [hzneg, hx', hy'] at hz
    have h1 : (1 : ZMod p) = 0 := by linear_combination (-1) * hz + (1 - τ) * hsq
    exact one_ne_zero h1

private lemma five_facts {τ : ZMod p} (h5 : orderOf τ = 5) :
    τ ^ 4 + τ ^ 3 + τ ^ 2 + τ + 1 = 0 ∧ 5 ∣ p - 1 := by
  have hτ5 : τ ^ 5 = 1 := by rw [← h5]; exact pow_orderOf_eq_one τ
  have hlt5 : ∀ m < 5, 0 < m → τ ^ m ≠ 1 := ((orderOf_eq_iff (by norm_num : 0 < 5)).mp h5).2
  have hτ1 : τ ≠ 1 := by simpa using hlt5 1 (by norm_num) (by norm_num)
  have hΦ : τ ^ 4 + τ ^ 3 + τ ^ 2 + τ + 1 = 0 := by
    have h : (τ - 1) * (τ ^ 4 + τ ^ 3 + τ ^ 2 + τ + 1) = 0 := by linear_combination hτ5
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (sub_eq_zero.mp h') hτ1
    · exact h'
  have hτne0 : τ ≠ 0 := by
    intro h0
    rw [h0] at hτ5
    norm_num at hτ5
  have hdiv5 : 5 ∣ p - 1 := by
    have hdiv : orderOf τ ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hτne0
    rwa [h5] at hdiv
  exact ⟨hΦ, hdiv5⟩

private lemma five_contra16 (hdiv5 : 5 ∣ p - 1) {N : ℕ} (hN : N = 16)
    (hN0 : (N : ZMod p) = 0) : False := by
  rw [hN] at hN0
  have hp16 : p ∣ 16 := (ZMod.natCast_eq_zero_iff 16 p).mp hN0
  have hp2 : p = 2 := by
    have h2pow : p ∣ 2 ^ 4 := by norm_num; exact hp16
    have hpdiv2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow h2pow
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hpdiv2
  have h51 : 5 ∣ 1 := by
    rw [hp2] at hdiv5
    exact hdiv5
  exact Nat.prime_five.not_dvd_one h51

private lemma five_neg_tau {τ x y z : ZMod p} (hΦ : τ ^ 4 + τ ^ 3 + τ ^ 2 + τ + 1 = 0)
    (hdiv5 : 5 ∣ p - 1) (hx : x = -τ ∨ x = τ ^ 2 - τ + 1)
    (hy : y = -τ ∨ y = τ ^ 2 - τ + 1) (hz : z * (τ - 1) ^ 2 = x * y) : z ≠ -τ := by
  intro hzneg
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rw [hx, hy, hzneg] at hz
    have hr : (-τ) * (τ - 1) ^ 2 - (-τ) * (-τ) = 0 := by linear_combination hz
    have hN : (1 : ZMod p) = 0 := by
      linear_combination (-1 - τ + τ ^ 3) * hr - (-1 + 2 * τ - τ ^ 2) * hΦ
    exact one_ne_zero hN
  · rw [hx, hy, hzneg] at hz
    have hr : (-τ) * (τ - 1) ^ 2 - (-τ) * (τ ^ 2 - τ + 1) = 0 := by linear_combination hz
    have hN : (1 : ZMod p) = 0 := by
      linear_combination (τ ^ 3) * hr - (-1 + τ) * hΦ
    exact one_ne_zero hN
  · rw [hx, hy, hzneg] at hz
    have hr : (-τ) * (τ - 1) ^ 2 - (-τ) * (τ ^ 2 - τ + 1) = 0 := by linear_combination hz
    have hN : (1 : ZMod p) = 0 := by
      linear_combination (τ ^ 3) * hr - (-1 + τ) * hΦ
    exact one_ne_zero hN
  · rw [hx, hy, hzneg] at hz
    have hr : (-τ) * (τ - 1) ^ 2 - (τ ^ 2 - τ + 1) * (τ ^ 2 - τ + 1) = 0 := by
      linear_combination hz
    have hN : (16 : ZMod p) = 0 := by
      linear_combination (-8 - 8 * τ) * hr - (-8 + 8 * τ) * hΦ
    exact five_contra16 hdiv5 rfl hN

private lemma five_q {τ x y z : ZMod p} (hΦ : τ ^ 4 + τ ^ 3 + τ ^ 2 + τ + 1 = 0)
    (hdiv5 : 5 ∣ p - 1) (hx : x = -τ ∨ x = τ ^ 2 - τ + 1)
    (hy : y = -τ ∨ y = τ ^ 2 - τ + 1) (hz : z * (τ - 1) ^ 2 = x * y) :
    z ≠ τ ^ 2 - τ + 1 := by
  intro hzq
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rw [hx, hy, hzq] at hz
    have hr : (τ ^ 2 - τ + 1) * (τ - 1) ^ 2 - (-τ) * (-τ) = 0 := by linear_combination hz
    have hN : (16 : ZMod p) = 0 := by
      linear_combination (16 + 16 * τ - 8 * τ ^ 3) * hr
        - (-32 * τ + 32 * τ ^ 2 - 8 * τ ^ 3) * hΦ
    exact five_contra16 hdiv5 rfl hN
  · rw [hx, hy, hzq] at hz
    have hr : (τ ^ 2 - τ + 1) * (τ - 1) ^ 2 - (-τ) * (τ ^ 2 - τ + 1) = 0 := by
      linear_combination hz
    have hN : (1 : ZMod p) = 0 := by
      linear_combination (-3 - 3 * τ + 2 * τ ^ 3) * hr
        - (-4 + 7 * τ - 6 * τ ^ 2 + 2 * τ ^ 3) * hΦ
    exact one_ne_zero hN
  · rw [hx, hy, hzq] at hz
    have hr : (τ ^ 2 - τ + 1) * (τ - 1) ^ 2 - (-τ) * (τ ^ 2 - τ + 1) = 0 := by
      linear_combination hz
    have hN : (1 : ZMod p) = 0 := by
      linear_combination (-3 - 3 * τ + 2 * τ ^ 3) * hr
        - (-4 + 7 * τ - 6 * τ ^ 2 + 2 * τ ^ 3) * hΦ
    exact one_ne_zero hN
  · rw [hx, hy, hzq] at hz
    have hr : (τ ^ 2 - τ + 1) * (τ - 1) ^ 2 - (τ ^ 2 - τ + 1) * (τ ^ 2 - τ + 1) = 0 := by
      linear_combination hz
    have hN : (1 : ZMod p) = 0 := by
      linear_combination (-1 - τ + τ ^ 3) * hr - (-1 + 2 * τ - τ ^ 2) * hΦ
    exact one_ne_zero hN

theorem mul_div_not_mem {τ x y z : ZMod p} (hτ : orderOf τ = 4 ∨ orderOf τ = 5)
    (hx : x = -τ ∨ x = τ ^ 2 - τ + 1) (hy : y = -τ ∨ y = τ ^ 2 - τ + 1)
    (hz : z * (τ - 1) ^ 2 = x * y) : z ≠ -τ ∧ z ≠ τ ^ 2 - τ + 1 := by
  rcases hτ with h4 | h5
  · exact mul_div_not_mem_four h4 hx hy hz
  · obtain ⟨hΦ, hdiv5⟩ := five_facts h5
    exact ⟨five_neg_tau hΦ hdiv5 hx hy hz, five_q hΦ hdiv5 hx hy hz⟩

variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M] {R : Subgroup (M ≃ₗ[ZMod p] M)}
  {τ : ZMod p} {α β γ : M ≃ₗ[ZMod p] M} {c₁ c₂ w y : M} {φ₁ φ₂ φ : Module.Dual (ZMod p) M}

private lemma l1i_span_pair_left (hτ1 : τ ≠ 1) :
    w ∈ Submodule.span (ZMod p) ({w + y, τ • w + y} : Set M) := by
  have hsub_ne : (1 - τ : ZMod p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hτ1)
  have h1 : w + y - (τ • w + y) = (1 - τ) • w := by module
  have h2 : w + y - (τ • w + y) ∈ Submodule.span (ZMod p) ({w + y, τ • w + y} : Set M) :=
    Submodule.sub_mem _ (Submodule.subset_span (Set.mem_insert _ _))
      (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [h1] at h2
  have h3 := Submodule.smul_mem _ ((1 - τ)⁻¹) h2
  rwa [smul_smul, inv_mul_cancel₀ hsub_ne, one_smul] at h3

private lemma l1i_span_pair_right (hτ1 : τ ≠ 1) :
    y ∈ Submodule.span (ZMod p) ({w + y, τ • w + y} : Set M) := by
  have hsub_ne : (1 - τ : ZMod p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hτ1)
  have h1 : τ • w + y - τ • (w + y) = (1 - τ) • y := by module
  have h2 : τ • w + y - τ • (w + y) ∈ Submodule.span (ZMod p) ({w + y, τ • w + y} : Set M) :=
    Submodule.sub_mem _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
  rw [h1] at h2
  have h3 := Submodule.smul_mem _ ((1 - τ)⁻¹) h2
  rwa [smul_smul, inv_mul_cancel₀ hsub_ne, one_smul] at h3

private lemma four_basic (hτ : 4 ≤ orderOf τ) :
    τ ≠ 1 ∧ (τ - 1 : ZMod p) ≠ 0 := by
  have h1 : τ ≠ 1 := by
    intro h
    have : orderOf τ = 1 := by rw [h, orderOf_one]
    omega
  exact ⟨h1, sub_ne_zero.mpr h1⟩

private lemma l1i_exists_psi (htv : QTwoLin.TransvectionFree R) (hτ : 4 ≤ orderOf τ)
    (hα : α ∈ R) (hβ : β ∈ R) (h₁ : IsHomologyWith τ α c₁ φ₁)
    (h₂ : IsHomologyWith τ β c₂ φ₂) (hcomm : α * β ≠ β * α)
    (hw : w ∈ Submodule.span (ZMod p) {c₁, c₂}) (hy₁ : φ₁ y = 0) (hy₂ : φ₂ y = 0) :
    ∃ ψ : M ≃ₗ[ZMod p] M, ψ ∈ R ∧ ψ w = τ • w ∧ ψ y = y := by
  obtain ⟨ψ, hψmem, hψW, hψY⟩ :=
    exists_eq_smul_on_span_of_not_commute htv hα hβ h₁ h₂ hτ hcomm
  refine ⟨ψ, ?_, hψW w hw, hψY y hy₁ hy₂⟩
  refine (Subgroup.closure_le R).mpr ?_ hψmem
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hα
  · exact hβ

private lemma l1i_conj_homology {ψ : M ≃ₗ[ZMod p] M}
    (hγh : IsHomologyWith τ γ (w + y) φ) (hψw : ψ w = τ • w) (hψy : ψ y = y) :
    IsHomologyWith τ (ψ * γ * ψ⁻¹) (τ • w + y) (φ ∘ₗ (ψ.symm : M →ₗ[ZMod p] M)) := by
  have h := hγh.conj ψ
  have hc : ψ (w + y) = τ • w + y := by rw [map_add, hψw, hψy]
  rw [hc] at h
  exact h

private lemma l1i_ne_of_conj {δ : M ≃ₗ[ZMod p] M} {ψ' : Module.Dual (ZMod p) M}
    (hγh : IsHomologyWith τ γ (w + y) φ)
    (hδh : IsHomologyWith τ δ (τ • w + y) ψ') (hτne1 : τ ≠ 1)
    (hcompl : IsCompl (Submodule.span (ZMod p) ({c₁, c₂} : Set M))
      (LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂)) (hw0 : w ≠ 0) (hy0 : y ≠ 0)
    (hw : w ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M)) (hy₁ : φ₁ y = 0) (hy₂ : φ₂ y = 0) :
    γ ≠ δ := by
  intro heq
  have hδeig : δ (w + y) = τ • (w + y) := by rw [← heq]; exact hγh.apply_centre
  have hmem : w + y ∈ Submodule.span (ZMod p) ({τ • w + y} : Set M) :=
    hδh.mem_span_of_apply_eq_smul hτne1 hδeig
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hlin : (a * τ - 1) • w = (1 - a) • y := by
    calc (a * τ - 1) • w = a • (τ • w + y) - a • y - w := by module
      _ = (w + y) - a • y - w := by rw [ha]
      _ = (1 - a) • y := by module
  have hW : (a * τ - 1) • w ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M) :=
    Submodule.smul_mem _ _ hw
  have hY : (a * τ - 1) • w ∈ LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂ := by
    rw [hlin]
    exact Submodule.smul_mem _ _ ⟨LinearMap.mem_ker.mpr hy₁, LinearMap.mem_ker.mpr hy₂⟩
  have hzero : (a * τ - 1) • w = 0 := by
    have hbot : (a * τ - 1) • w ∈ (⊥ : Submodule (ZMod p) M) :=
      hcompl.disjoint.le_bot ⟨hW, hY⟩
    simpa using hbot
  have haτ : a * τ = 1 := by
    rcases (smul_eq_zero.mp hzero) with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  have halin : (1 - a) • y = 0 := by rw [← hlin, hzero]
  have ha1 : a = 1 := by
    rcases (smul_eq_zero.mp halin) with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hy0
  rw [ha1, one_mul] at haτ
  exact hτne1 haτ

private lemma l1i_psi_inv {ψ : M ≃ₗ[ZMod p] M} (hτne0 : τ ≠ 0)
    (hψw : ψ w = τ • w) (hψy : ψ y = y) :
    ψ.symm w = τ⁻¹ • w ∧ ψ.symm y = y := by
  constructor
  · refine ψ.injective ?_
    rw [LinearEquiv.apply_symm_apply, map_smul, hψw, smul_smul, inv_mul_cancel₀ hτne0, one_smul]
  · refine ψ.injective ?_
    rw [LinearEquiv.apply_symm_apply, hψy]

private lemma l1i_transvection_contra (htv : QTwoLin.TransvectionFree R)
    {g h : M ≃ₗ[ZMod p] M} {cg ch : M} {φg φh : Module.Dual (ZMod p) M}
    (hg : g ∈ R) (hh : h ∈ R) (hgh : IsHomologyWith τ g cg φg)
    (hhh : IsHomologyWith τ h ch φh) (hτ2 : τ ^ 2 ≠ 1) (hne : g ≠ h)
    {v : M} (hv0 : v ≠ 0) (hv : v ∈ Submodule.span (ZMod p) ({cg, ch} : Set M))
    (hv1 : φg v = 0) (hv2 : φh v = 0) : False := by
  obtain ⟨t, htmem, httv⟩ := exists_transvection_of_mem_span_ker hgh hhh hτ2 hne hv0 hv hv1 hv2
  exact htv t ((Subgroup.closure_le R).mpr (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hg
    · exact hh) htmem) httv

theorem false_of_mixed_centre_of_apply_eq_zero (htv : QTwoLin.TransvectionFree R)
    (hτ : 4 ≤ orderOf τ) (hα : α ∈ R) (hβ : β ∈ R) (hγ : γ ∈ R)
    (h₁ : IsHomologyWith τ α c₁ φ₁) (h₂ : IsHomologyWith τ β c₂ φ₂)
    (hγh : IsHomologyWith τ γ (w + y) φ) (hcomm : α * β ≠ β * α)
    (hw : w ∈ Submodule.span (ZMod p) {c₁, c₂}) (hw0 : w ≠ 0) (hy₁ : φ₁ y = 0) (hy₂ : φ₂ y = 0)
    (hy0 : y ≠ 0) (hz : φ w = 0 ∨ φ y = 0) : False := by
  obtain ⟨hτne1, _⟩ := four_basic hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have hle : orderOf τ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hτne0 : τ ≠ 0 := by
    intro h0
    have hpos : 0 < orderOf τ := by omega
    have hpow : (0 : ZMod p) ^ orderOf τ = 1 := by rw [← h0]; exact pow_orderOf_eq_one τ
    rw [zero_pow hpos.ne'] at hpow
    exact zero_ne_one hpow
  obtain ⟨hc₂, h12, h21, hq⟩ := linked_of_not_commute htv hα hβ h₁ h₂ hτ2 hcomm
  have hcompl : IsCompl (Submodule.span (ZMod p) ({c₁, c₂} : Set M))
      (LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂) := isCompl_span_ker_inf_ker h₁ h₂ hq
  obtain ⟨ψ, hψR, hψw, hψy⟩ := l1i_exists_psi htv hτ hα hβ h₁ h₂ hcomm hw hy₁ hy₂
  have hδh := l1i_conj_homology hγh hψw hψy
  have hδR : ψ * γ * ψ⁻¹ ∈ R :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hψR hγ) (Subgroup.inv_mem _ hψR)
  have hγneδ := l1i_ne_of_conj hγh hδh hτne1 hcompl hw0 hy0 hw hy₁ hy₂
  obtain ⟨hψinv_w, hψinv_y⟩ := l1i_psi_inv hτne0 hψw hψy
  rcases hz with hzw | hzy
  · exact l1i_transvection_contra htv hγ hδR hγh hδh hτ2 hγneδ hw0
      (l1i_span_pair_left hτne1) hzw (by
        change φ (ψ.symm w) = 0
        rw [hψinv_w, map_smul, hzw, smul_zero])
  · exact l1i_transvection_contra htv hγ hδR hγh hδh hτ2 hγneδ hy0
      (l1i_span_pair_right hτne1) hzy (by
        change φ (ψ.symm y) = 0
        rw [hψinv_y, hzy])

private lemma l1i_mem_Q_of_not_commute (htv : QTwoLin.TransvectionFree R) (hτ : 4 ≤ orderOf τ)
    {g h : M ≃ₗ[ZMod p] M} {cg ch : M} {φg φh : Module.Dual (ZMod p) M}
    (hg : g ∈ R) (hh : h ∈ R) (hgh : IsHomologyWith τ g cg φg)
    (hhh : IsHomologyWith τ h ch φh) (hcomm : g * h ≠ h * g) :
    φg ch * φh cg = -τ ∨ φg ch * φh cg = τ ^ 2 - τ + 1 := by
  rcases orderOf_eq_four_or_five_of_not_commute htv hg hh hgh hhh hτ hcomm with h4 | h5
  · left; exact apply_mul_apply_eq_of_not_commute_four htv hg hh hgh hhh h4 hcomm
  · exact apply_mul_apply_eq_of_not_commute_five htv hg hh hgh hhh h5 hcomm

private lemma l1i_wy_not_mem_W (hcompl : IsCompl (Submodule.span (ZMod p) ({c₁, c₂} : Set M))
      (LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂)) (hw : w ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M))
    (hφy : φ y ≠ 0) (hy₁ : φ₁ y = 0) (hy₂ : φ₂ y = 0) :
    w + y ∉ Submodule.span (ZMod p) ({c₁, c₂} : Set M) := by
  intro hmem
  have hyW : y ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M) := by
    have : (w + y) - w = y := by module
    rw [← this]
    exact Submodule.sub_mem _ hmem hw
  have hbot : y ∈ (⊥ : Submodule (ZMod p) M) :=
    hcompl.disjoint.le_bot ⟨hyW, ⟨LinearMap.mem_ker.mpr hy₁, LinearMap.mem_ker.mpr hy₂⟩⟩
  have hy0 : y = 0 := by simpa using hbot
  exact hφy (by rw [hy0, map_zero])

private lemma l1i_hwY (hcompl : IsCompl (Submodule.span (ZMod p) ({c₁, c₂} : Set M))
      (LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂))
    (hw : w ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M)) (hφw : φ w ≠ 0) :
    w ∉ LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂ := by
  intro hwin
  have hbot : w ∈ (⊥ : Submodule (ZMod p) M) := hcompl.disjoint.le_bot ⟨hw, hwin⟩
  have hw0 : w = 0 := by simpa using hbot
  exact hφw (by rw [hw0, map_zero])

private lemma l1i_chi_on_W {χ : Module.Dual (ZMod p) M} (hχ₁ : χ c₁ = 0) (hχ₂ : χ c₂ = 0) :
    ∀ v ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M), χ v = 0 := by
  intro v hv
  rw [Submodule.mem_span_pair] at hv
  obtain ⟨s, t, hst⟩ := hv
  rw [← hst, map_add, map_smul, map_smul, hχ₁, hχ₂, smul_zero, smul_zero, add_zero]

private lemma l1i_ne_y_span (hwY : w ∉ LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂)
    (hy₁ : φ₁ y = 0) (hy₂ : φ₂ y = 0) : w + y ∉ Submodule.span (ZMod p) ({y} : Set M) := by
  intro hmem
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hweq : w = (a - 1) • y := by
    calc w = (w + y) - y := by module
      _ = a • y - y := by rw [← ha]
      _ = (a - 1) • y := by module
  have hw_y : w ∈ Submodule.span (ZMod p) ({y} : Set M) := by
    rw [hweq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)
  have hyspan : Submodule.span (ZMod p) ({y} : Set M) ≤ LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂ := by
    rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨LinearMap.mem_ker.mpr hy₁, LinearMap.mem_ker.mpr hy₂⟩
  exact hwY (hyspan hw_y)

private lemma l1i_dual_centre {χ : Module.Dual (ZMod p) M} {η : M ≃ₗ[ZMod p] M} {cη : M}
    {φη : Module.Dual (ZMod p) M} (hηh : IsHomologyWith τ η cη φη) (hτne1 : τ ≠ 1)
    (ha_ne : (τ - 1 : ZMod p) ≠ 0) (hχcη : χ cη = 0) (hχw : χ w = 0)
    (hχy : χ y = τ - 1) (hcη_span : cη ∈ Submodule.span (ZMod p) ({y, w + y} : Set M)) :
    ∃ t₀ : ZMod p, t₀ • w = cη ∧ t₀ ≠ 0 ∧ φη w = t₀⁻¹ * (τ - 1) := by
  rw [Submodule.mem_span_pair] at hcη_span
  obtain ⟨s, t, hst⟩ := hcη_span
  have hχc : χ (s • y + t • (w + y)) = 0 := by rw [hst]; exact hχcη
  have hμ : (s + t) * (τ - 1) = 0 := by
    have h := hχc
    rw [map_add, map_smul, map_smul, map_add, hχw, hχy] at h
    simpa [smul_eq_mul, add_mul] using h
  have hst0 : s + t = 0 := (mul_eq_zero.mp hμ).resolve_right ha_ne
  have hcη_eq : t • w = cη := by
    rw [← hst]
    calc t • w = (s + t) • y + t • w := by rw [hst0, zero_smul, zero_add]
      _ = s • y + t • (w + y) := by module
  have ht_ne : t ≠ 0 := by
    intro ht
    have : cη = 0 := by rw [← hcη_eq, ht, zero_smul]
    exact hηh.centre_ne_zero hτne1 this
  have hφη_w : φη w = t⁻¹ * (τ - 1) := by
    have h := hηh.1
    rw [← hcη_eq, map_smul] at h
    have h1 : t * φη w = τ - 1 := by simpa [smul_eq_mul] using h
    calc φη w = t⁻¹ * (t * φη w) := by rw [← mul_assoc, inv_mul_cancel₀ ht_ne, one_mul]
      _ = t⁻¹ * (τ - 1) := by rw [h1]
  exact ⟨t, hcη_eq, ht_ne, hφη_w⟩

private lemma l1i_off_line (hτne1 : τ ≠ 1) (h₁ : IsHomologyWith τ α c₁ φ₁)
    (h12 : φ₁ c₂ ≠ 0) (h21 : φ₂ c₁ ≠ 0)
    (hc₂ : c₂ ∉ Submodule.span (ZMod p) ({c₁} : Set M))
    (hwY : w ∉ LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂) :
    (φ₁ w ≠ 0 ∧ c₁ ∉ Submodule.span (ZMod p) ({w} : Set M)) ∨
      (φ₂ w ≠ 0 ∧ c₂ ∉ Submodule.span (ZMod p) ({w} : Set M)) := by
  by_cases h1w : φ₁ w = 0
  · right
    constructor
    · intro h2w
      exact hwY ⟨LinearMap.mem_ker.mpr h1w, LinearMap.mem_ker.mpr h2w⟩
    · intro hc2
      rw [Submodule.mem_span_singleton] at hc2
      obtain ⟨ν, hν⟩ := hc2
      exact h12 (by rw [← hν, map_smul, h1w, smul_zero])
  · by_cases hc1 : c₁ ∈ Submodule.span (ZMod p) ({w} : Set M)
    · right
      constructor
      · intro h2w
        rw [Submodule.mem_span_singleton] at hc1
        obtain ⟨μ, hμ⟩ := hc1
        apply h21
        rw [← hμ, map_smul, h2w, smul_zero]
      · intro hc2
        apply hc₂
        rw [Submodule.mem_span_singleton] at hc1 hc2 ⊢
        obtain ⟨μ, hμ⟩ := hc1
        obtain ⟨ν, hν⟩ := hc2
        have hμ_ne : μ ≠ 0 := by
          intro h0
          exact h₁.centre_ne_zero hτne1 (by rw [← hμ, h0, zero_smul])
        refine ⟨ν * μ⁻¹, ?_⟩
        calc (ν * μ⁻¹) • c₁ = (ν * μ⁻¹) • (μ • w) := by rw [← hμ]
          _ = ν • w := by rw [smul_smul, mul_assoc ν μ⁻¹ μ, inv_mul_cancel₀ hμ_ne, mul_one]
          _ = c₂ := by rw [hν]
    · left
      exact ⟨h1w, hc1⟩

private lemma l1i_key_transvection (htv : QTwoLin.TransvectionFree R)
    {a' : M ≃ₗ[ZMod p] M} {c' : M} {φ' : Module.Dual (ZMod p) M}
    (hγR : γ ∈ R) (ha'R : a' ∈ R) (hγh : IsHomologyWith τ γ (w + y) φ)
    (h'a : IsHomologyWith τ a' c' φ') (hτne1 : τ ≠ 1) (hs : φ c' = 0)
    (hφ'w : φ' w ≠ 0) (hφ'y : φ' y = 0) : False := by
  have hφ'cγ : φ' (w + y) = φ' w := by rw [map_add, hφ'y, add_zero]
  have hlin : QTwoLin.IsTransvectionLin (γ * a' * γ⁻¹ * a'⁻¹) :=
    isTransvectionLin_commutator_of_apply_eq_zero hγh h'a hτne1 hs (by rw [hφ'cγ]; exact hφ'w)
  have hmemR : γ * a' * γ⁻¹ * a'⁻¹ ∈ R :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hγR ha'R) (Subgroup.inv_mem _ hγR)) (Subgroup.inv_mem _ ha'R)
  exact htv _ hmemR hlin

private lemma l1i_nc {η : M ≃ₗ[ZMod p] M} {cη : M} {φη : Module.Dual (ZMod p) M}
    {a' : M ≃ₗ[ZMod p] M} {c' : M} {φ' : Module.Dual (ZMod p) M} {t₀ : ZMod p} {s : ZMod p}
    (hτne1 : τ ≠ 1) (ha_ne : (τ - 1 : ZMod p) ≠ 0) (ht_ne : t₀ ≠ 0) (hs_ne : s ≠ 0)
    (hγh : IsHomologyWith τ γ (w + y) φ) (hηh : IsHomologyWith τ η cη φη)
    (h'a : IsHomologyWith τ a' c' φ') (hφ'w : φ' w ≠ 0)
    (hφη_cγ : φη (w + y) = t₀⁻¹ * (τ - 1)) (hφη_c' : φη c' = s * (t₀⁻¹ * (τ - 1)))
    (hφ'_cγ : φ' (w + y) = φ' w) (ht₀ : t₀ • w = cη)
    (hcγ_not_W : w + y ∉ Submodule.span (ZMod p) ({c₁, c₂} : Set M))
    (hc'notspan : c' ∉ Submodule.span (ZMod p) ({w} : Set M))
    (hc'W : c' ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M))
    (hw : w ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M)) :
    η * γ ≠ γ * η ∧ η * a' ≠ a' * η ∧ a' * γ ≠ γ * a' := by
  have hspan_w_le_W : Submodule.span (ZMod p) ({w} : Set M) ≤
      Submodule.span (ZMod p) ({c₁, c₂} : Set M) := by
    rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  refine ⟨?_, ?_, ?_⟩
  · refine not_commute_of_apply_ne_zero hηh hγh hτne1 ?_ ?_
    · rw [hφη_cγ]; exact mul_ne_zero (inv_ne_zero ht_ne) ha_ne
    · intro hmem
      rw [← ht₀] at hmem
      apply hcγ_not_W
      rw [Submodule.mem_span_singleton] at hmem
      obtain ⟨a, ha⟩ := hmem
      exact hspan_w_le_W (Submodule.mem_span_singleton.mpr ⟨a * t₀, by rw [← smul_smul, ha]⟩)
  · refine not_commute_of_apply_ne_zero hηh h'a hτne1 ?_ ?_
    · rw [hφη_c']; exact mul_ne_zero hs_ne (mul_ne_zero (inv_ne_zero ht_ne) ha_ne)
    · intro hmem
      rw [← ht₀] at hmem
      apply hc'notspan
      rw [Submodule.mem_span_singleton] at hmem
      obtain ⟨a, ha⟩ := hmem
      exact Submodule.mem_span_singleton.mpr ⟨a * t₀, by rw [← smul_smul, ha]⟩
  · refine not_commute_of_apply_ne_zero h'a hγh hτne1 ?_ ?_
    · rw [hφ'_cγ]; exact hφ'w
    · intro hmem
      apply hcγ_not_W
      exact Submodule.span_le.mpr (by
        intro z hz; simp only [Set.mem_singleton_iff] at hz; subst hz; exact hc'W) hmem

private lemma l1i_q_contra (htv : QTwoLin.TransvectionFree R) (hτ : 4 ≤ orderOf τ)
    (hτo : orderOf τ = 4 ∨ orderOf τ = 5)
    {η : M ≃ₗ[ZMod p] M} {cη : M} {φη : Module.Dual (ZMod p) M}
    {a' : M ≃ₗ[ZMod p] M} {c' : M} {φ' : Module.Dual (ZMod p) M} {s : ZMod p}
    {t₀ : ZMod p} (ht_ne : t₀ ≠ 0)
    (hηR : η ∈ R) (hγR : γ ∈ R) (ha'R : a' ∈ R) (hηh : IsHomologyWith τ η cη φη)
    (hγh : IsHomologyWith τ γ (w + y) φ) (h'a : IsHomologyWith τ a' c' φ')
    (hηγ : η * γ ≠ γ * η) (hηa : η * a' ≠ a' * η) (haγ : a' * γ ≠ γ * a')
    (hφη_c' : φη c' = s * (t₀⁻¹ * (τ - 1))) (hφ_c' : φ c' = s * φ w)
    (hφη_cγ : φη (w + y) = t₀⁻¹ * (τ - 1)) (hφ_cη : φ cη = t₀ * φ w)
    (hφ'_cη : φ' cη = t₀ * φ' w) (hφ'_cγ : φ' (w + y) = φ' w) : False := by
  have hx := l1i_mem_Q_of_not_commute htv hτ hηR ha'R hηh h'a hηa
  have hy := l1i_mem_Q_of_not_commute htv hτ hηR hγR hηh hγh hηγ
  have hz := l1i_mem_Q_of_not_commute htv hτ ha'R hγR h'a hγh haγ
  have hxy : (φ' (w + y) * φ c') * (τ - 1) ^ 2 =
      (φη c' * φ' cη) * (φη (w + y) * φ cη) := by
    rw [hφ'_cγ, hφ_c', hφη_c', hφη_cγ, hφ_cη, hφ'_cη]
    field_simp
  rcases hz with hz | hz
  · exact (mul_div_not_mem hτo hx hy hxy).1 hz
  · exact (mul_div_not_mem hτo hx hy hxy).2 hz

private lemma l1i_cocycle (htv : QTwoLin.TransvectionFree R) (hτ : 4 ≤ orderOf τ)
    (hτo : orderOf τ = 4 ∨ orderOf τ = 5)
    {η : M ≃ₗ[ZMod p] M} {cη : M} {φη : Module.Dual (ZMod p) M}
    {a' : M ≃ₗ[ZMod p] M} {c' : M} {φ' : Module.Dual (ZMod p) M} {t₀ : ZMod p}
    {χ : Module.Dual (ZMod p) M}
    (hτne1 : τ ≠ 1) (ha_ne : (τ - 1 : ZMod p) ≠ 0) (hφw : φ w ≠ 0) (hφ'w : φ' w ≠ 0)
    (hφ'y : φ' y = 0) (hγh : IsHomologyWith τ γ (w + y) φ) (hγR : γ ∈ R)
    (hηh : IsHomologyWith τ η cη φη) (hηR : η ∈ R) (h'a : IsHomologyWith τ a' c' φ')
    (ha'R : a' ∈ R) (ht₀ : t₀ • w = cη) (ht_ne : t₀ ≠ 0)
    (hφη_w : φη w = t₀⁻¹ * (τ - 1)) (hφηy : φη y = 0) (hs : φ c' ≠ 0)
    (hχ_on_W : ∀ v ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M), χ v = 0)
    (hφη_kill : ∀ v, χ v = 0 → φ v = 0 → φη v = 0)
    (hc'W : c' ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M))
    (hw : w ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M))
    (hcγ_not_W : w + y ∉ Submodule.span (ZMod p) ({c₁, c₂} : Set M))
    (hc'notspan : c' ∉ Submodule.span (ZMod p) ({w} : Set M)) : False := by
  let s : ZMod p := φ c' * (φ w)⁻¹
  let e : M := c' - s • w
  have hs_ne : s ≠ 0 := by
    intro h0
    exact hs (by
      have h2 : φ c' = s * φ w := by dsimp only [s]; rw [mul_assoc, inv_mul_cancel₀ hφw, mul_one]
      rw [h0, zero_mul] at h2; exact h2)
  have hc'_eq : c' = s • w + e := by simp [e]
  have he_φ : φ e = 0 := by
    have h2 : φ c' = s * φ w := by dsimp only [s]; rw [mul_assoc, inv_mul_cancel₀ hφw, mul_one]
    dsimp only [e]
    rw [map_sub, map_smul, h2, smul_eq_mul, sub_self]
  have he_χ : χ e = 0 := by
    apply hχ_on_W
    exact Submodule.sub_mem _ hc'W (Submodule.smul_mem _ _ hw)
  have hφηe : φη e = 0 := hφη_kill e he_χ he_φ
  have hφη_c' : φη c' = s * (t₀⁻¹ * (τ - 1)) := by
    rw [hc'_eq, map_add, map_smul, hφηe, hφη_w, smul_eq_mul, add_zero]
  have hφ_c' : φ c' = s * φ w := by
    rw [hc'_eq, map_add, map_smul, he_φ, add_zero, smul_eq_mul]
  have hφη_cγ : φη (w + y) = t₀⁻¹ * (τ - 1) := by rw [map_add, hφη_w, hφηy, add_zero]
  have hφ_cη : φ cη = t₀ * φ w := by rw [← ht₀, map_smul, smul_eq_mul]
  have hφ'_cη : φ' cη = t₀ * φ' w := by rw [← ht₀, map_smul, smul_eq_mul]
  have hφ'_cγ : φ' (w + y) = φ' w := by rw [map_add, hφ'y, add_zero]
  obtain ⟨hηγ, hηa, haγ⟩ := l1i_nc (s := s) hτne1 ha_ne ht_ne hs_ne hγh hηh h'a hφ'w
    hφη_cγ hφη_c' hφ'_cγ ht₀ hcγ_not_W hc'notspan hc'W hw
  exact l1i_q_contra htv hτ hτo ht_ne hηR hγR ha'R hηh hγh h'a hηγ hηa haγ
    hφη_c' hφ_c' hφη_cγ hφ_cη hφ'_cη hφ'_cγ

private lemma l1i_key (htv : QTwoLin.TransvectionFree R) (hτ : 4 ≤ orderOf τ)
    (hτo : orderOf τ = 4 ∨ orderOf τ = 5)
    {η : M ≃ₗ[ZMod p] M} {cη : M} {φη : Module.Dual (ZMod p) M}
    {a' : M ≃ₗ[ZMod p] M} {c' : M} {φ' : Module.Dual (ZMod p) M} {t₀ : ZMod p}
    {χ : Module.Dual (ZMod p) M} (hτne1 : τ ≠ 1) (ha_ne : (τ - 1 : ZMod p) ≠ 0)
    (hγh : IsHomologyWith τ γ (w + y) φ) (hγR : γ ∈ R) (hηh : IsHomologyWith τ η cη φη)
    (hηR : η ∈ R) (h'a : IsHomologyWith τ a' c' φ') (ha'R : a' ∈ R)
    (ht₀ : t₀ • w = cη) (ht_ne : t₀ ≠ 0) (hφη_w : φη w = t₀⁻¹ * (τ - 1))
    (hφηy : φη y = 0) (hφη_kill : ∀ v, χ v = 0 → φ v = 0 → φη v = 0)
    (hχ_on_W : ∀ v ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M), χ v = 0)
    (hw : w ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M))
    (hcγ_not_W : w + y ∉ Submodule.span (ZMod p) ({c₁, c₂} : Set M)) (hφw : φ w ≠ 0)
    (hc'W : c' ∈ Submodule.span (ZMod p) ({c₁, c₂} : Set M))
    (hc'notspan : c' ∉ Submodule.span (ZMod p) ({w} : Set M)) (hφ'w : φ' w ≠ 0)
    (hφ'y : φ' y = 0) : False := by
  by_cases hs : φ c' = 0
  · exact l1i_key_transvection htv hγR ha'R hγh h'a hτne1 hs hφ'w hφ'y
  · exact l1i_cocycle htv hτ hτo hτne1 ha_ne hφw hφ'w hφ'y hγh hγR hηh hηR h'a ha'R ht₀
      ht_ne hφη_w hφηy hs hχ_on_W hφη_kill hc'W hw hcγ_not_W hc'notspan

theorem false_of_mixed_centre (htv : QTwoLin.TransvectionFree R)
    (hτ : 4 ≤ orderOf τ) {θ : M ≃ₗ[ZMod p] M} {χ : Module.Dual (ZMod p) M} (hα : α ∈ R)
    (hβ : β ∈ R) (hθ : θ ∈ R) (hγ : γ ∈ R) (h₁ : IsHomologyWith τ α c₁ φ₁)
    (h₂ : IsHomologyWith τ β c₂ φ₂) (hθh : IsHomologyWith τ θ y χ)
    (hγh : IsHomologyWith τ γ (w + y) φ) (hcomm : α * β ≠ β * α) (hy₁ : φ₁ y = 0)
    (hy₂ : φ₂ y = 0) (hχ₁ : χ c₁ = 0) (hχ₂ : χ c₂ = 0)
    (hw : w ∈ Submodule.span (ZMod p) {c₁, c₂}) (hφw : φ w ≠ 0) (hφy : φ y ≠ 0) : False := by
  obtain ⟨hτne1, ha_ne⟩ := four_basic hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have hle : orderOf τ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨hc₂, h12, h21, hqab⟩ := linked_of_not_commute htv hα hβ h₁ h₂ hτ2 hcomm
  have hcompl : IsCompl (Submodule.span (ZMod p) ({c₁, c₂} : Set M))
      (LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂) := isCompl_span_ker_inf_ker h₁ h₂ hqab
  have hwY := l1i_hwY hcompl hw hφw
  have hχ_on_W := l1i_chi_on_W (χ := χ) hχ₁ hχ₂
  have hχw : χ w = 0 := hχ_on_W w hw
  have hχwy : χ (w + y) = τ - 1 := by rw [map_add, hχw, hθh.1, zero_add]
  have hcγ_not_span := l1i_ne_y_span hwY hy₁ hy₂
  have hθγ_comm : θ * γ ≠ γ * θ :=
    not_commute_of_apply_ne_zero hθh hγh hτne1 (by rw [hχwy]; exact ha_ne) hcγ_not_span
  obtain ⟨η, hηmem, cη, φη, hηh, hcη_span, hχcη, hφηy, hφη_kill⟩ :=
    exists_dual_homology_of_not_commute htv hθ hγ hθh hγh hτ hθγ_comm
  have hηR : η ∈ R := by
    refine (Subgroup.closure_le R).mpr ?_ hηmem
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hθ
    · exact hγ
  obtain ⟨t₀, ht₀, ht_ne, hφη_w⟩ := l1i_dual_centre hηh hτne1 ha_ne hχcη hχw hθh.1 hcη_span
  have hcγ_not_W : w + y ∉ Submodule.span (ZMod p) ({c₁, c₂} : Set M) :=
    l1i_wy_not_mem_W hcompl hw hφy hy₁ hy₂
  have hoff := l1i_off_line hτne1 h₁ h12 h21 hc₂ hwY
  have hτo : orderOf τ = 4 ∨ orderOf τ = 5 :=
    orderOf_eq_four_or_five_of_not_commute htv hα hβ h₁ h₂ hτ hcomm
  rcases hoff with ⟨h1w, hc1not⟩ | ⟨h2w, hc2not⟩
  · exact l1i_key htv hτ hτo hτne1 ha_ne hγh hγ hηh hηR h₁ hα ht₀ ht_ne hφη_w hφηy
      hφη_kill hχ_on_W hw hcγ_not_W hφw (Submodule.subset_span (Set.mem_insert _ _)) hc1not
      h1w hy₁
  · exact l1i_key htv hτ hτo hτne1 ha_ne hγh hγ hηh hηR h₂ hβ ht₀ ht_ne hφη_w hφηy
      hφη_kill hχ_on_W hw hcγ_not_W hφw (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
      hc2not h2w hy₂

end CFSG.StandardType.ZS

end
