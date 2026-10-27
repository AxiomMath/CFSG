module

public import CFSG.RankThree.GF2n.Stroth80.Sec26b
public import CFSG.RankThree.GF2n.Stroth80.FieldAut

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_conj_iff {Z : Subgroup G} {g x : G} :
    x ∈ Subgroup.normalizer ((conjSubgroup g Z : Subgroup G) : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.normalizer (Z : Set G) := by
  have h := Subgroup.map_normalizer_eq_of_bijective (f := (MulAut.conj g).toMonoidHom) Z
    (MulAut.conj g).bijective
  have e : Subgroup.normalizer ((conjSubgroup g Z : Subgroup G) : Set G) =
      conjSubgroup g (Subgroup.normalizer (Z : Set G)) := h.symm
  rw [e, mem_conjSubgroup]

theorem exists_centralizes_of_fixes {M Q Z : Subgroup G} (hh : StrothHyp M Q Z) {g t : G}
    (htB : t ∈ conjSubgroup g Z) (ht1 : t ≠ 1)
    (hZN : ∀ z ∈ Z, z ∈ Subgroup.normalizer ((conjSubgroup g Z : Subgroup G) : Set G))
    (hZt : ∀ z ∈ Z, z * t = t * z) :
    ∃ z ∈ Z, z ≠ 1 ∧ ∀ b ∈ conjSubgroup g Z, z * b = b * z := by
  classical
  obtain ⟨K, _, _, _, γ, M₀, h⟩ := stroth_globalModelData hh
  have h' := h.conj g
  set B := conjSubgroup g Z with hB
  set γ' : G → K := fun x => γ (g⁻¹ * x * g) with hγ'
  have hreg : Tim79.GammaReg (conjSubgroup g Q) B γ' := h'.reg
  have hγ0 : γ' 1 = 0 := hreg.one
  let Vd : G → (K ≃+* K) → K → Prop := fun z σ a => ∀ b ∈ B, γ' (z * b * z⁻¹) = a * σ (γ' b)
  have hdata : ∀ z ∈ Z, ∃ (σ : K ≃+* K) (a : K), Vd z σ a := by
    intro z hz
    have hzM : z ∈ conjSubgroup g M := by
      rw [mem_conjSubgroup, ← hh.normalizer_Z.1, ← mem_normalizer_conj_iff]
      exact hZN z hz
    obtain ⟨σ, a, T, -, -, hγ, -⟩ := h'.act z hzM
    exact ⟨σ, a, hγ⟩
  have hzB : ∀ z ∈ Z, ∀ b ∈ B, z * b * z⁻¹ ∈ B := fun z hz b hb =>
    (Subgroup.mem_normalizer_iff.mp (hZN z hz) b).mp hb
  have hne0 : ∀ z ∈ Z, ∀ σ a, Vd z σ a → a ≠ 0 := by
    intro z hz σ a hV ha
    obtain ⟨b₁, hb₁, hγb₁⟩ := hreg.surj 1
    have h1 := hV b₁ hb₁
    rw [ha, zero_mul] at h1
    have h2 : z * b₁ * z⁻¹ = 1 := hreg.inj _ (hzB z hz b₁ hb₁) h1
    have h3 : b₁ = 1 := by
      have := congrArg (fun y => z⁻¹ * y * z) h2
      simpa [mul_assoc] using this
    rw [h3, hγ0] at hγb₁
    exact zero_ne_one hγb₁
  have huniq : ∀ z ∈ Z, ∀ σ σ' a a', Vd z σ a → Vd z σ' a' → σ = σ' ∧ a = a' := by
    intro z hz σ σ' a a' hV hV'
    obtain ⟨b₁, hb₁, hγb₁⟩ := hreg.surj 1
    have ha : a = a' := by
      have := (hV b₁ hb₁).symm.trans (hV' b₁ hb₁)
      simpa [hγb₁] using this
    subst ha
    refine ⟨RingEquiv.ext fun s => ?_, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hreg.surj s
    have := (hV b hb).symm.trans (hV' b hb)
    exact mul_left_cancel₀ (hne0 z hz σ a hV) this
  have hcomp : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, ∀ σ₁ σ₂ a₁ a₂, Vd z₁ σ₁ a₁ → Vd z₂ σ₂ a₂ →
      Vd (z₁ * z₂) (σ₂.trans σ₁) (a₁ * σ₁ a₂) := by
    intro z₁ hz₁ z₂ hz₂ σ₁ σ₂ a₁ a₂ hV₁ hV₂ b hb
    have e : z₁ * z₂ * b * (z₁ * z₂)⁻¹ = z₁ * (z₂ * b * z₂⁻¹) * z₁⁻¹ := by group
    rw [e, hV₁ _ (hzB z₂ hz₂ b hb), hV₂ b hb]
    simp [map_mul]
    ring
  have hγt : γ' t ≠ 0 := fun h0 => ht1 (hreg.inj t htB h0)
  have hfix : ∀ z ∈ Z, ∀ σ a, Vd z σ a → a * σ (γ' t) = γ' t := by
    intro z hz σ a hV
    have h1 := hV t htB
    have e : z * t * z⁻¹ = t := by rw [hZt z hz]; group
    rw [e] at h1
    exact h1.symm
  have hcent : ∀ z ∈ Z, ∀ a, Vd z (RingEquiv.refl K) a → ∀ b ∈ B, z * b = b * z := by
    intro z hz a hV b hb
    have ha : a = 1 := by
      have := hfix z hz _ _ hV
      simp only [RingEquiv.refl_apply] at this
      exact mul_right_cancel₀ hγt (by rw [this, one_mul])
    subst ha
    have h1 : γ' (z * b * z⁻¹) = γ' b := by simpa using hV b hb
    have h2 : z * b * z⁻¹ * b⁻¹ = 1 := by
      refine hreg.inj _ (B.mul_mem (hzB z hz b hb) (B.inv_mem hb)) ?_
      have := hreg.add (z * b * z⁻¹ * b⁻¹) (B.mul_mem (hzB z hz b hb) (B.inv_mem hb)) b hb
      rw [show z * b * z⁻¹ * b⁻¹ * b = z * b * z⁻¹ by group, h1] at this
      linear_combination (-1 : K) * this
    have h3 : z * b * z⁻¹ = b := mul_inv_eq_one.mp h2
    calc z * b = z * b * z⁻¹ * z := by group
      _ = b * z := by rw [h3]
  have hsq : ∀ z ∈ Z, z * z = 1 := fun z hz => by
    rw [← pow_two]; exact hh.isElemAbelian_Z.2 z hz
  have hZ2 : ∃ z₁ ∈ Z, z₁ ≠ 1 ∧ ∃ z₂ ∈ Z, z₂ ≠ 1 ∧ z₂ ≠ z₁ := by
    have h4 := hh.q4
    by_contra hcon
    push Not at hcon
    have hz₁ : ∃ z₁ ∈ Z, z₁ ≠ 1 := by
      by_contra h0
      push Not at h0
      have : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr h0
      rw [this, Subgroup.card_bot] at h4
      omega
    obtain ⟨z₁, hz₁, hz₁1⟩ := hz₁
    have hsub : (Z : Set G) ⊆ {1, z₁} := by
      intro z hz
      by_cases hz1 : z = 1
      · simp [hz1]
      · by_cases hzz : z = z₁
        · simp [hzz]
        · exact absurd (hcon z₁ hz₁ hz₁1 z hz hz1) hzz
    have hc : (Z : Set G).ncard ≤ ({1, z₁} : Set G).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, z₁} : Set G).ncard ≤ 2 := by
      have := Set.ncard_insert_le (1 : G) ({z₁} : Set G)
      rw [Set.ncard_singleton] at this
      exact this
    have h5 : Nat.card Z = (Z : Set G).ncard := Nat.card_coe_set_eq (Z : Set G)
    omega
  obtain ⟨z₁, hz₁, hz₁1, z₂, hz₂, hz₂1, hz₂₁⟩ := hZ2
  have hz₃ : z₁ * z₂ ∈ Z := Z.mul_mem hz₁ hz₂
  have hz₃1 : z₁ * z₂ ≠ 1 := by
    intro h1
    apply hz₂₁
    have h2 : z₂ = z₁⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right (hsq z₁ hz₁)
  obtain ⟨σ₁, a₁, hV₁⟩ := hdata z₁ hz₁
  obtain ⟨σ₂, a₂, hV₂⟩ := hdata z₂ hz₂
  obtain ⟨σ₃, a₃, hV₃⟩ := hdata _ hz₃
  have hone : Vd 1 (RingEquiv.refl K) 1 := fun b hb => by simp
  have hsqσ : ∀ z ∈ Z, ∀ σ a, Vd z σ a → σ * σ = 1 := by
    intro z hz σ a hV
    have h1 := hcomp z hz z hz σ σ a a hV hV
    rw [hsq z hz] at h1
    have := (huniq 1 Z.one_mem _ _ _ _ h1 hone).1
    exact RingEquiv.ext fun x => congrArg (fun e => e x) this
  have hσ₃ : σ₃ = σ₂.trans σ₁ :=
    (huniq _ hz₃ _ _ _ _ hV₃ (hcomp z₁ hz₁ z₂ hz₂ σ₁ σ₂ a₁ a₂ hV₁ hV₂)).1
  by_cases h1 : σ₁ = 1
  · exact ⟨z₁, hz₁, hz₁1, hcent z₁ hz₁ a₁ (by rw [h1] at hV₁; exact hV₁)⟩
  by_cases h2 : σ₂ = 1
  · exact ⟨z₂, hz₂, hz₂1, hcent z₂ hz₂ a₂ (by rw [h2] at hV₂; exact hV₂)⟩
  by_cases h3 : σ₃ = 1
  · exact ⟨z₁ * z₂, hz₃, hz₃1, hcent _ hz₃ a₃ (by rw [h3] at hV₃; exact hV₃)⟩
  exfalso
  have e12 : σ₁ = σ₂ := ringEquiv_eq_of_sq_eq_one _ _ (hsqσ z₁ hz₁ σ₁ a₁ hV₁)
    (hsqσ z₂ hz₂ σ₂ a₂ hV₂) h1 h2
  have e13 : σ₃ * σ₃ = 1 := hsqσ _ hz₃ σ₃ a₃ hV₃
  apply h3
  rw [hσ₃, ← e12]
  exact RingEquiv.ext fun x => congrArg (fun e => e x) (hsqσ z₁ hz₁ σ₁ a₁ hV₁)

theorem stroth_2_6 {M Q Z : Subgroup G} (hh : StrothHyp M Q Z) {t : G} (htQ : t ∈ Q)
    (htZ : t ∉ Z) (hconj : ∃ (g z : G), z ∈ Z ∧ t = g * z * g⁻¹) :
    ∃ g : G, conjSubgroup g Z ≤ Q ∧ t ∈ conjSubgroup g Z := by
  obtain ⟨g, z, hz, rfl⟩ := hconj
  have htB : g * z * g⁻¹ ∈ conjSubgroup g Z := by
    rw [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact hz
  have ht1 : g * z * g⁻¹ ≠ 1 := fun h1 => htZ (h1 ▸ Z.one_mem)
  have hTIB : IsTI (conjSubgroup g Z) := isTI_conjSubgroup hh.ti g
  have hZt : ∀ z' ∈ Z, z' * (g * z * g⁻¹) = (g * z * g⁻¹) * z' := fun z' hz' =>
    hh.toHyp79.V_central hz' htQ
  have hZN : ∀ z' ∈ Z, z' ∈ Subgroup.normalizer ((conjSubgroup g Z : Subgroup G) : Set G) :=
    fun z' hz' => Tim77.mem_normalizer_of_commute_of_isTI hTIB htB ht1 (hZt z' hz')
  obtain ⟨z₀, hz₀, hz₀1, hz₀c⟩ := exists_centralizes_of_fixes hh htB ht1 hZN hZt
  have hBM : conjSubgroup g Z ≤ M := by
    intro b hb
    rw [← hh.normalizer_Z.1]
    exact Tim77.mem_normalizer_of_commute_of_isTI hh.ti hz₀ hz₀1 (hz₀c b hb).symm
  obtain ⟨K, _, _, _, γ, M₀, h⟩ := stroth_globalModelData hh
  exact ⟨g, stroth_2_6_of_le_M hh h htQ htB htZ hBM, htB⟩

end CFSG.RankThree.GF2n.Stroth80
