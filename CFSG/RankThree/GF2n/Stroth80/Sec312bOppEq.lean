module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClQuad
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClCaseBase
public import CFSG.RankThree.GF2n.Stroth80.Sec311SpTrans

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

private theorem comm_orth_le_orth {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : ⁅orthSubgroup Q, orthSubgroup Q⁆ ≤ orthSubgroup Q := by
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  rw [commutatorElement_def]
  exact (orthSubgroup Q).mul_mem ((orthSubgroup Q).mul_mem ((orthSubgroup Q).mul_mem hg hh)
    ((orthSubgroup Q).inv_mem hg)) ((orthSubgroup Q).inv_mem hh)

private theorem exists_form_eq_one_of_ne {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {F : LinearMap.BilinForm K V} {e e' : V} (h : F e e' ≠ 0) : ∃ f : V, F e f = 1 :=
  ⟨(F e e')⁻¹ • e', by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ h]⟩

private theorem qf_transvection_eq {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {F : LinearMap.BilinForm K V}
    {Q : QuadraticForm K V} (hQ : Q.polarBilin = F) (x v : V) :
    Q (v + F v x • x) = Q v + (F v x) ^ 2 * (Q x + 1) := by
  rw [qf_add hQ, qf_smul, map_smul, smul_eq_mul]
  ring

private theorem comp_polarBilin_of_isom {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {F : LinearMap.BilinForm K V} {Q : QuadraticForm K V} (hQ : Q.polarBilin = F)
    {t : V ≃ₗ[K] V} (ht : t ∈ sympSubgroup F) :
    (Q.comp (t : V →ₗ[K] V)).polarBilin = F := by
  have hiso : IsIsom F t := ht
  rw [QuadraticMap.polarBilin_comp, hQ]
  exact LinearMap.ext₂ fun v w => hiso v w

private theorem exists_perp_form_ne_zero {K V : Type} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] {F : LinearMap.BilinForm K V} (hnd : F.Nondegenerate) (halt : F.IsAlt)
    {e x : V} (hxc : ∀ c : K, x ≠ c • e) : ∃ v : V, F v e = 0 ∧ F v x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := perp_perp hnd halt e x fun v hv => (form_comm halt x v).trans (hcon v hv)
  exact hxc c hc

private theorem quad_eq_one_of_normalizes {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {F : LinearMap.BilinForm K V}
    (hnd : F.Nondegenerate) (halt : F.IsAlt) (hdim : 3 ≤ Module.finrank K V) {e f : V}
    (hef : F e f = 1) {Q : QuadraticForm K V} (hQ : Q.polarBilin = F)
    {A : Subgroup (V ≃ₗ[K] V)} (hD : (A : Set (V ≃ₗ[K] V)) ⊆ pointRad F e)
    (hfull : ElationFull F (A : Set (V ≃ₗ[K] V)) e)
    (hA : ∀ g ∈ A, ∀ v, Q (g v) = Q v) {x : V} (hxc : ∀ c : K, x ≠ c • e)
    (hn : ∀ g ∈ A, symTransvection halt x 1 * g * (symTransvection halt x 1)⁻¹ ∈ A) :
    Q x = 1 := by
  obtain ⟨Q', hQ'pol, hQ'app⟩ : ∃ Q' : QuadraticForm K V, Q'.polarBilin = F ∧
      ∀ v, Q' v = Q (symTransvection halt x 1 v) :=
    ⟨Q.comp (symTransvection halt x 1 : V →ₗ[K] V),
      comp_polarBilin_of_isom hQ (symTransvection_mem halt x 1), fun v => rfl⟩
  have hinv : ∀ g ∈ A, ∀ v, Q' (g v) = Q' v := by
    intro g hg v
    have h1 := hA _ (hn g hg) (symTransvection halt x 1 v)
    have h2 : (symTransvection halt x 1 * g * (symTransvection halt x 1)⁻¹)
        (symTransvection halt x 1 v) = symTransvection halt x 1 (g v) := by
      simp [LinearEquiv.mul_apply]
    rw [h2] at h1
    rw [hQ'app, hQ'app]
    exact h1
  obtain ⟨c, hc⟩ := quadForm_eq_of_elationFull hnd halt hdim hef hD hfull hQ hQ'pol hA hinv
  have hQt : ∀ v, Q' v = Q v + (F v x) ^ 2 * (Q x + 1) := by
    intro v
    rw [hQ'app, symTransvection_apply, one_mul, qf_transvection_eq hQ]
  have key : ∀ v, (F v x) ^ 2 * (Q x + 1) = c * (F v e) ^ 2 := fun v => by
    linear_combination hc v - hQt v
  obtain ⟨v, hv1, hv2⟩ := exists_perp_form_ne_zero hnd halt hxc
  have h0 : (F v x) ^ 2 * (Q x + 1) = 0 := by
    rw [key v, hv1]
    ring
  have h1 : Q x + 1 = 0 := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hv2)
  linear_combination h1 - (two_eq_zero_K (K := K))

theorem opp_eq
    {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (F : LinearMap.BilinForm K V) (hnd : F.Nondegenerate) (halt : F.IsAlt) (h4 : 4 ≤ Nat.card K)
    (hdim : 4 ≤ Module.finrank K V)
    (e₁ e₂ : V) (h12 : F e₁ e₂ ≠ 0)
    (A₁ A₂ H₀ : Subgroup (V ≃ₗ[K] V)) (hH₀ : H₀ ≤ sympSubgroup F)
    (hA₁ : A₁ ≤ H₀ ⊓ pointRadSubgroup F e₁) (hA₂ : A₂ ≤ H₀ ⊓ pointRadSubgroup F e₂)
    (hf₁ : ElationFull F (A₁ : Set _) e₁) (hf₂ : ElationFull F (A₂ : Set _) e₂)
    (hH₀cases : H₀ = sympSubgroup F ∨ ∃ Q₀ : QuadraticForm K V, Q₀.polarBilin = F ∧
      H₀ = ⁅orthSubgroup Q₀, orthSubgroup Q₀⁆)
    (hH₁cases : A₁ ⊔ A₂ = sympSubgroup F ∨ ∃ Q : QuadraticForm K V, Q.polarBilin = F ∧
      A₁ ⊔ A₂ = ⁅orthSubgroup Q, orthSubgroup Q⁆)
    (hSinv : H₀ = sympSubgroup F → ∀ x : V, F x e₁ = 0 → ∀ g ∈ A₁,
      symTransvection halt x 1 * g * (symTransvection halt x 1)⁻¹ ∈ A₁) :
    A₁ ⊔ A₂ = H₀ := by
  have hd3 : 3 ≤ Module.finrank K V := by omega
  have hA₁H : A₁ ≤ H₀ := fun g hg => (Subgroup.mem_inf.mp (hA₁ hg)).1
  have hA₂H : A₂ ≤ H₀ := fun g hg => (Subgroup.mem_inf.mp (hA₂ hg)).1
  have hA₁P : A₁ ≤ pointRadSubgroup F e₁ := fun g hg => (Subgroup.mem_inf.mp (hA₁ hg)).2
  have hA₂P : A₂ ≤ pointRadSubgroup F e₂ := fun g hg => (Subgroup.mem_inf.mp (hA₂ hg)).2
  have hsup : A₁ ⊔ A₂ ≤ H₀ := sup_le hA₁H hA₂H
  have hD₁ : (A₁ : Set (V ≃ₗ[K] V)) ⊆ pointRad F e₁ := fun g hg => hA₁P hg
  have hD₂ : (A₂ : Set (V ≃ₗ[K] V)) ⊆ pointRad F e₂ := fun g hg => hA₂P hg
  have h21 : F e₂ e₁ ≠ 0 := fun h => h12 ((form_comm halt e₁ e₂).trans h)
  obtain ⟨f₁, hef₁⟩ := exists_form_eq_one_of_ne h12
  obtain ⟨f₂, hef₂⟩ := exists_form_eq_one_of_ne h21
  have he₁ : e₁ ≠ 0 := ne_zero_of_form_eq_one hef₁
  rcases hH₀cases with hH₀s | ⟨Q₀, hQ₀, hH₀o⟩ <;>
    rcases hH₁cases with hH₁s | ⟨Q, hQ, hH₁o⟩
  · rw [hH₁s, hH₀s]
  ·
    exfalso
    have hQle : A₁ ⊔ A₂ ≤ orthSubgroup Q := by
      rw [hH₁o]
      exact comm_orth_le_orth Q
    have hA₁Q : ∀ g ∈ A₁, ∀ v, Q (g v) = Q v :=
      fun g hg v => hQle (Subgroup.mem_sup_left hg) v
    have hclaim : ∀ x : V, F x e₁ = 0 → (∀ c : K, x ≠ c • e₁) → Q x = 1 := fun x hx hxc =>
      quad_eq_one_of_normalizes hnd halt hd3 hef₁ hQ hD₁ hf₁ hA₁Q hxc
        (fun g hg => hSinv hH₀s x hx g hg)
    obtain ⟨ω, hω, hωc⟩ := exists_perp_not_mem_span (F := F) hd3 he₁
    obtain ⟨l, hl0, hl1⟩ := exists_scalar_ne_zero_one h4
    have hQω : Q ω = 1 := hclaim ω hω hωc
    have hlω : F (l • ω) e₁ = 0 := by simp [hω]
    have hlc : ∀ c : K, l • ω ≠ c • e₁ := by
      intro c hc
      apply hωc (l⁻¹ * c)
      rw [mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hl0, one_smul]
    have hQlω : Q (l • ω) = 1 := hclaim (l • ω) hlω hlc
    rw [qf_smul, hQω, mul_one] at hQlω
    have hsq : (l - 1) ^ 2 = 0 := by
      linear_combination hQlω - (l - 1) * (two_eq_zero_K (K := K))
    exact hl1 (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq))
  ·
    exfalso
    have hH₀le : H₀ ≤ orthSubgroup Q₀ := by
      rw [hH₀o]
      exact comm_orth_le_orth Q₀
    have hSp : sympSubgroup F ≤ H₀ := by
      rw [← hH₁s]
      exact hsup
    have hQ1 : ∀ x : V, x ≠ 0 → Q₀ x = 1 := by
      intro x hx
      obtain ⟨v, hv⟩ : ∃ v : V, F v x ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hx (hnd.1 x fun n => (form_comm halt x n).trans (hcon n))
      have h1 : Q₀ (symTransvection halt x 1 v) = Q₀ v :=
        hH₀le (hSp (symTransvection_mem halt x 1)) v
      rw [symTransvection_apply, one_mul, qf_transvection_eq hQ₀] at h1
      have h2 : (F v x) ^ 2 * (Q₀ x + 1) = 0 := by linear_combination h1
      have h3 : Q₀ x + 1 = 0 := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 hv)
      linear_combination h3 - (two_eq_zero_K (K := K))
    obtain ⟨l, hl0, hl1⟩ := exists_scalar_ne_zero_one h4
    have hl : l • e₁ ≠ 0 := smul_ne_zero hl0 he₁
    have h1 := hQ1 e₁ he₁
    have h2 := hQ1 (l • e₁) hl
    rw [qf_smul, h1, mul_one] at h2
    have hsq : (l - 1) ^ 2 = 0 := by
      linear_combination h2 - (l - 1) * (two_eq_zero_K (K := K))
    exact hl1 (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq))
  ·
    have hQle : A₁ ⊔ A₂ ≤ orthSubgroup Q := by
      rw [hH₁o]
      exact comm_orth_le_orth Q
    have hH₀le : H₀ ≤ orthSubgroup Q₀ := by
      rw [hH₀o]
      exact comm_orth_le_orth Q₀
    have hA₁Q : ∀ g ∈ A₁, ∀ v, Q (g v) = Q v :=
      fun g hg v => hQle (Subgroup.mem_sup_left hg) v
    have hA₂Q : ∀ g ∈ A₂, ∀ v, Q (g v) = Q v :=
      fun g hg v => hQle (Subgroup.mem_sup_right hg) v
    have hA₁Q₀ : ∀ g ∈ A₁, ∀ v, Q₀ (g v) = Q₀ v := fun g hg v => hH₀le (hA₁H hg) v
    have hA₂Q₀ : ∀ g ∈ A₂, ∀ v, Q₀ (g v) = Q₀ v := fun g hg v => hH₀le (hA₂H hg) v
    obtain ⟨c₁, hc₁⟩ := quadForm_eq_of_elationFull hnd halt hd3 hef₁ hD₁ hf₁ hQ hQ₀ hA₁Q hA₁Q₀
    obtain ⟨c₂, hc₂⟩ := quadForm_eq_of_elationFull hnd halt hd3 hef₂ hD₂ hf₂ hQ hQ₀ hA₂Q hA₂Q₀
    have hc₂0 : c₂ = 0 := by
      have h1 := hc₁ e₁
      have h2 := hc₂ e₁
      have h3 : c₂ * (F e₁ e₂) ^ 2 = 0 := by
        linear_combination h1 - h2 + (c₁ * F e₁ e₁) * form_self halt e₁
      exact (mul_eq_zero.mp h3).resolve_right (pow_ne_zero 2 h12)
    have hQeq : Q₀ = Q := QuadraticMap.ext fun v => by
      rw [hc₂ v, hc₂0, zero_mul, add_zero]
    rw [hH₁o, hH₀o, hQeq]

end CFSG.RankThree.GF2n.Stroth80.Classify
