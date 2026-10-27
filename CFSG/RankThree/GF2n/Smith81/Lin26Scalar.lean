module

public import CFSG.RankThree.GF2n.Smith81.LinRestCore
public import CFSG.RankThree.GF2n.Smith81.Lin26Cartan
public import CFSG.RankThree.GF2n.Smith81.Lin26Linear

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise Matrix

section Scalar

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

@[expose] def RestModel.SLProp (R : RestModel M Q Z n V₁ V₂) : Prop :=
  ∀ U : R.M₀.E →ₗ[R.K] R.M₀.E, (∀ e, R.M₀.Qf (U e) = R.M₀.Qf e) →
    ∀ (h₁ : ∀ w ∈ R.W₁, U w ∈ R.W₁), (∀ w ∈ R.W₂, U w ∈ R.W₂) →
      LinearMap.det (U.restrict h₁) = 1 →
      ∃ s ∈ M, ∀ x ∈ Q, R.M₀.π (s * x * s⁻¹) = U (R.M₀.π x)

theorem RestModel.B_of_qf (R : RestModel M Q Z n V₁ V₂) (g : R.M₀.E →ₗ[R.K] R.M₀.E) (ν : R.K)
    (h : ∀ e, R.M₀.Qf (g e) = ν * R.M₀.Qf e) (e e' : R.M₀.E) :
    R.M₀.B (g e) (g e') = ν * R.M₀.B e e' := by
  have h1 := R.M₀.Qf_add (g e) (g e')
  rw [← map_add g, h (e + e'), h e, h e', R.M₀.Qf_add e e'] at h1
  linear_combination -h1

theorem RestModel.perfect (R : RestModel M Q Z n V₁ V₂) :
    (∀ a ∈ R.W₁, (∀ b ∈ R.W₂, R.M₀.B a b = 0) → a = 0) ∧
      (∀ b ∈ R.W₂, (∀ a ∈ R.W₁, R.M₀.B a b = 0) → b = 0) := by
  constructor
  · intro a ha h
    refine R.M₀.nondeg a fun e => ?_
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp
      (show e ∈ R.W₁ ⊔ R.W₂ by rw [R.hsup]; exact Submodule.mem_top)
    rw [map_add, R.iso₁ a ha w₁ hw₁, h w₂ hw₂, add_zero]
  · intro b hb h
    refine R.M₀.nondeg b fun e => ?_
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp
      (show e ∈ R.W₁ ⊔ R.W₂ by rw [R.hsup]; exact Submodule.mem_top)
    rw [map_add, R.iso₂ b hb w₂ hw₂, Tim79.QuadModel.B_comm, h w₁ hw₁, neg_zero, add_zero]

theorem RestModel.exists_scalar (R : RestModel M Q Z n V₁ V₂) (hn : 2 ≤ n) (hsl : R.SLProp)
    (h31 : ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂))
    (hroot₁ : ∃ Y : Subgroup G, Ctx M Q Z Y ∧ Y ≤ V₁ ∧ V₁ ≤ QB Y)
    (hroot₂ : ∃ Y : Subgroup G, Ctx M Q Z Y ∧ Y ≤ V₂ ∧ V₂ ≤ QB Y) :
    ∃ c ∈ M, ∃ ν : R.Kˣ, ν ≠ 1 ∧
      ∀ x ∈ Q, R.M₀.π (c * x * c⁻¹) = (ν : R.K) • R.M₀.π x := by
  classical
  have H := R.hyp
  obtain ⟨ν, hν⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := R.Kˣ)
  have hcardU : Nat.card R.Kˣ = Nat.card Z - 1 := by rw [Nat.card_units, R.gm.card]
  rw [hcardU] at hν
  obtain ⟨Y₂, hY₂, hY₂V, hmod₂⟩ := hroot₂
  obtain ⟨k, f, b, hh, hf₁, hf₂⟩ := R.cartan_homology hn h31 hY₂ hY₂V hmod₂ ν hν
  obtain ⟨Y₁, hY₁, hY₁V, hmod₁⟩ := hroot₁
  obtain ⟨k', f'₀, b', hh', hf₁', hf₂'⟩ := R.symm.cartan_homology hn
    (fun v hv hv1 => (h31 v hv hv1).trans or_comm) hY₁ hY₁V hmod₁ ν hν
  let f' : R.M₀.E →ₗ[R.K] R.M₀.E := f'₀
  have hh'' : IsHomology R.M₀ M R.W₁ k' ν f' b' := hh'
  have hf₁'' : ∀ w ∈ R.W₁, f' w ∈ R.W₁ := hf₂'
  have hf₂'' : ∀ w ∈ R.W₂, f' w ∈ R.W₂ := hf₁'
  have hBf := R.B_of_qf f (ν : R.K) hh.qf
  have hBf' := R.B_of_qf f' (ν : R.K) hh''.qf
  have hdet₂ : LinearMap.det (f.restrict hf₂) = ((ν⁻¹ : R.Kˣ) : R.K) :=
    det_restrict_homology R.W₂ f hf₂ hh.b_mem hh.b_ne _ hh.fb hh.hom
  have hdet₁' : LinearMap.det (f'.restrict hf₁'') = ((ν⁻¹ : R.Kˣ) : R.K) :=
    det_restrict_homology R.W₁ f' hf₁'' hh''.b_mem hh''.b_ne _ hh''.fb hh''.hom
  have hLA := det_restrict_mul_det_restrict R.M₀.B R.W₁ R.W₂ R.perfect.1 R.perfect.2 f hf₁ hf₂
    (ν : R.K) (fun a _ b _ => hBf a b)
  rw [hdet₂] at hLA
  set f₀ : R.M₀.E →ₗ[R.K] R.M₀.E := f.comp f' with hf₀
  have hf₀₁ : ∀ w ∈ R.W₁, f₀ w ∈ R.W₁ := fun w hw => hf₁ _ (hf₁'' w hw)
  have hf₀₂ : ∀ w ∈ R.W₂, f₀ w ∈ R.W₂ := fun w hw => hf₂ _ (hf₂'' w hw)
  have hqf₀ : ∀ e, R.M₀.Qf (f₀ e) = (ν : R.K) ^ 2 * R.M₀.Qf e := fun e => by
    show R.M₀.Qf (f (f' e)) = _
    rw [hh.qf, hh''.qf]; ring
  set U : R.M₀.E →ₗ[R.K] R.M₀.E := (ν : R.K)⁻¹ • f₀ with hU
  have hν0 : (ν : R.K) ≠ 0 := ν.ne_zero
  have hUapp : ∀ e, U e = (ν : R.K)⁻¹ • f₀ e := fun e => rfl
  have hqU : ∀ e, R.M₀.Qf (U e) = R.M₀.Qf e := fun e => by
    rw [hUapp, R.M₀.Qf_smul, hqf₀]
    field_simp
  have hU₁ : ∀ w ∈ R.W₁, U w ∈ R.W₁ := fun w hw => R.W₁.smul_mem _ (hf₀₁ w hw)
  have hU₂ : ∀ w ∈ R.W₂, U w ∈ R.W₂ := fun w hw => R.W₂.smul_mem _ (hf₀₂ w hw)
  have hdetU : LinearMap.det (U.restrict hU₁) = 1 := by
    have e1 : U.restrict hU₁ = (ν : R.K)⁻¹ • (f.restrict hf₁ ∘ₗ f'.restrict hf₁'') := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      simp [hUapp, hf₀]
    rw [e1, LinearMap.det_smul, LinearMap.det_comp, hdet₁', hLA, ← mul_pow,
      inv_mul_cancel₀ hν0, one_pow]
  obtain ⟨s, hsM, hs⟩ := hsl U hqU hU₁ hU₂ hdetU
  refine ⟨k * k' * s⁻¹, M.mul_mem (M.mul_mem hh.mem hh''.mem) (M.inv_mem hsM), ν, ?_,
    fun x hx => ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hν
    have := H.q4
    omega
  · have hxs : s⁻¹ * x * s ∈ Q := by
      simpa using conj_mem_Q H (M.inv_mem hsM) hx
    have e : k * k' * s⁻¹ * x * (k * k' * s⁻¹)⁻¹ = k * (k' * (s⁻¹ * x * s) * k'⁻¹) * k⁻¹ := by
      group
    have e2 : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    have h3 := hs _ hxs
    rw [e2] at h3
    rw [e, hh.act _ (conj_mem_Q H hh''.mem hxs), hh''.act _ hxs]
    have h4 : f (f' (R.M₀.π (s⁻¹ * x * s))) = (ν : R.K) • U (R.M₀.π (s⁻¹ * x * s)) := by
      rw [hUapp, smul_smul, mul_inv_cancel₀ hν0, one_smul]
      rfl
    rw [h4, ← h3]

end Scalar

end CFSG.RankThree.GF2n.Smith81
