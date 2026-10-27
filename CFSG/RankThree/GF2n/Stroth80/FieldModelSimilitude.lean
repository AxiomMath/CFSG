module

public import CFSG.RankThree.GF2n.Tim79Heis

public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open scoped commutatorElement Matrix
open Polynomial CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G]

section Similitude

theorem semilinear_similitude {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : QuadModel QF V K γ) (hVQF : V ≤ QF) {τ : G} {a : K} (σ : K ≃+* K)
    (hτV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQF : ∀ x ∈ QF, τ * x * τ⁻¹ ∈ QF) (hQF' : ∀ x ∈ QF, τ⁻¹ * x * τ ∈ QF)
    (hγ : ∀ v ∈ V, γ (τ * v * τ⁻¹) = a * σ (γ v)) :
    ∃ T : M₀.E ≃+ M₀.E, (∀ (c : K) (e : M₀.E), T (c • e) = σ c • T e) ∧
      (∀ x ∈ QF, M₀.π (τ * x * τ⁻¹) = T (M₀.π x)) ∧ ∀ e, M₀.Qf (T e) = a * σ (M₀.Qf e) := by
  have hVn : ∀ v, v ∈ V ↔ τ * v * τ⁻¹ ∈ V := Subgroup.mem_normalizer_iff.mp hτV
  have pi_one : M₀.π 1 = 0 := by
    have h := M₀.π_mul 1 QF.one_mem 1 QF.one_mem
    rw [mul_one] at h
    exact left_eq_add.mp h
  have pi_inv : ∀ x ∈ QF, M₀.π x⁻¹ = - M₀.π x := by
    intro x hx
    have h := M₀.π_mul x hx x⁻¹ (QF.inv_mem hx)
    rw [mul_inv_cancel, pi_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have pi_eq : ∀ x ∈ QF, ∀ y ∈ QF, M₀.π x = M₀.π y → x⁻¹ * y ∈ V := by
    intro x hx y hy h
    refine (M₀.π_ker _ (QF.mul_mem (QF.inv_mem hx) hy)).mp ?_
    rw [M₀.π_mul _ (QF.inv_mem hx) _ hy, pi_inv x hx, h, neg_add_cancel]
  choose lift hlift_mem hlift using M₀.π_surj
  let f₀ : M₀.E → M₀.E := fun e => M₀.π (τ * lift e * τ⁻¹)
  have hf₀ : ∀ x ∈ QF, f₀ (M₀.π x) = M₀.π (τ * x * τ⁻¹) := by
    intro x hx
    have h1 : x⁻¹ * lift (M₀.π x) ∈ V := pi_eq x hx _ (hlift_mem _) (hlift _).symm
    have hv : τ * (x⁻¹ * lift (M₀.π x)) * τ⁻¹ ∈ V := (hVn _).mp h1
    have e : τ * lift (M₀.π x) * τ⁻¹ =
        τ * x * τ⁻¹ * (τ * (x⁻¹ * lift (M₀.π x)) * τ⁻¹) := by group
    show M₀.π (τ * lift (M₀.π x) * τ⁻¹) = _
    rw [e, M₀.π_mul _ (hQF x hx) _ (hVQF hv), (M₀.π_ker _ (hVQF hv)).mpr hv, add_zero]
  have hadd : ∀ e e' : M₀.E, f₀ (e + e') = f₀ e + f₀ e' := by
    intro e e'
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj e'
    rw [← M₀.π_mul x hx y hy, hf₀ _ (QF.mul_mem hx hy), hf₀ x hx, hf₀ y hy,
      show τ * (x * y) * τ⁻¹ = τ * x * τ⁻¹ * (τ * y * τ⁻¹) by group,
      M₀.π_mul _ (hQF x hx) _ (hQF y hy)]
  have hB : ∀ e f : M₀.E, M₀.B (f₀ e) (f₀ f) = a * σ (M₀.B e f) := by
    intro e f
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj f
    rw [hf₀ x hx, hf₀ y hy, ← M₀.comm_eq _ (hQF x hx) _ (hQF y hy), ← M₀.comm_eq x hx y hy,
      show ⁅τ * x * τ⁻¹, τ * y * τ⁻¹⁆ = τ * ⁅x, y⁆ * τ⁻¹ by
        simp only [commutatorElement_def]; group]
    exact hγ _ (M₀.comm_mem x hx y hy)
  have hQ : ∀ e : M₀.E, M₀.Qf (f₀ e) = a * σ (M₀.Qf e) := by
    intro e
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    rw [hf₀ x hx, ← M₀.sq_eq _ (hQF x hx), ← M₀.sq_eq x hx,
      show (τ * x * τ⁻¹) ^ 2 = τ * x ^ 2 * τ⁻¹ by rw [pow_two, pow_two]; group]
    exact hγ _ (M₀.sq_mem x hx)
  have hsurj : Function.Surjective f₀ := by
    intro g
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj g
    refine ⟨M₀.π (τ⁻¹ * y * τ), ?_⟩
    rw [hf₀ _ (hQF' y hy), show τ * (τ⁻¹ * y * τ) * τ⁻¹ = y by group]
  have hsmul : ∀ (c : K) (e : M₀.E), f₀ (c • e) = σ c • f₀ e := by
    intro c e
    refine sub_eq_zero.mp (M₀.nondeg _ fun g => ?_)
    obtain ⟨g', rfl⟩ := hsurj g
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hB,
      map_mul]
    ring
  have hinj : ∀ e : M₀.E, f₀ e = 0 → e = 0 := by
    intro e he
    have hx := hlift_mem e
    have h1 : τ * lift e * τ⁻¹ ∈ V := (M₀.π_ker _ (hQF _ hx)).mp he
    have h2 : lift e ∈ V := (hVn _).mpr h1
    rw [← hlift e]
    exact (M₀.π_ker _ hx).mpr h2
  let Tm : M₀.E →+ M₀.E := AddMonoidHom.mk' f₀ hadd
  have hTinj : Function.Injective Tm := (injective_iff_map_eq_zero Tm).mpr hinj
  exact ⟨AddEquiv.ofBijective Tm ⟨hTinj, hsurj⟩, hsmul, fun x hx => (hf₀ x hx).symm, hQ⟩

@[expose] def castQuadModel {QF QF' V : Subgroup G} {K : Type} [Field K] {γ : G → K} (h : QF = QF')
    (M₀ : QuadModel QF V K γ) : QuadModel QF' V K γ where
  E := M₀.E
  acg := M₀.acg
  mod := M₀.mod
  fin := M₀.fin
  π := M₀.π
  B := M₀.B
  Qf := M₀.Qf
  π_mul := fun x hx y hy => M₀.π_mul x (h ▸ hx) y (h ▸ hy)
  π_surj := fun e => by
    obtain ⟨x, hx, hxe⟩ := M₀.π_surj e
    exact ⟨x, h ▸ hx, hxe⟩
  π_ker := fun x hx => M₀.π_ker x (h ▸ hx)
  comm_mem := fun x hx y hy => M₀.comm_mem x (h ▸ hx) y (h ▸ hy)
  sq_mem := fun x hx => M₀.sq_mem x (h ▸ hx)
  comm_eq := fun x hx y hy => M₀.comm_eq x (h ▸ hx) y (h ▸ hy)
  sq_eq := fun x hx => M₀.sq_eq x (h ▸ hx)
  alt := M₀.alt
  nondeg := M₀.nondeg
  Qf_smul := M₀.Qf_smul
  Qf_add := M₀.Qf_add

end Similitude

end CFSG.RankThree.GF2n.Stroth80.FieldModel
