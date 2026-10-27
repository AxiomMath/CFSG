module

public import CFSG.LocalAnalysis.StandardType.GGTableBPositionToral
public import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace CoverPToral

theorem forall_fix_of_toral {R : Type} [Group R] {p r : ℕ} (V : Set R)
    (hT : ∀ E' : Subgroup R, IsElemAbelian p E' → p ^ r ≤ Nat.card E' →
      ∃ β : MulAut R, ∀ x ∈ E', β x ∈ V)
    (hA : ∀ a : MulAut R, (∃ k : ℕ, a ^ p ^ k = 1) →
      ∃ (ρ₁ : R) (φ : MulAut R), a = MulAut.conj ρ₁ * φ ∧ ∀ v ∈ V, φ v = v)
    {E' : Subgroup R} (hE' : IsElemAbelian p E') (hcard : p ^ r ≤ Nat.card E')
    {a : MulAut R} (ha : ∃ k : ℕ, a ^ p ^ k = 1) :
    ∃ ρ : R, ∀ x ∈ E', ((MulAut.conj ρ)⁻¹ * a) x = x := by
  obtain ⟨β, hβ⟩ := hT E' hE' hcard
  obtain ⟨k, hk⟩ := ha
  have hbpow : (β * a * β⁻¹) ^ p ^ k = 1 := by
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  obtain ⟨ρ₁, φ, hb, hφ⟩ := hA (β * a * β⁻¹) ⟨k, hbpow⟩
  refine ⟨β⁻¹ ρ₁, fun x hx => ?_⟩
  have haeq : a = β⁻¹ * (MulAut.conj ρ₁ * φ) * β := by
    calc a = β⁻¹ * (β * a * β⁻¹) * β := by group
      _ = β⁻¹ * (MulAut.conj ρ₁ * φ) * β := by rw [hb]
  have hmain : (MulAut.conj (β⁻¹ ρ₁))⁻¹ * a = β⁻¹ * φ * β := by
    rw [← inv_mulAut_conj_mul β ρ₁, haeq]
    group
  rw [hmain]
  simp only [MulAut.mul_apply]
  rw [hφ (β x) (hβ x hx), MulAut.inv_apply_self]

theorem forall_fix_of_mulEquiv {R S : Type*} [Group R] [Group S] (e : R ≃* S) {p r : ℕ}
    (h : ∀ E' : Subgroup S, IsElemAbelian p E' → p ^ r ≤ Nat.card E' →
      ∀ a : MulAut S, (∃ k : ℕ, a ^ p ^ k = 1) →
        ∃ ρ : S, ∀ x ∈ E', ((MulAut.conj ρ)⁻¹ * a) x = x) :
    ∀ E' : Subgroup R, IsElemAbelian p E' → p ^ r ≤ Nat.card E' →
      ∀ a : MulAut R, (∃ k : ℕ, a ^ p ^ k = 1) →
        ∃ ρ : R, ∀ x ∈ E', ((MulAut.conj ρ)⁻¹ * a) x = x := by
  intro E' hE' hcard a ha
  have hE'map : IsElemAbelian p (E'.map e.toMonoidHom) := hE'.map e.toMonoidHom
  have hcard' : p ^ r ≤ Nat.card (E'.map e.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  obtain ⟨k, hk⟩ := ha
  have ha' : (MulAut.congr e a) ^ p ^ k = 1 := by
    rw [← map_pow, hk, map_one]
  obtain ⟨ρ', hρ'⟩ := h (E'.map e.toMonoidHom) hE'map hcard' (MulAut.congr e a) ⟨k, ha'⟩
  have hcongr : MulAut.congr e (MulAut.conj (e.symm ρ')) = MulAut.conj (e (e.symm ρ')) := by
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply, mul_assoc]
  rw [e.apply_symm_apply] at hcongr
  refine ⟨e.symm ρ', fun x hx => ?_⟩
  have hx' : e x ∈ E'.map e.toMonoidHom := Subgroup.mem_map_of_mem _ hx
  have h1 := hρ' (e x) hx'
  have hval : e (((MulAut.conj (e.symm ρ'))⁻¹ * a) x) =
      ((MulAut.conj ρ')⁻¹ * MulAut.congr e a) (e x) := by
    rw [show e (((MulAut.conj (e.symm ρ'))⁻¹ * a) x) =
      (MulAut.congr e ((MulAut.conj (e.symm ρ'))⁻¹ * a)) (e x) from by
        simp [MulAut.congr_apply]]
    rw [map_mul, map_inv, hcongr]
  apply e.injective
  rw [hval]
  exact h1

theorem ggCoverPTableB_of_forall_fix {R : Type} [Group R] (hZ : Subgroup.center R = ⊥)
    {p r : ℕ} {I : Set (MulAut R)} (hI : ∀ φ ∈ I, φ ∈ (MulAut.conj : R →* MulAut R).range)
    (hcard : ∀ {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
      {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)},
      GGTableBPosition p L' E I θ hE → p ^ r ≤ Nat.card (ggLAutImage L' θ E))
    (hfix : ∀ E' : Subgroup R, IsElemAbelian p E' → p ^ r ≤ Nat.card E' →
      ∀ a : MulAut R, (∃ k : ℕ, a ^ p ^ k = 1) →
        ∃ ρ : R, ∀ x ∈ E', ((MulAut.conj ρ)⁻¹ * a) x = x) :
    GGCoverPTableB p R I := by
  intro M _ _ L' E θ hE hP a ha
  obtain ⟨E_R, hERelem, hERcard, hinner⟩ :=
    exists_elemAbelian_of_forall_inner hZ θ hE hP.2.1
      (fun e => hI _ (hP.2.2.2.1 e))
  have hcardER : p ^ r ≤ Nat.card E_R := by
    rw [hERcard]
    exact hcard hP
  obtain ⟨ρ, hρ⟩ := hfix E_R hERelem hcardER a ha
  refine ⟨ρ, fun e => ?_⟩
  obtain ⟨x, hxmem, hxeq⟩ := hinner e
  rw [hxeq]
  exact CFSG.commute_conj_of_apply_eq (β := (MulAut.conj ρ)⁻¹ * a) (hρ x hxmem)

theorem exists_mulAut_mapsTo_of_mulEquiv {R S : Type*} [Group R] [Group S] (e : R ≃* S)
    {p r : ℕ} {T : Subgroup S}
    (hS : ∀ E : Subgroup S, IsElemAbelian p E → p ^ r ≤ Nat.card E →
      ∃ α : S ≃* S, E = T.map α.toMonoidHom)
    {E' : Subgroup R} (hE' : IsElemAbelian p E') (hcard : p ^ r ≤ Nat.card E') :
    ∃ β : MulAut R, ∀ x ∈ E', β x ∈ e.symm '' (T : Set S) := by
  obtain ⟨α, hα⟩ := hS (E'.map e.toMonoidHom) (hE'.map e.toMonoidHom)
    (by rwa [Subgroup.card_map_of_injective e.injective])
  refine ⟨(e.trans α.symm).trans e.symm, fun x hx => ?_⟩
  have hx' : e x ∈ T.map α.toMonoidHom := by
    rw [← hα]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hx
  obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.mp hx'
  have hαt : α t = e x := htx
  refine ⟨t, ht, ?_⟩
  show e.symm t = e.symm (α.symm (e x))
  rw [← hαt, MulEquiv.symm_apply_apply]

end CoverPToral

end CFSG.StandardType

end
