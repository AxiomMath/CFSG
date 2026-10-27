module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypAAuxQuot
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Invariance

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ]

theorem Admits.conj_mem {Q X : Subgroup Γ} (h : Admits Q X) {g x : Γ} (hg : g ∈ Q) (hx : x ∈ X) :
    g * x * g⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.mp (h hg) x).mp hx

theorem admits_of_forall_conj {Q X : Subgroup Γ} (h : ∀ g ∈ Q, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    Admits Q X := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem admits_closure {Q : Subgroup Γ} {S : Set Γ} (h : ∀ g ∈ Q, ∀ x ∈ S, g * x * g⁻¹ ∈ S) :
    Admits Q (Subgroup.closure S) := by
  refine admits_of_forall_conj fun g hg x hx => ?_
  have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    exact Subgroup.subset_closure (h g hg y hy)
  exact hle hx

theorem admits_bot (Q : Subgroup Γ) : Admits Q ⊥ := fun g _ => by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp

theorem admits_of_centralizes {Q X : Subgroup Γ} (h : ∀ g ∈ Q, ∀ x ∈ X, g * x = x * g) :
    Admits Q X := by
  refine admits_of_forall_conj fun g hg x hx => ?_
  have := h g hg x hx
  have h2 : g * x * g⁻¹ = x := by rw [this, mul_assoc, mul_inv_cancel, mul_one]
  rwa [h2]

theorem mem_sup_iff_mul_of_le_normalizer {S X : Subgroup Γ}
    (h : S ≤ Subgroup.normalizer (X : Set Γ)) {x : Γ} :
    x ∈ S ⊔ X ↔ ∃ s ∈ S, ∃ t ∈ X, x = s * t := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right S X h
  constructor
  · intro hx
    have hx' : x ∈ (S : Set Γ) * (X : Set Γ) := by
      rw [← hmul]
      exact hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨s, hs, t, ht, rfl⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right ht)

theorem mem_sup_iff_mul_of_le_normalizer' {S X : Subgroup Γ}
    (h : X ≤ Subgroup.normalizer (S : Set Γ)) {x : Γ} :
    x ∈ S ⊔ X ↔ ∃ s ∈ S, ∃ t ∈ X, x = s * t := by
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left S X h
  constructor
  · intro hx
    have hx' : x ∈ (S : Set Γ) * (X : Set Γ) := by
      rw [← hmul]
      exact hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨s, hs, t, ht, rfl⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right ht)

theorem inf_sup_le_sup_inf' {S U X : Subgroup Γ} (hSU : S ≤ U)
    (hX : X ≤ Subgroup.normalizer (S : Set Γ)) : U ⊓ (S ⊔ X) ≤ S ⊔ (U ⊓ X) := by
  intro x hx
  obtain ⟨hxU, hxSX⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨s, hs, t, ht, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' hX).mp hxSX
  have htU : t ∈ U ⊓ X :=
    Subgroup.mem_inf.mpr ⟨by simpa using mul_mem (inv_mem (hSU hs)) hxU, ht⟩
  exact mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right htU)

theorem inf_sup_eq_sup_inf' {S U X : Subgroup Γ} (hSU : S ≤ U)
    (hX : X ≤ Subgroup.normalizer (S : Set Γ)) : U ⊓ (S ⊔ X) = S ⊔ (U ⊓ X) :=
  le_antisymm (inf_sup_le_sup_inf' hSU hX)
    (sup_le (le_inf hSU le_sup_left) (inf_le_inf_left U le_sup_right))

theorem inf_sup_eq_sup_inf {S U X : Subgroup Γ} (hSU : S ≤ U)
    (hS : S ≤ Subgroup.normalizer (X : Set Γ)) : U ⊓ (S ⊔ X) = S ⊔ (U ⊓ X) :=
  le_antisymm (HypAAux.inf_sup_le_sup_inf hSU hS)
    (sup_le (le_inf hSU le_sup_left) (inf_le_inf_left U le_sup_right))

@[expose] def HasB (A D D₁ D₂ R : Subgroup Γ) : Prop :=
  ∃ B : Subgroup Γ, B ≤ R ∧ Admits (R ⊔ D ⊔ A) B ∧ B ⊓ D = D₂ ∧ R = B ⊔ D₁

theorem HasB.of_le {A D D₁ D₂ R R' : Subgroup Γ} (h : HasB A D D₁ D₂ R') (hRR' : R ≤ R')
    (hD₁ : D₁ ≤ R) (hD₂ : D₂ ≤ D₁) (hadm : Admits (D ⊔ A) R) (hD₁D : D₁ ≤ D) :
    HasB A D D₁ D₂ R := by
  obtain ⟨B, hBR', hBadm, hBD, hRB⟩ := h
  have hRadm : Admits (R ⊔ D ⊔ A) R := sup_le (sup_le Subgroup.le_normalizer
    (le_sup_left.trans hadm)) (le_sup_right.trans hadm)
  have hD₁B : D₁ ≤ Subgroup.normalizer (B : Set Γ) := fun x hx =>
    hBadm (Subgroup.mem_sup_left (Subgroup.mem_sup_right (hD₁D hx)))
  refine ⟨B ⊓ R, inf_le_right, ?_, ?_, ?_⟩
  · exact (hBadm.mono_left (sup_le_sup_right (sup_le_sup_right hRR' D) A)).inf hRadm
  · have : B ⊓ R ⊓ D = (B ⊓ D) ⊓ R := by
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [this, hBD]
    exact inf_eq_left.mpr (hD₂.trans hD₁)
  · refine le_antisymm ?_ (sup_le inf_le_right hD₁)
    have h1 : R ≤ R ⊓ (D₁ ⊔ B) := le_inf le_rfl ((hRR'.trans hRB.le).trans (by rw [sup_comm]))
    exact h1.trans ((HypAAux.inf_sup_le_sup_inf hD₁ hD₁B).trans (by rw [sup_comm, inf_comm]))

end CFSG.SignalizerFunctorTheorem.McBride.Near
