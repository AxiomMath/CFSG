module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.Quasithin.S146zU.UF1

section Quotient

theorem ker_eq_of_isSimpleGroup_quotient {Y A : Type*} [Group Y] [Group A] {O : Subgroup Y}
    [O.Normal] [IsSimpleGroup (Y ⧸ O)] (ρ : Y →* A) (hO : O ≤ ρ.ker) (hρ : ρ.ker ≠ ⊤) :
    ρ.ker = O := by
  have hn : ((ρ.ker).map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map (MonoidHom.normal_ker ρ) _ (QuotientGroup.mk'_surjective O)
  rcases hn.eq_bot_or_eq_top with h | h
  · refine le_antisymm (fun y hy => ?_) hO
    have hy' : QuotientGroup.mk' O y ∈ (ρ.ker).map (QuotientGroup.mk' O) := ⟨y, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at hy'
    exact (QuotientGroup.eq_one_iff y).mp hy'
  · exfalso
    refine hρ (eq_top_iff.mpr fun y _ => ?_)
    have hy' : QuotientGroup.mk' O y ∈ (ρ.ker).map (QuotientGroup.mk' O) :=
      h ▸ Subgroup.mem_top _
    obtain ⟨y', hy'k, hyy⟩ := hy'
    have h1 : y'⁻¹ * y ∈ O := by
      rw [← QuotientGroup.eq]
      exact hyy
    have h2 : ρ (y'⁻¹ * y) = 1 := hO h1
    have h3 : ρ y' = 1 := hy'k
    rw [map_mul, map_inv, h3, inv_one, one_mul] at h2
    exact h2

end Quotient

section Sup

variable {X A : Type*} [Group X] [Group A]

private theorem conj_mem_sup {Q K₁ K₂ : Subgroup X} [Q.Normal]
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b * a⁻¹ * b⁻¹ ∈ Q) :
    ∀ a ∈ K₁, ∀ y ∈ K₂ ⊔ Q, a * y * a⁻¹ ∈ K₂ ⊔ Q := by
  intro a ha y hy
  obtain ⟨b, hb, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ Q := hcomm a ha b hb
  have h2 : a * q * a⁻¹ ∈ Q := Subgroup.Normal.conj_mem inferInstance q hq a
  have e : a * (b * q) * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b * (a * q * a⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
    (Subgroup.mem_sup_left hb)) (Subgroup.mem_sup_right h2)

private theorem le_normalizer_sup {Q K₁ K₂ : Subgroup X} [Q.Normal]
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b * a⁻¹ * b⁻¹ ∈ Q) :
    K₁ ≤ Subgroup.normalizer ((K₂ ⊔ Q : Subgroup X) : Set X) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_sup hcomm a ha y hy, fun hy => ?_⟩
  have := conj_mem_sup hcomm a⁻¹ (K₁.inv_mem ha) _ hy
  simpa [mul_assoc] using this

theorem exists_mul_mul_of_mem_sup_of_commutator_le {Q K₁ K₂ : Subgroup X} [Q.Normal]
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b * a⁻¹ * b⁻¹ ∈ Q) {x : X} (hx : x ∈ K₁ ⊔ K₂) :
    ∃ a ∈ K₁, ∃ b ∈ K₂, ∃ q ∈ Q, x = a * b * q := by
  have hx' : x ∈ K₁ ⊔ (K₂ ⊔ Q) := sup_le_sup_left le_sup_left K₁ hx
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right K₁ (K₂ ⊔ Q) (le_normalizer_sup hcomm)
  have hx'' : x ∈ (↑(K₁ ⊔ (K₂ ⊔ Q)) : Set X) := hx'
  rw [hmul] at hx''
  obtain ⟨a, ha, y, hy, rfl⟩ := hx''
  obtain ⟨b, hb, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  exact ⟨a, ha, b, hb, q, hq, by rw [mul_assoc]⟩

theorem ker_inf_sup_le {Q K₁ : Subgroup X} [Q.Normal] (φ : X →* A) (hQ : Q ≤ φ.ker) (t : X)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₁.map (MulAut.conj t).toMonoidHom, a * b * a⁻¹ * b⁻¹ ∈ Q)
    (hφc : ∀ a ∈ K₁.map φ, ∀ b ∈ (K₁.map (MulAut.conj t).toMonoidHom).map φ, a * b = b * a)
    (hcentre : ∀ n ∈ K₁.map φ, (∀ m ∈ K₁.map φ, n * m = m * n) → n = 1)
    (hker : ∀ k ∈ K₁, φ k = 1 → k ∈ Q) :
    ∀ x ∈ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom, φ x = 1 → x ∈ Q := by
  intro x hx hφx
  obtain ⟨a, ha, b, hb, q, hq, rfl⟩ := exists_mul_mul_of_mem_sup_of_commutator_le hcomm hx
  have hqφ : φ q = 1 := hQ hq
  have h1 : φ a * φ b = 1 := by simpa [hqφ] using hφx
  have haφ : φ a ∈ K₁.map φ := Subgroup.mem_map_of_mem φ ha
  have hbφ : φ b ∈ (K₁.map (MulAut.conj t).toMonoidHom).map φ := Subgroup.mem_map_of_mem φ hb
  have hab : φ a = (φ b)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hφa : φ a = 1 := by
    refine hcentre _ haφ fun m hm => ?_
    have := hφc m hm (φ b)⁻¹ (Subgroup.inv_mem _ hbφ)
    rw [hab]
    exact this.symm
  have haQ : a ∈ Q := hker a ha hφa
  have hφb : φ b = 1 := by
    rw [hφa, one_mul] at h1
    exact h1
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hb
  have hkφ : φ k = 1 := by
    have e : φ ((MulAut.conj t).toMonoidHom k) = φ t * φ k * (φ t)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [e] at hφb
    have e2 : φ k = (φ t)⁻¹ * (φ t * φ k * (φ t)⁻¹) * φ t := by group
    rw [e2, hφb]
    group
  have hkQ : k ∈ Q := hker k hk hkφ
  have hbQ : (MulAut.conj t).toMonoidHom k ∈ Q := by
    simpa [MulAut.conj_apply] using Subgroup.Normal.conj_mem inferInstance k hkQ t
  exact Q.mul_mem (Q.mul_mem haQ hbQ) hq

end Sup

end CFSG.Quasithin.S146zU.UF1
