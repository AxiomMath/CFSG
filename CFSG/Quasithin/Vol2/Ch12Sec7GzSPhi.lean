module

public import CFSG.Assembly.OrderReductions.FrattiniElementary

public section

namespace CFSG.Quasithin.H13.I1277

open Subgroup
open scoped commutatorElement

section Phi

variable {G : Type} [Group G]

@[expose] def Phi' (Q : Subgroup G) : Subgroup G :=
  Subgroup.closure ({x | ∃ y ∈ Q, x = y ^ 2} ∪ {x | ∃ a ∈ Q, ∃ b ∈ Q, x = a * b * a⁻¹ * b⁻¹})

theorem sq_mem_Phi' {Q : Subgroup G} {y : G} (hy : y ∈ Q) : y ^ 2 ∈ Phi' Q :=
  Subgroup.subset_closure (Or.inl ⟨y, hy, rfl⟩)

theorem comm_mem_Phi' {Q : Subgroup G} {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    a * b * a⁻¹ * b⁻¹ ∈ Phi' Q :=
  Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, rfl⟩)

theorem Phi'_le (Q : Subgroup G) : Phi' Q ≤ Q := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x (⟨y, hy, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
  · exact Q.pow_mem hy 2
  · exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)

theorem Phi'_normal {H Q : Subgroup G} (hQn : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q) :
    ∀ h ∈ H, ∀ n ∈ Phi' Q, h * n * h⁻¹ ∈ Phi' Q := by
  intro h hh n hn
  have key : Phi' Q ≤ (Phi' Q).comap (MulAut.conj h).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (⟨y, hy, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · show h * y ^ 2 * h⁻¹ ∈ Phi' Q
      have e : h * y ^ 2 * h⁻¹ = (h * y * h⁻¹) ^ 2 := (conj_pow).symm
      rw [e]
      exact sq_mem_Phi' (hQn h hh y hy)
    · show h * (a * b * a⁻¹ * b⁻¹) * h⁻¹ ∈ Phi' Q
      have e : h * (a * b * a⁻¹ * b⁻¹) * h⁻¹ =
          (h * a * h⁻¹) * (h * b * h⁻¹) * (h * a * h⁻¹)⁻¹ * (h * b * h⁻¹)⁻¹ := by group
      rw [e]
      exact comm_mem_Phi' (hQn h hh a ha) (hQn h hh b hb)
  exact key hn

variable [Finite G]

open CFSG.OrderReductions.FrattiniElementary in
theorem Phi'_frattini {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) :
    ∀ n (hn : n ∈ Phi' Q), (⟨n, Phi'_le Q hn⟩ : ↥Q) ∈ frattini ↥Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Phi' Q ≤ (frattini ↥Q).map Q.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (⟨y, hy, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · exact ⟨⟨y, hy⟩ ^ 2, pow_mem_frattini 2 hQ ⟨y, hy⟩, rfl⟩
    · refine ⟨⁅(⟨a, ha⟩ : ↥Q), ⟨b, hb⟩⁆, commutator_le_frattini 2 hQ
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)), rfl⟩
  intro n hn
  obtain ⟨m, hm, hmn⟩ := hle hn
  have : m = ⟨n, Phi'_le Q hn⟩ := Subtype.ext hmn
  exact this ▸ hm

end Phi

end CFSG.Quasithin.H13.I1277

end
