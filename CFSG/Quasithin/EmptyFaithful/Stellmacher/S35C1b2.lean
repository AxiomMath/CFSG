module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.C1

open CFSG.Quasithin CFSG.Quasithin.F53Mod

variable {G : Type} [Group G]

theorem exists_proj {F C V : Subgroup G} (ho : IsOrthSec F C V) :
    ∃ (θ : ↥F →* Equiv.Perm (Fin 5)) (π : G → orth.W),
      Function.Surjective θ ∧ θ.ker = (cSecIn F C V).subgroupOf F ∧
      (∀ x ∈ V, ∀ y ∈ V, π (x * y) = π x * π y) ∧ (∀ x ∈ V, π x = 1 ↔ x ∈ C) ∧
      (∀ w : orth.W, ∃ x ∈ V, π x = w) ∧
      (∀ k : ↥F, ∀ m ∈ V, k * m * k⁻¹ ∈ V ∧
        π ((k : G) * m * (k : G)⁻¹) = orth.act (θ k) (π m)) := by
  classical
  obtain ⟨hn, θ, β, hθ, hθk, hsd⟩ := ho
  set e : orth.W ≃* (↥V ⧸ C.subgroupOf V) := MulEquiv.ofBijective β ⟨hsd.inj, hsd.surj⟩
  have heβ : ∀ w, e w = β w := fun w => rfl
  let π : G → orth.W := fun x => if h : x ∈ V then e.symm (QuotientGroup.mk ⟨x, h⟩) else 1
  have hπ : ∀ (x : G) (h : x ∈ V), π x = e.symm (QuotientGroup.mk ⟨x, h⟩) :=
    fun x h => by simp only [π, h, dite_true]
  refine ⟨θ, π, hθ, hθk, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hπ _ (V.mul_mem hx hy), hπ x hx, hπ y hy, ← map_mul]
    rfl
  · intro x hx
    rw [hπ x hx, MulEquiv.symm_apply_eq, map_one, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  · intro w
    obtain ⟨⟨x, hx⟩, hxw⟩ := QuotientGroup.mk_surjective (e w)
    refine ⟨x, hx, ?_⟩
    rw [hπ x hx, hxw, MulEquiv.symm_apply_apply]
  · intro k m hm
    have hu : β (e.symm (QuotientGroup.mk ⟨m, hm⟩)) = QuotientGroup.mk ⟨m, hm⟩ := by
      rw [← heβ, MulEquiv.apply_symm_apply]
    obtain ⟨hkm, h2⟩ := hsd.equiv k _ ⟨m, hm⟩ hu
    refine ⟨hkm, ?_⟩
    rw [hπ _ hkm, hπ m hm, MulEquiv.symm_apply_eq, heβ, h2]

end CFSG.Quasithin.F53.Stellmacher.S35.C1
