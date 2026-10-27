module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExc

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace NoOffRest

section Act

variable {W V : Type} [Group W]

@[expose] def ActNoOffender (ρ : W →* Equiv.Perm V) (p : ℕ) : Prop :=
  ∀ A : Subgroup W, IsElemAbelian p A → A ≠ ⊥ →
    Nat.card A * Nat.card {v : V // ∀ a ∈ A, ρ a v = v} < Nat.card V

theorem card_fix_map_conj (ρ : W →* Equiv.Perm V) (A : Subgroup W) (g : W) :
    Nat.card {v : V // ∀ a ∈ A.map (MulAut.conj g).toMonoidHom, ρ a v = v} =
      Nat.card {v : V // ∀ a ∈ A, ρ a v = v} := by
  have key : ∀ (a : W) (v : V), ρ ((MulAut.conj g).toMonoidHom a) v = v ↔
      ρ a ((ρ g)⁻¹ v) = (ρ g)⁻¹ v := fun a v => by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv,
      TableBExc.Three.perm_conj_apply_eq_iff]
  exact Nat.card_congr
    { toFun := fun v => ⟨(ρ g)⁻¹ v.1, fun a ha => (key a v.1).mp (v.2 _ ⟨a, ha, rfl⟩)⟩
      invFun := fun v => ⟨ρ g v.1, by
        rintro _ ⟨a, ha, rfl⟩
        exact (key a _).mpr (by simpa using v.2 a ha)⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }

theorem actNoOffender_of_sylow [Finite W] {ρ : W →* Equiv.Perm V} {p : ℕ} (hp : p.Prime)
    {S : Subgroup W} (hidx : ¬ p ∣ S.index)
    (hS : ∀ A : Subgroup W, A ≤ S → IsElemAbelian p A → A ≠ ⊥ →
      Nat.card A * Nat.card {v : V // ∀ a ∈ A, ρ a v = v} < Nat.card V) :
    ActNoOffender ρ p := by
  intro A hA hA1
  obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index hp hidx
    (TableB.isPGroup_of_isElemAbelian hA)
  have hne : A.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
  have h := hS _ hg (isElemAbelian_map_conj hA g) hne
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_fix_map_conj] at h

end Act

end NoOffRest

section Frame

variable {G : Type} [Group G] {W V : Type} [Group W] [AddCommGroup V]

@[expose] def GGBstarModelFrame (ρ : W →* Equiv.Perm V) (p : ℕ) (M Bs : Subgroup G) : Prop :=
  ∃ ι : Multiplicative V →* G, Function.Injective ι ∧ ι.range = Bs ∧
    ∀ g ∈ M, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
      ∃ w : W, ∀ v : V, g * ι (Multiplicative.ofAdd v) * g⁻¹ = ι (Multiplicative.ofAdd (ρ w v))

theorem GGBstarModelFrame.noOffender [Finite G] [Finite V] {ρ : W →* Equiv.Perm V} {p : ℕ}
    {M Bs : Subgroup G} (h : GGBstarModelFrame ρ p M Bs) (hρ : Function.Injective ρ)
    (hW : NoOffRest.ActNoOffender ρ p) : GGNoOffender p M Bs := by
  obtain ⟨ι, hinj, hrange, hact⟩ := h
  exact NoOffExc.noOffender_of_modelAct ρ hρ hW hinj hrange hact

end Frame

end CFSG.StandardType
