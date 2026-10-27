module

public import CFSG.Sporadic.Schreier.MathieuOddCoreAssembly

public section

namespace CFSG.Sporadic.Schreier

open CFSG.ComponentClassification.OuterAutomorphisms

variable {G H : Type*} [Group G] [Group H]

theorem oddCore_eq_bot_of_map {K : Subgroup G} (ψ : G ≃* H)
    (h : CFSG.oddCore (K.map ψ.toMonoidHom) = ⊥) : CFSG.oddCore K = ⊥ := by
  have h' := (noOddNormal_of_oddCore h).map (f := ψ.symm.toMonoidHom) ψ.symm.injective
  rw [Subgroup.map_map] at h'
  have hid : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id G := by
    ext g
    simp
  rw [hid, Subgroup.map_id] at h'
  exact oddCore_eq_bot_of_noOddNormal h'

theorem map_centralizer_equiv (ψ : G ≃* H) (t : G) :
    (Subgroup.centralizer ({t} : Set G)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ t} : Set H) := by
  ext h
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hg]
  · intro hh
    refine ⟨ψ.symm h, ?_, by simp⟩
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hh]

theorem map_fixSub_equiv (ψ : G ≃* H) (α : MulAut G) :
    (fixSub α).map ψ.toMonoidHom = fixSub (MulAut.congr ψ α) := by
  ext h
  simp only [Subgroup.mem_map, mem_fixSub, MulEquiv.coe_toMonoidHom, MulAut.congr_apply]
  constructor
  · rintro ⟨g, hg, rfl⟩
    simp [hg]
  · intro hh
    refine ⟨ψ.symm h, ?_, by simp⟩
    apply ψ.injective
    simpa using hh

theorem inner_of_equiv (ψ : G ≃* H)
    (h : ∀ t : H, orderOf t = 2 → CFSG.oddCore (Subgroup.centralizer ({t} : Set H)) = ⊥) :
    ∀ t : G, orderOf t = 2 → CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  intro t ht
  apply oddCore_eq_bot_of_map ψ
  rw [map_centralizer_equiv]
  exact h (ψ t) (by rw [MulEquiv.orderOf_eq]; exact ht)

theorem mulAut_card_of_equiv (ψ : G ≃* H) {k : ℕ}
    (h : Nat.card (MulAut H) ≤ k * Nat.card H) : Nat.card (MulAut G) ≤ k * Nat.card G := by
  rw [Nat.card_congr (MulAut.congr ψ).toEquiv, Nat.card_congr ψ.toEquiv]
  exact h

theorem outer_of_equiv (ψ : G ≃* H)
    (h : ∀ α : MulAut H, α * α = 1 → α ∉ inner H → CFSG.oddCore (fixSub α) = ⊥) :
    ∀ α : MulAut G, α * α = 1 → α ∉ inner G → CFSG.oddCore (fixSub α) = ⊥ := by
  intro α hα2 hα
  apply oddCore_eq_bot_of_map ψ
  rw [map_fixSub_equiv]
  refine h _ (by rw [← map_mul, hα2, map_one]) fun hin => hα ?_
  rw [← inner_map_congr ψ] at hin
  obtain ⟨β, hβ, hβα⟩ := hin
  rwa [(MulAut.congr ψ).injective hβα] at hβ

end CFSG.Sporadic.Schreier
