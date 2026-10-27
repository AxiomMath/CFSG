module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6E8Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

private theorem w183finG4A6_map_s6 {M : Type} [Group M]
    (e : M ≃* alternatingGroup (Fin 6)) {f : MulAut M →* Equiv.Perm (Fin 10)}
    (hfsurj : ∀ x ∈ A6Models.autA6, ∃ γ, f γ = x)
    (hfs6 : ∀ γ, γ ∈ w183finG4A6AutS6 e ↔ f γ ∈ A6Facts.s6) :
    (w183finG4A6AutS6 e).map f = A6Facts.s6 := by
  apply le_antisymm
  · rintro y ⟨γ, hγ, rfl⟩
    exact (hfs6 γ).1 hγ
  · intro y hy
    obtain ⟨γ, hγ⟩ := hfsurj y (A6Facts.s6_le_autA6 hy)
    exact ⟨γ, (hfs6 γ).2 (by rwa [hγ]), hγ⟩

private theorem w183finG4A6_map_psl29 {M : Type} [Group M]
    {f : MulAut M →* Equiv.Perm (Fin 10)}
    (hfsurj : ∀ x ∈ A6Models.autA6, ∃ γ, f γ = x)
    (hfinn : ∀ γ, γ ∈ innAutOf M ↔ f γ ∈ A6Models.psl29) :
    (innAutOf M).map f = A6Models.psl29 := by
  apply le_antisymm
  · rintro y ⟨γ, hγ, rfl⟩
    exact (hfinn γ).1 hγ
  · intro y hy
    obtain ⟨γ, hγ⟩ := hfsurj y (A6Facts.psl29_le_autA6 hy)
    exact ⟨γ, (hfinn γ).2 (by rwa [hγ]), hγ⟩

theorem w183finG4A6_autS6_normal {M : Type} [Group M] (e : M ≃* alternatingGroup (Fin 6)) :
    (w183finG4A6AutS6 e).Normal := by
  obtain ⟨f, hfinj, hfauto, hfsurj, hfinn, hfs6⟩ := w183finG4A6_exists_model e
  refine Subgroup.Normal.mk fun n hn g => ?_
  rw [hfs6] at hn ⊢
  have h := w183finG4A6_model_s6_normal (f g) (hfauto g) (f n) hn
  simpa using h

theorem w183finG4A6_elemAbelian_le_autS6 {M : Type} [Group M]
    (e : M ≃* alternatingGroup (Fin 6)) :
    ∀ A : Subgroup (MulAut M), IsElemAbelian 2 A → 8 ≤ Nat.card A → A ≤ w183finG4A6AutS6 e := by
  intro A hA h8
  obtain ⟨f, hfinj, hfauto, hfsurj, hfinn, hfs6⟩ := w183finG4A6_exists_model e
  have hBauto : A.map f ≤ A6Models.autA6 := by
    rintro b ⟨a, ha, rfl⟩
    exact hfauto a
  have hBel : IsElemAbelian 2 (A.map f) := IsElemAbelian.map hA f
  have hB8 : 8 ≤ Nat.card (A.map f) := by
    rw [Subgroup.card_map_of_injective hfinj]
    exact h8
  have hBs6 : A.map f ≤ A6Facts.s6 :=
    w183finG4A6_model_e8_le_s6 (A.map f) hBauto hBel hB8
  intro a ha
  rw [hfs6]
  exact hBs6 ⟨a, ha, rfl⟩

theorem w183finG4A6_inn_sup_eq_autS6 {M : Type} [Group M]
    (e : M ≃* alternatingGroup (Fin 6)) :
    ∀ A : Subgroup (MulAut M), IsElemAbelian 2 A → 8 ≤ Nat.card A →
      innAutOf M ⊔ A = w183finG4A6AutS6 e := by
  intro A hA h8
  obtain ⟨f, hfinj, hfauto, hfsurj, hfinn, hfs6⟩ := w183finG4A6_exists_model e
  have hAle : A ≤ w183finG4A6AutS6 e := w183finG4A6_elemAbelian_le_autS6 e A hA h8
  have hInnle : innAutOf M ≤ w183finG4A6AutS6 e := by
    intro γ hγ
    rw [hfs6]
    exact A6Facts.psl29_le_s6 ((hfinn γ).1 hγ)
  have hBauto : A.map f ≤ A6Models.autA6 := by
    rintro b ⟨a, ha, rfl⟩
    exact hfauto a
  have hBel : IsElemAbelian 2 (A.map f) := IsElemAbelian.map hA f
  have hB8 : 8 ≤ Nat.card (A.map f) := by
    rw [Subgroup.card_map_of_injective hfinj]
    exact h8
  have hBs6 : A.map f ≤ A6Facts.s6 :=
    w183finG4A6_model_e8_le_s6 (A.map f) hBauto hBel hB8
  have hmodel : A6Models.psl29 ⊔ A.map f = A6Facts.s6 :=
    w183finG4A6_model_psl_sup (A.map f) hBs6 hBel hB8
  have hmap_sup : (innAutOf M ⊔ A).map f = A6Facts.s6 := by
    rw [Subgroup.map_sup (innAutOf M) A f, w183finG4A6_map_psl29 hfsurj hfinn]
    exact hmodel
  have hmapAutS6 : (w183finG4A6AutS6 e).map f = A6Facts.s6 :=
    w183finG4A6_map_s6 e hfsurj hfs6
  have hmap_le : (w183finG4A6AutS6 e).map f ≤ (innAutOf M ⊔ A).map f := by
    rw [hmapAutS6, hmap_sup]
  exact le_antisymm (sup_le hInnle hAle)
    ((Subgroup.map_le_map_iff_of_injective hfinj).mp hmap_le)

end CFSG.LocalAnalysis.WeakClosure81

end
