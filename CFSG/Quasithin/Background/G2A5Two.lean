module

public import CFSG.Quasithin.Background.G2A5Setting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A5Model
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

namespace A5SettingCore

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5SettingCore V V₁ L T H)

include S

omit [Finite G] in
theorem theta_not_mem_A4s {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) : S.D.θ ⟨g, hg⟩ ∉ A4s :=
  S.D.theta_not_mem_A4s (le_conjClosure V₁ L) hg hgN

theorem Phi_I_surjective {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    ∀ A : A5, ∃ i : ↥(L ⊔ conjClosure V H),
      (i : G) ∈ conjClosure V H ⊔ rconj (conjClosure V H) g ∧ S.Phi i = A := by
  set U := conjClosure V H with hU
  let J : Subgroup A5 := ((U ⊔ rconj U g).subgroupOf (L ⊔ U)).map S.Phi
  have hgLU : g ∈ L ⊔ U := (le_sup_left : L ≤ L ⊔ U) hg
  have hJ1 : K4 ≤ J := by
    rw [← S.Ubar_eq_K4]
    rintro _ ⟨u, rfl⟩
    exact ⟨⟨u, (le_sup_right : U ≤ L ⊔ U) u.2⟩,
      Subgroup.mem_subgroupOf.2 ((le_sup_left : U ≤ U ⊔ rconj U g) u.2), rfl⟩
  have hJ2 : ∀ k ∈ K4, (S.D.θ ⟨g, hg⟩)⁻¹ * k * S.D.θ ⟨g, hg⟩ ∈ J := by
    intro k hk
    rw [← S.Ubar_eq_K4] at hk
    obtain ⟨u, rfl⟩ := hk
    have hu : (u : G) ∈ L ⊔ U := (le_sup_right : U ≤ L ⊔ U) u.2
    have hgu : g⁻¹ * u * g ∈ U ⊔ rconj U g :=
      (le_sup_right : rconj U g ≤ U ⊔ rconj U g) (inv_mul_mul_mem_rconj u.2)
    have hguLU : g⁻¹ * u * g ∈ L ⊔ U :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hgLU) hu) hgLU
    refine ⟨⟨g⁻¹ * u * g, hguLU⟩, Subgroup.mem_subgroupOf.2 hgu, ?_⟩
    have h1 : (⟨g⁻¹ * u * g, hguLU⟩ : ↥(L ⊔ U)) = ⟨g, hgLU⟩⁻¹ * ⟨u, hu⟩ * ⟨g, hgLU⟩ :=
      Subtype.ext (by simp)
    rw [h1, map_mul, map_mul, map_inv, S.Phi_of_L ⟨g, hg⟩]
    rfl
  have hkl4 : ∀ a ∈ kl 4, ∃ ha : a.sign = 1,
      (⟨a, Equiv.Perm.mem_alternatingGroup.2 ha⟩ : A5) ∈ K4 := by
    intro a ha
    have h := (kl_four a).1 ha
    exact ⟨sign_klein a h, h⟩
  intro A
  have hA : A ∈ J := by
    set x : Equiv.Perm (Fin 5) := ((S.D.θ ⟨g, hg⟩ : A5) : Equiv.Perm (Fin 5)) with hx
    have hx4 : x 4 ≠ 4 := fun h => S.theta_not_mem_A4s hg hgN h
    have hp : x⁻¹ 4 ≠ 4 := fun h => hx4 (by
      rw [Equiv.Perm.inv_eq_iff_eq] at h
      exact h.symm)
    obtain ⟨a₁, ha₁, b₁, hb₁, a₂, ha₂, b₂, hb₂, hAeq⟩ :=
      kl_gen (x⁻¹ 4) hp (A : Equiv.Perm (Fin 5)) (Equiv.Perm.mem_alternatingGroup.1 A.2)
    obtain ⟨hsa₁, hKa₁⟩ := hkl4 a₁ ha₁
    obtain ⟨hsa₂, hKa₂⟩ := hkl4 a₂ ha₂
    obtain ⟨k₁, hk₁, hbk₁⟩ := kl_conj_cover x b₁ hb₁
    obtain ⟨k₂, hk₂, hbk₂⟩ := kl_conj_cover x b₂ hb₂
    obtain ⟨hsk₁, hKk₁⟩ := hkl4 k₁ hk₁
    obtain ⟨hsk₂, hKk₂⟩ := hkl4 k₂ hk₂
    have hJb₁ : (⟨b₁, by
        rw [hbk₁]
        exact Equiv.Perm.mem_alternatingGroup.2 (by simp [hsk₁, Equiv.Perm.sign_mul,
          Equiv.Perm.sign_inv])⟩ : A5) ∈ J := by
      have := hJ2 _ hKk₁
      convert this using 1
      apply Subtype.ext
      simp [hbk₁, hx]
    have hJb₂ : (⟨b₂, by
        rw [hbk₂]
        exact Equiv.Perm.mem_alternatingGroup.2 (by simp [hsk₂, Equiv.Perm.sign_mul,
          Equiv.Perm.sign_inv])⟩ : A5) ∈ J := by
      have := hJ2 _ hKk₂
      convert this using 1
      apply Subtype.ext
      simp [hbk₂, hx]
    have hAprod : A = ⟨a₁, Equiv.Perm.mem_alternatingGroup.2 hsa₁⟩ *
        ⟨b₁, by
          rw [hbk₁]
          exact Equiv.Perm.mem_alternatingGroup.2 (by simp [hsk₁, Equiv.Perm.sign_mul,
            Equiv.Perm.sign_inv])⟩ *
        ⟨a₂, Equiv.Perm.mem_alternatingGroup.2 hsa₂⟩ *
        ⟨b₂, by
          rw [hbk₂]
          exact Equiv.Perm.mem_alternatingGroup.2 (by simp [hsk₂, Equiv.Perm.sign_mul,
            Equiv.Perm.sign_inv])⟩ := Subtype.ext hAeq
    rw [hAprod]
    exact J.mul_mem (J.mul_mem (J.mul_mem (hJ1 hKa₁) hJb₁) (hJ1 hKa₂)) hJb₂
  obtain ⟨i, hi, rfl⟩ := hA
  exact ⟨i, Subgroup.mem_subgroupOf.1 hi, rfl⟩

theorem G24_two_aux {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    conjClosure V H ⊔ rconj (conjClosure V H) g = L ⊔ conjClosure V H := by
  set U := conjClosure V H with hU
  have hdec : ∀ x ∈ L ⊔ U, ∃ o ∈ pCoreOf 2 (L ⊔ T) ⊓ (L ⊔ U), ∃ i ∈ U ⊔ rconj U g,
      x = o * i := by
    intro x hx
    obtain ⟨i, hiI, hi⟩ := S.Phi_I_surjective hg hgN (S.Phi ⟨x, hx⟩)
    refine ⟨x * (i : G)⁻¹, ⟨?_, ?_⟩, i, hiI, by group⟩
    · have h1 : S.Phi (⟨x, hx⟩ * i⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hi, mul_inv_cancel]
      exact (S.Phi_eq_one_iff _).1 h1
    · exact Subgroup.mul_mem _ hx (inv_mem i.2)
  exact eq_sup_of_normal_closure (T₀ := pCoreOf 2 (L ⊔ T) ⊓ (L ⊔ U)) S.hyp.base.oTwo_eq hg rfl
    (fun x hx => S.hyp.G22_three.2 (S.O_le_T hx.1))
    ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_left) inf_le_right hdec

end A5SettingCore

namespace A5Setting

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5Setting V V₁ L T H)

include S

omit [Finite G] in
theorem theta_not_mem_A4s {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) : S.D.θ ⟨g, hg⟩ ∉ A4s :=
  S.D.theta_not_mem_A4s (le_conjClosure V₁ L) hg hgN

theorem Phi_I_surjective {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    ∀ A : A5, ∃ i : ↥(L ⊔ conjClosure V H),
      (i : G) ∈ conjClosure V H ⊔ rconj (conjClosure V H) g ∧ S.Phi i = A :=
  S.toCore.Phi_I_surjective hg hgN

theorem G24_two_aux {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    conjClosure V H ⊔ rconj (conjClosure V H) g = L ⊔ conjClosure V H := S.toCore.G24_two_aux hg hgN

end A5Setting

namespace AlmostSpecialA5Core

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Core V V₁ L T H)

include hyp

theorem G24_two {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    conjClosure V H ⊔ rconj (conjClosure V H) g = L ⊔ conjClosure V H := by
  obtain ⟨D⟩ := hyp.natural.nonempty_natData5 hyp.base.le_V (le_conjClosure V₁ L) hyp.card_V₁
    hyp.V_eq
  let S : A5SettingCore V V₁ L T H := ⟨hyp, D⟩
  exact S.G24_two_aux hg hgN

end AlmostSpecialA5Core

namespace AlmostSpecialA5Hyp

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Hyp V V₁ L T H)

include hyp

theorem G24_two {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    conjClosure V H ⊔ rconj (conjClosure V H) g = L ⊔ conjClosure V H := hyp.toCore.G24_two hg hgN

end AlmostSpecialA5Hyp

end CFSG.Quasithin
