module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3H
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open C11P9A

namespace C11P9A

theorem isSylowTwoOf_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {S : Subgroup G}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) :
    QuasithinUnique.IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hS.2.1.map _, ?_⟩
  rw [show ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.map e.toMonoidHom).index from
    Subgroup.relIndex_top_right _, Subgroup.index_map_of_bijective e.bijective]
  have h := hS.2.2
  rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h

theorem map_mem_sc_iff {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (φ : G →* G') (hφ : Function.Injective φ) (X : Subgroup G) (x : G) :
    φ x ∈ sectionCentralizer (X.map φ) (pCoreOf 2 (X.map φ)) ↔
      x ∈ sectionCentralizer X (pCoreOf 2 X) := by
  rw [pCoreOf_map_of_injective φ hφ]
  have h := map_inf_sectionCentralizer φ hφ ⊤ X (pCoreOf 2 X)
  constructor
  · intro hx
    have h1 : φ x ∈ (⊤ : Subgroup G).map φ ⊓
        sectionCentralizer (X.map φ) ((pCoreOf 2 X).map φ) := ⟨⟨x, trivial, rfl⟩, hx⟩
    rw [h] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rw [hφ hyx] at hy
    exact hy.2
  · intro hx
    have h1 : φ x ∈ ((⊤ : Subgroup G) ⊓ sectionCentralizer X (pCoreOf 2 X)).map φ :=
      ⟨x, ⟨trivial, hx⟩, rfl⟩
    rw [← h] at h1
    exact h1.2

theorem map_commutator_top {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆.map e.toMonoidHom =
      ⁅(⊤ : Subgroup G'), (⊤ : Subgroup G')⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]

theorem exists_equiv_S0P {R : Type} [Group R] {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (e : R ≃* PGL3 F) {S : Subgroup R}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ e' : R ≃* PGL3 F, S.map e'.toMonoidHom = S0P F := by
  obtain ⟨c, hc⟩ := exists_conj_S0P hF (isSylowTwoOf_map e hS)
  refine ⟨e.trans (MulAut.conj c⁻¹), ?_⟩
  have h1 : (e.trans (MulAut.conj c⁻¹)).toMonoidHom =
      (MulAut.conj c⁻¹).toMonoidHom.comp e.toMonoidHom := MonoidHom.ext fun _ => rfl
  have h2 : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      MonoidHom.id (PGL3 F) := by
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  rw [h1, ← Subgroup.map_map, hc, Subgroup.map_map, h2, Subgroup.map_id]

theorem map_eq_Ptheta {R : Type} [Group R] [Finite R] {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 4) (e : R ≃* PGL3 F) {S P : Subgroup R}
    (he : S.map e.toMonoidHom = S0P F) (hP1 : P ≠ ⊥) (hPp : ⁅P, P⁆ = P)
    (hPc : P ≠ ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆)
    (hSP : S ≤ Subgroup.normalizer (P : Set R)) :
    P.map e.toMonoidHom = Ptheta F 0 ∨ P.map e.toMonoidHom = Ptheta F 1 := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine classify_pgl hF ?_ ?_ ?_ ?_
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]
  · rw [← Subgroup.map_commutator, hPp]
  · rw [← map_commutator_top e]
    exact fun h => hPc (Subgroup.map_injective hinj h)
  · rw [← he, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hSP

end C11P9A

theorem factPGL34Levi_holds : FactPGL34Levi := by
  intro R _ _ ⟨F, _, _, hF, ⟨e₀⟩⟩ S P₁ P₂ hS hne h₁ h₂ hp₁ hp₂ hc₁ hc₂ hSP₁ hSP₂ x hx hx3 hx₁
    hx₂
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2) (by norm_num) (by rw [hF]; norm_num)
  obtain ⟨e, he⟩ := exists_equiv_S0P hF (e₀ : R ≃* PGL3 F) hS
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hx' : e.toMonoidHom x ∈ Subgroup.normalizer (S0P F : Set (PGL3 F)) := by
    rw [← he, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨x, hx, rfl⟩
  have hx3' : orderOf (e.toMonoidHom x) = 3 := by rw [orderOf_injective _ hinj]; exact hx3
  have hx₁' := (map_mem_sc_iff _ hinj P₁ x).mpr hx₁
  have hx₂' := (map_mem_sc_iff _ hinj P₂ x).mpr hx₂
  have hne' : P₁.map e.toMonoidHom ≠ P₂.map e.toMonoidHom := fun h =>
    hne (Subgroup.map_injective hinj h)
  rcases map_eq_Ptheta hF e he h₁ hp₁ hc₁ hSP₁ with k₁ | k₁ <;>
    rcases map_eq_Ptheta hF e he h₂ hp₂ hc₂ hSP₂ with k₂ | k₂
  · exact hne' (k₁.trans k₂.symm)
  · rw [k₁] at hx₁'
    rw [k₂] at hx₂'
    exact false_of_mem_sc_both hF hx' hx3' hx₁' hx₂'
  · rw [k₁] at hx₁'
    rw [k₂] at hx₂'
    exact false_of_mem_sc_both hF hx' hx3' hx₂' hx₁'
  · exact hne' (k₁.trans k₂.symm)

theorem factPGL34Torus_holds : FactPGL34Torus := by
  intro R _ _ ⟨F, _, _, hF, ⟨e₀⟩⟩ S P₁ P₂ hS _ _ h₂ _ hp₂ _ hc₂ _ hSP₂ E hE hE9
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2) (by norm_num) (by rw [hF]; norm_num)
  obtain ⟨e, he⟩ := exists_equiv_S0P hF (e₀ : R ≃* PGL3 F) hS
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hE' : E.map e.toMonoidHom ≤ Subgroup.normalizer (S0P F : Set (PGL3 F)) := by
    rw [← he, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hE
  have hE9' : Nat.card ↥(E.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hE9
  have key : (E ⊓ sectionCentralizer P₂ (pCoreOf 2 P₂)).map e.toMonoidHom =
      E.map e.toMonoidHom ⊓ sectionCentralizer (P₂.map e.toMonoidHom)
        (pCoreOf 2 (P₂.map e.toMonoidHom)) := by
    rw [pCoreOf_map_of_injective _ hinj, map_inf_sectionCentralizer _ hinj]
  intro hbot
  rcases map_eq_Ptheta hF e he h₂ hp₂ hc₂ hSP₂ with k | k
  · apply exists_mem_sc hF 0 hE' hE9'
    rw [← k, ← key, hbot, Subgroup.map_bot]
  · apply exists_mem_sc hF 1 hE' hE9'
    rw [← k, ← key, hbot, Subgroup.map_bot]

end CFSG.Quasithin.Vol2.Ch11.SecS
