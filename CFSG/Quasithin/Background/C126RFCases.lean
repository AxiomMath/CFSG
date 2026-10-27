module

public import CFSG.Quasithin.Background.C126RFSurj
public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.Adapters.LinearSmallCatalog

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2

@[expose] def PType {A : Type*} [Group A] (P : Subgroup A) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
    Nonempty (↥P ≃* alternatingGroup (Fin 5))

theorem PType.nontrivial {A : Type*} [Group A] {P : Subgroup A} (h : PType P) : Nontrivial ↥P := by
  rcases h with ⟨n, hn, F, _, _, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have := nontrivial_sl2 (F := F)
    exact e.toEquiv.nontrivial
  · exact e.toEquiv.nontrivial

theorem isPSL_two_two_two_of_alternating_five (X : Type) [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 5))) : CFSG.Quasithin.IsPSL 2 2 2 X := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hcard]; norm_num))
  exact ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hcard, ⟨e.trans e5.symm⟩⟩

theorem a134_of_surjective {Y A : Type} [Group Y] [Group A]
    (hY : CFSG.Open.IsQuasisimple Y) {P : Subgroup A} (hP : PType P) (f : Y →* ↥P)
    (hf : Function.Surjective f) : A134TypesCentral Y := by
  have hnt := hP.nontrivial
  rcases hP with ⟨n, hn, F, _, _, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨n, isPSL_two_two_quot_center hY f hf hn hF e⟩
  · obtain ⟨e1⟩ := nonempty_quot_center_mulEquiv hY f hf
      (center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by simp)))
    exact Or.inl ⟨2, isPSL_two_two_two_of_alternating_five _ ⟨e1.trans e⟩⟩

theorem iSup_le_normalizer {A : Type*} [Group A] (I : Finset (Subgroup A))
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    {L₀ : Subgroup A} (hL₀ : L₀ ∈ I) {B : Subgroup A} (hBL : B ≤ L₀)
    (hB : L₀ ≤ Subgroup.normalizer (B : Set A)) :
    (⨆ L ∈ I, L) ≤ Subgroup.normalizer (B : Set A) := by
  refine iSup₂_le fun L hL => ?_
  by_cases hLe : L = L₀
  · rw [hLe]
    exact hB
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    have hc : ∀ c ∈ B, a * c = c * a := fun c hc => hcomm L hL L₀ hL₀ hLe a ha c (hBL hc)
    constructor
    · intro hb
      have h2 : a * b * a⁻¹ = b := by
        rw [hc b hb]
        group
      rw [h2]
      exact hb
    · intro hb
      have h1 := hc _ hb
      have h2 : a * b * a⁻¹ = b := by
        have h3 : a * (a * b * a⁻¹) = a * b := by
          rw [h1]
          group
        exact mul_left_cancel h3
      rw [h2] at hb
      exact hb

section Family

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_perfect_normalized {H T V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : NatCase H T V hV ∨ A5Case H T V hV) :
    ∃ P : Subgroup (MulAut (IntMod V hV)), PType P ∧ Group.IsPerfect ↥P ∧
      P ≤ autI hV (thompsonJ H) ∧ autI hV (thompsonJ H) ≤ Subgroup.normalizer (P : Set _) := by
  rcases h with ⟨-, I, hfam, hnat⟩ | ⟨-, I, hfam, ha5⟩
  · obtain ⟨hcard, hJ, hcomm, -⟩ := hfam
    obtain ⟨L₀, hL₀⟩ : I.Nonempty := by
      rcases hcard with h | h <;> exact Finset.card_pos.1 (by omega)
    obtain ⟨n, hn, -, F, hFf, hFi, hF, e, -⟩ := hnat L₀ hL₀
    refine ⟨L₀, Or.inl ⟨n, hn, F, hFf, Finite.of_fintype F, ?_, ⟨e⟩⟩,
      isPerfect_of_sl2_equiv hn hF e, ?_, ?_⟩
    · rw [Nat.card_eq_fintype_card, hF]
    · rw [hJ]
      exact le_iSup₂ (f := fun L _ => L) L₀ hL₀
    · rw [hJ]
      exact iSup_le_normalizer I hcomm hL₀ le_rfl Subgroup.le_normalizer
  · obtain ⟨hcard, hJ, hcomm, -⟩ := hfam
    obtain ⟨L₀, hL₀⟩ : I.Nonempty := by
      rcases hcard with h | h <;> exact Finset.card_pos.1 (by omega)
    obtain ⟨θ, -⟩ := ha5 L₀ hL₀
    set φ : Equiv.Perm (Fin 5) →* MulAut (IntMod V hV) := L₀.subtype.comp θ.symm.toMonoidHom
      with hφdef
    have hφ : Function.Injective φ := L₀.subtype_injective.comp θ.symm.injective
    set P : Subgroup (MulAut (IntMod V hV)) := (alternatingGroup (Fin 5)).map φ with hPdef
    have e : ↥(alternatingGroup (Fin 5)) ≃* ↥P := Subgroup.equivMapOfInjective _ φ hφ
    have hPL : P ≤ L₀ := by
      rintro _ ⟨a, -, rfl⟩
      exact (θ.symm a).2
    have hnorm : (P.subgroupOf L₀).Normal := by
      refine ⟨fun x hx g => ?_⟩
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_map.2 ⟨θ g * a * (θ g)⁻¹,
        (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem a ha (θ g), ?_⟩
      have h1 : φ (θ g) = (g : MulAut (IntMod V hV)) := by simp [φ]
      rw [map_mul, map_mul, map_inv, h1, hax]
      rfl
    have hperfA : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    have hperf : Group.IsPerfect ↥P :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    refine ⟨P, Or.inr ⟨e.symm⟩, hperf, ?_, ?_⟩
    · rw [hJ]
      exact hPL.trans (le_iSup₂ (f := fun L _ => L) L₀ hL₀)
    · rw [hJ]
      exact iSup_le_normalizer I hcomm hL₀ hPL
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hPL).1 hnorm)

end Family

end CFSG.Quasithin.C126
