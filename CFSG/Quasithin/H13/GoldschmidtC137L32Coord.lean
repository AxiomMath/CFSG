module

public import CFSG.Quasithin.H13.GoldschmidtC137L32Blk
public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.Quasithin.L3 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

@[expose] noncomputable def vecMapK {F : Type} [Field F] (σ : F ≃+* ZMod 2) (j : ℕ) :
    Multiplicative (Fin j → Fin 3 → F) ≃* Multiplicative (Fin j → Fin 3 → ZMod 2) :=
  AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ =>
    AddEquiv.piCongrRight fun _ => σ.toAddEquiv)

theorem card_eq_two_of_modO2Surj [Finite G] {L : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168) {α : ↥L →* ↥(StatedSL 3 F)}
    (hα : IsModO2Surj L α) : Nat.card F = 2 := by
  have : Finite F := Finite.of_fintype F
  apply card_eq_two_of_card_SL3
  rw [Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα.1).toEquiv,
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hα.2).toEquiv]
  exact hcard

theorem exists_coords [Finite G] {L M : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168) {α : ↥L →* ↥(StatedSL 3 F)}
    (hα : IsModO2Surj L α) {j : ℕ} (hM : IsSumOfNaturalModulesVia L M ⊥ α false j) :
    ∃ (α'' : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (β' : ↥M ≃* Multiplicative (Fin j → Vec)),
      Function.Surjective α'' ∧ α''.ker = CFSG.pCore 2 ↥L ∧ L ≤ normalizer (M : Set G) ∧
      ∀ (l : ↥L) (u v : ↥M), (v : G) = l * u * l⁻¹ → ∀ i,
        Multiplicative.toAdd (β' v) i = act (α'' l) (Multiplicative.toAdd (β' u) i) := by
  obtain ⟨hLM, -, β, hβs, hβker, hβeq⟩ := hM
  have hF2 := card_eq_two_of_modO2Surj hcard hα
  obtain ⟨σ⟩ : Nonempty (F ≃+* ZMod 2) := by
    let _ : Fintype F := Fintype.ofFinite F
    exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hF2]; simp)⟩
  let e2 : StatedSL 3 (ZMod 2) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  have hmap_coe : ∀ γ : StatedSL 3 (ZMod 2),
      ((e2 γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        ((γ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro γ
    have := specialLinearGroupEquivStatedSL_coe 3 (ZMod 2) (e2 γ)
    rw [show specialLinearGroupEquivStatedSL 3 (ZMod 2) (e2 γ) = γ from
      MulEquiv.apply_symm_apply _ _] at this
    exact this.symm
  refine ⟨(e2.toMonoidHom.comp (statedSLMap σ).toMonoidHom).comp α,
    MulEquiv.ofBijective ((vecMapK σ j).toMonoidHom.comp β)
      ⟨(vecMapK σ j).injective.comp hβinj, (vecMapK σ j).surjective.comp hβs⟩, ?_, ?_, hLM, ?_⟩
  · exact (e2.surjective.comp (statedSLMap σ).surjective).comp hα.1
  · rw [MonoidHom.ker_comp_of_injective _ (e2.toMonoidHom.comp (statedSLMap σ).toMonoidHom)
      (e2.injective.comp (statedSLMap σ).injective)]
    exact hα.2
  · intro l u v huv i
    have h1 := hβeq l u v huv i
    funext p
    show σ (Multiplicative.toAdd (β v) i p) = _
    rw [h1]
    have h2 := RingHom.map_mulVec σ.toRingHom
      ((moduleAct false (α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
      (Multiplicative.toAdd (β u) i) p
    have h3 : moduleAct false (α l : GL (Fin 3) F) = ((α l : GL (Fin 3) F) : Matrix _ _ F) := by
      simp [moduleAct]
    rw [h3] at h2
    show _ = ((((e2 (statedSLMap σ (α l)) :
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))).mulVec
        (fun q => σ (Multiplicative.toAdd (β u) i q))) p
    rw [hmap_coe, statedSLMap_coe]
    exact h2

end CFSG.Quasithin.H13.U3.GC137
