module

public import CFSG.LieType.SteinbergBROddLinearThreeParabolic
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem card_eq_two_of_card_SL3 {F : Type} [Field F] [Finite F]
    (h : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 168) : Nat.card F = 2 := by
  rw [CFSG.LieType.SteinbergBR.BlockPar.card_SL_three'] at h
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  by_contra hne
  have h3 : 3 ≤ Nat.card F := by omega
  set q := Nat.card F with hqdef
  have h27 : 27 ≤ q ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left h3 3
  have h9 : 9 ≤ q ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left h3 2
  have h8 : 8 ≤ q ^ 2 - 1 := by omega
  have h26 : 26 ≤ q ^ 3 - 1 := by omega
  have : 27 * (8 * 26) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    Nat.mul_le_mul h27 (Nat.mul_le_mul h8 h26)
  omega

@[expose] noncomputable def slMap {F : Type} [Field F] (σ : F ≃+* ZMod 2) :
    Matrix.SpecialLinearGroup (Fin 3) F ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map σ.toRingHom)
    (Matrix.SpecialLinearGroup.map σ.symm.toRingHom)
    (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])

@[expose] noncomputable def statedSLMap {F : Type} [Field F] (σ : F ≃+* ZMod 2) :
    StatedSL 3 F ≃* StatedSL 3 (ZMod 2) :=
  (specialLinearGroupEquivStatedSL 3 F).symm.trans
    ((slMap σ).trans (specialLinearGroupEquivStatedSL 3 (ZMod 2)))

theorem statedSLMap_coe {F : Type} [Field F] (σ : F ≃+* ZMod 2) (γ : StatedSL 3 F) :
    ((statedSLMap σ γ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ := by
  obtain ⟨s, rfl⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective γ
  show ((specialLinearGroupEquivStatedSL 3 (ZMod 2)
      (slMap σ ((specialLinearGroupEquivStatedSL 3 F).symm
        (specialLinearGroupEquivStatedSL 3 F s))) : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [MulEquiv.symm_apply_apply, specialLinearGroupEquivStatedSL_coe,
    specialLinearGroupEquivStatedSL_coe]
  exact Matrix.SpecialLinearGroup.map_apply_coe σ.toRingHom s

@[expose] noncomputable def vecMap {F : Type} [Field F] (σ : F ≃+* ZMod 2) :
    Multiplicative (Fin 3 → F) ≃* Multiplicative (Fin 3 → ZMod 2) :=
  AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)

theorem isLnBlock_of_isSL3Block {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168) (hB : IsSL3Block L) : IsLnBlock L 3 := by
  obtain ⟨hshort, n, F, hF, hFin, hFcard, α, hα, hker, β, hβ, hβker, hβeq⟩ := hB
  have : Finite F := Finite.of_fintype F
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 168 := by
    rw [Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv]
    exact hcard
  have hF2 : Nat.card F = 2 := card_eq_two_of_card_SL3 hSL
  obtain ⟨σ⟩ : Nonempty (F ≃+* ZMod 2) := by
    let _ : Fintype F := Fintype.ofFinite F
    exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hF2]; simp)⟩
  refine ⟨hshort, (statedSLMap σ).toMonoidHom.comp α, ?_, ?_, (vecMap σ).toMonoidHom.comp β,
    ?_, ?_, ?_⟩
  · exact (statedSLMap σ).surjective.comp hα
  · rw [MonoidHom.ker_comp_of_injective α (statedSLMap σ).toMonoidHom (statedSLMap σ).injective]
    exact hker
  · exact (vecMap σ).surjective.comp hβ
  · rw [MonoidHom.ker_comp_of_injective β (vecMap σ).toMonoidHom (vecMap σ).injective]
    exact hβker
  · intro ℓ u v huv
    have h1 := hβeq ℓ u v huv
    funext i
    have h2 := RingHom.map_mulVec σ.toRingHom
      ((α ℓ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (Multiplicative.toAdd (β u)) i
    show σ (Multiplicative.toAdd (β v) i) =
      ((((statedSLMap σ (α ℓ)) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (fun j => σ (Multiplicative.toAdd (β u) j))) i
    rw [h1, statedSLMap_coe]
    exact h2

end CFSG.Quasithin.H13.U3.GC137
