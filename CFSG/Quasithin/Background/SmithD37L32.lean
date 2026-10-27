module

public import CFSG.Quasithin.Background.SmithD37Real
public import CFSG.Quasithin.Background.SmithD37Core
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.Assembly.LowTwoRank
open scoped Matrix

section Two

variable {K : Type} [Field K]

private theorem units_eq_one_of_natCard_two (hK : Nat.card K = 2) (c : Kˣ) : c = 1 := by
  have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim c 1

private theorem statedSL_eq_top_of_natCard_two (hK : Nat.card K = 2) (n : ℕ) :
    StatedSL n K = ⊤ := by
  rw [eq_top_iff]
  intro A _
  apply Subgroup.subset_closure
  show (A : Matrix (Fin n) (Fin n) K).det = 1
  rw [← Matrix.GeneralLinearGroup.val_det_apply,
    units_eq_one_of_natCard_two hK (Matrix.GeneralLinearGroup.det A), Units.val_one]

private theorem statedScalars_subgroupOf_eq_bot_of_natCard_two (hK : Nat.card K = 2) (n : ℕ) :
    (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨c, hc⟩
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [show (g : Matrix.GeneralLinearGroup (Fin n) K) = _ from hc.symm,
    units_eq_one_of_natCard_two hK c, map_one]
  rfl

private noncomputable def statedProjEquivOfNatCardTwo (hK : Nat.card K = 2) (n : ℕ) :
    StatedProj (StatedSL n K) ≃* ↥(StatedSL n K) :=
  (QuotientGroup.quotientMulEquivOfEq
    (statedScalars_subgroupOf_eq_bot_of_natCard_two hK n)).trans QuotientGroup.quotientBot

private noncomputable def glEquivStatedSLOfNatCardTwo (hK : Nat.card K = 2) (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) K ≃* ↥(StatedSL n K) :=
  Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr (statedSL_eq_top_of_natCard_two hK n).symm)

private theorem isPSL_three_two_of_mulEquiv_statedSL {X : Type} [Group X]
    (hK : Nat.card K = 2) (e : X ≃* ↥(StatedSL 3 K)) : IsPSL 3 2 1 X :=
  ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, K, inferInstance,
    Nat.finite_of_card_ne_zero (by omega), hK.trans (pow_one 2).symm,
    ⟨e.trans (statedProjEquivOfNatCardTwo hK 3).symm⟩⟩

end Two

section Seven

theorem natCard_of_isPSL_two_seven {X : Type} [Group X] (h : IsPSL 2 7 1 X) :
    Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven h

end Seven

section Main

private theorem range_subtype_comp_eq {G H : Type} [Group G] [Group H] (L : Subgroup H)
    (S : Subgroup G) (hS : S = ⊤) (ψ : G ≃* ↥L) :
    (L.subtype.comp (ψ.toMonoidHom.comp S.subtype)).range = L := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact (ψ g).2
  · intro hx
    refine ⟨⟨ψ.symm ⟨x, hx⟩, hS ▸ Subgroup.mem_top _⟩, ?_⟩
    simp

theorem l32_of_dim_three {U : Type} [CommGroup U] [Finite U] {L₁ L₂ : Subgroup (MulAut U)}
    {F : Type} [Field F] [Fintype F] (Mm : MatModel L₁ L₂ F 3) (hF : Nat.card F = 2)
    (h₁ : Nat.card ↥L₁ = 168) (h₂ : Nat.card ↥L₂ = 168) :
    IsPSL 3 2 1 ↥L₁ ∧ TensorNatL32 (L₁ ⊔ L₂) := by
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) F) = 168 := by
    rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hF, Fin.prod_univ_three]
    norm_num
  set e₁ := MulEquiv.ofBijective Mm.R₁ (Mm.inj₁.bijective_of_nat_card_le (by rw [hGL, h₁]))
  set e₂ := MulEquiv.ofBijective Mm.R₂ (Mm.inj₂.bijective_of_nat_card_le (by rw [hGL, h₂]))
  refine ⟨isPSL_three_two_of_mulEquiv_statedSL hF
    (e₁.trans (glEquivStatedSLOfNatCardTwo hF 3)), ?_⟩
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF]
  set ε : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hc
  set μ : Matrix (Fin 3) (Fin 3) F ≃+* Matrix (Fin 3) (Fin 3) (ZMod 2) := ε.mapMatrix
  set γ : Matrix.GeneralLinearGroup (Fin 3) F ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    Units.mapEquiv μ.toMulEquiv
  have hγ : ∀ g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2),
      ((γ.symm g : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        μ.symm (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := fun _ => rfl
  have hS : StatedSL 3 (ZMod 2) = ⊤ := statedSL_eq_top_of_natCard_two (Nat.card_zmod 2) 3
  set β : U ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    Mm.β.trans (AddEquiv.toMultiplicative μ.toAddEquiv)
  have hβ : ∀ u, β u = Multiplicative.ofAdd (μ (Multiplicative.toAdd (Mm.β u))) := fun _ => rfl
  refine tensorNat_realizes_of_pair L₁ L₂ β
    (L₁.subtype.comp ((γ.symm.trans e₁.symm).toMonoidHom.comp (StatedSL 3 (ZMod 2)).subtype))
    (L₂.subtype.comp ((γ.symm.trans e₂.symm).toMonoidHom.comp (StatedSL 3 (ZMod 2)).subtype))
    (range_subtype_comp_eq L₁ _ hS _) (range_subtype_comp_eq L₂ _ hS _) ?_ ?_
  · intro g u
    have h := Mm.act₁ (e₁.symm (γ.symm g)) u
    rw [show Mm.R₁ (e₁.symm (γ.symm g)) = γ.symm g from e₁.apply_symm_apply _, hγ] at h
    rw [hβ, hβ]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype, MulEquiv.trans_apply]
    rw [h, toAdd_ofAdd, toAdd_ofAdd, map_mul, RingEquiv.apply_symm_apply]
  · intro g u
    have h := Mm.act₂ (e₂.symm (γ.symm g)) u
    rw [show Mm.R₂ (e₂.symm (γ.symm g)) = γ.symm g from e₂.apply_symm_apply _, hγ] at h
    rw [hβ, hβ]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype, MulEquiv.trans_apply]
    have hT : ∀ M : Matrix (Fin 3) (Fin 3) F, μ Mᵀ = (μ M)ᵀ := fun M =>
      Matrix.transpose_map (f := ⇑ε) (M := M)
    rw [h, toAdd_ofAdd, toAdd_ofAdd, map_mul, hT, RingEquiv.apply_symm_apply]

end Main

end CFSG.Quasithin.SmithD37
