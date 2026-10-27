module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Vec

variable {hc : Ctx M Q Z B} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
  {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}

@[expose, instance_reducible] def Sec8Pts.vecAct (_h : Sec8Pts hc t r m K φ u u') :
    DistribMulAction ↥(Rt M (LB M Q B) t) (Fin m ⊕ Fin m → K) where
  smul ρ a := (φ ρ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ a
  one_smul a := by
    show ((φ 1 : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ a = a
    rw [map_one]
    simp
  mul_smul ρ σ a := by
    show ((φ (ρ * σ) : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ a =
      (φ ρ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        ((φ σ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ a)
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  smul_zero ρ := Matrix.mulVec_zero _
  smul_add ρ a b := Matrix.mulVec_add _ _ _

theorem Sec8Pts.isSecMod [CharP K 2] (h : Sec8Pts hc t r m K φ u u') :
    ∃ κ : ↥(Vt M (LB M Q B) B Z t) →* Multiplicative (Fin m ⊕ Fin m → K),
      @IsSecMod G _ (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (Fin m ⊕ Fin m → K) _
        h.vecAct κ := by
  obtain ⟨-, hN, ψ, hψ⟩ := h.act
  haveI := hN
  refine ⟨ψ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf (Vt M (LB M Q B) B Z t))), ?_⟩
  refine @IsSecMod.mk G _ (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (Fin m ⊕ Fin m → K) _
    h.vecAct _ ?_ ?_ ?_ ?_
  · intro a
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ψ.symm a)
    exact ⟨x, by simp [hx]⟩
  · intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro ρ x y hxy
    have := hψ ρ x y hxy
    refine Multiplicative.toAdd.injective ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      toAdd_ofAdd]
    exact this
  · intro a
    funext i
    simp [CharTwo.add_self_eq_zero]

end Vec

end CFSG.RankThree.GF2n.Stroth80
