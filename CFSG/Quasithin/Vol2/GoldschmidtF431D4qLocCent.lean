module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocBase

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique
  CFSG.Quasithin

set_option linter.unusedSectionVars false

section FieldActor

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem units_map_entrywiseHom_pinnedX_one_d4 (δ : K ≃+* K) (α : Fin TwistTag.D4.tag.rank → ℤ) :
    Units.map (entrywiseHom δ.toRingHom) (pinnedX TwistTag.D4.tag K α 1) =
      pinnedX TwistTag.D4.tag K α 1 :=
  Units.ext ((entrywise_pinnedX _ _ _).trans (by rw [map_one]))

theorem fieldActor_zC (δ : K ≃+* K) : fieldActor σ δ (zC σ) = zC σ := by
  apply Subtype.ext
  rw [coe_fieldActor]
  exact units_map_entrywiseHom_pinnedX_one_d4 δ _

theorem fieldActor_tC (hσ : ∀ c, σ (σ (σ c)) = c) (δ : K ≃+* K) :
    fieldActor σ δ (tC σ hσ) = tC σ hσ := by
  apply Subtype.ext
  rw [coe_fieldActor]
  show Units.map (entrywiseHom δ.toRingHom) (d4x₄ K σ 1) = d4x₄ K σ 1
  rw [d4x₄, coe_trialityOrbitProd, map_mul, map_mul]
  simp only [map_one, units_map_entrywiseHom_pinnedX_one_d4]

end FieldActor

theorem conj_mul_mem_autStab {G : Type} [Group G] {P : Subgroup G} {g : G} (hg : g ∈ P)
    {ψ : MulAut G} (hψ : ψ ∈ autStab P) : MulAut.conj g * ψ ∈ autStab P := by
  intro x
  rw [MulAut.mul_apply, MulAut.conj_apply, hψ x]
  constructor
  · intro hx
    exact P.mul_mem (P.mul_mem hg hx) (P.inv_mem hg)
  · intro hx
    have := P.mul_mem (P.mul_mem (P.inv_mem hg) hx) hg
    simpa [mul_assoc] using this

section Stab

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
  {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
  (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

@[expose] noncomputable def MbSt (Kb : Subgroup (MulAut (Cm σ))) (P : Subgroup (Cm σ)) :
    Subgroup ↥Kb :=
  (Kb ⊓ autStab P).subgroupOf Kb

theorem mem_MbSt {Kb : Subgroup (MulAut (Cm σ))} {P : Subgroup (Cm σ)} {φ : ↥Kb} :
    φ ∈ MbSt σ Kb P ↔ (φ : MulAut (Cm σ)) ∈ autStab P :=
  ⟨fun h => (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2,
    fun h => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨φ.2, h⟩)⟩

variable (Kb : Subgroup (MulAut (Cm σ)))
  (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)

end Stab

end CFSG.Quasithin.H13.F431.D4q.Loc
