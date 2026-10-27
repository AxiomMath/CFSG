module

public import CFSG.Quasithin.EmptyFaithful.S143KG
public import CFSG.Quasithin.EmptyFaithful.S143KF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

section Model

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T)

include hS htT htRQ

theorem Setup.exists_model :
    ∃ (y : G) (hyH : y ∈ mcOf T) (cm : Mat4),
      y ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) ∧ y * y * y = 1 ∧
      (∀ v w : V4, vm v cm = vm w cm → v = w) ∧
      (∀ γ ∈ rOf T M, A6ok cm (cmat z a r r1 γ)) ∧
      (∀ u ∈ uOfL22 T M, A6ok cm (cmat z a r r1 u)) ∧
      A6ok cm (cmat z a r r1 x) ∧ A6ok cm (cmat z a r r1 y) ∧
      (closureCodes [cmat z a r r1 x, cmat z a r r1 y]).length = 360 ∧
      (∀ γ₁ ∈ rOf T M, ∀ u₁ ∈ uOfL22 T M, ∀ γ₂ ∈ rOf T M, ∀ u₂ ∈ uOfL22 T M,
        cmat z a r r1 γ₁ = cmat z a r r1 u₁ → cmat z a r r1 γ₁ ≠ I4 →
          cmat z a r r1 γ₂ = cmat z a r r1 u₂ → cmat z a r r1 γ₂ ≠ I4 →
            cmat z a r r1 γ₁ = cmat z a r r1 γ₂) ∧
      ∀ n : ↥(mcOf T), (n : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) →
        Odd (orderOf n) → ∃ i : ℕ, c.actK n = c.actK ⟨y, hyH⟩ ^ i := by
  obtain ⟨R1, R2, hR1, hR2, hRH, hR⟩ := hS.exists_RHyp htT htRQ
  obtain ⟨N1, N2, hN1, hN2, hUH, hU⟩ := hS.exists_UHyp htT htRQ hR
  obtain ⟨y, hyH, hyN, hy3, hyM, hYH, hodd⟩ := hS.exists_YHyp hU
  obtain ⟨cm, hcm, hRok, hUok, hxok, hyok, hcl, hinter⟩ :=
    model_main hR1 hR2 hRH hN1 hN2 hUH hyM hYH
  rw [← hS.cmat_x] at hxok hcl
  refine ⟨y, hyH, cm, hyN, hy3, hcm, ?_, ?_, hxok, hyok, hcl, ?_, hodd⟩
  · intro γ hγ
    exact hRok _ ((hR _).mpr ⟨γ, hγ, rfl⟩)
  · intro u hu
    exact hUok _ ((hU _).mpr ⟨u, hu, rfl⟩)
  · intro γ₁ hγ₁ u₁ hu₁ γ₂ hγ₂ u₂ hu₂ h1 h1' h2 h2'
    refine hinter _ ((hR _).mpr ⟨γ₁, hγ₁, rfl⟩) ((hU _).mpr ⟨u₁, hu₁, h1.symm⟩) h1' _
      ((hR _).mpr ⟨γ₂, hγ₂, rfl⟩) ((hU _).mpr ⟨u₂, hu₂, h2.symm⟩) h2'

end Model

end S143

end CFSG.Quasithin
