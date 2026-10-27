module

public import CFSG.Quasithin.Background.S1549CN1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem claim_n2 (h11 : StageLemma14111) (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t)
    {H : Subgroup G} (hb : InspBase cx H)
    (hno : ¬ ∃ A, @IsStrongFFStarOffender (UTil T M V₁ H) (modInst hb.hF98.toHypF91)
      (StarOf T M V₁ H H) A ∧ A ≤ StarOf T M V₁ H (pCoreOf 2 (Y0 T Mc M ⊔ T)))
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
      (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)))
    (hle : mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ≤
      mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G))) :
    VH T M H ≤ UH T M V₁ H ⊔
      F9.EH (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G) := by
  have h98 := hb.hF98
  obtain ⟨heq, -, -⟩ := claim_n1 h11 h113 cx hb hno s hpos hle
  have hlt := claim_g h113 cx hb.adm h98 hb.claimC s
  obtain ⟨δ, δ', k, y, sk, hy1, hy2, eU, eB, eDH, eDγ⟩ :=
    h98.exists_symmetric_setup s (h98.not_Vγ_le_ballStab_of_lt s hlt)
  have m1 : mIdx (F8.Uγ (ZS153 T M V₁) H (k : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (k : G)) =
      mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) := by
    rw [eU, eDγ, F9.mIdx_conjSub]
    rfl
  have m2 : mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (k : G)) =
      mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) := by
    have hUH : UH T M V₁ H = conjSub (y : G) (F8.Uγ (ZS153 T M V₁) H (g : G)) := eB.symm
    rw [eDH, hUH, F9.mIdx_conjSub]
  have hpos' : 0 < mIdx (F8.Uγ (ZS153 T M V₁) H (k : G))
      (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (k : G)) := by
    rw [m1, heq]; exact hpos
  have hle' : mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (k : G)) ≤
      mIdx (F8.Uγ (ZS153 T M V₁) H (k : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (k : G)) := by
    rw [m1, m2, heq]
  obtain ⟨-, -, hV⟩ := claim_n1 h11 h113 cx hb hno sk hpos' hle'
  have hyp := h98.amalgamHypV
  have hyg : (y : G) * (g : G) ∈ H := by
    have h1 : (y * g) • F8.γ₁ T (Y153 Mc M) H = F8.γ₁ T (Y153 Mc M) H := by
      rw [mul_smul, s.edge₁, hy1]
    have := mem_stab_of_smul_eq h1
    rw [stab_γ₁ hyp.le₂] at this
    simpa using this
  have hky : (k : G)⁻¹ * (y : G) ∈ H := by
    have h1 : (k⁻¹ * y) • F8.γ₁ T (Y153 Mc M) H = F8.γ₁ T (Y153 Mc M) H := by
      rw [mul_smul, hy2, ← sk.edge₁, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rw [stab_γ₁ hyp.le₂] at this
    simpa using this
  have eVk : conjSub (y : G) (conjClosure (VZ T M) H) = F8.Uγ (VZ T M) H (k : G) := by
    have e : (y : G) = (k : G) * ((k : G)⁻¹ * (y : G)) := by group
    rw [F8.Uγ, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer
      (le_normalizer_conjClosure _ H hky)]
  have eA : conjSub (y : G) (F8.A₁ (quasithinOmegaOneCenter T) (g : G)) =
      quasithinOmegaOneCenter T := by
    rw [F8.A₁, ← conjSub_mul, F7.conjSub_eq_of_mem_normalizer (h98.H_normalizes_V₁ hyg)]
  have hEH : conjSub (y : G)
      (F9.EH (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) =
      F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (k : G) := by
    rw [F9.EH, F9.Eγ, conjSub_centralizerMod, eA, eB, eVk]
  have h1 : conjSub (y : G) (VH T M H) ≤ conjSub (y : G) (UH T M V₁ H ⊔
      F9.EH (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) := by
    rw [conjSub_sup, hEH]
    show conjSub (y : G) (conjClosure (VZ T M) H) ≤
      conjSub (y : G) (conjClosure (ZS153 T M V₁) H) ⊔ _
    rw [eVk, ← eU]
    exact hV.le
  have h2 := (conjSub_le_iff (y : G)).mp h1
  rwa [conjSub_conjSub_inv] at h2

end S1549C

end CFSG.Quasithin
