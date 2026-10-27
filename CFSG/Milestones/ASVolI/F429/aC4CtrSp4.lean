module

public import CFSG.Milestones.ASVolI.F429.aC4Gen
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpAut

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

theorem burnsideF429a_cent_of_model₂ {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {C : Type} [Group C] (Ψ : C ≃* ↥Gp)
    {P₁ P₂ U : Subgroup C} (h₁ : M₁.subgroupOf Gp = P₁.map Ψ.toMonoidHom)
    (h₂ : M₂.subgroupOf Gp = P₂.map Ψ.toMonoidHom) (hU : pCoreOf 2 (P₁ ⊓ P₂) = U)
    (hinner : ∀ β : MulAut C, (∀ x, β x ∈ P₁ ↔ x ∈ P₁) → (∀ x, β x ∈ P₂ ↔ x ∈ P₂) →
      (∀ u ∈ U, β u = u) → β ∈ (MulAut.conj : C →* MulAut C).range) :
    ∀ z ∈ M₁ ⊓ M₂, (∀ s ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)), z * s = s * z) → z ∈ Gp := by
  intro r hr hcent
  set φ : C →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hφx : ∀ x : C, φ x = ((Ψ x : ↥Gp) : E) := fun x => rfl
  have hB : (M₁ ⊓ M₂).subgroupOf Gp = (P₁ ⊓ P₂).map Ψ.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, h₁, h₂, Subgroup.map_inf_eq _ _ _ Ψ.injective]
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (P₁ ⊓ P₂).map φ := burnsideF429_inf_eq_map Ψ hB
  have hG₁ : Gp ⊓ M₁ = P₁.map φ := burnsideF429_inf_eq_map Ψ h₁
  have hG₂ : Gp ⊓ M₂ = P₂.map φ := burnsideF429_inf_eq_map Ψ h₂
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = U.map φ := by
    rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, hU]
  let β : MulAut C := (Ψ.trans (burnsideF4d_rho Gp r)).trans Ψ.symm
  have hβφ : ∀ x : C, φ (β x) = r * φ x * r⁻¹ := by
    intro x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp r (Ψ x))) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply r (Ψ x)
  have hnorm : ∀ M : Subgroup E, r ∈ M → ∀ y : E, y ∈ Gp ⊓ M ↔ r * y * r⁻¹ ∈ Gp ⊓ M := by
    intro M hM y
    constructor
    · rintro ⟨hyG, hyM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem y hyG r,
        M.mul_mem (M.mul_mem hM hyM) (M.inv_mem hM)⟩
    · rintro ⟨hyG, hyM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hyG r⁻¹
        simpa [mul_assoc] using this
      · have := M.mul_mem (M.mul_mem (M.inv_mem hM) hyM) hM
        simpa [mul_assoc] using this
  have hstab : ∀ (P : Subgroup C) (M : Subgroup E), Gp ⊓ M = P.map φ → r ∈ M →
      ∀ x, β x ∈ P ↔ x ∈ P := by
    intro P M hPM hM x
    have e1 : β x ∈ P ↔ φ (β x) ∈ P.map φ := (Subgroup.mem_map_iff_mem hφ).symm
    have e2 : x ∈ P ↔ φ x ∈ P.map φ := (Subgroup.mem_map_iff_mem hφ).symm
    rw [e1, e2, ← hPM, hβφ]
    exact (hnorm M hM (φ x)).symm
  have h3 : ∀ u ∈ U, β u = u := by
    intro u hu
    apply hφ
    rw [hβφ]
    have hu' : φ u ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
      rw [hS]
      exact ⟨u, hu, rfl⟩
    rw [hcent _ hu']
    group
  obtain ⟨g, hg⟩ := hinner β (hstab P₁ M₁ hG₁ hr.1) (hstab P₂ M₂ hG₂ hr.2) h3
  have hρ : burnsideF4d_rho Gp r = burnsideF4d_rho Gp ((Ψ g : ↥Gp) : E) := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    obtain ⟨x, rfl⟩ := Ψ.surjective y
    rw [burnsideF4d_rho_apply, burnsideF4d_rho_apply]
    have e1 := hβφ x
    rw [← hg, MulAut.conj_apply, map_mul, map_mul, map_inv] at e1
    rw [← hφx, ← hφx, ← e1]
  have hr' := burnsideF4d_rho_injective hc hρ
  rw [hr']
  exact (Ψ g).2

theorem burnsideF429a_pCoreOf_le_sylow {E : Type} [Group E] [Finite E] {Gp M : Subgroup E}
    [Gp.Normal] {T : Subgroup E} (hT : ChF.IsSylowOf 2 T M) : pCoreOf 2 (Gp ⊓ M) ≤ T := by
  refine CFSG.QuasithinUnique.IsSylowTwoOf.le_of_normalizes hT
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right) (fun m hm => ?_)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  apply CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxG, hxM⟩
    exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG m, M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)⟩
  · rintro ⟨hxG, hxM⟩
    refine ⟨?_, ?_⟩
    · have := (inferInstance : Gp.Normal).conj_mem _ hxG m⁻¹
      simpa [mul_assoc] using this
    · have := M.mul_mem (M.mul_mem (M.inv_mem hm) hxM) hm
      simpa [mul_assoc] using this

end Generic

section SpModel

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.SteinbergBS
  CFSG.QuasithinUnique.Fin257.Sp4 CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpOut2 CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem burnsideF429a_Sp_frob_eq_one_of_fixU {g : antiSp F} (hg : g ∈ bor F) (k : ℕ)
    (h : ∀ x : F, g * (frobAut F ^ k) (uElt x 0 0 0) * g⁻¹ = uElt x 0 0 0) :
    frobAut F ^ k = 1 := by
  have h0 : (0 : F) ^ 2 ^ k = 0 := zero_pow (pow_ne_zero k two_ne_zero)
  have key : ∀ x : F, glMat (g : GL (Fin 4) F) 0 0 * x ^ 2 ^ k =
      x * glMat (g : GL (Fin 4) F) 1 1 := by
    intro x
    have h1 : g * (frobAut F ^ k) (uElt x 0 0 0) = uElt x 0 0 0 * g := by
      calc g * (frobAut F ^ k) (uElt x 0 0 0) =
          (g * (frobAut F ^ k) (uElt x 0 0 0) * g⁻¹) * g := by group
        _ = uElt x 0 0 0 * g := by rw [h x]
    rw [frobAut_pow_uElt, h0] at h1
    have h2 := congrArg (fun y : antiSp F => glMat (y : GL (Fin 4) F) 0 1) h1
    simp only [glMat_mul, glMat_uElt] at h2
    simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at h2
    linear_combination h2
  have h00 : glMat (g : GL (Fin 4) F) 0 0 ≠ 0 :=
    (upper_diag_ne_zero (upper_of_mem_normalizer hg)).1
  have h11 : glMat (g : GL (Fin 4) F) 1 1 = glMat (g : GL (Fin 4) F) 0 0 := by
    have := key 1
    simpa using this.symm
  apply frobAut_pow_eq_one_of_fix
  intro x
  have h3 := key x
  rw [h11] at h3
  have h4 : glMat (g : GL (Fin 4) F) 0 0 * (x ^ 2 ^ k - x) = 0 := by linear_combination h3
  exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left h00)

theorem burnsideF429a_Sp_inner_of_fixU {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card F = 2 ^ n)
    {β : MulAut (antiSp F)} (h : StabRad β) (hU : ∀ u ∈ antiUnipotent F, β u = u) :
    β ∈ (MulAut.conj : antiSp F →* MulAut (antiSp F)).range := by
  obtain ⟨g, hg, k, hβ⟩ := aut_form_both hn hK h
  have hFr : frobAut F ^ k = 1 := burnsideF429a_Sp_frob_eq_one_of_fixU hg k (fun x => by
    have := hU _ (uElt_mem_antiUnipotent x 0 0 0)
    rwa [hβ, MulAut.mul_apply, MulAut.conj_apply] at this)
  rw [hβ, hFr, mul_one]
  exact ⟨g, rfl⟩

end SpModel

section Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2)

theorem burnsideF429a_ctr_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : ctr T ≤ Gp := by
  intro z hz
  haveI := hyp.finite
  haveI := hyp.normal
  have hST := burnsideF429a_pCoreOf_le_sylow (Gp := Gp) hT
  have hzc : ∀ s ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)), z * s = s * z := fun s hs =>
    (Subgroup.mem_centralizer_iff.mp hz.2 s (hST hs)).symm
  obtain ⟨marking, e1, e2⟩ := burnsideF4g_marking (c := .Sp4) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4gSp_yam_of_marking_ge marking
  rw [← e1, ← e2] at hTD
  obtain ⟨-, F, hFf, hFfin, hFchar, e, R, i, hFcard, hRi, hDd, he1, he2⟩ :=
    CFSG.Quasithin.H13.F431.SpOut2.spAmalgam_data_out (burnsideF4g_lieModel_Sp4 hf hyp.model)
      (burnsideF4d_amalgamExt hyp.toHypF_4_4g TD hTD)
  have hP : ∀ (X : Subgroup ↥Gp) (P : Subgroup (antiSp F)), X.map e.toMonoidHom = P →
      X = P.map e.symm.toMonoidHom := by
    intro X P hXP
    subst hXP
    ext x
    constructor
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      simpa using hw
  have h₁ : M₁.subgroupOf Gp = (Subgroup.normalizer (R 0 : Set (antiSp F))).map
      e.symm.toMonoidHom := hP _ _ he1
  have h₂ : M₂.subgroupOf Gp = (Subgroup.normalizer (R 1 : Set (antiSp F))).map
      e.symm.toMonoidHom := hP _ _ he2
  have hBor : Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓
      Subgroup.normalizer (R 1 : Set (antiSp F)) = bor F :=
    CFSG.QuasithinUnique.Borel252.BorelData.inf_norm hDd.borel
  have hU : pCoreOf 2 (Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓
      Subgroup.normalizer (R 1 : Set (antiSp F))) = antiUnipotent F := by
    rw [hBor]
    exact CFSG.QuasithinUnique.Borel252.pCoreOf_normalizer_sylow hDd.borel.sylow
  refine burnsideF429a_cent_of_model₂ hyp.centralizer_trivial e.symm h₁ h₂ hU
    (fun β hβ₁ hβ₂ hβU => ?_) z (hT.1 hz.1) hzc
  have hA0 : ∀ x, x ∈ R 0 ↔ β x ∈ R 0 :=
    (mem_autStab_iff_of_normalizer hDd.borel.core₁ β).mp (fun y => (hβ₁ y).symm)
  have hA1 : ∀ x, x ∈ R 1 ↔ β x ∈ R 1 :=
    (mem_autStab_iff_of_normalizer hDd.borel.core₂ β).mp (fun y => (hβ₂ y).symm)
  have hst : StabRad β := by
    rcases hRi with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨fun x => (hA0 x).symm, fun x => (hA1 x).symm⟩
    · exact ⟨fun x => (hA1 x).symm, fun x => (hA0 x).symm⟩
  exact burnsideF429a_Sp_inner_of_fixU hf hFcard hst hβU

end Sp4

end CFSG.ASVolI
