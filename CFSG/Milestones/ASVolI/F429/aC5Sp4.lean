module

public import CFSG.Milestones.ASVolI.F429.aR5Gen
public import CFSG.Milestones.ASVolI.F429.Defs
public import CFSG.Milestones.ASVolI.F429.aC3
public import CFSG.Milestones.ASVolI.F429.aC4Gen
public import CFSG.Milestones.ASVolI.F429.aOddGen
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpAut

public section

namespace CFSG.ASVolI

section SpModel

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.SteinbergBS
  CFSG.QuasithinUnique.Fin257.Sp4 CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpOut2 CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F
  CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem burnsideF429a_Sp_frob_eq_one_of_family {g : antiSp F} (hg : g ∈ bor F) (k : ℕ)
    (x : Fˣ → antiSp F) (i : Fin 4) (hxB : ∀ c, x c ∈ bor F)
    (hxi : ∀ c, glMat ((x c : antiSp F) : GL (Fin 4) F) i i = c)
    (h : ∀ c, g * (frobAut F ^ k) (x c) * g⁻¹ * (x c)⁻¹ ∈ antiUnipotent F) :
    frobAut F ^ k = 1 := by
  apply frobAut_pow_eq_one_of_fix
  intro y
  by_cases hy : y = 0
  · rw [hy, zero_pow (pow_ne_zero k two_ne_zero)]
  set s : Fˣ := Units.mk0 y hy with hs
  have hh : x s ∈ bor F := hxB s
  have hφh : (frobAut F ^ k) (x s) ∈ bor F := (frob_pow_mem_bor_iff k _).mpr hh
  have hxU := h s
  have hx : g * (frobAut F ^ k) (x s) * g⁻¹ * (x s)⁻¹ ∈ bor F := Subgroup.le_normalizer hxU
  have hraw : (g * (frobAut F ^ k) (x s) * g⁻¹ * (x s)⁻¹) * x s * g =
      g * (frobAut F ^ k) (x s) := by group
  have hrel : (⟨_, hx⟩ : ↥(bor F)) * ⟨_, hh⟩ * ⟨g, hg⟩ = ⟨g, hg⟩ * ⟨_, hφh⟩ :=
    Subtype.ext hraw
  have hd := congrArg (dgHom F i) hrel
  rw [map_mul, map_mul, map_mul] at hd
  have hx0 : dgHom F i ⟨_, hx⟩ = 1 := glMat_diag_of_mem_U hxU i
  have hg0 : dgHom F i ⟨g, hg⟩ ≠ 0 := by
    have := upper_diag_ne_zero (upper_of_mem_normalizer hg)
    fin_cases i
    · exact this.1
    · exact this.2.1
    · exact this.2.2.1
    · exact this.2.2.2
  rw [hx0, one_mul] at hd
  have hcancel := mul_left_cancel₀ hg0 ((mul_comm _ _).trans hd)
  have hφ0 : dgHom F i ⟨_, hφh⟩ = (s : F) ^ 2 ^ k := by
    have := mat_frobAut_pow (F := F) k (x s)
    have h00 := congrFun (congrFun this i) i
    simpa [dgHom_apply, hxi s] using h00
  have hs0 : dgHom F i ⟨_, hh⟩ = (s : F) := hxi s
  rw [hφ0, hs0] at hcancel
  simpa [hs] using hcancel.symm

theorem burnsideF429a_Sp_torus_family {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card F = 2 ^ n)
    (j : Fin 2) : ∃ (x : Fˣ → antiSp F) (i : Fin 4),
      (∀ c, x c ∈ perfectCore (Subgroup.normalizer (Rrad F j : Set (antiSp F)))) ∧
      (∀ c, x c ∈ bor F) ∧ (∀ c, glMat ((x c : antiSp F) : GL (Fin 4) F) i i = c) := by
  have hpc : perfectCore (Subgroup.normalizer (Rrad F j : Set (antiSp F))) =
      Subgroup.centralizer (rootU F (axisOf j) : Set (antiSp F)) := by
    rw [← rootA_axisOf j, axis_perfectCore_normalizer (hS_axis hn hK j)]
  rw [hpc]
  fin_cases j
  · refine ⟨fun c => dSp c c⁻¹, 0, fun c => ?_, fun c => dSp_mem_normalizer _ _,
      fun c => (glMat_dSp_diag c c⁻¹).1⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    have e := dSp_conj_uElt (K := F) c c⁻¹ 0 b 0 0
    simp only [inv_inv, mul_zero, Units.mul_inv, one_mul] at e
    calc uElt 0 b 0 0 * dSp c c⁻¹ = (dSp c c⁻¹ * uElt 0 b 0 0 * (dSp c c⁻¹)⁻¹) * dSp c c⁻¹ := by
          rw [e]
      _ = dSp c c⁻¹ * uElt 0 b 0 0 := by group
  · refine ⟨fun c => dSp 1 c, 1, fun c => ?_, fun c => dSp_mem_normalizer _ _,
      fun c => (glMat_dSp_diag 1 c).2⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, rfl⟩
    have e := dSp_conj_uElt (K := F) 1 c 0 0 d 0
    simp only [mul_zero, Units.val_one, one_pow, one_mul] at e
    calc uElt 0 0 d 0 * dSp 1 c = (dSp 1 c * uElt 0 0 d 0 * (dSp 1 c)⁻¹) * dSp 1 c := by
          rw [e]
      _ = dSp 1 c * uElt 0 0 d 0 := by group

end SpModel

section Key

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F CFSG.Quasithin.H13.F431.SpOut2
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2)

theorem burnsideF429a_Sp4_setup5 {f : ℕ} {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E}
    [Gp.Normal] (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (e : ↥Gp ≃* antiSp F)
      (R : Fin 2 → Subgroup (antiSp F)),
      Nat.card F = 2 ^ f ∧
      M₁.subgroupOf Gp = (Subgroup.normalizer (R 0 : Set (antiSp F))).map e.symm.toMonoidHom ∧
      M₂.subgroupOf Gp = (Subgroup.normalizer (R 1 : Set (antiSp F))).map e.symm.toMonoidHom ∧
      Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓ Subgroup.normalizer (R 1 : Set (antiSp F)) =
        bor F ∧
      pCoreOf 2 (Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓
        Subgroup.normalizer (R 1 : Set (antiSp F))) = antiUnipotent F ∧
      (∀ j, ∃ j', R j = Rrad F j') ∧
      (∀ β : MulAut (antiSp F),
        (∀ x, β x ∈ Subgroup.normalizer (R 0 : Set (antiSp F)) ↔
          x ∈ Subgroup.normalizer (R 0 : Set (antiSp F))) →
        (∀ x, β x ∈ Subgroup.normalizer (R 1 : Set (antiSp F)) ↔
          x ∈ Subgroup.normalizer (R 1 : Set (antiSp F))) →
        ∃ g ∈ bor F, ∃ k : ℕ, β = MulAut.conj g * frobAut F ^ k) ∧
      ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp := by
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
  have hRj : ∀ j, ∃ j', R j = Rrad F j' := by
    rcases hRi with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact fun j => ⟨j, rfl⟩
    · intro j
      fin_cases j
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
  have hform : ∀ β : MulAut (antiSp F),
      (∀ x, β x ∈ Subgroup.normalizer (R 0 : Set (antiSp F)) ↔
        x ∈ Subgroup.normalizer (R 0 : Set (antiSp F))) →
      (∀ x, β x ∈ Subgroup.normalizer (R 1 : Set (antiSp F)) ↔
        x ∈ Subgroup.normalizer (R 1 : Set (antiSp F))) →
      ∃ g ∈ bor F, ∃ k : ℕ, β = MulAut.conj g * frobAut F ^ k := by
    intro β hβ₁ hβ₂
    have hA0 : ∀ x, x ∈ R 0 ↔ β x ∈ R 0 :=
      (mem_autStab_iff_of_normalizer hDd.borel.core₁ β).mp (fun y => (hβ₁ y).symm)
    have hA1 : ∀ x, x ∈ R 1 ↔ β x ∈ R 1 :=
      (mem_autStab_iff_of_normalizer hDd.borel.core₂ β).mp (fun y => (hβ₂ y).symm)
    have hst : StabRad β := by
      rcases hRi with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨fun x => (hA0 x).symm, fun x => (hA1 x).symm⟩
      · exact ⟨fun x => (hA1 x).symm, fun x => (hA0 x).symm⟩
    exact aut_form_both hf hFcard hst
  set φ : antiSp F →* E := Gp.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp e.symm.injective
  have hB : (M₁ ⊓ M₂).subgroupOf Gp = (Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓
      Subgroup.normalizer (R 1 : Set (antiSp F))).map e.symm.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, h₁, h₂, Subgroup.map_inf_eq _ _ _ e.symm.injective]
  have hGB := burnsideF429_inf_eq_map e.symm hB
  have hSG : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp := by
    have htop : (⊤ : Subgroup (antiSp F)).map φ = Gp := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact (e.symm y).2
      · intro hx
        exact ⟨e ⟨x, hx⟩, Subgroup.mem_top _, by simp [hφdef]⟩
    rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, hU, ← htop]
    exact burnsideF429_isSylowOf_map φ hφ
      (hDd.borel.sylow : ChF.IsSylowOf 2 (antiUnipotent F) ⊤)
  exact ⟨F, hFf, hFfin, hFchar, e, R, hFcard, h₁, h₂, hBor, hU, hRj, hform, hSG⟩

theorem burnsideF429a_Sp4_key_of_setup {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hf : 2 ≤ f) (hFcard : Nat.card F = 2 ^ f) (e : ↥Gp ≃* antiSp F)
    (R : Fin 2 → Subgroup (antiSp F))
    (h₁ : M₁.subgroupOf Gp = (Subgroup.normalizer (R 0 : Set (antiSp F))).map e.symm.toMonoidHom)
    (h₂ : M₂.subgroupOf Gp = (Subgroup.normalizer (R 1 : Set (antiSp F))).map e.symm.toMonoidHom)
    (hBor : Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓
      Subgroup.normalizer (R 1 : Set (antiSp F)) = bor F)
    (hU : pCoreOf 2 (Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓
      Subgroup.normalizer (R 1 : Set (antiSp F))) = antiUnipotent F)
    (hform : ∀ β : MulAut (antiSp F),
      (∀ x, β x ∈ Subgroup.normalizer (R 0 : Set (antiSp F)) ↔
        x ∈ Subgroup.normalizer (R 0 : Set (antiSp F))) →
      (∀ x, β x ∈ Subgroup.normalizer (R 1 : Set (antiSp F)) ↔
        x ∈ Subgroup.normalizer (R 1 : Set (antiSp F))) →
      ∃ g ∈ bor F, ∃ k : ℕ, β = MulAut.conj g * frobAut F ^ k)
    {M : Subgroup E} {j : Fin 2}
    (hMj : M.subgroupOf Gp = (Subgroup.normalizer (R j : Set (antiSp F))).map e.symm.toMonoidHom)
    (hj' : ∃ j', R j = Rrad F j') (hLM : oPPrime 2 (Gp ⊓ M) = perfectCore (Gp ⊓ M)) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr _ _ hcomm
  set φ : antiSp F →* E := Gp.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp e.symm.injective
  have hB : (M₁ ⊓ M₂).subgroupOf Gp = (Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓
      Subgroup.normalizer (R 1 : Set (antiSp F))).map e.symm.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, h₁, h₂, Subgroup.map_inf_eq _ _ _ e.symm.injective]
  have hGB := burnsideF429_inf_eq_map e.symm hB
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (antiUnipotent F).map φ := by
    rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, hU]
  have hGM : Gp ⊓ M = (Subgroup.normalizer (R j : Set (antiSp F))).map φ :=
    burnsideF429_inf_eq_map e.symm hMj
  have hL : oPPrime 2 (Gp ⊓ M) =
      (perfectCore (Subgroup.normalizer (R j : Set (antiSp F)))).map φ := by
    rw [hLM, hGM, burnsideF429_perfectCore_map φ hφ]
  obtain ⟨j', hRj'⟩ := hj'
  obtain ⟨x, i, hxL, hxB, hxi⟩ := burnsideF429a_Sp_torus_family hf hFcard j'
  refine burnsideF429a_mem_of_model₂ hc e.symm h₁ h₂ hr (fun β hβ₁ hβ₂ hβr => ?_)
  obtain ⟨g, hg, k', hβ⟩ := hform β hβ₁ hβ₂
  have hcx : ∀ c, g * (frobAut F ^ k') (x c) * g⁻¹ * (x c)⁻¹ ∈ antiUnipotent F := by
    intro c
    have hb : φ (x c) ∈ oPPrime 2 (Gp ⊓ M) ⊓ (M₁ ⊓ M₂) := by
      refine ⟨?_, ?_⟩
      · rw [hL, hRj']
        exact ⟨x c, hxL c, rfl⟩
      · have : φ (x c) ∈ Gp ⊓ (M₁ ⊓ M₂) := by
          rw [hGB, hBor]
          exact ⟨x c, hxB c, rfl⟩
        exact this.2
    have h1 := hcomm _ hb
    rw [hS] at h1
    have e1 : r * φ (x c) * r⁻¹ * (φ (x c))⁻¹ = φ (β (x c) * (x c)⁻¹) := by
      rw [map_mul, map_inv]
      show r * φ (x c) * r⁻¹ * (φ (x c))⁻¹ = ((e.symm (β (x c)) : ↥Gp) : E) * (φ (x c))⁻¹
      rw [hβr]
      rfl
    rw [e1] at h1
    have h2 := (Subgroup.mem_map_iff_mem hφ).mp h1
    rwa [hβ, MulAut.mul_apply, MulAut.conj_apply] at h2
  have hFr : frobAut F ^ k' = 1 :=
    burnsideF429a_Sp_frob_eq_one_of_family hg k' x i hxB hxi hcx
  rw [hβ, hFr, mul_one]
  exact ⟨g, rfl⟩

theorem burnsideF429a_key1_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₁) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, _, _, _, e, R, hFcard, h₁, h₂, hBor, hU, hRj, hform, -⟩ :=
    burnsideF429a_Sp4_setup5 hyp hf
  exact burnsideF429a_Sp4_key_of_setup hyp.centralizer_trivial hf hFcard e R h₁ h₂ hBor hU hform
    h₁ (hRj 0) (burnsideF429a_Sp4_pkg hyp hf).2.1

theorem burnsideF429a_key2_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₂) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, _, _, _, e, R, hFcard, h₁, h₂, hBor, hU, hRj, hform, -⟩ :=
    burnsideF429a_Sp4_setup5 hyp hf
  exact burnsideF429a_Sp4_key_of_setup hyp.centralizer_trivial hf hFcard e R h₁ h₂ hBor hU hform
    h₂ (hRj 1) (burnsideF429a_Sp4_pkg hyp hf).2.2

theorem burnsideF429a_c5_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C5 .Sp4 Gp M₁ M₂ hyp T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, _, _, _, e, R, -, -, -, -, -, -, -, hSG⟩ := burnsideF429a_Sp4_setup5 hyp hf
  exact Or.inl ⟨burnsideF429a_c5_of_key hSG inf_le_left hT (burnsideF429a_key1_Sp4 hyp hf),
    burnsideF429a_c5_of_key hSG inf_le_right hT (burnsideF429a_key2_Sp4 hyp hf)⟩

end Key

end CFSG.ASVolI
