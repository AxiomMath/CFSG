module

public import CFSG.Quasithin.EmptyFaithful.SBc7HypCore
public import CFSG.Quasithin.EmptyFaithful.SBc4H31
public import CFSG.Quasithin.EmptyFaithful.SBc6Ctx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc7

section Arith

theorem card_SL3_eq {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 3)
    (by norm_num)
  rw [hF, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at h2
  simpa using h2

theorem card_field_eq_two_of_card_le {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) {N : ℕ} (hN : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = N)
    (hle : N ≤ 6048) : Nat.card F = 2 ∧ N = 168 := by
  have h2 := card_SL3_eq hF
  rw [hN] at h2
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    omega
  have hn1 : n = 1 := by
    by_contra hne
    have hn2 : 2 ≤ n := by omega
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have h64 : 64 ≤ (2 ^ n) ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h4 3
    have h15 : 15 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have h63 : 63 ≤ (2 ^ n) ^ 3 - 1 := by omega
    have h1 : 15 * 63 ≤ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := Nat.mul_le_mul h15 h63
    have h3 : 64 * (15 * 63) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      Nat.mul_le_mul h64 h1
    omega
  subst hn1
  refine ⟨by simpa using hF, ?_⟩
  norm_num at h2
  omega

end Arith

section Facts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem not_Yp_le_pCoreOf (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) : ¬ Yp ≤ pCoreOf 2 L := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := c25.facts.sylow
  obtain ⟨-, hel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    c25.ctx.charTwo (SBc5.omegaOneCenter_le_Sgp hh)
  have hQC := (SBc6.pCoreOf_le_of_ctx c).2
  intro hle
  exact c25.facts.star_ne (autI_eq_bot_of_le_centralizer hel (hle.trans hQC))

theorem Sgp_le_normalizer_Yp (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  intro x hx
  have hxM : x ∈ M ⊓ I := ⟨c.c29.norm_le hx.2, hF.sylow.1 hx⟩
  rw [← hF.norm_eq] at hxM
  exact hxM.2

theorem blockU_le_Sgp (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) : blockU L ≤ Sgp153 T V₁ := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := c25.facts.sylow
  have hQP : blockU L ≤ pCoreOf 2 L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_pCoreOf 2 L)
  exact hQP.trans ((SBc6.pCoreOf_le_of_ctx c).1.trans (pCoreOf_le_of_isSylowTwoOf hsyl))

theorem card_quot_of_outcome31 (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (h : Outcome31 T V₁ I L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∨
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := by
  obtain ⟨hcases, hker⟩ := h
  rcases hcases with hA | hG | ⟨hP, -⟩
  · right; left
    obtain ⟨α, hα, hαk, -⟩ := hA.2
    rw [SBd5.card_quot_of_surj_ker' hα hαk, SBd5.card_alt_eq' (by norm_num)]
    decide
  · right; right
    obtain ⟨-, hpsu, -⟩ := hG
    exact S153H.card_psu_three_three hpsu
  · left
    obtain ⟨ψ, hψs, hψk⟩ := SBc6.exists_cover_of_ctx c.toCtx15330
    have hker' : ψ.ker = CFSG.pCore 2 ↥L := by
      ext x
      rw [MonoidHom.mem_ker, hψk, AppC.mem_pCore_iff_mem_blockQ]
      constructor
      · intro hx
        have : (x : G) ∈ L ⊓ Subgroup.centralizer (UI153 T I : Set G) := ⟨x.2, hx⟩
        rw [hker] at this
        exact this
      · intro hx
        have : (x : G) ∈ L ⊓ Subgroup.centralizer (UI153 T I : Set G) := by
          rw [hker]
          exact hx
        exact this.2
    rw [SBd5.card_quot_of_surj_ker' hψs hker']
    exact S153H.card_psl_three_two hP

theorem card_field_eq_two (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (h : Outcome31 T V₁ I L)
    {n : ℕ} {F : Type} [Field F] [Fintype F] (hFc : Fintype.card F = 2 ^ n)
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj L α) :
    Fintype.card F = 2 := by
  have hq : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [SBd5.card_quot_of_surj_ker' hα.1 hα.2]
    exact Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.toEquiv
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hFc]
  have hle : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) ≤ 6048 := by
    rw [← hq]
    rcases card_quot_of_outcome31 c h with h1 | h1 | h1 <;> rw [h1] <;> norm_num
  obtain ⟨h1, -⟩ := card_field_eq_two_of_card_le hF rfl hle
  rwa [Nat.card_eq_fintype_card] at h1

end Facts

section Main

theorem input31Hyperplane_holds : Input31Hyperplane := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hout hcase
  have hLI : L ≤ I := S153H.le_I_of_ctx31 c
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  obtain ⟨k, n, F, hF, hFin, α, hcard, hmod, hsum⟩ : ∃ (k n : ℕ) (F : Type) (_ : Field F)
      (_ : Fintype F) (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α ∧
      IsSumOfNaturalModulesVia L (c134Q I L) ⊥ α false k := by
    rcases hcase with h1 | h2
    · change IsC134Case1 I (Sgp153 T V₁) L at h1
      obtain ⟨-, n, F, hF, hFin, hcard, hsec⟩ := h1
      obtain ⟨α, hα, hαk, hsum⟩ := (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).1 hsec
      exact ⟨1, n, F, hF, hFin, α, hcard, ⟨hα, hαk⟩, hsum⟩
    · change IsC134Case2 I (Sgp153 T V₁) L at h2
      obtain ⟨⟨n, F, hF, hFin, α, hcard, hmod, hsum⟩, -⟩ := h2
      exact ⟨2, n, F, hF, hFin, α, hcard, hmod, hsum⟩
  have hF2 : Fintype.card F = 2 := card_field_eq_two c hout hcard hmod
  obtain ⟨hLQ, -, β, hβs, hβk, hβe⟩ := hsum
  have hβk' : β.ker = ⊥ := by rw [hβk, Subgroup.bot_subgroupOf]
  have hQeq : blockU L = c134Q I L := by
    have hle : blockU L ≤ c134Q I L :=
      Subgroup.commutator_mono_left (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLI)
        (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hIL hg)) (pCoreOf_isPGroup 2 L))
    exact le_antisymm hle (SBc4.c134Q_le_blockU c)
  have hy : ∃ y ∈ Yp, ∃ hyL : y ∈ L, α ⟨y, hyL⟩ ≠ 1 := by
    obtain ⟨y, hyY, hyn⟩ := Set.not_subset.mp (not_Yp_le_pCoreOf c.toCtx15330)
    have hyL : y ∈ L := c.c27.Yp_le hyY
    refine ⟨y, hyY, hyL, fun h1 => hyn ?_⟩
    have h2 : (⟨y, hyL⟩ : ↥L) ∈ α.ker := h1
    rw [hmod.2] at h2
    exact (AppC.mem_pCore_iff_mem_blockQ _).1 h2
  have hQY : c134Q I L ≤ Subgroup.normalizer (Yp : Set G) := by
    rw [← hQeq]
    exact (blockU_le_Sgp c.toCtx15330).trans (Sgp_le_normalizer_Yp c.toCtx15330)
  rw [hQeq]
  exact hyperplane_core hF2 α hmod.1 β hβs hβk' hLQ hβe hQY hy

end Main

end SBc7

end CFSG.Quasithin
