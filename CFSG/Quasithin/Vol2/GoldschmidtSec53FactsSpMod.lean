module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpDiag
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpModelLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsMod

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F1 CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpModel CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.RankThree.PartOne.KCRootAxis CFSG.QuasithinUnique.Fin257.Sp4
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2)

theorem TransFacts.symm {P : Type} [Group P] {N₁ N₂ : Subgroup P} (h : TransFacts N₁ N₂) :
    TransFacts N₂ N₁ where
  solv := by
    rw [inf_comm]
    exact h.solv
  trans₁ := h.trans₂
  trans₂ := h.trans₁

theorem SplitFacts.symm {P : Type} [Group P] {N₁ N₂ : Subgroup P} (h : SplitFacts N₁ N₂) :
    SplitFacts N₂ N₁ where
  le₁ := by
    rw [inf_comm]
    exact h.le₂
  le₂ := by
    rw [inf_comm]
    exact h.le₁
  ne₁ := h.ne₂
  ne₂ := h.ne₁
  inf := fun x hx1 hx2 => h.inf x hx2 hx1
  third := by
    rw [inf_comm]
    intro a ha a' ha' h1 h2 h1' h2'
    exact h.third a ha a' ha' h2 h1 h2' h1'

section Sp

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem exists_sq_eq' (a : F) : ∃ r : F, r * r = a := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) a
  exact ⟨r, hr.symm⟩

theorem pCoreOf_inf_sp (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Subgroup.normalizer (radA1 F : Set (antiSp F)) ⊓ Subgroup.normalizer (radA2 F : Set (antiSp F))
      = bor F ∧
    pCoreOf 2 (Subgroup.normalizer (radA1 F : Set (antiSp F)) ⊓
      Subgroup.normalizer (radA2 F : Set (antiSp F))) = antiUnipotent F := by
  have hB := borel_antiSp (F := F) hn hF
  have h1 := Borel252.BorelData.inf_norm hB
  exact ⟨h1, by rw [h1]; exact Borel252.pCoreOf_normalizer_sylow hB.sylow⟩

theorem transFacts_sp (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    TransFacts (Subgroup.normalizer (radA1 F : Set (antiSp F)))
      (Subgroup.normalizer (radA2 F : Set (antiSp F))) := by
  have hD := spDData_antiSp hn hF
  refine ⟨?_, hD.Z_trans 0, hD.Z_trans 1⟩
  rw [(pCoreOf_inf_sp hn hF).1]
  exact isSolvable_bor hD.borel.sylow.2.1

theorem splitFacts_sp (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    SplitFacts (Subgroup.normalizer (radA1 F : Set (antiSp F)))
      (Subgroup.normalizer (radA2 F : Set (antiSp F))) := by
  have hD := spDData_antiSp hn hF
  obtain ⟨hinf, hcore⟩ := pCoreOf_inf_sp hn hF
  have z0 : centerOf (perfectCore (Subgroup.normalizer (radA1 F : Set (antiSp F)))) =
      rootU₁ F := spZc_eq hn hF 0
  have z1 : centerOf (perfectCore (Subgroup.normalizer (radA2 F : Set (antiSp F)))) =
      rootU₂ F := spZc_eq hn hF 1
  refine ⟨?_, ?_, hD.Z_ne 0, hD.Z_ne 1, hD.Z_inf, ?_⟩
  · rw [hcore]
    exact (hD.Z_le 0).trans inf_le_left
  · rw [hcore]
    exact (hD.Z_le 1).trans inf_le_left
  · intro a ha a' ha' h1 h2 h1' h2'
    rw [hcore, centerOf_antiUnipotent] at ha ha'
    obtain ⟨b, c, rfl⟩ := ha
    obtain ⟨b', c', rfl⟩ := ha'
    rw [z0] at h1 h1'
    rw [z1] at h2 h2'
    have hc : c ≠ 0 := fun h => h1 ⟨b, by rw [h]⟩
    have hb : b ≠ 0 := fun h => h2 ⟨c, by rw [h]⟩
    have hc' : c' ≠ 0 := fun h => h1' ⟨b', by rw [h]⟩
    have hb' : b' ≠ 0 := fun h => h2' ⟨c', by rw [h]⟩
    obtain ⟨r, hr⟩ := exists_sq_eq' (c' / c)
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact div_ne_zero hc' hc (by rw [← hr, mul_zero])
    have hrb : r * b ≠ 0 := mul_ne_zero hr0 hb
    have hq : b' / (r * b) ≠ 0 := div_ne_zero hb' hrb
    refine ⟨dSp (Units.mk0 r hr0) (Units.mk0 (b' / (r * b)) hq), ?_, ?_⟩
    · rw [hinf]
      exact dSp_mem_normalizer _ _
    · rw [dSp_conj_uElt]
      congr 1
      · simp
      · simp only [Units.val_mk0]
        field_simp
      · simp only [Units.val_mk0]
        have : r * r * c = c' := by rw [hr]; field_simp
        linear_combination this
      · simp

end Sp

section Model

variable {G : Type} [Group G]

theorem exists_sp_facts {M L H B D T : Subgroup G} {f : ℕ}
    (hty : IsOfLieType52 M L H B D T .PSp 2 f) :
    ∃ (P : Type) (_ : Group P) (_ : Finite P) (N₁ N₂ : Subgroup P), TransFacts N₁ N₂ ∧
      SplitFacts N₁ N₂ ∧
      Nonempty ((RankTwoAmalgam.ofSubgroups (fG1 M L H B) (fG2 M L H D)).Iso
        (RankTwoAmalgam.ofSubgroups N₁ N₂)) := by
  obtain ⟨Y, _, hY, TY, M₁, M₂, hpair, ⟨Φ⟩⟩ := hty.1
  obtain ⟨hf, F, hFf, hFfin, hFchar, hFcard, ⟨e1⟩⟩ := exists_equiv_antiSp hY
  have hy1 := hpair.map e1
  have hU := (borel_antiSp (F := F) hf hFcard).sylow
  obtain ⟨h, -, hh⟩ := IsSylowTwoOf.exists_conj hy1.1 hU
  let E : Y ≃* antiSp F := e1.trans (MulAut.conj h)
  have hy2 : IsYAmalgamPair (antiUnipotent F) (M₁.map E.toMonoidHom) (M₂.map E.toMonoidHom) := by
    have := hpair.map E
    have hTD : TY.map E.toMonoidHom = antiUnipotent F := by
      rw [hh, Subgroup.map_map]
      rfl
    rwa [hTD] at this
  let Ψ := F431.U42.Am.isoTrans Φ (F431.U42.Am.ofSubgroupsMapInj E.toMonoidHom E.injective M₁ M₂)
  rcases yam_antiSp hf hFcard hy2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨antiSp F, inferInstance, inferInstance, _, _, transFacts_sp hf hFcard,
      splitFacts_sp hf hFcard,
      ⟨F431.U42.Am.isoTrans Ψ (F431.U42.Am.ofSubgroupsCongr h1 h2)⟩⟩
  · exact ⟨antiSp F, inferInstance, inferInstance, _, _, (transFacts_sp hf hFcard).symm,
      (splitFacts_sp hf hFcard).symm,
      ⟨F431.U42.Am.isoTrans Ψ (F431.U42.Am.ofSubgroupsCongr h1 h2)⟩⟩

end Model

end CFSG.Quasithin.H13.Sec53F
