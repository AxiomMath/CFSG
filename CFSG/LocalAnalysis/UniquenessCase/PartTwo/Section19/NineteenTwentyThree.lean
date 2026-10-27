module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem ctx22_t_mem_normalizer {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ : Subgroup G}
    (h : Ctx19_22 D V₀ V p L A t B r A₀) :
    t ∈ normalizer (centralizer (A₀ : Set G) : Set G) := by
  have htA₀ : t ∈ normalizer (A₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : A₀.map (MulAut.conj t).toMonoidHom ≤ A₀ := by
      rintro x ⟨a, ha, rfl⟩
      have hinv : (MulAut.conj t) a = a⁻¹ := by
        simpa [MulAut.conj_apply, mul_assoc] using h.ctx.hinv a (h.hA₀ ha)
      change (MulAut.conj t) a ∈ A₀
      rw [hinv]
      exact A₀.inv_mem ha
    have hcard : Nat.card (A₀.map (MulAut.conj t).toMonoidHom) = Nat.card A₀ :=
      Subgroup.card_map_of_injective (K := A₀) (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective
    exact eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  exact (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup A₀) htA₀

private theorem ctx22_B_le_M {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ : Subgroup G}
    (h : Ctx19_22 D V₀ V p L A t B r A₀) : B ≤ D.M := by
  have hI := IOf_le_M D p h.ctx.hyp.hL.1.1.le
  rw [h.ctx.hB]
  exact sup_le (h.ctx.hA.trans hI) (Subgroup.zpowers_le.mpr (hI h.ctx.htA))

theorem nineteen_twentythree (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ : Subgroup G}
    (h : Ctx19_22 D V₀ V p L A t B r A₀)
    (h14 : R19_14At D V₀ V p L A t B r h.ctx) :
    R19_23At D V₀ V p L A t B r A₀ h := by
  change pCoreOf 2 (centralizer (A₀ : Set G)) = ⊥
  by_contra hQne
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx.hyp.big
  have hV0in : InCalV D.M V₀ := (inCalV0_of_hyp125 h.ctx.hyp.hyp125 hV0ne).1
  have hV0M : V₀ ≤ D.M := hV0in.2.1
  have hV0norm : D.M ≤ normalizer (V₀ : Set G) := hV0in.2.2.1
  have hV0el : IsElemAbelian 2 V₀ := hV0in.2.2.2
  have hV0p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup hV0el
  have hBleM : B ≤ D.M := ctx22_B_le_M h
  have hAleH : A ≤ centralizer (A₀ : Set G) :=
    le_centralizer_of_isMulCommutative_of_le (isMulCommutative_of_isZModSq h.ctx.hAcard) h.hA₀
  have htN : t ∈ normalizer (centralizer (A₀ : Set G) : Set G) := ctx22_t_mem_normalizer h
  have hHleNQ : centralizer (A₀ : Set G) ≤
      normalizer (pCoreOf 2 (centralizer (A₀ : Set G)) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have htNQ : t ∈ normalizer (pCoreOf 2 (centralizer (A₀ : Set G)) : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _) htN
  let Y : Subgroup G := V₀ ⊔ B
  have hYleM : Y ≤ D.M := sup_le hV0M hBleM
  have hV0leO2Y : V₀ ≤ pCoreOf 2 Y := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_left ?_ hV0p
    exact hYleM.trans hV0norm
  have hBleNQ : B ≤ normalizer (pCoreOf 2 (centralizer (A₀ : Set G)) : Set G) := by
    rw [h.ctx.hB]
    refine sup_le ?_ (Subgroup.zpowers_le.mpr htNQ)
    exact hAleH.trans hHleNQ
  have hYleNQ : Y ≤ normalizer (pCoreOf 2 (centralizer (A₀ : Set G)) : Set G) :=
    sup_le (h.hV₀.trans hHleNQ) hBleNQ
  have hYeq : Y = B ⊔ pCoreOf 2 Y := by
    refine le_antisymm ?_ ?_
    · exact sup_le (hV0leO2Y.trans le_sup_right) le_sup_left
    · exact sup_le le_sup_right (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hO2Yne : pCoreOf 2 Y ≠ ⊥ := by
    intro hbot
    apply hV0ne
    exact le_bot_iff.mp (hbot ▸ hV0leO2Y)
  have hcal : calMOf Y ≠ {D.M} := by
    intro hcal
    let s : Set (Subgroup G) := {K | IsTwoLocal K ∧
      normalizer (pCoreOf 2 (centralizer (A₀ : Set G)) : Set G) ≤ K}
    have hfin : s.Finite := Set.toFinite s
    obtain ⟨N, ⟨hN2, hN0N⟩, hmax⟩ := hfin.exists_maximal
      ⟨normalizer (pCoreOf 2 (centralizer (A₀ : Set G)) : Set G),
        ⟨pCoreOf 2 (centralizer (A₀ : Set G)), hQne,
          CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩, le_rfl⟩
    have hNmax : rankThreeIsMaxTwoLocal N := by
      refine ⟨hN2, fun K hK hNK => ?_⟩
      exact (hmax ⟨hK, hN0N.trans hNK⟩ hNK).antisymm hNK
    have hYleN : Y ≤ N := hYleNQ.trans hN0N
    have hNmem : N ∈ calMOf Y := ⟨hNmax, hYleN⟩
    have hNne : N ≠ D.M := by
      intro hNM
      apply h.hcent
      exact hHleNQ.trans (hN0N.trans (le_of_eq hNM))
    rw [hcal] at hNmem
    exact hNne (by simpa using hNmem)
  have hYmu : Y ∈ muSet D B := ⟨hYleM, hYeq, hO2Yne, hcal⟩
  have hempty : muSet D B = ∅ := h14
  rw [hempty] at hYmu
  exact hYmu

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
