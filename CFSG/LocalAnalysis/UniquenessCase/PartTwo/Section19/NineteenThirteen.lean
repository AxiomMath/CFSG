module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
public import CFSG.GroupTheory.ZModSqElemAbelianNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_isElemAbelian_card_nine_of_isZModSq {A : Subgroup G} {n : ℕ}
    (hA : IsZModSq A n) (h3 : 3 ∣ Nat.card A) :
    ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hcard := card_eq_of_isZModSq hA
  obtain ⟨e⟩ := hA
  have h3m : 3 ∣ 2 ^ n - 1 := by
    rw [hcard] at h3
    exact (Nat.prime_three.dvd_mul.mp h3).elim id id
  exact CFSG.GroupTheory.exists_isElemAbelian_card_nine_of_mulEquiv_zmod_sq e h3m

theorem nineteen_thirteen_sylow (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h12 : Concl19_12 D A 3) :
    3 ∈ piSet A → ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M →
      CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3mem P hP
  have h3dvd : 3 ∣ Nat.card A := h3mem.2
  have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h
  obtain ⟨E₀, hE₀A, hE₀el, hE₀card⟩ :=
    exists_isElemAbelian_card_nine_of_isZModSq h.hAcard h3dvd
  have hE₀U : E₀ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    h12 E₀ hE₀A hE₀el hE₀card
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hE₀M : E₀ ≤ D.M := hE₀A.trans hAM
  have hE₀p : IsPGroup 3 ↥(E₀.subgroupOf D.M) := by
    refine IsPGroup.iff_card.mpr ⟨2, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀M).toEquiv, hE₀card]
    norm_num
  obtain ⟨P', hP'⟩ := hE₀p.exists_le_sylow
  let P'G : Subgroup G := (P' : Subgroup D.M).map D.M.subtype
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf 3 P'G D.M := ⟨P', rfl⟩
  have hE₀P' : E₀ ≤ P'G := by
    intro x hx
    have hx' : (⟨x, hE₀M hx⟩ : ↥D.M) ∈ E₀.subgroupOf D.M := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map_of_mem _ (hP' hx')
  obtain ⟨m, hmM, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hP hP'syl
  let E : Subgroup G := E₀.map (MulAut.conj m⁻¹).toMonoidHom
  have hEU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    conj_mem_uniqueSet hE₀U (D.M.inv_mem hmM)
  have hEP : E ≤ P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyP' : y ∈ P'G := hE₀P' hy
    have h1 : m⁻¹ * y * m ∈ P := (hconj y).mp hyP'
    simpa [MulAut.conj_apply] using h1
  have hNE : normalizer (E : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hEU
  have hNP : normalizer (P : Set G) ≤ D.M := by
    intro g hg
    have hPconj : P.map (MulAut.conj g).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hEconj : E.map (MulAut.conj g).toMonoidHom ≤ P := by
      rw [← hPconj]
      exact Subgroup.map_mono hEP
    have hEle : E ≤ D.M.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro x hx
      have hxg : g * x * g⁻¹ ∈ P := hEconj ⟨x, hx, rfl⟩
      refine Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hP.le hxg, ?_⟩
      show (MulAut.conj g⁻¹) (g * x * g⁻¹) = x
      simp only [MulAut.conj_apply]
      group
    have hMeq : D.M.map (MulAut.conj g⁻¹).toMonoidHom = D.M := hEU.2 g⁻¹ hEle
    have hginv : g⁻¹ ∈ D.M := by
      have hmem : g⁻¹ ∈ Subgroup.normalizer (D.M : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMeq
      rwa [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal] at hmem
    simpa using D.M.inv_mem hginv
  have h := CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le
    (p := 3) (T := P) (H := D.M) (M := ⊤) (by simpa using hP)
    (by simpa using hNP)
  simpa using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
