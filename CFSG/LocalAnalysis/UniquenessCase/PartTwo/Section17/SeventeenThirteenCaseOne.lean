module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenCommon
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.GroupTheory.PCoreOfSubnormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

theorem eq_char_of_isLieOverOdd17_of_isL3EpsOdd17
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hNotL2 : K_LieModelNotL2) {X : Type} [Group X] {r q : ℕ}
    (hlie : IsLieOverOdd17 X r q) (hL3 : IsL3EpsOdd17 X r) : q = r := by
  obtain ⟨hr, hr2, t, n, f, hadm, rfl, hm⟩ := hlie
  obtain ⟨t₃, ht₃, h3⟩ : ∃ t₃ : CFSG.Open.StatedLieTag, (t₃ = .PSL ∨ t₃ = .PSU) ∧
      LieModel X t₃ 3 r 1 := by
    rcases hL3 with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have hadm3 := h3.admissible
  have hfac := (hO X t n r f hadm hm).2.2
  have hfac3 := (hO X t₃ 3 r 1 hadm3 h3).2.2
  have h3e : CFSG.ComponentClassification.CatLeaf.lieSylowExponent t₃ 3 = 3 := by
    rcases ht₃ with rfl | rfl <;> rfl
  have hN : CFSG.ComponentClassification.CatLeaf.lieSylowExponent t n * f = 3 := by
    rw [← hfac, hfac3, h3e, mul_one]
  have hfd : f ∣ 3 := Dvd.intro_left _ hN
  rcases (Nat.dvd_prime Nat.prime_three).mp hfd with hf | hf
  · subst hf
    simp
  · subst hf
    exfalso
    have hN1 : CFSG.ComponentClassification.CatLeaf.lieSylowExponent t n = 1 := by omega
    have hb : CFSG.ComponentClassification.CatLeaf.lieSylowExponent t n * 3 ≤ 10 := by omega
    have hL2 : IsL2Over17 X (r ^ 3) → False := fun h =>
      hNotL2 X t₃ 3 r 1 (r ^ 3) hr2 (Or.inr (by decide)) hadm3 h3 h
    clear hfac hfac3 hN hfd hb
    rcases CFSG.ComponentClassification.CatLeaf.lie_casework hadm (by omega) with
      ⟨ht, hn1, hn2, -, -⟩ | ⟨ht, hn1, hn2, -, -⟩ | ⟨ht, hn0, -, -⟩
    · rcases ht with rfl | rfl
      · interval_cases n
        · exact hL2 ⟨r, 3, hr, hr2, rfl, by norm_num, hm⟩
        all_goals (simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hN1 <;>
          omega)
      · have h3n : 3 ≤ n := hadm.2.2.1
        interval_cases n <;>
          simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hN1 <;> omega
    · rcases ht with rfl | rfl <;> interval_cases n <;>
        simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hN1 <;> omega
    · subst hn0
      cases t <;> simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at hN1 <;>
        omega

variable {G : Type} [Group G] [Finite G]


theorem delta17_12_case_one_triple
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hNotL2 : K_LieModelNotL2) {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h9 : R17_9At D V₀ V L r q hC) {H : Subgroup G}
    (hH : H ∈ Delta17_12 D (fundPred q) r q L) (h1 : P17_12_1 r q L) :
    ∃ K : Subgroup (Bar2 H), CFSG.IsComponent K ∧
      orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊔
        CFSG.LocalAnalysis.WeakClosure81.barImage H D.T = ⊤ ∧
      OddComponentShapeCore q (↥K ⧸ Subgroup.center ↥K) := by
  classical
  have h9' : 3 < q := by
    unfold R17_9At at h9
    exact h9
  rw [Delta17_12, dif_pos h1] at hH
  obtain ⟨x, hxM, rfl⟩ := hH
  set U : Subgroup G := L.map (MulAut.conj x).toMonoidHom with hU
  have hLM : L ≤ D.M := hC.memL.1.le
  have hUM : U ≤ D.M := by
    rw [hU, Subgroup.map_le_iff_le_comap]
    intro y hy
    rw [Subgroup.mem_comap]
    exact D.M.mul_mem (D.M.mul_mem hxM (hLM hy)) (D.M.inv_mem hxM)
  have hHM : D.T ⊔ U ≤ D.M := sup_le D.sylowM.le hUM
  have hUcal : U ∈ calC D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj x)
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj.mp
        (Subgroup.le_normalizer hxM)) hC.memL
  let π : ↥(D.T ⊔ U) →* Bar2 (D.T ⊔ U) :=
    QuotientGroup.mk' (CFSG.pCore 2 ↥(D.T ⊔ U))
  let φ : ↥U →* Bar2 (D.T ⊔ U) := π.comp (Subgroup.inclusion le_sup_right)
  let K : Subgroup (Bar2 (D.T ⊔ U)) := φ.range
  have hKdef : K = (U.subgroupOf (D.T ⊔ U)).map π := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨Subgroup.inclusion le_sup_right u, Subgroup.mem_subgroupOf.mpr u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, Subgroup.mem_subgroupOf.mp hu⟩, rfl⟩
  have hKcomp : CFSG.IsComponent K := by
    rw [hKdef]
    exact isComponent_barImage_of_mem_calC le_sup_right hHM hUcal
  have hgen : K ⊔ CFSG.LocalAnalysis.WeakClosure81.barImage (D.T ⊔ U) D.T = ⊤ := by
    rw [hKdef]
    exact barImage_sup_barImage_eq_top rfl le_sup_right
  have horb : orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage (D.T ⊔ U) D.T) ⊔
      CFSG.LocalAnalysis.WeakClosure81.barImage (D.T ⊔ U) D.T = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hgen]
    exact sup_le ((le_orbitClosure K _).trans le_sup_left) le_sup_right
  have hUsub : CFSG.Open.IsSubnormal U (D.T ⊔ U) := by
    have h1 : CFSG.Assembly.IsSubnormal U D.M :=
      CFSG.Assembly.isSubnormal_iff_open.mpr hUcal.1
    have h2 := h1.inf_of_le hHM
    rw [inf_eq_left.mpr le_sup_right] at h2
    exact CFSG.Assembly.isSubnormal_iff_open.mp h2
  have hO2U : CFSG.Open.pCoreOf 2 U = U ⊓ CFSG.Open.pCoreOf 2 (D.T ⊔ U) :=
    CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hUsub
  have hφker : φ.ker = (U ⊓ CFSG.Open.pCoreOf 2 (D.T ⊔ U)).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hu
      refine ⟨u.2, ?_⟩
      have hu' : Subgroup.inclusion le_sup_right u ∈ CFSG.pCore 2 ↥(D.T ⊔ U) :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion le_sup_right u)).mp
          (by simpa [φ, π] using hu)
      rw [← CFSG.openPCoreOf_subgroupOf 2 (D.T ⊔ U)] at hu'
      exact Subgroup.mem_subgroupOf.mp hu'
    · rintro ⟨-, hu⟩
      apply (QuotientGroup.eq_one_iff (Subgroup.inclusion le_sup_right u)).mpr
      rw [← CFSG.openPCoreOf_subgroupOf 2 (D.T ⊔ U)]
      exact Subgroup.mem_subgroupOf.mpr hu
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥U)).ker ≤ φ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, hφker, ← hO2U, CFSG.openPCoreOf_subgroupOf,
      QuotientGroup.ker_mk']
  have hB : CFSG.IsQuasisimple (Bar2 U) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hUcal.2.2
  have hnt : Nontrivial ↥K := by
    obtain ⟨a, b, hab⟩ := hKcomp.1.2.2
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) b
    exact ⟨u, v, fun h => hab (by rw [h])⟩
  obtain ⟨-, ⟨e3⟩⟩ :=
    @CFSG.GroupTheory.quasisimple_and_centralQuotient_of_ker_le _ _ _ _ _ _ hB
      (QuotientGroup.mk' (CFSG.pCore 2 ↥U)) (QuotientGroup.mk'_surjective _)
      φ.rangeRestrict φ.rangeRestrict_surjective hker hnt
  obtain ⟨e1⟩ := uc22p20c_barInf_equiv_map L x
  obtain ⟨e2⟩ := uc22p21k_barInf_equiv_of_calC hUcal
  have e : BarInf L ≃* (↥K ⧸ Subgroup.center ↥K) := e1.trans (e2.trans e3)
  have hcore : OddComponentShapeCore q (↥K ⧸ Subgroup.center ↥K) := by
    rcases h1 with hL2 | hL3
    · exact Or.inl ⟨q, isL2Over17_of_mulEquiv e.symm hL2, Or.inl rfl, h9'⟩
    · have hq : q = r := eq_char_of_isLieOverOdd17_of_isL3EpsOdd17 hO hNotL2 hC.lie hL3
      have hL3q : IsL3EpsOdd17 (BarInf L) q := by
        rw [← hq] at hL3
        exact hL3
      refine Or.inr ⟨?_, h9'⟩
      rcases hL3q with h | h
      · exact Or.inl (LieModel.of_mulEquiv e h)
      · exact Or.inr (LieModel.of_mulEquiv e h)
  exact ⟨K, hKcomp, horb, hcore⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
