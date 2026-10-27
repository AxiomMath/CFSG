module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_cClos_good_vector_of_fixed
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (h3 : 3 ∈ D.sig)
    {w : Vtil ⊥ V h.hyp151.isElemAbelian} (hw : w ≠ 1)
    (hwT : ∀ τ ∈ barSub ⊥ V h.hyp151.isElemAbelian D.T, τ w = w)
    {E : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))}
    (hEM : E ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hEab : IsElemAbelian 3 E)
    (hEcard : 9 ≤ Nat.card ↥E) (hEw : ∀ e ∈ E, e w = w) :
    ∃ v : G, v ∈ V ∧ v ∈ E3.cClos V (D.k + 0) D.T ∧ v ≠ 1 ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨x, hx⟩ := mkTil_surjective (⊥ : Subgroup G) V hV w
  have hx1 : x ≠ 1 := by
    intro h1
    apply hw
    rw [← hx, h1, map_one]
  have hx0 : x.val ∉ (⊥ : Subgroup G) := by
    rw [Subgroup.mem_bot]
    exact fun h1 => hx1 (Subtype.ext h1)
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hcomm : ∀ t ∈ D.T, t * x.val = x.val * t := by
    intro t ht
    have hst : t ∈ stabTil (⊥ : Subgroup G) V := hMs (D.sylowM.le ht)
    have hmem : actTil (⊥ : Subgroup G) V hV ⟨t, hst⟩ ∈ barSub (⊥ : Subgroup G) V hV D.T :=
      actTil_mem_barSub (⊥ : Subgroup G) V hV ht hst
    have hfix' : actTil (⊥ : Subgroup G) V hV ⟨t, hst⟩ (mkTil (⊥ : Subgroup G) V hV x) =
        mkTil (⊥ : Subgroup G) V hV x := by
      rw [hx]
      exact hwT _ hmem
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix'
    have h3' : t * x.val * t⁻¹ = x.val :=
      mul_inv_eq_one.mp (Subgroup.mem_bot.1 hfix')
    calc t * x.val = (t * x.val * t⁻¹) * t := by group
      _ = x.val * t := by rw [h3']
  have hEpt : E ≤ ptCent (Mbar D.M ⊥ V hV) (mkTil (⊥ : Subgroup G) V hV x) := by
    intro e he
    refine Subgroup.mem_inf.2 ⟨hEM he, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    change e (mkTil (⊥ : Subgroup G) V hV x) = mkTil (⊥ : Subgroup G) V hV x
    rw [hx]
    exact hEw e he
  have hEc : ¬ IsCyclic ↥E :=
    s16c7_not_isCyclic_of_elemAbelian Nat.prime_three hEab (by
      show 3 ^ 2 ≤ Nat.card E
      norm_num
      exact hEcard)
  refine ⟨x.val, x.val_mem, ?_, ?_, ?_⟩
  · refine Subgroup.mem_inf.2 ⟨s15_13A_le_T h.hyp151.hyp125 x.val_mem, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y (E3.wClos_le (D.k + 0) D.T hy)
  · intro h1
    exact hx0 (by rw [h1]; exact Subgroup.one_mem _)
  · exact centralizer_le_of_noncyclic_bar D S.h61 Nat.prime_three (by norm_num) h3 hV
      h.hyp151.hyp125.pairFacts (Or.inl rfl) (by rw [Subgroup.card_bot]; norm_num) x hx0 hEpt
      hEab.isPGroup hEc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
