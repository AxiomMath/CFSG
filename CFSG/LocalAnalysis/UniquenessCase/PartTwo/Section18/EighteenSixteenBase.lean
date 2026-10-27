module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3OddNc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_mSub_of_rk_top_le (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {N : ℕ} (hN : N ≤ rk ↥(⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))) :
    N ≤ mSub V := by
  have h1 := rk_top_vtil_add_mSub V₀ V h.isElemAbelian h.pairFacts.le
  omega

theorem isCyclic_of_le_normalizer_of_not_centralizer_le (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    {W X : Subgroup G} (hXV : X ≤ V) (hXW : X ≤ W) (hX : X ≠ ⊥)
    (hW : ¬ centralizer (W : Set G) ≤ D.M) {P : Subgroup G}
    (hP : P ≤ normalizer (X : Set G)) (hPM : P ≤ D.M) (hPp : IsPGroup p P) :
    IsCyclic P := by
  by_contra hPc
  have hX2 : IsPGroup 2 X := (h.hyp125.isElemAbelian.isPGroup).to_le hXV
  have hN : normalizer (X : Set G) ≤ D.M :=
    normalizer_le_of_noncyclic D h61 h.hp hPM hPp hPc hX hX2 hP
  refine hW ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hXW)).trans ?_)
  exact (Subgroup.centralizer_le_normalizer (X : Set G)).trans hN

theorem preBarSub_le_normalizer_of_stab {D : Data G} {V X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hXV : X ≤ V) {E : Subgroup (Vtil ⊥ V hV)}
    (hE : imgTil ⊥ V hV X = E)
    {P : Subgroup (MulAut (Vtil ⊥ V hV))} (hP : P ≤ stabSub E) :
    preBarSub D.M ⊥ V hV P ≤ normalizer (X : Set G) := by
  have key : ∀ g : G, g ∈ preBarSub D.M ⊥ V hV P → ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    obtain ⟨-, hstg, hxPg⟩ := (mem_preBarSub D.M ⊥ V hV P).1 hg
    have h1 : mkTil ⊥ V hV (IntMod.mk hV ⟨x, hXV hx⟩) ∈ E := by
      rw [← hE]
      exact (mem_imgTil ⊥ V hV X _).2 ⟨IntMod.mk hV ⟨x, hXV hx⟩, hx, rfl⟩
    have h2 : actTil ⊥ V hV ⟨g, hstg⟩ (mkTil ⊥ V hV (IntMod.mk hV ⟨x, hXV hx⟩)) ∈ E :=
      ((mem_stabSub.1 (hP hxPg)) (mkTil ⊥ V hV (IntMod.mk hV ⟨x, hXV hx⟩))).2 h1
    rw [actTil_mk] at h2
    obtain ⟨y, hyX, hy⟩ := (mem_imgTil ⊥ V hV X _).1 (hE ▸ h2)
    have h3 : y.val * (((actStab ⊥ V hV ⟨g, hstg⟩) (IntMod.mk hV ⟨x, hXV hx⟩)).val)⁻¹ ∈
        (⊥ : Subgroup G) := (mkTil_eq_iff ⊥ V hV y _).1 hy
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h3
    have hval : ((actStab ⊥ V hV ⟨g, hstg⟩) (IntMod.mk hV ⟨x, hXV hx⟩)).val = g * x * g⁻¹ := by
      rw [actStab_apply_val]
      rfl
    rw [hval] at h3
    rw [← h3]
    exact hyX
  intro m hm
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · intro hx
    simpa using key m⁻¹ ((preBarSub D.M ⊥ V hV P).inv_mem hm) x hx
  · intro hx
    have h := key m hm _ hx
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [e] at h

theorem exists_noncyclic_le_normalizer_of_stab {D : Data G} {V X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hXV : X ≤ V) {E : Subgroup (Vtil ⊥ V hV)}
    (hE : imgTil ⊥ V hV X = E)
    {p : ℕ} (hp : p.Prime) {P : Subgroup (MulAut (Vtil ⊥ V hV))} (hPM : P ≤ Mbar D.M ⊥ V hV)
    (hPp : IsPGroup p P) (hPc : ¬ IsCyclic P) (hP : P ≤ stabSub E) :
    ∃ Q : Subgroup G, Q ≤ normalizer (X : Set G) ∧ Q ≤ D.M ∧ IsPGroup p Q ∧ ¬ IsCyclic Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQpre, hQp, hQc⟩ := s16c167_exists_pSub_lift hV hPM hPp hPc
  refine ⟨Q, hQpre.trans (preBarSub_le_normalizer_of_stab hV hXV hE hP), ?_, hQp, hQc⟩
  intro q hq
  have h := hQpre hq
  exact (mem_preBarSub D.M ⊥ V hV P).1 h |>.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
