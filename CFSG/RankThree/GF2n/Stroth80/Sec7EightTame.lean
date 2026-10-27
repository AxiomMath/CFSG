module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EightAssembly

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step76EightTamePointStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
    (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t) →
    ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup r B ⊔ Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t)

section Tame

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_inv_le_of_le_conj {g : G} {A C : Subgroup G} (h : A ≤ conjSubgroup g C) :
    conjSubgroup g⁻¹ A ≤ C := by
  intro y hy
  have hy' : g * y * g⁻¹ ∈ A := by
    rw [mem_conjSubgroup] at hy
    simpa using hy
  have h1 := h hy'
  rw [mem_conjSubgroup] at h1
  have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  rwa [e] at h1

theorem step76EightTameConj_of_point (hP : Step76EightTamePointStatement)
    (h56 : Stroth56NatStatement) : Step76EightTameConjStatement := by
  intro G _ _ M Q Z B hc n t hs hno h4 Z0 hZ0 g hg hΓ htame
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r₁, hr₁R, hr₁le⟩ := hP G M Q Z B hc n t hs hno h4 Z0 hZ0 g hg hΓ htame
  have hr₁M : r₁ ∈ M := hc.Rt_le_M t hr₁R
  have hZVle : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hr₁le' : conjSubgroup r₁ B ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    le_trans le_sup_left hr₁le
  have hm₁M : g⁻¹ * r₁ ∈ M := M.mul_mem (M.inv_mem hg) hr₁M
  have hle : conjSubgroup (g⁻¹ * r₁) B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    apply sup_le
    · rw [conjSubgroup_mul]
      exact conj_inv_le_of_le_conj hr₁le'
    · exact hZVle
  obtain ⟨r₂, hr₂R, hE₁⟩ := h56 G M Q Z B hc n t hs
    (not_omegaMinus_two_of_cases (Or.inr (Or.inr h4))) (g⁻¹ * r₁) hm₁M hle
  have hr₂M : r₂ ∈ M := hc.Rt_le_M t hr₂R
  have hZg : conjSubgroup g Z = Z := conjSubgroup_eq_self_iff.mpr (hc.hyp.Z_normal.2 hg)
  have hsup : ∀ (A C : Subgroup G), conjSubgroup g (A ⊔ C) = conjSubgroup g A ⊔ conjSubgroup g C :=
    fun A C => by
      unfold conjSubgroup
      exact Subgroup.map_sup _ _ _
  have hA : conjSubgroup g (conjSubgroup (g⁻¹ * r₁) B) = conjSubgroup r₁ B := by
    rw [← conjSubgroup_mul]
    congr 1
    group
  have hB : conjSubgroup g (conjSubgroup r₂ B) = conjSubgroup (g * r₂) B := by
    rw [conjSubgroup_mul]
  have hE₂ : conjSubgroup (g * r₂) B ⊔ Z = conjSubgroup r₁ B ⊔ Z := by
    have h := congrArg (conjSubgroup g) hE₁
    rw [hsup, hA, hZg, hsup, hB, hZg] at h
    exact h.symm
  have hLB := hc.conj_LB_eq_of_conj_BZ (M.mul_mem hg hr₂M) hr₁M hE₂
  have hLB_le : Q ≤ LB M Q B := fun q hq => Subgroup.mem_sup_left hq
  have hx1 : (g * r₂)⁻¹ * (g * t * g⁻¹) * (g * r₂) ∈ LB M Q B := by
    have e : (g * r₂)⁻¹ * (g * t * g⁻¹) * (g * r₂) = ⁅r₂⁻¹, t⁆ * t := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have ht' : ⁅r₂⁻¹, t⁆ ∈ Q := hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hr₂R)
    exact (LB M Q B).mul_mem (hLB_le ht') ht
  have hx2 : g * t * g⁻¹ ∈ conjSubgroup (g * r₂) (LB M Q B) := mem_conjSubgroup.mpr hx1
  rw [hLB] at hx2
  have hx' : r₁⁻¹ * (g * t * g⁻¹) * r₁ ∈ LB M Q B := mem_conjSubgroup.mp hx2
  refine ⟨r₁, hr₁R, r₁⁻¹ * (g * t * g⁻¹) * r₁, hx', ?_, ?_⟩
  · refine ⟨M.mul_mem (M.mul_mem (M.inv_mem hr₁M) (M.mul_mem (M.mul_mem hg (hc.LB_le_M ht))
      (M.inv_mem hg))) hr₁M, r₁⁻¹ * g, M.mul_mem (M.inv_mem hr₁M) hg, ?_⟩
    have e : r₁⁻¹ * (g * t * g⁻¹) * r₁ * ((r₁⁻¹ * g) * t * (r₁⁻¹ * g)⁻¹)⁻¹ = 1 := by group
    rw [e]
    exact Q.one_mem
  · have e : g * t * g⁻¹ = r₁ * (r₁⁻¹ * (g * t * g⁻¹) * r₁) * r₁⁻¹ := by group
    exact (congrArg (Ut Q Z) e).trans
      (Ut_conj_of_normalizes (hc.conj_Q_eq hr₁M) (hc.conj_Z_eq hr₁M) _)

end Tame

end CFSG.RankThree.GF2n.Stroth80
