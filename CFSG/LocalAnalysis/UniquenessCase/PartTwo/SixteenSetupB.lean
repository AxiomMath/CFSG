module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.LocalAnalysis.WeakClosure81.SixTwo
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16b_eq_of_mem_zpowers {w x : G} (hw2 : w ^ 2 = 1) (hx : x ∈ Subgroup.zpowers w)
    (hx1 : x ≠ 1) : x = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · exfalso
    apply hx1
    rw [zpow_mul]
    simp [hw2]
  · rw [zpow_add, zpow_mul]
    simp [hw2]

private theorem s16b_gamma_le_of_centralizer_le {M : Subgroup G} {w : G} (hw2 : w ^ 2 = 1)
    (hC : centralizer ({w} : Set G) ≤ M) : rankThreeGamma 1 2 (Subgroup.zpowers w) ≤ M := by
  refine rankThreeGamma_le_of_normalizer_le (V₀ := Subgroup.zpowers w) (fun X hX hX1 => ?_)
    le_rfl
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX1
  have hxw : (x : G) = w :=
    s16b_eq_of_mem_zpowers hw2 (hX x.2) (fun h => hx1 (Subtype.ext h))
  have hwX : w ∈ X := hxw ▸ x.2
  intro n hn
  have hn' : n * w * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hn w).1 hwX
  have hne : n * w * n⁻¹ ≠ 1 := fun h => by
    have : w = 1 := by simpa using h
    exact hx1 (Subtype.ext (hxw.trans this))
  have hnw : n * w * n⁻¹ = w := s16b_eq_of_mem_zpowers hw2 (hX hn') hne
  apply hC
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact (mul_inv_eq_iff_eq_mul.1 hnw).symm

theorem exists_centralizer_not_le (D : Data G) (h129 : R129_1 D) (h22 : R1622 D)
    {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) :
    ∃ z ∈ V, z ≠ 1 ∧ ¬ centralizer ({z} : Set G) ≤ D.M := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hTI := h129 V₀ V h.hyp125
  obtain ⟨g, hg⟩ : ∃ g : G, ¬ (V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = ⊥ ∨
      V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = V) := by
    by_contra hcon
    exact hTI fun g => by
      by_contra hg
      exact hcon ⟨g, hg⟩
  rw [not_or] at hg
  obtain ⟨hg0, hgV⟩ := hg
  have hgM : g ∉ D.M := by
    intro hgM
    apply hgV
    have hgN : g ∈ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer hgM
    have hconj : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V := by
      ext x
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      exact (Subgroup.mem_normalizer_iff''.1 hgN x).symm
    rw [hconj, inf_idem]
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V, w ≠ 1 := by
    by_contra hcon
    apply hg0
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hcon ⟨x, hx, hx1⟩
  have hw2 : w ^ 2 = 1 := by simpa using hV.2 w hw.1
  refine ⟨w, hw.1, hw1, fun hC => ?_⟩
  have hUV : Subgroup.zpowers w ≤ V := (Subgroup.zpowers_le).2 hw.1
  have h22' := h22 V₀ V h g hgM (Subgroup.zpowers w) hUV (s16b_gamma_le_of_centralizer_le hw2 hC)
  have hv : g⁻¹ * w * g ∈ conjSubgroup (Subgroup.zpowers w) g ⊓ V := by
    refine Subgroup.mem_inf.2 ⟨?_, CFSG.CGT.Timmesfeld75.mem_conjSubgroup.1 hw.2⟩
    rw [mem_conjSubgroup_iff]
    have e : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
    rw [e]
    exact Subgroup.mem_zpowers w
  rw [h22', Subgroup.mem_bot] at hv
  apply hw1
  have e : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
  rw [e, hv]
  group

@[expose] def R16_45b (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L →
      ∀ x : IntMod V hV, Setup1645 D V hV x →
        (∀ Q : Vtil V₀ V hV → ZMod 2, IsMinusQuadF2 Q → QuadInvariant Q (lBar V₀ V hV L) →
            Q (mkTil V₀ V hV x) = 0) ∧
        IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)) ∧
        IsE16A5 ↥(barSub V₀ V hV (xInf L x.val)) ∧
        CFSG.Open.pRank 3 (centralizer ({x.val} : Set G)) = 1 ∧
        ∀ q : ℕ, q.Prime → 3 < q → CFSG.Open.pRank q (centralizer ({x.val} : Set G)) ≤ 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
