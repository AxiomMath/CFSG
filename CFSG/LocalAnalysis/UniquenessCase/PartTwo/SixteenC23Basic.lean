module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSetupB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteenSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem c23_uniqueMax_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {E X : Subgroup G} (hE : IsPGroup p E) (hEc : ¬ IsCyclic E) (hEX : E ≤ X) (hXM : X ≤ D.M) :
    UniqueMax D.M X :=
  ElevenFourteen.uniqueMax_of_le D.maxLocal (h61 p hp E (hEX.trans hXM) hE hEc) hEX hXM

private theorem c23_eq_of_mem_zpowers {w x : G} (hw2 : w ^ 2 = 1) (hx : x ∈ Subgroup.zpowers w)
    (hx1 : x ≠ 1) : x = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · exfalso
    apply hx1
    rw [zpow_mul]
    simp [hw2]
  · rw [zpow_add, zpow_mul]
    simp [hw2]

theorem c23_gamma_le_of_centralizer_le {M : Subgroup G} {w : G} (hw2 : w ^ 2 = 1)
    (hC : centralizer ({w} : Set G) ≤ M) : rankThreeGamma 1 2 (Subgroup.zpowers w) ≤ M := by
  refine rankThreeGamma_le_of_normalizer_le (V₀ := Subgroup.zpowers w) (fun X hX hX1 => ?_)
    le_rfl
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX1
  have hxw : (x : G) = w :=
    c23_eq_of_mem_zpowers hw2 (hX x.2) (fun h => hx1 (Subtype.ext h))
  have hwX : w ∈ X := hxw ▸ x.2
  intro n hn
  have hn' : n * w * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hn w).1 hwX
  have hne : n * w * n⁻¹ ≠ 1 := fun h => by
    have : w = 1 := by simpa using h
    exact hx1 (Subtype.ext (hxw.trans this))
  have hnw : n * w * n⁻¹ = w := c23_eq_of_mem_zpowers hw2 (hX hn') hne
  apply hC
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact (mul_inv_eq_iff_eq_mul.1 hnw).symm

theorem c23_inf_conjSubgroup_eq_bot (D : Data G) (h22 : R1622 D) {V₀ V : Subgroup G}
    (h : Hyp16 D V₀ V) {U : Subgroup G} (hUV : U ≤ V)
    (hU : ∀ w ∈ U, w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) {g : G}
    (hg : g ∉ D.M) : V ⊓ conjSubgroup U g = ⊥ := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  by_contra ha1
  obtain ⟨haV, haU⟩ := Subgroup.mem_inf.mp ha
  have huU : g * a * g⁻¹ ∈ U := mem_conjSubgroup_iff.mp haU
  have hu1 : g * a * g⁻¹ ≠ 1 := by
    intro hc
    apply ha1
    have hconj : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [hconj, hc]
    simp
  have huV : g * a * g⁻¹ ∈ V := hUV huU
  have hu2 : (g * a * g⁻¹) ^ 2 = 1 := by simpa using hV.2 (g * a * g⁻¹) huV
  have hC : centralizer ({g * a * g⁻¹} : Set G) ≤ D.M :=
    (centralizer_le_of_uniqueMax D.maxLocal hu1 ⟨1, by simpa using hu2⟩
      (hU (g * a * g⁻¹) huU hu1)).1
  have hΓ : rankThreeGamma 1 2 (Subgroup.zpowers (g * a * g⁻¹)) ≤ D.M :=
    c23_gamma_le_of_centralizer_le hu2 hC
  have h22' := h22 V₀ V h g hg (Subgroup.zpowers (g * a * g⁻¹))
    (Subgroup.zpowers_le.2 huV) hΓ
  have hv : a ∈ conjSubgroup (Subgroup.zpowers (g * a * g⁻¹)) g ⊓ V :=
    Subgroup.mem_inf.2 ⟨mem_conjSubgroup_iff.2 (Subgroup.mem_zpowers _), haV⟩
  rw [h22', Subgroup.mem_bot] at hv
  exact ha1 hv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
