module

public import CFSG.Quasithin.Vol2.Ch11SecA15Excl2
public import CFSG.Quasithin.Background.C134L32CorrM
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch11SecA15Kill

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

variable {G : Type} [Group G]

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem not_isC134Case4W (hF : Facts15) (hF11 : Facts11) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) : ¬ CFSG.Quasithin.C134Case4Min (L ⊔ ROf T L V₁) (ROf T L V₁) L := by
  rintro ⟨⟨a, F, _, _, α, hF', hα, -, -, ⟨hLU, -, β, hβs, hβker, hβ⟩, -, -⟩, hNC⟩
  obtain ⟨_, hirr, -, -, -⟩ := h1102 G T L I n h
  have hLZ : L ≤ Subgroup.normalizer (centerOf (c134Q (L ⊔ ROf T L V₁) L) : Set G) :=
    le_normalizer_centerOf L_le_normalizer_c134Q
  have hVU : fsuV T I ≤ ⁅centerOf (c134Q (L ⊔ ROf T L V₁) L), L⁆ :=
    calc fsuV T I = ⁅fsuV T I, L⁆ := hirr.2.2.2.1.symm
      _ ≤ ⁅centerOf (c134Q (L ⊔ ROf T L V₁) L), L⁆ :=
          Subgroup.commutator_mono (fsuV_le_centerOf_c134Q h1102 h) le_rfl
  have hzU : ∀ z ∈ centerOf (T ⊓ (L ⊔ ROf T L V₁)), ∀ l ∈ L,
      l * z * l⁻¹ * z⁻¹ ∈ ⁅centerOf (c134Q (L ⊔ ROf T L V₁) L), L⁆ := by
    intro z hz
    refine commutator_mem_of_perfect h.fsu.faithful.1.2.1.2.1
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hLZ) (fun a ha a' ha' => ?_)
      (fun l hl a ha => ?_) (fun l hl => commutator_mem_centerOf_c134Q h hz hl)
    · have hcomm : a * a' = a' * a := Subgroup.mem_centralizer_iff.mp ha'.2 a ha.1
      have : a * a' * a⁻¹ * a'⁻¹ = 1 := by
        rw [hcomm]
        group
      rw [this]
      exact Subgroup.one_mem _
    · have := Subgroup.commutator_mem_commutator hl ha
      rw [Subgroup.commutator_comm, commutatorElement_def] at this
      exact this
  exact false_of_notCentralizerCore h hNC (ROf_eq_pCoreOf_centralizer hF hF11 hG2 h1102 h1103
    h1110 h hU hF' hα β hβs (injective_of_ker_eq_bot_subgroupOf hβker)
    (fun l u v huv i => by simpa [moduleAct] using hβ l u v huv i) hLU hVU hzU)

end CFSG.Quasithin.Vol2.Ch11.SecA
