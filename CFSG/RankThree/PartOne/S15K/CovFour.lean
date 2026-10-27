module

public import CFSG.RankThree.PartOne.S15K.CovAt

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

@[expose] def KF158FourShort : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    Outcome152Four p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, ∀ K J : Subgroup G, IsKt p E t K → K ≤ J → autMovedInG E t ≤ K →
      p * Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) = Nat.card ↥A →
      J ∈ thetaCompCentralizer p (A ⊓ Subgroup.centralizer (J : Set G)) →
      (∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
        S = ⁅S, A⁆) →
      A ⊓ Subgroup.centralizer (J : Set G) = autFixedInG E t ∧
      ∃ s₁ ∈ reflectionSet p E, ∃ s₂ ∈ reflectionSet p E, s₁ ≠ t ∧ s₂ ≠ t ∧ s₁ ≠ s₂ ∧
        t * s₁ = s₁ * t ∧ t * s₂ = s₂ * t ∧ s₁ * s₂ = s₂ * s₁ ∧
        (∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
          conjAut E w hw * t * (conjAut E w hw)⁻¹ = s₁) ∧
        (∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
          conjAut E w hw * t * (conjAut E w hw)⁻¹ = s₂)

variable {G : Type} [Group G] [Finite G]

theorem kf158CovAtRowFour_of_short (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hShort : KF158FourShort) : KF158CovAtRowFour := by
  intro G _ _ p A c L E h15 hF h13 hout t ht K J hKt hKJ hmov hcard hJθ hS2 a ha
  refine Or.inl ?_
  obtain ⟨hD, s₁, hs₁, s₂, hs₂, hne₁, hne₂, hne₁₂, hc₁, hc₂, hc₁₂, ⟨w₁, hw₁, hw₁t⟩, ⟨w₂, hw₂, hw₂t⟩⟩ :=
    hShort G p A c L E h15 hF h13 hout t ht K J hKt hKJ hmov hcard hJθ hS2
  have h := h15.h12
  have hp := h.prime
  have hEA : E = A := by
    obtain ⟨-, -, -, -, -, hEA, -⟩ := hout
    exact hEA
  have C := reflCtx_of_hyp h
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  obtain ⟨ã, hã, hãa, hã1⟩ := exists_mem_autMoved_of_zpowers C.prime ht.1.2 ha
  have ha1 : a ≠ 1 := fun h1 => hã1 (Subtype.ext (hãa.trans h1))
  have htt := ReflCtx.mul_self_eq_one_of ht.1
  have hss₁ := ReflCtx.mul_self_eq_one_of hs₁.1
  have hss₂ := ReflCtx.mul_self_eq_one_of hs₂.1
  have key : ∀ (s : MulAut E) (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      conjAut E w hw * t * (conjAut E w hw)⁻¹ = s → a ∈ autFixedInG E s →
        autMovedInG E s ≤ zeroLayer p E a := by
    intro s w hw hws hfix
    have hfix' : a ∈ conjBy w (autFixedInG E t) := by
      rw [← Equivariance.autFixedInG_conj t hw, hws]
      exact hfix
    have hb : w⁻¹ * a * w ∈ autFixedInG E t := Equivariance.mem_conjBy.1 hfix'
    have hbD : w⁻¹ * a * w ∈ A ⊓ Subgroup.centralizer (J : Set G) := hD ▸ hb
    have hb1 : w⁻¹ * a * w ≠ 1 := by
      intro h1
      apply ha1
      have : a = w * (w⁻¹ * a * w) * w⁻¹ := by group
      rw [this, h1]
      group
    have hXb := Sec158.layer_ge_of_KF158A hS h82 h15 hcard hJθ hS2 hbD hb1
    have h2 : conjBy w (zeroLayer p E (w⁻¹ * a * w)) = zeroLayer p E a := by
      rw [← Sec158.zeroLayer_conjBy hp hw]
      congr 1
      group
    calc autMovedInG E s = conjBy w (autMovedInG E t) := by
          rw [← hws]
          exact Equivariance.autMovedInG_conj t hw
      _ ≤ conjBy w (zeroLayer p E (w⁻¹ * a * w)) :=
          Subgroup.map_mono (hmov.trans (hKJ.trans hXb))
      _ = zeroLayer p E a := h2
  have hfix₁ : a ∈ autFixedInG E s₁ :=
    ⟨ã, C.fixes_moved hss₁ htt hc₁.symm hs₁.1.2 ht.1.2 hne₁ hã, hãa⟩
  have hfix₂ : a ∈ autFixedInG E s₂ :=
    ⟨ã, C.fixes_moved hss₂ htt hc₂.symm hs₂.1.2 ht.1.2 hne₂ hã, hãa⟩
  have h₁ := key s₁ w₁ hw₁ hw₁t hfix₁
  have h₂ := key s₂ w₂ hw₂ hw₂t hfix₂
  have hsup := C.eq_sup_of_three ht.1 hs₁.1 hs₂.1 hc₁ hc₂ hc₁₂ hne₁.symm hne₂.symm hne₁₂ hE3
  refine le_of_sup_eq_top hsup ?_ ?_
  · show autMovedInG E t ≤ _
    rw [← ha]
    exact le_sup_right
  · rw [Subgroup.map_sup]
    exact le_sup_of_le_left (sup_le h₁ h₂)

end CFSG.RankThree.PartOne.S15K
