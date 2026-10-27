module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec52C
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81S0
import CFSG.RankThree.PartTwo.Sec21.FF81J
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}
  {M : Subgroup G}

theorem A₁_le_M (h526 : FF81Conc5_2_6 b b₁ b₂ b₃ s₀) (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) :
    Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) ≤ M := by
  obtain ⟨-, ⟨-, hAH, -⟩, -⟩ := h526
  exact hAH.trans hM7.2.2.2.2.2

theorem b_mem_A₁ : b ∈ Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem b₁_mem_A₁ : b₁ ∈ Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem b₂b₃_mem_A₁ : b₂ * b₃ ∈ Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem conj_eq_of_mem_cenS {t x : G} (ht : t ∈ CenS L) (hx : x ∈ L) : t * x * t⁻¹ = x := by
  rw [← Subgroup.mem_centralizer_iff.mp ht x hx, mul_inv_cancel_right]

theorem β_mem_L (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) : β' b₂ b₃ ∈ L :=
  L.mul_mem h5.basis.hb₂ (L.pow_mem h5.basis.hb₃ 2)

theorem t₀_mem_M (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) :
    t₀ ∈ M := by
  apply hM7.2.2.2.2.2
  refine ⟨?_, ?_⟩
  · have hle : Subgroup.closure ({β' b₂ b₃, s₀} : Set G) ≤ L := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact β_mem_L h5
      · exact h5.hs₀L
    exact Subgroup.centralizer_le hle h5.ht₀L
  · refine mem_nor_of_gen fun x hx => ?_
    rcases hx with rfl | rfl | rfl
    · rw [h5.ht₀b]
      exact Subgroup.inv_mem _ b_mem_A₁
    · rw [conj_eq_of_mem_cenS h5.ht₀L h5.basis.hb₁]
      exact b₁_mem_A₁
    · rw [conj_eq_of_mem_cenS h5.ht₀L (L.mul_mem h5.basis.hb₂ h5.basis.hb₃)]
      exact b₂b₃_mem_A₁

theorem s₀_mem_cenS_M (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) : s₀ ∈ CenS M :=
  Subgroup.mem_centralizer_iff.mpr fun m hm =>
    (Subgroup.mem_centralizer_iff.mp (hM7.1 hm) s₀ (Subgroup.subset_closure (by simp))).symm

theorem M_le_cen_β (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) : M ≤ Cen (β' b₂ b₃) := fun m hm =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (hM7.1 hm) (β' b₂ b₃)
      (Subgroup.subset_closure (by simp))).symm

theorem card_A₁ (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) :
    Nat.card (Subgroup.closure ({b, b₁, b₂ * b₃} : Set G)) = 27 := by
  have hbij : Function.Bijective (fun v : {v : P51.V // v 2 = v 3} =>
      (⟨h5.ε v.1, h5.mem_A₁_of v.2⟩ : Subgroup.closure ({b, b₁, b₂ * b₃} : Set G))) := by
    refine ⟨fun v w h => ?_, fun x => ?_⟩
    · exact Subtype.ext (h5.ε_inj (congrArg Subtype.val h))
    · obtain ⟨v, hv, hx⟩ := h5.coord_of_mem_A₁ x.2
      exact ⟨⟨v, hv⟩, Subtype.ext hx⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card]
  decide +kernel

theorem isElemAb_A₁ (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) :
    IsElemAb 3 3 (Subgroup.closure ({b, b₁, b₂ * b₃} : Set G)) :=
  ⟨CFSG.IsElementaryAbelian.of_le h5.hE.1 h5.A₁_le_B', by rw [card_A₁ h5]; norm_num⟩

section C

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem comm_b_b₁ : b * b₁ = b₁ * b :=
  comm_of_isElemAb (isElemAb_A₁ h5) b b_mem_A₁ b₁ b₁_mem_A₁

theorem b₁_cube_A₁ : b₁ ^ 3 = 1 := pow_three_eq_one_of_isElemAb (isElemAb_A₁ h5) b₁_mem_A₁

theorem c₂_mul_c₃ : (b * b₁) * (b⁻¹ * b₁) = b₁ ^ 2 := by
  have hc : Commute b b₁ := comm_b_b₁ h5
  calc b * b₁ * (b⁻¹ * b₁) = b * (b₁ * b⁻¹) * b₁ := by group
    _ = b * (b⁻¹ * b₁) * b₁ := by rw [hc.symm.inv_right.eq]
    _ = b₁ * b₁ := by group
    _ = b₁ ^ 2 := (sq b₁).symm

theorem c₂_mul_c₃_sq : (b * b₁) * (b⁻¹ * b₁) ^ 2 = b⁻¹ := by
  have hc : Commute b b₁ := comm_b_b₁ h5
  have h1 : b₁ ^ 3 = 1 := b₁_cube_A₁ h5
  have hc' : Commute b⁻¹ b₁ := hc.inv_left
  calc b * b₁ * (b⁻¹ * b₁) ^ 2 = b * b₁ * (b⁻¹ ^ 2 * b₁ ^ 2) := by rw [hc'.mul_pow]
    _ = b * (b₁ * b⁻¹ ^ 2) * b₁ ^ 2 := by group
    _ = b * (b⁻¹ ^ 2 * b₁) * b₁ ^ 2 := by rw [(hc.symm.inv_right.pow_right 2).eq]
    _ = b⁻¹ * b₁ ^ 3 := by group
    _ = b⁻¹ := by rw [h1, mul_one]

theorem inv_mul_eq : b⁻¹ * b₁ = (b * b₁ ^ 2)⁻¹ := by
  have hc : Commute b b₁ := comm_b_b₁ h5
  have h1 : b₁ ^ 3 = 1 := b₁_cube_A₁ h5
  have : b₁⁻¹ = b₁ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h1])
  rw [mul_inv_rev, ← this, inv_inv, hc.symm.inv_right.eq]

theorem closure_c_eq :
    Subgroup.closure ({b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G) =
      Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) := by
  have h1 : b₁ ^ 3 = 1 := b₁_cube_A₁ h5
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact b₂b₃_mem_A₁
    · exact Subgroup.mul_mem _ b_mem_A₁ b₁_mem_A₁
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ b_mem_A₁) b₁_mem_A₁
  · rw [Subgroup.closure_le]
    have hc2 : b * b₁ ∈ Subgroup.closure ({b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hc3 : b⁻¹ * b₁ ∈ Subgroup.closure ({b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hb₁sq : b₁ ^ 2 ∈ Subgroup.closure ({b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G) := by
      rw [← c₂_mul_c₃ h5]; exact Subgroup.mul_mem _ hc2 hc3
    have hb₁ : b₁ ∈ Subgroup.closure ({b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G) := by
      have := Subgroup.pow_mem _ hb₁sq 2
      rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h1, one_mul, pow_one] at this
    rintro x (rfl | rfl | rfl)
    · have := Subgroup.mul_mem _ hc2 (Subgroup.inv_mem _ hb₁)
      rwa [mul_inv_cancel_right] at this
    · exact hb₁
    · exact Subgroup.subset_closure (by simp)

theorem M_mono (h526 : FF81Conc5_2_6 b b₁ b₂ b₃ s₀) (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) :
    ∀ n ∈ M, n ∈ Nor (Subgroup.closure ({b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G)) →
      ∀ x ∈ ({b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G),
        n * x * n⁻¹ ∈ ({b₂ * b₃, (b₂ * b₃)⁻¹, b * b₁, (b * b₁)⁻¹, b⁻¹ * b₁, (b⁻¹ * b₁)⁻¹} :
          Set G) := by
  intro n hnM hnN x hx
  rw [closure_c_eq h5] at hnN
  obtain ⟨-, ⟨-, -, -, hmon, -⟩, -⟩ := h526
  have hnH : n ∈ CenS (Subgroup.closure ({β' b₂ b₃, s₀} : Set G)) ⊓
      Nor (Subgroup.closure ({b, b₁, b₂ * b₃} : Set G)) := ⟨hM7.1 hnM, hnN⟩
  have e1 := inv_mul_eq h5
  have e2 : b * b₁ ^ 2 = (b⁻¹ * b₁)⁻¹ := by rw [e1, inv_inv]
  rcases hx with rfl | rfl | rfl
  · have := hmon n hnH (b₂ * b₃) (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, e2, inv_inv] at this ⊢
    tauto
  · have := hmon n hnH (b * b₁) (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, e2, inv_inv] at this ⊢
    tauto
  · have := hmon n hnH (b * b₁ ^ 2) (by simp)
    have e3 : n * (b⁻¹ * b₁) * n⁻¹ = (n * (b * b₁ ^ 2) * n⁻¹)⁻¹ := by rw [e1]; group
    rw [e3]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, e2, inv_inv] at this ⊢
    rcases this with h | h | h | h | h | h <;> rw [h] <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, inv_inv, true_or, or_true]

theorem closure_β_c_eq :
    Subgroup.closure ({β' b₂ b₃, b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G) =
      Subgroup.closure ({b, b₁, b₂, b₃} : Set G) := by
  obtain ⟨-, -, -, h23⟩ := triple_facts h5.basis.elem
  have hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
  have hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
  have hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
  have hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact Subgroup.mul_mem _ hb₂B (Subgroup.pow_mem _ hb₃B 2)
    · exact Subgroup.mul_mem _ hb₂B hb₃B
    · exact Subgroup.mul_mem _ hbB hb₁B
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hbB) hb₁B
  · have hA : Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) ≤
        Subgroup.closure ({β' b₂ b₃, b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G) := by
      rw [← closure_c_eq h5]
      exact Subgroup.closure_mono (fun x hx => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    have hβ : β' b₂ b₃ ∈ Subgroup.closure ({β' b₂ b₃, b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hb₃ : b₃ ∈ Subgroup.closure ({β' b₂ b₃, b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G) := by
      have := Subgroup.mul_mem _ hβ (Subgroup.inv_mem _ (hA b₂b₃_mem_A₁))
      rwa [show β' b₂ b₃ * (b₂ * b₃)⁻¹ = b₃ by
        calc β' b₂ b₃ * (b₂ * b₃)⁻¹ = b₂ * b₃ * b₃ * b₃⁻¹ * b₂⁻¹ := by simp only [β']; group
          _ = b₂ * b₃ * b₂⁻¹ := by group
          _ = b₃ := by rw [h23]; group] at this
    have hb₂ : b₂ ∈ Subgroup.closure ({β' b₂ b₃, b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G) := by
      have := Subgroup.mul_mem _ (hA b₂b₃_mem_A₁) (Subgroup.inv_mem _ hb₃)
      rwa [mul_inv_cancel_right] at this
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact hA b_mem_A₁
    · exact hA b₁_mem_A₁
    · exact hb₂
    · exact hb₃

end C

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
