module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Root
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6Disc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem rankTwo_linearIndependent_of_gramDet3_ne_zero
    {x y z : Fin Tag.E6.rank → ℤ} (hx : iform x x = 2) (hy : iform y y = 2)
    (hz : iform z z = 2) (hg : gramDet3 x y z ≠ 0) : LinearIndependent ℤ ![x, y, z] := by
  have h0 : ∀ v : Fin Tag.E6.rank → ℤ, iform 0 v = 0 := fun v => by
    simpa using iform_smul_left (0 : ℤ) v v
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have hsum' : g 0 • x + g 1 • y + g 2 • z = 0 := by
    simpa [Fin.sum_univ_three] using hsum
  have ex : 2 * g 0 + iform x y * g 1 + iform x z * g 2 = 0 := by
    have h := congrArg (fun v => iform v x) hsum'
    simp only [iform_add_left, iform_smul_left, smul_eq_mul, h0, hx, iform_comm y x,
      iform_comm z x] at h
    linear_combination h
  have ey : iform x y * g 0 + 2 * g 1 + iform y z * g 2 = 0 := by
    have h := congrArg (fun v => iform v y) hsum'
    simp only [iform_add_left, iform_smul_left, smul_eq_mul, h0, hy, iform_comm z y] at h
    linear_combination h
  have ez : iform x z * g 0 + iform y z * g 1 + 2 * g 2 = 0 := by
    have h := congrArg (fun v => iform v z) hsum'
    simp only [iform_add_left, iform_smul_left, smul_eq_mul, h0, hz] at h
    linear_combination h
  have k0 : gramDet3 x y z * g 0 = 0 := by
    unfold gramDet3
    linear_combination (4 - iform y z ^ 2) * ex
      + (iform x z * iform y z - 2 * iform x y) * ey
      + (iform x y * iform y z - 2 * iform x z) * ez
  have k1 : gramDet3 x y z * g 1 = 0 := by
    unfold gramDet3
    linear_combination (iform x z * iform y z - 2 * iform x y) * ex
      + (4 - iform x z ^ 2) * ey
      + (iform x y * iform x z - 2 * iform y z) * ez
  have k2 : gramDet3 x y z * g 2 = 0 := by
    unfold gramDet3
    linear_combination (iform x y * iform y z - 2 * iform x z) * ex
      + (iform x y * iform x z - 2 * iform y z) * ey
      + (4 - iform x y ^ 2) * ez
  have hg0 : g 0 = 0 := (mul_eq_zero.1 k0).resolve_left hg
  have hg1 : g 1 = 0 := (mul_eq_zero.1 k1).resolve_left hg
  have hg2 : g 2 = 0 := (mul_eq_zero.1 k2).resolve_left hg
  fin_cases i
  exacts [hg0, hg1, hg2]

theorem rankTwo_three_le_finrank_of_linearIndependent
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} {x y z : Fin Tag.E6.rank → ℤ}
    (hx : x ∈ Ψ) (hy : y ∈ Ψ) (hz : z ∈ Ψ) (hli : LinearIndependent ℤ ![x, y, z]) :
    3 ≤ Module.finrank ℤ (Submodule.span ℤ Ψ) := by
  have h1 : Module.finrank ℤ (Submodule.span ℤ (Set.range ![x, y, z])) = 3 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have h2 : Submodule.span ℤ (Set.range ![x, y, z]) ≤ Submodule.span ℤ Ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span hx
    · exact Submodule.subset_span hy
    · exact Submodule.subset_span hz
  have h3 := Submodule.finrank_mono h2
  omega

theorem rankTwo_gramDet3_eq_zero
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hr : Module.finrank ℤ (Submodule.span ℤ Ψ) = 2)
    {α β γ : Fin Tag.E6.rank → ℤ} (hα : α ∈ Ψ) (hβ : β ∈ Ψ) (hγ : γ ∈ Ψ)
    (hα2 : iform α α = 2) (hβ2 : iform β β = 2) (hγ2 : iform γ γ = 2) :
    gramDet3 α β γ = 0 := by
  by_contra hne
  have h3 := rankTwo_three_le_finrank_of_linearIndependent hα hβ hγ
    (rankTwo_linearIndependent_of_gramDet3_ne_zero hα2 hβ2 hγ2 hne)
  omega

theorem rankTwo_ab_of_bounds (a b : ℤ) (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hb1 : -1 ≤ b)
    (hb2 : b ≤ 1) (h : 8 + 2 * (-1 * a * b) - 2 * ((-1) ^ 2 + a ^ 2 + b ^ 2) = 0) :
    (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
  interval_cases a <;> interval_cases b <;> simp_all

theorem isRootComponent_rank_two_E6
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hr : Module.finrank ℤ (Submodule.span ℤ Ψ) = 2) :
    ∃ α β : Fin Tag.E6.rank → ℤ, iform α β = -1 ∧ Ψ = tcA2Set α β := by
  have hnorm : ∀ x ∈ Ψ, iform x x = 2 := fun x hx =>
    e6_iform_self x (mem_rootFinset.2 (hΨ.isRoot x hx))
  obtain ⟨α, hα, β₀, hβ₀, hne1, hne2, hs0⟩ := exists_pair_ne_of_two_le_finrank_span hΨ hr.ge
  have hα2 : iform α α = 2 := hnorm α hα
  obtain ⟨hl, hu⟩ := abs_iform_le_one hα2 (hnorm β₀ hβ₀) hne1 hne2
  obtain ⟨β, hβ, hβ2, hs⟩ : ∃ β ∈ Ψ, iform β β = 2 ∧ iform α β = -1 := by
    rcases (show iform α β₀ = 1 ∨ iform α β₀ = -1 by omega) with h | h
    · refine ⟨-β₀, hΨ.neg_mem _ hβ₀, ?_, ?_⟩
      · rw [iform_neg_left_eq_neg, iform_neg_right_eq_neg, neg_neg, hnorm β₀ hβ₀]
      · rw [iform_neg_right_eq_neg, h]
    · exact ⟨β₀, hβ₀, hnorm β₀ hβ₀, h⟩
  have hne : α ≠ -β := by
    intro h
    rw [h, iform_neg_left_eq_neg, hβ2] at hs
    norm_num at hs
  have hroot : IsRoot Tag.E6 (α + β) :=
    isRoot_add_of_iform_neg (hΨ.isRoot α hα) (hΨ.isRoot β hβ) hne (by rw [hs]; norm_num)
  have hsum : α + β ∈ Ψ := hΨ.add_mem α hα β hβ hroot
  have hA : tcA2Set α β ⊆ Ψ := by
    intro x hx
    simp only [tcA2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hα
    · exact hβ
    · exact hsum
    · exact hΨ.neg_mem _ hα
    · exact hΨ.neg_mem _ hβ
    · exact hΨ.neg_mem _ hsum
  refine ⟨α, β, hs, Set.Subset.antisymm ?_ hA⟩
  intro γ hγ
  simp only [tcA2Set, Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases hA' : γ = α ∨ γ = -α ∨ γ = β ∨ γ = -β
  · rcases hA' with h | h | h | h <;> simp [h]
  · push Not at hA'
    obtain ⟨hga, hga', hgb, hgb'⟩ := hA'
    have hγ2 : iform γ γ = 2 := hnorm γ hγ
    obtain ⟨ha1, ha2⟩ := abs_iform_le_one hα2 hγ2 hga hga'
    obtain ⟨hb1, hb2⟩ := abs_iform_le_one hβ2 hγ2 hgb hgb'
    have hG := rankTwo_gramDet3_eq_zero hr hα hβ hγ hα2 hβ2 hγ2
    unfold gramDet3 at hG
    rw [hs] at hG
    rcases rankTwo_ab_of_bounds (iform α γ) (iform β γ) ha1 ha2 hb1 hb2
        (by linear_combination hG) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hδ : iform (γ - (α + β)) (γ - (α + β)) = 0 := by
        simp only [iform_sub_left, iform_sub_right, iform_add_left, iform_add_right]
        norm_num [hγ2, hα2, hβ2, hs, ha, hb, iform_comm γ α, iform_comm γ β, iform_comm β α]
      have hz : γ = α + β := sub_eq_zero.1 (vec_eq_zero_of_iform_self_eq_zero hδ)
      simp [hz]
    · have hδ : iform (γ + (α + β)) (γ + (α + β)) = 0 := by
        simp only [iform_add_left, iform_add_right]
        norm_num [hγ2, hα2, hβ2, hs, ha, hb, iform_comm γ α, iform_comm γ β, iform_comm β α]
      have hz : γ = -(α + β) := eq_neg_of_add_eq_zero_left (vec_eq_zero_of_iform_self_eq_zero hδ)
      simp [hz]

end CFSG.StandardType.TableCRes

end
