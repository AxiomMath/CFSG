module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineHypAux

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
open CFSG.StandardType.FrameRoute.FS81.NineHyp
open scoped Matrix

private theorem wt_eq_four_of_zero_one_full {w : Coords (5 + 1)}
    (h0 : w 0 = 0) (h1 : w 1 = 0) (hfull : ∀ k : Fin 4, w k.succ.succ ≠ 0) :
    wt w = 4 := by
  unfold wt
  have hsupp : (Finset.univ.filter fun i : Fin (5 + 1) => w i ≠ 0) =
      ({2, 3, 4, 5} : Finset (Fin (5 + 1))) := by
    ext j
    fin_cases j
    · simp [h0]
    · simp [h1]
    · simpa using hfull 0
    · simpa using hfull 1
    · simpa using hfull 2
    · simpa using hfull 3
  rw [hsupp]
  norm_num

private theorem exists_centralizer_conj_b2_of_full_support {G : Type} [Group G] [Finite G]
    {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (B.span : Set G))))
    {t : G} (ht : orderOf t = 2) (hActsT : B.Acts t tMat)
    {w : Coords (5 + 1)} (hw0 : w 0 = 0) (hw1 : w 1 = 0)
    (hfull : ∀ k : Fin 4, w k.succ.succ ≠ 0) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set G), c * B.b 2 * c⁻¹ = B.vec w := by
  classical
  obtain ⟨w₀, c₀, hc₀C, hfull₀, hw₀0, hw₀1, heq₀⟩ :=
    exists_centralizer_conj_b2_full (K := K) (E := E) hB hrec hfus hodd ht hActsT
  have hwt : wt w₀ = wt w := by
    rw [wt_eq_four_of_zero_one_full hw₀0 hw₀1 hfull₀,
      wt_eq_four_of_zero_one_full hw0 hw1 hfull]
  obtain ⟨A, hAmem, hAeq, hAcomm⟩ :=
    exists_evenAll0_map_of_zero_one hwt hw₀0 hw₀1 hw0 hw1
  obtain ⟨cA, hcAC, hcAActs⟩ :=
    exists_centralizer_acts_evenAll0 hrec hodd ht hActsT hAmem hAcomm
  refine ⟨cA * c₀, (Subgroup.centralizer ({t} : Set G)).mul_mem hcAC hc₀C, ?_⟩
  calc (cA * c₀) * B.b 2 * (cA * c₀)⁻¹ = cA * (c₀ * B.b 2 * c₀⁻¹) * cA⁻¹ := by group
    _ = cA * B.vec w₀ * cA⁻¹ := by rw [heq₀]
    _ = B.vec (A *ᵥ w₀) := B.acts_vec hcAActs w₀
    _ = B.vec w := by rw [hAeq]

theorem exists_centralizer_conj_mem_hyperplane_of_recOutTwD5 {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (E : Set G)))) {t : G} (ht : orderOf t = 2)
    (ht0 : t * B.b 0 * t⁻¹ = (B.b 0)⁻¹) (ht1 : t * B.b 1 * t⁻¹ = (B.b 1)⁻¹)
    (ht2 : ∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t) :
    ∀ H ∈ Coprime.hyperplanes 3
        (Subgroup.closure (Set.range fun i : Fin 4 => B.b i.succ.succ)),
      ∃ c ∈ Subgroup.centralizer ({t} : Set G), c * B.b 2 * c⁻¹ ∈ H := by
  intro H hH
  have hodd' : Odd (Nat.card ↥(Subgroup.centralizer (B.span : Set G))) := by
    simpa [hB.1] using hodd
  have hActsT : B.Acts t tMat := acts_tMat_of ht ht0 ht1 ht2
  obtain ⟨w, hwH, hwcase⟩ := hyperplane_special hH
  rcases hwcase with ⟨i, hw⟩ | hfull
  · obtain ⟨c, hcC, hceq⟩ :=
      exists_centralizer_conj_b2_coord hrec hodd' ht hActsT i
    refine ⟨c, hcC, ?_⟩
    rw [hceq]
    simpa [hw, ext4_single] using hwH
  · have hw0 : (ext4 w) 0 = 0 := rfl
    have hw1 : (ext4 w) 1 = 0 := rfl
    have hfull_ext : ∀ k : Fin 4, (ext4 w) k.succ.succ ≠ 0 := by
      intro k
      simpa [ext4] using hfull k
    obtain ⟨c, hcC, hceq⟩ :=
      exists_centralizer_conj_b2_of_full_support hB hrec hfus hodd' ht hActsT hw0 hw1 hfull_ext
    refine ⟨c, hcC, ?_⟩
    rw [hceq]
    exact hwH

end CFSG.StandardType.FrameRoute.FS81

end
