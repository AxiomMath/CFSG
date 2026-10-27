module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c15t_perm_fin_three_centralizer_cube :
    ∀ g h : Equiv.Perm (Fin 3), g ^ 3 = 1 → g ≠ 1 → h * g = g * h → h ^ 3 = 1 := by
  decide

theorem s16c15t_mem_right_of_commute_oddBar (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (h2 : Case168_2 D ⊥ V hV L)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hI : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    {x : MulAut (Vtil ⊥ V hV)} (hx : x ∈ Mbar D.M ⊥ V hV) (hx2 : x * x = 1)
    (hcomm : ∀ y ∈ oddBar D.M ⊥ V hV, x * y = y * x) : x ∈ L₀ := by
  classical
  obtain ⟨e⟩ := h2.1
  have hodd := s16c167_oddBar_case2 D h2
  obtain ⟨hKL, hdisj, hsup⟩ := hI
  have hKc : kBar D.M ⊥ V hV L ≤ Subgroup.centralizer (L₀ : Set (MulAut (Vtil ⊥ V hV))) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKL
  have hnorm : kBar D.M ⊥ V hV L ≤ Subgroup.normalizer (L₀ : Set (MulAut (Vtil ⊥ V hV))) :=
    hKc.trans (Subgroup.centralizer_le_normalizer _)
  have hxs : x ∈ (↑(kBar D.M ⊥ V hV L ⊔ L₀) : Set (MulAut (Vtil ⊥ V hV))) := by
    rw [hsup]
    exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hxs
  obtain ⟨κ, hκ, l, hl, hxe⟩ := hxs
  have hxe' : x = κ * l := hxe.symm
  subst hxe'
  have hlK : ∀ k ∈ kBar D.M ⊥ V hV L, l * k = k * l := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (hKc hk)) l hl
  have hκy : ∀ y ∈ oddBar D.M ⊥ V hV, κ * y = y * κ := by
    intro y hy
    have h1 := hcomm y hy
    have h2' := hlK y (hodd.1 hy)
    have h3 : (κ * y) * l = (y * κ) * l := by
      calc (κ * y) * l = κ * (y * l) := by rw [mul_assoc]
        _ = κ * (l * y) := by rw [h2']
        _ = κ * l * y := by rw [mul_assoc]
        _ = y * (κ * l) := h1
        _ = (y * κ) * l := by rw [mul_assoc]
    exact mul_right_cancel h3
  haveI : Nontrivial ↥(oddBar D.M ⊥ V hV) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h1 : Nat.card ↥(oddBar D.M ⊥ V hV) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [hodd.2] at h1
    norm_num at h1
  obtain ⟨y0, hy0⟩ := exists_ne (1 : ↥(oddBar D.M ⊥ V hV))
  have hy0cube : (y0 : ↥(oddBar D.M ⊥ V hV)) ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := y0) (G := ↥(oddBar D.M ⊥ V hV))
    rwa [hodd.2] at h
  let ky : ↥(kBar D.M ⊥ V hV L) := ⟨(y0 : MulAut (Vtil ⊥ V hV)), hodd.1 y0.2⟩
  have hkycube : ky ^ 3 = 1 := by
    apply Subtype.ext
    have h := congrArg (fun z : ↥(oddBar D.M ⊥ V hV) => (z : MulAut (Vtil ⊥ V hV))) hy0cube
    simpa [ky] using h
  have hkyne : ky ≠ 1 := by
    intro h
    apply hy0
    apply Subtype.ext
    have h' : (ky : MulAut (Vtil ⊥ V hV)) = 1 := congrArg Subtype.val h
    exact h'
  have hekycube : (e ky) ^ 3 = 1 := by rw [← map_pow, hkycube, map_one]
  have hekyne : e ky ≠ 1 := fun h => hkyne (e.injective (by rw [h, map_one]))
  have hκ3 : κ ^ 3 = 1 := by
    have hcomm' : e ⟨κ, hκ⟩ * e ky = e ky * e ⟨κ, hκ⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hκy y0 y0.2)
    have h3 := s16c15t_perm_fin_three_centralizer_cube (e ky) (e ⟨κ, hκ⟩) hekycube hekyne hcomm'
    have h4 : (⟨κ, hκ⟩ : ↥(kBar D.M ⊥ V hV L)) ^ 3 = 1 :=
      e.injective (by rw [map_pow, h3, map_one])
    have h5 := congrArg Subtype.val h4
    simpa using h5
  have hlκ : l * κ = κ * l := hlK κ hκ
  have hsq : κ ^ 2 * l ^ 2 = 1 := by
    have h1 : (κ * l) * (κ * l) = κ ^ 2 * l ^ 2 := by
      rw [pow_two, pow_two]
      calc (κ * l) * (κ * l) = κ * (l * κ) * l := by simp only [mul_assoc]
        _ = κ * (κ * l) * l := by rw [hlκ]
        _ = κ * κ * (l * l) := by simp only [mul_assoc]
    rw [← h1]
    exact hx2
  have hκ2 : κ ^ 2 = 1 := by
    have h1 : κ ^ 2 = (l ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    have h2' : κ ^ 2 ∈ kBar D.M ⊥ V hV L ⊓ L₀ :=
      ⟨(kBar D.M ⊥ V hV L).pow_mem hκ 2, by rw [h1]; exact L₀.inv_mem (L₀.pow_mem hl 2)⟩
    rw [hdisj] at h2'
    exact Subgroup.mem_bot.1 h2'
  have hκ1 : κ = 1 := by
    calc κ = κ ^ 3 * (κ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hκ3, hκ2]; simp
  rw [hκ1, one_mul]
  exact hl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
