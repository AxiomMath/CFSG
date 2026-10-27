module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_three_conj_fix_rank_le_eight_of_normalizes
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd3 : rk ↥(commSub ⊤ L ⊓ fixV L) = 3)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∈ centSub (commSub ⊤ L))
    {g : MulAut W} (hg : g ∈ A) (hgN : g ∉ normalizer (L : Set (MulAut W)))
    (hne : commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≠ ⊥)
    (hhN : g⁻¹ * τ * g ∈ normalizer (L : Set (MulAut W))) :
    rk ↥(((commSub ⊤ L).map g.toMonoidHom) ⊓ fixV (Subgroup.zpowers τ)) ≤ 8 := by
  let τ' : MulAut W := g⁻¹ * τ * g
  have hτ'def : τ' = g⁻¹ * τ * g := rfl
  have hτ'conj : τ' = MulAut.conj g⁻¹ τ := by
    rw [hτ'def, MulAut.conj_apply, inv_inv]
  have hconjτ : (MulAut.conj g).toMonoidHom τ' = τ := by
    rw [hτ'conj]
    change MulAut.conj g (MulAut.conj g⁻¹ τ) = τ
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hτeq : τ = g * τ' * g⁻¹ := by
    rw [← hconjτ]
    change MulAut.conj g τ' = g * τ' * g⁻¹
    rw [MulAut.conj_apply]
  have hτ'A : τ' ∈ A := by
    rw [hτ'def]
    exact A.mul_mem (A.mul_mem (A.inv_mem hg) hτ) hg
  have hτ'2 : τ' ^ 2 = 1 := by
    rw [hτ'conj, ← map_pow, hτ2, map_one]
  have hτ'1 : τ' ≠ 1 := by
    intro h
    apply hτ1
    rw [h] at hτeq
    simpa using hτeq
  have hτ'N : τ' ∈ normalizer (L : Set (MulAut W)) := by
    rw [hτ'def]
    exact hhN
  have hτ'C : τ' ∉ centSub (commSub ⊤ L) := by
    intro hmem
    apply hne
    rw [commSub_eq_bot_iff]
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [mem_fixV_zpowers_iff_apply]
    calc τ (g u) = (g * τ' * g⁻¹) (g u) := by rw [hτeq]
      _ = g (τ' u) := by simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      _ = g u := by rw [(mem_centSub.mp hmem) u hu]
  have hhard := s16h_l3_cover_rank_three hW hL3 hd3 hτ'2 hτ'N hτ'C
  have hYmap : (fixV (Subgroup.zpowers τ')).map g.toMonoidHom =
      fixV (Subgroup.zpowers τ) := by
    rw [← fixV_map_conj_eq (Subgroup.zpowers τ') g, MonoidHom.map_zpowers, hconjτ]
  have hmain : (commSub ⊤ L).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers τ) =
      (commSub ⊤ L ⊓ fixV (Subgroup.zpowers τ')).map g.toMonoidHom := by
    rw [← hYmap, ← Subgroup.map_inf (commSub ⊤ L) (fixV (Subgroup.zpowers τ'))
      g.toMonoidHom g.injective]
  calc rk ↥((commSub ⊤ L).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers τ))
      = rk ↥((commSub ⊤ L ⊓ fixV (Subgroup.zpowers τ')).map g.toMonoidHom) := by rw [hmain]
    _ = rk ↥(commSub ⊤ L ⊓ fixV (Subgroup.zpowers τ')) := by
          unfold rk
          rw [Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
    _ ≤ rk ↥(commSub ⊤ L ⊓ fixV L) + 5 := hhard
    _ = 3 + 5 := by rw [hd3]
    _ ≤ 8 := by norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
