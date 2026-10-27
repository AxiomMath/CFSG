module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB2B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BA2ABA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Sev
public import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_central_conj_comm_rank_move
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∈ centSub (commSub ⊤ L))
    {g : MulAut W} (hg : g ∈ A)
    (hgN : g ∉ normalizer (L : Set (MulAut W)))
    (hmov : τ ∉ stabSub ((commSub ⊤ L).map g.toMonoidHom))
    (hne : commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≠ ⊥) :
    3 ≤ rk ↥(commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ)) := by
  have hττ : τ * τ = 1 := by simpa [pow_two] using hτ2
  let a : MulAut W := g⁻¹ * τ * g
  have haA : a ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hg) hτ) hg
  have ha2 : a ^ 2 = 1 := by
    rw [pow_two]
    calc a * a = g⁻¹ * (τ * τ) * g := by simp only [a]; group
      _ = 1 := by rw [hττ]; group
  have hconj : ∀ x : W, g⁻¹ (τ x) = a (g⁻¹ x) := by
    intro x
    simp only [a, MulAut.mul_apply]
    simp
  have haN : a ∉ normalizer (L : Set (MulAut W)) := by
    intro haN
    apply hmov
    have ha_stab : a ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
      StabLat.mem_stabSub_commSub (X := L) (Y := ⊤)
        (mem_stabSub.mpr (fun _ => by simp)) haN
    refine mem_stabSub.mpr fun u => ?_
    have hgτ : g⁻¹ (τ u) = a (g⁻¹ u) := hconj u
    constructor
    · intro hu
      obtain ⟨v, hv, hvτ⟩ := Subgroup.mem_map.mp hu
      have hgv : g v = τ u := hvτ
      have hv' : v = a (g⁻¹ u) := by
        apply g.injective
        rw [hgv, ← hgτ]
        simp
      exact Subgroup.mem_map.mpr ⟨g⁻¹ u,
        (mem_stabSub.mp ha_stab (g⁻¹ u)).mp (hv' ▸ hv), by simp⟩
    · intro hu
      obtain ⟨v, hv, hgu⟩ := Subgroup.mem_map.mp hu
      have hgv : g v = u := hgu
      have hv' : v = g⁻¹ u := by
        apply g.injective
        rw [hgv]
        simp
      refine Subgroup.mem_map.mpr ⟨a (g⁻¹ u),
        (mem_stabSub.mp ha_stab (g⁻¹ u)).mpr (hv' ▸ hv), ?_⟩
      rw [← hgτ]
      simp [hgu]
  have hInt : commSub (⊤ : Subgroup W) L ⊓ (commSub (⊤ : Subgroup W) L).map a.toMonoidHom
      ≤ commSub (⊤ : Subgroup W) L ⊓ fixV L :=
    le_inf inf_le_left (s16h_e3_two_inf_map_le_fixV A L t a hconc haA ha2 haN)
  have hfixZ : commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers a)
      ≤ commSub (⊤ : Subgroup W) L ⊓ fixV L := by
    refine le_trans ?_ hInt
    refine le_inf inf_le_left ?_
    intro u hu
    rw [Subgroup.mem_inf] at hu
    have hua : a u = u := by
      simpa using (mem_fixV.mp hu.2) a (Subgroup.mem_zpowers a)
    exact Subgroup.mem_map.mpr ⟨u, hu.1, hua⟩
  let W' : Subgroup W := (commSub (⊤ : Subgroup W) L).map g.toMonoidHom
  have hbound : rk ↥(W' ⊓ fixV (Subgroup.zpowers τ))
      ≤ rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV L) := by
    have hmaple : (W' ⊓ fixV (Subgroup.zpowers τ)).map (g⁻¹).toMonoidHom
        ≤ commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers a) := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      rw [Subgroup.mem_inf] at hv ⊢
      constructor
      · obtain ⟨w, hw, hgw⟩ := Subgroup.mem_map.mp hv.1
        rw [← hgw]
        simpa using hw
      · rw [mem_fixV_zpowers_iff]
        have hτfix : τ v = v := (mem_fixV.mp hv.2) τ (Subgroup.mem_zpowers τ)
        calc a (g⁻¹ v) = g⁻¹ (τ v) := (hconj v).symm
          _ = g⁻¹ v := by rw [hτfix]
    calc rk ↥(W' ⊓ fixV (Subgroup.zpowers τ))
        = rk ↥((W' ⊓ fixV (Subgroup.zpowers τ)).map (g⁻¹).toMonoidHom) := by
          unfold rk
          rw [Subgroup.card_map_of_injective (f := (g⁻¹).toMonoidHom) (g⁻¹).injective]
      _ ≤ rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers a)) := rk_mono hmaple
      _ ≤ rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV L) := rk_mono hfixZ
  have hnull := CFSG.LocalAnalysis.WeakClosure81.rk_eq_rk_commSub_add_rk_inf_fixV
    (W := W) hW (I := W') hττ
  have hsum := s16h_e3_l3_three_sum_rank L (commSub (⊤ : Subgroup W) L)
      (commSub (⊤ : Subgroup W) L ⊓ fixV L) hL3
  have hrkW' : rk ↥W' = rk ↥(commSub (⊤ : Subgroup W) L) := by
    unfold rk
    rw [Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
  change 3 ≤ rk ↥(commSub W' (Subgroup.zpowers τ))
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
