module

public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGammaInvolution
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB1AA2BAAAA
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_two_conj_fix_rank_le_four
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) = 2)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∈ centSub (commSub ⊤ L))
    {g : MulAut W} (hg : g ∈ A) (hgN : g ∉ normalizer (L : Set (MulAut W)))
    (hne : commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≠ ⊥) :
    rk ↥(((commSub ⊤ L).map g.toMonoidHom) ⊓ fixV (Subgroup.zpowers τ)) ≤ 4 := by
  by_cases hhN : g⁻¹ * τ * g ∈ normalizer (L : Set (MulAut W))
  · exact s16h_e3_l3_two_conj_fix_rank_le_four_of_normalizes hW ht ht2 ht1 htr hconc
      hcomp hthin hZ hL3 hd2 hτ hτ2 hτ1 hτN hτC hg hgN hne hhN
  · set h : MulAut W := g⁻¹ * τ * g with hhdef
    have hhA : h ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hg) hτ) hg
    have hhconc := hconc.2.1 h hhA hhN
    have hswap : commSub (⊤ : Subgroup W) (L.map (MulAut.conj h).toMonoidHom) ≤ fixV L :=
      commSub_le_fixV_of_commutator_eq_bot hhconc.1 (commSub_eq_bot_iff.mp hhconc.2)
    have hmap : commSub (⊤ : Subgroup W) (L.map (MulAut.conj h).toMonoidHom) =
        (commSub (⊤ : Subgroup W) L).map h.toMonoidHom := Asc81c.commSub_map_conj L h
    have hWhle : (commSub (⊤ : Subgroup W) L).map h.toMonoidHom ≤ fixV L := by
      rw [← hmap]; exact hswap
    set U : Subgroup W := (commSub ⊤ L).map g.toMonoidHom with hUdef
    have hsub : U ⊓ fixV (Subgroup.zpowers τ) ≤ U ⊓ U.map τ.toMonoidHom := by
      refine le_inf inf_le_left ?_
      rintro x ⟨hxU, hxfix⟩
      exact Subgroup.mem_map.mpr ⟨x, hxU, by
        simpa using mem_fixV_zpowers_iff_apply.mp hxfix⟩
    have hcomp' : τ.toMonoidHom.comp g.toMonoidHom = g.toMonoidHom.comp h.toMonoidHom := by
      ext x
      show τ (g x) = g (h x)
      rw [show h = g⁻¹ * τ * g from hhdef]
      simp [MulAut.mul_apply]
    have hmap2 : U.map τ.toMonoidHom =
        ((commSub (⊤ : Subgroup W) L).map h.toMonoidHom).map g.toMonoidHom := by
      rw [hUdef, Subgroup.map_map, hcomp', Subgroup.map_map]
    have hinf : U ⊓ U.map τ.toMonoidHom =
        (commSub (⊤ : Subgroup W) L ⊓
          (commSub (⊤ : Subgroup W) L).map h.toMonoidHom).map g.toMonoidHom := by
      rw [hmap2, hUdef, ← Subgroup.map_inf _ _ g.toMonoidHom g.injective]
    have hrkeq : rk ↥((commSub (⊤ : Subgroup W) L ⊓
        (commSub (⊤ : Subgroup W) L).map h.toMonoidHom).map g.toMonoidHom) =
        rk ↥(commSub (⊤ : Subgroup W) L ⊓
          (commSub (⊤ : Subgroup W) L).map h.toMonoidHom) := by
      unfold rk
      rw [Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
    have hWhZ : commSub (⊤ : Subgroup W) L ⊓
        (commSub (⊤ : Subgroup W) L).map h.toMonoidHom ≤ commSub ⊤ L ⊓ fixV L :=
      le_inf inf_le_left (inf_le_right.trans hWhle)
    have hrkZ : rk ↥(commSub (⊤ : Subgroup W) L ⊓
        (commSub (⊤ : Subgroup W) L).map h.toMonoidHom) ≤ 2 := by
      have h := rk_mono hWhZ
      rw [hd2] at h
      exact h
    calc rk ↥(U ⊓ fixV (Subgroup.zpowers τ))
        ≤ rk ↥(U ⊓ U.map τ.toMonoidHom) := rk_mono hsub
      _ = rk ↥((commSub (⊤ : Subgroup W) L ⊓
            (commSub (⊤ : Subgroup W) L).map h.toMonoidHom).map g.toMonoidHom) := by rw [hinf]
      _ = rk ↥(commSub (⊤ : Subgroup W) L ⊓
            (commSub (⊤ : Subgroup W) L).map h.toMonoidHom) := hrkeq
      _ ≤ 2 := hrkZ
      _ ≤ 4 := by norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
