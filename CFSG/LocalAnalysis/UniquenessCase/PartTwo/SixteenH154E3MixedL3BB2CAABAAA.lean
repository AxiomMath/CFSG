module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2BABABBABA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BA2ABA
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGammaInvolution
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_central_conj_comm_rank_stab
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
    (hstab : τ ∈ stabSub ((commSub ⊤ L).map g.toMonoidHom))
    (hne : commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≠ ⊥) :
    3 ≤ rk ↥(commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ)) := by
  let W' : Subgroup W := (commSub ⊤ L).map g.toMonoidHom
  have hsum : rk ↥(commSub ⊤ L ⊓ fixV L) + 9 ≤ rk ↥W' := by
    have h := s16h_e3_l3_three_sum_rank L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) hL3
    have hrk : rk ↥W' = rk ↥(commSub ⊤ L) := by
      show rk ↥((commSub ⊤ L).map g.toMonoidHom) = rk ↥(commSub ⊤ L)
      unfold rk
      rw [Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
    omega
  have hstab' : ∀ x ∈ Subgroup.zpowers τ, ∀ w ∈ W', x w ∈ W' := by
    intro x hx w hw
    have hxstab : x ∈ stabSub W' := Subgroup.zpowers_le.mpr hstab hx
    exact (mem_stabSub.mp hxstab w).mpr hw
  have hident : rk ↥(commSub W' (Subgroup.zpowers τ)) +
      rk ↥(W' ⊓ fixV (Subgroup.zpowers τ)) = rk ↥W' :=
    rk_commSub_add_rk_inf_fixV (V := W) (g := τ) (W := W') hstab'
  have hfix : rk ↥(W' ⊓ fixV (Subgroup.zpowers τ)) ≤ rk ↥(commSub ⊤ L ⊓ fixV L) + 6 := by
    by_cases hhN : g⁻¹ * τ * g ∈ normalizer (L : Set (MulAut W))
    · set τ' : MulAut W := g⁻¹ * τ * g with hτ'def
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
      have hτ'2 : τ' ^ 2 = 1 := by
        rw [hτ'conj, ← map_pow, hτ2, map_one]
      have hτ'1 : τ' ≠ 1 := by
        intro h
        apply hτ1
        rw [h] at hτeq
        simpa using hτeq
      have hτ'N : τ' ∈ normalizer (L : Set (MulAut W)) := hhN
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
      have hfix' := s16h_e3_l3_bb2bababba_fix_rank hW hL3 hτ'2 hτ'1 hτ'N hτ'C
      have hYmap : (fixV (Subgroup.zpowers τ')).map g.toMonoidHom =
          fixV (Subgroup.zpowers τ) := by
        rw [← fixV_map_conj_eq (Subgroup.zpowers τ') g, MonoidHom.map_zpowers, hconjτ]
      have hmain : W' ⊓ fixV (Subgroup.zpowers τ) =
          (commSub ⊤ L ⊓ fixV (Subgroup.zpowers τ')).map g.toMonoidHom := by
        rw [show W' = (commSub ⊤ L).map g.toMonoidHom from rfl, ← hYmap,
          ← Subgroup.map_inf (commSub ⊤ L) (fixV (Subgroup.zpowers τ'))
            g.toMonoidHom g.injective]
      calc rk ↥(W' ⊓ fixV (Subgroup.zpowers τ))
          = rk ↥((commSub ⊤ L ⊓ fixV (Subgroup.zpowers τ')).map g.toMonoidHom) := by
            rw [hmain]
        _ = rk ↥(commSub ⊤ L ⊓ fixV (Subgroup.zpowers τ')) := by
              unfold rk
              rw [Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
        _ ≤ rk ↥(commSub ⊤ L ⊓ fixV L) + 6 := hfix'
    · set h : MulAut W := g⁻¹ * τ * g with hhdef
      have hhA : h ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hg) hτ) hg
      have hhconc := hconc.2.1 h hhA hhN
      have hswap : commSub (⊤ : Subgroup W) (L.map (MulAut.conj h).toMonoidHom) ≤ fixV L :=
        commSub_le_fixV_of_commutator_eq_bot hhconc.1 (commSub_eq_bot_iff.mp hhconc.2)
      have hmap : commSub (⊤ : Subgroup W) (L.map (MulAut.conj h).toMonoidHom) =
          (commSub (⊤ : Subgroup W) L).map h.toMonoidHom := Asc81c.commSub_map_conj L h
      have hWhle : (commSub (⊤ : Subgroup W) L).map h.toMonoidHom ≤ fixV L := by
        rw [← hmap]; exact hswap
      have hsub : W' ⊓ fixV (Subgroup.zpowers τ) ≤ W' ⊓ W'.map τ.toMonoidHom := by
        refine le_inf inf_le_left ?_
        rintro x ⟨hxU, hxfix⟩
        exact Subgroup.mem_map.mpr ⟨x, hxU, by
          simpa using mem_fixV_zpowers_iff_apply.mp hxfix⟩
      have hcomp' : τ.toMonoidHom.comp g.toMonoidHom = g.toMonoidHom.comp h.toMonoidHom := by
        ext x
        show τ (g x) = g (h x)
        rw [show h = g⁻¹ * τ * g from hhdef]
        simp [MulAut.mul_apply]
      have hmap2 : W'.map τ.toMonoidHom =
          ((commSub (⊤ : Subgroup W) L).map h.toMonoidHom).map g.toMonoidHom := by
        rw [show W' = (commSub ⊤ L).map g.toMonoidHom from rfl, Subgroup.map_map, hcomp',
          Subgroup.map_map]
      have hinf : W' ⊓ W'.map τ.toMonoidHom =
          (commSub (⊤ : Subgroup W) L ⊓
            (commSub (⊤ : Subgroup W) L).map h.toMonoidHom).map g.toMonoidHom := by
        rw [hmap2, show W' = (commSub ⊤ L).map g.toMonoidHom from rfl,
          ← Subgroup.map_inf _ _ g.toMonoidHom g.injective]
      have hrkeq : rk ↥((commSub (⊤ : Subgroup W) L ⊓
          (commSub (⊤ : Subgroup W) L).map h.toMonoidHom).map g.toMonoidHom) =
          rk ↥(commSub (⊤ : Subgroup W) L ⊓
            (commSub (⊤ : Subgroup W) L).map h.toMonoidHom) := by
        unfold rk
        rw [Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
      have hWhZ : commSub (⊤ : Subgroup W) L ⊓
          (commSub (⊤ : Subgroup W) L).map h.toMonoidHom ≤ commSub ⊤ L ⊓ fixV L :=
        le_inf inf_le_left (inf_le_right.trans hWhle)
      calc rk ↥(W' ⊓ fixV (Subgroup.zpowers τ))
          ≤ rk ↥(W' ⊓ W'.map τ.toMonoidHom) := rk_mono hsub
        _ = rk ↥((commSub (⊤ : Subgroup W) L ⊓
              (commSub (⊤ : Subgroup W) L).map h.toMonoidHom).map g.toMonoidHom) := by
              rw [hinf]
        _ = rk ↥(commSub (⊤ : Subgroup W) L ⊓
              (commSub (⊤ : Subgroup W) L).map h.toMonoidHom) := hrkeq
        _ ≤ rk ↥(commSub ⊤ L ⊓ fixV L) := rk_mono hWhZ
        _ ≤ rk ↥(commSub ⊤ L ⊓ fixV L) + 6 := by omega
  change 3 ≤ rk ↥(commSub W' (Subgroup.zpowers τ))
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
