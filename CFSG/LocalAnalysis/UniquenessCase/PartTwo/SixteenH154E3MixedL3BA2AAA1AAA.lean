module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BA2AAA1AAAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_rk_sumOfNat_le
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {k m : ℕ} (h : SumOfNat N L U Z k)
    (hm : ∀ I : Subgroup W, N L I Z → rk ↥I = rk ↥Z + m) :
    rk ↥U ≤ rk ↥Z + k * m := by
  obtain ⟨I, hZI, hind, hsup, hnat⟩ := h
  have hfin : ∀ s : Finset (Fin k), rk ↥(Z ⊔ ⨆ i ∈ s, I i) = rk ↥Z + s.card * m := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hbot : (⨆ i ∈ (∅ : Finset (Fin k)), I i) = ⊥ := by
          refine iSup_eq_bot.2 fun i => iSup_eq_bot.2 fun hi => ?_
          exact absurd hi (Finset.notMem_empty i)
        rw [hbot, sup_bot_eq]
        simp
    | insert a s has ih =>
        have hTX : (⨆ i ∈ s, I i) ≤ ⨆ (j : Fin k) (_ : j ≠ a), I j := by
          refine iSup_le fun i => iSup_le fun his => ?_
          exact le_iSup₂ (f := fun j (_ : j ≠ a) => I j) i (fun hia => has (hia ▸ his))
        have hle : Z ⊔ ⨆ i ∈ s, I i ≤ Z ⊔ ⨆ (j : Fin k) (_ : j ≠ a), I j :=
          sup_le le_sup_left (hTX.trans le_sup_right)
        have hinf : (Z ⊔ ⨆ i ∈ s, I i) ⊓ I a = Z := by
          refine le_antisymm ?_ (le_inf le_sup_left (hZI a))
          calc (Z ⊔ ⨆ i ∈ s, I i) ⊓ I a
              ≤ I a ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ a), I j) :=
                le_inf inf_le_right (inf_le_left.trans hle)
            _ ≤ Z := hind a
        have h2 := rk_sup_add_rk_inf (Z ⊔ ⨆ i ∈ s, I i) (I a)
        rw [hinf] at h2
        have h3 : rk ↥(I a) = rk ↥Z + m := hm (I a) (hnat a)
        rw [ih, h3] at h2
        have h4 : (s.card + 1) * m = s.card * m + m := by ring
        have hsup_ins : Z ⊔ ⨆ i ∈ insert a s, I i = (Z ⊔ ⨆ i ∈ s, I i) ⊔ I a := by
          rw [Finset.iSup_insert, sup_comm (I a) (⨆ i ∈ s, I i), ← sup_assoc]
        rw [hsup_ins, Finset.card_insert_of_notMem has, h4]
        omega
  have huniv : (⨆ i ∈ (Finset.univ : Finset (Fin k)), I i) = ⨆ i, I i := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun i => iSup_le fun _ => le_iSup (fun i => I i) i
    · exact iSup_le fun i =>
        le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => I i) i
          (Finset.mem_univ i)
  have h5 := hfin Finset.univ
  rw [Finset.card_univ, Fintype.card_fin, huniv, hsup] at h5
  exact le_of_eq h5

theorem s16h_e3_l3_three_sum_rank_le
    (L : Subgroup (MulAut W)) (U Z : Subgroup W) (h : s16h_H5L3Sum L U Z 3) :
    rk ↥U ≤ rk ↥Z + 9 := by
  obtain ⟨-, hsum⟩ := h
  have hm : ∀ I : Subgroup W, BinaryNaturalSL L I Z 3 1 → rk ↥I = rk ↥Z + 3 := by
    intro I hI
    obtain ⟨K, hField, hFin, hK, hreal⟩ := hI
    have := s16fh_rk_of_realizes_nat hK hreal
    simpa using this
  have := s16h_rk_sumOfNat_le (m := 3) hsum hm
  simpa using this

theorem s16h_e3_l3_three_commSub_rank_ge_four
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
    (hτC : τ ∉ centSub (commSub ⊤ L)) :
    4 ≤ rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers τ)) :=
  s16h_e3_l3_three_commSub_rank_ge_four_aux hW ht ht2 ht1 htr hconc hcomp hthin hZ hL3 hd3
    hτ hτ2 hτ1 hτN hτC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
