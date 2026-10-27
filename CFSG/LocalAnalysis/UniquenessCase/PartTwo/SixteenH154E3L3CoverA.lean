module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfDim
public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_rk_fixV_autSec_commSub_zpowers {V : Type} [CommGroup V] [Finite V]
    {τ : MulAut V} {W U : Subgroup V}
    (hτW : Subgroup.zpowers τ ≤ stabSub W) (hτU : Subgroup.zpowers τ ≤ stabSub U) :
    rk ↥(fixV (autSec (Subgroup.zpowers τ) W U)) +
      rk ↥(commSub (⊤ : Subgroup (Sec W U)) (autSec (Subgroup.zpowers τ) W U)) =
      rk ↥(⊤ : Subgroup (Sec W U)) := by
  let X : Subgroup (MulAut V) := Subgroup.zpowers τ
  let τ' : ↥X := ⟨τ, Subgroup.mem_zpowers τ⟩
  let g : MulAut (Sec W U) := CFSG.Quasithin.B5.secHom X hτW hτU τ'
  have htop : (⊤ : Subgroup ↥X) = Subgroup.zpowers τ' := by
    refine le_antisymm ?_ le_top
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
  have hA : autSec X W U = Subgroup.zpowers g := by
    rw [← CFSG.Quasithin.B5.range_secHom X hτW hτU, MonoidHom.range_eq_map, htop,
      MonoidHom.map_zpowers]
  have h := rk_commV_add_rk_fixV g
  rw [commV_eq_commSub] at h
  rw [← hA] at h
  dsimp only [X] at h
  rw [rk_top]
  simpa [add_comm] using h

theorem s16h_e3_l3_rk_sumOfNat_le
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

theorem s16h_e3_l3_sum_rank (L : Subgroup (MulAut W)) (U Z : Subgroup W) (k : ℕ)
    (h : s16h_H5L3Sum L U Z k) : rk ↥U = rk ↥Z + 3 * k := by
  obtain ⟨-, hsum⟩ := h
  have hm : ∀ I : Subgroup W, BinaryNaturalSL L I Z 3 1 → rk ↥I = rk ↥Z + 3 := by
    intro I hI
    obtain ⟨K, hField, hFin, hK, hreal⟩ := hI
    have := s16fh_rk_of_realizes_nat (d := 3) (a := 1) hK hreal
    simpa using this
  have hle := s16h_e3_l3_rk_sumOfNat_le (m := 3) hsum hm
  have hge := s16fh_rk_sumOfNat_ge (N := fun H I Z => BinaryNaturalSL H I Z 3 1) hsum hm
  omega

theorem s16h_e3_l3_sum_rank_four (L : Subgroup (MulAut W)) (U Z : Subgroup W) (k : ℕ)
    (h : s16h_H5L3Sum L U Z k) (hd : rk ↥Z = k) : rk ↥U = 4 * k := by
  have h1 := s16h_e3_l3_sum_rank L U Z k h
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
