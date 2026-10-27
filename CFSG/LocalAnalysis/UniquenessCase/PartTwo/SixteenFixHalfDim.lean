module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

theorem s16fh_rk_of_realizes_nat [Finite W] {K : Type} [Field K] [Finite K] {d a : ℕ}
    (hK : Nat.card K = 2 ^ a) {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (h : (FFModel.nat (StatedSL d K)).Realizes L I Z) : rk ↥I = rk ↥Z + d * a := by
  obtain ⟨π, hπ⟩ := h
  have h1 : Nat.card ↥I = Nat.card (FFModel.nat (StatedSL d K)).Mod * Nat.card ↥Z :=
    CFSG.Quasithin.G64.RealizesVia.card_eq hπ
  have h2 : Nat.card (FFModel.nat (StatedSL d K)).Mod = Nat.card K ^ d :=
    CFSG.Quasithin.G64.card_natMod (StatedSL d K)
  have hcard : Nat.card ↥I = 2 ^ (d * a) * Nat.card ↥Z := by
    rw [h1, h2, hK, ← pow_mul, Nat.mul_comm a d]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : (2 : ℕ) ^ (d * a) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hZ : Nat.card ↥Z ≠ 0 := Nat.card_pos.ne'
  calc rk ↥I = padicValNat 2 (Nat.card ↥I) := rfl
    _ = padicValNat 2 (2 ^ (d * a) * Nat.card ↥Z) := by rw [hcard]
    _ = d * a + padicValNat 2 (Nat.card ↥Z) := by
        rw [padicValNat.mul hpow hZ, padicValNat.prime_pow]
    _ = rk ↥Z + d * a := by unfold rk; omega

theorem s16fh_rk_sumOfNat_ge [Finite W]
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {k m : ℕ} (h : SumOfNat N L U Z k)
    (hm : ∀ I : Subgroup W, N L I Z → rk ↥I = rk ↥Z + m) :
    rk ↥Z + k * m ≤ rk ↥U := by
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
  exact le_of_eq h5.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
