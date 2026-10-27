module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Set
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_exists_stable_irr (h : ThreeNat A L T)
    (hodd : Odd (Nat.card ↥(irrSet L))) : ∃ I ∈ irrSet L, StableUnder T I := by
  have hTA : T ≤ A := h.sylow.le
  have hTN : T ≤ Subgroup.normalizer (L : Set (MulAut W)) := hTA.trans h.normal
  have hsmul : ∀ t : ↥T, ∀ I : ↥(irrSet L),
      ((t : MulAut W) • (I : Subgroup W)) ∈ irrSet L := by
    intro t I
    have ht := hTN t.2
    exact CFSG.LocalAnalysis.WeakClosure81.map_mem_irrSet
      (fun x hx => conj_mem_of_mem_normalizer ht hx)
      (fun x hx => inv_conj_mem_of_mem_normalizer ht hx) I.2
  letI : MulAction ↥T ↥(irrSet L) :=
    { smul := fun t I => ⟨(t : MulAut W) • (I : Subgroup W), hsmul t I⟩
      one_smul := fun I => by
        apply Subtype.ext
        show (((1 : ↥T) : MulAut W)) • (I : Subgroup W) = (I : Subgroup W)
        simp
      mul_smul := fun t₁ t₂ I => by
        apply Subtype.ext
        show (((t₁ * t₂ : ↥T) : MulAut W)) • (I : Subgroup W) =
          (t₁ : MulAut W) • ((t₂ : MulAut W) • (I : Subgroup W))
        rw [Subgroup.coe_mul, mul_smul] }
  have hT2 : IsPGroup 2 ↥T := h.sylow.isPGroup
  have h2 : ¬ 2 ∣ Nat.card ↥(irrSet L) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hodd' : Nat.card ↥(irrSet L) % 2 = 1 := Nat.odd_iff.1 hodd
    omega
  obtain ⟨I, hIfix⟩ := hT2.nonempty_fixed_point_of_prime_not_dvd_card (↥(irrSet L)) h2
  refine ⟨(I : Subgroup W), I.2, ?_⟩
  intro t ht u hu
  have hfix : (⟨t, ht⟩ : ↥T) • I = I := (MulAction.mem_fixedPoints).1 hIfix ⟨t, ht⟩
  have hval : (t : MulAut W) • (I : Subgroup W) = (I : Subgroup W) :=
    congrArg Subtype.val hfix
  have hmem : t u ∈ (t : MulAut W) • (I : Subgroup W) :=
    Subgroup.smul_mem_pointwise_smul u t (I : Subgroup W) hu
  rwa [hval] at hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
