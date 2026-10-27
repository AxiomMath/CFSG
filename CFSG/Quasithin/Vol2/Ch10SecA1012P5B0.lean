module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Quasithin.Vol2.Ch10SecAShape

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isSylowTwoOf_T0_inf_B0 (hyp : Ch10.Hyp10 G T L I) :
    IsSylowTwoOf (T0 T L ⊓ B0 T L) (B0 T L) := by
  have hloc := hyp.fsu.maximal.1
  have hL0syl : IsSylowTwoOf (T0 T L) (fsuL0 T L) :=
    B6.isSylowTwoOf_inf_normal ⟨le_sup_right, hloc.1, hloc.2.2.1⟩ (fsuL0_le_sup T L)
      (sup_le ((le_fsuL0 T L).trans Subgroup.le_normalizer) (le_fsuM T L))
  have hle : T0 T L ≤ fsuL0 T L ⊓ Subgroup.normalizer (T0 T L : Set G) :=
    le_inf inf_le_right Subgroup.le_normalizer
  have hX : IsSylowTwoOf (T0 T L) (fsuL0 T L ⊓ Subgroup.normalizer (T0 T L : Set G)) := by
    refine ⟨hle, hL0syl.2.1, fun hd => hL0syl.2.2 ?_⟩
    have h := Subgroup.relIndex_mul_relIndex (T0 T L) _ (fsuL0 T L) hle inf_le_left
    exact hd.trans (Dvd.intro _ h)
  exact B6.isSylowTwoOf_inf_normal hX (oTwoUpper_le _) (le_normalizer_oTwoUpper _)

theorem sup_eq_B0 (hyp : Ch10.Hyp10 G T L I) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (B0 T L)) : D ⊔ (T0 T L ⊓ B0 T L) = B0 T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDB, hDodd, k, hk⟩ := hD
  obtain ⟨hSB, hS2, hSidx⟩ := isSylowTwoOf_T0_inf_B0 hyp
  set S := T0 T L ⊓ B0 T L with hSdef
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hS2
  have h1 : Nat.card (B0 T L) = 2 ^ k * Nat.card D := by
    have h := Subgroup.relIndex_mul_card D (B0 T L)
    rw [inf_eq_left.mpr hDB, hk] at h
    exact h.symm
  have h2 : Nat.card (B0 T L) = 2 ^ j * S.relIndex (B0 T L) := by
    have h := Subgroup.relIndex_mul_card S (B0 T L)
    rw [inf_eq_left.mpr hSB, hj] at h
    rw [← h, mul_comm]
  have hodd : Odd (S.relIndex (B0 T L)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSidx)
  obtain ⟨hjk, -⟩ := two_pow_mul_odd_inj hodd hDodd (h2.symm.trans h1)
  have hdvd : Nat.card D * Nat.card S ∣ Nat.card ↥(D ⊔ S) := by
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (Subgroup.card_dvd_of_le le_sup_left)
      (Subgroup.card_dvd_of_le le_sup_right)
    rw [hj]
    exact (Nat.coprime_two_right.mpr hDodd).pow_right j
  refine Subgroup.eq_of_le_of_card_ge (sup_le hDB hSB) ?_
  rw [h1, ← hjk, ← hj, mul_comm]
  exact Nat.le_of_dvd Nat.card_pos hdvd

omit [Finite G] in
theorem commutator_sup_le_of_le_centralizer {W D S : Subgroup G}
    (hDW : D ≤ Subgroup.normalizer (W : Set G)) (hSW : S ≤ Subgroup.centralizer (W : Set G)) :
    ⁅W, D ⊔ S⁆ ≤ ⁅W, D⁆ := by
  set K := ⁅W, D⁆ with hKdef
  have hKW : K ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hDW
  let H' : Subgroup G :=
    { carrier := {b | b ∈ Subgroup.normalizer (K : Set G) ∧ ∀ w ∈ W, ⁅w, b⁆ ∈ K}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun w hw => ?_⟩
        have he : ⁅w, a * b⁆ = ⁅w, a⁆ * (a * ⁅w, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [he]
        exact K.mul_mem (ha' w hw) ((Subgroup.mem_normalizer_iff.mp ha _).mp (hb' w hw))
      one_mem' := ⟨Subgroup.one_mem _, fun w _ => by
        rw [commutatorElement_def, mul_one, mul_inv_cancel, one_mul, inv_one]
        exact K.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun w hw => ?_⟩
        have he : ⁅w, a⁻¹⁆ = a⁻¹ * ⁅w, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [he]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) _).mp
          (K.inv_mem (ha' w hw)) }
  have hD : D ≤ H' := fun d hd =>
    ⟨le_normalizer_commutator hDW Subgroup.le_normalizer hd,
      fun w hw => Subgroup.commutator_mem_commutator hw hd⟩
  have hS : S ≤ H' := by
    intro s hs
    have hc := Subgroup.mem_centralizer_iff.mp (hSW hs)
    refine ⟨Subgroup.mem_normalizer_iff.mpr fun k => ?_, fun w hw => ?_⟩
    · constructor
      · intro hk
        have h1 : s * k * s⁻¹ = k := by rw [← hc k (hKW hk), mul_inv_cancel_right]
        rw [h1]
        exact hk
      · intro hk
        have h3 : s * k * s⁻¹ = k := by
          have h1 := hc _ (hKW hk)
          have h2 : s * k = s * (s * k * s⁻¹) := by rw [← h1]; group
          exact (mul_left_cancel h2).symm
        rw [← h3]
        exact hk
    · have h1 : ⁅w, s⁆ = 1 := by
        rw [commutatorElement_def, hc w hw, mul_inv_cancel_right, mul_inv_cancel]
      rw [h1]
      exact K.one_mem
  rw [Subgroup.commutator_le]
  intro w hw b hb
  exact ((sup_le hD hS) hb).2 w hw

theorem commutator_B0_le (hyp : Ch10.Hyp10 G T L I) {D W : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (B0 T L)) (hW : T0 T L ≤ Subgroup.centralizer (W : Set G))
    (hDW : D ≤ Subgroup.normalizer (W : Set G)) : ⁅W, B0 T L⁆ ≤ ⁅W, D⁆ := by
  rw [← sup_eq_B0 hyp hD]
  exact commutator_sup_le_of_le_centralizer hDW (inf_le_left.trans hW)

end CFSG.Quasithin.Vol2.Ch10.SecA
