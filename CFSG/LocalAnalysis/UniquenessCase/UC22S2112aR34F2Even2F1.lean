module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S13d
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Odd
import CFSG.RankThree.Classical.SteinbergBJOddSymplecticOuterOrder
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith
import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaOdd
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaEven
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTriality
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_inner_of_odd_f1 {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : LieModel X t n p 1)
    (ht : ((t = .PSL ∨ t = .PSU) ∧ 3 ≤ n) ∨ (t = .PSp ∧ 2 ≤ n))
    (hd : ∀ s : ℕ, s.Prime → s ≠ 2 → ¬ s ∣ (genericOrders t n p 1).1)
    {α : MulAut X} (hα : Odd (orderOf α)) : α ∈ (MulAut.conj : X →* MulAut X).range := by
  have hn0 : n ≠ 0 := by
    rcases ht with ⟨-, hn⟩ | ⟨-, hn⟩ <;> omega
  have hclass : StatedClassicalModel X t n p 1 := hX.statedClassicalModel_of_ne_zero hn0
  have hbound : Nat.card (Outer X) ∣ 2 * (genericOrders t n p 1).1 := by
    rcases ht with ⟨htPS, hn⟩ | ⟨rfl, hn⟩
    · rcases htPS with rfl | rfl
      · obtain ⟨hb, -⟩ :=
          CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
            (T := X) (τ := .PSL) (Or.inl rfl) hn hp (le_rfl : 1 ≤ 1) hclass
        simpa [CFSG.RankThree.OuterOrder.determinantParameter, genericOrders] using hb
      · obtain ⟨hb, -⟩ :=
          CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
            (T := X) (τ := .PSU) (Or.inr rfl) hn hp (le_rfl : 1 ≤ 1) hclass
        simpa [CFSG.RankThree.OuterOrder.determinantParameter, genericOrders] using hb
    · obtain ⟨-, K, hfield, hfin, hK, ⟨e⟩⟩ := hclass
      have hb :=
        (CFSG.RankThree.Classical.odd_symplectic_outer_order_divides_field_multiplier_bound
          (ℓ := p) (f := 1) (r := n) hp hp2 (le_rfl : 1 ≤ 1) hn (K := K) hK).1
      rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e.symm] at hb
      have hgd : 1 * Nat.gcd 2 (p ^ 1 - 1) = (genericOrders .PSp n p 1).1 := by
        simp [genericOrders]
      rw [hgd] at hb
      exact hb.trans (dvd_mul_left (genericOrders .PSp n p 1).1 2)
  have hpos : 0 < 2 * (genericOrders t n p 1).1 :=
    Nat.mul_pos (by norm_num)
      (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_fst_pos hX.admissible)
  have hP : IsPGroup 2 (Outer X) := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
      (Nat.pos_of_dvd_of_pos hbound hpos).ne' ?_)
    refine fun {s} hs hsdiv => ?_
    by_contra hs2
    rcases hs.dvd_mul.1 (hsdiv.trans hbound) with h2 | hd'
    · exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).1 h2)
    · exact hd s hs hs2 hd'
  exact uc22s13d_out_mem_of_isPGroup hP hα (pow_orderOf_eq_one α)

section Exc


private theorem uc22s2112r34_inner_f1_exc_prime {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {n p : ℕ} (hadm : StatedLieAdmissible t n p 1) (hX : LieModel X t n p 1)
    (ht : t = .POmegaOdd ∨ t = .POmegaMinus ∨ t = .G2 ∨ t = .trialityD4)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : t = .trialityD4 → r ≠ 3)
    {β : MulAut X} (hβ : β ^ r = 1)
    (hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X) : False := by
  have htne : t ≠ .Tits := by
    rcases ht with rfl | rfl | rfl | rfl <;> decide
  have hrd : ¬ r ∣ CFSG.ComponentClassification.CatLeaf.lieOrderDivisor t n (p ^ 1) := by
    rcases ht with rfl | rfl | rfl | rfl
    · intro h
      have h2 : r ∣ 2 := by
        simpa [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor] using h
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
    · intro h
      have hg : r ∣ Nat.gcd 4 ((p ^ 1) ^ n + 1) := by
        simpa [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor] using h
      have h4 : r ∣ 4 := hg.trans (Nat.gcd_dvd_left 4 ((p ^ 1) ^ n + 1))
      have h2 : r ∣ 2 := hr.dvd_of_dvd_pow (by
        show r ∣ 2 ^ 2
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
        exact h4)
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
    · intro h
      exact hr.not_dvd_one (by
        simpa [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor] using h)
    · intro h
      exact hr.not_dvd_one (by
        simpa [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor] using h)
  have hd4 : ¬ (t = .POmegaPlus ∧ n = 4 ∧ r = 3) := by
    rintro ⟨h, -⟩
    rcases ht with rfl | rfl | rfl | rfl <;> exact absurd h (by decide)
  rcases ht with rfl | rfl | rfl | rfl
  · rcases CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_POmegaOdd
      X n p 1 hadm hX htne r hr hr2 hrd hd4 β hβ hβout with
      ⟨f0, hf0, -⟩ | ⟨h, -⟩
    · exact hr.not_dvd_one ⟨f0, hf0⟩
    · exact absurd h (by decide)
  · rcases CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_POmegaMinus
      X n p 1 hadm hX htne r hr hr2 hrd hd4 β hβ hβout with
      ⟨f0, hf0, -⟩ | ⟨h, -⟩
    · exact hr.not_dvd_one ⟨f0, hf0⟩
    · exact absurd h (by decide)
  · rcases CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_G2
      X n p 1 hadm hX htne r hr hr2 hrd hd4 β hβ hβout with
      ⟨f0, hf0, -⟩ | ⟨h, -⟩
    · exact hr.not_dvd_one ⟨f0, hf0⟩
    · exact absurd h (by decide)
  · obtain ⟨f0, hf0, -⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrder_trialityD4_of_ne_three
        X n p 1 hadm hX htne r hr hr2 hrd hd4 (hr3 rfl) β hβ hβout
    exact hr.not_dvd_one ⟨f0, hf0⟩

theorem uc22s2112r34_inner_of_squarefree_f1_exc {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {n p : ℕ} (hadm : StatedLieAdmissible t n p 1) (hX : LieModel X t n p 1)
    (ht : t = .POmegaOdd ∨ t = .POmegaMinus ∨ t = .G2 ∨ t = .trialityD4)
    {α : MulAut X} (hα : Odd (orderOf α)) (hsq : Squarefree (orderOf α))
    (h3 : t = .trialityD4 → ¬ 3 ∣ orderOf α) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  by_contra hαout
  let π : MulAut X →* MulAut X ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
    QuotientGroup.mk' _
  have hπα : π α ≠ 1 := by
    intro h
    exact hαout ((QuotientGroup.eq_one_iff
      (N := CFSG.ComponentClassification.OuterAutomorphisms.inner X) α).mp h)
  have hdvd : orderOf (π α) ∣ orderOf α := orderOf_map_dvd π α
  have hne : orderOf (π α) ≠ 1 := by
    rintro h
    exact hπα (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
  have hrdvdα : r ∣ orderOf α := hrdvd.trans hdvd
  have hrodd : Odd r := Odd.of_dvd_nat hα hrdvdα
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hrodd
    omega
  have hr3 : t = .trialityD4 → r ≠ 3 := by
    intro htd hr3eq
    exact h3 htd (by simpa [hr3eq] using hrdvdα)
  set k : ℕ := orderOf α / r with hk
  have hmul : r * k = orderOf α := by
    rw [hk, Nat.mul_div_cancel' hrdvdα]
  have hrk : ¬ r ∣ k := by
    intro hdiv
    have hsq' : r * r ∣ orderOf α := by
      rw [← hmul]
      exact Nat.mul_dvd_mul_left r hdiv
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq r hr) hsq'
  have hπβ : (π α) ^ k ≠ 1 := by
    intro hpow
    exact hrk (hrdvd.trans (orderOf_dvd_of_pow_eq_one hpow))
  have hβpow : (α ^ k) ^ r = 1 := by
    rw [← pow_mul, mul_comm k r, hmul, pow_orderOf_eq_one]
  have hβout : α ^ k ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    intro hmem
    apply hπβ
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff
      (N := CFSG.ComponentClassification.OuterAutomorphisms.inner X) (α ^ k)).mpr hmem
  exact uc22s2112r34_inner_f1_exc_prime hadm hX ht hr hr2 hr3 hβpow hβout

end Exc

section Center

theorem uc22s2112r34_not_dvd_center_of_five_le (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {M L : Subgroup G} (hL : L ∈ calC M)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : LieModel (BarInf L) t n p f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrg : ¬ r ∣ (genericOrders t n p f).1) : ¬ r ∣ Nat.card ↥(center (Bar2 L)) := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hm : CFSG.Models.LieModel (Bar2 L ⧸ center (Bar2 L)) t n p f :=
    CFSG.Models.LieModel.of_mulEquiv e
      (CFSG.ComponentClassification.HarrisLit.T1.P58b3.models_lieModel_of_lieModel hTB hp
        (by omega) hX)
  have he : exceptionalOrders t n p f = (1, 1) := by
    unfold exceptionalOrders
    split <;> first | rfl | omega
  have hne : (genericOrders t n p f).1 * (genericOrders t n p f).2 * (1 * 1) ≠ 0 := by
    have h1 := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_fst_pos
      hX.admissible
    have h2 := (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_snd_le
      t n p f).1
    exact Nat.mul_ne_zero (Nat.mul_ne_zero h1.ne' h2.ne') (by norm_num)
  have hdvd : Nat.card ↥(center (Bar2 L)) ∣
      (genericOrders t n p f).1 * (genericOrders t n p f).2 * (1 * 1) :=
    CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hL.2.2 hm rfl he hne
  have hrb : ¬ r ∣ (genericOrders t n p f).2 := by
    intro h
    have hb := (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_snd_le
      t n p f).2
    have hb0 := (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_snd_le
      t n p f).1
    have := Nat.le_of_dvd hb0 h
    have := hr.two_le
    omega
  intro h
  have hd' : r ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 * (1 * 1) :=
    h.trans hdvd
  rcases hr.dvd_mul.1 hd' with h | h
  · rcases hr.dvd_mul.1 h with h | h
    · exact hrg h
    · exact hrb h
  · exact hr.not_dvd_one (by simpa using h)

theorem uc22s2112r34_not_dvd_radical_of_gO (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G} (c : Ctx21 D (Choice214U D))
    {L : Subgroup G} (hL : L ∈ calC D.M) {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hX : LieModel (BarInf L) t n p f)
    (hd : ∀ s : ℕ, s.Prime → s ≠ 2 → ¬ s ∣ (genericOrders t n p f).1) :
    ∀ s : ℕ, s.Prime → s ∣ Nat.card c.B0 → ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
  intro s hs hsB
  have hs2 : s ≠ 2 := by
    rintro rfl
    exact (ch214_odd_card c.hpi).not_two_dvd_nat hsB
  exact not_dvd_card_solvableRadical hL.2.2 hs hs2
    (uc22s2112r34_not_dvd_center_of_five_le hGA hTB hL hp hp5 hX hs hs2 (hd s hs hs2))

end Center

end CFSG.LocalAnalysis.UniquenessCase.UC22
