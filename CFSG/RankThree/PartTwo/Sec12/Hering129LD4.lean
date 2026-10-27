module

public import CFSG.RankThree.PartTwo.Sec12.Hering129LG2
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF2
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusLayer
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL3Model
import CFSG.LieType.SteinbergBROddLinearThreeParabolic

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof CFSG.LieType.Chevalley

section Arith

theorem eq_of_sl3Order_eq' {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t)
    (h : s ^ 3 * ((s ^ 2 - 1) * (s ^ 3 - 1)) = t ^ 3 * ((t ^ 2 - 1) * (t ^ 3 - 1))) : s = t := by
  rw [← mul_assoc, ← mul_assoc] at h
  rcases lt_trichotomy s t with hst | hst | hst
  · exact absurd h (KFacts.sl3Order_lt (by omega) hst).ne
  · exact hst
  · exact absurd h.symm (KFacts.sl3Order_lt (by omega) hst).ne

theorem two_pow_mod_three_of_even {m : ℕ} (h : Even m) : 2 ^ m % 3 = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_odd {m : ℕ} (h : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end Arith

section D4


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem d4_layer_threeA (P : D4Par n X σ) (hn : 2 ≤ n) {z : C0 σ} (hx : IsClassX σ z) :
    Group.IsPerfect ↥(layerSub σ z) ∧ Sec4.IsSLThreePiAt ↥(layerSub σ z) (2 ^ n) := by
  haveI := P.charP
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨F, hFf, hFfin, h4, h3, e, -⟩ := layer_linear_model P hn hev hx
    have hcard := layer_card_even P hn hev hx
    have hS := CFSG.LieType.SteinbergBR.BlockPar.card_SL_three' (F := F)
    rw [Nat.card_congr e.toEquiv, hS] at hcard
    have hq4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hFc : Nat.card F = 2 ^ n := eq_of_sl3Order_eq' (by omega) (by omega) hcard
    have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num)).1
    refine ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_⟩
    refine ⟨F, hFf, hFfin, Or.inl ⟨hFc, two_pow_mod_three_of_even hev, ⟨?_⟩⟩⟩
    exact e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)
  · obtain ⟨F, hFf, hF, e, -⟩ := layer_unitary_model P hn hodd hx
    have hq2 : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) hn)
    have hperf : Group.IsPerfect ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n F 3) :=
      KFacts.isPerfect_unitarySU_three hF hq2
    refine ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_⟩
    refine ⟨F, hFf, hF.finite, Or.inr ⟨?_, two_pow_mod_three_of_odd hodd, ⟨?_⟩⟩⟩
    · rw [hF.card, ← pow_mul, mul_comm]
    · exact e.trans (MulEquiv.subgroupCongr
        (show CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n F 3 =
          CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F from rfl))

theorem d4_isThreeA (P : D4Par n X σ) (hn : 2 ≤ n) {z : C0 σ} (hzA : z ∈ Asub σ)
    (hz : orderOf z = 3) : IsThreeA z (2 ^ n) := by
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  have hx : IsClassX σ z := ⟨hz3, hz1, 1, by simpa using hzA⟩
  obtain ⟨hperf, hSL⟩ := d4_layer_threeA P hn hx
  obtain ⟨hzD, -⟩ := classX_layer σ P hn hx
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  have hres : resCent (⊤ : Subgroup (C0 σ)) z = layerSub σ z := by
    apply le_antisymm
    · show inSubgroup perfectResidual ((⊤ : Subgroup (C0 σ)) ⊓
        Subgroup.centralizer ({z} : Set (C0 σ))) ≤ _
      rw [top_inf_eq]
      exact inSubgroup_perfectResidual_le_commutator' _
    · have hle : layerSub σ z ≤ (⊤ : Subgroup (C0 σ)) ⊓
          Subgroup.centralizer ({z} : Set (C0 σ)) := by
        refine le_inf le_top ?_
        refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
        rw [commutatorElement_def]
        exact (cenX σ z).mul_mem ((cenX σ z).mul_mem ((cenX σ z).mul_mem ha hb)
          ((cenX σ z).inv_mem ha)) ((cenX σ z).inv_mem hb)
      exact le_inSubgroup_perfectResidual_of_isPerfect hle hperf
  refine ⟨hz, ?_, ?_⟩
  · rw [hres]
    exact hzD
  · exact isSLThreePiAt_congr (MulEquiv.subgroupCongr hres.symm) hSL

theorem d4_resCent_threeB (P : D4Par n X σ) (hn : 2 ≤ n) {t : C0 σ} (htB : t ∈ Bsub σ)
    (ht : orderOf t = 3) : resCent (⊤ : Subgroup (C0 σ)) t = Asub σ := by
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  have ht3 : t ^ 3 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hX4 : 4 ≤ Nat.card X := by
    rw [P.card]
    calc 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      _ ≤ (2 ^ n) ^ 3 := Nat.le_self_pow (by norm_num) _
  apply le_antisymm
  · show inSubgroup perfectResidual ((⊤ : Subgroup (C0 σ)) ⊓
      Subgroup.centralizer ({t} : Set (C0 σ))) ≤ _
    rw [top_inf_eq]
    exact (inSubgroup_perfectResidual_le_commutator' _).trans
      (centralizer_comm_le_asub σ n P.one_le P.card P.frob htB ht3 ht1)
  · have hperf : Group.IsPerfect ↥(Asub σ) := (isQuasisimple_d4ShortSL2 P.sigma_pow_three hX4).1
    have hle : Asub σ ≤ (⊤ : Subgroup (C0 σ)) ⊓ Subgroup.centralizer ({t} : Set (C0 σ)) := by
      refine le_inf le_top fun a ha => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Asub_Bsub_commute ha htB
    exact le_inSubgroup_perfectResidual_of_isPerfect hle hperf

theorem d4_threeLocalModel [Finite (C0 σ)] (P : D4Par n X σ) (hn : 2 ≤ n)
    (r : TauCeti.PrimePower) (hr : r.card = 2 ^ n) :
    ThreeLocalModel (C0 σ) r (r.card ^ 3) (Asub σ) (Bsub σ) := by
  haveI := P.charP
  have hfix4 := P.four_le_card_fix hn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  refine ⟨?_, ?_, fun a ha b hb => Asub_Bsub_commute ha hb, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : Fintype X := Fintype.ofFinite X
    refine ⟨X, inferInstance, inferInstance, ?_, ⟨(asubEquiv P).symm⟩⟩
    rw [← Nat.card_eq_fintype_card, P.card, hr]
  · have := (isQuasisimple_sl2 hfix4).1
    exact Group.IsPerfect.ofSurjective (f := (bsubEquiv P).toMonoidHom) (bsubEquiv P).surjective
  · intro x hxA hxB _
    have : x ∈ Asub σ ⊓ Bsub σ := ⟨hxA, hxB⟩
    rw [Asub_inf_Bsub P] at this
    exact Subgroup.mem_bot.mp this
  · obtain ⟨h3', h1'⟩ := sl2Three_pow_three (fixSubfield σ)
    refine ⟨((bsubEquiv P (sl2Three (fixSubfield σ)) : Bsub σ) : C0 σ), (bsubEquiv P _).2, ?_⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← Subgroup.coe_pow, ← map_pow, h3', map_one, Subgroup.coe_one]
    · intro h
      apply h1'
      apply (bsubEquiv P).injective
      rw [map_one]
      exact Subtype.ext h
  · intro g hg
    have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hg
      omega
    exact KS11Lie6Proof.d4ThreeConj_holds X (2 ^ n) σ P.card P.frob h3 g hg3 hg1
  · intro z hzA hz
    rw [hr]
    exact d4_isThreeA P hn hzA hz
  · intro t htB ht
    exact d4_resCent_threeB P hn htB ht

end D4

end Hering129L

end CFSG.RankThree.PartTwo.Sec12
