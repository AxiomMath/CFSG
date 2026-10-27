module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusDefs

import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryModel
import CFSG.Quasithin.EmptyFaithful.S151TBTyp
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.Quasithin.Background.A1cA132Action
import CFSG.Quasithin.Background.A1cA133Three
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.C1GNSolvConnect
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.E3Gen
import CFSG.Quasithin.Background.InternalSecB51
import CFSG.Quasithin.Background.InternalSecFF
import CFSG.Quasithin.EmptyFaithful.S14117
import CFSG.Quasithin.EmptyFaithful.S14117Coprime
import CFSG.Quasithin.EmptyFaithful.S14117Rank
import CFSG.Quasithin.EmptyFaithful.S1417Glue
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S151cA2
import CFSG.Quasithin.EmptyFaithful.S151cCases
import CFSG.Quasithin.EmptyFaithful.S152UGen
import CFSG.Quasithin.EmptyFaithful.T1515Top9
import CFSG.Quasithin.H13.J4Core
import CFSG.Quasithin.Vol2.Ch10SecA1012Three
import CFSG.Quasithin.Vol2.Ch10SecA1012Two
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.Sporadic.Schreier.M11
import CFSG.Sporadic.Schreier.M22

public section

namespace CFSG.StandardType.SuSplitRootGen

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem eq_one_of_mem_centralizer_range_of_pow_eq_one
    {G : Type} [Group G] {F : Type} [Field F] [Finite F] {f m ε p : ℕ} [Fact p.Prime]
    (h : UnitaryFieldData 2 f F) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) (hd : 3 ≤ 2 * m + ε)
    {φ : hypSU h m ε →* G} (hker : φ.ker ≤ Subgroup.center (hypSU h m ε)) {c : G}
    (hc : c ∈ φ.range) (hcX : c ∈ Subgroup.centralizer (φ.range : Set G)) (hcp : c ^ p = 1) :
    c = 1 := by
  classical
  have hf2 : 2 ≤ f := by
    have h1 : 1 ≤ f := h.one_le
    have hne : f ≠ 1 := by
      intro hf
      rw [hf, show 2 ^ 1 - 1 = 1 by norm_num, Nat.dvd_one] at hpq
      exact (Fact.out : p.Prime).ne_one hpq
    omega
  have h2f : 2 ^ f ≠ 2 := by
    have hlt : 2 < 2 ^ f :=
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  have hperf : Group.IsPerfect (hypSU h m ε) := by
    obtain ⟨hq, -⟩ :=
      CFSG.AGLEmbedding.LeviBlock.hypSU_facts_of_three_le (h := h) (s := m) (ε := ε) hd
        (fun hc => h2f (congrArg Prod.snd hc))
    exact Group.isPerfect_def.mpr hq.1
  obtain ⟨s, rfl⟩ := hc
  have hsX : φ.rangeRestrict s ∈ Subgroup.center φ.range := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using hcX (y : G) y.2
  have hker' : φ.rangeRestrict.ker ≤ Subgroup.center (hypSU h m ε) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    simpa using congrArg (fun y : φ.range => (y : G)) hx
  have hscen : s ∈ Subgroup.center (hypSU h m ε) :=
    CFSG.Quasithin.S151TB.Typ.mem_center_of_map_mem_center φ.rangeRestrict hker' hsX
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := m) (ε := ε)
  set e : hypSU h m ε ≃* unitarySU 2 f F (2 * m + ε) := hypTransport h hR with he
  have hes : e s ∈ Subgroup.center (unitarySU 2 f F (2 * m + ε)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hscen x]
  have hcenter :=
    CFSG.SeitzReduction.F4Pilot.center_gramSU_eq_normOneScalars (h := h)
      (C := (1 : GL (Fin (2 * m + ε)) F)) isPrimeFormGram_one hd
      (fun hq => h2f hq.2)
  simp only [Units.val_one] at hcenter
  have hSU : unitarySU 2 f F (2 * m + ε) =
      gramSU h (1 : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) F) :=
    unitarySU_eq_gramSU h _
  have hEs : (MulEquiv.subgroupCongr hSU) (e s) ∈ Subgroup.center
      (gramSU h (1 : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) F)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := (MulEquiv.subgroupCongr hSU).surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hes x]
  obtain ⟨c, hnorm, -, hvalE⟩ := mem_normOneScalars.mp (hcenter ▸ hEs)
  have hval' : (e s : GL (Fin (2 * m + ε)) F) =
      Matrix.GeneralLinearGroup.scalar (Fin (2 * m + ε)) c := by
    rw [← hvalE, MulEquiv.subgroupCongr_apply]
  have hs_scalar : (s : GL (HypIndex m ε) F) = Matrix.GeneralLinearGroup.scalar (HypIndex m ε) c := by
    refine Units.ext ?_
    have h1 := coe_hypTransport_symm (h := h) (r := m) (ε := ε) hR (e s)
    rw [show (hypTransport h hR).symm (hypTransport h hR s) = s from
      MulEquiv.symm_apply_apply _ _] at h1
    rw [hval', Matrix.GeneralLinearGroup.coe_scalar, transportInv_scalar hR] at h1
    exact h1
  have hc1 : c ^ (2 ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← h.norm_eq_pow (c : F)]
    exact hnorm
  have hspow : s ^ (2 ^ f + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hs_scalar, ← map_pow, hc1, map_one]
  have hc_pow : (φ s) ^ (2 ^ f + 1) = 1 := by
    rw [← map_pow, hspow, map_one]
  have h1 : orderOf (φ s) ∣ p := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hcp
  have h2 : orderOf (φ s) ∣ 2 ^ f + 1 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hc_pow
  have hcop : p.Coprime (2 ^ f + 1) := by
    rw [(Fact.out : p.Prime).coprime_iff_not_dvd]
    intro hdvd
    have h2f1 : ((2 : ZMod p) ^ f) = 1 := by
      have h : ((2 ^ f - 1 : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact hpq
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
        sub_eq_zero] at h
      exact h
    have h2f2 : ((2 : ZMod p) ^ f) = -1 := by
      have h0 : ((2 ^ f + 1 : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact hdvd
      rw [Nat.cast_add, Nat.cast_one] at h0
      have h1 : ((2 ^ f : ℕ) : ZMod p) = -1 := (add_eq_zero_iff_eq_neg).mp h0
      simpa using h1
    have h2z : ((2 : ℕ) : ZMod p) = 0 := by
      have h : (1 : ZMod p) = -1 := h2f1.symm.trans h2f2
      rw [show ((2 : ℕ) : ZMod p) = 1 + 1 by norm_num]
      nth_rewrite 1 [h]
      exact neg_add_cancel 1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h2z))
  have h3 : orderOf (φ s) ∣ Nat.gcd p (2 ^ f + 1) := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one, Nat.dvd_one] at h3
  exact orderOf_eq_one_iff.mp h3

end CFSG.StandardType.SuSplitRootGen

end
