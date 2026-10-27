module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Q1
public import CFSG.Quasithin.EmptyFaithful.SBd8FlagNine
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13.L52Par

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.L239.L52 (q1 q1_ker_isPGroup)

local notation "SL5" => SpecialLinearGroup (Fin 5) (ZMod 2)

@[expose] def cuts (j : ℕ) : Finset ℕ :=
  [{1, 2, 3, 4}, {1, 4}, {4}, {1, 2, 4}, {1}, {1, 3, 4}, {3}, {2, 3, 4}, {2}, {2, 4}, {3, 4},
    {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}].getD j ∅

@[expose] def QF (s : Finset ℕ) : Subgroup SL5 := flagStabilizer 5 (ZMod 2) (s : Set ℕ)

@[expose] def Yq (j : ℕ) : Subgroup SL5 := QF (cuts j)

@[expose] def ordIdx : List ℕ := [1, 21, 315, 3, 315, 3, 63, 3, 63, 9, 21, 21, 9, 9, 3]

theorem refl_mem_QF {s : Finset ℕ} {i : ℕ} (hi : 1 ≤ i) (hin : i < 5) :
    reflection 5 (ZMod 2) i hi hin ∈ QF s ↔ i ∉ s :=
  ((subflag_stabilizer_generation (s : Set ℕ)).2.2 i hi hin).trans (not_congr Finset.mem_coe)

theorem QF_anti {s t : Finset ℕ} (h : s ⊆ t) : QF t ≤ QF s :=
  BinaryParabolic.flagStabilizer_anti (Finset.coe_subset.2 h)

theorem QF_le_iff {s t : Finset ℕ} (ht : ∀ i ∈ t, 1 ≤ i ∧ i < 5) : QF s ≤ QF t ↔ t ⊆ s := by
  refine ⟨fun h i hi => ?_, QF_anti⟩
  by_contra his
  obtain ⟨h1, h5⟩ := ht i hi
  exact (refl_mem_QF h1 h5).1 (h ((refl_mem_QF h1 h5).2 his)) hi

theorem U_le_QF (s : Finset ℕ) : unitriangular 5 (ZMod 2) ≤ QF s :=
  BinaryParabolic.unitriangular_le_flagStabilizer _

theorem QF_full : QF {1, 2, 3, 4} = unitriangular 5 (ZMod 2) := by
  rw [QF, ← BinaryParabolic.flagStabilizer_Icc (n := 5)]
  congr 1
  ext i
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_Icc]
  omega

theorem card_U : Nat.card (unitriangular 5 (ZMod 2)) = 1024 := by
  rw [card_unitriangular, Nat.card_zmod]
  norm_num

theorem card_SL5 : Nat.card SL5 = 9999360 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_five, ZMod.card]

theorem card_SL3 : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three, ZMod.card]

theorem card_QF_of_relIndex {s : Finset ℕ} {m : ℕ}
    (h : (unitriangular 5 (ZMod 2)).relIndex (QF s) = m) : Nat.card (QF s) = m * 1024 := by
  have h' := Subgroup.relIndex_mul_card (H := unitriangular 5 (ZMod 2)) (K := QF s)
  rw [inf_eq_left.2 (U_le_QF s), h, card_U] at h'
  exact h'.symm

theorem card_QF_full : Nat.card (QF {1, 2, 3, 4}) = 1 * 1024 := by
  rw [QF_full, card_U, one_mul]

theorem card_QF_three {s : Finset ℕ} {j : ℕ} (hj : 1 ≤ j) (hj5 : j < 5)
    (hs : (s : Set ℕ) = Set.Icc 1 (5 - 1) \ {j}) : Nat.card (QF s) = 3 * 1024 := by
  apply card_QF_of_relIndex
  rw [QF, hs]
  exact BinaryParabolic.relIndex_parabolic hj hj5

theorem QF_singleton (k : ℕ) : QF {k} = stabilizer (flagSpace 5 (ZMod 2) k) := by
  ext g
  rw [QF, Finset.coe_singleton, mem_flagStabilizer]
  simp

theorem index_QF_singleton {k : ℕ} (hk : k ≤ 5) :
    ((QF {k}).index : ℚ) = gaussianCoeff 5 k 2 := by
  have h := (subspace_index (K := ZMod 2) (n := 5) hk).2 _ (finrank_flagSpace hk)
  have hcomap : (projStabilizer (flagSpace 5 (ZMod 2) k)).comap (proj 5 (ZMod 2)) =
      stabilizer (flagSpace 5 (ZMod 2) k) := by
    rw [projStabilizer, Subgroup.comap_map_eq_self]
    rw [ker_proj]
    exact scalars_le_stabilizer _
  rw [QF_singleton, ← hcomap, Subgroup.index_comap_of_surjective _ (proj_surjective 5 (ZMod 2)), h,
    Nat.card_zmod]

theorem card_QF_singleton {k c : ℕ} (hk : k ≤ 5) (hc : gaussianCoeff 5 k 2 = c) :
    Nat.card (QF {k}) * c = 9999360 := by
  have h := Subgroup.card_mul_index (QF {k})
  have hi : (QF {k}).index = c := by exact_mod_cast (index_QF_singleton hk).trans hc
  rw [card_SL5, hi] at h
  exact h

theorem card_QF_one : Nat.card (QF {1}) = 315 * 1024 := by
  have h := card_QF_singleton (k := 1) (c := 31) (by norm_num)
    (by norm_num [gaussianCoeff, Finset.prod_range_succ])
  omega

theorem card_QF_two : Nat.card (QF {2}) = 63 * 1024 := by
  have h := card_QF_singleton (k := 2) (c := 155) (by norm_num)
    (by norm_num [gaussianCoeff, Finset.prod_range_succ])
  omega

theorem card_QF_three' : Nat.card (QF {3}) = 63 * 1024 := by
  have h := card_QF_singleton (k := 3) (c := 155) (by norm_num)
    (by norm_num [gaussianCoeff, Finset.prod_range_succ])
  omega

theorem card_QF_four : Nat.card (QF {4}) = 315 * 1024 := by
  have h := card_QF_singleton (k := 4) (c := 31) (by norm_num)
    (by norm_num [gaussianCoeff, Finset.prod_range_succ])
  omega

theorem card_QF_234 : Nat.card (QF {2, 3, 4}) = 3 * 1024 :=
  card_QF_three (j := 1) (by norm_num) (by norm_num) (by ext i; simp; omega)

theorem card_QF_134 : Nat.card (QF {1, 3, 4}) = 3 * 1024 :=
  card_QF_three (j := 2) (by norm_num) (by norm_num) (by ext i; simp; omega)

theorem card_QF_124 : Nat.card (QF {1, 2, 4}) = 3 * 1024 :=
  card_QF_three (j := 3) (by norm_num) (by norm_num) (by ext i; simp; omega)

theorem card_QF_123 : Nat.card (QF {1, 2, 3}) = 3 * 1024 :=
  card_QF_three (j := 4) (by norm_num) (by norm_num) (by ext i; simp; omega)

theorem pair_arith {c : ℕ} (hU : 1024 ∣ c) (hdvd : c ∣ 63 * 1024) (h3 : 3 * 1024 ∣ c)
    (hne3 : c ≠ 3 * 1024) (hne63 : c ≠ 63 * 1024) : c = 9 * 1024 ∨ c = 21 * 1024 := by
  obtain ⟨m, rfl⟩ := hU
  have hm : m ∣ 63 := by
    rw [mul_comm 63] at hdvd
    exact (mul_dvd_mul_iff_left (by norm_num : (1024 : ℕ) ≠ 0)).1 hdvd
  have hm3 : 3 ∣ m := by
    rw [mul_comm 3] at h3
    exact (mul_dvd_mul_iff_left (by norm_num : (1024 : ℕ) ≠ 0)).1 h3
  have hle : m ≤ 63 := Nat.le_of_dvd (by norm_num) hm
  interval_cases m <;> omega

theorem card_QF_pair {s t u : Finset ℕ} (hst : s ⊆ t) (hus : u ⊆ s) (hts : s ≠ t) (hsu : u ≠ s)
    (hbd : ∀ i ∈ t, 1 ≤ i ∧ i < 5) (ht : Nat.card (QF t) = 3 * 1024)
    (hu : Nat.card (QF u) = 63 * 1024) :
    Nat.card (QF s) = 9 * 1024 ∨ Nat.card (QF s) = 21 * 1024 := by
  have hbs : ∀ i ∈ s, 1 ≤ i ∧ i < 5 := fun i hi => hbd i (hst hi)
  apply pair_arith
  · rw [← card_U]
    exact Subgroup.card_dvd_of_le (U_le_QF s)
  · rw [← hu]
    exact Subgroup.card_dvd_of_le (QF_anti hus)
  · rw [← ht]
    exact Subgroup.card_dvd_of_le (QF_anti hst)
  · intro h
    have he := Subgroup.eq_of_le_of_card_ge (QF_anti hst) (h.trans ht.symm).le
    exact hts (Finset.Subset.antisymm hst ((QF_le_iff hbd).1 he.ge))
  · intro h
    have he := Subgroup.eq_of_le_of_card_ge (QF_anti hus) (hu.trans h.symm).le
    exact hsu (Finset.Subset.antisymm hus ((QF_le_iff hbs).1 he.ge))

theorem card_QF_24 : Nat.card (QF {2, 4}) = 9 * 1024 := by
  have h9 : 9 ∣ Nat.card (QF {2, 4}) :=
    SBd8.Flag.nine_dvd_card_flagStabilizer (a := 0) (b := 2) (by norm_num) (by norm_num)
      (by norm_num) (by simp) (by simp)
  rcases card_QF_pair (s := {2, 4}) (t := {1, 2, 4}) (u := {2}) (by decide) (by decide)
    (by decide) (by decide) (by decide) card_QF_124 card_QF_two with h | h <;> omega

theorem card_QF_13 : Nat.card (QF {1, 3}) = 9 * 1024 := by
  have h9 : 9 ∣ Nat.card (QF {1, 3}) :=
    SBd8.Flag.nine_dvd_card_flagStabilizer (a := 1) (b := 3) (by norm_num) (by norm_num)
      (by norm_num) (by simp) (by simp)
  rcases card_QF_pair (s := {1, 3}) (t := {1, 2, 3}) (u := {3}) (by decide) (by decide)
    (by decide) (by decide) (by decide) card_QF_123 card_QF_three' with h | h <;> omega

theorem card_QF_23 : Nat.card (QF {2, 3}) = 9 * 1024 := by
  have h9 : 9 ∣ Nat.card (QF {2, 3}) :=
    SBd8.Flag.nine_dvd_card_flagStabilizer (a := 0) (b := 3) (by norm_num) (by norm_num)
      (by norm_num) (by simp) (by simp)
  rcases card_QF_pair (s := {2, 3}) (t := {1, 2, 3}) (u := {2}) (by decide) (by decide)
    (by decide) (by decide) (by decide) card_QF_123 card_QF_two with h | h <;> omega

@[expose] def g7a : SL5 :=
  ⟨!![0, 0, 1, 0, 0; 1, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1], by decide +kernel⟩

@[expose] def g7b : SL5 :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0], by decide +kernel⟩

theorem orderOf_g7a : orderOf g7a = 7 :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  orderOf_eq_prime (Subtype.ext (by decide +kernel)) (fun h => by
    have := congrArg (fun g : SL5 => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 0) h
    revert this
    decide +kernel)

theorem orderOf_g7b : orderOf g7b = 7 :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  orderOf_eq_prime (Subtype.ext (by decide +kernel)) (fun h => by
    have := congrArg (fun g : SL5 => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 2) h
    revert this
    decide +kernel)

theorem g7a_mem : g7a ∈ QF {3, 4} := by
  have key : ∀ k l : Fin 5, ((l : ℕ) < 3 → 3 ≤ (k : ℕ) →
      ((g7a : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l).val = 0) ∧ ((l : ℕ) < 4 → 4 ≤ (k : ℕ) →
      ((g7a : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l).val = 0) := by decide +kernel
  refine QuasithinUnique.Vol2Native.A312L.mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · exact (ZMod.val_eq_zero _).1 ((key k l).1 hl hk)
  · exact (ZMod.val_eq_zero _).1 ((key k l).2 hl hk)

theorem g7b_mem : g7b ∈ QF {1, 2} := by
  have key : ∀ k l : Fin 5, ((l : ℕ) < 1 → 1 ≤ (k : ℕ) →
      ((g7b : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l).val = 0) ∧ ((l : ℕ) < 2 → 2 ≤ (k : ℕ) →
      ((g7b : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l).val = 0) := by decide +kernel
  refine QuasithinUnique.Vol2Native.A312L.mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · exact (ZMod.val_eq_zero _).1 ((key k l).1 hl hk)
  · exact (ZMod.val_eq_zero _).1 ((key k l).2 hl hk)

theorem card_QF_34 : Nat.card (QF {3, 4}) = 21 * 1024 := by
  have h7 : 7 ∣ Nat.card (QF {3, 4}) := by
    have h := Subgroup.orderOf_dvd_natCard _ g7a_mem
    rwa [orderOf_g7a] at h
  rcases card_QF_pair (s := {3, 4}) (t := {1, 3, 4}) (u := {3}) (by decide) (by decide)
    (by decide) (by decide) (by decide) card_QF_134 card_QF_three' with h | h <;> omega

theorem card_QF_12 : Nat.card (QF {1, 2}) = 21 * 1024 := by
  have h7 : 7 ∣ Nat.card (QF {1, 2}) := by
    have h := Subgroup.orderOf_dvd_natCard _ g7b_mem
    rwa [orderOf_g7b] at h
  rcases card_QF_pair (s := {1, 2}) (t := {1, 2, 3}) (u := {2}) (by decide) (by decide)
    (by decide) (by decide) (by decide) card_QF_123 card_QF_two with h | h <;> omega

theorem arith14 {m k r : ℕ} (hm : m ∣ 315) (h3 : 3 ∣ m) (hne : m ≠ 3) (hr : r ∣ 168)
    (hc : 2 ^ k * r = 1024 * m) : m = 21 := by
  have hcop : Nat.Coprime m (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left hm (by norm_num))
  have h1 : m ∣ 2 ^ k * r := by
    rw [hc]
    exact Dvd.intro_left 1024 rfl
  have h2 : m ∣ 168 := hcop.dvd_of_dvd_mul_left (h1.trans (mul_dvd_mul_left _ hr))
  have hg : Nat.gcd 315 168 = 21 := by norm_num
  have h21 : m ∣ 21 := by
    rw [← hg]
    exact Nat.dvd_gcd hm h2
  have hle : m ≤ 21 := Nat.le_of_dvd (by norm_num) h21
  interval_cases m <;> omega

theorem card_QF_14 : Nat.card (QF {1, 4}) = 21 * 1024 := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hQ : QF {1, 4} = flagStabilizer 5 (ZMod 2) {1, 4} := by
    rw [QF, Finset.coe_insert, Finset.coe_singleton]
  have hker := q1_ker_isPGroup (K := ZMod 2) hK
  have h1 := Subgroup.card_ker_mul_card_range (q1 (ZMod 2) hK)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
  have h2 : Nat.card (q1 (ZMod 2) hK).range ∣ 168 := by
    have h := Subgroup.card_subgroup_dvd_card (q1 (ZMod 2) hK).range
    rwa [card_SL3] at h
  rw [hk] at h1
  have hc : 2 ^ k * Nat.card (q1 (ZMod 2) hK).range =
      Nat.card (QF {1, 4}) := by
    rw [hQ]
    exact h1
  obtain ⟨m, hm⟩ : 1024 ∣ Nat.card (QF {1, 4}) := by
    rw [← card_U]
    exact Subgroup.card_dvd_of_le (U_le_QF _)
  have h315 : 1024 * m ∣ 1024 * 315 := by
    rw [← hm, mul_comm 1024 315, ← card_QF_one]
    exact Subgroup.card_dvd_of_le (QF_anti (by decide))
  have h3 : 1024 * 3 ∣ 1024 * m := by
    rw [← hm, mul_comm 1024 3, ← card_QF_124]
    exact Subgroup.card_dvd_of_le (QF_anti (by decide))
  have hne : m ≠ 3 := by
    rintro rfl
    have he := Subgroup.eq_of_le_of_card_ge (QF_anti (s := {1, 4}) (t := {1, 2, 4}) (by decide))
      (hm.trans (card_QF_124.trans (mul_comm 3 1024)).symm).le
    have := (QF_le_iff (s := {1, 4}) (t := {1, 2, 4}) (by decide)).1 he.ge
    revert this
    decide
  have h21 := arith14 ((mul_dvd_mul_iff_left (by norm_num : (1024 : ℕ) ≠ 0)).1 h315)
    ((mul_dvd_mul_iff_left (by norm_num : (1024 : ℕ) ≠ 0)).1 h3) hne h2 (hc.trans hm)
  omega

theorem Yq_zero : Yq 0 = unitriangular 5 (ZMod 2) := QF_full

theorem U_le_Yq (j : ℕ) : unitriangular 5 (ZMod 2) ≤ Yq j := U_le_QF _

theorem card_Yq : ∀ j < 15, Nat.card (Yq j) = ordIdx.getD j 0 * 1024 := by
  intro j hj
  interval_cases j
  · exact card_QF_full
  · exact card_QF_14
  · exact card_QF_four
  · exact card_QF_124
  · exact card_QF_one
  · exact card_QF_134
  · exact card_QF_three'
  · exact card_QF_234
  · exact card_QF_two
  · exact card_QF_24
  · exact card_QF_34
  · exact card_QF_12
  · exact card_QF_13
  · exact card_QF_23
  · exact card_QF_123

theorem cuts_bound : ∀ j < 15, ∀ i ∈ cuts j, 1 ≤ i ∧ i < 5 := by decide

theorem Yq_le_iff {i j : ℕ} (hj : j < 15) : Yq i ≤ Yq j ↔ cuts j ⊆ cuts i :=
  QF_le_iff (cuts_bound j hj)

theorem eq_top_or_Yq {A : Subgroup SL5} (hA : unitriangular 5 (ZMod 2) ≤ A) :
    A = ⊤ ∨ ∃ j < 15, A = Yq j := by
  classical
  have hA' := (borel_overgroups A (BinaryParabolic.upperTriangular_eq_unitriangular ▸ hA)).1
  set I := borelOvergroupCuts A with hIdef
  have hI : ∀ i ∈ I, 1 ≤ i ∧ i < 5 := fun i ⟨h1, h5, _⟩ => ⟨h1, h5⟩
  set s : Finset ℕ := (Finset.range 5).filter (· ∈ I) with hs
  have hsI : (s : Set ℕ) = I := by
    ext i
    simp only [hs, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨(hI i h).2, h⟩⟩
  have hsub : s ∈ (Finset.range 5).powerset := Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have h0 : 0 ∉ s := fun h => by
    have h' : (0 : ℕ) ∈ (s : Set ℕ) := h
    rw [hsI] at h'
    have := (hI 0 h').1
    omega
  have key : ∀ t ∈ (Finset.range 5).powerset, 0 ∉ t → t = ∅ ∨ ∃ j < 15, t = cuts j := by
    decide +kernel
  rcases key s hsub h0 with h | ⟨j, hj, h⟩
  · left
    rw [hA', ← hsI, h, Finset.coe_empty, flagStabilizer_empty]
  · right
    refine ⟨j, hj, ?_⟩
    rw [hA', ← hsI, h]
    rfl

end CFSG.Quasithin.H13.L52Par
