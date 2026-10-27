module

public import CFSG.Quasithin.H13.L32A726R
public import CFSG.RankThree.Automorphisms.SuzukiCoprime
public import CFSG.RankThree.PartTwo.KFacts.KS14SzClassical
public import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree
public import CFSG.RankThree.PartTwo.KFacts.KS14SzRee
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru

public section

namespace CFSG.Quasithin.H13.KG726Sz

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.KFacts

theorem three_dvd_card_of_mem {α : Type*} [Group α] {H : Subgroup α} {w : α} (hw : w ∈ H)
    (h3 : w ^ 3 = 1) (h1 : w ≠ 1) : 3 ∣ Nat.card H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (⟨w, hw⟩ : H) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using h3)) fun h => h1 (congrArg Subtype.val h)
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem three_dvd_card_alternatingGroup {n : ℕ} (hn : 3 ≤ n) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have h3 : (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ *
      Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨2, by omega⟩).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  have ho : orderOf (⟨_, h3.mem_alternatingGroup⟩ : alternatingGroup (Fin n)) = 3 := by
    rw [Subgroup.orderOf_mk, h3.orderOf]
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem three_dvd_card_m11 : 3 ∣ Nat.card (NativeSporadic.Carrier .M11) := by
  set a : Equiv.Perm (Fin 11) :=
    List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]
  set b : Equiv.Perm (Fin 11) := List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]
  have ha : a ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : b ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact three_dvd_card_of_mem
    (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ha hb) hb) ha) hb) hb)
    (by decide +kernel) (by decide +kernel)

theorem three_dvd_card_m12 : 3 ∣ Nat.card (NativeSporadic.Carrier .M12) := by
  set b : Equiv.Perm (Fin 12) := List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] *
    List.formPerm [4, 11, 10] * List.formPerm [5, 9, 6]
  have hb : b ∈ NativeSporadic.M12 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact three_dvd_card_of_mem hb (by decide +kernel) (by decide +kernel)

theorem three_dvd_card_m22 : 3 ∣ Nat.card (NativeSporadic.Carrier .M22) := by
  set a : Equiv.Perm (Fin 22) :=
    List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
      List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] *
      List.formPerm [10, 13]
  set b : Equiv.Perm (Fin 22) :=
    List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
      List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]
  have ha : a ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : b ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hbi := inv_mem hb
  exact three_dvd_card_of_mem
    (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ha hb) ha) hb) ha) hbi) ha)
      hbi)
    (by decide +kernel) (by decide +kernel)

theorem three_dvd_card_m23 : 3 ∣ Nat.card (NativeSporadic.Carrier .M23) := by
  set a : Equiv.Perm (Fin 23) :=
    List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
      List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
      List.formPerm [20, 21]
  set b : Equiv.Perm (Fin 23) :=
    List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
      List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]
  have ha : a ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : b ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact three_dvd_card_of_mem
    (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ha hb) hb) ha) hb) hb)
    (by decide +kernel) (by decide +kernel)

theorem three_dvd_card_m24 : 3 ∣ Nat.card (NativeSporadic.Carrier .M24) := by
  set b : Equiv.Perm (Fin 24) := List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] *
    List.formPerm [2, 8, 14] * List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] *
    List.formPerm [18, 23, 22]
  have hb : b ∈ NativeSporadic.M24 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact three_dvd_card_of_mem hb (by decide +kernel) (by decide +kernel)

theorem three_dvd_card_carrier
    {s : TauCeti.SporadicName} (hs : IsLemma115SporadicName s) :
    3 ∣ Nat.card (NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact three_dvd_card_m11
  · exact three_dvd_card_m12
  · exact three_dvd_card_m22
  · exact three_dvd_card_m23
  · exact three_dvd_card_m24
  · rw [show Nat.card (NativeSporadic.Carrier .J2) = 604800 from CFSG.Sporadic.J2.card_J2]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from
      CFSG.Sporadic.J4.card_J4]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .HS) = 44352000 from CFSG.Sporadic.HS.card_HS]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .He) = 4030387200 from CFSG.Sporadic.He.card_He]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 from CFSG.Sporadic.Ru.card_Ru]
    norm_num

theorem three_dvd_or_suzuki
    {X : Type} [Group X] [Finite X]
    (h : Lemma115LieCharTwo X) : 3 ∣ Nat.card X ∨ ∃ f : ℕ, SuzukiModel X 2 f := by
  rcases h with ((⟨f, h8⟩ | hT) | ⟨n, -, hL⟩) | hA6 | hU
  · rcases h8 with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, -, h1⟩ |
      ⟨-, -, h1⟩
    · exact .inl (KS14.classicalModel_exists_orderOf_eq_three h1).2
    · exact .inl (KS14.classicalModel_exists_orderOf_eq_three h1).2
    · exact .inl (KS14.classicalModel_exists_orderOf_eq_three h1).2
    · exact .inl (KS14.classicalModel_exists_orderOf_eq_three h1).2
    · exact .inl
        (CFSG.RankThree.Chevalley.Chevalley_exceptional_models_order_divisible_by_three X _ _ _ h1)
    · exact .inl
        (CFSG.RankThree.Chevalley.Chevalley_exceptional_models_order_divisible_by_three X _ _ _ h1)
    · exact .inl (KS14.three_dvd_card_of_reeTitsModel h1)
    · exact .inr ⟨f, h1⟩
  · exact .inl (KS14.three_dvd_card_of_reeTitsModel hT)
  · exact .inl (KS14.classicalModel_exists_orderOf_eq_three hL).2
  · obtain ⟨e⟩ := hA6
    refine .inl ?_
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_alternatingGroup (by norm_num)
  · exact .inl (KS14.classicalModel_exists_orderOf_eq_three hU).2

section Cases

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem three_dvd_card_caseB
    (h : Lemma115CaseB L z) :
    3 ∣ Nat.card L := by
  obtain ⟨-, -, hX, -⟩ := h
  have h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hX with h1 | h1
    · exact (KS14.classicalModel_exists_orderOf_eq_three h1).2
    · exact CFSG.RankThree.Chevalley.Chevalley_exceptional_models_order_divisible_by_three _ _ _ _
        h1
  exact h3.trans (Subgroup.card_quotient_dvd_card _)

omit [Finite G] in
theorem three_dvd_card_caseC (h : Lemma115CaseC L z) : 3 ∣ Nat.card L := by
  obtain ⟨φ, -⟩ := h
  have h3 : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [Nat.card_congr φ.toEquiv]
    exact three_dvd_card_alternatingGroup (by norm_num)
  exact h3.trans (Subgroup.card_quotient_dvd_card _)

omit [Finite G] in
theorem three_dvd_card_caseD (h : Lemma115CaseD L z) : 3 ∣ Nat.card L := by
  obtain ⟨φ, -⟩ := h
  have h3 : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [Nat.card_congr φ.toEquiv]
    exact three_dvd_card_alternatingGroup (by norm_num)
  exact h3.trans (Subgroup.card_quotient_dvd_card _)

omit [Finite G] in
theorem three_dvd_card_caseE (h : Lemma115CaseE L z) : 3 ∣ Nat.card L := by
  obtain ⟨h1 | ⟨p, -, h1⟩, -⟩ := h
  · exact (KS14.classicalModel_exists_orderOf_eq_three h1).2
  · exact (KS14.classicalModel_exists_orderOf_eq_three h1).2

omit [Finite G] in
theorem three_dvd_card_caseF
    (h : Lemma115CaseF L z) : 3 ∣ Nat.card L := by
  obtain ⟨⟨s, hs, ⟨e⟩⟩, -⟩ := h
  have h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_carrier hs
  exact h3.trans (Subgroup.card_quotient_dvd_card _)

end Cases

theorem kg14726Sz_holds :
    KG14726Sz := by
  intro G _ _ L z hc _ h3 P hP
  rcases hc with ⟨-, hlie, -⟩ | hB | hC | hD | hE | hF
  · rcases three_dvd_or_suzuki hlie with h | ⟨f, hsz⟩
    · exact absurd h h3
    · exact (CFSG.RankThree.Automorphisms.Suzuki_coprime_odd_prime_automorphism_subgroups_cyclic.{0}
        ↥L 2 f hsz Nat.prime_three ⟨1, rfl⟩ h3).1 P hP
  · exact absurd (three_dvd_card_caseB hB) h3
  · exact absurd (three_dvd_card_caseC hC) h3
  · exact absurd (three_dvd_card_caseD hD) h3
  · exact absurd (three_dvd_card_caseE hE) h3
  · exact absurd (three_dvd_card_caseF hF) h3

end CFSG.Quasithin.H13.KG726Sz
