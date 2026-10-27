module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.Quasithin.P134

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.EmptyFaithfulMultiple

@[expose] def E9Outcome {A : Type} [Group A] (L P T : Subgroup A) : Prop :=
  StatedClassicalModel ↥L .PSL 3 3 1 ∨
    (∃ n : ℕ, Even n ∧ StatedClassicalModel ↥L .PSp 2 2 n ∧ AutCyclic T P) ∨
    Nonempty (↥L ≃* NativeSporadic.Carrier .M11) ∨ StatedClassicalModel ↥L .PSL 4 2 1 ∨
    StatedClassicalModel ↥L .PSL 5 2 1 ∨ Nonempty (↥L ≃* NativeSporadic.Carrier .He)

theorem three_dvd_card_M11 : 3 ∣ Nat.card (NativeSporadic.Carrier .M11) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haM : (List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] *
      List.formPerm [7, 8] : Equiv.Perm (Fin 11)) ∈ NativeSporadic.M11 :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbM : (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8] : Equiv.Perm (Fin 11)) ∈
      NativeSporadic.M11 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨a, ha⟩ : ∃ a : NativeSporadic.M11, (a : Equiv.Perm (Fin 11)) = List.formPerm [1, 9] *
      List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8] := ⟨⟨_, haM⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : NativeSporadic.M11,
      (b : Equiv.Perm (Fin 11)) = List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8] :=
    ⟨⟨_, hbM⟩, rfl⟩
  have hg3 : (a * b * b * a * b * b) ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one, ha, hb]
    decide +kernel
  have hg1 : a * b * b * a * b * b ≠ 1 := by
    intro h
    have := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_one, ha, hb] at this
    revert this
    decide +kernel
  have hord : orderOf (a * b * b * a * b * b) = 3 := orderOf_eq_prime hg3 hg1
  have := orderOf_dvd_natCard (a * b * b * a * b * b)
  rwa [hord] at this

theorem two_mul_card_alternating (n : ℕ) (hn : 2 ≤ n) :
    2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm, Fintype.card_fin]

theorem three_dvd_card_alternating (n : ℕ) (hn : 3 ≤ n) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have h := two_mul_card_alternating n (by omega)
  have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  rw [← h] at h3
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)

theorem statedClassicalModel_of_alternating_eight {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 8))) : StatedClassicalModel X .PSL 4 2 1 := by
  rcases (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff X).mpr h with
    ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact hc
  all_goals exact absurd ht (by decide)

theorem dispatch (hF : Facts134E9He) {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    (hL : CFSG.Milestones.SQTKSimpleList ↥L) :
    (∃ f : ℕ, SuzukiModel ↥L 2 f) ∨
      (3 ∣ Nat.card L ∧ (E9Config L P T → E9Outcome L P T)) := by
  rcases hL with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, hodd⟩ | (⟨f, hf⟩ | hf) | ⟨n, hn, hmod⟩ |
    ⟨s, hs, ⟨e⟩⟩
  ·
    have hcard : Nat.card L = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
    right
    refine ⟨hcard ▸ three_dvd_card_alternating n (by omega), fun hcfg => ?_⟩
    interval_cases n
    · exfalso
      have h9 : 9 ∣ Nat.card L := hcfg.card ▸ Subgroup.card_dvd_of_le hcfg.le
      have h60 := two_mul_card_alternating 5 (by norm_num)
      rw [← hcard] at h60
      norm_num [Nat.factorial] at h60
      omega
    · exact (hF.alt6 A L P T ⟨e⟩ hcfg).elim
    · exact (hF.alt7 A L P T ⟨e⟩ hcfg).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl (statedClassicalModel_of_alternating_eight ⟨e⟩))))
  ·
    right
    rcases hodd with ⟨f, hf, hmod⟩ | hmod | hmod
    · refine ⟨hF.psl2OddOrder p f hp hp2 hf ↥L hmod, fun hcfg => ?_⟩
      exfalso
      by_cases hp3 : p = 3
      · subst hp3
        rcases hf with rfl | rfl
        · have h := hmod.1.2.2.2.2
          exact h (by norm_num)
        · exact hF.psl2Nine A L P T hmod hcfg
      · exact hF.psl2OddCyclic p f hp hp2 hp3 hf A L P T hmod hcfg
    · refine ⟨hF.psl3OddOrder p hp hp2 ↥L hmod, fun hcfg => ?_⟩
      by_cases hp3 : p = 3
      · subst hp3
        exact Or.inl hmod
      · exfalso
        have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
          have : p % 3 ≠ 0 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
            (Nat.dvd_of_mod_eq_zero h)).symm
          omega
        rcases h3 with h3 | h3
        · exact hF.psl3Plus p hp h3 A L P T hmod hcfg
        · exact hF.psl3Minus p hp hp2 h3 A L P T hmod hcfg
    · refine ⟨hF.psu3OddOrder p hp hp2 ↥L hmod, fun hcfg => ?_⟩
      exfalso
      by_cases hp3 : p = 3
      · subst hp3
        exact hF.psu3Three A L P T hmod hcfg
      · have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
          have : p % 3 ≠ 0 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
            (Nat.dvd_of_mod_eq_zero h)).symm
          omega
        rcases h3 with h3 | h3
        · exact hF.psu3Plus p hp h3 A L P T hmod hcfg
        · exact hF.psu3Minus p hp hp2 h3 A L P T hmod hcfg
  ·
    rcases hf with ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ |
      ⟨-, -, hmod⟩ | ⟨-, -, hmod⟩
    · exact Or.inr ⟨hF.psl2EvenOrder f ↥L hmod,
        fun hcfg => (hF.psl2EvenCyclic f A L P T hmod hcfg).elim⟩
    · exact Or.inr ⟨hF.psl3EvenOrder f ↥L hmod,
        fun hcfg => (hF.psl3Even f A L P T hmod hcfg).elim⟩
    · exact Or.inr ⟨hF.psu3EvenOrder f ↥L hmod,
        fun hcfg => (hF.psu3Even f A L P T hmod hcfg).elim⟩
    · refine Or.inr ⟨hF.psp4EvenOrder f ↥L hmod, fun hcfg => ?_⟩
      obtain ⟨hev, hcyc⟩ := hF.psp4Even f A L P T hmod hcfg
      exact Or.inr (Or.inl ⟨f, hev, hmod, hcyc⟩)
    · exact Or.inr ⟨hF.g2EvenOrder f ↥L hmod,
        fun hcfg => (hF.g2Even f A L P T hmod hcfg).elim⟩
    · exact Or.inr ⟨hF.d4EvenOrder f ↥L hmod,
        fun hcfg => (hF.d4Even f A L P T hmod hcfg).elim⟩
    · exact Or.inr ⟨hF.f4EvenOrder f ↥L hmod,
        fun hcfg => (hF.f4Even f A L P T hmod hcfg).elim⟩
    · exact Or.inl ⟨f, hmod⟩
  ·
    exact Or.inr ⟨hF.titsOrder ↥L hf, fun hcfg => (hF.tits A L P T hf hcfg).elim⟩
  ·
    refine Or.inr ⟨hF.psl45Order n hn ↥L hmod, fun _ => ?_⟩
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl hmod)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmod))))
  ·
    right
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨Nat.card_congr e.toEquiv ▸ three_dvd_card_M11,
        fun _ => Or.inr (Or.inr (Or.inl ⟨e⟩))⟩
    · exact ⟨hF.m12.1 ↥L ⟨e⟩, fun hcfg => (hF.m12.2 A L P T ⟨e⟩ hcfg).elim⟩
    · exact ⟨hF.m22.1 ↥L ⟨e⟩, fun hcfg => (hF.m22.2 A L P T ⟨e⟩ hcfg).elim⟩
    · exact ⟨hF.m23.1 ↥L ⟨e⟩, fun hcfg => (hF.m23.2 A L P T ⟨e⟩ hcfg).elim⟩
    · exact ⟨hF.m24.1 ↥L ⟨e⟩, fun hcfg => (hF.m24.2 A L P T ⟨e⟩ hcfg).elim⟩
    · exact ⟨hF.j1Order ↥L ⟨e⟩, fun hcfg => (hF.j1 A L P T ⟨e⟩ hcfg).elim⟩
    · exact ⟨hF.j2.1 ↥L ⟨e⟩, fun hcfg => (hF.j2.2 A L P T ⟨e⟩ hcfg).elim⟩
    · exact ⟨hF.j4.1 ↥L ⟨e⟩, fun hcfg => (hF.j4.2 A L P T ⟨e⟩ hcfg).elim⟩
    · exact ⟨hF.hs.1 ↥L ⟨e⟩, fun hcfg => (hF.hs.2 A L P T ⟨e⟩ hcfg).elim⟩
    ·
      exact ⟨hF.he ↥L ⟨e⟩, fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩))))⟩
    · exact ⟨hF.ru.1 ↥L ⟨e⟩, fun hcfg => (hF.ru.2 A L P T ⟨e⟩ hcfg).elim⟩

end CFSG.Quasithin.P134
