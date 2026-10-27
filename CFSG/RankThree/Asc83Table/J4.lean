module

public import CFSG.RankThree.Asc83Table.MatGroup
public import CFSG.RankThree.Asc83Table.J4Check
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Sporadic.J4
public import Certificates.Certificate8002
public import Certificates.Certificate3084
public import CFSG.Sporadic.J4Base

public section

namespace CFSG.RankThree.Asc83Table.J4

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem facts : Ex27Facts j4Cert 17 18 0 :=
  ⟨mem_facts 0 rfl, mem_facts 1 rfl, mem_facts 2 rfl, mem_facts 3 rfl, mem_facts 4 rfl⟩

noncomputable abbrev E (i : Fin 4) : E9Basis NativeSporadic.J4 :=
  facts.basis (spec2fr 112) j4_check i

theorem bR_mem_0 : bR ∈ (E 0).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 0 (g := 60) (o := 6) (pp := 2) (q := 2) (r := 0)
    (s := 2) (mem_facts 5 rfl) (mem_facts 6 rfl) (mem_facts 7 rfl) (by decide)

theorem bS_mem_0 : bS ∈ (E 0).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 0 (g := 61) (o := 2) (pp := 2) (q := 0) (r := 0)
    (s := 1) (mem_facts 8 rfl) (mem_facts 9 rfl) (mem_facts 10 rfl) (by decide)

theorem w0_mem_0 : w0 ∈ (E 0).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 0 (g := 81) (o := 12) (pp := 0) (q := 1) (r := 1)
    (s := 0) (mem_facts 11 rfl) (mem_facts 12 rfl) (mem_facts 13 rfl) (by decide)

theorem bR_mem_1 : bR ∈ (E 1).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 1 (g := 62) (o := 6) (pp := 2) (q := 2) (r := 0)
    (s := 2) (mem_facts 14 rfl) (mem_facts 15 rfl) (mem_facts 16 rfl) (by decide)

theorem bS_mem_1 : bS ∈ (E 1).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 1 (g := 63) (o := 2) (pp := 2) (q := 0) (r := 0)
    (s := 1) (mem_facts 17 rfl) (mem_facts 18 rfl) (mem_facts 19 rfl) (by decide)

theorem w0_mem_1 : w0 ∈ (E 1).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 1 (g := 87) (o := 12) (pp := 0) (q := 1) (r := 1)
    (s := 0) (mem_facts 20 rfl) (mem_facts 21 rfl) (mem_facts 22 rfl) (by decide)

theorem bR_mem_2 : bR ∈ (E 2).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 2 (g := 64) (o := 6) (pp := 2) (q := 2) (r := 0)
    (s := 2) (mem_facts 23 rfl) (mem_facts 24 rfl) (mem_facts 25 rfl) (by decide)

theorem bS_mem_2 : bS ∈ (E 2).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 2 (g := 65) (o := 12) (pp := 2) (q := 0) (r := 0)
    (s := 1) (mem_facts 26 rfl) (mem_facts 27 rfl) (mem_facts 28 rfl) (by decide)

theorem w0_mem_2 : w0 ∈ (E 2).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 2 (g := 66) (o := 12) (pp := 0) (q := 1) (r := 1)
    (s := 0) (mem_facts 29 rfl) (mem_facts 30 rfl) (mem_facts 31 rfl) (by decide)

theorem bR_mem_3 : bR ∈ (E 3).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 3 (g := 67) (o := 6) (pp := 2) (q := 2) (r := 0)
    (s := 2) (mem_facts 32 rfl) (mem_facts 33 rfl) (mem_facts 34 rfl) (by decide)

theorem bS_mem_3 : bS ∈ (E 3).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 3 (g := 68) (o := 6) (pp := 2) (q := 0) (r := 0)
    (s := 1) (mem_facts 35 rfl) (mem_facts 36 rfl) (mem_facts 37 rfl) (by decide)

theorem w0_mem_3 : w0 ∈ (E 3).rhoE.range :=
  facts.mem_range (spec2fr 112) j4_check 3 (g := 69) (o := 4) (pp := 0) (q := 1) (r := 1)
    (s := 0) (mem_facts 38 rfl) (mem_facts 39 rfl) (mem_facts 40 rfl) (by decide)

theorem automizer_B (i : Fin 4) : Nonempty (Automizer (E i).sub ≃* GL23) := by
  fin_cases i
  · exact (E 0).nonempty_gl bR_mem_0 bS_mem_0 w0_mem_0
  · exact (E 1).nonempty_gl bR_mem_1 bS_mem_1 w0_mem_1
  · exact (E 2).nonempty_gl bR_mem_2 bS_mem_2 w0_mem_2
  · exact (E 3).nonempty_gl bR_mem_3 bS_mem_3 w0_mem_3

theorem factorization_card : (Nat.card NativeSporadic.J4).factorization 3 = 3 := by
  rw [CFSG.Sporadic.J4.card_J4]
  exact factorization_eq_of_eq Nat.prime_three
    (show 86775571046077562880 = 3 ^ 3 * 3213910038743613440 by norm_num) (by norm_num)

theorem table {L : Type} [Group L] (hL : NativeSporadic.IsSporadic L .J4) :
    (∀ P : Sylow 3 L, Nat.card P = 27) ∧ CFSG.pRank 3 L = 2 ∧
      ∀ B : Subgroup L, IsElementaryAbelian 3 B → Nat.card B = 9 →
        ActsNontriviallyOnTwoSubgroup B →
          Nonempty (Automizer B ≃* GL23) := by
  obtain ⟨e⟩ := hL
  obtain ⟨h₁, h₂, h₃⟩ := ex27_transport (facts.x_cube (spec2fr 112) j4_check)
    (facts.y_cube (spec2fr 112) j4_check) (facts.z_x (spec2fr 112) j4_check)
    (facts.z_y (spec2fr 112) j4_check) (facts.z_ne (spec2fr 112) j4_check) factorization_card
    (e : L ≃* NativeSporadic.J4)
  refine ⟨h₁, h₂, fun B _ hB _ => ?_⟩
  obtain ⟨i, ⟨f⟩⟩ := h₃ B hB
  obtain ⟨q⟩ := automizer_B i
  exact ⟨f.trans q⟩

end CFSG.RankThree.Asc83Table.J4
