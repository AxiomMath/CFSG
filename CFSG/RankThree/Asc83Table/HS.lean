module

public import CFSG.RankThree.Asc83Table.MatGroup
public import CFSG.RankThree.Asc83Table.HSCheck
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Sporadic.HS
public import Certificates.Certificate8000
public import Certificates.Certificate3167
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.RankThree.Asc83Table.HS

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem facts : E9Facts hsCert 5 6 0 0 0 0 :=
  ⟨mem_facts 0 rfl, mem_facts 1 rfl, mem_facts 4 rfl, mem_facts 5 rfl, mem_facts 6 rfl,
    mem_facts 7 rfl, mem_facts 8 rfl⟩

noncomputable abbrev E : E9Basis NativeSporadic.HS := facts.basis (spec2fr 20) hs_check

@[expose] def sdR : GL23 := gl23 !![0, 1; 1, 1] !![2, 1; 1, 0] (by decide) (by decide)

@[expose] def sdS : GL23 := gl23 !![1, 0; 1, 2] !![1, 0; 1, 2] (by decide) (by decide)

theorem sdR_mem : sdR ∈ E.rhoE.range :=
  facts.mem_range (spec2fr 20) hs_check (g := 7) (o := 8) (pp := 0) (q := 1) (r := 1) (s := 1)
    (mem_facts 2 rfl) (mem_facts 9 rfl) (mem_facts 10 rfl) (by decide)

theorem sdS_mem : sdS ∈ E.rhoE.range :=
  facts.mem_range (spec2fr 20) hs_check (g := 8) (o := 6) (pp := 1) (q := 0) (r := 1) (s := 2)
    (mem_facts 3 rfl) (mem_facts 11 rfl) (mem_facts 12 rfl) (by decide)

theorem sdR_pow : sdR ^ 8 = 1 := by decide +kernel

theorem sdS_pow : sdS ^ 2 = 1 := by decide +kernel

theorem sd_conj : sdS * sdR * sdS⁻¹ = sdR ^ 3 := by decide +kernel

theorem sd_ne : ∀ i : Fin 8, ∀ e : Fin 2, sdR ^ (i : ℕ) * sdS ^ (e : ℕ) = 1 → i = 0 ∧ e = 0 := by
  decide +kernel

theorem not_dvd_card : ¬ 27 ∣ Nat.card NativeSporadic.HS := by
  rw [CFSG.Sporadic.HS.card_HS]
  decide

theorem automizer_P0 : Nonempty (Automizer E.sub ≃* CFSG.Open.SemidihedralGroup 4) :=
  E.nonempty_semidihedral (E.three_not_dvd not_dvd_card) sdR_mem sdS_mem sdR_pow sdS_pow sd_conj
    sd_ne

theorem factorization_card : (Nat.card NativeSporadic.HS).factorization 3 = 2 := by
  rw [CFSG.Sporadic.HS.card_HS]
  exact factorization_eq_of_eq Nat.prime_three (show 44352000 = 3 ^ 2 * 4928000 by norm_num)
    (by norm_num)

theorem table {L : Type} [Group L] (hL : NativeSporadic.IsSporadic L .HS) :
    (∀ P : Sylow 3 L, IsElementaryAbelian 3 (P : Subgroup L) ∧ Nat.card P = 9) ∧
      CFSG.pRank 3 L = 2 ∧
      ∀ B : Subgroup L, IsElementaryAbelian 3 B → Nat.card B = 9 →
        ActsNontriviallyOnTwoSubgroup B →
          Nonempty (Automizer B ≃* CFSG.Open.SemidihedralGroup 4) := by
  obtain ⟨e⟩ := hL
  obtain ⟨h₁, h₂, h₃⟩ := e9_transport E factorization_card (e : L ≃* NativeSporadic.HS)
  obtain ⟨q⟩ := automizer_P0
  exact ⟨h₁, h₂, fun B _ hB _ => (h₃ B hB).map fun f => f.trans q⟩

end CFSG.RankThree.Asc83Table.HS
