
module

public import CFSG.Sporadic.Schreier.PairHeClassesBase
import all CFSG.Sporadic.Schreier.PairHeClassesBase

public import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Sporadic.Schreier.PairHeCheck
public import CFSG.Sporadic.Schreier.PairHeCountTwo
public import CFSG.Sporadic.Schreier.PairHeTriple1
public import CFSG.Sporadic.Schreier.PairCounts
public import CFSG.Sporadic.Schreier.PairClassCover
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.PairHeCheckInputs
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairHeCheck
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import Certificates.Certificate2225Base

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB

theorem hePartners_a0_le :
    hePartners (heGenPerm 0) ≤ 322560 := by
  rw [hePartners_rep repW_hewA (heGenPerm_mem_orig (by norm_num))]
  exact PairHe.partner_bound.1

theorem heT1_not_conj
    {d : Equiv.Perm (Fin 8330)} (_hd : d ∈ heChain.originalSubgroup) :
    heT1 ≠ d * heGenPerm 0 * d⁻¹ := by
  intro h
  have h1 := heFix_conj d (heGenPerm 0)
  rw [← h, ← countP_fix_of_rep rep_t1Arr, ← countP_fix_of_rep (rep_heGen (by norm_num)),
    PairHe.partner_bound.2.1, PairHe.partner_bound.2.2] at h1
  exact absurd h1 (by norm_num)

theorem heInvols_length :
    heInvols.length = 212415 := by
  have h1 := card_subtype_eq_countP heChain.originalSubgroup (enumeration heChain)
    (enumeration_nodup heChain heChain_valid.1) (mem_enumeration_iff heChain heChain_valid.1)
    (fun y => orderOf y = 2)
  rw [List.countP_eq_length_filter] at h1
  have h2 := he_card_order 2 (by norm_num)
  rw [PairHe.count_two, card_orderOf_coe] at h2
  rw [heInvols, ← h1]
  exact h2

theorem he_entries_perm :
    (heE1 ++ heE2).Perm heInvols := by
  obtain ⟨-, hok, hkeys, hsize⟩ := PairHe.classes
  have hclosed : ∀ c ∈ heChain.originalSubgroup, ∀ x ∈ heInvols, c * x * c⁻¹ ∈ heInvols := by
    intro c hc x hx
    obtain ⟨hxP, hxo⟩ := mem_heInvols.1 hx
    rw [mem_heInvols]
    exact ⟨mul_mem (mul_mem hc hxP) (inv_mem hc),
      (MulEquiv.orderOf_eq (MulAut.conj c) x).trans hxo⟩
  have h1 : ∀ c ∈ PairHe.cl, ∃ x ∈ heInvols, RepW 8330 c.1 x ∧ x ∈ heChain.originalSubgroup := by
    intro c hc
    rw [he_cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨heGenPerm 0, mem_heInvols.2 ⟨heGenPerm_mem_orig (by norm_num),
        orderOf_heGenPerm_zero⟩, repW_hewA, heGenPerm_mem_orig (by norm_num)⟩
    · exact ⟨heT1, mem_heInvols.2 ⟨heT1_mem, orderOf_heT1⟩, repW_hewT, heT1_mem⟩
  have h4 : (PairHe.cl.map fun c => c.2.1.size).sum = heInvols.length := by
    rw [hsize, heInvols_length]
    rfl
  have h := closureEntries_perm heChainArrays (chainCheckFacts heChain_check.1)
    heChain_valid.1 he_baseFaithful he_bs_lt he_gens heInvols hclosed PairHe.cl h1 hok hkeys h4
  rw [he_cl_eq] at h
  simpa only [heE1, heE2, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_append] using h

theorem he_entries_nodup :
    (heE1 ++ heE2).Nodup :=
  he_entries_perm.nodup_iff.2 heInvols_nodup

theorem he_invol_cover
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heChain.originalSubgroup)
    (hxo : orderOf x = 2) : x ∈ heE1 ∨ x ∈ heE2 :=
  List.mem_append.1 (he_entries_perm.mem_iff.2 (mem_heInvols.2 ⟨hx, hxo⟩))

theorem he_conj_a0_iff
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heChain.originalSubgroup) :
    (∃ d ∈ heChain.originalSubgroup, x = d * heGenPerm 0 * d⁻¹) ↔ x ∈ heE1 := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases he_invol_cover hx (by rw [he_conj_orderOf, orderOf_heGenPerm_zero]) with h | h
    · exact h
    · obtain ⟨d', hd', he⟩ := heE2_conj _ h
      exfalso
      refine heT1_not_conj (mul_mem (inv_mem hd') hd) ?_
      have : heT1 = d'⁻¹ * (d * heGenPerm 0 * d⁻¹) * d' := by rw [he]; group
      rw [this]
      group
  · exact heE1_conj x

theorem he_conj_t1_iff
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heChain.originalSubgroup) :
    (∃ d ∈ heChain.originalSubgroup, x = d * heT1 * d⁻¹) ↔ x ∈ heE2 := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases he_invol_cover hx (by rw [he_conj_orderOf, orderOf_heT1]) with h | h
    · obtain ⟨d', hd', he⟩ := heE1_conj _ h
      exfalso
      refine heT1_not_conj (mul_mem (inv_mem hd) hd') ?_
      have : heT1 = d⁻¹ * (d' * heGenPerm 0 * d'⁻¹) * d := by rw [← he]; group
      rw [this]
      group
    · exact h
  · exact heE2_conj x

end CFSG.Sporadic.Schreier
