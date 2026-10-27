
module

public import CFSG.Quasithin.Recognition.L34AmalgamDataBase

public import CFSG.Quasithin.Recognition.M22WittData
public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public import CFSG.Quasithin.Recognition.L34AmalgamDataInputs
public import Certificates.Certificate7036

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.Sporadic.Mathieu

theorem gen_B_facts :
    ∀ j : Fin 5, j.val < 3 → (gen j : Equiv.Perm (Fin 22)) 0 = 0 ∧
    (gen j : Equiv.Perm (Fin 22)) 1 = 1 ∧
    ∀ p ∈ m22HexadL, (gen j : Equiv.Perm (Fin 22)) p ∈ m22HexadL :=
  Certificates.certificate7036.1

theorem gen_t_facts :
    (bT1 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (bT1 : Equiv.Perm (Fin 22)) 1 = 1 ∧
    ¬ (∀ p ∈ m22HexadL, (bT1 : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧ bT1 * bT1 = 1 ∧
    (bT2 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (bT2 : Equiv.Perm (Fin 22)) 1 ≠ 1 ∧
    (∀ p ∈ m22HexadL, (bT2 : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧ bT2 * bT2 = 1 :=
  Certificates.certificate7036.2.1

theorem evalW_amalRels : ∀ w ∈ amalRels, evalW gen w = 1 :=
  Certificates.certificate7036.2.2.1

theorem evalW_extra_good :
    ∀ i : Fin 12, IsGood i → evalW gen (extra i 3) = 1 :=
  Certificates.certificate7036.2.2.2

theorem bT1_mem_two : bT1 ∈ m22TwoStab := by
  have h0 : (bT1 : Equiv.Perm (Fin 22)) 0 = 0 := gen_t_facts.1
  have h1 : (bT1 : Equiv.Perm (Fin 22)) 1 = 1 := gen_t_facts.2.1
  rw [← smul_m22_def] at h0 h1
  exact Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr h0,
    MulAction.mem_stabilizer_iff.mpr h1⟩

theorem bT2_mem_ptHex : bT2 ∈ m22PtHexStab :=
  M22Witt.mem_m22PtHexStab_iff.mpr ⟨gen_t_facts.2.2.2.2.1, gen_t_facts.2.2.2.2.2.2.1⟩

theorem gen_mem_two (j : Fin 5) (hj : j ≠ 4) :
    gen j ∈ m22TwoStab := by
  rcases Nat.lt_or_ge j.val 3 with h | h
  · obtain ⟨h0, h1, -⟩ := gen_B_facts j h
    rw [← smul_m22_def] at h0 h1
    exact Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr h0,
      MulAction.mem_stabilizer_iff.mpr h1⟩
  · have hj3 : j = 3 := by
      have := j.isLt
      have : j.val ≠ 4 := fun e => hj (Fin.ext e)
      exact Fin.ext (by omega)
    rw [hj3, gen_three]
    exact bT1_mem_two

theorem gen_mem_ptHex (j : Fin 5) (hj : j ≠ 3) :
    gen j ∈ m22PtHexStab := by
  rcases Nat.lt_or_ge j.val 3 with h | h
  · obtain ⟨h0, -, hh⟩ := gen_B_facts j h
    exact M22Witt.mem_m22PtHexStab_iff.mpr ⟨h0, hh⟩
  · have hj4 : j = 4 := by
      have := j.isLt
      have : j.val ≠ 3 := fun e => hj (Fin.ext e)
      exact Fin.ext (by omega)
    rw [hj4, gen_four]
    exact bT2_mem_ptHex

theorem bT1_not_mem : bT1 ∉ m22PtHexStab := fun h =>
  gen_t_facts.2.2.1 (M22Witt.mem_m22PtHexStab_iff.mp h).2

theorem bT2_not_mem : bT2 ∉ m22TwoStab := by
  intro h
  have h1 : bT2 • (1 : Fin 22) = 1 := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp h).2
  rw [smul_m22_def] at h1
  exact gen_t_facts.2.2.2.2.2.1 h1

end CFSG.Quasithin.L34Amalgam
