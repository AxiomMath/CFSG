
module

public import CFSG.Sporadic.Co2Rank3.FactsBase

public import CFSG.Sporadic.Co2Rank3.Check

public noncomputable section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Sporadic.Co2Rank3.Native MulAction

theorem co2Rank3Facts : Co2Rank3Facts := by
  have h := co2Rank3_check
  simp only [co2Rank3TOK, Bool.and_eq_true, and_assoc, beq_iff_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩

theorem co2P0_eq_closure :
    co2P0 = Subgroup.closure {g | ∃ k < lev1Gens.size, co2Strong (level1Idx.getD k 0) = g} := by
  rw [← co2Q_levelSubgroup_one, co2Q_levelSubgroup_eq (by norm_num) co2Rank3Facts.lev1
    (by decide)]
  simp [lev1Gens]

theorem co2P01_eq_closure :
    co2P01 = Subgroup.closure {g | ∃ k < lev2Gens.size, co2Strong (level2Idx.getD k 0) = g} := by
  rw [← co2Q_levelSubgroup_two, co2Q_levelSubgroup_eq (by norm_num) co2Rank3Facts.lev2
    (by decide)]
  simp [lev2Gens]

theorem rep_stab
    {k : ℕ} (hk : k < stabGens.size) : Rep 2300 stabGens[k]! (co2StabGen k) := by
  have hk' : k < stabWords.length := by simpa [stabGens] using hk
  rw [stabGens, getElem!_toArray_map (d := []) hk']
  refine rep_wordA (fun h hh => rep_co2Strong hh) (fun h hh => rep_co2StrongInv hh) _ ?_
  have := List.all_eq_true.1 co2Rank3Facts.letters
  exact this _ (by rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk')

theorem co2StabGen_fix
    {k : ℕ} (hk : k < 3) :
    co2StabGen k 0 = 0 ∧ co2StabGen k 3 = 3 := by
  have hk' : k < stabGens.size := by rw [co2Rank3Facts.stab_size]; exact hk
  have h := Array.all_eq_true.1 co2Rank3Facts.fix k hk'
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← getElem!_pos stabGens k hk'] at h
  have hr := rep_stab hk'
  exact ⟨Fin.ext (by rw [← hr (0 : Fin 2300)]; exact h.1),
    Fin.ext (by rw [← hr (3 : Fin 2300)]; exact h.2)⟩

theorem co2N_le :

    co2N ≤ co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) (3 : Fin 2300) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [co2Rank3Facts.stab_size] at hk
  obtain ⟨h0, h3⟩ := co2StabGen_fix hk
  exact ⟨⟨co2StabGen_mem k, h0⟩, h3⟩

end CFSG.Sporadic.Co2Rank3
