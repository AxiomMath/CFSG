module

public import CFSG.Quasithin.EmptyFaithful.A38c5Main
public import CFSG.Quasithin.EmptyFaithful.A38c5FmGrp
public import CFSG.Quasithin.EmptyFaithful.A38c5FmBlk
public import CFSG.Quasithin.EmptyFaithful.A38c5FmAff
public import CFSG.Quasithin.EmptyFaithful.A38c5FmRank

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace CFSG.Quasithin.A38c5

theorem dsub_eq_D8 : B3.Dsub 8 = Fm.D8 := by
  unfold B3.Dsub B3.Am Fm.D8
  congr 1
  ext g
  simp only [B3.gensAm, List.mem_map, List.mem_range, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : i < 4 := by omega
    interval_cases i
    · left; decide
    · right; left; decide
    · right; right; left; decide
    · right; right; right; decide
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨3, by decide, by decide⟩

theorem finiteFactS8 : FiniteFactS8 := by
  intro T₁ hT₁ hD K hKA hKmax hKN
  rw [dsub_eq_D8] at hD ⊢
  have hA8ne : alternatingGroup (Fin 8) ≠ ⊥ := by
    intro h
    have hmem : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    rw [h, Subgroup.mem_bot] at hmem
    revert hmem; decide
  obtain ⟨-, hKne, hcoatom, -⟩ := Fm.coatom_of_isMaxParabolic2 hKmax
  have hK1 : K ≠ ⊥ := Fm.ne_bot_of_isMaxParabolic2 hA8ne hKmax
  have hM : K ⊔ T₁ ≠ ⊤ := Fm.alt8_sup_ne_top hKA hK1 hKne hKN
  have hMtrans : ∀ x y : Fin 8, ∃ g ∈ K ⊔ T₁, g x = y := fun x y => by
    obtain ⟨g, hg, hgx⟩ := Fm.isSylowTwoOf_transitive hT₁ x y
    exact ⟨g, Subgroup.mem_sup_right hg, hgx⟩
  have hMD : Fm.D8 ≤ K ⊔ T₁ := hD.trans le_sup_right
  rcases Fm.overgroup_classification (K ⊔ T₁) hM hMD hMtrans with hMu | ⟨B, hB, hBM⟩
  · exfalso
    have hKle : K ≤ alternatingGroup (Fin 8) ⊓ Fm.Smu := le_inf hKA (le_sup_left.trans hMu)
    obtain ⟨H, hHA, hHne, hlt⟩ := Fm.kmu_not_coatom
    have hKH : K ≤ H := hKle.trans hlt.le
    have hHK : H = K := hcoatom H hKH hHA hHne
    rw [hHK] at hlt
    exact absurd hKle (not_le_of_gt hlt)
  · have hT₁B : T₁ ≤ Fm.PStab B := le_sup_right.trans hBM
    have hKB : K ≤ alternatingGroup (Fin 8) ⊓ Fm.PStab B := le_inf hKA (le_sup_left.trans hBM)
    have hKeq : alternatingGroup (Fin 8) ⊓ Fm.PStab B = K :=
      hcoatom _ hKB inf_le_left (Fm.kB_ne_alt hB)
    rw [← hKeq]
    exact Fm.final_rank hB hT₁B hD

end CFSG.Quasithin.A38c5

namespace CFSG.Quasithin

theorem countStrongD_holds (hPre : Input32Preamble) : CountStrongD :=
  countStrongD_of_finite_fact A38c5.finiteFactS8 hPre

end CFSG.Quasithin
