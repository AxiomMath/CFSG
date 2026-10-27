module

public import CFSG.Quasithin.EmptyFaithful.A38c5FmGrp
public import CFSG.Quasithin.EmptyFaithful.A38c5FmBlk
public import CFSG.Quasithin.EmptyFaithful.A38c5FmAff

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A38c5.Fm

namespace CFSG.Quasithin.A38c6

theorem parabolic_classification {T K : Subgroup P8} (hT : IsSylowTwoOf T ⊤) (hD : D8 ≤ T)
    (hKA : K ≤ alternatingGroup (Fin 8)) (hKmax : IsMaxParabolic2 (alternatingGroup (Fin 8)) K)
    (hKN : T ≤ Subgroup.normalizer (K : Set P8)) :
    ∃ B ∈ blocks3, K = alternatingGroup (Fin 8) ⊓ PStab B ∧ T ≤ PStab B := by
  have hA8ne : alternatingGroup (Fin 8) ≠ ⊥ := by
    intro h
    have hmem : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    rw [h, Subgroup.mem_bot] at hmem
    revert hmem; decide
  obtain ⟨-, hKne, hcoatom, -⟩ := coatom_of_isMaxParabolic2 hKmax
  have hK1 : K ≠ ⊥ := ne_bot_of_isMaxParabolic2 hA8ne hKmax
  have hM : K ⊔ T ≠ ⊤ := alt8_sup_ne_top hKA hK1 hKne hKN
  have hMtrans : ∀ x y : Fin 8, ∃ g ∈ K ⊔ T, g x = y := fun x y => by
    obtain ⟨g, hg, hgx⟩ := isSylowTwoOf_transitive hT x y
    exact ⟨g, Subgroup.mem_sup_right hg, hgx⟩
  have hMD : D8 ≤ K ⊔ T := hD.trans le_sup_right
  rcases overgroup_classification (K ⊔ T) hM hMD hMtrans with hMu | ⟨B, hB, hBM⟩
  · exfalso
    have hKle : K ≤ alternatingGroup (Fin 8) ⊓ Smu := le_inf hKA (le_sup_left.trans hMu)
    obtain ⟨H, hHA, hHne, hlt⟩ := kmu_not_coatom
    have hKH : K ≤ H := hKle.trans hlt.le
    have hHK : H = K := hcoatom H hKH hHA hHne
    rw [hHK] at hlt
    exact absurd hKle (not_le_of_gt hlt)
  · have hT₁B : T ≤ PStab B := le_sup_right.trans hBM
    have hKB : K ≤ alternatingGroup (Fin 8) ⊓ PStab B := le_inf hKA (le_sup_left.trans hBM)
    have hKeq : alternatingGroup (Fin 8) ⊓ PStab B = K :=
      hcoatom _ hKB inf_le_left (kB_ne_alt hB)
    exact ⟨B, hB, hKeq.symm, hT₁B⟩

end CFSG.Quasithin.A38c6
