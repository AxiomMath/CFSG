module

public import CFSG.RankThree.GF2n.Smith81.S81A5Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

theorem enum_lt_two_iff (I : Set.powersetCard (Fin 6) 3) (s : Fin 3) :
    (enum I s).val < 2 ↔ s.val < tau I := by
  have hI : I.val = Finset.univ.map (enum I).toEmbedding := by
    ext x
    rw [Finset.mem_map]
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I x).mpr hx
      exact ⟨a, Finset.mem_univ _, ha⟩
    · rintro ⟨a, -, ha⟩
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I x).mp ⟨a, ha⟩
  have htau : tau I = (Finset.univ.filter (fun s : Fin 3 => (enum I s).val < 2)).card := by
    rw [tau, hI, Finset.filter_map, Finset.card_map]
    rfl
  have h01 : (enum I 0).val < (enum I 1).val :=
    Fin.lt_def.mp ((enum I).strictMono (show (0 : Fin 3) < 1 by decide))
  have h12 : (enum I 1).val < (enum I 2).val :=
    Fin.lt_def.mp ((enum I).strictMono (show (1 : Fin 3) < 2 by decide))
  have e0 : (enum I 0).val < 2 ↔ 0 < tau I := by
    rw [htau, Finset.card_filter, Fin.sum_univ_three]
    split_ifs <;> omega
  have e1 : (enum I 1).val < 2 ↔ 1 < tau I := by
    rw [htau, Finset.card_filter, Fin.sum_univ_three]
    split_ifs <;> omega
  have e2 : (enum I 2).val < 2 ↔ 2 < tau I := by
    rw [htau, Finset.card_filter, Fin.sum_univ_three]
    split_ifs <;> omega
  fin_cases s
  · exact e0
  · exact e1
  · exact e2

variable (K)

@[expose] def patSet (t : ℕ) : Set (Cube K) :=
  {ξ | ∃ a : Fin 3 → Fin 6 → K, (∀ i : Fin 3, i.val < t → a i ∈ W2 K) ∧
    (∀ i : Fin 3, t ≤ i.val → a i ∈ W4 K) ∧ ξ = ιMulti K 3 a}

@[expose] def Vt (t : ℕ) : Submodule K (Cube K) := Submodule.span K (patSet K t)

abbrev Usp : Submodule K (Cube K) := Vt K 2

@[expose] def supp (t : ℕ) : Submodule K (Cube K) where
  carrier := {ξ | ∀ I, tau I ≠ t → coord K ξ I = 0}
  add_mem' := fun {a b} ha hb I hI => by
    rw [coord_add, ha I hI, hb I hI, add_zero]
  zero_mem' := fun I _ => coord_zero I
  smul_mem' := fun c x hx I hI => by
    rw [coord_smul, hx I hI, mul_zero]

variable {K}

theorem cubeBasis_apply (I : Set.powersetCard (Fin 6) 3) :
    cubeBasis K I = ιMulti K 3 (fun s => e K (enum I s)) := by
  unfold cubeBasis
  rw [exteriorPower.basis_apply]
  simp only [exteriorPower.ιMulti_family]
  congr 1
  funext s
  simp [Pi.basisFun_apply, e]

theorem cubeBasis_mem_Vt (I : Set.powersetCard (Fin 6) 3) : cubeBasis K I ∈ Vt K (tau I) := by
  apply Submodule.subset_span
  refine ⟨fun s => e K (enum I s), ?_, ?_, cubeBasis_apply I⟩
  · intro s hs
    exact e_mem_W2 ((enum_lt_two_iff I s).2 hs)
  · intro s hs
    apply e_mem_W4
    by_contra h
    exact absurd ((enum_lt_two_iff I s).1 (by omega)) (by omega)

theorem supp_le_Vt (t : ℕ) : supp K t ≤ Vt K t := by
  intro ξ hξ
  have h : ξ = Finsupp.linearCombination K (cubeBasis K) ((cubeBasis K).repr ξ) :=
    ((cubeBasis K).linearCombination_repr ξ).symm
  rw [h, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun I hI => Submodule.smul_mem _ _ ?_
  have hne : coord K ξ I ≠ 0 := by simpa [coord] using hI
  have htau : tau I = t := by
    by_contra hne'
    exact hne (hξ I hne')
  rw [← htau]
  exact cubeBasis_mem_Vt I

end CFSG.RankThree.GF2n.Smith81.A5Cube
