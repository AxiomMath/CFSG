module

public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4Block
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public section

namespace CFSG.Quasithin.SzN2

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6

variable {K : Type} [Field K]

theorem sp4_le_borel_of_solvable [Finite K] (hK4 : ∃ s : Finset K, s.card = 4)
    {A : Subgroup (StatedSp 2 K)} (hVA : unipotent 2 K ≤ A) (hA : Group.IsSolvable ↥A) :
    A ≤ borelSubgroup 2 K := by
  obtain ⟨hle, -⟩ :=
    (symplectic_unitriangular_overgroup_subflag_containment (r := 2) (K := K)).1 A hVA
  have key : ∀ k : Fin 2, weylRep K k ∉ A := by
    intro k hk
    let j : Fin 2 := Fin.rev k
    have hHA : H2 K j ≤ A := by
      show spWeylGroup K (Fin.rev j) ≤ A
      rw [Fin.rev_rev]
      exact sup_le hVA ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.mpr hk))
    have hpc : perfectCore (Q2 K j) ≤ A :=
      calc perfectCore (Q2 K j) = ⁅perfectCore (Q2 K j), perfectCore (Q2 K j)⁆ :=
            (perfectCore_perfect _).symm
        _ ≤ ⁅Q2 K j, Q2 K j⁆ := Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)
        _ ≤ H2 K j := commutator_Q2_le j
        _ ≤ A := hHA
    have hs : Group.IsSolvable ↥(perfectCore (Q2 K j)) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hpc)
        (Subgroup.inclusion_injective hpc)
    exact not_isSolvable_sl2 hK4 (Group.isSolvable_of_surjective
      (f := CFSG.QuasithinUnique.Vol2Native.A312L.blkN j)
      (CFSG.QuasithinUnique.Vol2Native.A312L.blkN_surjective hK4 j))
  rw [borelSubgroup_eq_flagStabilizer]
  intro g hg
  rw [mem_flagStabilizer]
  intro x hx
  have hx' : x ∈ borelCuts K A := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa using (succ_mem_borelCuts_iff A (0 : Fin 2)).mpr (key 0)
    · simpa using (succ_mem_borelCuts_iff A (1 : Fin 2)).mpr (key 1)
  exact mem_flagStabilizer.mp (hle hg) x hx'

theorem isSylowTwoOf_unipotent [Finite K] [CharP K 2] :
    IsSylowTwoOf (unipotent 2 K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 2
  exact hP ▸ isSylowTwoOf_top_of_sylow P

theorem sp4_solvable_overgroup_le_normalizer [Finite K] [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) :
    ∀ Ū Y : Subgroup (StatedSp 2 K), IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Group.IsSolvable ↥Y →
      Y ≤ Subgroup.normalizer (Ū : Set (StatedSp 2 K)) :=
  fun _ _ hŪ hUY hY =>
    solvable_overgroup_le_normalizer_of_sylow isSylowTwoOf_unipotent
      (fun _ hY hs => by rw [normalizer_unipotent]; exact sp4_le_borel_of_solvable hK4 hY hs)
      hŪ hUY hY

theorem borelSubgroup_le_Q2' (j : Fin 2) : borelSubgroup 2 K ≤ Q2 K j := by
  have hj := j.isLt
  rw [Q2_eq]
  exact borelSubgroup_le_flagStabilizer (fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    omega)

theorem sp4_residualOvergroupsAt [Finite K] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    ResidualOvergroupsAt (StatedSp 2 K) (unipotent 2 K) (fun j : Fin 2 => Q2 K j) := by
  have hB := isSolvable_borelSubgroup (r := 2) (K := K) hK
  have h := residualOvergroupsAt_of_rank_two_data (π := MonoidHom.id (StatedSp 2 K))
    Function.surjective_id (V := unipotent 2 K) (B := borelSubgroup 2 K) (Q := Q2 K) (H := H2 K)
    (by rw [MonoidHom.ker_id]; exact bot_le) unipotent_le_borelSubgroup borelSubgroup_le_Q2'
    Q2_ne covBy_Q2 (fun A hVA hAt => contained_in_Q2 hVA hAt) hB commutator_Q2_le
    (fun j A hVA hAQ hAns => H2_le_of_nonsolvable hB j hVA hAQ hAns)
  simpa [Subgroup.map_id] using h

theorem sp4_rankTwoData [Finite K] [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    ∀ Ū : Subgroup (StatedSp 2 K), IsSylowTwoOf Ū ⊤ →
      ∃ P : Fin 2 → Subgroup (StatedSp 2 K), P 0 ≠ P 1 ∧
        (∀ A : Subgroup (StatedSp 2 K), Ū ≤ A → (A ⋖ ⊤ ↔ ∃ j, A = P j)) ∧
        ∀ j, Subgroup.normalizer (Ū : Set (StatedSp 2 K)) ≤ P j := by
  intro Ū hŪ
  obtain ⟨φ, hφ, hres⟩ := (sp4_residualOvergroupsAt hK).exists_iso_of_isSylow (MulEquiv.refl _)
    isSylowTwoOf_unipotent hŪ
  refine ⟨fun j => (Q2 K j).map φ.symm.toMonoidHom, hres.1, hres.2.2.1, fun j x hx => ?_⟩
  have h1 : (Subgroup.normalizer (Ū : Set (StatedSp 2 K))).map φ.toMonoidHom =
      Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) := by
    rw [Subgroup.map_equiv_normalizer_eq, hφ]
  have h2 : φ x ∈ Q2 K j := by
    have h3 : φ x ∈ (Subgroup.normalizer (Ū : Set (StatedSp 2 K))).map φ.toMonoidHom :=
      ⟨x, hx, rfl⟩
    rw [h1, normalizer_unipotent] at h3
    exact borelSubgroup_le_Q2' j h3
  exact ⟨φ x, h2, by simp⟩

end CFSG.Quasithin.SzN2
