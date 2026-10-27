module

public import CFSG.Quasithin.Vol2.F134LieL3Plane

public section

namespace CFSG.Quasithin.H13.NQCore.Psl3Even

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.SteinbergBS CFSG.Quasithin.F134.LieL3
open scoped LinearAlgebra.Projectivization MatrixGroups

variable {K : Type} [Field K]

theorem projPerm_fix_basePt_of_coprime [Finite K] {Q : Subgroup (projectiveSL 3 K)}
    (h1 : Nat.Coprime (Nat.card Q) (Nat.card K + 1))
    (h2 : Nat.Coprime (Nat.card Q) (Nat.card K ^ 2 + 1))
    (h3 : Nat.Coprime (Nat.card Q) (Nat.card K ^ 2 + Nat.card K + 1))
    (hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q, ∃ y ∈ Q, ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s) {x : projectiveSL 3 K} (hx : x ∈ Q) :
    projPerm 3 K x (basePt K) = basePt K := by
  classical
  set O : Set (ℙ K (Fin 3 → K)) := {p | ∃ y ∈ Q, projPerm 3 K y (basePt K) = p} with hOdef
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hOdvd : O.ncard ∣ Nat.card Q := by
    let _ : MulAction Q (ℙ K (Fin 3 → K)) :=
      MulAction.compHom _ ((projPerm 3 K).comp Q.subtype)
    have h1 : O = MulAction.orbit Q (basePt K) := by
      ext p
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
    rw [h1, ← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  have hbad : ∀ m : ℕ, O.ncard = m → Nat.Coprime (Nat.card Q) m → 2 ≤ m → False := by
    intro m hm hcop hm2
    rw [hm] at hOdvd
    have := Nat.Coprime.eq_one_of_dvd hcop.symm hOdvd
    omega
  have hbase : basePt K ∈ O := ⟨1, Q.one_mem, by rw [map_one, Equiv.Perm.one_apply]⟩
  have hinv : ∀ u ∈ projUnitriangular 3 K, ∀ p ∈ O, projPerm 3 K u p ∈ O := by
    rintro u hu _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', s, hs, hus⟩ := hQU u hu y hy
    refine ⟨y', hy', ?_⟩
    rw [← Equiv.Perm.mul_apply, ← map_mul, hus, map_mul, Equiv.Perm.mul_apply,
      projPerm_basePt_of_mem hs]
  set LP : Set (ℙ K (Fin 3 → K)) := Set.range linePt with hLP
  set OP : Set (ℙ K (Fin 3 → K)) := Set.range fun p : K × K => offPt p.1 p.2 with hOP
  have hLPcard : LP.ncard = Nat.card K := Set.ncard_range_of_injective linePt_injective
  have hOPcard : OP.ncard = Nat.card K ^ 2 := by
    rw [hOP, Set.ncard_range_of_injective offPt_injective, Nat.card_prod, sq]
  have hLPnot : basePt K ∉ LP := by
    rintro ⟨a, h⟩
    exact basePt_ne_linePt a h.symm
  have hOPnot : basePt K ∉ OP := by
    rintro ⟨⟨a, b⟩, h⟩
    exact basePt_ne_offPt a b h.symm
  have hdisj : Disjoint LP OP := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨⟨a', b'⟩, h⟩
    exact linePt_ne_offPt a a' b' h.symm
  have hLall : (∃ a, linePt a ∈ O) → LP ⊆ O := by
    rintro ⟨a, ha⟩ _ ⟨a', rfl⟩
    have := hinv _ (Subgroup.mem_map_of_mem _ (up3_mem_unitriangular 0 0 (a' - a))) _ ha
    rwa [projPerm_proj, up3_smul_linePt, add_sub_cancel] at this
  have hOall : (∃ a b, offPt a b ∈ O) → OP ⊆ O := by
    rintro ⟨a, b, hab⟩ _ ⟨⟨a', b'⟩, rfl⟩
    have := hinv _ (Subgroup.mem_map_of_mem _ (up3_mem_unitriangular (b' - b) (a' - a) 0)) _ hab
    rwa [projPerm_proj, up3_smul_offPt, add_sub_cancel, add_sub_cancel] at this
  have hcov : ∀ p, p = basePt K ∨ p ∈ LP ∨ p ∈ OP := fun p => by
    rcases point_cases p with h | ⟨a, h⟩ | ⟨a, b, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, h.symm⟩)
    · exact Or.inr (Or.inr ⟨(a, b), h.symm⟩)
  have hxO : projPerm 3 K x (basePt K) ∈ O := ⟨x, hx, rfl⟩
  by_cases hL : ∃ a, linePt a ∈ O <;> by_cases hOf : ∃ a b, offPt a b ∈ O
  ·
    have hO : O = insert (basePt K) (LP ∪ OP) :=
      le_antisymm (fun p _ => by
        rcases hcov p with rfl | h | h
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Or.inl h)
        · exact Set.mem_insert_of_mem _ (Or.inr h))
        (Set.insert_subset hbase (Set.union_subset (hLall hL) (hOall hOf)))
    refine (hbad (Nat.card K ^ 2 + Nat.card K + 1) ?_ h3 (by nlinarith)).elim
    rw [hO, Set.ncard_insert_of_notMem (by simp [hLPnot, hOPnot]), Set.ncard_union_eq hdisj,
      hLPcard, hOPcard]
    ring
  ·
    have hO : O = insert (basePt K) LP :=
      le_antisymm (fun p hp => by
        rcases hcov p with rfl | h | h
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ h
        · obtain ⟨⟨a, b⟩, rfl⟩ := h
          exact absurd ⟨a, b, hp⟩ hOf)
        (Set.insert_subset hbase (hLall hL))
    refine (hbad (Nat.card K + 1) ?_ h1 (by omega)).elim
    rw [hO, Set.ncard_insert_of_notMem hLPnot, hLPcard]
  ·
    have hO : O = insert (basePt K) OP :=
      le_antisymm (fun p hp => by
        rcases hcov p with rfl | h | h
        · exact Set.mem_insert _ _
        · obtain ⟨a, rfl⟩ := h
          exact absurd ⟨a, hp⟩ hL
        · exact Set.mem_insert_of_mem _ h)
        (Set.insert_subset hbase (hOall hOf))
    refine (hbad (Nat.card K ^ 2 + 1) ?_ h2 (by nlinarith)).elim
    rw [hO, Set.ncard_insert_of_notMem hOPnot, hOPcard]
  ·
    rcases hcov (projPerm 3 K x (basePt K)) with h | ⟨a, h⟩ | ⟨⟨a, b⟩, h⟩
    · exact h
    · exact absurd ⟨a, h ▸ hxO⟩ hL
    · exact absurd ⟨a, b, by rw [show offPt a b = projPerm 3 K x (basePt K) from h]; exact hxO⟩
        hOf

theorem mem_upperTriangular_of_coprime [Finite K] [CharP K 2] {Q : Subgroup (projectiveSL 3 K)}
    (h1 : Nat.Coprime (Nat.card Q) (Nat.card K + 1))
    (h2 : Nat.Coprime (Nat.card Q) (Nat.card K ^ 2 + 1))
    (h3 : Nat.Coprime (Nat.card Q) (Nat.card K ^ 2 + Nat.card K + 1))
    (hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q, ∃ y ∈ Q, ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s) {g : SL(3, K)} (hg : proj 3 K g ∈ Q) : g ∈ upperTriangular 3 K := by
  obtain ⟨h10, h20⟩ := entries_of_smul_basePt (projPerm_fix_basePt_of_coprime h1 h2 h3 hQU hg)
  set Q' := Q.map (gammaZero K).toMonoidHom with hQ'def
  have hγU := map_projUnitriangular_gammaZero (F := K)
  have hQ'card : Nat.card Q' = Nat.card Q := by
    rw [hQ'def, Subgroup.card_map_of_injective (gammaZero K).injective]
  have hQ'U : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q', ∃ y ∈ Q', ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s := by
    rintro u hu _ ⟨x, hx, rfl⟩
    rw [← hγU] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    obtain ⟨y, hy, s, hs, hus⟩ := hQU u₀ hu₀ x hx
    refine ⟨gammaZero K y, ⟨y, hy, rfl⟩, gammaZero K s, ?_, ?_⟩
    · rw [← hγU]
      exact ⟨s, hs, rfl⟩
    · change gammaZero K u₀ * gammaZero K x = gammaZero K y * gammaZero K s
      rw [← map_mul, hus, map_mul]
  obtain ⟨h, hh, e1, e2⟩ := gammaZero_proj_inv g
  have hhQ' : proj 3 K h ∈ Q' := by
    rw [← hh, map_inv]
    exact ⟨_, Q.inv_mem hg, rfl⟩
  obtain ⟨h10', h20'⟩ := entries_of_smul_basePt
    (projPerm_fix_basePt_of_coprime (Q := Q') (by rwa [hQ'card]) (by rwa [hQ'card])
      (by rwa [hQ'card]) hQ'U hhQ')
  rw [e1] at h10'
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end CFSG.Quasithin.H13.NQCore.Psl3Even
