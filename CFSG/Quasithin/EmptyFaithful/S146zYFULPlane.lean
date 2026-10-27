module

public import CFSG.Quasithin.Vol2.F134LieL3Plane

public section

namespace CFSG.Quasithin.S146zY

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.SteinbergBS CFSG.Quasithin.F134.LieL3
open scoped LinearAlgebra.Projectivization MatrixGroups

variable {K : Type} [Field K]

theorem projPerm_fix_basePt_twentyFive [Finite K] {Q : Subgroup (projectiveSL 3 K)}
    (hQ : Nat.card Q ∣ 25) (hK5 : Nat.card K % 5 = 1)
    (hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q, ∃ y ∈ Q, ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s) {x : projectiveSL 3 K} (hx : x ∈ Q) :
    projPerm 3 K x (basePt K) = basePt K := by
  classical
  set O : Set (ℙ K (Fin 3 → K)) := {p | ∃ y ∈ Q, projPerm 3 K y (basePt K) = p} with hOdef
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq6 : 6 ≤ Nat.card K := by omega
  have hOdvd : O.ncard ∣ 25 := by
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
    exact (Subgroup.index_dvd_card _).trans hQ
  have hOle : O.ncard ≤ 25 := Nat.le_of_dvd (by norm_num) hOdvd
  have hbase : basePt K ∈ O := ⟨1, Q.one_mem, by rw [map_one, Equiv.Perm.one_apply]⟩
  have hinv : ∀ u ∈ projUnitriangular 3 K, ∀ p ∈ O, projPerm 3 K u p ∈ O := by
    rintro u hu _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', s, hs, hus⟩ := hQU u hu y hy
    refine ⟨y', hy', ?_⟩
    rw [← Equiv.Perm.mul_apply, ← map_mul, hus, map_mul, Equiv.Perm.mul_apply,
      projPerm_basePt_of_mem hs]
  have hoff : ∀ a b, offPt a b ∉ O := by
    intro a b hab
    have hall : ∀ a' b', offPt a' b' ∈ O := by
      intro a' b'
      have := hinv _ (Subgroup.mem_map_of_mem _ (up3_mem_unitriangular (b' - b) (a' - a) 0)) _ hab
      rwa [projPerm_proj, up3_smul_offPt, add_sub_cancel, add_sub_cancel] at this
    have hsub : insert (basePt K) (Set.range fun p : K × K => offPt p.1 p.2) ⊆ O := by
      rintro _ (rfl | ⟨⟨a', b'⟩, rfl⟩)
      · exact hbase
      · exact hall a' b'
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite O)
    rw [Set.ncard_insert_of_notMem (by rintro ⟨⟨a', b'⟩, h⟩; exact basePt_ne_offPt a' b' h.symm)
      (Set.toFinite _), Set.ncard_range_of_injective offPt_injective, Nat.card_prod] at hcard
    have : 6 * 6 ≤ Nat.card K * Nat.card K := Nat.mul_le_mul hq6 hq6
    omega
  have hline : ∀ a, linePt a ∉ O := by
    intro a ha
    have hall : ∀ a', linePt a' ∈ O := by
      intro a'
      have := hinv _ (Subgroup.mem_map_of_mem _ (up3_mem_unitriangular 0 0 (a' - a))) _ ha
      rwa [projPerm_proj, up3_smul_linePt, add_sub_cancel] at this
    have hO : O = insert (basePt K) (Set.range linePt) := by
      apply le_antisymm
      · intro p hp
        rcases point_cases p with rfl | ⟨a', rfl⟩ | ⟨a', b', rfl⟩
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ⟨a', rfl⟩
        · exact absurd hp (hoff a' b')
      · rintro _ (rfl | ⟨a', rfl⟩)
        · exact hbase
        · exact hall a'
    rw [hO, Set.ncard_insert_of_notMem (by rintro ⟨a', h⟩; exact basePt_ne_linePt a' h.symm)
      (Set.toFinite _), Set.ncard_range_of_injective linePt_injective] at hOdvd
    have hle : Nat.card K ≤ 24 := by
      have := Nat.le_of_dvd (by norm_num) hOdvd
      omega
    obtain ⟨q, hq⟩ : ∃ q, Nat.card K = q := ⟨_, rfl⟩
    rw [hq] at hOdvd hle hK5 hq6
    interval_cases q <;> omega
  have hxO : projPerm 3 K x (basePt K) ∈ O := ⟨x, hx, rfl⟩
  rcases point_cases (projPerm 3 K x (basePt K)) with h | ⟨a, h⟩ | ⟨a, b, h⟩
  · exact h
  · exact absurd (h ▸ hxO) (hline a)
  · exact absurd (h ▸ hxO) (hoff a b)

theorem mem_upperTriangular_of_le_twentyFive [Finite K] [CharP K 2]
    {Q : Subgroup (projectiveSL 3 K)} (hQ : Nat.card Q ∣ 25) (hK5 : Nat.card K % 5 = 1)
    (hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q, ∃ y ∈ Q, ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s) {g : SL(3, K)} (hg : proj 3 K g ∈ Q) : g ∈ upperTriangular 3 K := by
  obtain ⟨h10, h20⟩ := entries_of_smul_basePt (projPerm_fix_basePt_twentyFive hQ hK5 hQU hg)
  set Q' := Q.map (gammaZero K).toMonoidHom with hQ'def
  have hγU := map_projUnitriangular_gammaZero (F := K)
  have hQ'card : Nat.card Q' ∣ 25 := by
    rw [hQ'def, Subgroup.card_map_of_injective (gammaZero K).injective]
    exact hQ
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
  obtain ⟨h, hh, h1, h2⟩ := gammaZero_proj_inv g
  have hhQ' : proj 3 K h ∈ Q' := by
    rw [← hh, map_inv]
    exact ⟨_, Q.inv_mem hg, rfl⟩
  obtain ⟨h10', h20'⟩ :=
    entries_of_smul_basePt (projPerm_fix_basePt_twentyFive hQ'card hK5 hQ'U hhQ')
  rw [h1] at h10'
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end CFSG.Quasithin.S146zY
