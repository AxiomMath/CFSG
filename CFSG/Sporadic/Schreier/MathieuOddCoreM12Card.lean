module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier.Native

theorem m12_card_centralizerIn_involution
    {u : Equiv.Perm (Fin 12)}
    (hu : u ∈ NativeSporadic.M12) (ho : orderOf u = 2) :
    Nat.card (centralizerIn NativeSporadic.M12 u) = 192 ∨
      Nat.card (centralizerIn NativeSporadic.M12 u) = 240 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  obtain ⟨hok, hsz, -⟩ := m12_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m12_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m12_rep_data2
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  rw [m12InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn m12Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) (by norm_num) [m12Rep1, m12Rep2]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨by simpa using hr1, hro1⟩
      · exact ⟨by simpa using hr2, hro2⟩) 1000 hok
  rw [← m12Certificate_originalSubgroup] at hu ⊢
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  rw [centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hcard : Nat.card m12Certificate.originalSubgroup = 95040 := by
    rw [m12Certificate_originalSubgroup, m12_card]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    rw [centralizerIn_eq_of_le _ _ hK1 (hsize _ (by simp)) (by rw [hsz.1, hKc1, hcard]), hKc1]
  · right
    rw [centralizerIn_eq_of_le _ _ hK2 (hsize _ (by simp)) (by rw [hsz.2, hKc2, hcard]), hKc2]

theorem card_centralizer_involution_of_mulEquiv_M12
    {Y : Type*} [Group Y]
    (e : Y ≃* NativeSporadic.Carrier .M12) {u : Y} (ho : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set Y)) = 192 ∨
      Nat.card (Subgroup.centralizer ({u} : Set Y)) = 240 := by
  let e' : Y ≃* NativeSporadic.M12 := e
  let v : NativeSporadic.M12 := e' u
  have hv : orderOf ((v : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ho]
  have h1 : Nat.card (Subgroup.centralizer ({u} : Set Y)) =
      Nat.card (Subgroup.centralizer ({v} : Set NativeSporadic.M12)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨e' x, ?_⟩
        invFun := fun y => ⟨e'.symm y, ?_⟩
        left_inv := fun x => Subtype.ext (e'.symm_apply_apply x)
        right_inv := fun y => Subtype.ext (e'.apply_symm_apply y) }
    · have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, hx]
    · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e'.injective
      rw [map_mul, map_mul, e'.apply_symm_apply]
      exact hy
  have h2 : Nat.card (Subgroup.centralizer ({v} : Set NativeSporadic.M12)) =
      Nat.card (centralizerIn NativeSporadic.M12 (v : Equiv.Perm (Fin 12))) := by
    rw [← map_centralizer_subtype, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  rw [h1, h2]
  exact m12_card_centralizerIn_involution v.2 hv

end CFSG.Sporadic.Schreier
