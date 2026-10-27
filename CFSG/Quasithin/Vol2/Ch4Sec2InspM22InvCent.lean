module

public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22SporMid

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Mathieu
open CFSG.Blueprint

theorem m23InvCent_centralizerIn_card
    {u : Equiv.Perm (Fin 23)}
    (hu : u ∈ NativeSporadic.M23) (ho : orderOf u = 2) :
    Nat.card (centralizerIn NativeSporadic.M23 u) = 2688 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn m23Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) (by norm_num) [m23Rep1]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 4000 hok
  rw [← m23Certificate_originalSubgroup] at hu ⊢
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  rw [centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hcard : Nat.card m23Certificate.originalSubgroup = 10200960 := by
    rw [m23Certificate_originalSubgroup, m23_card]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [centralizerIn_eq_of_le _ _ hK1 (hsize _ (by simp)) (by rw [hsz, hKc1, hcard]), hKc1]

theorem m23InvCent_centralizer_card
    {Y : Type*} [Group Y]
    (e : Y ≃* NativeSporadic.Carrier .M23) {u : Y} (ho : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set Y)) = 2688 := by
  let e' : Y ≃* NativeSporadic.M23 := e
  let v : NativeSporadic.M23 := e' u
  have hv : orderOf ((v : NativeSporadic.M23) : Equiv.Perm (Fin 23)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ho]
  have h1 : Nat.card (Subgroup.centralizer ({u} : Set Y)) =
      Nat.card (Subgroup.centralizer ({v} : Set NativeSporadic.M23)) := by
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
  have h2 : Nat.card (Subgroup.centralizer ({v} : Set NativeSporadic.M23)) =
      Nat.card (centralizerIn NativeSporadic.M23 (v : Equiv.Perm (Fin 23))) := by
    rw [← map_centralizer_subtype, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  rw [h1, h2]
  exact m23InvCent_centralizerIn_card v.2 hv

theorem m23InvCentOrd_holds :
    M23InvCentOrd := by
  intro t ht
  exact m23InvCent_centralizer_card (MulEquiv.refl _) ht

theorem m24InvCent_centralizerIn_card
    {u : Equiv.Perm (Fin 24)}
    (hu : u ∈ NativeSporadic.M24) (ho : orderOf u = 2) :
    Nat.card (centralizerIn NativeSporadic.M24 u) = 21504 ∨
      Nat.card (centralizerIn NativeSporadic.M24 u) = 7680 := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  obtain ⟨hok, hsz, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  rw [m24InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn m24Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) (by norm_num) [m24Rep1, m24Rep2]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨by simpa using hr1, hro1⟩
      · exact ⟨by simpa using hr2, hro2⟩) 40000 hok
  rw [← m24Certificate_originalSubgroup] at hu ⊢
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  rw [centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hcard : Nat.card m24Certificate.originalSubgroup = 244823040 := by
    rw [m24Certificate_originalSubgroup, m24_card]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · right
    rw [centralizerIn_eq_of_le _ _ hK1 (hsize _ (by simp)) (by rw [hsz.1, hKc1, hcard]), hKc1]
  · left
    rw [centralizerIn_eq_of_le _ _ hK2 (hsize _ (by simp)) (by rw [hsz.2, hKc2, hcard]), hKc2]

theorem m24InvCent_centralizer_card
    {Y : Type*} [Group Y]
    (e : Y ≃* NativeSporadic.Carrier .M24) {u : Y} (ho : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set Y)) = 21504 ∨
      Nat.card (Subgroup.centralizer ({u} : Set Y)) = 7680 := by
  let e' : Y ≃* NativeSporadic.M24 := e
  let v : NativeSporadic.M24 := e' u
  have hv : orderOf ((v : NativeSporadic.M24) : Equiv.Perm (Fin 24)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ho]
  have h1 : Nat.card (Subgroup.centralizer ({u} : Set Y)) =
      Nat.card (Subgroup.centralizer ({v} : Set NativeSporadic.M24)) := by
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
  have h2 : Nat.card (Subgroup.centralizer ({v} : Set NativeSporadic.M24)) =
      Nat.card (centralizerIn NativeSporadic.M24 (v : Equiv.Perm (Fin 24))) := by
    rw [← map_centralizer_subtype, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  rw [h1, h2]
  exact m24InvCent_centralizerIn_card v.2 hv

theorem m24InvCentOrd_holds :
    M24InvCentOrd := by
  intro t ht
  exact m24InvCent_centralizer_card (MulEquiv.refl _) ht

end CFSG.Quasithin.H13.Ch4

end
