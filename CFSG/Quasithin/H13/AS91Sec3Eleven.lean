module

public import CFSG.Quasithin.H13.AS91Sec3Orbit
public import Certificates.Certificate89015
public import CFSG.Quasithin.H13.AS91Sec3Bridge
public import CFSG.Quasithin.H13.AS91Sec3Trans

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

theorem isTrio_trioIn_of_mem {U : Finset (Finset (Fin 24))}
    {D : Finset (Finset (Finset (Fin 24)))} (hD : IsDiscOrOval U D) {k : Finset (Finset (Fin 24))}
    (hk : k ∈ D) : IsTrio k ∧ TrioIn k U := by
  unfold IsDiscOrOval at hD
  rcases hD with ⟨_, -, -, h⟩ | ⟨-, h⟩
  · exact ⟨((h k).1 hk).1, ((h k).1 hk).2.1⟩
  · exact ⟨(h k hk).1, (h k hk).2.1⟩

theorem coplanar_self_of_trioIn {S : Finset (Finset (Fin 24))} (hS : IsSextet S)
    {l : Finset (Finset (Fin 24))} (h : TrioIn l S) : Coplanar l l :=
  ⟨S, hS, h, h⟩

section Cert


theorem stmt311_one {p : ℕ} (hp : p < 3795) {Dl : List ℕ}
    (hDl : Dl ∈ Native.discsOvals (Native.trioSexts ()) 0) :
    ∃ d ∈ Dl, Native.coplanar (Native.trioSexts ()) p d = true ∨
      Native.zc (Native.trioList ())[p]! (Native.trioList ())[d]! = 1 := by
  have h : Native.stmt311Check () = true := Certificates.certificate89015
  simp only [Native.stmt311Check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range, Bool.or_eq_true, and_assoc] at h
  obtain ⟨-, h2, -⟩ := h
  obtain ⟨d, hd, hc⟩ := h2 p hp Dl hDl
  exact ⟨d, hd, hc⟩

theorem stmt311_two {q : ℕ} (hq : q < 1771) {Dl : List ℕ}
    (hDl : Dl ∈ Native.discsOvals (Native.trioSexts ()) 0) :
    ∃ d ∈ Dl, ∃ k ∈ Native.sextTrios (Native.trioSexts ()) q,
      k = d ∨ Native.coplanar (Native.trioSexts ()) d k = true := by
  have h : Native.stmt311Check () = true := Certificates.certificate89015
  simp only [Native.stmt311Check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range, Bool.or_eq_true, and_assoc] at h
  obtain ⟨-, -, h3⟩ := h
  obtain ⟨d, hd, k, hk, hc⟩ := h3 q hq Dl hDl
  exact ⟨d, hd, k, hk, hc⟩

theorem key_disc {D : Finset (Finset (Finset (Fin 24)))} {p₀ : ℕ} (hp₀ : p₀ < 3795)
    (hU : TrioIn (trioFin p₀) (sextFin 0))
    (hDk : ∀ k, k ∈ D ↔ IsTrio k ∧ TrioIn k (sextFin 0) ∧ k ≠ trioFin p₀ ∧
      ¬ Disjoint k (trioFin p₀)) :
    ∃ Dl ∈ Native.discsOvals (Native.trioSexts ()) 0, ∀ d ∈ Dl, d < 3795 ∧ trioFin d ∈ D := by
  have hp₀LU : p₀ ∈ Native.sextTrios (Native.trioSexts ()) 0 :=
    (sextTrios_iff (q := 0) (by norm_num)).2 ⟨hp₀, hU⟩
  refine ⟨(Native.sextTrios (Native.trioSexts ()) 0).filter
    (fun k => k != p₀ && Native.meets (Native.trioList ())[p₀]! (Native.trioList ())[k]!), ?_, ?_⟩
  · simp only [Native.discsOvals]
    exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨p₀, hp₀LU, rfl⟩))
  · intro d hd
    simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
    obtain ⟨hdLU, hdne, hmeets⟩ := hd
    obtain ⟨hd1, hdU⟩ := (sextTrios_iff (q := 0) (by norm_num)).1 hdLU
    exact ⟨hd1, (hDk _).2 ⟨isTrio_trioFin hd1, hdU, fun h => hdne (trioFin_injective hd1 hp₀ h),
      (meets_iff hp₀ hd1).1 hmeets⟩⟩

theorem key_oval {D : Finset (Finset (Finset (Fin 24)))} (hcard : D.card = 5)
    (hT : ∀ k ∈ D, IsTrio k ∧ TrioIn k (sextFin 0) ∧ ∀ k' ∈ D, k ≠ k' → Disjoint k k') :
    ∃ Dl ∈ Native.discsOvals (Native.trioSexts ()) 0, ∀ d ∈ Dl, d < 3795 ∧ trioFin d ∈ D := by
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = (Finset.range 3795).filter (fun p => trioFin p ∈ D) :=
    ⟨_, rfl⟩
  have hmemS : ∀ p, p ∈ S ↔ p < 3795 ∧ trioFin p ∈ D := by
    intro p
    rw [hS, Finset.mem_filter, Finset.mem_range]
  have himage : S.image trioFin = D := by
    ext k
    constructor
    · intro hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
      exact ((hmemS p).1 hp).2
    · intro hk
      obtain ⟨p, hp, hpk⟩ := (isTrio_iff k).1 (hT k hk).1
      exact Finset.mem_image.2 ⟨p, (hmemS p).2 ⟨hp, by rw [hpk]; exact hk⟩, hpk⟩
  have hinj : Set.InjOn trioFin (S : Set ℕ) := by
    intro p hp p' hp' h
    exact trioFin_injective ((hmemS p).1 (Finset.mem_coe.1 hp)).1
      ((hmemS p').1 (Finset.mem_coe.1 hp')).1 h
  have hScard : S.card = 5 := by
    rw [← Finset.card_image_of_injOn hinj, himage, hcard]
  have hpw : (Native.sextTrios (Native.trioSexts ()) 0).Pairwise (· < ·) :=
    pairwise_lt_filter_range _ _
  have hsub : ∀ x ∈ S, x ∈ Native.sextTrios (Native.trioSexts ()) 0 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := (hmemS x).1 hx
    exact (sextTrios_iff (q := 0) (by norm_num)).2 ⟨hx1, (hT _ hx2).2.1⟩
  have hsort := sort_mem_combs hpw hsub
  rw [hScard] at hsort
  have hpred : (S.sort.all fun d => S.sort.all fun k =>
      d == k || !(Native.meets (Native.trioList ())[d]! (Native.trioList ())[k]!)) = true := by
    simp only [List.all_eq_true]
    intro d hd k hk
    obtain ⟨hd1, hdD⟩ := (hmemS d).1 ((Finset.mem_sort _).1 hd)
    obtain ⟨hk1, hkD⟩ := (hmemS k).1 ((Finset.mem_sort _).1 hk)
    by_cases hdk : d = k
    · subst hdk
      simp
    · have hne : trioFin d ≠ trioFin k := fun h => hdk (trioFin_injective hd1 hk1 h)
      have hdisj : Disjoint (trioFin d) (trioFin k) := (hT _ hdD).2.2 _ hkD hne
      have hm : Native.meets (Native.trioList ())[d]! (Native.trioList ())[k]! = false := by
        cases hmeets : Native.meets (Native.trioList ())[d]! (Native.trioList ())[k]! with
        | false => rfl
        | true => exact absurd hdisj.symm ((meets_iff hd1 hk1).1 hmeets)
      simp [hdk, hm]
  refine ⟨S.sort, ?_, fun d hd => (hmemS d).1 ((Finset.mem_sort _).1 hd)⟩
  simp only [Native.discsOvals]
  exact List.mem_append.2 (Or.inr (List.mem_filter.2 ⟨hsort, hpred⟩))

theorem base_key {D : Finset (Finset (Finset (Fin 24)))} (hD : IsDiscOrOval (sextFin 0) D) :
    ∃ Dl ∈ Native.discsOvals (Native.trioSexts ()) 0, ∀ d ∈ Dl, d < 3795 ∧ trioFin d ∈ D := by
  unfold IsDiscOrOval at hD
  rcases hD with ⟨d₀, hd₀, hd₀U, hDk⟩ | ⟨hcard, hT⟩
  · obtain ⟨p₀, hp₀, rfl⟩ := (isTrio_iff d₀).1 hd₀
    exact key_disc hp₀ hd₀U hDk
  · exact key_oval hcard hT

theorem base_one {D : Finset (Finset (Finset (Fin 24)))} (hD : IsDiscOrOval (sextFin 0) D)
    {l : Finset (Finset (Fin 24))} (hl : IsTrio l) :
    ∃ d ∈ D, Coplanar l d ∨ Delta l d 3 := by
  obtain ⟨p, hp, rfl⟩ := (isTrio_iff l).1 hl
  obtain ⟨Dl, hDl, hsub⟩ := base_key hD
  obtain ⟨d, hd, hc⟩ := stmt311_one hp hDl
  obtain ⟨hd1, hd2⟩ := hsub d hd
  refine ⟨trioFin d, hd2, ?_⟩
  rcases hc with hc | hc
  · exact Or.inl ((coplanar_iff hp hd1).1 hc)
  · rw [zc_eq hp hd1] at hc
    exact Or.inr hc

theorem base_two {D : Finset (Finset (Finset (Fin 24)))} (hD : IsDiscOrOval (sextFin 0) D)
    {π : Finset (Finset (Fin 24))} (hπ : IsSextet π) :
    ∃ d ∈ D, ∃ k, IsTrio k ∧ TrioIn k π ∧ Coplanar d k := by
  obtain ⟨q, hq, rfl⟩ := (isSextet_iff π).1 hπ
  obtain ⟨Dl, hDl, hsub⟩ := base_key hD
  obtain ⟨d, hd, k, hk, hc⟩ := stmt311_two hq hDl
  obtain ⟨hd1, hd2⟩ := hsub d hd
  obtain ⟨hk1, hk2⟩ := (sextTrios_iff hq).1 hk
  rcases hc with hkd | hc
  · have hk2' : TrioIn (trioFin d) (sextFin q) := by
      rw [← hkd]
      exact hk2
    exact ⟨trioFin d, hd2, trioFin d, isTrio_trioFin hd1, hk2',
      coplanar_self_of_trioIn (isSextet_sextFin (q := 0) (by norm_num))
        (isTrio_trioIn_of_mem hD hd2).2⟩
  · exact ⟨trioFin d, hd2, trioFin k, isTrio_trioFin hk1, hk2, (coplanar_iff hd1 hk1).1 hc⟩

theorem exists_coplanar_or_delta_three {U l : Finset (Finset (Fin 24))}
    {D : Finset (Finset (Finset (Fin 24)))} (hU : IsSextet U) (hD : IsDiscOrOval U D)
    (hl : IsTrio l) : ∃ d ∈ D, Coplanar l d ∨ Delta l d 3 := by
  obtain ⟨g, hg, hgU⟩ := sextet_transitive hU
  have hD' : IsDiscOrOval (sextFin 0) (g • D) := by
    rw [← hgU]
    exact (isDiscOrOval_smul_iff hg).2 hD
  obtain ⟨d', hd', hc⟩ := base_one hD' (isTrio_smul hg hl)
  obtain ⟨e, he, rfl⟩ := Finset.mem_smul_finset.1 hd'
  refine ⟨e, he, ?_⟩
  rcases hc with hc | hc
  · exact Or.inl ((coplanar_smul_iff hg).1 hc)
  · exact Or.inr ((delta_smul_iff hg 3).1 hc)

theorem exists_trioIn_coplanar {U π : Finset (Finset (Fin 24))}
    {D : Finset (Finset (Finset (Fin 24)))} (hU : IsSextet U) (hD : IsDiscOrOval U D)
    (hπ : IsSextet π) : ∃ d ∈ D, ∃ k, IsTrio k ∧ TrioIn k π ∧ Coplanar d k := by
  obtain ⟨g, hg, hgU⟩ := sextet_transitive hU
  have hD' : IsDiscOrOval (sextFin 0) (g • D) := by
    rw [← hgU]
    exact (isDiscOrOval_smul_iff hg).2 hD
  obtain ⟨d', hd', k', hk', hk'π, hc⟩ := base_two hD' ((isSextet_smul_iff hg).2 hπ)
  obtain ⟨e, he, rfl⟩ := Finset.mem_smul_finset.1 hd'
  obtain ⟨k, rfl⟩ : ∃ k, k' = g • k := ⟨g⁻¹ • k', (smul_inv_smul g k').symm⟩
  exact ⟨e, he, k, (isTrio_smul_iff hg).1 hk', (trioIn_smul_iff g).1 hk'π,
    (coplanar_smul_iff hg).1 hc⟩

end Cert

end CFSG.Quasithin.H13.AS91.M24G
