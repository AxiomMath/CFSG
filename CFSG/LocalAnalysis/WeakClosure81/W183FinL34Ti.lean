module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinL34Loc
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34Cert

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.Open

private theorem w183finL34_exists_ne_one_r1 {A : Subgroup (Equiv.Perm (Fin 42))}
    (hcard : Nat.card A = 4) (hr : r₁ ∈ A) :
    ∃ y ∈ A, y ≠ 1 ∧ y ≠ r₁ := by
  by_contra hcon
  have hcon' : ∀ y ∈ A, y = 1 ∨ y = r₁ := by
    intro y hy
    by_cases h1 : y = 1
    · exact Or.inl h1
    · by_cases hr' : y = r₁
      · exact Or.inr hr'
      · exact absurd ⟨h1, hr'⟩ (fun h : y ≠ 1 ∧ y ≠ r₁ => hcon ⟨y, hy, h.1, h.2⟩)
  have hsub : (A : Set (Equiv.Perm (Fin 42))) ⊆ {1, r₁} := by
    intro x hx
    rcases hcon' x hx with h | h <;> simp [h]
  have h2 : (A : Set (Equiv.Perm (Fin 42))).ncard ≤
      ({1, r₁} : Set (Equiv.Perm (Fin 42))).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({1, r₁} : Set (Equiv.Perm (Fin 42))).ncard ≤ 2 := by
    calc _ ≤ ({r₁} : Set (Equiv.Perm (Fin 42))).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by simp
  have h4 : (A : Set (Equiv.Perm (Fin 42))).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  omega

private theorem w183finL34_eq_four {A : Subgroup (Equiv.Perm (Fin 42))}
    (hcard : Nat.card A = 4) (hr : r₁ ∈ A) {y : Equiv.Perm (Fin 42)} (hy : y ∈ A)
    (hy1 : y ≠ 1) (hyr : y ≠ r₁) :
    ∀ a ∈ A, a = 1 ∨ a = r₁ ∨ a = y ∨ a = r₁ * y := by
  have hsub : ({1, r₁, y, r₁ * y} : Set (Equiv.Perm (Fin 42))) ⊆ A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact A.one_mem
    · exact hr
    · exact hy
    · exact A.mul_mem hr hy
  have hne1 : r₁ * y ≠ 1 := fun h => hyr ((eq_inv_of_mul_eq_one_right h).trans
    (inv_eq_of_mul_eq_one_right r1_sq))
  have hne2 : r₁ * y ≠ r₁ := fun h => hy1 (by simpa using h)
  have hne3 : r₁ * y ≠ y := fun h => r1_ne_one (by simpa using h)
  have h4 : ({1, r₁, y, r₁ * y} : Set (Equiv.Perm (Fin 42))).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [r1_ne_one.symm, hy1.symm, hne1.symm])
        (Set.toFinite _),
      Set.ncard_insert_of_notMem (by simp [hyr.symm, hne2.symm]) (Set.toFinite _),
      Set.ncard_pair hne3.symm]
  have hA : (A : Set (Equiv.Perm (Fin 42))).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [h4, hA]) (Set.toFinite _)
  intro a ha
  have : a ∈ ({1, r₁, y, r₁ * y} : Set (Equiv.Perm (Fin 42))) := by rw [heq]; exact ha
  simpa using this

private theorem w183finL34_isElemAbelian_map_conj {A : Subgroup (Equiv.Perm (Fin 42))}
    (hel : IsElemAbelian 2 A) (y : Equiv.Perm (Fin 42)) :
    IsElemAbelian 2 (A.map (MulAut.conj y⁻¹).toMonoidHom) := by
  haveI : IsMulCommutative A := hel.1
  refine ⟨Subgroup.map_isMulCommutative A _, ?_⟩
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [← map_pow, hel.2 a ha, map_one]

theorem local_classification
    {A : Subgroup (Equiv.Perm (Fin 42))} (hAS : A ≤ S) (hcard : Nat.card A = 4)
    (hel : IsElemAbelian 2 A) (hr : r₁ ∈ A)
    (hN : ∀ u ∈ C₁, u ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 42)))) : A = Z0 := by
  have hrep1 : RepN r1N r₁ := by rw [r1_eq]; exact repN_wN r1W
  have hAZ : A ≤ Z0 := by
    obtain ⟨y, hy, hy1, hyr⟩ := w183finL34_exists_ne_one_r1 hcard hr
    have hfour := w183finL34_eq_four hcard hr hy hy1 hyr
    have hcomm : y * r₁ = r₁ * y := by
      have := hel.1.is_comm.comm ⟨y, hy⟩ ⟨r₁, hr⟩
      exact congrArg Subtype.val this
    have hyC : y ∈ C₁ :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hcomm, hAS hy⟩
    obtain ⟨w₁, hw₁, rfl⟩ := mem_c1 hyC
    have hy2 : wordPerm w₁ * wordPerm w₁ = 1 := by
      have := hel.2 _ hy
      simpa [pow_two] using this
    have hnorm : normE4 (wN w₁) = true := by
      unfold normE4
      have e1 : eqN (wN w₁) idN = false := by
        by_contra h
        have h' : eqN (wN w₁) idN = true := by simpa using h
        exact hy1 ((RepN.eq_iff (repN_wN w₁) RepN.one).1 h')
      have e2 : eqN (wN w₁) r1N = false := by
        by_contra h
        have h' : eqN (wN w₁) r1N = true := by simpa using h
        exact hyr ((RepN.eq_iff (repN_wN w₁) hrep1).1 h')
      have e3 : eqN (compN (wN w₁) (wN w₁)) idN = true :=
        (RepN.eq_iff ((repN_wN w₁).comp (repN_wN w₁)) RepN.one).2 hy2
      have e4 : commN (wN w₁) r1N = true :=
        (RepN.eq_iff ((repN_wN w₁).comp hrep1) (hrep1.comp (repN_wN w₁))).2 hcomm
      have e5 : c1N.all (fun u => [idN, r1N, wN w₁, compN r1N (wN w₁)].any
          (fun a => eqN (compN u (wN w₁)) (compN a u))) = true := by
        rw [List.all_eq_true]
        intro u hu
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
        have hnu := Subgroup.mem_normalizer_iff.1 (hN _ (wordPerm_mem_c1 hw)) (wordPerm w₁)
        have hconj : wordPerm w * wordPerm w₁ * (wordPerm w)⁻¹ ∈ A := hnu.1 hy
        have hmulinv : (wordPerm w * wordPerm w₁ * (wordPerm w)⁻¹) * wordPerm w =
            wordPerm w * wordPerm w₁ := by group
        rw [List.any_eq_true]
        rcases hfour _ hconj with h | h | h | h
        · refine ⟨idN, by simp, ?_⟩
          refine (RepN.eq_iff ((repN_wN w).comp (repN_wN w₁))
            (RepN.one.comp (repN_wN w))).2 ?_
          rw [← hmulinv, h]
        · refine ⟨r1N, by simp, ?_⟩
          refine (RepN.eq_iff ((repN_wN w).comp (repN_wN w₁))
            (hrep1.comp (repN_wN w))).2 ?_
          rw [← hmulinv, h]
        · refine ⟨wN w₁, by simp, ?_⟩
          refine (RepN.eq_iff ((repN_wN w).comp (repN_wN w₁))
            ((repN_wN w₁).comp (repN_wN w))).2 ?_
          rw [← hmulinv, h]
        · refine ⟨compN r1N (wN w₁), by simp, ?_⟩
          refine (RepN.eq_iff ((repN_wN w).comp (repN_wN w₁))
            ((hrep1.comp (repN_wN w₁)).comp (repN_wN w))).2 ?_
          rw [← hmulinv, h]
      rw [e1, e2, e3, e4, e5]
      rfl
    have hmemc1 : wN w₁ ∈ c1N := List.mem_map.2 ⟨w₁, hw₁, rfl⟩
    have hfilt : wN w₁ ∈ c1N.filter normE4 := List.mem_filter.2 ⟨hmemc1, hnorm⟩
    have hz := List.all_eq_true.1 normE4_z0 _ hfilt
    obtain ⟨zN, hzN, hzeq⟩ := List.any_eq_true.1 hz
    obtain ⟨zw, hzw, rfl⟩ := List.mem_map.1 hzN
    have hyz : wordPerm w₁ = wordPerm zw := (RepN.eq_iff (repN_wN w₁) (repN_wN zw)).1 hzeq
    have hmul : ∀ z ∈ z0W, ∃ z' ∈ z0W, r₁ * wordPerm z = wordPerm z' := by
      intro z hz
      have h := List.all_eq_true.1 z0_mul (wN r1W) (List.mem_map.2 ⟨r1W, by decide, rfl⟩)
      have h2 := List.all_eq_true.1 h (wN z) (List.mem_map.2 ⟨z, hz, rfl⟩)
      obtain ⟨cN, hcN, hceq⟩ := List.any_eq_true.1 h2
      obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hcN
      refine ⟨z', hz', ?_⟩
      rw [r1_eq]
      exact (RepN.eq_iff ((repN_wN r1W).comp (repN_wN z)) (repN_wN z')).1 hceq
    intro x hx
    rcases hfour x hx with h | h | h | h
    · exact mem_Z0_iff.2 ⟨[], by decide, by simp [h, wordPerm]⟩
    · exact mem_Z0_iff.2 ⟨r1W, by decide, by rw [h, r1_eq]⟩
    · exact mem_Z0_iff.2 ⟨zw, hzw, by rw [h, hyz]⟩
    · obtain ⟨z', hz', hz'eq⟩ := hmul zw hzw
      exact mem_Z0_iff.2 ⟨z', hz', by rw [h, hyz]; exact hz'eq.symm⟩
  refine Subgroup.eq_of_le_of_card_ge hAZ ?_
  rw [card_Z0, hcard]

@[expose] def nW : List ℕ := [1, 0, 1, 0, 2, 0, 0, 1, 0, 0, 2]

theorem n_normalizes_z0 :
    z0N.all (fun z => z0N.any (fun z' => eqN (compN (wN nW) z) (compN z' (wN nW))) &&
      (eqN z idN || !eqN (compN (wN nW) z) (compN z (wN nW)))) = true := by
  decide +kernel

private theorem w183finL34_fpf_z0W :
    (∀ w ∈ z0W, ∃ w' ∈ z0W, wordPerm nW * wordPerm w * (wordPerm nW)⁻¹ = wordPerm w') ∧
    ∀ w ∈ z0W, wordPerm w ≠ 1 → wordPerm nW * wordPerm w * (wordPerm nW)⁻¹ ≠ wordPerm w := by
  constructor
  · intro w hw
    have h := List.all_eq_true.1 n_normalizes_z0 (wN w) (List.mem_map.2 ⟨w, hw, rfl⟩)
    simp only [Bool.and_eq_true] at h
    obtain ⟨zN, hzN, hzeq⟩ := List.any_eq_true.1 h.1
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hzN
    refine ⟨w', hw', ?_⟩
    have hconj := (RepN.eq_iff ((repN_wN nW).comp (repN_wN w))
      ((repN_wN w').comp (repN_wN nW))).1 hzeq
    calc wordPerm nW * wordPerm w * (wordPerm nW)⁻¹
        = (wordPerm w' * wordPerm nW) * (wordPerm nW)⁻¹ := by rw [hconj]
      _ = wordPerm w' := by group
  · intro w hw hw1 hfix
    have h := List.all_eq_true.1 n_normalizes_z0 (wN w) (List.mem_map.2 ⟨w, hw, rfl⟩)
    simp only [Bool.and_eq_true] at h
    have h2 := h.2
    have hne : eqN (wN w) idN = false := by
      by_contra hc
      have hc' : eqN (wN w) idN = true := by simpa using hc
      exact hw1 ((RepN.eq_iff (repN_wN w) RepN.one).1 hc')
    rw [hne] at h2
    have h3 : eqN (compN (wN nW) (wN w)) (compN (wN w) (wN nW)) = true := by
      refine (RepN.eq_iff ((repN_wN nW).comp (repN_wN w))
        ((repN_wN w).comp (repN_wN nW))).2 ?_
      have := congrArg (· * wordPerm nW) hfix
      simpa [mul_assoc] using this
    simp [h3] at h2

theorem exists_fpf_Z0 :
    ∃ n ∈ S, (∀ x ∈ Z0, n * x * n⁻¹ ∈ Z0) ∧ ∀ x ∈ Z0, x ≠ 1 → n * x * n⁻¹ ≠ x := by
  refine ⟨wordPerm nW, wordPerm_mem nW, ?_, ?_⟩
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := mem_Z0_iff.1 hx
    obtain ⟨w', hw', hw'eq⟩ := w183finL34_fpf_z0W.1 w hw
    exact mem_Z0_iff.2 ⟨w', hw', hw'eq.symm⟩
  · intro x hx hx1 hfix
    obtain ⟨w, hw, rfl⟩ := mem_Z0_iff.1 hx
    exact w183finL34_fpf_z0W.2 w hw hx1 hfix

theorem exists_conj_Z0
    {A : Subgroup (Equiv.Perm (Fin 42))} (hAS : A ≤ S) (hcard : Nat.card A = 4)
    (hel : IsElemAbelian 2 A)
    (hTI : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ S, g * t = t * g →
      g ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 42)))) :
    ∃ k ∈ S, A.map (MulAut.conj k⁻¹).toMonoidHom = Z0 := by
  have hne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  haveI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hne
  obtain ⟨t, ht, ht1⟩ := Subgroup.exists_ne_one_of_nontrivial A
  have ht2 : t * t = 1 := by
    have := hel.2 t ht
    simpa [pow_two] using this
  have hS : r₁⁻¹ * t ∈ S := S.mul_mem (S.inv_mem r₁_mem_S) (hAS ht)
  obtain ⟨y, hyS, hyeq⟩ :=
    CFSG.ComponentClassification.CatFactsL4U4.conj_of_mul_mem_S r₁_mem_R (S_le_R (hAS ht))
      r1_sq ht2 r1_ne_one ht1 hS
  have hr1_eq : y⁻¹ * t * y = r₁ := by
    rw [← hyeq]; group
  set A' : Subgroup (Equiv.Perm (Fin 42)) := A.map (MulAut.conj y⁻¹).toMonoidHom with hA'def
  have hr1A' : r₁ ∈ A' := by
    rw [hA'def]
    refine Subgroup.mem_map.2 ⟨t, ht, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simpa using hr1_eq
  have hA'S : A' ≤ S := by
    rw [hA'def]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_mem_S (R.inv_mem (S_le_R hyS)) (hAS ha)
  have hA'card : Nat.card A' = 4 := by
    rw [hA'def, Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective, hcard]
  have hA'el : IsElemAbelian 2 A' := by
    rw [hA'def]
    exact w183finL34_isElemAbelian_map_conj hel y
  have hN' : ∀ u ∈ C₁, u ∈ Subgroup.normalizer (A' : Set (Equiv.Perm (Fin 42))) := by
    have hfwd : ∀ u ∈ C₁, ∀ x ∈ A', u * x * u⁻¹ ∈ A' := by
      intro u hu x hx
      rw [hA'def] at hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      have huS : u ∈ S := (Subgroup.mem_inf.1 hu).2
      have hucomm : u * r₁ = r₁ * u :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hu).1
      set g : Equiv.Perm (Fin 42) := y * u * y⁻¹ with hg
      have hgS : g ∈ S := by
        rw [hg]
        exact S.mul_mem (S.mul_mem hyS huS) (S.inv_mem hyS)
      have hgt : g * t = t * g := by
        rw [hg, ← hyeq]
        calc (y * u * y⁻¹) * (y * r₁ * y⁻¹) = y * (u * r₁) * y⁻¹ := by group
          _ = y * (r₁ * u) * y⁻¹ := by rw [hucomm]
          _ = (y * r₁ * y⁻¹) * (y * u * y⁻¹) := by group
      have hgN : g ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 42))) :=
        hTI t ht ht1 g hgS hgt
      have hga : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hgN a).1 ha
      rw [hA'def]
      refine Subgroup.mem_map.2 ⟨g * a * g⁻¹, hga, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hg]
      group
    intro u hu
    refine Subgroup.mem_normalizer_iff.2 (fun x => ⟨hfwd u hu x, ?_⟩)
    intro hx
    have := hfwd u⁻¹ (C₁.inv_mem hu) (u * x * u⁻¹) hx
    have hxx : u⁻¹ * (u * x * u⁻¹) * u = x := by group
    rw [inv_inv, hxx] at this
    exact this
  exact ⟨y, hyS, local_classification hA'S hA'card hA'el hr1A' hN'⟩

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end
