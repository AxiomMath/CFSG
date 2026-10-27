module

public import CFSG.Quasithin.Vol2.KGFactMinParBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even8

public section

namespace CFSG.Quasithin.H13.KGMinPar

open Equiv CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.L246C127.Even8

variable {X : Type} [Group X]

@[expose] def a8Mem (j : ℕ) : List (Perm (Fin 8)) := (tGens :: lat).getD j []

@[expose] def a8Ord (j : ℕ) : ℕ := [64, 192, 192, 192, 576, 1344, 1344, 20160].getD j 0

@[expose] def a8Y (j : ℕ) : Subgroup ↥(alternatingGroup (Fin 8)) :=
  (Subgroup.closure {g | g ∈ a8Mem j}).subgroupOf (alternatingGroup (Fin 8))

@[expose] def a8Ext (j : ℕ) : Perm (Fin 8) :=
  [permOf 8 [[2, 4], [3, 5]], permOf 8 [[1, 2], [5, 6]], permOf 8 [[1, 2], [5, 7]],
    permOf 8 [[5, 6, 7]], permOf 8 [[1, 2, 4], [3, 6, 5]], permOf 8 [[1, 2, 4], [3, 7, 5]],
    permOf 8 [[3, 4], [6, 7]]].getD j 1

theorem a8Mem_succ {j : ℕ} (hj : j < 7) : a8Mem (j + 1) = tGens ++ [a8Ext j] := by
  interval_cases j <;> rfl

theorem a8Ext_sign {j : ℕ} (hj : j < 7) : Perm.sign (a8Ext j) = 1 := by
  interval_cases j <;> simp [a8Ext, permOf, List.formPerm_cons_cons, Perm.sign_swap']

theorem tGens_le_a8Mem {j : ℕ} (hj : j < 8) : ∀ g ∈ tGens, g ∈ a8Mem j := by
  intro g hg
  rcases j with _ | j
  · exact hg
  · rw [a8Mem_succ (by omega)]
    exact List.mem_append_left _ hg

theorem a8Mem_le {j : ℕ} (hj : j < 8) :
    Subgroup.closure {g | g ∈ a8Mem j} ≤ alternatingGroup (Fin 8) := by
  rw [Subgroup.closure_le]
  intro g hg
  rcases j with _ | j
  · exact D_le (Subgroup.subset_closure hg)
  · rw [Set.mem_ofPred_eq, a8Mem_succ (by omega)] at hg
    rcases List.mem_append.mp hg with h | h
    · exact D_le (Subgroup.subset_closure h)
    · rw [List.mem_singleton.mp h]
      exact Perm.mem_alternatingGroup.mpr (a8Ext_sign (by omega))

theorem D_le_a8Mem {j : ℕ} (hj : j < 8) : D ≤ Subgroup.closure {g | g ∈ a8Mem j} :=
  Subgroup.closure_mono fun g hg => tGens_le_a8Mem hj g hg

theorem card_a8Y {j : ℕ} (hj : j < 8) :
    Nat.card (a8Y j) = a8Ord j := by
  rw [a8Y, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (a8Mem_le hj)).toEquiv]
  have h := cert.card_member_idx (rawIsEnc 8) (cert.closedOK_of_check cert_check)
    (cert.sizesOK_of_check cert_check) j hj
  rw [show a8Mem j = (cert.tGens :: cert.lat)[j]'hj from List.getD_eq_getElem _ _ hj]
  exact h

theorem a8_complete :
    ∀ Z : Subgroup ↥(alternatingGroup (Fin 8)), D.subgroupOf (alternatingGroup (Fin 8)) ≤ Z →
      ∃ j ≤ 8, Z = memberOrTop 8 a8Y j := by
  intro Z hZ
  let Z' : Subgroup (Perm (Fin 8)) := Z.map (alternatingGroup (Fin 8)).subtype
  have hDZ : Subgroup.closure {g | g ∈ cert.tGens} ≤ Z' := fun t ht =>
    ⟨⟨t, D_le ht⟩, hZ (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hZM : Z' ≤ Subgroup.closure {g | g ∈ cert.mGens} := by
    show Z' ≤ Subgroup.closure {g | g ∈ mGens}
    rw [closure_mGens]
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  obtain ⟨L, hL, hZL⟩ := cert.overgroups (rawIsEnc 8) cert_check Z' hDZ hZM
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hL
  have hj8 : j < 8 := hj
  refine ⟨j, hj8.le, ?_⟩
  have hZZ : Z'.subgroupOf (alternatingGroup (Fin 8)) = Z :=
    Subgroup.comap_map_eq_self_of_injective (alternatingGroup (Fin 8)).subtype_injective Z
  rw [← hZZ, hZL]
  simp only [memberOrTop, hj8, ite_true, a8Y]
  rw [show a8Mem j = (cert.tGens :: cert.lat)[j]'hj from List.getD_eq_getElem _ _ hj]

theorem a8_sylow :
    IsSylowTwoOf (D.subgroupOf (alternatingGroup (Fin 8))) ⊤ :=
  isSylow_D

theorem a8Ext_zero_mem_five : a8Ext 0 ∈ Subgroup.closure {g | g ∈ a8Mem 5} := by
  have e : a8Ext 0 =
      (permOf 8 [[0, 7, 2, 5], [1, 6, 3, 4]])⁻¹ * (permOf 8 [[1, 2, 4], [3, 6, 5]])⁻¹ *
      (permOf 8 [[0, 4, 1, 5], [2, 7, 3, 6]])⁻¹ * (permOf 8 [[1, 2, 4], [3, 6, 5]]) *
      (permOf 8 [[0, 7, 2, 5], [1, 6, 3, 4]])⁻¹ * (permOf 8 [[1, 2, 4], [3, 6, 5]]) *
      (permOf 8 [[4, 7], [5, 6]]) * (permOf 8 [[1, 2, 4], [3, 6, 5]])⁻¹ := by
    decide +kernel
  have h : ∀ g ∈ [permOf 8 [[0, 4, 1, 5], [2, 7, 3, 6]], permOf 8 [[4, 7], [5, 6]],
      permOf 8 [[0, 7, 2, 5], [1, 6, 3, 4]], permOf 8 [[1, 2, 4], [3, 6, 5]]],
      g ∈ Subgroup.closure {g | g ∈ a8Mem 5} := fun g hg => Subgroup.subset_closure hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h2)
    (Subgroup.inv_mem _ h3)) (Subgroup.inv_mem _ h0)) h3) (Subgroup.inv_mem _ h2)) h3) h1)
    (Subgroup.inv_mem _ h3)

theorem a8Ext_zero_mem_six : a8Ext 0 ∈ Subgroup.closure {g | g ∈ a8Mem 6} := by
  have e : a8Ext 0 =
      (permOf 8 [[4, 7], [5, 6]])⁻¹ * (permOf 8 [[1, 2, 4], [3, 7, 5]])⁻¹ *
      (permOf 8 [[4, 7], [5, 6]]) * (permOf 8 [[0, 4, 1, 5], [2, 7, 3, 6]]) *
      (permOf 8 [[1, 2, 4], [3, 7, 5]]) * (permOf 8 [[0, 7, 2, 5], [1, 6, 3, 4]]) := by
    decide +kernel
  have h : ∀ g ∈ [permOf 8 [[0, 4, 1, 5], [2, 7, 3, 6]], permOf 8 [[4, 7], [5, 6]],
      permOf 8 [[0, 7, 2, 5], [1, 6, 3, 4]], permOf 8 [[1, 2, 4], [3, 7, 5]]],
      g ∈ Subgroup.closure {g | g ∈ a8Mem 6} := fun g hg => Subgroup.subset_closure hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) (Subgroup.inv_mem _ h3)) h1) h0) h3) h2

theorem a8_one_le {k : ℕ} (hk : k = 5 ∨ k = 6) :
    Subgroup.closure {g | g ∈ a8Mem 1} ≤ Subgroup.closure {g | g ∈ a8Mem k} := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [Set.mem_ofPred_eq, a8Mem_succ (by norm_num)] at hg
  rcases List.mem_append.mp hg with h | h
  · exact Subgroup.subset_closure (tGens_le_a8Mem (by omega) g h)
  · rw [List.mem_singleton.mp h]
    rcases hk with rfl | rfl
    · exact a8Ext_zero_mem_five
    · exact a8Ext_zero_mem_six

@[expose] def bisect : Subgroup (Perm (Fin 8)) where
  carrier := {g | (∀ i : Fin 8, (g i).val < 4 ↔ i.val < 4) ∨
    (∀ i : Fin 8, (g i).val < 4 ↔ ¬ i.val < 4)}
  mul_mem' := by
    rintro g h (hg | hg) (hh | hh)
    · exact Or.inl fun i => by rw [Perm.mul_apply, hg, hh]
    · exact Or.inr fun i => by rw [Perm.mul_apply, hg, hh]
    · exact Or.inr fun i => by rw [Perm.mul_apply, hg, hh]
    · exact Or.inl fun i => by rw [Perm.mul_apply, hg, hh, not_not]
  one_mem' := Or.inl fun _ => Iff.rfl
  inv_mem' := by
    rintro g (hg | hg)
    · refine Or.inl fun i => ?_
      have := hg (g⁻¹ i)
      rw [Perm.inv_def, Equiv.apply_symm_apply] at this
      rw [Perm.inv_def]
      exact this.symm
    · refine Or.inr fun i => ?_
      have := hg (g⁻¹ i)
      rw [Perm.inv_def, Equiv.apply_symm_apply] at this
      rw [Perm.inv_def]
      tauto

theorem mem_bisect_iff {g : Perm (Fin 8)} : g ∈ bisect ↔
    (∀ i : Fin 8, (g i).val < 4 ↔ i.val < 4) ∨ (∀ i : Fin 8, (g i).val < 4 ↔ ¬ i.val < 4) :=
  Iff.rfl

theorem a8_four_le_bisect : Subgroup.closure {g | g ∈ a8Mem 4} ≤ bisect := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [Set.mem_ofPred_eq, a8Mem_succ (by norm_num)] at hg
  have h0 : permOf 8 [[0, 4, 1, 5], [2, 7, 3, 6]] ∈ bisect := by
    rw [mem_bisect_iff]; decide +kernel
  have h1 : permOf 8 [[4, 7], [5, 6]] ∈ bisect := by rw [mem_bisect_iff]; decide +kernel
  have h2 : permOf 8 [[0, 7, 2, 5], [1, 6, 3, 4]] ∈ bisect := by
    rw [mem_bisect_iff]; decide +kernel
  have h3 : a8Ext 3 ∈ bisect := by rw [mem_bisect_iff]; decide +kernel
  simp only [tGens, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem a8_one_not_le_four :
    ¬ Subgroup.closure {g | g ∈ a8Mem 1} ≤ Subgroup.closure {g | g ∈ a8Mem 4} := by
  intro h
  have h1 : a8Ext 0 ∈ Subgroup.closure {g | g ∈ a8Mem 1} := by
    apply Subgroup.subset_closure
    rw [Set.mem_ofPred_eq, a8Mem_succ (by norm_num)]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have h2 : a8Ext 0 ∉ bisect := by rw [mem_bisect_iff]; decide +kernel
  exact h2 (a8_four_le_bisect (h h1))

theorem l42_key [Finite X] {L T : Subgroup X}
    (hT : IsSylowTwoOf T L) (e : ↥L ≃* ↥(alternatingGroup (Fin 8))) : Key T L := by
  obtain ⟨φ, hφ, hlat⟩ := exists_lat (Y := a8Y) a8_sylow
    (fun j hj => Subgroup.comap_mono (D_le_a8Mem hj)) a8_complete hT e
  set Z : ℕ → Subgroup X := fun j => (a8Y j).map φ with hZ
  have hcard : ∀ j < 8, Nat.card (Z j) = a8Ord j := fun j hj =>
    (Subgroup.card_map_of_injective hφ).trans (card_a8Y hj)
  have hL : Nat.card L = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_alt]
  have hmono : ∀ {i k : ℕ}, i < 8 → k < 8 →
      (Subgroup.closure {g | g ∈ a8Mem i} ≤ Subgroup.closure {g | g ∈ a8Mem k} ↔ Z i ≤ Z k) := by
    intro i k hi hk
    rw [Subgroup.map_le_map_iff_of_injective hφ]
    constructor
    · exact fun h => Subgroup.comap_mono h
    · intro h x hx
      have := h (Subgroup.mem_subgroupOf.mpr (show ((⟨x, a8Mem_le hi hx⟩ :
        ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) ∈ _ from hx))
      exact Subgroup.mem_subgroupOf.mp this
  have hZ7 : Z 7 = L := Subgroup.eq_of_le_of_card_ge (hlat.le_L 7 (by norm_num))
    (by rw [hL, hcard 7 (by norm_num)]; decide)
  have hlt : ∀ m < 7, a8Ord m < 20160 := by decide
  have hnotL : ∀ m < 7, ¬ L ≤ Z m := fun m hm hLm => by
    have h1 := Subgroup.card_le_of_le hLm
    rw [hL, hcard m (by omega)] at h1
    exact absurd (hlt m hm) (not_lt_of_ge h1)
  have hcaseL : ∃ o₁ o₂ : ℕ, L ⊓ canon T L o₁ ≠ L ∧ L ⊓ canon T L o₂ ≠ L ∧
      (L ⊓ canon T L o₁) ⊔ (L ⊓ canon T L o₂) = L := by
    refine ⟨576, 1344, hlat.case le_rfl (a := 4) (b := 1) (m₁ := 4) (m₂ := 5)
      (by norm_num) (by norm_num) (by norm_num) (by rw [hL]; norm_num) (by rw [hL]; norm_num)
      (hlat.le_L 4 (by norm_num)) (hlat.le_L 1 (by norm_num)) ?_ ?_ (hcard 4 (by norm_num))
      (hcard 5 (by norm_num)) (hnotL 4 (by norm_num)) (hnotL 5 (by norm_num)) ?_⟩
    · intro j hj hc
      have hc' : a8Ord j = 576 := (hcard j hj).symm.trans hc
      have : ∀ j < 8, a8Ord j = 576 → j = 4 := by decide
      obtain rfl := this j hj hc'
      exact le_rfl
    · intro j hj hc
      have hc' : a8Ord j = 1344 := (hcard j hj).symm.trans hc
      have : ∀ j < 8, a8Ord j = 1344 → j = 5 ∨ j = 6 := by decide
      exact (hmono (by norm_num) hj).mp (a8_one_le (this j hj hc'))
    · intro j hj h4 h1
      have h576 : 576 ∣ a8Ord j := by
        have := Subgroup.card_dvd_of_le h4
        rw [hcard 4 (by norm_num), hcard j hj] at this
        exact this
      have : ∀ j < 8, 576 ∣ a8Ord j → j = 4 ∨ j = 7 := by decide
      rcases this j hj h576 with rfl | rfl
      · exact absurd ((hmono (by norm_num) (by norm_num)).mpr h1) a8_one_not_le_four
      · exact hZ7.ge
  intro W hTW hWL h5
  rcases hlat.complete W hTW hWL with rfl | ⟨w, hw, rfl⟩
  · exact hcaseL
  · have h5w : ∀ w < 8, 5 ∣ a8Ord w → w = 7 := by decide
    rw [h5w w hw (hcard w hw ▸ h5), hZ7]
    exact hcaseL

end CFSG.Quasithin.H13.KGMinPar
