module

public import CFSG.Quasithin.Background.RonanH143Data

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk

@[expose] def eArr : Array ℕ :=
  #[1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 11, 10, 13, 12, 14, 15, 22, 23, 21, 20, 19, 18, 16, 17]

theorem e_ok : InvPairOK 24 eArr eArr = true ∧ autArrOK eArr eArr = true ∧
    eArr[0]! = 1 ∧ eArr[1]! = 0 := by
  decide +kernel

@[expose] def ePerm : P24 := permOfArr 24 eArr eArr e_ok.1

theorem hasArr_ePerm : HasArr ePerm eArr := hasArr_permOfArr e_ok.1

theorem ePerm_mem_mog22plus : ePerm ∈ mog22plus := by
  refine ⟨mem_AutPerm_of_arr e_ok.1 e_ok.2.1, Or.inr ⟨?_, ?_⟩⟩
  · exact hasArr_ePerm.apply_eq 0 e_ok.2.2.1
  · exact hasArr_ePerm.apply_eq 1 e_ok.2.2.2

theorem ePerm_sq : ePerm * ePerm = 1 := by decide +kernel

theorem ePerm_inv : ePerm⁻¹ = ePerm := inv_eq_of_mul_eq_one_right ePerm_sq

@[expose] def eK : List ℕ :=
  [0, 7, 0, 7, 0, 7, 0, 7, 1, 6, 1, 6, 1, 6, 1, 6, 3, 4, 3, 4, 3, 4, 3, 4, 2, 5, 2, 5, 2, 5, 2, 5,
    5, 2, 5, 2, 5, 2, 5, 2, 4, 3, 4, 3, 4, 3, 4, 3, 6, 1, 6, 1, 6, 1, 6, 1, 7, 0, 7, 0, 7, 0, 7, 0,
    14, 9, 14, 9, 14, 9, 14, 9, 15, 8, 15, 8, 15, 8, 15, 8, 13, 10, 13, 10, 13, 10, 13, 10, 12, 11,
    12, 11, 12, 11, 12, 11, 11, 12, 11, 12, 11, 12, 11, 12, 10, 13, 10, 13, 10, 13, 10, 13, 8, 15,
    8, 15, 8, 15, 8, 15, 9, 14, 9, 14, 9, 14, 9, 14]

@[expose] def eKF (t : Fin 16) (j : Fin 8) : Fin 16 :=
  ⟨(eK.getD (8 * (t : ℕ) + (j : ℕ)) 0) % 16, Nat.mod_lt _ (by norm_num)⟩

theorem ePerm_conj_PO' : ∀ (t : Fin 16) (j : Fin 8),
    ePerm * (koPerm t * dPerm j) * ePerm⁻¹ = koPerm (eKF t j) * dPerm j := by
  decide +kernel

theorem ePerm_conj_mem_PO {y : P24} (hy : y ∈ PO) : ePerm * y * ePerm⁻¹ ∈ PO := by
  obtain ⟨t, j, rfl⟩ := hy
  rw [ePerm_conj_PO']
  exact PO.mul_mem (koPerm_mem_PO _) (dPerm_mem_PO _)

@[expose] def nq2Perm (u : Fin 32) : P24 :=
  if (u : ℕ) < 16 then nqPerm ⟨u % 16, by omega⟩ else nqPerm ⟨u % 16, by omega⟩ * ePerm

@[expose] def xor32 (s t : Fin 32) : Fin 32 := ⟨((s : ℕ) ^^^ t) % 32, Nat.mod_lt _ (by norm_num)⟩

theorem nq2Perm_mul : ∀ s t : Fin 32, nq2Perm s * nq2Perm t = nq2Perm (xor32 s t) := by
  decide +kernel

theorem nq2Perm_zero : nq2Perm 0 = 1 := by decide +kernel

theorem nq2Perm_sq : ∀ t : Fin 32, nq2Perm t * nq2Perm t = 1 := by decide +kernel

theorem nq2Perm_injective : Function.Injective nq2Perm := by
  have : ∀ s t : Fin 32, nq2Perm s = nq2Perm t → s = t := by decide +kernel
  exact fun s t h => this s t h

@[expose] def NQ2 : Subgroup P24 where
  carrier := {g | ∃ u, g = nq2Perm u}
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨xor32 s t, nq2Perm_mul s t⟩
  one_mem' := ⟨0, nq2Perm_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, inv_eq_of_mul_eq_one_right (nq2Perm_sq t)⟩

theorem mem_NQ2_iff {g : P24} : g ∈ NQ2 ↔ ∃ u, g = nq2Perm u := Iff.rfl

theorem card_NQ2 : Nat.card NQ2 = 32 := by
  have h : (NQ2 : Set P24) = Set.range nq2Perm := by
    ext g
    simp only [SetLike.mem_coe, mem_NQ2_iff, Set.mem_range]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective nq2Perm_injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem isPGroup_NQ2 : IsPGroup 2 NQ2 := by
  intro ⟨g, hg⟩
  obtain ⟨t, rfl⟩ := hg
  exact ⟨1, Subtype.ext (by simpa [pow_two] using nq2Perm_sq t)⟩

theorem nq2_smul_Zq : ∀ (u : Fin 32) (i : Fin 5), nq2Perm u • Zq i = Zq i := by
  decide +kernel

theorem NQ_le_NQ2 : NQ ≤ NQ2 := by
  rintro _ ⟨t, rfl⟩
  refine ⟨⟨t, by omega⟩, ?_⟩
  have h : (t : ℕ) < 16 := t.2
  simp only [nq2Perm, h, ↓reduceIte]
  congr 1
  exact Fin.ext (by simp [Nat.mod_eq_of_lt h])

@[expose] def P2 : Subgroup P24 where
  carrier := {x | ∃ y ∈ PO, x = y ∨ x = y * ePerm}
  mul_mem' := by
    rintro a b ⟨y₁, hy₁, ha | ha⟩ ⟨y₂, hy₂, hb | hb⟩
    · exact ⟨y₁ * y₂, PO.mul_mem hy₁ hy₂, Or.inl (by rw [ha, hb])⟩
    · exact ⟨y₁ * y₂, PO.mul_mem hy₁ hy₂, Or.inr (by rw [ha, hb, mul_assoc])⟩
    · refine ⟨y₁ * (ePerm * y₂ * ePerm⁻¹), PO.mul_mem hy₁ (ePerm_conj_mem_PO hy₂), Or.inr ?_⟩
      rw [ha, hb]
      group
    · refine ⟨y₁ * (ePerm * y₂ * ePerm⁻¹), PO.mul_mem hy₁ (ePerm_conj_mem_PO hy₂), Or.inl ?_⟩
      have : y₁ * ePerm * (y₂ * ePerm) = y₁ * (ePerm * y₂ * ePerm⁻¹) * (ePerm * ePerm) := by group
      rw [ha, hb, this, ePerm_sq, mul_one]
  one_mem' := ⟨1, PO.one_mem, Or.inl rfl⟩
  inv_mem' := by
    rintro a ⟨y, hy, ha | ha⟩
    · exact ⟨y⁻¹, PO.inv_mem hy, Or.inl (by rw [ha])⟩
    · refine ⟨ePerm * y⁻¹ * ePerm⁻¹, ePerm_conj_mem_PO (PO.inv_mem hy), Or.inr ?_⟩
      rw [ha]
      calc (y * ePerm)⁻¹ = ePerm⁻¹ * y⁻¹ := mul_inv_rev _ _
        _ = ePerm * y⁻¹ := by rw [ePerm_inv]
        _ = ePerm * y⁻¹ * ePerm⁻¹ * ePerm := by group

theorem mem_P2_iff {x : P24} : x ∈ P2 ↔ ∃ y ∈ PO, x = y ∨ x = y * ePerm := Iff.rfl

theorem PO_le_P2 : PO ≤ P2 := fun y hy => ⟨y, hy, Or.inl rfl⟩

theorem ePerm_mem_P2 : ePerm ∈ P2 := ⟨1, PO.one_mem, Or.inr (by rw [one_mul])⟩

theorem NQ2_le_P2 : NQ2 ≤ P2 := by
  rintro _ ⟨u, rfl⟩
  by_cases hu : (u : ℕ) < 16
  · refine ⟨nqPerm ⟨u % 16, by omega⟩, nqPerm_mem_PO _, Or.inl ?_⟩
    simp [nq2Perm, hu]
  · refine ⟨nqPerm ⟨u % 16, by omega⟩, nqPerm_mem_PO _, Or.inr ?_⟩
    simp [nq2Perm, hu]

theorem card_fixO' : Nat.card fixO = 16 := by
  have h : (fixO : Set (Equiv.Perm (Fin 24))) = Set.range koPerm := by
    ext σ
    simp only [SetLike.mem_coe, mem_fixO_iff, Set.mem_range]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩
  have hinj : Function.Injective koPerm := by
    intro s t h
    have h1 := koPerm_eight s
    have h2 := koPerm_eight t
    rw [h] at h1
    exact Fin.ext (by omega)
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end CFSG.Quasithin.RonanH143
