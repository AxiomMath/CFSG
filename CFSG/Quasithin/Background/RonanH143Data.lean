module

public import CFSG.Quasithin.Background.RonanH143Vocab
public import CFSG.Quasithin.Background.HModChk
public import CFSG.Quasithin.Background.H16TwoM22PfA
public import CFSG.Quasithin.Background.H16TwoM22PfB

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk

@[expose] def zMask : Fin 5 → ℕ := ![60, 49920, 15360, 12779520, 3932160]

@[expose] def Zq (i : Fin 5) : Finset (Fin 24) := maskSet (zMask i)

@[expose] def Bstd : Finset (Fin 24) := maskSet 195

@[expose] def Ostd : Finset (Fin 24) := maskSet 255

@[expose] def Hstd : Finset (Fin 24) := maskSet 252

@[expose] def Qstd : Finset (Finset (Fin 24)) := Finset.univ.image Zq

@[expose] def Sstd : Finset (Finset (Fin 24)) := insert Bstd Qstd

theorem Zq_injective : Function.Injective Zq := by
  intro i j h
  have : ∀ i j : Fin 5, Zq i = Zq j → i = j := by decide +kernel
  exact this i j h

theorem Bstd_notMem_Qstd : Bstd ∉ Qstd := by decide +kernel

theorem Sstd_erase : Sstd.erase Bstd = Qstd := by
  unfold Sstd
  exact Finset.erase_insert Bstd_notMem_Qstd

theorem mem_Qstd_iff (T : Finset (Fin 24)) : T ∈ Qstd ↔ ∃ i, Zq i = T := by
  simp [Qstd]

theorem Qstd_card : Qstd.card = 5 := by decide +kernel

theorem Hstd_eq : Hstd = ((Ostd.erase 0).erase 1) := by decide +kernel

@[expose] def nqK : List ℕ := [0, 1, 6, 7, 6, 7, 0, 1, 6, 7, 0, 1, 0, 1, 6, 7]

@[expose] def nqJ : List ℕ := [0, 0, 0, 0, 4, 4, 4, 4, 2, 2, 2, 2, 6, 6, 6, 6]

@[expose] def nqKF (t : Fin 16) : Fin 16 := ⟨(nqK.getD t 0) % 16, Nat.mod_lt _ (by norm_num)⟩

@[expose] def nqJF (t : Fin 16) : Fin 8 := ⟨(nqJ.getD t 0) % 8, Nat.mod_lt _ (by norm_num)⟩

@[expose] def nqPerm (t : Fin 16) : P24 := koPerm (nqKF t) * dPerm (nqJF t)

theorem nqPerm_mul : ∀ s t : Fin 16, nqPerm s * nqPerm t = nqPerm (xorF s t) := by
  decide +kernel

theorem nqPerm_zero : nqPerm 0 = 1 := by decide +kernel

theorem nqPerm_sq : ∀ t : Fin 16, nqPerm t * nqPerm t = 1 := by decide +kernel

theorem nqPerm_injective : Function.Injective nqPerm := by
  have : ∀ s t : Fin 16, nqPerm s = nqPerm t → s = t := by decide +kernel
  exact fun s t h => this s t h

theorem nqPerm_mem_PO (t : Fin 16) : nqPerm t ∈ PO :=
  PO.mul_mem (koPerm_mem_PO _) (dPerm_mem_PO _)

theorem nqPerm_mem_mog22 (t : Fin 16) : nqPerm t ∈ mog22 :=
  PO_le_mog22 (nqPerm_mem_PO t)

@[expose] def NQ : Subgroup P24 where
  carrier := {g | ∃ t, g = nqPerm t}
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨xorF s t, nqPerm_mul s t⟩
  one_mem' := ⟨0, nqPerm_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, inv_eq_of_mul_eq_one_right (nqPerm_sq t)⟩

theorem mem_NQ_iff {g : P24} : g ∈ NQ ↔ ∃ t, g = nqPerm t := Iff.rfl

theorem card_NQ : Nat.card NQ = 16 := by
  have h : (NQ : Set P24) = Set.range nqPerm := by
    ext g
    simp only [SetLike.mem_coe, mem_NQ_iff, Set.mem_range]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective nqPerm_injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem NQ_le_PO : NQ ≤ PO := by
  rintro _ ⟨t, rfl⟩
  exact nqPerm_mem_PO t

theorem NQ_le_mog22 : NQ ≤ mog22 := NQ_le_PO.trans PO_le_mog22

theorem isPGroup_NQ : IsPGroup 2 NQ := by
  intro ⟨g, hg⟩
  obtain ⟨t, rfl⟩ := hg
  exact ⟨1, Subtype.ext (by simpa [pow_two] using nqPerm_sq t)⟩

theorem NQ_comm (x y : P24) (hx : x ∈ NQ) (hy : y ∈ NQ) : x * y = y * x := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  rw [nqPerm_mul, nqPerm_mul]
  congr 1
  simp only [xorF, Nat.xor_comm]

@[expose] def g1Arr : Array ℕ :=
  #[0, 1, 8, 9, 14, 15, 6, 7, 16, 23, 18, 20, 21, 19, 17, 22, 10, 11, 2, 3, 4, 5, 12, 13]

@[expose] def g1Inv : Array ℕ :=
  #[0, 1, 18, 19, 20, 21, 6, 7, 2, 3, 16, 17, 22, 23, 4, 5, 8, 14, 10, 13, 11, 12, 15, 9]

theorem g1_ok : InvPairOK 24 g1Arr g1Inv = true ∧ autArrOK g1Arr g1Inv = true ∧
    g1Arr[0]! = 0 ∧ g1Arr[1]! = 1 := by
  decide +kernel

@[expose] def g1Perm : P24 := permOfArr 24 g1Arr g1Inv g1_ok.1

theorem hasArr_g1Perm : HasArr g1Perm g1Arr := hasArr_permOfArr g1_ok.1

theorem g1Perm_mem_mog22 : g1Perm ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr g1_ok.1 g1_ok.2.1) hasArr_g1Perm g1_ok.2.2.1 g1_ok.2.2.2

@[expose] def g2Perm : P24 := koPerm 10 * dPerm 1

@[expose] def a2Perm : P24 := koPerm 2

theorem g2Perm_mem_PO : g2Perm ∈ PO := PO.mul_mem (koPerm_mem_PO _) (dPerm_mem_PO _)

theorem a2Perm_mem_PO : a2Perm ∈ PO := koPerm_mem_PO _

@[expose] def sig1 : Equiv.Perm (Fin 5) := List.formPerm [0, 1, 3, 2, 4]

@[expose] def sig2 : Equiv.Perm (Fin 5) := Equiv.swap 2 3

@[expose] def siga2 : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 3 4

theorem sig1_isCycle : sig1.IsCycle := by
  unfold sig1
  exact List.isCycle_formPerm (by decide) (by decide)

theorem sig1_support : sig1.support = ⊤ := by
  unfold sig1
  rw [List.support_formPerm_of_nodup _ (by decide) (by decide)]
  decide

theorem sig2_eq : sig2 = Equiv.swap 3 (sig1 3) := by decide +kernel

theorem g1_smul_Zq : ∀ i, g1Perm • Zq i = Zq (sig1 i) := by decide +kernel

theorem g2_smul_Zq : ∀ i, g2Perm • Zq i = Zq (sig2 i) := by decide +kernel

theorem a2_smul_Zq : ∀ i, a2Perm • Zq i = Zq (siga2 i) := by decide +kernel

theorem nq_smul_Zq : ∀ (t : Fin 16) (i : Fin 5), nqPerm t • Zq i = Zq i := by decide +kernel

@[expose] def tab (F : List ℕ) (t : Fin 16) : Fin 16 := ⟨(F.getD t 0) % 16, Nat.mod_lt _ (by norm_num)⟩

@[expose] def F1 : List ℕ := [0, 4, 8, 12, 9, 13, 1, 5, 14, 10, 6, 2, 7, 3, 15, 11]

@[expose] def FA2 : List ℕ := [0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 15, 14, 13, 12]

theorem conj_g1_nq : ∀ t : Fin 16, g1Perm * nqPerm t * g1Perm⁻¹ = nqPerm (tab F1 t) := by
  decide +kernel

theorem conj_a2_nq : ∀ t : Fin 16, a2Perm * nqPerm t * a2Perm⁻¹ = nqPerm (tab FA2 t) := by
  decide +kernel

end CFSG.Quasithin.RonanH143
