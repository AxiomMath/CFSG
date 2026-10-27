module

public import CFSG.Monster.B.TwoA.Base.SevenPairA

public section

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code CFSG.Sporadic.Mathieu

open scoped Pointwise

@[expose] def qgenFun : Fin 10 → Fin 24 → Fin 24 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22],
  ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21],
  ![0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19],
  ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15],
  ![0, 1, 2, 3, 4, 6, 7, 5, 8, 11, 9, 10, 16, 19, 17, 18, 20, 23, 21, 22, 12, 15, 13, 14],
  ![0, 1, 2, 3, 5, 4, 7, 6, 8, 9, 10, 11, 13, 12, 15, 14, 18, 19, 16, 17, 23, 22, 21, 20],
  ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15, 20, 23, 21, 22, 16, 18, 19, 17],
  ![0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 12, 13, 15, 14, 20, 21, 23, 22, 16, 17, 19, 18],
  ![1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 11, 10, 13, 12, 14, 15, 22, 23, 21, 20, 19, 18, 16, 17],
  ![0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 17, 16, 21, 20, 19, 18, 23, 22]]

@[expose] def qgenInv : Fin 10 → Fin 24 → Fin 24 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22],
  ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21],
  ![0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19],
  ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15],
  ![0, 1, 2, 3, 4, 7, 5, 6, 8, 10, 11, 9, 20, 22, 23, 21, 12, 14, 15, 13, 16, 18, 19, 17],
  ![0, 1, 2, 3, 5, 4, 7, 6, 8, 9, 10, 11, 13, 12, 15, 14, 18, 19, 16, 17, 23, 22, 21, 20],
  ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15, 20, 23, 21, 22, 16, 18, 19, 17],
  ![0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 12, 13, 15, 14, 20, 21, 23, 22, 16, 17, 19, 18],
  ![1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 11, 10, 13, 12, 14, 15, 22, 23, 21, 20, 19, 18, 16, 17],
  ![0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 17, 16, 21, 20, 19, 18, 23, 22]]

@[expose] def qgen (i : Fin 10) : Equiv.Perm (Fin 24) where
  toFun := qgenFun i
  invFun := qgenInv i
  left_inv := (by decide : ∀ i x, qgenInv i (qgenFun i x) = x) i
  right_inv := (by decide : ∀ i x, qgenFun i (qgenInv i x) = x) i

theorem qgen_mem (i : Fin 10) : qgen i ∈ AutPerm := by
  fin_cases i <;> exact mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

@[expose] def qgenA (i : Fin 10) : AutPerm := ⟨qgen i, qgen_mem i⟩

theorem qgen_01 : ∀ i : Fin 10, (qgen i 0 = 0 ∧ qgen i 1 = 1) ∨ (qgen i 0 = 1 ∧ qgen i 1 = 0) := by
  decide

theorem qgen_23 : ∀ i : Fin 10, i.val < 9 →
    (qgen i 2 = 2 ∧ qgen i 3 = 3) ∨ (qgen i 2 = 3 ∧ qgen i 3 = 2) := by
  decide

theorem qgen_nine_smul_A2 : qgen 9 • A2 = A2 := by decide +kernel

theorem qgenA_mem_Ppair (i : Fin 10) : qgenA i ∈ Ppair := (mem_Ppair_iff _).2 (qgen_01 i)

theorem qgenA_mem_Ftwo {i : Fin 10} (hi : i.val < 9) : qgenA i ∈ Ftwo :=
  (mem_Ftwo_iff _).2 ⟨qgenA_mem_Ppair i, qgen_23 i hi⟩

theorem qgenA_nine_mem_FA2 : qgenA 9 ∈ FA2 :=
  Subgroup.mem_inf.2 ⟨qgenA_mem_Ppair 9, MulAction.mem_stabilizer_iff.2 qgen_nine_smul_A2⟩

@[expose] def pword (l : List (Fin 10)) : Equiv.Perm (Fin 24) := (l.map qgen).prod

@[expose] def qword (l : List (Fin 10)) : AutPerm := (l.map qgenA).prod

theorem coe_qword (l : List (Fin 10)) : (qword l : Equiv.Perm (Fin 24)) = pword l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change ((qgenA i * qword l : AutPerm) : Equiv.Perm (Fin 24)) = qgen i * pword l
    rw [Subgroup.coe_mul, ih]
    rfl

theorem qword_mem {Q : Subgroup AutPerm} (hQ : ∀ i, qgenA i ∈ Q) (l : List (Fin 10)) :
    qword l ∈ Q :=
  Q.list_prod_mem fun _ hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hQ i

@[expose] def wx : Fin 24 → List (Fin 10) := ![[], [],
    [], [7], [9], [9, 7], [4, 9, 7], [4, 4, 9, 7], [6, 9], [6, 9, 7], [1, 6, 9], [1, 6, 9, 7],
    [2, 6, 9], [2, 6, 9, 7], [2, 1, 6, 9], [2, 1, 6, 9, 7], [3, 6, 9], [3, 6, 9, 7], [3, 1, 6, 9],
    [3, 1, 6, 9, 7], [3, 2, 6, 9], [3, 2, 6, 9, 7], [8, 3, 6, 9], [4, 3, 6, 9, 7]]

@[expose] def uz : Fin 24 → List (Fin 10) := ![
    [], [], [], [], [5, 4, 9, 4, 4, 9], [4, 9, 4, 4, 9], [9, 4, 9], [9, 4, 4, 9], [1, 6, 9, 4, 9],
    [4, 6, 9, 4, 9], [6, 9, 4, 9], [6, 9, 4, 4, 9], [2, 1, 6, 9, 4, 9], [2, 4, 6, 9, 4, 9],
    [2, 6, 9, 4, 9], [2, 6, 9, 4, 4, 9], [3, 1, 6, 9, 4, 9], [4, 2, 6, 9, 4, 9], [3, 6, 9, 4, 9],
    [3, 6, 9, 4, 4, 9], [8, 3, 6, 9, 4, 4, 9], [4, 3, 6, 9, 4, 9], [3, 2, 6, 9, 4, 9],
    [3, 2, 6, 9, 4, 4, 9]]

theorem pword_wx : ∀ x : Fin 24, 2 ≤ x.val → pword (wx x) 2 = x := by decide +kernel

theorem pword_uz : ∀ z : Fin 24, 3 ≤ z.val → pword (uz z) 2 = 2 ∧ pword (uz z) 3 = z := by
  decide +kernel

theorem qgenA_mem_sup (i : Fin 10) : qgenA i ∈ Ftwo ⊔ FA2 := by
  by_cases hi : i.val < 9
  · exact Subgroup.mem_sup_left (qgenA_mem_Ftwo hi)
  · have h9 : i = 9 := Fin.ext (by omega)
    rw [h9]
    exact Subgroup.mem_sup_right qgenA_nine_mem_FA2

theorem two_le_of_ne : ∀ x : Fin 24, x ≠ 0 → x ≠ 1 → 2 ≤ x.val := by decide

theorem exists_sup_pair {x y : Fin 24} (hx : 2 ≤ x.val) (hy : 2 ≤ y.val) (hxy : x ≠ y) :
    ∃ q ∈ Ftwo ⊔ FA2, (q : Equiv.Perm (Fin 24)) 2 = x ∧ (q : Equiv.Perm (Fin 24)) 3 = y := by
  set w := qword (wx x)
  have hw : (w : Equiv.Perm (Fin 24)) 2 = x := by rw [coe_qword]; exact pword_wx x hx
  have hwP : w ∈ Ppair := qword_mem qgenA_mem_Ppair _
  set z := (w : Equiv.Perm (Fin 24))⁻¹ y
  have hwz : (w : Equiv.Perm (Fin 24)) z = y := (Equiv.Perm.inv_eq_iff_eq.1 rfl).symm
  have hz : 3 ≤ z.val := by
    have hy01 := Ppair_apply_ne (Ppair.inv_mem hwP)
      (i := y) (fun h => by rw [h] at hy; simp at hy) (fun h => by rw [h] at hy; simp at hy)
    have h2 := two_le_of_ne z hy01.1 hy01.2
    have hz2 : z ≠ 2 := fun h => hxy (by rw [← hw, ← hwz, h])
    have : z.val ≠ 2 := fun h => hz2 (Fin.ext h)
    omega
  set u := qword (uz z)
  have hu := pword_uz z hz
  rw [← coe_qword] at hu
  refine ⟨w * u, (Ftwo ⊔ FA2).mul_mem (qword_mem qgenA_mem_sup _) (qword_mem qgenA_mem_sup _),
    ?_, ?_⟩
  · rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, hu.1, hw]
  · rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, hu.2, hwz]

theorem Ppair_eq_sup : Ppair = Ftwo ⊔ FA2 := by
  refine le_antisymm (fun p hp => ?_) (sup_le inf_le_left FA2_le_Ppair)
  have h2 := Ppair_apply_ne hp (i := 2) (by decide) (by decide)
  have h3 := Ppair_apply_ne hp (i := 3) (by decide) (by decide)
  obtain ⟨q, hq, hq2, hq3⟩ := exists_sup_pair (two_le_of_ne _ h2.1 h2.2)
    (two_le_of_ne _ h3.1 h3.2) ((p : Equiv.Perm (Fin 24)).injective.ne (by decide))
  have hqP : q ∈ Ppair := sup_le inf_le_left FA2_le_Ppair hq
  have hF : q⁻¹ * p ∈ Ftwo := by
    refine (mem_Ftwo_iff _).2 ⟨Ppair.mul_mem (Ppair.inv_mem hqP) hp, .inl ⟨?_, ?_⟩⟩
    · rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, ← hq2, InvMemClass.coe_inv]
      exact Equiv.Perm.inv_eq_iff_eq.2 rfl
    · rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, ← hq3, InvMemClass.coe_inv]
      exact Equiv.Perm.inv_eq_iff_eq.2 rfl
  have e : p = q * (q⁻¹ * p) := by group
  rw [e]
  exact (Ftwo ⊔ FA2).mul_mem hq (Subgroup.mem_sup_left hF)

end CFSG.Monster.B.TwoA
