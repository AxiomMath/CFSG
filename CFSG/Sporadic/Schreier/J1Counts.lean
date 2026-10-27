module

public import CFSG.Sporadic.Schreier.J1CountCheck

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem rep_j1ATbl : Rep 3080 j1ATbl j1A1 := rep_j1A1

theorem rep_j1BTbl : Rep 3080 j1BTbl j1A2 := rep_j1A2

theorem rep_j1AInvTbl :
    Rep 3080 j1AInvTbl j1A1⁻¹ := rep_j1ATbl.inv_of_invOK j1_gen_checks.1

theorem rep_j1BInvTbl :
    Rep 3080 j1BInvTbl j1A2⁻¹ := rep_j1BTbl.inv_of_invOK j1_gen_checks.2.1

theorem j1A1_mem : j1A1 ∈ j1P := Subgroup.subset_closure (Set.mem_insert _ _)

theorem j1A2_mem : j1A2 ∈ j1P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def j1GenPerm (l : ℕ) : Equiv.Perm (Fin 3080) :=
  if l = 0 then j1A1 else j1A2

theorem j1GenTbls_size : j1GenTbls.size = 2 := by
  simp [j1GenTbls]

theorem j1GenPerm_spec :
    ∀ l < j1GenTbls.size, Rep 3080 j1GenTbls[l]! (j1GenPerm l) ∧
    Rep 3080 j1GenInvTbls[l]! (j1GenPerm l)⁻¹ ∧ j1GenPerm l ∈ j1P := by
  intro l hl
  rw [j1GenTbls_size] at hl
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · have h1 : j1GenTbls[0]! = j1ATbl := by simp [j1GenTbls]
    have h2 : j1GenInvTbls[0]! = j1AInvTbl := by simp [j1GenInvTbls]
    have h3 : j1GenPerm 0 = j1A1 := by simp [j1GenPerm]
    rw [h1, h2, h3]
    exact ⟨rep_j1ATbl, rep_j1AInvTbl, j1A1_mem⟩
  · have h1 : j1GenTbls[1]! = j1BTbl := by simp [j1GenTbls]
    have h2 : j1GenInvTbls[1]! = j1BInvTbl := by simp [j1GenInvTbls]
    have h3 : j1GenPerm 1 = j1A2 := by simp [j1GenPerm]
    rw [h1, h2, h3]
    exact ⟨rep_j1BTbl, rep_j1BInvTbl, j1A2_mem⟩

theorem at_j1_image_pair_count :
    orderOf j1A1 = 2 ∧ orderOf j1A2 = 3 ∧ orderOf (j1A1 * j1A2) = 7 ∧
      orderOf (j1A1 * j1A2 * j1A1⁻¹ * j1A2⁻¹) = 19 ∧
      Nat.card {x : j1P // orderOf x = 2} = 1463 ∧ Nat.card {y : j1P // orderOf y = 3} = 5852 ∧
      Nat.card {p : j1P × j1P // orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 7 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 19} = 175560 := by
  obtain ⟨Q, hrec, hQ, -, -, -, hP, -, -⟩ := fam_j1_order
  have hord : ∀ m, orderTables Q m = j1OrderTables m := fun m => by
    rw [orderTables, j1_levelTables hrec]
    rfl
  obtain ⟨-, -, ha, hb, hab⟩ := j1_gen_checks
  have ha' : orderOf j1A1 = 2 := (ordTest_iff perm_faithful rep_j1ATbl (by norm_num)).1 ha
  have hb' : orderOf j1A2 = 3 := (ordTest_iff perm_faithful rep_j1BTbl (by norm_num)).1 hb
  obtain ⟨hab', hc'⟩ := (pairTest_iff perm_faithful rep_j1ATbl rep_j1BTbl (by norm_num)
    (by norm_num) ha' hb' (by norm_num) (by norm_num)).1 hab
  have h2 := card_orderOf_eq (by norm_num) Q hQ (m := 2) (by norm_num)
  have h3 := card_orderOf_eq (by norm_num) Q hQ (m := 3) (by norm_num)
  rw [hord, j1_count_two, hP] at h2
  rw [hord, j1_count_three, hP] at h3
  have hT := card_image_pairs_eq_classTotal (by norm_num) Q hQ (mx := 2) (my := 3) (r := 7)
    (s := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (gens := j1GenTbls)
    (gensInv := j1GenInvTbls) (gg := j1GenPerm) (by rw [hP]; exact j1GenPerm_spec) 2000
    (by rw [hord]; exact j1_classOK)
  rw [hord, hord, j1_classTotal, hP] at hT
  exact ⟨ha', hb', hab', hc', h2, h3, hT⟩

end CFSG.Sporadic.Schreier
