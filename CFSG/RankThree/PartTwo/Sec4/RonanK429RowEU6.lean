module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEU6Fix
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU)

namespace U6

open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open Matrix

@[expose] def m12a : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

@[expose] def m12b : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

theorem m12a_mem : m12a ∈ Blueprint.NativeSporadic.M12 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m12b_mem : m12b ∈ Blueprint.NativeSporadic.M12 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

@[expose] def m12x : Equiv.Perm (Fin 12) :=
  m12a * m12b * m12a * m12b * m12a * m12b * m12a * m12b * m12b * m12a * m12b * m12b

@[expose] def m12y : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 1, 9, 10, 5, 8, 6, 11, 7, 4] * List.formPerm [2, 3]

theorem m12x_eq : m12x = m12y := by decide +kernel

theorem m12x_mem : m12x ∈ Blueprint.NativeSporadic.M12 :=
  have ha := m12a_mem
  have hb := m12b_mem
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem ha hb) ha) hb) ha) hb) ha) hb) hb) ha) hb) hb

theorem orderOf_m12y : orderOf m12y = 10 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide +kernel

theorem orderOf_m12x : orderOf m12x = 10 := by
  rw [m12x_eq, orderOf_m12y]

theorem exists_fix_orderOf {α : MulAut P6} {K : Subgroup P6} (hKC : K ≤ autFix α)
    (x : K ⧸ CFSG.pCore 2 K) : ∃ g : P6, α g = g ∧ orderOf g = orderOf x := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have hk : orderOf (k : K ⧸ CFSG.pCore 2 K) ∣ orderOf k := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 K)) k
    rwa [QuotientGroup.mk'_apply] at h
  have hk0 : orderOf k ≠ 0 := (isOfFinOrder_of_finite k).orderOf_pos.ne'
  refine ⟨((k ^ (orderOf k / orderOf (k : K ⧸ CFSG.pCore 2 K)) : K) : P6),
    mem_autFix.mp (hKC (SetLike.coe_mem _)), ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_orderOf_div hk0 hk]

theorem card_P6_dvd : Nat.card P6 ∣ 27590492160 := by
  rw [← card_S6]
  exact Subgroup.card_quotient_dvd_card _

theorem typeOrders_S6 : typeOrders 27590492160 3100 = [2520, 95040, 443520, 20160] := by
  decide +kernel

theorem good429_P6 (α : MulAut P6) (h3 : α ^ 3 = 1) (h1 : α ≠ 1) : Good429 (autFix α) := by
  obtain ⟨A, rfl⟩ := exists_conj6_eq_of_pow_three h3
  have hA3 := exists_pow_three_eq_scalar h3
  have hns : ∀ d : F4c, matC (A : GL (Fin 6) F4) ≠ Matrix.scalar (Fin 6) d :=
    fun d h => h1 (conj6_eq_one_of_matC h)
  intro K hKC hKp hKs hT
  haveI := hKp
  haveI := nontrivial_of_isType429 hT
  have hel : ∀ r : ℕ, r.Prime → r ∣ Nat.card (K ⧸ CFSG.pCore 2 K) →
      ∃ g : P6, conj6 A g = g ∧ orderOf g = r := by
    intro r hr hdvd
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K ⧸ CFSG.pCore 2 K) r hdvd
    obtain ⟨g, hg, hgo⟩ := exists_fix_orderOf hKC x
    exact ⟨g, hg, hgo.trans hx⟩
  have hQ : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ 27590492160 :=
    (Subgroup.card_quotient_dvd_card _).trans
      ((Subgroup.card_subgroup_dvd_card K).trans card_P6_dvd)
  have hmem := card_mem_typeOrders (M := 27590492160) (B := 3100) (by norm_num) (by norm_num) hT hQ
  rw [typeOrders_S6] at hmem
  have h57 : ¬ (5 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) ∧ 7 ∣ Nat.card (K ⧸ CFSG.pCore 2 K)) := by
    rintro ⟨h5, h7⟩
    obtain ⟨g5, hg5, ho5⟩ := hel 5 (by norm_num) h5
    obtain ⟨g7, hg7, ho7⟩ := hel 7 (by norm_num) h7
    exact pow_three_ne_one_of_seven hns hg7 ho7 (pow_three_eq_one_of_five hA3 hg5 ho5)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · exact h57 ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩
  · have hM12 : Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M12) := by
      rcases hT with ⟨p, e, hp, -, hiso⟩ | ⟨⟨φ⟩⟩ | hm | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · exact absurd hiso (KS14.not_isoLThreePi_of_card h
          (KS14.forall_of_forall_lt (by norm_num) (by norm_num) KS14.checkSL_m12)
          (KS14.forall_of_forall_lt (by norm_num) (by norm_num) KS14.checkSU_m12) p e)
      · have hc := Nat.card_congr φ.toEquiv
        rw [h, KS14.card_alternatingGroup_five_seven_ten.2.1] at hc
        norm_num at hc
      · exact hm
      · have hc := Nat.card_congr φ.toEquiv
        rw [h, KS14.card_nativeM22] at hc
        norm_num at hc
      · have hc := Nat.card_congr φ.toEquiv
        rw [h, KS14.card_nativeJ2] at hc
        norm_num at hc
    obtain ⟨φ⟩ := hM12
    obtain ⟨g11, hg11, ho11⟩ := hel 11 (by norm_num) (by rw [h]; norm_num)
    have h10 : orderOf (⟨m12x, m12x_mem⟩ : Blueprint.NativeSporadic.M12) = 10 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_m12x
    obtain ⟨g10, hg10, ho10⟩ := exists_fix_orderOf hKC (φ.symm ⟨m12x, m12x_mem⟩)
    rw [MulEquiv.orderOf_eq, h10] at ho10
    exact trace_ne_zero_of_eleven hA3 hns hg11 ho11 (trace_eq_zero_of_ten hA3 hg10 ho10)
  · exact h57 ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩
  · exact h57 ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩

end U6

theorem noCfgS429_su62 {S : Type} [Group S] [Finite S] (e : S ≃* projSU 6 2 1) : NoCfgS429 S := by
  let φ : S ≃* Item434SmallTwoIVU62.P6 := e.trans Item434SmallTwoIVU62.u6Equiv
  refine noCfgS429_of_good fun σ h3 h1 => ?_
  have hτ3 : MulAut.congr φ σ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hτ1 : MulAut.congr φ σ ≠ 1 := by
    rw [Ne, MulEquiv.map_eq_one_iff]
    exact h1
  have hg := U6.good429_P6 (MulAut.congr φ σ) hτ3 hτ1
  rw [autFix_congr] at hg
  exact Good429.of_map φ.toMonoidHom φ.injective hg

theorem eight_SU6 : RowSOf429 (projSU 6 2 1) :=
  rowSOf429_of_noCfg fun _ _ _ _ _ ⟨e⟩ => noCfgS429_su62 e

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
