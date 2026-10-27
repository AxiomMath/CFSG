module

public import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2LemmaATop
public import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2Main
public import Certificates.Certificate642001

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace SimsFinalL2

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.L34
open CFSG.RankThree.PartTwo.KFacts.L34Max Certificates.Data.L34QEight

theorem l34QEight_check :
    qClosed = true ∧ closureCheck = true :=
  Certificates.certificate642001

theorem qClosed_spec :
    qList.Nodup ∧ (∀ a ∈ qList, ∀ b ∈ qList, a * b ∈ qList) ∧ ∀ a ∈ qList, a⁻¹ ∈ qList := by
  have h := l34QEight_check.1
  simp only [qClosed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem one_mem_qList : (1 : Equiv.Perm (Fin 21)) ∈ qList :=
  List.mem_map.mpr ⟨1, List.mem_cons_self, tab_eq 1⟩

theorem q1_mem : q1 ∈ N0 := by
  rw [q1, tab_eq]
  exact N0.mul_mem n0a_mem n0b_mem

theorem q2_mem : q2 ∈ N0 := by
  rw [q2, tab_eq]
  exact N0.mul_mem (N0.mul_mem n0b_mem n0a_mem) n0a_mem

theorem mem_N0_of_mem_qList {a : Equiv.Perm (Fin 21)} (ha : a ∈ qList) : a ∈ N0 := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
  rw [tab_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N0.one_mem
  · exact q1_mem
  · exact N0.pow_mem q1_mem 2
  · exact N0.pow_mem q1_mem 3
  · exact q2_mem
  · exact N0.mul_mem q1_mem q2_mem
  · exact N0.mul_mem (N0.pow_mem q1_mem 2) q2_mem
  · exact N0.mul_mem (N0.pow_mem q1_mem 3) q2_mem

@[expose] def Q0 : Subgroup (Equiv.Perm (Fin 21)) where
  carrier := {a | a ∈ qList}
  mul_mem' ha hb := qClosed_spec.2.1 _ ha _ hb
  one_mem' := one_mem_qList
  inv_mem' ha := qClosed_spec.2.2 _ ha

theorem Q0_le_N0 : Q0 ≤ N0 := fun _ ha => mem_N0_of_mem_qList ha

theorem card_Q0 : Nat.card Q0 = 8 := by
  have hS : (Q0 : Set (Equiv.Perm (Fin 21))) = ↑qList.toFinset := by
    ext a
    simp [Q0]
  rw [← SetLike.coe_sort_coe, hS, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup qClosed_spec.1]
  simp [qList]

theorem exists_orderOf_eq_three_mem_closure
    {x : Equiv.Perm (Fin 21)} (hx : x ∈ P21)
    (hx57 : orderOf x = 5 ∨ orderOf x = 7) :
    ∃ w ∈ Subgroup.closure {y | ∃ q ∈ qList, y = q * x * q⁻¹}, orderOf w = 3 := by
  set S := {y | ∃ q ∈ qList, y = q * x * q⁻¹} with hSdef
  have hall := l34QEight_check.2
  rw [closureCheck] at hall
  have h := forall_of_all QP21 QP21_ok hall x hx
  have h57 : (orderIs x 5 || orderIs x 7) = true := by
    rcases hx57 with h5 | h7
    · simp [(orderIs_iff x (by norm_num : 0 < 5)).mpr h5]
    · simp [(orderIs_iff x (by norm_num : 0 < 7)).mpr h7]
  have hw : wordOK qList x = true := by
    rw [h57, Bool.not_true, Bool.false_or] at h
    exact h
  simp only [wordOK, List.any_eq_true] at hw
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := hw
  refine ⟨x * a * b * c, ?_, (orderIs_iff _ (by norm_num : 0 < 3)).mp habc⟩
  have hS : ∀ q ∈ qList, q * x * q⁻¹ ∈ Subgroup.closure S := fun q hq =>
    Subgroup.subset_closure ⟨q, hq, rfl⟩
  have hconj : ∀ d ∈ conjs qList x, d ∈ Subgroup.closure S := by
    intro d hd
    simp only [conjs, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | ⟨q, hq, rfl | rfl⟩
    · exact Subgroup.one_mem _
    · rw [tab_eq]
      exact hS q hq
    · rw [tab_eq, show q * x⁻¹ * q⁻¹ = (q * x * q⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ (hS q hq)
  have hx' : x ∈ Subgroup.closure S := by
    simpa using hS 1 one_mem_qList
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx' (hconj a ha))
    (hconj b hb)) (hconj c hc)

end SimsFinalL2

open CFSG.Certificates CFSG.GH74.KGroups.L34 CFSG.RankThree.PartTwo.KFacts.L34Max
open Certificates.Data.L34QEight in
theorem kFactL34QEightClosure_holds :
    KFactL34QEightClosure := by
  intro X _ _ ⟨e⟩ Bb Q hBb hQ hQB x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ₀⟩ := nonempty_mulEquiv_P21
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_eq_E0' (e.trans ψ₀) hBb
  set Q' := Q.map φ.toMonoidHom with hQ'
  have hQ'N : Q' ≤ N0' := by
    rw [← normalizer_E0', ← hφ, ← Subgroup.map_equiv_normalizer_eq Bb φ]
    exact Subgroup.map_mono hQB
  have hQ'8 : Nat.card Q' = 8 := by
    rw [hQ', Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hQ]
  have hQ0P : SimsFinalL2.Q0 ≤ P21 := SimsFinalL2.Q0_le_N0.trans N0_le_P21
  set Q0' := SimsFinalL2.Q0.subgroupOf P21 with hQ0'
  have hQ0N : Q0' ≤ N0' := fun a ha =>
    Subgroup.mem_subgroupOf.mpr (SimsFinalL2.Q0_le_N0 (Subgroup.mem_subgroupOf.mp ha))
  have hQ0'8 : Nat.card Q0' = 8 := by
    rw [hQ0', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0P).toEquiv, SimsFinalL2.card_Q0]
  have h8 : 2 ^ (Nat.card N0').factorization 2 = 8 := by
    rw [card_N0', show (72 : ℕ) = 2 ^ 3 * 9 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hcard0 : Nat.card (Q0'.subgroupOf N0') = 2 ^ (Nat.card N0').factorization 2 := by
    rw [h8, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0N).toEquiv, hQ0'8]
  have hcard1 : Nat.card (Q'.subgroupOf N0') = 2 ^ (Nat.card N0').factorization 2 := by
    rw [h8, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ'N).toEquiv, hQ'8]
  obtain ⟨n, hn⟩ := exists_map_conj_eq_of_card hcard0 hcard1
  set f : X →* Equiv.Perm (Fin 21) :=
    P21.subtype.comp ((MulAut.conj (n : P21)).toMonoidHom.comp φ.toMonoidHom) with hf
  have hfinj : Function.Injective f :=
    P21.subtype_injective.comp ((MulAut.conj (n : P21)).injective.comp φ.injective)
  have hqf : ∀ q' ∈ qList, ∃ q ∈ Q, f q = q' := by
    intro q' hq'
    have h1 : (⟨⟨q', hQ0P hq'⟩, hQ0N (Subgroup.mem_subgroupOf.mpr hq')⟩ : N0') ∈
        Q0'.subgroupOf N0' := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hq')
    rw [← hn] at h1
    obtain ⟨r, hr, hrq⟩ := h1
    have hr' : ((r : P21) : P21) ∈ Q' := Subgroup.mem_subgroupOf.mp hr
    obtain ⟨q, hq, hqr⟩ := hr'
    refine ⟨q, hq, ?_⟩
    have h2 := congrArg (fun z : N0' => ((z : P21) : Equiv.Perm (Fin 21))) hrq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h2
    rw [hf, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← h2]
    congr 2
    rw [← hqr]
    rfl
  have hx'P : f x ∈ P21 := (((MulAut.conj (n : P21)).toMonoidHom.comp φ.toMonoidHom) x).2
  have hx'o : orderOf (f x) = 5 ∨ orderOf (f x) = 7 := by
    rw [orderOf_injective f hfinj x]
    exact hx
  obtain ⟨w, hw, hw3⟩ := SimsFinalL2.exists_orderOf_eq_three_mem_closure hx'P hx'o
  set C := Subgroup.closure {y : X | ∃ q ∈ Q, y = q * x * q⁻¹} with hC
  have hle : Subgroup.closure {y | ∃ q ∈ qList, y = q * f x * q⁻¹} ≤ C.map f := by
    rw [Subgroup.closure_le]
    rintro _ ⟨q', hq', rfl⟩
    obtain ⟨q, hq, rfl⟩ := hqf q' hq'
    exact ⟨q * x * q⁻¹, Subgroup.subset_closure ⟨q, hq, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩
  obtain ⟨u, hu, rfl⟩ := hle hw
  have hu3 : orderOf (⟨u, hu⟩ : C) = 3 := by
    rw [Subgroup.orderOf_mk, ← orderOf_injective f hfinj u]
    exact hw3
  rw [← hu3]
  exact orderOf_dvd_natCard _

theorem kFactL34QEightTop_holds :
    KFactL34QEightTop :=
  kFactL34QEightTop_of_closure kFactL34QEightClosure_holds

section Certified


theorem step204FinalL2ZNe_holds (h1812 : Sec18.Item181_2) (h1841 : Sec18.Item184_1)
    (h1842 : Sec18.Item184_2) : Step204FinalL2ZNe :=
  step204FinalL2ZNe_of_sec18 h1812 h1841 h1842 kFactL34QEightTop_holds

end Certified

end CFSG.RankThree.PartTwo.Sec20
