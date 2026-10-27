module

public import CFSG.Sporadic.HNSchreier.Primitive
public import CFSG.Sporadic.HNSchreier.Order
public import CFSG.Sporadic.HN.ConjSimple
public import Certificates.Certificate2096
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier.Native

theorem prep_ppow {t : Array ℕ} {g : Equiv.Perm X} (h : PRep hnsData.n t g) :
    ∀ e, PRep hnsData.n (ppow hnsData.n t e) (g ^ e)
  | 0 => by simpa [ppow] using (prep_pid (n := hnsData.n))
  | e + 1 => by
    rw [pow_succ]
    exact prep_pcomp (prep_ppow h e) h

private theorem prep_ppow_of_rep {n : ℕ} {t : Array ℕ}
    {g : Equiv.Perm (Fin n)} (h : PRep n t g) :
    ∀ e, PRep n (ppow n t e) (g ^ e)
  | 0 => by simpa [ppow] using (prep_pid (n := n))
  | e + 1 => by
    rw [pow_succ]
    exact prep_pcomp (prep_ppow_of_rep h e) h

private theorem order_parts_of_checks {n : ℕ} {a0 a1 : Equiv.Perm (Fin n)}
    {t0 t1 : Array ℕ} (hA : PRep n t0 a0) (hB : PRep n t1 a1)
    (checks : orderChecks n t0 t1 = true) : a0 ^ 2 = 1 ∧ a0 ≠ 1 ∧ a1 ^ 3 = 1 ∧ a1 ≠ 1 ∧
    (a0 * ((a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0)⁻¹ * a1 *
      (a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0))) ^ 19 = 1 ∧
    a0 * ((a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0)⁻¹ * a1 *
      (a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0)) ≠ 1 := by
  have h := checks
  unfold orderChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hi0, hi1⟩, h2⟩, h1⟩, h3⟩, h1'⟩, h19⟩, hx⟩ := h
  set S : Array (Array ℕ) := #[t0, t1]
  set Si := pinvs n S
  have hS : ∀ h < 2, PRep n S[h]! ((fun i => if i = 0 then a0 else a1) h) := by
    intro h hh
    interval_cases h
    · exact hA
    · exact hB
  have hSi : ∀ h < 2, PRep n Si[h]! ((fun i => if i = 0 then a0 else a1) h)⁻¹ := by
    intro h hh
    interval_cases h
    · exact prep_inv_of_pisInv hA hi0
    · exact prep_inv_of_pisInv hB hi1
  have hw := prep_pword hS hSi conjProdWord (by decide)
  have hval : Quiver.SchreierGraph.evalWord (fun h : Fin 2 =>
      (fun i => if i = 0 then a0 else a1) (h : ℕ)) (ptoLetters 2 conjProdWord) =
      a0 * ((a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0)⁻¹ * a1 *
        (a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0)) := by
    simp [conjProdWord, ptoLetters, Quiver.SchreierGraph.evalWord, mul_assoc]
  rw [hval] at hw
  have hp0 := hA
  have hp1 := hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact eq_of_peq (prep_ppow_of_rep hp0 2) prep_pid h2
  · intro e
    rw [e] at hp0
    exact absurd ((peq_iff hp0 prep_pid).2 rfl) (by rw [h1]; simp)
  · exact eq_of_peq (prep_ppow_of_rep hp1 3) prep_pid h3
  · intro e
    rw [e] at hp1
    exact absurd ((peq_iff hp1 prep_pid).2 rfl) (by rw [h1']; simp)
  · exact eq_of_peq (prep_ppow_of_rep hw 19) prep_pid h19
  · intro e
    rw [e] at hw
    exact absurd ((peq_iff hw prep_pid).2 rfl) (by rw [hx]; simp)

theorem order_parts :
    a0 ^ 2 = 1 ∧ a0 ≠ 1 ∧ a1 ^ 3 = 1 ∧ a1 ≠ 1 ∧
    (a0 * ((a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0)⁻¹ * a1 *
      (a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0))) ^ 19 = 1 ∧
    a0 * ((a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0)⁻¹ * a1 *
      (a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0)) ≠ 1 := by
  exact order_parts_of_checks prep_a0 prep_a1 order_cert

abbrev a0P : PH := ⟨a0, a0_mem⟩

abbrev a1P : PH := ⟨a1, a1_mem⟩

theorem orderOf_a0P :
    orderOf a0P = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime order_parts.1 order_parts.2.1

theorem orderOf_a1P :
    orderOf a1P = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime order_parts.2.2.1 order_parts.2.2.2.1

theorem closure_a0P_a1P : Subgroup.closure ({a0P, a1P} : Set PH) = ⊤ := by
  apply Subgroup.map_injective PH.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

theorem card_stabilizer_x0 :
    Nat.card (MulAction.stabilizer PH x0) = 239500800 := by
  rw [← card_PH_stab_zero]
  refine Nat.card_congr
    { toFun := fun g => ⟨g.1.1, Subgroup.mem_inf.2 ⟨g.1.2, (mem_fixingSubgroup_iff _).2 ?_⟩⟩
      invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, ?_⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact g.2
  · have := (mem_fixingSubgroup_iff (Equiv.Perm X)).1 (Subgroup.mem_inf.1 g.2).2 x0 rfl
    exact this

theorem ph_simple :
    IsSimpleGroup PH := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have := ph_preprimitive
  have : FaithfulSMul PH X := ⟨fun {g h} hgh => Subtype.ext (Equiv.ext hgh)⟩
  refine CFSG.Sporadic.F5.isSimpleGroup_of_primitive_conj_product
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin, hns_n]; norm_num)
    a0P a1P ⟨_, mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem a0_mem a1_mem) a1_mem) a0_mem) a1_mem) a0_mem) a1_mem) a0_mem)
      a1_mem) a0_mem) a1_mem) a0_mem⟩ closure_a0P_a1P x0
    (by rw [orderOf_a0P, orderOf_a1P]; decide) ?_
  rw [card_stabilizer_x0, ← Subgroup.orderOf_coe]
  have h19 : orderOf (a0 * ((a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0)⁻¹ * a1 *
      (a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0))) = 19 :=
    orderOf_eq_prime order_parts.2.2.2.2.1 order_parts.2.2.2.2.2
  convert (show Nat.Coprime 19 239500800 by decide) using 2

theorem fam_hn_certified_simplicity :
    Nontrivial Blueprint.NativeSporadic.HN ∧ IsSimpleGroup Blueprint.NativeSporadic.HN := by
  have hP := ph_simple
  have hs : IsSimpleGroup Blueprint.NativeSporadic.HN := MulEquiv.isSimpleGroup hnEquivP
  exact ⟨hs.toNontrivial, hs⟩

end CFSG.Sporadic.HNSchreier
