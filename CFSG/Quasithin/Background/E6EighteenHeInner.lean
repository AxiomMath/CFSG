module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInner
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He
public import CFSG.Quasithin.Background.E6EighteenB

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.QuasithinUnique.Id2519.HeInner CFSG.Sporadic.HeldB
open scoped commutatorElement

theorem card_centralizer_mul_ncard_carrier {H : Type*} [Group H] [Finite H] (g : H) :
    Nat.card (Subgroup.centralizer ({g} : Set H)) * (ConjClasses.mk g).carrier.ncard =
      Nat.card H := by
  have hc : (ConjClasses.mk g).carrier = _root_.conjugatesOf g := by
    ext h
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    exact isConj_comm
  rw [hc, ← Subgroup.index_centralizer_eq_ncard, Subgroup.card_mul_index]

theorem heDpSizes_pos : ∀ i : Fin heDpSizes.length, 0 < heDpSizes[i] := by
  decide

theorem heDpSizes_eq_one_of_dvd :
    ∀ i : Fin heDpSizes.length, 6 ∣ 20160 / heDpSizes[i] → heDpSizes[i] = 1 := by
  decide

theorem heDpSizes_eq_nine_of_eq_one :
    ∀ i : Fin heDpSizes.length, heDpSizes[i] = 1 → (i : ℕ) = 9 := by
  decide

theorem heDp_false_of_commute {y z : ↥heDp.originalSubgroup}
    (hy : orderOf y = 3) (hz : orderOf z = 2) (hyz : y * z = z * y) : False := by
  classical
  obtain ⟨e, he⟩ := heDp_classes_equiv
  set C := Subgroup.centralizer ({y} : Set ↥heDp.originalSubgroup) with hC
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hyz.symm
  have h3 : 3 ∣ Nat.card C := hy ▸ Subgroup.orderOf_dvd_natCard C hyC
  have h2 : 2 ∣ Nat.card C := hz ▸ Subgroup.orderOf_dvd_natCard C hzC
  have hmul := card_centralizer_mul_ncard_carrier y
  rw [card_heDp] at hmul
  obtain ⟨i, hi⟩ := e.surjective (ConjClasses.mk y)
  have hs := he i
  rw [hi] at hs
  rw [hs] at hmul
  have hdiv : Nat.card C = 20160 / heDpSizes[i] := by
    rw [← hmul, Nat.mul_div_cancel _ (heDpSizes_pos i)]
  have h6 : 6 ∣ 20160 / heDpSizes[i] := by
    rw [← hdiv]
    omega
  have hi9 := heDpSizes_eq_nine_of_eq_one i (heDpSizes_eq_one_of_dvd i h6)
  obtain ⟨j, hj⟩ := e.surjective (ConjClasses.mk 1)
  have hs1 := he j
  rw [hj] at hs1
  have h1 : (ConjClasses.mk (1 : ↥heDp.originalSubgroup)).carrier = {1} := by
    ext g
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left,
      Set.mem_singleton_iff]
  rw [h1, Set.ncard_singleton] at hs1
  have hj9 := heDpSizes_eq_nine_of_eq_one j hs1.symm
  have hij : i = j := Fin.ext (hi9.trans hj9.symm)
  have hy1 : ConjClasses.mk y = ConjClasses.mk 1 := by rw [← hi, ← hj, hij]
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] at hy1
  rw [hy1, orderOf_one] at hy
  omega

theorem swap_mul_swap_mem_alternatingGroup {i j k l : Fin 7} (hij : i ≠ j) (hkl : k ≠ l) :
    Equiv.swap i j * Equiv.swap k l ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
    Equiv.Perm.sign_swap hkl]
  decide

@[expose] def alt7Elt (i j k l : Fin 7) (hij : i ≠ j) (hkl : k ≠ l) : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap i j * Equiv.swap k l, swap_mul_swap_mem_alternatingGroup hij hkl⟩

theorem alt7_witnesses : ∃ a b d u₁ v₁ u₂ v₂ : alternatingGroup (Fin 7),
    a ^ 3 = 1 ∧ a ≠ 1 ∧ b ^ 2 = 1 ∧ a * b = b * a ∧ (b * (d * b * d⁻¹)) ^ 3 = 1 ∧
      b * (d * b * d⁻¹) ≠ 1 ∧ ⁅u₁, v₁⁆ = a ∧ ⁅u₂, v₂⁆ = b := by
  refine ⟨alt7Elt 0 1 1 2 (by decide) (by decide), alt7Elt 3 4 5 6 (by decide) (by decide),
    alt7Elt 2 3 3 4 (by decide) (by decide), alt7Elt 0 1 0 2 (by decide) (by decide),
    alt7Elt 0 1 3 4 (by decide) (by decide), alt7Elt 0 1 3 4 (by decide) (by decide),
    alt7Elt 3 5 4 6 (by decide) (by decide), Subtype.ext (by decide),
    fun h => absurd (congrArg Subtype.val h) (by decide), Subtype.ext (by decide),
    Subtype.ext (by decide), Subtype.ext (by decide),
    fun h => absurd (congrArg Subtype.val h) (by decide), Subtype.ext (by decide),
    Subtype.ext (by decide)⟩

theorem heInnerGrp0_isEmpty_alt7
    (B : Subgroup ↥heInnerGrp0) : IsEmpty (↥B ≃* alternatingGroup (Fin 7)) := by
  refine ⟨fun φ => ?_⟩
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g : alternatingGroup (Fin 7) →* ↥heXp.originalSubgroup :=
    heRes0.comp (B.subtype.comp φ.symm.toMonoidHom) with hg
  have hker : ∀ x : alternatingGroup (Fin 7), x ^ 3 = 1 → x ≠ 1 → g x ≠ 1 := by
    intro x hx3 hx1 hgx
    have hmem : ((φ.symm x : ↥B) : ↥heInnerGrp0) ∈ heRes0.ker := hgx
    set w : ↥heRes0.ker := ⟨_, hmem⟩ with hw
    have hw3 : w ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change (((φ.symm x : ↥B) : ↥heInnerGrp0) : Equiv.Perm (Fin 8330)) ^ 3 = 1
      rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← map_pow, hx3, map_one]
      rfl
    have hw4 : w ^ 4 = 1 := by
      rw [← card_ker_heRes0]
      exact pow_card_eq_one'
    have hw1 : w = 1 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hw3, one_mul] at hw4
      exact hw4
    apply hx1
    have h1 : ((φ.symm x : ↥B) : ↥heInnerGrp0) = 1 := congrArg Subtype.val hw1
    have h2 : φ.symm x = 1 := Subtype.ext h1
    rw [← φ.apply_symm_apply x, h2, map_one]
  obtain ⟨a, b, d, u₁, v₁, u₂, v₂, ha3, ha1, hb2, hab, hx3, hx1, hca, hcb⟩ := alt7_witnesses
  have hga : g a ≠ 1 := hker a ha3 ha1
  have hgb : g b ≠ 1 := by
    intro h
    apply hker _ hx3 hx1
    rw [map_mul, map_mul, map_mul, map_inv, h, mul_one, one_mul, mul_inv_cancel]
  have hmemD : ∀ u v : alternatingGroup (Fin 7),
      ((g ⁅u, v⁆ : ↥heXp.originalSubgroup) : Equiv.Perm (Fin 105)) ∈ heDp.originalSubgroup := by
    intro u v
    have h1 : g ⁅u, v⁆ ∈ commutator ↥heXp.originalSubgroup := by
      rw [map_commutatorElement, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact Subgroup.mem_subgroupOf.1 (commutator_le_subgroupOf h1)
  have hyD := hmemD u₁ v₁
  have hzD := hmemD u₂ v₂
  rw [hca] at hyD
  rw [hcb] at hzD
  set y : ↥heDp.originalSubgroup := ⟨_, hyD⟩ with hy
  set z : ↥heDp.originalSubgroup := ⟨_, hzD⟩ with hz
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    change ((g a : ↥heXp.originalSubgroup) : Equiv.Perm (Fin 105)) ^ 3 = 1
    rw [← Subgroup.coe_pow, ← map_pow, ha3, map_one]
    rfl
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    change ((g b : ↥heXp.originalSubgroup) : Equiv.Perm (Fin 105)) ^ 2 = 1
    rw [← Subgroup.coe_pow, ← map_pow, hb2, map_one]
    rfl
  have hy1 : y ≠ 1 := by
    intro h
    have h' : ((g a : ↥heXp.originalSubgroup) : Equiv.Perm (Fin 105)) = 1 := congrArg Subtype.val h
    exact hga (Subtype.ext h')
  have hz1 : z ≠ 1 := by
    intro h
    have h' : ((g b : ↥heXp.originalSubgroup) : Equiv.Perm (Fin 105)) = 1 := congrArg Subtype.val h
    exact hgb (Subtype.ext h')
  have hyz : y * z = z * y := by
    apply Subtype.ext
    change ((g a : ↥heXp.originalSubgroup) : Equiv.Perm (Fin 105)) *
        (g b : ↥heXp.originalSubgroup) =
      ((g b : ↥heXp.originalSubgroup) : Equiv.Perm (Fin 105)) * (g a : ↥heXp.originalSubgroup)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]
  exact heDp_false_of_commute (orderOf_eq_prime hy3 hy1) (orderOf_eq_prime hz2 hz1) hyz

theorem IsA7Group.nonempty_mulEquiv_of_card_center {B : Type*} [Group B] (h : IsA7Group B)
    (hz : Nat.card (Subgroup.center B) = 1) : Nonempty (B ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨⟨φ⟩, -⟩ := h
  have hZ : Subgroup.center B = ⊥ := Subgroup.eq_bot_of_card_eq _ hz
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans φ⟩

theorem heInnerGrp0_not_isA7Group
    (B : Subgroup ↥heInnerGrp0) : ¬ IsA7Group ↥B := by
  intro h7
  have hc := h7.card_eq
  rcases h7.2 with hz | hz
  · obtain ⟨φ⟩ := h7.nonempty_mulEquiv_of_card_center hz
    exact (heInnerGrp0_isEmpty_alt7 B).false φ
  · rw [hz] at hc
    have hdvd := Subgroup.card_subgroup_dvd_card B
    rw [hc, CFSG.QuasithinUnique.Id2519.HeInner.card_heInnerGrp0] at hdvd
    norm_num at hdvd

theorem heInnerGrp1_not_isA7Group
    (B : Subgroup ↥heInnerGrp1) : ¬ IsA7Group ↥B := by
  intro h7
  have hdvd := h7.dvd_card.trans (Subgroup.card_subgroup_dvd_card B)
  rw [CFSG.QuasithinUnique.Id2519.HeInner.card_heInnerGrp1] at hdvd
  norm_num at hdvd

theorem factHeInnerNoA7_holds :
    ∀ (S : Type) [Group S], Nonempty (S ≃* Blueprint.NativeSporadic.He) → ∀ s : S, orderOf s = 2 →
      ∀ B : Subgroup S, B ≤ Subgroup.centralizer ({s} : Set S) → ¬ IsA7Group ↥B := by
  intro S _ ⟨e⟩ s hs B hB h7
  set F := CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj s)
    with hF
  have hBF : B ≤ F := by
    intro x hx
    have hx' := Subgroup.mem_centralizer_singleton_iff.1 (hB hx)
    change MulAut.conj s x = x
    rw [MulAut.conj_apply, ← hx', mul_inv_cancel_right]
  have key : ∀ Q : Subgroup (Equiv.Perm (Fin 8330)), Nonempty (↥F ≃* ↥Q) →
      ∃ B' : Subgroup ↥Q, IsA7Group ↥B' := by
    rintro Q ⟨ψ⟩
    exact ⟨(B.subgroupOf F).map ψ.toMonoidHom,
      (h7.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBF).symm).of_mulEquiv
        ((B.subgroupOf F).equivMapOfInjective ψ.toMonoidHom ψ.injective)⟩
  rcases CFSG.SeitzReduction.SporadicRefine.he_inner_fixedSubgroup_cases e s hs with h0 | h1
  · obtain ⟨B', hB'⟩ := key _ h0
    exact heInnerGrp0_not_isA7Group B' hB'
  · obtain ⟨B', hB'⟩ := key _ h1
    exact heInnerGrp1_not_isA7Group B' hB'

end E6

end CFSG.Quasithin
