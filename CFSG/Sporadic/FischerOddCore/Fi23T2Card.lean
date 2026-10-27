module

public import CFSG.Sporadic.FischerOddCore.Fi23NoComp

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer

theorem card_le_ncard_mul_card_stabilizer {G X : Type*} [Group G] [MulAction G X] [Finite G]
    (x : X) {Y : Set X} (hY : Y.Finite) (hsub : MulAction.orbit G x ⊆ Y) :
    Nat.card G ≤ Y.ncard * Nat.card (MulAction.stabilizer G x) := by
  rw [← Subgroup.card_mul_index (MulAction.stabilizer G x), MulAction.index_stabilizer, mul_comm]
  exact Nat.mul_le_mul_right _ (Set.ncard_le_ncard hsub hY)

theorem card_le_two_of_subset {H : Type*} [Group H] {K : Subgroup H} {a b : H}
    (h : (K : Set H) ⊆ {a, b}) : Nat.card K ≤ 2 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  exact (Set.ncard_le_ncard h (Set.toFinite _)).trans
    ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))

theorem fi22_card_centralizer_of_not_mem_D
    {f : CFSG.Sporadic.Fi22.J} (hf2 : f * f = 1)
    (hf1 : f ≠ 1) (hfD : f ∉ CFSG.Sporadic.Fi22.D) :
    Nat.card ↥(Subgroup.centralizer ({f} : Set CFSG.Sporadic.Fi22.J)) ≤ 53084160 := by
  set τ : fi22P := fi22PJ.symm f
  have hτP : (τ : Equiv.Perm (Fin 3510)) ∈ fi22P := τ.2
  have hτ : orderOf (τ : Equiv.Perm (Fin 3510)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact hf2) hf1
  obtain ⟨k, hk, r, hr, hrτ⟩ := fi22R_involution_conj (fi22P_le_R hτP) hτ
  have hrn := fi22R_le_normalizer hr
  have hkP : fi22ExtRep k ∈ fi22P := by
    rw [← hrτ]
    exact (Subgroup.mem_normalizer_iff.1 hrn _).1 hτP
  have hk3 : k < 3 := by
    by_contra h
    obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
    exact (CTUC_Fi22_all_extension_involutions_covered.2.1 j (by omega)).2 hkP
  have e1 := @centralizerMulEquiv CFSG.Sporadic.Fi22.J fi22P inferInstance inferInstance
    fi22PJ.symm f
  have e2 : ↥(Subgroup.centralizer ({fi22PJ.symm f} : Set fi22P)) ≃*
      ↥(fi22P ⊓ Subgroup.centralizer {(τ : Equiv.Perm (Fin 3510))}) :=
    (infCentralizerEquiv fi22P hτP).symm
  have e3 : ↥(fi22P ⊓ Subgroup.centralizer {(τ : Equiv.Perm (Fin 3510))}) ≃*
      ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep k}) :=
    (fi22CP_conj_equiv hrn _).trans (MulEquiv.subgroupCongr (by rw [hrτ]))
  rw [Nat.card_congr ((e1.trans e2).trans e3).toEquiv]
  obtain ⟨h0, h1, -⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  interval_cases k
  · rw [h0, card_fi22H_zero]
    norm_num
  · rw [h1, card_fi22H_one]
  · exfalso
    apply hfD
    have hrin : r⁻¹ ∈ Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))) :=
      Subgroup.inv_mem _ hrn
    have hα : normalizerConj hrin fi22OuterZP = τ := by
      apply Subtype.ext
      rw [normalizerConj_apply, fi22OuterZP_eq]
      change r⁻¹ * fi22OuterZ * r⁻¹⁻¹ = (τ : Equiv.Perm (Fin 3510))
      rw [← fi22ExtRep_two, ← hrτ]
      group
    have hzτ := (fi22P_aut_class (normalizerConj hrin)).1
    rw [hα] at hzτ
    have hyτ : IsConj fi22Ya τ := isConj_fi22OuterZP_fi22Ya.symm.trans hzτ
    have := MonoidHom.map_isConj
      (@MulEquiv.toMonoidHom fi22P CFSG.Sporadic.Fi22.J inferInstance inferInstance fi22PJ) hyτ
    rw [MulEquiv.coe_toMonoidHom, fi22Ya, MulEquiv.apply_symm_apply,
      show fi22PJ τ = f from MulEquiv.apply_symm_apply fi22PJ f] at this
    exact this

open CFSG.Sporadic.Fi23 in
theorem fi23_card_centralizer_Cd_t2 :
    Nat.card ↥(Subgroup.centralizer ({⟨t2, fi23_t2_mem_Cd⟩} : Set Cd)) ≤ 2 * 53084160 := by
  set t' : Cd := ⟨t2, fi23_t2_mem_Cd⟩
  set L := Subgroup.centralizer ({t'} : Set Cd)
  have hf2 : fi23Kappa t' * fi23Kappa t' = 1 := by
    rw [← map_mul, show (t' * t' : Cd) = 1 from
      Subtype.ext (show t2 * t2 = 1 by rw [← sq]; exact t2_sq), map_one]
  have hf1 : fi23Kappa t' ≠ 1 := fun h => by
    rcases fi23Kappa_eq_one h with h1 | h1
    · exact ne_one_of_isIdT rep_XCT invParts.C_ne h1
    · exact fi23_t2_not_mem (show t2 ∈ D23 by rw [show t2 = d from h1]; exact IsConj.refl _)
  have hF := fi22_card_centralizer_of_not_mem_D hf2 hf1 fi23Kappa_t2_not_mem
  let ρ : ↥L →* ↥(Subgroup.centralizer ({fi23Kappa t'} : Set CFSG.Sporadic.Fi22.J)) :=
    { toFun := fun c => ⟨fi23Kappa c, by
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.1 c.2]⟩
      map_one' := Subtype.ext (map_one fi23Kappa)
      map_mul' := fun x y => Subtype.ext (map_mul fi23Kappa (x : Cd) (y : Cd)) }
  have hdCd : d ∈ Cd := mem_Cd.2 rfl
  have hdL : (⟨d, hdCd⟩ : Cd) ∈ L := Subgroup.mem_centralizer_singleton_iff.2
    (Subtype.ext (mem_Cd.1 fi23_t2_mem_Cd).symm)
  have hker : (ρ.ker : Set ↥L) ⊆ {1, ⟨⟨d, hdCd⟩, hdL⟩} := by
    intro x hx
    have h1 : fi23Kappa (x : Cd) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    rcases fi23Kappa_eq_one h1 with h | h
    · left
      exact Subtype.ext (Subtype.ext h)
    · right
      exact Subtype.ext (Subtype.ext h)
  have hk2 := card_le_two_of_subset hker
  have hcard := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker] at hcard
  have hr := Subgroup.card_le_card_group ρ.range
  rw [← hcard]
  exact Nat.mul_le_mul hk2 (hr.trans hF)

open CFSG.Sporadic.Fi23 in
theorem fi23_card_centralizer_t2 :
    Nat.card ↥(Subgroup.centralizer ({t2} : Set J)) ≤ 318504960 := by
  classical
  set C2 := Subgroup.centralizer ({t2} : Set J)
  set Y : Set J := {d, d1, c39}
  let act : MulAction ↥C2 ↥Y :=
    { smul := fun c y => ⟨(c : J) * y * (c : J)⁻¹, fi23_triple_invariant c c.2 y y.2⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : C2) : J) * (y : J) * ((1 : C2) : J)⁻¹ = y
        simp)
      mul_smul := fun c e y => Subtype.ext (by
        show ((c * e : C2) : J) * (y : J) * ((c * e : C2) : J)⁻¹ =
          (c : J) * ((e : J) * (y : J) * (e : J)⁻¹) * (c : J)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  have hdY : d ∈ Y := Set.mem_insert _ _
  have h1 := card_le_ncard_mul_card_stabilizer (G := ↥C2) (⟨d, hdY⟩ : ↥Y)
    (Set.toFinite (Set.univ : Set ↥Y)) (Set.subset_univ _)
  have hY3 : (Set.univ : Set ↥Y).ncard ≤ 3 := by
    rw [Set.ncard_univ, Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le _ _).trans (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans
      (by rw [Set.ncard_singleton])))
  have hst : Nat.card ↥(MulAction.stabilizer ↥C2 (⟨d, hdY⟩ : ↥Y)) ≤
      Nat.card ↥(Subgroup.centralizer ({⟨t2, fi23_t2_mem_Cd⟩} : Set Cd)) := by
    have hfix : ∀ c : ↥(MulAction.stabilizer ↥C2 (⟨d, hdY⟩ : ↥Y)),
        ((c : C2) : J) * d = d * ((c : C2) : J) := fun c => by
      have h := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 c.2)
      change ((c : C2) : J) * d * ((c : C2) : J)⁻¹ = d at h
      calc ((c : C2) : J) * d = ((c : C2) : J) * d * ((c : C2) : J)⁻¹ * ((c : C2) : J) := by
            group
        _ = d * ((c : C2) : J) := by rw [h]
    refine Nat.card_le_card_of_injective
      (fun c => ⟨⟨((c : C2) : J), mem_Cd.2 (hfix c)⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
          (Subgroup.mem_centralizer_singleton_iff.1 (c : C2).2))⟩) ?_
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab)
  calc Nat.card ↥C2 ≤ (Set.univ : Set ↥Y).ncard *
        Nat.card ↥(MulAction.stabilizer ↥C2 (⟨d, hdY⟩ : ↥Y)) := h1
    _ ≤ 3 * (2 * 53084160) := Nat.mul_le_mul hY3 (hst.trans fi23_card_centralizer_Cd_t2)
    _ = 318504960 := by norm_num

end CFSG.Sporadic.FischerOddCore
