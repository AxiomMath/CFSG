module

public import CFSG.Sporadic.FischerOddCore.Fi23LocalComp
public import CFSG.Sporadic.FischerOddCore.NoCompLemmas

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.LocalCores CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

section Triple

open CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer

theorem fi23_c39_mem :
    c39 ∈ D23 := (isConj_d_iff _).2 ⟨⟨39, by norm_num⟩, rfl⟩

theorem fi23_c39_local_d :
    c39 ∈ LocalClass D23 d := by
  refine ⟨fi23_c39_mem, fun h => ?_, c39_commute_d⟩
  have h' : conjPt 39 = conjPt 0 := by rw [conjPt_zero]; exact h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h')
    (by norm_num)

theorem fi23_c39_local_d1 :
    c39 ∈ LocalClass D23 d1 := by
  refine ⟨fi23_c39_mem, fun h => ?_, c39_commute_d1⟩
  have h' : conjPt 39 = conjPt 1 := h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h')
    (by norm_num)

theorem fi23_t2_comm_d :
    d * t2 = t2 * d := by
  unfold t2
  calc d * (d * d1 * c39) = d * (d * d1) * c39 := by group
    _ = d * (d1 * d) * c39 := by rw [d1_commute]
    _ = d * d1 * (d * c39) := by group
    _ = d * d1 * (c39 * d) := by rw [c39_commute_d]
    _ = d * d1 * c39 * d := by group

theorem fi23_t2_comm_d1 :
    d1 * t2 = t2 * d1 := by
  unfold t2
  calc d1 * (d * d1 * c39) = d1 * d * d1 * c39 := by group
    _ = d * d1 * d1 * c39 := by rw [d1_commute]
    _ = d * d1 * (d1 * c39) := by group
    _ = d * d1 * (c39 * d1) := by rw [c39_commute_d1]
    _ = d * d1 * c39 * d1 := by group

theorem fi23_t2_comm_c39 :
    c39 * t2 = t2 * c39 := by
  unfold t2
  calc c39 * (d * d1 * c39) = c39 * d * d1 * c39 := by group
    _ = d * c39 * d1 * c39 := by rw [c39_commute_d]
    _ = d * (c39 * d1) * c39 := by group
    _ = d * (d1 * c39) * c39 := by rw [c39_commute_d1]
    _ = d * d1 * c39 * c39 := by group

theorem fi23_c39_sq : c39 * c39 = 1 := by rw [← sq]; exact c39_sq

theorem fi23_d1_sq : d1 * d1 = 1 := by rw [← sq]; exact d1_sq

theorem fi23_mul_t2_isConj
    {y : J} (hy : y = d ∨ y = d1 ∨ y = c39) : IsConj (d * d1) (y * t2) := by
  rcases hy with rfl | rfl | rfl
  · have e : d * t2 = d1 * c39 := by
      unfold t2
      rw [← mul_assoc, ← mul_assoc, d_sq, one_mul]
    rw [e]
    exact isConj_d_mul_d1_of_mem fi23_d1_mem fi23_c39_local_d1
  · have e : d1 * t2 = d * c39 := by
      unfold t2
      calc d1 * (d * d1 * c39) = d1 * d * d1 * c39 := by group
        _ = d * d1 * d1 * c39 := by rw [d1_commute]
        _ = d * (d1 * d1) * c39 := by group
        _ = d * c39 := by rw [fi23_d1_sq, mul_one]
    rw [e]
    exact isConj_d_mul_d1_of_mem (IsConj.refl d) fi23_c39_local_d
  · have e : c39 * t2 = d * d1 := by
      rw [fi23_t2_comm_c39]
      unfold t2
      rw [mul_assoc, fi23_c39_sq, mul_one]
    rw [e]

theorem fi23_triple_mem
    {c : J} (hc : c * t2 = t2 * c) {y : J}
    (hy : y = d ∨ y = d1 ∨ y = c39) :
    c * y * c⁻¹ = d ∨ c * y * c⁻¹ = d1 ∨ c * y * c⁻¹ = c39 := by
  have hyD : y ∈ D23 := by
    rcases hy with rfl | rfl | rfl
    · exact IsConj.refl _
    · exact fi23_d1_mem
    · exact fi23_c39_mem
  have hyt : y * t2 = t2 * y := by
    rcases hy with rfl | rfl | rfl
    · exact fi23_t2_comm_d
    · exact fi23_t2_comm_d1
    · exact fi23_t2_comm_c39
  obtain ⟨⟨k, hk⟩, hxk0⟩ := (isConj_d_iff _).1 (conj_mem_D23 c y hyD)
  have hxk : conjPt k = c * y * c⁻¹ := hxk0
  have hcc : c⁻¹ * t2 * c = t2 := by rw [mul_assoc, ← hc]; group
  have hfix : conjPt k * t2 = t2 * conjPt k := by
    rw [hxk]
    calc c * y * c⁻¹ * t2 = c * (y * (c⁻¹ * t2 * c)) * c⁻¹ := by group
      _ = c * (y * t2) * c⁻¹ := by rw [hcc]
      _ = c * (t2 * y) * c⁻¹ := by rw [hyt]
      _ = c * t2 * (y * c⁻¹) := by group
      _ = t2 * c * (y * c⁻¹) := by rw [hc]
      _ = t2 * (c * y * c⁻¹) := by group
  have hap : ap XCT k = k := ap_eq_of_commute rep_XCT hk hfix
  have hconj : IsConj (d * d1) (conjPt k * t2) := by
    rw [hxk]
    have e : c * y * c⁻¹ * t2 = c * (y * t2) * c⁻¹ := by
      calc c * y * c⁻¹ * t2 = c * (y * (c⁻¹ * t2 * c)) * c⁻¹ := by group
        _ = c * (y * t2) * c⁻¹ := by rw [hcc]
    rw [e]
    exact (fi23_mul_t2_isConj hy).trans ((isConj_iff (α := J)).2 ⟨c, rfl⟩)
  have hcount : CFSG.Sporadic.Fi23.Native.fixCount (compT 31671 (ptT k) XCT) = 695 := by
    rw [← card_fixed_eq (Rep.compT (rep_ptT k) rep_XCT), ← card_fixed_conj hconj,
      card_fixed_d_mul_d1]
  have hcert := fi23Trip_certificate
  unfold fi23TripOK at hcert
  dsimp only at hcert
  have h := allIn_eq_true.1 hcert k (Nat.zero_le _) hk
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · left
    rw [← hxk]
    subst h
    exact conjPt_zero
  · right; left
    rw [← hxk]
    subst h
    rfl
  · right; right
    rw [← hxk]
    subst h
    rfl
  · exact absurd hap h
  · exact absurd hcount h

theorem fi23_triple_invariant :
    ∀ c ∈ Subgroup.centralizer ({t2} : Set J),
    ∀ y ∈ ({d, d1, c39} : Set J), c * y * c⁻¹ ∈ ({d, d1, c39} : Set J) := by
  intro c hc y hy
  have hy' : y = d ∨ y = d1 ∨ y = c39 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy
  have h := fi23_triple_mem ((Subgroup.mem_centralizer_singleton_iff (G := J)).1 hc) hy'
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

theorem fi23_t2_mem_Cd :
    t2 ∈ Cd := mem_Cd.2 fi23_t2_comm_d.symm

theorem fi23_t2_not_mem :
    t2 ∉ D23 := fun h => by
  have := card_fixed_conj (h : IsConj d t2)
  rw [card_fixed_d, card_fixed_t2] at this
  omega

theorem fi23_d_t2_not_mem :
    d * t2 ∉ D23 := fun h => by
  have h1 := card_fixed_conj (h : IsConj d (d * t2))
  have h2 := card_fixed_conj (fi23_mul_t2_isConj (Or.inl rfl))
  rw [card_fixed_d, ← h2, card_fixed_d_mul_d1] at h1
  omega

end Triple

theorem fi23Kappa_t2_not_mem :
    fi23Kappa ⟨CFSG.Sporadic.Fi23.t2, fi23_t2_mem_Cd⟩ ∉ CFSG.Sporadic.Fi22.D := by
  intro h
  obtain ⟨k, hk, hke⟩ := CFSG.Sporadic.Fi22.mem_D_iff.1 h
  have hi := CFSG.Sporadic.Fi23.phiP_lt hk
  have hx : fi23Kappa (CFSG.Sporadic.Fi23.starCd _ hi) = CFSG.Sporadic.Fi22.conjPt k :=
    CFSG.Sporadic.Fi23.pi22_injective (by
      rw [fi23Kappa_apply, CFSG.Sporadic.Fi23.pi22_quotCenterEquiv,
        CFSG.Sporadic.Fi23.rho_starCd, CFSG.Sporadic.Fi23.phiD_phiP hk])
  have hstar : (CFSG.Sporadic.Fi23.starCd _ hi : CFSG.Sporadic.Fi23.J) ∈
      CFSG.Sporadic.Fi23.D23 :=
    (CFSG.Sporadic.Fi23.conjPt_mem_star (CFSG.Sporadic.Fi23.ea_get_mem hi)).1
  have hk1 : fi23Kappa (⟨CFSG.Sporadic.Fi23.t2, fi23_t2_mem_Cd⟩ *
      (CFSG.Sporadic.Fi23.starCd _ hi)⁻¹) = 1 := by
    rw [map_mul, map_inv, hke, hx, mul_inv_cancel]
  rcases fi23Kappa_eq_one hk1 with h1 | h1
  · apply fi23_t2_not_mem
    have e : CFSG.Sporadic.Fi23.t2 = (CFSG.Sporadic.Fi23.starCd _ hi : CFSG.Sporadic.Fi23.J) := by
      have h1' : CFSG.Sporadic.Fi23.t2 *
          (CFSG.Sporadic.Fi23.starCd _ hi : CFSG.Sporadic.Fi23.J)⁻¹ = 1 := h1
      exact mul_inv_eq_one.1 h1'
    rw [e]
    exact hstar
  · apply fi23_d_t2_not_mem
    have h1' : CFSG.Sporadic.Fi23.t2 *
        (CFSG.Sporadic.Fi23.starCd _ hi : CFSG.Sporadic.Fi23.J)⁻¹ = CFSG.Sporadic.Fi23.d := h1
    have h2 : CFSG.Sporadic.Fi23.t2 =
        CFSG.Sporadic.Fi23.d * (CFSG.Sporadic.Fi23.starCd _ hi : CFSG.Sporadic.Fi23.J) := by
      rw [← h1']
      group
    have e : CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.t2 =
        (CFSG.Sporadic.Fi23.starCd _ hi : CFSG.Sporadic.Fi23.J) := by
      rw [h2, ← mul_assoc, CFSG.Sporadic.Fi23.d_sq, one_mul]
    rw [e]
    exact hstar

@[expose] def normalizerConj {G : Type*} [Group G] {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) : MulAut P where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.1 hg _).2 (by
    rw [show g * (g⁻¹ * (x : G) * g) * g⁻¹ = x by group]; exact x.2)⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv x := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem normalizerConj_apply {G : Type*} [Group G] {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (x : P) :
    ((normalizerConj hg x : P) : G) = g * x * g⁻¹ := rfl

theorem isSolvable_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Group.IsSolvable B) : Group.IsSolvable A :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem fi22H_one_selfCentralizing :
    ∃ Q : Subgroup ↥(fi22H 1), Q.Normal ∧ IsPGroup 2 Q ∧
      Subgroup.centralizer (Q : Set ↥(fi22H 1)) ≤ Q := by
  obtain ⟨⟨Q, hQle, hQn, hQcard, hQc⟩, -⟩ :=
    CTI_Fi22_second_involution_centralizer_normal_two_subgroup
  refine ⟨Q.subgroupOf (fi22H 1), hQn, ?_, ?_⟩
  · apply IsPGroup.of_card (n := 10)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv, hQcard]
    norm_num
  · intro y hy
    rw [Subgroup.mem_subgroupOf]
    apply hQc
    refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := Subgroup.mem_centralizer_iff.1 hy ⟨q, hQle hq⟩ (Subgroup.mem_subgroupOf.2 hq)
    exact congrArg Subtype.val this

theorem fi22_centralizer_of_not_mem_D
    {f : CFSG.Sporadic.Fi22.J} (hf2 : f * f = 1)
    (hf1 : f ≠ 1) (hfD : f ∉ CFSG.Sporadic.Fi22.D) :
    (∃ Q : Subgroup ↥(Subgroup.centralizer ({f} : Set CFSG.Sporadic.Fi22.J)), Q.Normal ∧
        IsPGroup 2 Q ∧ Subgroup.centralizer (Q : Set _) ≤ Q) ∨
      Group.IsSolvable ↥(Subgroup.centralizer ({f} : Set CFSG.Sporadic.Fi22.J)) := by
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
  obtain ⟨h0, h1, -⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  interval_cases k
  · right
    have e := ((e1.trans e2).trans e3).trans (MulEquiv.subgroupCongr h0)
    have hs : Group.IsSolvable (fi22H 0) :=
      CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two (by
        rw [card_fi22H_zero]; exact
        primeFactors_card_fi22H_zero)
    exact @isSolvable_of_mulEquiv ↥(Subgroup.centralizer ({f} : Set CFSG.Sporadic.Fi22.J))
      (fi22H 0) inferInstance inferInstance e hs
  · left
    have e := ((e1.trans e2).trans e3).trans (MulEquiv.subgroupCongr h1)
    obtain ⟨Q, hQn, hQ2, hQc⟩ := fi22H_one_selfCentralizing
    exact @exists_selfCentralizing_of_mulEquiv
      ↥(Subgroup.centralizer ({f} : Set CFSG.Sporadic.Fi22.J)) (fi22H 1) inferInstance
      inferInstance e Q hQn hQ2 hQc
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
theorem fi23_no_component_t2
    (B : Subgroup ↥(Subgroup.centralizer ({t2} : Set J))) :
    ¬ IsComponent B := by
  intro hB
  have hY3 : ({d, d1, c39} : Set J).ncard ≤ 3 :=
    (Set.ncard_insert_le _ _).trans (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans
      (by rw [Set.ncard_singleton])))
  have hBd : ∀ b ∈ B, (b : J) * d = d * (b : J) := fun b hb => by
    have h := @conj_eq_of_perfect_of_invariant J inferInstance
      (Subgroup.centralizer ({t2} : Set J)) ({d, d1, c39} : Set J) (Set.toFinite _) hY3
      fi23_triple_invariant B hB.1.1 b hb d (Set.mem_insert _ _)
    calc (b : J) * d = (b : J) * d * (b : J)⁻¹ * (b : J) := by group
      _ = d * (b : J) := by rw [h]
  have hf2 : fi23Kappa ⟨t2, fi23_t2_mem_Cd⟩ * fi23Kappa ⟨t2, fi23_t2_mem_Cd⟩ = 1 := by
    rw [← map_mul, show (⟨t2, fi23_t2_mem_Cd⟩ * ⟨t2, fi23_t2_mem_Cd⟩ : Cd) = 1 from
      Subtype.ext (show t2 * t2 = 1 by rw [← sq]; exact t2_sq), map_one]
  have hf1 : fi23Kappa ⟨t2, fi23_t2_mem_Cd⟩ ≠ 1 := fun h => by
    rcases fi23Kappa_eq_one h with h1 | h1
    · exact ne_one_of_isIdT rep_XCT invParts.C_ne h1
    · exact fi23_t2_not_mem (show t2 ∈ D23 by rw [show t2 = d from h1]; exact IsConj.refl _)
  have hnt : ∀ c : J, c * t2 * c⁻¹ ≠ d * t2 := fun c h => by
    have h1 := card_fixed_conj ((isConj_iff (α := J)).2 ⟨c, h⟩ : IsConj t2 (d * t2))
    have h2 := card_fixed_conj (fi23_mul_t2_isConj (Or.inl rfl))
    rw [card_fixed_t2, ← h2, card_fixed_d_mul_d1] at h1
    omega
  exact @not_isComponent_of_commute J CFSG.Sporadic.Fi22.J inferInstance inferInstance
    inferInstance d t2 d_sq fi23_t2_mem_Cd fi23Kappa fi23Kappa_surjective
    (fun _ hc => fi23Kappa_eq_one hc) hnt
    (fi22_centralizer_of_not_mem_D hf2 hf1 fi23Kappa_t2_not_mem) B hB hBd

end CFSG.Sporadic.FischerOddCore
