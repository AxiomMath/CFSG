module

public import CFSG.Sporadic.HeldB.CertPBridge
public import CFSG.Sporadic.Schreier.PairHeClasses
public import CFSG.Sporadic.Schreier.PairOuterClass
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.He

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem he_patRel_iff {G : Type*} [Group G] {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 7) :
    PatRel PairHe.conds x y ↔ orderOf (x * y) = 17 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 6 ∧
      orderOf (x * y ^ 2) = 12 ∧ orderOf (x * y * x * y ^ 2) = 15 := by
  have hx2 : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← hx, pow_orderOf_eq_one])
  have hy7 : y⁻¹ = y ^ 6 :=
    inv_eq_of_mul_eq_one_right (by
      rw [← pow_succ', show 6 + 1 = orderOf y by rw [hy], pow_orderOf_eq_one])
  have e1 : ([false, true].map fun b => if b then y else x).prod = x * y := by
    simp
  have e2 : (PairHe.commPat.map fun b => if b then y else x).prod = x * y * x⁻¹ * y⁻¹ := by
    rw [hx2, hy7]
    simp only [PairHe.commPat, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, ↓reduceIte, mul_one, pow_succ, pow_zero, one_mul, mul_assoc]
  have e3 : (PairHe.pat12.map fun b => if b then y else x).prod = x * y ^ 2 := by
    simp only [PairHe.pat12, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, ↓reduceIte, mul_one, pow_succ, pow_zero, one_mul]
  have e4 : (PairHe.pat15.map fun b => if b then y else x).prod = x * y * x * y ^ 2 := by
    simp only [PairHe.pat15, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, ↓reduceIte, mul_one, pow_succ, pow_zero, one_mul, mul_assoc]
  unfold PatRel
  rw [show PairHe.conds = [([false, true], 17), (PairHe.commPat, 6), (PairHe.pat12, 12),
    (PairHe.pat15, 15)] from rfl]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  rw [e1, e2, e3, e4]

@[expose] def hea0 : heP := ⟨heGenPerm 0, heGenPerm_mem (by norm_num)⟩

@[expose] def hea1 : heP := ⟨heGenPerm 1, heGenPerm_mem (by norm_num)⟩

theorem heT1_memP : heT1 ∈ heP := by
  rw [heP_eq_originalSubgroup]
  exact heT1_mem

@[expose] def het1 : heP := ⟨heT1, heT1_memP⟩

theorem mem_orig_of_heP (x : heP) : (x : Equiv.Perm (Fin 8330)) ∈ heChain.originalSubgroup :=
  heP_eq_originalSubgroup ▸ x.2

theorem he_isConj_iff (a x : heP) : IsConj a x ↔
    ∃ d ∈ heChain.originalSubgroup, (x : Equiv.Perm (Fin 8330)) = d * a * d⁻¹ := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, mem_orig_of_heP c, rfl⟩
  · rintro ⟨d, hd, hx⟩
    refine ⟨⟨d, heP_eq_originalSubgroup ▸ hd⟩, Subtype.ext ?_⟩
    rw [hx]
    rfl

theorem orderOf_hea0 :
    orderOf hea0 = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_heGenPerm_zero

theorem orderOf_het1 :
    orderOf het1 = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_heT1

theorem he_orderOf_of_isConj {a x : heP} (h : IsConj a x) : orderOf x = orderOf a := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem he_isConj_a0_iff
    (x : heP) : IsConj hea0 x ↔ (x : Equiv.Perm (Fin 8330)) ∈ heE1 := by
  rw [he_isConj_iff]
  exact he_conj_a0_iff (mem_orig_of_heP x)

theorem he_isConj_t1_iff
    (x : heP) : IsConj het1 x ↔ (x : Equiv.Perm (Fin 8330)) ∈ heE2 := by
  rw [he_isConj_iff]
  exact he_conj_t1_iff (mem_orig_of_heP x)

theorem he_card_conj_eq {a : heP} {E : List (Equiv.Perm (Fin 8330))} (hE : E.Nodup)
    (h : ∀ x : heP, IsConj a x ↔ (x : Equiv.Perm (Fin 8330)) ∈ E)
    (hsub : ∀ e ∈ E, e ∈ heP) : Nat.card {x : heP // IsConj a x} = E.length := by
  refine card_eq_length _ Subtype.val Subtype.val_injective E hE fun b => ?_
  constructor
  · intro hb
    exact ⟨⟨b, hsub b hb⟩, (h _).2 hb, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx

theorem heE1_sub :
    ∀ e ∈ heE1, e ∈ heP := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := heE1_conj e he
  rw [heP_eq_originalSubgroup]
  exact mul_mem (mul_mem hd (heGenPerm_mem_orig (by norm_num))) (inv_mem hd)

theorem heE2_sub :
    ∀ e ∈ heE2, e ∈ heP := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := heE2_conj e he
  rw [heP_eq_originalSubgroup]
  exact mul_mem (mul_mem hd heT1_mem) (inv_mem hd)

@[expose] def HeImagePair (x y : heP) : Prop :=
  orderOf x = 2 ∧ orderOf y = 7 ∧ orderOf (x * y) = 17 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 6 ∧
    orderOf (x * y ^ 2) = 12 ∧ orderOf (x * y * x * y ^ 2) = 15

theorem heImagePair_iff {x y : heP} (hx : orderOf x = 2) :
    HeImagePair x y ↔ orderOf (y : Equiv.Perm (Fin 8330)) = 7 ∧
      PatRel PairHe.conds (x : Equiv.Perm (Fin 8330)) y := by
  rw [Subgroup.orderOf_coe, patRel_coe, HeImagePair]
  constructor
  · rintro ⟨-, hy, h⟩
    exact ⟨hy, (he_patRel_iff hx hy).2 h⟩
  · rintro ⟨hy, h⟩
    exact ⟨hx, hy, (he_patRel_iff hx hy).1 h⟩

theorem he_card_partners {x : heP} (hx : orderOf x = 2) :
    Nat.card {y : heP // HeImagePair x y} = hePartners x := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun y => heImagePair_iff hx), hePartners]
  exact Nat.card_congr ((MulEquiv.subgroupCongr heP_eq_originalSubgroup).toEquiv.subtypeEquiv
    fun _ => Iff.rfl)

theorem AT_He_image_pair_count :
    orderOf (heGenPerm 0) = 2 ∧ orderOf (heGenPerm 1) = 7 ∧
      orderOf (heGenPerm 0 * heGenPerm 1) = 17 ∧
      orderOf (heGenPerm 0 * heGenPerm 1 * (heGenPerm 0)⁻¹ * (heGenPerm 1)⁻¹) = 6 ∧
      orderOf (heGenPerm 0 * heGenPerm 1 ^ 2) = 12 ∧
      orderOf (heGenPerm 0 * heGenPerm 1 * heGenPerm 0 * heGenPerm 1 ^ 2) = 15 ∧
      Nat.card {x : heP // orderOf x = 2} = 212415 ∧
      (∃ r : heP, orderOf r = 2 ∧ ¬IsConj hea0 r ∧
        (∀ x : heP, orderOf x = 2 ↔ IsConj hea0 x ∨ IsConj r x) ∧
        Nat.card {x : heP // IsConj hea0 x} = 24990 ∧
        Nat.card {x : heP // IsConj r x} = 187425) ∧
      (∀ x : heP, IsConj hea0 x → Nat.card {y : heP // HeImagePair x y} ≤ 322560) ∧
      Nat.card {p : heP × heP // IsConj hea0 p.1 ∧ HeImagePair p.1 p.2} ≤ 8060774400 := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := PairHe.word_orders
  have ha := heGenPerm_mem_orig (by norm_num : 0 < 2)
  have hb := heGenPerm_mem_orig (by norm_num : 1 < 2)
  have o1 := he_orderOf_of_word repW_hewA ha (by norm_num) w1
  have o2 := he_orderOf_of_word repW_hewB hb (by norm_num) w2
  have hpat : ∀ pat : List Bool, RepW 8330 (patW PairHe.wA PairHe.wB pat)
      (pat.map fun b => if b then heGenPerm 1 else heGenPerm 0).prod :=
    repW_patW repW_hewA repW_hewB
  have hmem : ∀ pat : List Bool,
      (pat.map fun b => if b then heGenPerm 1 else heGenPerm 0).prod ∈ heChain.originalSubgroup :=
    fun pat => patProd_mem _ ha hb pat
  have hrel : PatRel PairHe.conds (heGenPerm 0) (heGenPerm 1) := by
    intro c hc
    rw [show PairHe.conds = [([false, true], 17), (PairHe.commPat, 6), (PairHe.pat12, 12),
      (PairHe.pat15, 15)] from rfl] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact he_orderOf_of_word (hpat _) (hmem _) (by norm_num) w3
    · exact he_orderOf_of_word (hpat _) (hmem _) (by norm_num) w4
    · exact he_orderOf_of_word (hpat _) (hmem _) (by norm_num) w5
    · exact he_orderOf_of_word (hpat _) (hmem _) (by norm_num) w6
  obtain ⟨o3, o4, o5, o6⟩ := (he_patRel_iff o1 o2).1 hrel
  have h2 := he_card_order 2 (by norm_num)
  rw [PairHe.count_two, ← heP_eq_originalSubgroup] at h2
  have hnd := List.nodup_append.1 he_entries_nodup
  have hc1 : Nat.card {x : heP // IsConj hea0 x} = 24990 := by
    rw [he_card_conj_eq hnd.1 he_isConj_a0_iff heE1_sub, heE1_length]
  have hc2 : Nat.card {x : heP // IsConj het1 x} = 187425 := by
    rw [he_card_conj_eq hnd.2.1 he_isConj_t1_iff heE2_sub, heE2_length]
  have hnc : ¬IsConj hea0 het1 := by
    rw [he_isConj_iff]
    rintro ⟨d, hd, h⟩
    exact heT1_not_conj hd h
  have hcover : ∀ x : heP, orderOf x = 2 ↔ IsConj hea0 x ∨ IsConj het1 x := by
    intro x
    constructor
    · intro hx
      rw [← Subgroup.orderOf_coe] at hx
      rcases he_invol_cover (mem_orig_of_heP x) hx with h | h
      · exact Or.inl ((he_isConj_a0_iff x).2 h)
      · exact Or.inr ((he_isConj_t1_iff x).2 h)
    · rintro (h | h)
      · rw [he_orderOf_of_isConj h, orderOf_hea0]
      · rw [he_orderOf_of_isConj h, orderOf_het1]
  have hpa : ∀ x : heP, IsConj hea0 x → Nat.card {y : heP // HeImagePair x y} ≤ 322560 := by
    intro x hx
    rw [he_card_partners (by rw [he_orderOf_of_isConj hx, orderOf_hea0])]
    obtain ⟨d, hd, hxd⟩ := (he_isConj_iff _ _).1 hx
    rw [hxd, hePartners_conj hd]
    exact hePartners_a0_le
  have hT : Nat.card {p : heP × heP // IsConj hea0 p.1 ∧ HeImagePair p.1 p.2} ≤ 8060774400 := by
    refine (card_pairs_le_of_class hpa).trans (Nat.le_of_eq ?_)
    rw [hc1]
  exact ⟨o1, o2, o3, o4, o5, o6, h2, ⟨het1, orderOf_het1, hnc, hcover, hc1, hc2⟩, hpa, hT⟩

theorem AT_He_Schreier :
    Nat.card (Outer Blueprint.NativeSporadic.He) ≤ 2 ∧
      IsMulCommutative (Outer Blueprint.NativeSporadic.He) ∧
      Group.IsSolvable (Outer Blueprint.NativeSporadic.He) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, -, ⟨r, -, -, hcov, hc1, hc2⟩, -, hT⟩ := AT_He_image_pair_count
  have ha : orderOf hea0 = 2 := orderOf_hea0
  have hb : orderOf hea1 = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact o2
  have hrel : PatRel PairHe.conds hea0 hea1 := by
    rw [he_patRel_iff ha hb]
    simp only [← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact ⟨o3, o4, o5, o6⟩
  have hcomm : hea0 * hea1 ≠ hea1 * hea0 := by
    refine mul_ne_mul_of_orderOf_commutator (s := 6) ?_ (by norm_num)
    rw [← Subgroup.orderOf_coe]
    exact o4
  have hgen : Subgroup.closure ({hea0, hea1} : Set heP) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top (by rw [heP]) _ _
  have hcls : ∀ x : heP, orderOf x = 2 →
      Nat.card {y : heP // IsConj x y} = Nat.card {y : heP // IsConj hea0 y} → IsConj hea0 x := by
    intro x hx hxc
    refine ((hcov x).1 hx).resolve_right fun hrx => ?_
    have e : Nat.card {y : heP // IsConj x y} = Nat.card {y : heP // IsConj r y} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun y =>
        ⟨fun h => hrx.trans h, fun h => (isConj_comm.1 hrx).trans h⟩)
    rw [e, hc1, hc2] at hxc
    exact absurd hxc (by norm_num)
  have hT' : Nat.card {p : heP × heP //
      Nat.card {x : heP // IsConj p.1 x} = Nat.card {x : heP // IsConj hea0 x} ∧
      orderOf p.1 = orderOf hea0 ∧ orderOf p.2 = orderOf hea1 ∧ PatRel PairHe.conds p.1 p.2} ≤
      8060774400 := by
    have hmap : ∀ p : heP × heP,
        (Nat.card {x : heP // IsConj p.1 x} = Nat.card {x : heP // IsConj hea0 x} ∧
          orderOf p.1 = orderOf hea0 ∧ orderOf p.2 = orderOf hea1 ∧
          PatRel PairHe.conds p.1 p.2) → IsConj hea0 p.1 ∧ HeImagePair p.1 p.2 := by
      rintro p ⟨h0, h1, h2, h3⟩
      rw [ha] at h1
      rw [hb] at h2
      refine ⟨hcls _ h1 h0, ?_⟩
      rw [HeImagePair]
      exact ⟨h1, h2, (he_patRel_iff h1 h2).1 h3⟩
    exact le_trans (Nat.card_le_card_of_injective (fun p => ⟨p.1, hmap p.1 p.2⟩)
      fun p q h => Subtype.ext (by injection h)) hT
  have hP : Nat.card (Outer heP) ≤ 2 :=
    outer_card_le_of_classPatCounts heP_simple hgen hcomm PairHe.conds hrel card_heP
      (by norm_num) hT' (k := 2) (by norm_num)
  have : Finite Blueprint.NativeSporadic.He := CFSG.Sporadic.He.fam_he_simplicity.1
  have hcard : Nat.card (Outer Blueprint.NativeSporadic.He) ≤ 2 :=
    outer_card_le_of_equiv (G := Blueprint.NativeSporadic.He) hP heEquivP
  exact ⟨hcard, commutative_of_card_le_four (hcard.trans (by norm_num)),
    solvable_of_card_le_four (hcard.trans (by norm_num))⟩

end CFSG.Sporadic.Schreier
