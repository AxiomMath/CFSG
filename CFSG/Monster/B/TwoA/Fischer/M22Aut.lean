module

public import CFSG.Monster.B.TwoA.Fischer.M22AutCheck
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Monster.B.TwoA.Base.M22

public noncomputable section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Mathieu CFSG.Monster.B.TwoA
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem card_mulAut_le_five {G : Type*} [Group G] [Finite G] (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    Nat.card (MulAut G) ≤ Nat.card {p : G × G // orderOf p.1 = orderOf a ∧
      orderOf p.2 = orderOf b ∧ orderOf (p.1 * p.2) = orderOf (a * b) ∧
      orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = orderOf (a * b * a⁻¹ * b⁻¹) ∧
      orderOf (p.1 * p.2 * p.2) = orderOf (a * b * b)} := by
  refine Nat.card_le_card_of_injective (fun σ => ⟨(σ a, σ b), ?_⟩) fun σ τ h => ?_
  · simp only [MulEquiv.orderOf_eq, ← map_mul, ← map_inv, and_self]
  · have h' := congrArg Subtype.val h
    exact imagePairEvaluation_injective a b hgen (Subtype.ext h')

theorem card_image_pairs5_eq {n : ℕ} (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {mx my r s t : ℕ} (hmx : 0 < mx) (hmy : 0 < my) (hr : 0 < r)
    (hs : 0 < s) (ht : 0 < t) :
    Nat.card {p : Q.originalSubgroup × Q.originalSubgroup // orderOf p.1 = mx ∧
      orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s ∧
      orderOf (p.1 * p.2 * p.2) = t} =
      pairCount (orderTables Q mx) (orderTables Q my)
        (fun x y => pairTest n r s mx my x y && ordW n [x, y, y] t) := by
  set L := enumeration Q
  have hcoe : ∀ p : Q.originalSubgroup × Q.originalSubgroup,
      (orderOf p.1 = mx ∧ orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s ∧ orderOf (p.1 * p.2 * p.2) = t) ↔
      (orderOf (p.1 : Equiv.Perm (Fin n)) = mx ∧ orderOf (p.2 : Equiv.Perm (Fin n)) = my ∧
        (orderOf ((p.1 : Equiv.Perm (Fin n)) * p.2) = r ∧
          orderOf ((p.1 : Equiv.Perm (Fin n)) * p.2 * (p.1 : Equiv.Perm (Fin n))⁻¹ *
            (p.2 : Equiv.Perm (Fin n))⁻¹) = s ∧
          orderOf ((p.1 : Equiv.Perm (Fin n)) * p.2 * p.2) = t)) := fun p => by
    simp only [← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe),
    card_pairs_eq_sum Q.originalSubgroup L (enumeration_nodup Q hQ) (mem_enumeration_iff Q hQ)
      (fun h => orderOf h = mx) (fun h => orderOf h = my)
      (fun x y => orderOf (x * y) = r ∧ orderOf (x * y * x⁻¹ * y⁻¹) = s ∧
        orderOf (x * y * y) = t),
    pairCount_spec (forall₂_orderTables hn Q hmx) (forall₂_orderTables hn Q hmy)
      (R := fun x y => orderOf (x * y) = r ∧ orderOf (x * y * x⁻¹ * y⁻¹) = s ∧
        orderOf (x * y * y) = t) ?_,
    List.map_reverse, List.sum_reverse]
  · congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [List.countP_reverse]
  · intro x xg y yg hx hy hxg hyg
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hxg hyg
    have hxyy : List.Forall₂ (Rep n) [x, y, y] [xg, yg, yg] :=
      .cons hx (.cons hy (.cons hy .nil))
    rw [Bool.and_eq_true, pairTest_iff perm_faithful hx hy hr hs hxg.2 hyg.2 hmx hmy,
      ordW_iff perm_faithful hxyy ht, and_assoc]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem orderOf_m22a_mul_m22b_mul_m22b :
    orderOf (m22a * m22b * m22b) = 5 := by
  have hw : List.Forall₂ (Rep 22) [toTable m22gA, toTable m22gB, toTable m22gB]
      [m22gA, m22gB, m22gB] :=
    .cons (rep_toTable (by norm_num) _)
      (.cons (rep_toTable (by norm_num) _) (.cons (rep_toTable (by norm_num) _) .nil))
  have h := (ordW_iff perm_faithful hw (by norm_num)).1 m22_word_ab2
  rw [← Subgroup.orderOf_coe]
  simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc, Subgroup.coe_mul] using h

theorem card_m22_pairs5 :
    Nat.card {p : CFSG.Blueprint.NativeSporadic.M22 × CFSG.Blueprint.NativeSporadic.M22 //
      orderOf p.1 = 2 ∧ orderOf p.2 = 4 ∧ orderOf (p.1 * p.2) = 11 ∧
      orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 6 ∧ orderOf (p.1 * p.2 * p.2) = 5} = 887040 := by
  have hT := card_image_pairs5_eq (by norm_num) m22Certificate m22Certificate_check
    (mx := 2) (my := 4) (r := 11) (s := 6) (t := 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [m22_pair5_count, m22Certificate_originalSubgroup] at hT
  exact hT

theorem autEmbed_coe_P0in (p : P0in) :
    autEmbed (p : Ppair) = MulAut.conj (P0inEquiv p) := by
  rw [autEmbed, MonoidHom.comp_apply, MulAut.conjNormal_val, MulEquiv.coe_toMonoidHom,
    congr_conj]

theorem catalog_M22_full_automorphism_order :
    Nat.card (MulAut CFSG.Blueprint.NativeSporadic.M22) = 887040 ∧
    Nat.card (Outer CFSG.Blueprint.NativeSporadic.M22) = 2 ∧
    Nonempty (Outer CFSG.Blueprint.NativeSporadic.M22 ≃* Multiplicative (ZMod 2)) ∧
    Function.Bijective autEmbed ∧
    P0in.map autEmbed = inner CFSG.Blueprint.NativeSporadic.M22 := by
  obtain ⟨hfin, -, hsimple⟩ := fam_m22_simplicity
  obtain ⟨ha, hb, hab, hc, -, -, -⟩ := at_m22_image_pair_count
  have hgen : Subgroup.closure ({m22a, m22b} : Set CFSG.Blueprint.NativeSporadic.M22) = ⊤ :=
    closure_pair_eq_top m22_eq _ _
  have hle := card_mulAut_le_five m22a m22b hgen
  rw [ha, hb, hab, hc, orderOf_m22a_mul_m22b_mul_m22b, card_m22_pairs5] at hle
  have hge : 887040 ≤ Nat.card (MulAut CFSG.Blueprint.NativeSporadic.M22) := by
    rw [← natCard_Ppair]
    exact Nat.card_le_card_of_injective autEmbed autEmbed_injective
  have hcard : Nat.card (MulAut CFSG.Blueprint.NativeSporadic.M22) = 887040 := le_antisymm hle hge
  have hbij : Function.Bijective autEmbed :=
    autEmbed_injective.bijective_of_nat_card_le (by rw [hcard, natCard_Ppair])
  have hmap : P0in.map autEmbed = inner CFSG.Blueprint.NativeSporadic.M22 := by
    ext σ
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨P0inEquiv ⟨p, hp⟩, (autEmbed_coe_P0in ⟨p, hp⟩).symm⟩
    · rintro ⟨g, rfl⟩
      refine ⟨(P0inEquiv.symm g : Ppair), (P0inEquiv.symm g).2, ?_⟩
      rw [autEmbed_coe_P0in, MulEquiv.apply_symm_apply]
  have hinner : Nat.card (inner CFSG.Blueprint.NativeSporadic.M22) = 443520 := by
    rw [card_inner_of_center_eq_bot
      (center_eq_bot_of_simple hsimple (mul_ne_mul_of_orderOf_commutator hc (by norm_num))),
      m22_card]
  have hout : Nat.card (Outer CFSG.Blueprint.NativeSporadic.M22) = 2 := by
    have h := (inner CFSG.Blueprint.NativeSporadic.M22).card_eq_card_quotient_mul_card_subgroup
    rw [hcard, hinner] at h
    change 887040 = Nat.card (Outer CFSG.Blueprint.NativeSporadic.M22) * 443520 at h
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hcard, hout, ⟨mulEquivOfPrimeCardEq hout ?_⟩, hbij, hmap⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

end CFSG.Monster.B.TwoA.Fischer
