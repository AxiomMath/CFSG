module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXJ

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

theorem w16g_three_Q_eq_XSupp (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ9 : Nat.card ↥Q = 9) (he : (s13Supp X Q).ncard = 3) :
    Q = s13XSupp X (s13Supp X Q) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : 3 ≠ 2 := by norm_num
  have hSsub : s13Supp X Q ⊆ s13IsoComps X := fun U hU => hU.1
  have hSne : (s13Supp X Q).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h] at he
    simp at he
  have hQle : Q ≤ s13XSupp X (s13Supp X Q) :=
    (le_s13XSupp_iff h.hW hp3 hp32 h.hXe h.hQX).mpr subset_rfl
  have hlt : Nat.card ↥(s13XSupp X (s13Supp X Q)) < 27 := by
    have h := s13_card_XSupp_lt h.hW hp3 hp32 h.hXe hH0 hSsub hSne
    rw [he] at h
    norm_num at h
    exact h
  have hge : 9 ≤ Nat.card ↥(s13XSupp X (s13Supp X Q)) := by
    rw [← hQ9]
    exact Nat.le_of_dvd (card_subgroup_pos _) (Subgroup.card_dvd_of_le hQle)
  have hpg : IsPGroup 3 ↥(s13XSupp X (s13Supp X Q)) := by
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (h.hXe.2 (x : MulAut W) ((mem_s13XSupp.mp x.2).1))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  have hcard : Nat.card ↥(s13XSupp X (s13Supp X Q)) = 9 := by
    rw [hk] at hge hlt
    have hk_lt : k < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
    have hk_ge : 2 ≤ k := by
      by_contra hk2
      have h01 : k = 0 ∨ k = 1 := by omega
      rcases h01 with h0 | h1
      · rw [h0] at hge; norm_num at hge
      · rw [h1] at hge; norm_num at hge
    have hk_eq : k = 2 := by omega
    rw [hk, hk_eq]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge hQle (by rw [hcard, hQ9])

theorem w16g_three_rk_eq_six (h : HAb A X Q t 3) (he : (s13Supp X Q).ncard = 3) :
    rk ↥(commSub ⊤ Q) = 6 := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : 3 ≠ 2 := by norm_num
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  haveI : Fintype {U : Subgroup W // U ∈ s13Supp X Q} := Fintype.ofFinite _
  rw [rk_commSub_top_eq_sum h.hW hp3 hp32 h.hXe h.hQX]
  rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  have hrank2 : ∀ i : {U : Subgroup W // U ∈ s13Supp X Q}, rk ↥(i.1) = 2 :=
    fun i => (s13_three_ranks h).1 he i.1 i.2
  calc ∑ i : {U : Subgroup W // U ∈ s13Supp X Q}, rk ↥(i.1)
      = ∑ _i : {U : Subgroup W // U ∈ s13Supp X Q}, 2 :=
        Finset.sum_congr rfl (fun i _ => hrank2 i)
    _ = 2 * Nat.card {U : Subgroup W // U ∈ s13Supp X Q} := by
        rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, ← Nat.card_eq_fintype_card,
          mul_comm]
    _ = 2 * (s13Supp X Q).ncard := by rw [Nat.card_coe_set_eq]
    _ = 6 := by rw [he]

theorem w16g_three_inv_ne_bot (h : HAb A X Q t 3) :
    ⁅Q, Subgroup.zpowers t⁆ ≠ ⊥ := by
  intro hbot
  obtain ⟨q, hqQ, hq1⟩ : ∃ q ∈ Q, q ≠ 1 := by
    by_contra hc
    push Not at hc
    exact h.hQ1 (le_bot_iff.mp fun q hq => by rw [Subgroup.mem_bot]; exact hc q hq)
  have hcomm : t * q = q * t :=
    (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) hqQ)) t
      (Subgroup.mem_zpowers t)
  have hfix : t * q * t⁻¹ = q := by
    rw [hcomm]
    group
  have hq_eq_inv : q = q⁻¹ := hfix.symm.trans (h.hQinv q hqQ)
  have hq2 : q * q = 1 := by
    nth_rewrite 2 [hq_eq_inv]
    exact mul_inv_cancel q
  have hq3 : q ^ 3 = 1 := h.hXe.2 q (h.hQX hqQ)
  have hq_one : q = 1 := by
    have h : q = q ^ 3 * (q ^ 2)⁻¹ := by group
    rw [hq3, pow_two, hq2] at h
    simpa using h
  exact hq1 hq_one

private theorem w16g_supp_zpowers_coord {X : Subgroup (MulAut W)} {p : ℕ}
    {lam : s13IsoComps X → Additive ↥X →+ ZMod p} (hl : IsCoord X p lam)
    {z : MulAut W} (hz : z ∈ X) (U : s13IsoComps X) :
    (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers z) ↔
      lam U (Additive.ofMul ⟨z, hz⟩) ≠ 0 := by
  have h1 : (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers z) ↔
      commSub (U : Subgroup W) (Subgroup.zpowers z) ≠ ⊥ := by
    simp only [s13Supp, Set.mem_setOf_eq, U.2, true_and]
  rw [h1]
  exact (coord_ne_zero_iff hl ⟨z, hz⟩ U).symm

private theorem w16g_supp_mono {X : Subgroup (MulAut W)} {L L' : Subgroup (MulAut W)}
    (hLL' : L ≤ L') : s13Supp X L ⊆ s13Supp X L' := by
  intro U hU
  exact ⟨hU.1, fun hbot => hU.2 (le_bot_iff.mp (hbot ▸ commSub_mono le_rfl hLL'))⟩

private theorem w16g_commSub_zpowers_eq_bot_iff {U : Subgroup W} {z : MulAut W} :
    commSub U (Subgroup.zpowers z) = ⊥ ↔ z ∈ centSub U := by
  rw [commSub_eq_bot_iff]
  constructor
  · intro h
    rw [mem_centSub]
    intro u hu
    exact (mem_fixV.mp (h hu)) z (Subgroup.mem_zpowers z)
  · intro h u hu
    rw [mem_fixV]
    intro w hw
    exact mem_centSub.mp (Subgroup.zpowers_le.mpr h hw) u hu

private theorem w16g_supp_mul_subset_free {X : Subgroup (MulAut W)} {x y : MulAut W} :
    s13Supp X (Subgroup.zpowers (x * y)) ⊆
      s13Supp X (Subgroup.zpowers x) ∪ s13Supp X (Subgroup.zpowers y) := by
  intro U hU
  have hUX : U ∈ s13IsoComps X := hU.1
  rw [Set.mem_union]
  by_contra hc
  push Not at hc
  have hx0 : commSub U (Subgroup.zpowers x) = ⊥ := by
    by_contra hne; exact hc.1 ⟨hUX, hne⟩
  have hy0 : commSub U (Subgroup.zpowers y) = ⊥ := by
    by_contra hne; exact hc.2 ⟨hUX, hne⟩
  exact hU.2 (by
    rw [w16g_commSub_zpowers_eq_bot_iff] at hx0 hy0 ⊢
    exact (centSub U).mul_mem hx0 hy0)

private theorem w16g_eq_one_of_supp_empty {p : ℕ} (h : HAb A X Q t p) {z : MulAut W}
    (hz : z ∈ X)
    (hsupp : s13Supp X (Subgroup.zpowers z) = ∅) : z = 1 := by
  have hp : p.Prime := by
    rcases h.hp with h3 | h7
    · rw [h3]; norm_num
    · rw [h7]; norm_num
  have hp2 : p ≠ 2 := by
    rcases h.hp with h3 | h7
    · rw [h3]; norm_num
    · rw [h7]; norm_num
  have hbot : commSub ⊤ (Subgroup.zpowers z) = ⊥ := by
    rw [commSub_top_eq_iSup_s13Supp h.hW hp hp2 h.hXe (Subgroup.zpowers_le.mpr hz), hsupp]
    simp
  have hfix : ∀ w : W, z w = w := by
    intro w
    have hw : w ∈ fixV (Subgroup.zpowers z) :=
      (commSub_eq_bot_iff.mp hbot) (Subgroup.mem_top w)
    exact (mem_fixV.mp hw) z (Subgroup.mem_zpowers z)
  exact MulEquiv.ext hfix

private theorem w16g_eq_one_of_supp_ncard_le_one {p : ℕ} (h : HAb A X Q t p)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    {z : MulAut W} (hz : z ∈ X)
    (hle : (s13Supp X (Subgroup.zpowers z)).ncard ≤ 1) : z = 1 := by
  by_contra hne
  have hemp : s13Supp X (Subgroup.zpowers z) ≠ ∅ := fun hempty =>
    hne (w16g_eq_one_of_supp_empty h hz hempty)
  have hpos : 0 < (s13Supp X (Subgroup.zpowers z)).ncard := by
    rw [Set.ncard_pos]
    exact Set.nonempty_iff_ne_empty.mpr hemp
  exact hH0 z hz hne (by omega)

private theorem w16g_zmod3_eq_one_or_neg_one {a : ZMod 3} (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  revert a
  decide

private theorem w16g_neg_sub_self_zmod3 (b : ZMod 3) : -b - b = b := by
  revert b; decide

private theorem w16g_two_ne_zero_zmod3 : (2 : ZMod 3) ≠ 0 := by decide

private theorem w16g_zmod3_add_eq_zero_or_sub_eq_zero {a b : ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0) :
    a + b = 0 ∨ a - b = 0 := by
  rcases w16g_zmod3_eq_one_or_neg_one ha with rfl | rfl <;>
    rcases w16g_zmod3_eq_one_or_neg_one hb with rfl | rfl <;> norm_num

private theorem w16g_three_line_eq_of_supp_eq (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    {Q₁ Q₂ : Subgroup (MulAut W)} (hQ₁X : Q₁ ≤ X) (hQ₂X : Q₂ ≤ X)
    (hQ₁ : Nat.card ↥Q₁ = 3) (hQ₂ : Nat.card ↥Q₂ = 3)
    (hsupp : s13Supp X Q₁ = s13Supp X Q₂)
    (he : (s13Supp X Q₁).ncard = 3) : Q₁ = Q₂ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨lam, hl⟩ := exists_coord h.hW (by norm_num : Nat.Prime 3)
    (by norm_num : (3 : ℕ) ≠ 2) h.hXe
  obtain ⟨q₁, hq₁⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Q₁).mp
    (isCyclic_of_prime_card hQ₁)
  obtain ⟨q₂, hq₂⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Q₂).mp
    (isCyclic_of_prime_card hQ₂)
  have hq₁X : q₁ ∈ X := hQ₁X (hq₁ ▸ Subgroup.mem_zpowers q₁)
  have hq₂X : q₂ ∈ X := hQ₂X (hq₂ ▸ Subgroup.mem_zpowers q₂)
  have hsupp₁ : s13Supp X (Subgroup.zpowers q₁) = s13Supp X Q₁ := by rw [hq₁]
  have hsupp₂ : s13Supp X (Subgroup.zpowers q₂) = s13Supp X Q₂ := by rw [hq₂]
  have hsupp₂' : s13Supp X (Subgroup.zpowers q₂⁻¹) = s13Supp X Q₂ := by
    rw [Subgroup.zpowers_inv, hsupp₂]
  have hcoord_ne : ∀ (U : Subgroup W) (hU : U ∈ s13Supp X Q₁),
      lam ⟨U, hU.1⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) ≠ 0 ∧
        lam ⟨U, hU.1⟩ (Additive.ofMul ⟨q₂, hq₂X⟩) ≠ 0 := by
    intro U hU
    have hUX : U ∈ s13IsoComps X := hU.1
    constructor
    · exact (w16g_supp_zpowers_coord hl hq₁X ⟨U, hUX⟩).mp (by rw [hsupp₁]; exact hU)
    · exact (w16g_supp_zpowers_coord hl hq₂X ⟨U, hUX⟩).mp
        (by rw [hsupp₂, ← hsupp]; exact hU)
  have hcover : s13Supp X Q₁ ⊆
      s13Supp X (Subgroup.zpowers (q₁ * q₂)) ∪
        s13Supp X (Subgroup.zpowers (q₁ * q₂⁻¹)) := by
    intro U hU
    have hUX : U ∈ s13IsoComps X := hU.1
    have h12 := hcoord_ne U hU
    rw [Set.mem_union, w16g_supp_zpowers_coord hl (X.mul_mem hq₁X hq₂X) ⟨U, hUX⟩,
      w16g_supp_zpowers_coord hl (X.mul_mem hq₁X (X.inv_mem hq₂X)) ⟨U, hUX⟩]
    by_contra hc
    push Not at hc
    have hsum : (⟨q₁ * q₂, X.mul_mem hq₁X hq₂X⟩ : ↥X) =
        ⟨q₁, hq₁X⟩ * ⟨q₂, hq₂X⟩ := rfl
    have hsum' : (⟨q₁ * q₂⁻¹, X.mul_mem hq₁X (X.inv_mem hq₂X)⟩ : ↥X) =
        ⟨q₁, hq₁X⟩ * ⟨q₂, hq₂X⟩⁻¹ := rfl
    have h0 : lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) +
        lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₂, hq₂X⟩) = 0 := by
      have hh := hc.1
      rw [hsum, ofMul_mul, map_add] at hh
      exact hh
    have h0' : lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) -
        lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₂, hq₂X⟩) = 0 := by
      have hh := hc.2
      rw [hsum', ofMul_mul, ofMul_inv, map_add, map_neg] at hh
      rw [sub_eq_add_neg]
      exact hh
    have h2a : (2 : ZMod 3) * lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) = 0 := by
      have hh : (lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) +
          lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₂, hq₂X⟩)) +
          (lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) -
          lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₂, hq₂X⟩)) = 0 + 0 :=
        congrArg₂ (· + ·) h0 h0'
      rw [add_zero] at hh
      have : (lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) +
          lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₂, hq₂X⟩)) +
          (lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) -
          lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₂, hq₂X⟩)) =
          2 * lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) := by ring
      rwa [this] at hh
    exact h12.1 ((mul_eq_zero.mp h2a).resolve_left w16g_two_ne_zero_zmod3)
  have hunion : s13Supp X (Subgroup.zpowers (q₁ * q₂)) ∪
      s13Supp X (Subgroup.zpowers (q₁ * q₂⁻¹)) = s13Supp X Q₁ := by
    apply le_antisymm
    · refine Set.union_subset ?_ ?_
      · refine (w16g_supp_mul_subset_free (x := q₁) (y := q₂)).trans ?_
        rw [hsupp₁, hsupp₂, ← hsupp, Set.union_self]
      · refine (w16g_supp_mul_subset_free (x := q₁) (y := q₂⁻¹)).trans ?_
        rw [hsupp₁, hsupp₂', ← hsupp, Set.union_self]
    · exact hcover
  have hdisj : s13Supp X (Subgroup.zpowers (q₁ * q₂)) ∩
      s13Supp X (Subgroup.zpowers (q₁ * q₂⁻¹)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro U ⟨hU1, hU2⟩
    have hUX : U ∈ s13IsoComps X := hU1.1
    have hUe : U ∈ s13Supp X Q₁ := by rw [← hunion]; exact Set.mem_union_left _ hU1
    have h12 := hcoord_ne U hUe
    have ha : lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) ≠ 0 := h12.1
    have hb : lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₂, hq₂X⟩) ≠ 0 := h12.2
    have hz1 : lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁ * q₂, X.mul_mem hq₁X hq₂X⟩) ≠ 0 :=
      (w16g_supp_zpowers_coord hl (X.mul_mem hq₁X hq₂X) ⟨U, hUX⟩).mp hU1
    have hz2 : lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁ * q₂⁻¹,
        X.mul_mem hq₁X (X.inv_mem hq₂X)⟩) ≠ 0 :=
      (w16g_supp_zpowers_coord hl (X.mul_mem hq₁X (X.inv_mem hq₂X)) ⟨U, hUX⟩).mp hU2
    have hsum : (⟨q₁ * q₂, X.mul_mem hq₁X hq₂X⟩ : ↥X) =
        ⟨q₁, hq₁X⟩ * ⟨q₂, hq₂X⟩ := rfl
    have hsum' : (⟨q₁ * q₂⁻¹, X.mul_mem hq₁X (X.inv_mem hq₂X)⟩ : ↥X) =
        ⟨q₁, hq₁X⟩ * ⟨q₂, hq₂X⟩⁻¹ := rfl
    have hp : lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) +
        lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₂, hq₂X⟩) ≠ 0 := by
      intro hzero
      apply hz1
      rw [hsum, ofMul_mul, map_add]
      exact hzero
    have hm : lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₁, hq₁X⟩) -
        lam ⟨U, hUX⟩ (Additive.ofMul ⟨q₂, hq₂X⟩) ≠ 0 := by
      intro hzero
      apply hz2
      rw [hsum', ofMul_mul, ofMul_inv, map_add, map_neg]
      rw [sub_eq_add_neg] at hzero
      exact hzero
    exact (w16g_zmod3_add_eq_zero_or_sub_eq_zero ha hb).elim hp hm
  have hsum3 : (s13Supp X (Subgroup.zpowers (q₁ * q₂))).ncard +
      (s13Supp X (Subgroup.zpowers (q₁ * q₂⁻¹))).ncard = 3 := by
    have hh := Set.ncard_inter_add_ncard_union
      (s13Supp X (Subgroup.zpowers (q₁ * q₂)))
      (s13Supp X (Subgroup.zpowers (q₁ * q₂⁻¹)))
    rw [hdisj, hunion, Set.ncard_empty, zero_add, he] at hh
    exact hh.symm
  have hone : (s13Supp X (Subgroup.zpowers (q₁ * q₂))).ncard ≤ 1 ∨
      (s13Supp X (Subgroup.zpowers (q₁ * q₂⁻¹))).ncard ≤ 1 := by
    omega
  rcases hone with hle | hle
  · have hprod : q₁ * q₂ = 1 :=
      w16g_eq_one_of_supp_ncard_le_one h hH0 (X.mul_mem hq₁X hq₂X) hle
    have hqeq : q₁ = q₂⁻¹ := by
      rw [← mul_inv_eq_one]; exact hprod
    rw [← hq₁, ← hq₂, hqeq, Subgroup.zpowers_inv]
  · have hprod : q₁ * q₂⁻¹ = 1 :=
      w16g_eq_one_of_supp_ncard_le_one h hH0 (X.mul_mem hq₁X (X.inv_mem hq₂X)) hle
    have hqeq : q₁ = q₂ := mul_inv_eq_one.mp hprod
    rw [← hq₁, ← hq₂, hqeq]

private theorem w16g_kerOn_inter_card (h : HAb A X Q t 3) (hQ9 : Nat.card ↥Q = 9)
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam)
    {U : Subgroup W} (hU : U ∈ s13IsoComps X) (hUsupp : U ∈ s13Supp X Q) :
    Nat.card ↥(Q ⊓ s13KerOn X U) = 3 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have hH := s13KerOn_mem_hyperplanes h.hW hp3 hp32 h.hXe hU
  have hle : (s13KerOn X U).relIndex Q ≤ 3 := by
    have h1 : (s13KerOn X U).relIndex Q ≤ (s13KerOn X U).relIndex X :=
      relIndex_le_of_le_right h.hQX (by rw [hH.2]; norm_num)
    rwa [hH.2] at h1
  have hdvd : (s13KerOn X U).relIndex Q ∣ 9 := by
    rw [← hQ9]; exact relIndex_dvd_card (H := s13KerOn X U) (K := Q)
  have hne1 : (s13KerOn X U).relIndex Q ≠ 1 := by
    intro h1
    have hQle : Q ≤ s13KerOn X U := Subgroup.relIndex_eq_one.mp h1
    obtain ⟨x, hxQ, hxne⟩ := (mem_s13Supp_iff_coord hl h.hQX ⟨U, hU⟩).mp hUsupp
    have hxker : (x : MulAut W) ∈ s13KerOn X U := hQle hxQ
    exact hxne (((hl ⟨U, hU⟩).2 x).mpr hxker)
  have hcases : (s13KerOn X U).relIndex Q = 1 ∨ (s13KerOn X U).relIndex Q = 2 ∨
      (s13KerOn X U).relIndex Q = 3 := by
    have hpos : 0 < (s13KerOn X U).relIndex Q := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact absurd (relIndex_eq_zero_of_le_right h.hQX h0) (by rw [hH.2]; norm_num)
    omega
  rcases hcases with h1 | h2 | h3
  · exact absurd h1 hne1
  · exfalso
    obtain ⟨k, hk⟩ := hdvd
    rw [h2] at hk
    omega
  · have hcard := Subgroup.relIndex_mul_card (H := s13KerOn X U) (K := Q)
    rw [h3, hQ9, inf_comm] at hcard
    omega

private theorem w16g_three_proj (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ9 : Nat.card ↥Q = 9) (he : (s13Supp X Q).ncard = 3)
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam) :
    (∀ (x : ↥X) (U : s13IsoComps X), (U : Subgroup W) ∈ s13Supp X Q →
      lam U (Additive.ofMul ⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹,
        X.mul_mem (h.hXA t h.htA (x : MulAut W) x.2) (X.inv_mem x.2)⟩) =
        lam U (Additive.ofMul x)) ∧
    (∀ (x : ↥X) (U : s13IsoComps X), (U : Subgroup W) ∉ s13Supp X Q →
      lam U (Additive.ofMul ⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹,
        X.mul_mem (h.hXA t h.htA (x : MulAut W) x.2) (X.inv_mem x.2)⟩) = 0) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  set e : Set (Subgroup W) := s13Supp X Q with hedef
  have htX : ∀ x ∈ X, t * x * t⁻¹ ∈ X := h.hXA t h.htA
  have htX' : ∀ x ∈ X, t⁻¹ * x * t ∈ X := by
    intro x hx; simpa using h.hXA t⁻¹ (A.inv_mem h.htA) x hx
  obtain ⟨σ, c, hσ, hc⟩ := exists_monomial h.hW hp3 hp32 h.hXe hl htX htX'
  have ht2 : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have hσ2 : ∀ U : s13IsoComps X, σ (σ U) = U := by
    intro U
    apply Subtype.ext
    have hcomp : t.toMonoidHom.comp t.toMonoidHom = MonoidHom.id W := by
      ext w; change t (t w) = w
      rw [← MulAut.mul_apply, ht2, MulAut.one_apply]
    rw [hσ (σ U), hσ U, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hrel : ∀ (x : ↥X) (hxQ : (x : MulAut W) ∈ Q) (U : s13IsoComps X),
      (c U : ZMod 3) * lam U (Additive.ofMul x) + lam (σ U) (Additive.ofMul x) = 0 := by
    intro x hxQ U
    have hxinv : t * (x : MulAut W) * t⁻¹ = (x : MulAut W)⁻¹ := h.hQinv (x : MulAut W) hxQ
    have heq : (⟨t * (x : MulAut W) * t⁻¹, htX (x : MulAut W) x.2⟩ : ↥X) =
        ⟨(x : MulAut W)⁻¹, X.inv_mem x.2⟩ := Subtype.ext hxinv
    have h1 : lam (σ U) (Additive.ofMul ⟨(x : MulAut W)⁻¹, X.inv_mem x.2⟩) =
        (c U : ZMod 3) * lam U (Additive.ofMul x) := by
      rw [← heq]
      exact hc U x (htX (x : MulAut W) x.2)
    have h2 : lam (σ U) (Additive.ofMul ⟨(x : MulAut W)⁻¹, X.inv_mem x.2⟩) =
        - lam (σ U) (Additive.ofMul x) := by
      have heq2 : (⟨(x : MulAut W)⁻¹, X.inv_mem x.2⟩ : ↥X) = ⟨x, x.2⟩⁻¹ :=
        Subtype.ext rfl
      rw [heq2, ofMul_inv, map_neg]
    rw [h2] at h1
    rw [← h1]
    abel
  have htQ : Q.map (MulAut.conj t).toMonoidHom = Q := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro q ⟨q₀, hq₀, rfl⟩
      change MulAut.conj t q₀ ∈ Q
      rw [MulAut.conj_apply, h.hQinv q₀ hq₀]
      exact Q.inv_mem hq₀
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hσmem : ∀ U : s13IsoComps X, (U : Subgroup W) ∈ e → (σ U).val ∈ e := by
    intro U hU
    have hconj : e = (fun V : Subgroup W => V.map t.toMonoidHom) '' e := by
      rw [hedef]
      have h1 := s13Supp_conj (X := X) (L := Q) (g := t) htX htX'
      rwa [htQ] at h1
    rw [hσ U, hconj]
    exact ⟨U, hU, rfl⟩
  have hσid : ∀ U : s13IsoComps X, (U : Subgroup W) ∈ e → σ U = U := by
    intro U hU
    by_contra hne
    have hVmem : (σ U).val ∈ e := hσmem U hU
    have hVne : σ U ≠ U := hne
    have hUsupp : (U : Subgroup W) ∈ s13Supp X Q := by rw [← hedef]; exact hU
    have hKcard : Nat.card ↥(Q ⊓ s13KerOn X U) = 3 :=
      w16g_kerOn_inter_card h hQ9 hl U.2 hUsupp
    have hKne : (Q ⊓ s13KerOn X U) ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hKcard
      norm_num at hKcard
    haveI : Nontrivial ↥(Q ⊓ s13KerOn X U) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hKne
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥(Q ⊓ s13KerOn X U))
    have hxQ : (x : MulAut W) ∈ Q := x.2.1
    have hxX : (x : MulAut W) ∈ X := h.hQX hxQ
    have hxkerU : (x : MulAut W) ∈ s13KerOn X U := x.2.2
    have hlu : lam U (Additive.ofMul ⟨(x : MulAut W), hxX⟩) = 0 :=
      ((hl U).2 ⟨(x : MulAut W), hxX⟩).mpr hxkerU
    have hlv : lam (σ U) (Additive.ofMul ⟨(x : MulAut W), hxX⟩) = 0 := by
      have h1 := hrel ⟨(x : MulAut W), hxX⟩ hxQ U
      rw [hlu, mul_zero, zero_add] at h1
      exact h1
    have hxsupp : s13Supp X (Subgroup.zpowers (x : MulAut W)) ⊆ e := by
      rw [hedef]
      exact w16g_supp_mono (Subgroup.zpowers_le.mpr hxQ)
    have hUnot : (U : Subgroup W) ∉ s13Supp X (Subgroup.zpowers (x : MulAut W)) := by
      intro hmem
      exact ((w16g_supp_zpowers_coord hl hxX U).mp hmem) hlu
    have hVnot : (σ U).val ∉ s13Supp X (Subgroup.zpowers (x : MulAut W)) := by
      intro hmem
      exact ((w16g_supp_zpowers_coord hl hxX (σ U)).mp hmem) hlv
    have hsub : s13Supp X (Subgroup.zpowers (x : MulAut W)) ⊆
        e \ {(U : Subgroup W), (σ U).val} := by
      intro V hV
      refine ⟨hxsupp hV, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hUnot (h ▸ hV), fun h => hVnot (h ▸ hV)⟩
    have hUVsub : ({(U : Subgroup W), (σ U).val} : Set (Subgroup W)) ⊆ e := by
      intro V hV
      rcases Set.mem_insert_iff.mp hV with rfl | hV
      · exact hU
      · rw [Set.mem_singleton_iff.mp hV]; exact hVmem
    have hUVne : (U : Subgroup W) ≠ (σ U).val :=
      fun h => hVne (Subtype.ext h.symm)
    have hle : (s13Supp X (Subgroup.zpowers (x : MulAut W))).ncard ≤ 1 := by
      have hncard : (e \ {(U : Subgroup W), (σ U).val}).ncard = 1 := by
        rw [Set.ncard_sdiff hUVsub, he, Set.ncard_pair hUVne]
      rw [← hncard]
      exact Set.ncard_le_ncard hsub
    exact hx1 (Subtype.ext (w16g_eq_one_of_supp_ncard_le_one h hH0 hxX hle))
  have hcneg : ∀ U : s13IsoComps X, (U : Subgroup W) ∈ e → (c U : ZMod 3) = -1 := by
    intro U hU
    have hσU : σ U = U := hσid U hU
    obtain ⟨x, hxQ, hxne⟩ := (mem_s13Supp_iff_coord hl h.hQX U).mp (by rw [← hedef]; exact hU)
    have h1 := hrel x hxQ U
    rw [hσU] at h1
    have h2 : ((c U : ZMod 3) + 1) * lam U (Additive.ofMul x) = 0 := by
      rw [add_mul, one_mul]
      exact h1
    exact add_eq_zero_iff_eq_neg.mp ((mul_eq_zero.mp h2).resolve_right hxne)
  have hcost : rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) = 3 := by
    have h1 := (cost_commSub_Q h).1
    have h2 := w16g_three_rk_eq_six h he
    omega
  have hQmap1 : Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom = Q := by
    rw [show MulAut.conj (1 : MulAut W) = 1 from by ext w; simp [MulAut.conj_apply]]
    exact Subgroup.map_id Q
  have ht1 : (1 : MulAut W) * t * 1⁻¹ = t := by simp
  have hcost' : rk ↥(commSub (commSub ⊤ (Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom))
      (Subgroup.zpowers ((1 : MulAut W) * t * 1⁻¹))) = 3 := by
    rw [hQmap1, ht1]; exact hcost
  have hsatU : ∀ U ∈ s13IsoComps X, U ∉ e → commSub U (Subgroup.zpowers t) = ⊥ := by
    intro U hU hUe
    have hU' : U ∉ s13Supp X (Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom) := by
      rw [hQmap1]
      rwa [← hedef]
    have h1 := (saturation h (a := 1) A.one_mem hcost').1 U hU hU'
    simpa [ht1] using h1
  constructor
  · intro x U hU
    have hσU : σ U = U := hσid U hU
    have hcU : (c U : ZMod 3) = -1 := hcneg U hU
    have h1 : lam U (Additive.ofMul ⟨t * (x : MulAut W) * t⁻¹,
        htX (x : MulAut W) x.2⟩) = - lam U (Additive.ofMul x) := by
      have h := hc U x (htX (x : MulAut W) x.2)
      simpa [hσU, hcU] using h
    have hsplit : (⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹,
          X.mul_mem (htX (x : MulAut W) x.2) (X.inv_mem x.2)⟩ : ↥X) * ⟨x, x.2⟩ =
        ⟨t * (x : MulAut W) * t⁻¹, htX (x : MulAut W) x.2⟩ := by
      apply Subtype.ext
      show (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹) * (x : MulAut W) =
        t * (x : MulAut W) * t⁻¹
      group
    have h := congrArg (fun y : ↥X => lam U (Additive.ofMul y)) hsplit
    rw [ofMul_mul, map_add, h1] at h
    have h2 : lam U (Additive.ofMul ⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹,
        X.mul_mem (htX (x : MulAut W) x.2) (X.inv_mem x.2)⟩) =
        - lam U (Additive.ofMul x) - lam U (Additive.ofMul x) :=
      eq_sub_of_add_eq h
    rw [h2]
    exact w16g_neg_sub_self_zmod3 _
  · intro x U hU
    have htcent : t ∈ centSub (U : Subgroup W) :=
      (w16g_commSub_zpowers_eq_bot_iff (U := (U : Subgroup W)) (z := t)).mp
        (hsatU (U : Subgroup W) U.2 hU)
    have hstab : StableUnder X (U : Subgroup W) := s13IsoComps_stable U.2
    have hπX : t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹ ∈ X :=
      X.mul_mem (htX (x : MulAut W) x.2) (X.inv_mem x.2)
    have hmem : t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹ ∈
        centSub (U : Subgroup W) := by
      rw [mem_centSub]
      intro u hu
      have htu : t u = u := mem_centSub.mp htcent u hu
      have hxinu : (x : MulAut W)⁻¹ u ∈ (U : Subgroup W) :=
        hstab (x : MulAut W)⁻¹ (X.inv_mem x.2) u hu
      have htinu : t⁻¹ ((x : MulAut W)⁻¹ u) = (x : MulAut W)⁻¹ u := by
        have h2 : t⁻¹ (t ((x : MulAut W)⁻¹ u)) = (x : MulAut W)⁻¹ u := by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
        rwa [mem_centSub.mp htcent ((x : MulAut W)⁻¹ u) hxinu] at h2
      show t ((x : MulAut W) (t⁻¹ ((x : MulAut W)⁻¹ u))) = u
      rw [htinu, MulAut.apply_inv_self, htu]
    have h0 : lam U (Additive.ofMul ⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹,
        hπX⟩) = 0 :=
      ((hl U).2 ⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹, hπX⟩).mpr ⟨hπX, hmem⟩
    have h1 : lam U (Additive.ofMul ⟨t * (x : MulAut W) * t⁻¹,
        htX (x : MulAut W) x.2⟩) = lam U (Additive.ofMul x) := by
      have hsplit : (⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹,
            hπX⟩ : ↥X) * ⟨x, x.2⟩ =
          ⟨t * (x : MulAut W) * t⁻¹, htX (x : MulAut W) x.2⟩ := by
        apply Subtype.ext
        show (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹) * (x : MulAut W) =
          t * (x : MulAut W) * t⁻¹
        group
      have h := congrArg (fun y : ↥X => lam U (Additive.ofMul y)) hsplit
      rw [ofMul_mul, map_add, h0, zero_add] at h
      exact h.symm
    have hsplit2 : (⟨t * (x : MulAut W) * t⁻¹, htX (x : MulAut W) x.2⟩ : ↥X) =
        ⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹, hπX⟩ * ⟨x, x.2⟩ := by
      apply Subtype.ext
      show t * (x : MulAut W) * t⁻¹ =
        (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹) * (x : MulAut W)
      group
    have h := congrArg (fun y : ↥X => lam U (Additive.ofMul y)) hsplit2
    rw [ofMul_mul, map_add, h1] at h
    exact add_right_cancel (h.symm.trans (zero_add _).symm)

theorem w16g_three_blocks (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ9 : Nat.card ↥Q = 9) (he : (s13Supp X Q).ncard = 3) :
    ∀ a ∈ A, s13Supp X (Q.map (MulAut.conj a).toMonoidHom) = s13Supp X Q ∨
      Disjoint (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) (s13Supp X Q) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨lam, hl⟩ := exists_coord h.hW hp3 hp32 h.hXe
  obtain ⟨hproj_mem, hproj_not⟩ := w16g_three_proj h hH0 hQ9 he hl
  have hsuppπ : ∀ x : ↥X,
      s13Supp X (Subgroup.zpowers (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹)) =
        s13Supp X Q ∩ s13Supp X (Subgroup.zpowers (x : MulAut W)) := by
    intro x
    have hxX : (x : MulAut W) ∈ X := x.2
    have hπX : t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹ ∈ X :=
      X.mul_mem (h.hXA t h.htA (x : MulAut W) x.2) (X.inv_mem x.2)
    ext U
    rw [Set.mem_inter_iff]
    by_cases hUcomp : U ∈ s13IsoComps X
    · by_cases hU : U ∈ s13Supp X Q
      · rw [w16g_supp_zpowers_coord hl hπX ⟨U, hUcomp⟩, hproj_mem x ⟨U, hUcomp⟩ hU,
          w16g_supp_zpowers_coord hl hxX ⟨U, hUcomp⟩]
        simp [hU]
      · rw [w16g_supp_zpowers_coord hl hπX ⟨U, hUcomp⟩, hproj_not x ⟨U, hUcomp⟩ hU]
        simp [hU]
    · have h1 : U ∉ s13Supp X
          (Subgroup.zpowers (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹)) :=
        fun h => hUcomp h.1
      have h2 : U ∉ s13Supp X (Subgroup.zpowers (x : MulAut W)) := fun h => hUcomp h.1
      have h3 : U ∉ s13Supp X Q := fun h => hUcomp h.1
      simp [h1, h2, h3]
  intro a ha
  set e' : Set (Subgroup W) := s13Supp X (Q.map (MulAut.conj a).toMonoidHom) with he'def
  have hQaX : Q.map (MulAut.conj a).toMonoidHom ≤ X := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    exact h.hXA a ha q (h.hQX hq)
  have hcardQa : Nat.card ↥(Q.map (MulAut.conj a).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, hQ9]
  have he'card : e'.ncard = 3 := by
    rcases s13_three_shape (h.conj ha) hH0 with ⟨-, h3⟩ | ⟨-, h3'⟩ | ⟨h3, -⟩
    · rw [hcardQa] at h3; norm_num at h3
    · rw [hcardQa] at h3'; norm_num at h3'
    · rw [he'def]; exact h3
  have hne1 : (e' ∩ s13Supp X Q).ncard ≠ 1 := by
    intro h1
    obtain ⟨U, hUeq⟩ := Set.ncard_eq_one.mp h1
    have hUinter : U ∈ e' ∩ s13Supp X Q := by rw [hUeq]; exact Set.mem_singleton U
    have hUe' : U ∈ e' := hUinter.1
    have hUe : U ∈ s13Supp X Q := hUinter.2
    have hUcomp : U ∈ s13IsoComps X := hUe'.1
    obtain ⟨x, hxQa, hxne⟩ := (mem_s13Supp_iff_coord hl hQaX ⟨U, hUcomp⟩).mp hUe'
    have hxX : (x : MulAut W) ∈ X := hQaX hxQa
    have hxsupp : s13Supp X (Subgroup.zpowers (x : MulAut W)) ⊆ e' := by
      rw [he'def]; exact w16g_supp_mono (Subgroup.zpowers_le.mpr hxQa)
    have hUmem : U ∈ s13Supp X
        (Subgroup.zpowers (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹)) := by
      rw [hsuppπ x]
      exact ⟨hUe, (w16g_supp_zpowers_coord hl hxX ⟨U, hUcomp⟩).mpr hxne⟩
    have hsub : s13Supp X
        (Subgroup.zpowers (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹)) ⊆ {U} := by
      rw [hsuppπ x]
      intro V hV
      have hVinter : V ∈ e' ∩ s13Supp X Q := ⟨hxsupp hV.2, hV.1⟩
      rwa [hUeq] at hVinter
    have hsupp_eq : s13Supp X
        (Subgroup.zpowers (t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹)) = {U} := by
      rw [Set.eq_singleton_iff_nonempty_unique_mem]
      exact ⟨⟨U, hUmem⟩, fun V hV => Set.mem_singleton_iff.mp (hsub hV)⟩
    have hπX : t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹ ∈ X :=
      X.mul_mem (h.hXA t h.htA (x : MulAut W) x.2) (X.inv_mem x.2)
    have hπne : t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹ ≠ 1 := by
      intro hπ1
      have h0 : lam ⟨U, hUcomp⟩ (Additive.ofMul
          ⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹, hπX⟩) = 0 := by
        have heq : (⟨t * (x : MulAut W) * t⁻¹ * (x : MulAut W)⁻¹, hπX⟩ : ↥X) = 1 :=
          Subtype.ext hπ1
        simp [heq]
      rw [hproj_mem x ⟨U, hUcomp⟩ hUe] at h0
      exact hxne h0
    exact hH0 _ hπX hπne (by rw [hsupp_eq, Set.ncard_singleton])
  have hne2 : (e' ∩ s13Supp X Q).ncard ≠ 2 := by
    intro h2
    obtain ⟨U0, U1, hU01, hUeq⟩ := Set.ncard_eq_two.mp h2
    have hU0inter : U0 ∈ e' ∩ s13Supp X Q := by
      rw [hUeq]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
    have hU1inter : U1 ∈ e' ∩ s13Supp X Q := by
      rw [hUeq]; exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton U1))
    have hU0e' : U0 ∈ e' := hU0inter.1
    have hU0e : U0 ∈ s13Supp X Q := hU0inter.2
    have hU1e' : U1 ∈ e' := hU1inter.1
    have hU1e : U1 ∈ s13Supp X Q := hU1inter.2
    have hU0comp : U0 ∈ s13IsoComps X := hU0e'.1
    have hU1comp : U1 ∈ s13IsoComps X := hU1e'.1
    have hK0card : Nat.card ↥(Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U0) = 3 :=
      w16g_kerOn_inter_card (h.conj ha) hcardQa hl hU0comp (by rw [← he'def]; exact hU0e')
    have hK1card : Nat.card ↥(Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U1) = 3 :=
      w16g_kerOn_inter_card (h.conj ha) hcardQa hl hU1comp (by rw [← he'def]; exact hU1e')
    by_cases hK : Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U0 =
        Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U1
    · have hKne : (Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U0) ≠ ⊥ := by
        intro hbot; rw [hbot, Subgroup.card_bot] at hK0card; norm_num at hK0card
      haveI : Nontrivial ↥(Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U0) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hKne
      obtain ⟨q', hq'1⟩ := exists_ne (1 : ↥(Q.map (MulAut.conj a).toMonoidHom ⊓
        s13KerOn X U0))
      have hq'Qa : (q' : MulAut W) ∈ Q.map (MulAut.conj a).toMonoidHom := q'.2.1
      have hq'X : (q' : MulAut W) ∈ X := hQaX hq'Qa
      have hq'ker0 : (q' : MulAut W) ∈ s13KerOn X U0 := q'.2.2
      have hq'ker1 : (q' : MulAut W) ∈ s13KerOn X U1 := by
        have hmem : (q' : MulAut W) ∈
            Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U1 := by
          rw [← hK]
          exact q'.2
        exact hmem.2
      have hq'supp : s13Supp X (Subgroup.zpowers (q' : MulAut W)) ⊆ e' \ s13Supp X Q := by
        intro V hV
        refine ⟨?_, ?_⟩
        · rw [he'def]; exact w16g_supp_mono (Subgroup.zpowers_le.mpr hq'Qa) hV
        · intro hVe
          have hVinter : V ∈ e' ∩ s13Supp X Q :=
            ⟨by rw [he'def]; exact w16g_supp_mono (Subgroup.zpowers_le.mpr hq'Qa) hV, hVe⟩
          rw [hUeq] at hVinter
          have hlamV : lam ⟨V, hV.1⟩ (Additive.ofMul ⟨(q' : MulAut W), hq'X⟩) ≠ 0 :=
            (w16g_supp_zpowers_coord hl hq'X ⟨V, hV.1⟩).mp hV
          rcases Set.mem_insert_iff.mp hVinter with hV0 | hV1
          · rw [hV0] at hV
            have hlam0' : lam ⟨U0, hU0comp⟩ (Additive.ofMul ⟨(q' : MulAut W), hq'X⟩) = 0 :=
              ((hl ⟨U0, hU0comp⟩).2 ⟨(q' : MulAut W), hq'X⟩).mpr hq'ker0
            exact absurd hlam0' ((w16g_supp_zpowers_coord hl hq'X ⟨U0, hU0comp⟩).mp hV)
          · have hVU1 : V = U1 := Set.mem_singleton_iff.mp hV1
            rw [hVU1] at hV
            exact absurd (((hl ⟨U1, hU1comp⟩).2 ⟨(q' : MulAut W), hq'X⟩).mpr hq'ker1)
              ((w16g_supp_zpowers_coord hl hq'X ⟨U1, hU1comp⟩).mp hV)
      have hncard : (e' \ s13Supp X Q).ncard = 1 := by
        have h := Set.ncard_sdiff (Set.inter_subset_left : e' ∩ s13Supp X Q ⊆ e')
        rw [he'card, h2] at h
        have heq : e' \ (e' ∩ s13Supp X Q) = e' \ s13Supp X Q := by
          ext V; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
        rw [heq] at h; omega
      have hle : (s13Supp X (Subgroup.zpowers (q' : MulAut W))).ncard ≤ 1 := by
        rw [← hncard]; exact Set.ncard_le_ncard hq'supp
      exact hq'1 (Subtype.ext (w16g_eq_one_of_supp_ncard_le_one h hH0 hq'X hle))
    · have hK0ne : (Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U0) ≠ ⊥ := by
        intro hbot; rw [hbot, Subgroup.card_bot] at hK0card; norm_num at hK0card
      haveI : Nontrivial ↥(Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U0) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hK0ne
      have hnotsub : ¬ (Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U0 ≤
          Q.map (MulAut.conj a).toMonoidHom ⊓ s13KerOn X U1) := by
        intro hle
        exact hK (Subgroup.eq_of_le_of_card_ge hle (by rw [hK0card, hK1card]))
      obtain ⟨q', hq'K0, hq'notK1⟩ := Set.not_subset.mp hnotsub
      have hq'Qa : (q' : MulAut W) ∈ Q.map (MulAut.conj a).toMonoidHom := hq'K0.1
      have hq'X : (q' : MulAut W) ∈ X := hQaX hq'Qa
      have hq'ker0 : (q' : MulAut W) ∈ s13KerOn X U0 := hq'K0.2
      have hq'notker1 : (q' : MulAut W) ∉ s13KerOn X U1 :=
        fun h => hq'notK1 ⟨hq'Qa, h⟩
      have hlam0 : lam ⟨U0, hU0comp⟩ (Additive.ofMul ⟨(q' : MulAut W), hq'X⟩) = 0 :=
        ((hl ⟨U0, hU0comp⟩).2 ⟨(q' : MulAut W), hq'X⟩).mpr hq'ker0
      have hlam1 : lam ⟨U1, hU1comp⟩ (Additive.ofMul ⟨(q' : MulAut W), hq'X⟩) ≠ 0 :=
        fun h0 => hq'notker1 (((hl ⟨U1, hU1comp⟩).2 ⟨(q' : MulAut W), hq'X⟩).mp h0)
      have hq'supp : s13Supp X (Subgroup.zpowers (q' : MulAut W)) ⊆ e' := by
        rw [he'def]; exact w16g_supp_mono (Subgroup.zpowers_le.mpr hq'Qa)
      have hU1mem : U1 ∈ s13Supp X
          (Subgroup.zpowers (t * (q' : MulAut W) * t⁻¹ * (q' : MulAut W)⁻¹)) := by
        rw [hsuppπ ⟨(q' : MulAut W), hq'X⟩]
        exact ⟨hU1e, (w16g_supp_zpowers_coord hl hq'X ⟨U1, hU1comp⟩).mpr hlam1⟩
      have hsub : s13Supp X
          (Subgroup.zpowers (t * (q' : MulAut W) * t⁻¹ * (q' : MulAut W)⁻¹)) ⊆ {U1} := by
        rw [hsuppπ ⟨(q' : MulAut W), hq'X⟩]
        intro V hV
        have hVinter : V ∈ e' ∩ s13Supp X Q := ⟨hq'supp hV.2, hV.1⟩
        rw [hUeq] at hVinter
        rcases Set.mem_insert_iff.mp hVinter with hV0 | hV1
        · exfalso
          rw [hV0] at hV
          exact absurd hlam0 ((w16g_supp_zpowers_coord hl hq'X ⟨U0, hU0comp⟩).mp hV.2)
        · exact hV1
      have hsupp_eq : s13Supp X
          (Subgroup.zpowers (t * (q' : MulAut W) * t⁻¹ * (q' : MulAut W)⁻¹)) = {U1} := by
        rw [Set.eq_singleton_iff_nonempty_unique_mem]
        exact ⟨⟨U1, hU1mem⟩, fun V hV => Set.mem_singleton_iff.mp (hsub hV)⟩
      have hπX : t * (q' : MulAut W) * t⁻¹ * (q' : MulAut W)⁻¹ ∈ X :=
        X.mul_mem (h.hXA t h.htA (q' : MulAut W) hq'X) (X.inv_mem hq'X)
      have hπne : t * (q' : MulAut W) * t⁻¹ * (q' : MulAut W)⁻¹ ≠ 1 := by
        intro hπ1
        have h0 : lam ⟨U1, hU1comp⟩ (Additive.ofMul
            ⟨t * (q' : MulAut W) * t⁻¹ * (q' : MulAut W)⁻¹, hπX⟩) = 0 := by
          have heq : (⟨t * (q' : MulAut W) * t⁻¹ * (q' : MulAut W)⁻¹, hπX⟩ : ↥X) = 1 :=
            Subtype.ext hπ1
          simp [heq]
        rw [hproj_mem ⟨(q' : MulAut W), hq'X⟩ ⟨U1, hU1comp⟩ hU1e] at h0
        exact hlam1 h0
      exact hH0 _ hπX hπne (by rw [hsupp_eq, Set.ncard_singleton])
  have hle3 : (e' ∩ s13Supp X Q).ncard ≤ 3 :=
    (Set.ncard_le_ncard Set.inter_subset_right).trans_eq he
  have hcases : (e' ∩ s13Supp X Q).ncard = 0 ∨ (e' ∩ s13Supp X Q).ncard = 3 := by omega
  rcases hcases with h0 | h3
  · right
    exact Set.disjoint_iff_inter_eq_empty.mpr
      ((Set.ncard_eq_zero (s := e' ∩ s13Supp X Q)).mp h0)
  · left
    have hsub : s13Supp X Q ⊆ e' := by
      have heq : e' ∩ s13Supp X Q = s13Supp X Q :=
        Set.eq_of_subset_of_ncard_le Set.inter_subset_right (by rw [he, h3])
      rw [← heq]; exact Set.inter_subset_left
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [he'card, he])).symm

private theorem w16g_three_plane_Xle (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    (hblk : ∀ a ∈ A, s13Supp X (Q.map (MulAut.conj a).toMonoidHom) = s13Supp X Q ∨
      Disjoint (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) (s13Supp X Q)) :
    X ≤ Q ⊔ s13XSupp X (s13IsoComps X \ s13Supp X Q) := by
  classical
  have hconj : conjClosure A Q ≤ Q ⊔ s13XSupp X (s13IsoComps X \ s13Supp X Q) := by
    unfold conjClosure
    rw [Subgroup.closure_le]
    rintro x ⟨g, hg, q, hq, rfl⟩
    have hgX : Q.map (MulAut.conj g).toMonoidHom ≤ X := by
      intro y hy
      obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hy
      exact h.hXA g hg q' (h.hQX hq')
    have hgen : g * q * g⁻¹ ∈ Q.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨q, hq, MulAut.conj_apply g q⟩
    rcases hblk g hg with heq | hdisj
    · have hcard : Nat.card ↥(Q.map (MulAut.conj g).toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hQ3]
      have he' : (s13Supp X (Q.map (MulAut.conj g).toMonoidHom)).ncard = 3 := by
        rw [heq]; exact he
      have hQgeq := w16g_three_line_eq_of_supp_eq h hH0 hgX h.hQX hcard hQ3 heq he'
      rw [hQgeq] at hgen
      exact Subgroup.mem_sup_left hgen
    · have hsub : s13Supp X (Q.map (MulAut.conj g).toMonoidHom) ⊆
          s13IsoComps X \ s13Supp X Q :=
        fun U hU => ⟨hU.1, fun hUe => Set.disjoint_left.mp hdisj hU hUe⟩
      have hleZ : Q.map (MulAut.conj g).toMonoidHom ≤
          s13XSupp X (s13IsoComps X \ s13Supp X Q) :=
        (le_s13XSupp_iff h.hW (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2)
          h.hXe hgX).mpr hsub
      exact Subgroup.mem_sup_right (hleZ hgen)
  rw [← h.hXgen] at hconj
  exact hconj

private theorem w16g_three_plane_Yle (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    (hXle : X ≤ Q ⊔ s13XSupp X (s13IsoComps X \ s13Supp X Q)) :
    s13XSupp X (s13Supp X Q) ≤ Q := by
  classical
  let Z : Subgroup (MulAut W) := s13XSupp X (s13IsoComps X \ s13Supp X Q)
  have hXleZ : X ≤ Q ⊔ Z := hXle
  have hZleB : ∀ {z : MulAut W}, z ∈ Z →
      s13Supp X (Subgroup.zpowers z) ⊆ s13IsoComps X \ s13Supp X Q := by
    intro z hz U hU
    refine ⟨hU.1, fun hUB => ?_⟩
    have hzker : z ∈ s13KerOn X U :=
      (mem_s13XSupp.mp hz).2 U hU.1 (fun hB => hB.2 hUB)
    exact hU.2 (w16g_commSub_zpowers_eq_bot_iff.mpr hzker.2)
  intro x hx
  have hxX : x ∈ X := (mem_s13XSupp.mp hx).1
  have hxsupp : s13Supp X (Subgroup.zpowers x) ⊆ s13Supp X Q := by
    intro U hU
    by_contra hUQ
    have hxker : x ∈ s13KerOn X U := (mem_s13XSupp.mp hx).2 U hU.1 hUQ
    exact hU.2 (w16g_commSub_zpowers_eq_bot_iff.mpr hxker.2)
  have hmem : ∃ q ∈ Q, ∃ z ∈ Z, q * z = x := by
    let S : Subgroup (MulAut W) :=
      { carrier := {y | ∃ q ∈ Q, ∃ z ∈ Z, q * z = y}
        one_mem' := ⟨1, Q.one_mem, 1, Z.one_mem, one_mul 1⟩
        mul_mem' := by
          rintro y y' ⟨q, hq, z, hz, rfl⟩ ⟨q', hq', z', hz', rfl⟩
          refine ⟨q * q', Q.mul_mem hq hq', z * z', Z.mul_mem hz hz', ?_⟩
          have hcomm : z * q' = q' * z := congrArg Subtype.val
            (h.hXe.1.is_comm.comm ⟨z, s13XSupp_le hz⟩ ⟨q', h.hQX hq'⟩)
          rw [mul_assoc, ← mul_assoc q' z z', ← hcomm, mul_assoc, ← mul_assoc]
        inv_mem' := by
          rintro y ⟨q, hq, z, hz, rfl⟩
          refine ⟨q⁻¹, Q.inv_mem hq, z⁻¹, Z.inv_mem hz, ?_⟩
          have hcomm : z⁻¹ * q⁻¹ = q⁻¹ * z⁻¹ := congrArg Subtype.val
            (h.hXe.1.is_comm.comm ⟨z⁻¹, X.inv_mem (s13XSupp_le hz)⟩
              ⟨q⁻¹, X.inv_mem (h.hQX hq)⟩)
          rw [mul_inv_rev, ← hcomm] }
    have hQleS : Q ≤ S := fun q hq => ⟨q, hq, 1, Z.one_mem, mul_one q⟩
    have hZleS : Z ≤ S := fun z hz => ⟨1, Q.one_mem, z, hz, one_mul z⟩
    exact (sup_le hQleS hZleS) (hXleZ hxX)
  obtain ⟨q, hq, z, hz, hxz⟩ := hmem
  have hqX : q ∈ X := h.hQX hq
  have hzx : z = q⁻¹ * x := by rw [← hxz]; group
  have hzsupp : s13Supp X (Subgroup.zpowers z) ⊆ s13Supp X Q := by
    rw [hzx]
    refine (w16g_supp_mul_subset_free (x := q⁻¹) (y := x)).trans ?_
    refine (Set.union_subset_union ?_ hxsupp).trans (le_of_eq (Set.union_self _))
    rw [Subgroup.zpowers_inv]
    exact w16g_supp_mono (Subgroup.zpowers_le.mpr hq)
  have hzB : s13Supp X (Subgroup.zpowers z) ⊆ s13IsoComps X \ s13Supp X Q := hZleB hz
  have hempty : s13Supp X (Subgroup.zpowers z) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro U hU
    exact (hzB hU).2 (hzsupp hU)
  have hz1 : z = 1 := w16g_eq_one_of_supp_empty h (s13XSupp_le hz) hempty
  rw [← hxz, hz1, mul_one]
  exact hq

theorem w16g_three_plane_eq (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    (hblk : ∀ a ∈ A, s13Supp X (Q.map (MulAut.conj a).toMonoidHom) = s13Supp X Q ∨
      Disjoint (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) (s13Supp X Q)) :
    Q = s13XSupp X (s13Supp X Q) := by
  have hXle := w16g_three_plane_Xle h hH0 hQ3 he hblk
  have hYle := w16g_three_plane_Yle h hH0 hQ3 he hXle
  have hQleY : Q ≤ s13XSupp X (s13Supp X Q) :=
    (le_s13XSupp_iff h.hW (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2)
      h.hXe h.hQX).mpr subset_rfl
  exact le_antisymm hQleY hYle

end CFSG.LocalAnalysis.WeakClosure81
