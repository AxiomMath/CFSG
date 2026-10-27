module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import Mathlib.Algebra.Ring.Parity

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Classical

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6

universe v
universe u

@[expose] public def theorem_6_5_c_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K M H1 : Subgroup L)
    (S SM : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_6_4_statement K M H1 S T →
    inducedKernelFamily K M SM →
      ¬ coherentFamily SM T →
        ∀ p : ℕ, nonabelianPQuotient M K p → ¬ K.relIndex (⊤ : Subgroup L) ∣ p - 1

/-- Peterfalvi `(6.6)`. -/


theorem isMulCommutative_of_isPGroup_commutator_quotient_cyclic
    {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hQp : IsPGroup p Q)
    (hcyc : IsCyclic (Q ⧸ commutator Q)) :
    IsMulCommutative Q := by
  classical
  haveI : Fact (IsPGroup p Q) := ⟨hQp⟩
  have hcomm_le_Φ : commutator Q ≤ frattini Q := by
    intro x hx
    rw [frattini_eq_closure_commutator_union_powers (R := Q) (p := p)]
    exact Subgroup.subset_closure (Or.inl hx)
  obtain ⟨xbar, hxbar⟩ := IsCyclic.exists_generator (α := Q ⧸ commutator Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) xbar
  let H : Subgroup Q := Subgroup.zpowers x
  have hHmap_top : H.map (QuotientGroup.mk' (commutator Q)) = ⊤ := by
    apply top_unique
    intro y _hy
    rw [show H.map (QuotientGroup.mk' (commutator Q)) =
        Subgroup.zpowers (QuotientGroup.mk' (commutator Q) x) by
      simp [H]]
    exact hxbar y
  have hHsup_comm : H ⊔ commutator Q = ⊤ := by
    apply top_unique
    intro y _hy
    have hybar : QuotientGroup.mk' (commutator Q) y ∈
        H.map (QuotientGroup.mk' (commutator Q)) := by
      simp [hHmap_top]
    rcases Subgroup.mem_map.mp hybar with ⟨h, hhH, hhq⟩
    have hzcomm : h⁻¹ * y ∈ commutator Q := by
      apply (QuotientGroup.eq_one_iff (N := commutator Q) (x := h⁻¹ * y)).1
      calc
        QuotientGroup.mk' (commutator Q) (h⁻¹ * y)
            = (QuotientGroup.mk' (commutator Q) h)⁻¹ *
                QuotientGroup.mk' (commutator Q) y := by simp
        _ = 1 := by simp [hhq]
    exact (Subgroup.mem_sup_of_normal_right (s := H) (t := commutator Q) (x := y)).2
      ⟨h, hhH, h⁻¹ * y, hzcomm, by simp⟩
  have hHsup_Φ : H ⊔ frattini Q = ⊤ := by
    apply top_unique
    intro y _hy
    have hy' : y ∈ H ⊔ commutator Q := by simp [hHsup_comm]
    exact (sup_le_sup_left hcomm_le_Φ H) hy'
  have hH_top : H = ⊤ := lemma_1_7_a (R := Q) (p := p) (H := H) hHsup_Φ
  have hQ_cyclic : IsCyclic Q := by
    exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨x, by simpa [H] using hH_top⟩
  letI : IsCyclic Q := hQ_cyclic
  exact ⟨by infer_instance⟩

theorem commutator_quotient_card_data_of_isPGroup_noncomm
    {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hQp : IsPGroup p Q) (hnoncomm : ¬ IsMulCommutative Q) :
    p ^ 2 ≤ Nat.card (Q ⧸ commutator Q) ∧ p ∣ Nat.card (Q ⧸ commutator Q) := by
  classical
  have hQabp : IsPGroup p (Q ⧸ commutator Q) := hQp.to_quotient (commutator Q)
  obtain ⟨n, hcard⟩ := hQabp.exists_card_eq
  have hnot_dvd_p : ¬ Nat.card (Q ⧸ commutator Q) ∣ p := by
    intro hdiv
    have hcyc : IsCyclic (Q ⧸ commutator Q) := isCyclic_of_card_dvd_prime hdiv
    exact hnoncomm (isMulCommutative_of_isPGroup_commutator_quotient_cyclic hQp hcyc)
  have hn_ge_two : 2 ≤ n := by
    by_contra hn
    have hn_le_one : n ≤ 1 := by omega
    have hcard_dvd_p : Nat.card (Q ⧸ commutator Q) ∣ p := by
      rw [hcard]
      simpa using (Nat.pow_dvd_pow p hn_le_one)
    exact hnot_dvd_p hcard_dvd_p
  constructor
  · rw [hcard]
    exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hn_ge_two
  · rw [hcard]
    exact dvd_pow_self p (by omega)

theorem theorem_6_5_c_commutator_quotient_card_eq_relIndex
    {L : Type u} [Group L] [Finite L]
    {K M H1 : Subgroup L}
    (hMH1 : M ≤ H1)
    (hMnormK : (M.subgroupOf K).Normal)
    (hH1normK : (H1.subgroupOf K).Normal)
    (hcommEq : (H1.subgroupOf K).map (QuotientGroup.mk' (M.subgroupOf K)) =
          commutator (K ⧸ M.subgroupOf K)) :
    Nat.card ((K ⧸ M.subgroupOf K) ⧸ commutator (K ⧸ M.subgroupOf K)) =
      H1.relIndex K := by
  classical
  let Msub : Subgroup K := M.subgroupOf K
  let Hsub : Subgroup K := H1.subgroupOf K
  haveI : Msub.Normal := hMnormK
  haveI : Hsub.Normal := hH1normK
  have hMsubHsub : Msub ≤ Hsub := by
    intro x hx
    exact hMH1 hx
  let Q : Type u := K ⧸ Msub
  let Hbar : Subgroup Q := Hsub.map (QuotientGroup.mk' Msub)
  haveI : Hbar.Normal := by
    dsimp [Hbar]
    infer_instance
  let e₁ : Q ⧸ commutator Q ≃* Q ⧸ Hbar :=
    QuotientGroup.quotientMulEquivOfEq (by
      dsimp [Hbar, Q, Msub, Hsub]
      exact hcommEq.symm)
  let e₂ : Q ⧸ Hbar ≃* K ⧸ Hsub :=
    QuotientGroup.quotientQuotientEquivQuotient Msub Hsub hMsubHsub
  calc
    Nat.card ((K ⧸ M.subgroupOf K) ⧸ commutator (K ⧸ M.subgroupOf K))
        = Nat.card (K ⧸ Hsub) := by
          exact Nat.card_congr (e₁.trans e₂).toEquiv
    _ = H1.relIndex K := by
          simpa [Hsub, Subgroup.relIndex] using (Subgroup.index_eq_card (H := Hsub)).symm

theorem theorem_6_5_c_prime_ge_two_mul_add_one_of_odd_dvd_sub_one
    {p n : ℕ} (hp : Nat.Prime p) (hp_ne_two : p ≠ 2)
    (hoddn : Odd n) (hdiv : n ∣ p - 1) :
    2 * n + 1 ≤ p := by
  rcases hdiv with ⟨m, hm⟩
  have hp_gt_one : 1 < p := hp.one_lt
  have hp_pred_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp_gt_one
  have hpodd : Odd p := hp.odd_of_ne_two hp_ne_two
  have hp_pred_even : Even (p - 1) := by
    rcases hpodd with ⟨a, ha⟩
    rw [ha, Nat.add_sub_cancel]
    exact even_two_mul a
  have hm_even : Even m := by
    rw [← Nat.not_odd_iff_even]
    intro hmodd
    have hprod_odd : Odd (n * m) := hoddn.mul hmodd
    exact (Nat.not_odd_iff_even.mpr hp_pred_even) (by simpa [hm] using hprod_odd)
  rcases hm_even with ⟨r, hr⟩
  subst m
  have hr_pos : 0 < r := by
    by_contra hrpos
    have hr0 : r = 0 := by omega
    have : p - 1 = 0 := by simpa [hr0] using hm
    omega
  have hm_ge_two : 2 ≤ r + r := by omega
  have htwo_n_le_pred : 2 * n ≤ p - 1 := by
    calc
      2 * n = n * 2 := by omega
      _ ≤ n * (r + r) := Nat.mul_le_mul_left n hm_ge_two
      _ = p - 1 := hm.symm
  omega

public theorem theorem_6_5_c
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K M H1 : Subgroup L)
    (S SM : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_6_5_c_statement K M H1 S SM T := by
  classical
  intro h64 hSM hnotSM p hpQ hdiv
  rcases h64 with ⟨h61, hoddL, hMH1, hMK, hnil, hcomm, hfrob⟩
  have h64' : hypothesis_6_4_statement K M H1 S T :=
    ⟨h61, hoddL, hMH1, hMK, hnil, hcomm, hfrob⟩
  rcases theorem_6_5_a K M H1 S SM T h64' hSM hnotSM with ⟨_hchief, hupper⟩
  rcases hpQ with ⟨_hpMK, _hpMnormK, _hpMnorm, _hpKnorm, hpprime, hQp, hnoncomm⟩
  haveI : Fact p.Prime := ⟨hpprime⟩
  rcases hcomm with
    ⟨_hMKc, _hH1K, hMH1c, hMnormK, _hMnormc, hH1norm, _hKnormc, hcommEq⟩
  have hH1normK : (H1.subgroupOf K).Normal := hH1norm.subgroupOf K
  let Q : Type u := K ⧸ M.subgroupOf K
  have hcard_eq : Nat.card (Q ⧸ commutator Q) = H1.relIndex K := by
    simpa [Q] using
      theorem_6_5_c_commutator_quotient_card_eq_relIndex
        (K := K) (M := M) (H1 := H1) hMH1c hMnormK hH1normK hcommEq
  have hcard_eq_ft : Fintype.card (Q ⧸ commutator Q) = H1.relIndex K := by
    simpa [Nat.card_eq_fintype_card] using hcard_eq
  have hdata : p ^ 2 ≤ Nat.card (Q ⧸ commutator Q) ∧
      p ∣ Nat.card (Q ⧸ commutator Q) :=
    commutator_quotient_card_data_of_isPGroup_noncomm (Q := Q) hQp hnoncomm
  have hlower : p ^ 2 ≤ H1.relIndex K := by
    simpa [Nat.card_eq_fintype_card, hcard_eq_ft] using hdata.1
  have hp_dvd_Hrel : p ∣ H1.relIndex K := by
    simpa [Nat.card_eq_fintype_card, hcard_eq_ft] using hdata.2
  have hHrel_dvd_L : H1.relIndex K ∣ Nat.card L :=
    (Subgroup.relIndex_dvd_card (H := H1) (K := K)).trans
      (Subgroup.card_subgroup_dvd_card (s := K))
  have hp_dvd_L : p ∣ Nat.card L := hp_dvd_Hrel.trans hHrel_dvd_L
  have hp_ne_two : p ≠ 2 := hoddL.ne_two_of_dvd_nat hp_dvd_L
  let n : ℕ := K.relIndex (⊤ : Subgroup L)
  have hn_odd : Odd n := by
    have hn_dvd_L : n ∣ Nat.card L := by
      simpa [n, Subgroup.relIndex_top_right] using (Subgroup.index_dvd_card (H := K))
    exact hoddL.of_dvd_nat hn_dvd_L
  have hn_pos : 0 < n := by
    rcases hn_odd with ⟨a, ha⟩
    omega
  have hp_ge : 2 * n + 1 ≤ p :=
    theorem_6_5_c_prime_ge_two_mul_add_one_of_odd_dvd_sub_one
      hpprime hp_ne_two hn_odd (by simpa [n] using hdiv)
  have hstrict : 4 * n ^ 2 + 1 < p ^ 2 := by
    nlinarith
  have hupper' : H1.relIndex K ≤ 4 * n ^ 2 + 1 := by
    simpa [n] using hupper
  exact (not_lt_of_ge hupper') (lt_of_lt_of_le hstrict hlower)

end CFSG.Section6
