module

public import Mathlib.Basic.Logic.Basic
public import Mathlib.GroupTheory.PGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section

variable {G : Type*} [Group G] [Finite G]

public theorem CFSG.exists_nontrivial_center_mem_normal (N : Subgroup G) [N.Normal] [Nontrivial N]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)] :
    ∃ x : N, x ≠ 1 ∧ (x : G) ∈ Subgroup.center G := by
  let hGconj : IsPGroup p (ConjAct G) :=
    (Fact.out : IsPGroup p G).of_equiv ConjAct.toConjAct
  have hN_p : IsPGroup p N := (Fact.out : IsPGroup p G).to_subgroup N
  obtain ⟨n, hn_pos, hcardN⟩ := hN_p.nontrivial_iff_card.mp (by infer_instance : Nontrivial N)
  have hdvd : p ∣ Nat.card N := by
    rw [hcardN]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn_pos)
  have hone_fixed : ((1 : N) : N) ∈ MulAction.fixedPoints (ConjAct G) N := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨x, hxfix, hxne⟩ :=
    hGconj.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := N) hdvd hone_fixed
  refine ⟨x, (fun h => hxne h.symm), ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hxg : (ConjAct.toConjAct g) • x = x :=
    (MulAction.mem_fixedPoints.mp hxfix) (ConjAct.toConjAct g)
  have hxg' : (ConjAct.toConjAct g) • (x : G) = x := by
    exact Subtype.ext_iff.mp hxg
  have hconj : g * (x : G) * g⁻¹ = x := by
    simpa [ConjAct.smul_def] using hxg'
  have hmul : g * (x : G) = x * g := by
    simpa [mul_assoc] using congrArg (fun t => t * g) hconj
  simpa [eq_comm] using hmul

theorem CFSG.exists_normal_subgroup_card_eq_prime_in_normal
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)]
    (N : Subgroup G) [N.Normal] (hN_nontrivial : Nontrivial N) :
    ∃ Z : Subgroup G, Z.Normal ∧ Z ≤ N ∧ Nat.card Z = p := by
  let I : Subgroup G := N ⊓ Subgroup.center G
  have hI_p : IsPGroup p I := (Fact.out : IsPGroup p G).to_subgroup I
  obtain ⟨x, hx_ne_one, hx_center⟩ :=
    exists_nontrivial_center_mem_normal (N := N) (p := p)
  have hxI : (x : G) ∈ I := ⟨x.property, hx_center⟩
  haveI : Nontrivial I := by
    refine ⟨⟨1, ⟨⟨x, hxI⟩, ?_⟩⟩⟩
    intro hEq
    have hx_eq_one : x = 1 := by
      apply Subtype.ext
      exact (Subtype.ext_iff.mp hEq).symm
    exact hx_ne_one hx_eq_one
  obtain ⟨n, hn_pos, hcardI⟩ := hI_p.nontrivial_iff_card.mp (by infer_instance : Nontrivial I)
  have hp_dvd : p ∣ Nat.card I := by
    rw [hcardI]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn_pos)
  letI : Fintype I := Fintype.ofFinite I
  have hp_dvd_f : p ∣ Fintype.card I := by
    simpa [Nat.card_eq_fintype_card] using hp_dvd
  obtain ⟨y, hy_order⟩ := exists_prime_orderOf_dvd_card (G := I) p hp_dvd_f
  let Z : Subgroup G := Subgroup.zpowers (y : G)
  have hZ_le_N : Z ≤ N := by
    exact (Subgroup.zpowers_le).2 (y.property.1)
  have hZ_le_center : Z ≤ Subgroup.center G := by
    exact (Subgroup.zpowers_le).2 (y.property.2)
  have hZ_normal : Z.Normal := by
    refine ⟨fun z hz g => ?_⟩
    have hz_center : z ∈ Subgroup.center G := hZ_le_center hz
    have hcomm : g * z = z * g := (Subgroup.mem_center_iff.mp hz_center) g
    have hconj : g * z * g⁻¹ = z := by
      calc
        g * z * g⁻¹ = (z * g) * g⁻¹ := by simp [mul_assoc, hcomm]
        _ = z := by simp [mul_assoc]
    simpa [hconj] using hz
  have hZ_card : Nat.card Z = p := by
    calc
      Nat.card Z = orderOf (y : G) := by
        dsimp [Z]
        exact Nat.card_zpowers (y : G)
      _ = p := by
        simpa using hy_order
  exact ⟨Z, hZ_normal, hZ_le_N, hZ_card⟩

theorem CFSG.exists_normal_subgroup_card_pow_le
    {p : ℕ} [Fact p.Prime] :
    ∀ {G : Type*} [Group G] [Finite G] [Fact (IsPGroup p G)]
      (N : Subgroup G) [N.Normal] {k : ℕ},
      Nat.card N = p ^ k → ∀ r : ℕ, r ≤ k →
        ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = p ^ r
  | G, _, _, _, N, _, 0, hcard, r, hr => by
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
      refine ⟨⊥, inferInstance, bot_le, ?_⟩
      simp [hr0]
  | G, _, _, _, N, _, k + 1, hcard, r, hr => by
      by_cases hr0 : r = 0
      · refine ⟨⊥, inferInstance, bot_le, ?_⟩
        simp [hr0]
      · have hN_nontrivial : Nontrivial N := by
          apply Finite.one_lt_card_iff_nontrivial.mp
          rw [hcard]
          exact one_lt_pow₀ (Fact.out : Nat.Prime p).one_lt (Nat.succ_ne_zero k)
        obtain ⟨Z, hZ_normal, hZ_le_N, hcardZ⟩ :=
          exists_normal_subgroup_card_eq_prime_in_normal (G := G) (p := p)
            (N := N) hN_nontrivial
        letI : Z.Normal := hZ_normal
        let q : G →* (G ⧸ Z) := QuotientGroup.mk' Z
        let Nbar : Subgroup (G ⧸ Z) := N.map q
        have hNbar_normal : Nbar.Normal := by
          simpa [Nbar, q] using (QuotientGroup.map_normal Z N)
        letI : Nbar.Normal := hNbar_normal
        let Npre : Subgroup G := Nbar.comap q
        have hker_le_N : q.ker ≤ N := by
          simpa [q, QuotientGroup.ker_mk'] using hZ_le_N
        have hNpre_eq : Npre = N := by
          simpa [Npre, Nbar] using (Subgroup.comap_map_eq_self (f := q) (H := N) hker_le_N)
        have hcardQuotNpre : Nat.card (Npre ⧸ q.ker.subgroupOf Npre) = Nat.card Nbar := by
          simpa [Npre] using
            (card_quotient_subgroupOf_comap_eq (f := q) (hf := QuotientGroup.mk'_surjective Z)
              (H := Nbar))
        have hcardKerSubNpre : Nat.card (q.ker.subgroupOf Npre) = Nat.card Z := by
          have hcardKerSubNpre' : Nat.card (q.ker.subgroupOf Npre) = Nat.card q.ker := by
            exact Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (Subgroup.ker_le_comap (f := q) (H := Nbar))).toEquiv
          rw [hcardKerSubNpre']
          simp [q, QuotientGroup.ker_mk']
        have hcardN_expr : Nat.card N = Nat.card Nbar * Nat.card Z := by
          have hcardNpre_expr : Nat.card Npre = Nat.card Nbar * Nat.card Z := by
            calc
              Nat.card Npre = Nat.card (Npre ⧸ q.ker.subgroupOf Npre) * Nat.card (q.ker.subgroupOf Npre) := by
                simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := q.ker.subgroupOf Npre))
              _ = Nat.card Nbar * Nat.card Z := by rw [hcardQuotNpre, hcardKerSubNpre]
          simpa [hNpre_eq] using hcardNpre_expr
        have hcardNbar : Nat.card Nbar = p ^ k := by
          apply Nat.eq_of_mul_eq_mul_right ((Fact.out : Nat.Prime p).pos)
          calc
            Nat.card Nbar * p = Nat.card Nbar * Nat.card Z := by simp [hcardZ]
            _ = Nat.card N := hcardN_expr.symm
            _ = p ^ (k + 1) := hcard
            _ = p ^ k * p := by simp [Nat.pow_succ, Nat.mul_comm]
        have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr_pos)
        have hr' : r' ≤ k := Nat.le_of_succ_le_succ hr
        haveI : Fact (IsPGroup p (G ⧸ Z)) := ⟨(Fact.out : IsPGroup p G).to_quotient Z⟩
        obtain ⟨Kbar, hKbar_normal, hKbar_le, hcardKbar⟩ :=
          exists_normal_subgroup_card_pow_le (p := p) (G := (G ⧸ Z)) (N := Nbar)
            (k := k) hcardNbar r' hr'
        letI : Kbar.Normal := hKbar_normal
        refine ⟨Kbar.comap q, inferInstance, ?_, ?_⟩
        · have hcomap_le : Kbar.comap q ≤ Nbar.comap q := Subgroup.comap_mono hKbar_le
          simpa [Npre, hNpre_eq] using hcomap_le
        · have hcardQuotK : Nat.card ((Kbar.comap q) ⧸ q.ker.subgroupOf (Kbar.comap q)) = Nat.card Kbar :=
            card_quotient_subgroupOf_comap_eq (f := q) (hf := QuotientGroup.mk'_surjective Z) (H := Kbar)
          have hcardKerSub : Nat.card (q.ker.subgroupOf (Kbar.comap q)) = Nat.card q.ker := by
            exact Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (Subgroup.ker_le_comap (f := q) (H := Kbar))).toEquiv
          have hcardK_expr : Nat.card (Kbar.comap q) = Nat.card Kbar * Nat.card Z := by
            calc
              Nat.card (Kbar.comap q) =
                  Nat.card ((Kbar.comap q) ⧸ q.ker.subgroupOf (Kbar.comap q)) *
                    Nat.card (q.ker.subgroupOf (Kbar.comap q)) := by
                      simpa using
                        (Subgroup.card_eq_card_quotient_mul_card_subgroup
                          (s := q.ker.subgroupOf (Kbar.comap q)))
              _ = Nat.card Kbar * Nat.card Z := by
                    rw [hcardQuotK, hcardKerSub]
                    simp [q, QuotientGroup.ker_mk']
          calc
            Nat.card (Kbar.comap q) = Nat.card Kbar * Nat.card Z := hcardK_expr
            _ = p ^ r' * p := by rw [hcardKbar, hcardZ]
            _ = p ^ (r' + 1) := by simp [Nat.pow_succ', Nat.mul_comm]

/-- Lemma 1.22: normal subgroups of all intermediate `p`-power orders in a normal subgroup
of a finite `p`-group. -/
public theorem CFSG.exists_normal_subgroup_card_pow_of_normal
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)] (N : Subgroup G) (hN : N.Normal)
    {k : ℕ} (hcard : Nat.card N = p ^ k) :
    ∀ r : ℕ, r ≤ k → ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = p ^ r := by
  letI : N.Normal := hN
  exact exists_normal_subgroup_card_pow_le (p := p) (N := N) (k := k) hcard

end
