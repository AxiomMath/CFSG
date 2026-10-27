module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndRep
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.PartTwo.NotationBlocks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.OrderReductions.FrattiniAutomorphisms CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open scoped IsMulCommutative Matrix

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {D : Subgroup G}

theorem finrank_fixed_le_two (h : CriticalAt p D) (hp2 : p ≠ 2)
    [IsElementaryAbelian p (D ⧸ frattini D)] (hloc : localRank p G < 3) {t : G}
    (ht : orderOf t = 2) :
    Module.finrank (ZMod p) (Module.End.eigenspace (frattiniLin h t) 1) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp' : p.Prime := Fact.out
  have hDp : IsPGroup p D := pCore_isPGroup.to_le h.le
  have : D.Normal := h.normal
  have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by simpa using h.exp x x.2)
  have hclass := h.commutator_le_center
  obtain ⟨hchar, hVcomm, -, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  set C := fixedSubgroupOf (h.conjD t) with hC
  have hCt : ∀ c ∈ C.map D.subtype, c * t = t * c := by
    rintro _ ⟨c, hc, rfl⟩
    have h1 := congrArg Subtype.val ((mem_fixedSubgroupOf (h.conjD t) c).mp hc)
    rw [h.conjD_apply] at h1
    change (c : G) * t = t * c
    calc (c : G) * t = t * c * t⁻¹ * t := by rw [h1]
      _ = t * c := by group
  have hrankC : CFSG.pRank p C ≤ 2 := by
    have h1 := pRank_le_localRank_of_centralizes hp' hp2 ht hCt
    rw [← pRank_congr_mulEquiv hp'.one_lt (C.equivMapOfInjective D.subtype D.subtype_injective)]
      at h1
    omega
  let Z := Subgroup.zpowers t
  have hZ2 : IsPGroup 2 Z := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ← ht, pow_orderOf_eq_one, one_zpow, Subgroup.coe_one]⟩
  let α : Z →* MulAut D := h.conjD.comp Z.subtype
  have hN : ∀ b : Z, ∀ n ∈ frattini D, α b n ∈ frattini D := by
    intro b n hn
    have h1 := Subgroup.characteristic_iff_map_eq.mp hchar (α b)
    rw [← h1]
    exact Subgroup.mem_map_of_mem _ hn
  have hcop : ¬ 2 ∣ Nat.card (frattini D) := not_two_dvd_card_of_odd hp2 (hDp.to_subgroup _)
  have hset := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hZ2 α (frattini D) hN
    hcop
  have hlift : ∀ w ∈ Module.End.eigenspace (frattiniLin h t) 1,
      ∃ c ∈ C, w = Additive.ofMul (c : D ⧸ frattini D) := by
    intro w hw
    rw [Module.End.mem_eigenspace_iff, one_smul] at hw
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hwx : w = Additive.ofMul (x : D ⧸ frattini D) := by rw [hx]; rfl
    have hfixa : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini D) hN
        ⟨t, Subgroup.mem_zpowers t⟩ (x : D ⧸ frattini D) = (x : D ⧸ frattini D) := by
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      have h1 := hw
      rw [hwx, frattiniLin_apply] at h1
      exact congrArg Additive.toMul h1
    have hmem : (x : D ⧸ frattini D) ∈ {q : D ⧸ frattini D | ∀ b : Z,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini D) hN b q =
          q} := by
      rintro ⟨b, hb⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hb' : (⟨t ^ k, hb⟩ : Z) = ⟨t, Subgroup.mem_zpowers t⟩ ^ k := Subtype.ext (by simp)
      rw [hb', map_zpow]
      exact zpow_apply_eq_self_of_apply_eq_self hfixa k
    rw [hset] at hmem
    obtain ⟨c, hc, hcx⟩ := hmem
    refine ⟨c, hc ⟨t, Subgroup.mem_zpowers t⟩, ?_⟩
    rw [hwx, ← hcx]
    rfl
  let f : C →* D ⧸ frattini D := (QuotientGroup.mk' (frattini D)).comp C.subtype
  have hcomm_ker : commutator C ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hVcomm.is_comm.comm _ _
  have hrange : Nat.card f.range ≤ Nat.card (C ⧸ commutator C) := by
    have h1 := Subgroup.card_ker_mul_card_range f
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator C)
    have h3 := Subgroup.card_le_of_le hcomm_ker
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    have h4 : Nat.card f.range * Nat.card f.ker ≤
        Nat.card (C ⧸ commutator C) * Nat.card f.ker := by
      calc Nat.card f.range * Nat.card f.ker = Nat.card C := by rw [← h1, mul_comm]
        _ = Nat.card (C ⧸ commutator C) * Nat.card (commutator C) := h2
        _ ≤ Nat.card (C ⧸ commutator C) * Nat.card f.ker := Nat.mul_le_mul_left _ h3
    exact Nat.le_of_mul_le_mul_right h4 hpos
  have hCC : Nat.card (C ⧸ commutator C) ≤ p ^ 2 := by
    have hCp : IsPGroup p C := hDp.to_subgroup C
    have hrank := (class_two_small_rank_order_bounds hCp (subgroup_pow_eq_one hexp C)
      (subgroup_commutator_le_center hclass C)).1 hrankC
    obtain ⟨k, hk⟩ := (hCp.to_quotient (commutator C)).exists_card_eq
    have hk2 := (quotient_commutator_rank hp' (subgroup_pow_eq_one hexp C) hk).2
    rw [hk]
    exact Nat.pow_le_pow_right hp'.pos (hk2 ▸ hrank)
  have hcardE : Nat.card (Module.End.eigenspace (frattiniLin h t) 1) ≤ p ^ 2 := by
    refine le_trans ?_ (hrange.trans hCC)
    refine Nat.card_le_card_of_injective
      (fun w => (⟨Additive.toMul (w : Additive (D ⧸ frattini D)), ?_⟩ : f.range)) ?_
    · obtain ⟨c, hc, hcw⟩ := hlift w w.2
      exact ⟨⟨c, hc⟩, by rw [hcw]; rfl⟩
    · intro w₁ w₂ hw
      apply Subtype.ext
      simpa using congrArg Subtype.val hw
  have : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  have : Fintype (Module.End.eigenspace (frattiniLin h t) 1) := Fintype.ofFinite _
  have hpow := Module.card_eq_pow_finrank (K := ZMod p)
    (V := Module.End.eigenspace (frattiniLin h t) 1)
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
  rw [hpow] at hcardE
  exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp hcardE

end CFSG.RankThree.PartTwo.Sec4.Census
