module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndRep
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.PartTwo.NotationBlocks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

open CFSG CFSG.OrderReductions.FrattiniAutomorphisms CFSG.RankThree.PartTwo
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (D : Subgroup G)

@[expose] noncomputable def frattiniActN :
    Subgroup.normalizer (D : Set G) →* MulAut (D ⧸ frattini D) :=
  (quotientAutomorphism (frattini D)).comp D.normalizerMonoidHom

variable (p) in
@[expose] noncomputable def frattiniLinN [IsElementaryAbelian p (D ⧸ frattini D)] :
    Subgroup.normalizer (D : Set G) →* Module.End (ZMod p) (Additive (D ⧸ frattini D)) :=
  (Sec4.Census.autToEndP p (D ⧸ frattini D)).comp (frattiniActN D)

omit [Finite G] [Fact p.Prime] in
theorem normalizerMonoidHom_coe (n : Subgroup.normalizer (D : Set G)) (x : D) :
    ((D.normalizerMonoidHom n x : D) : G) = (n : G) * x * (n : G)⁻¹ :=
  rfl

omit [Finite G] in
theorem frattiniLinN_apply [IsElementaryAbelian p (D ⧸ frattini D)]
    (n : Subgroup.normalizer (D : Set G)) (x : D) :
    frattiniLinN p D n (Additive.ofMul (x : D ⧸ frattini D)) =
      Additive.ofMul ((D.normalizerMonoidHom n x : D) : D ⧸ frattini D) :=
  congrArg Additive.ofMul (quotientAutomorphism_apply _ _ _)

theorem finrank_fixed_le_two' (hDp : IsPGroup p D) (hp2 : p ≠ 2) (hexp : ∀ x : D, x ^ p = 1)
    (hclass : commutator D ≤ Subgroup.center D) [IsElementaryAbelian p (D ⧸ frattini D)]
    {t : Subgroup.normalizer (D : Set G)} (ht : orderOf t = 2)
    (hrank : CFSG.pRank p (D ⊓ Subgroup.centralizer {(t : G)} : Subgroup G) ≤ 2) :
    Module.finrank (ZMod p) (Module.End.eigenspace (frattiniLinN p D t) 1) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp' : p.Prime := Fact.out
  obtain ⟨hchar, hVcomm, -, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  set C := fixedSubgroupOf (D.normalizerMonoidHom t) with hC
  have hCmap : C.map D.subtype = D ⊓ Subgroup.centralizer {(t : G)} := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      have h1 := congrArg Subtype.val ((mem_fixedSubgroupOf _ c).mp hc)
      rw [normalizerMonoidHom_coe] at h1
      refine ⟨c.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      change (c : G) * t = t * c
      calc (c : G) * t = (t : G) * c * (t : G)⁻¹ * t := by rw [h1]
        _ = t * c := by group
    · rintro ⟨hgD, hgt⟩
      refine ⟨⟨g, hgD⟩, (mem_fixedSubgroupOf _ _).mpr (Subtype.ext ?_), rfl⟩
      rw [normalizerMonoidHom_coe]
      have h1 : g * (t : G) = t * g := Subgroup.mem_centralizer_singleton_iff.mp hgt
      change (t : G) * g * (t : G)⁻¹ = g
      rw [← h1]
      group
  have hrankC : CFSG.pRank p C ≤ 2 := by
    rw [pRank_congr_mulEquiv hp'.one_lt (C.equivMapOfInjective D.subtype D.subtype_injective),
      hCmap]
    exact hrank
  let Z := Subgroup.zpowers t
  have hZ2 : IsPGroup 2 Z := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ← ht, pow_orderOf_eq_one, one_zpow, Subgroup.coe_one]⟩
  let α : Z →* MulAut D := D.normalizerMonoidHom.comp Z.subtype
  have hN : ∀ b : Z, ∀ n ∈ frattini D, α b n ∈ frattini D := by
    intro b n hn
    have h1 := Subgroup.characteristic_iff_map_eq.mp hchar (α b)
    rw [← h1]
    exact Subgroup.mem_map_of_mem _ hn
  have hcop : ¬ 2 ∣ Nat.card (frattini D) := not_two_dvd_card_of_odd hp2 (hDp.to_subgroup _)
  have hset := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hZ2 α (frattini D) hN
    hcop
  have hlift : ∀ w ∈ Module.End.eigenspace (frattiniLinN p D t) 1,
      ∃ c ∈ C, w = Additive.ofMul (c : D ⧸ frattini D) := by
    intro w hw
    rw [Module.End.mem_eigenspace_iff, one_smul] at hw
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hwx : w = Additive.ofMul (x : D ⧸ frattini D) := by rw [hx]; rfl
    have hfixa : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini D) hN
        ⟨t, Subgroup.mem_zpowers t⟩ (x : D ⧸ frattini D) = (x : D ⧸ frattini D) := by
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      have h1 := hw
      rw [hwx, frattiniLinN_apply] at h1
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
  have hcardE : Nat.card (Module.End.eigenspace (frattiniLinN p D t) 1) ≤ p ^ 2 := by
    refine le_trans ?_ (hrange.trans hCC)
    refine Nat.card_le_card_of_injective
      (fun w => (⟨Additive.toMul (w : Additive (D ⧸ frattini D)), ?_⟩ : f.range)) ?_
    · obtain ⟨c, hc, hcw⟩ := hlift w w.2
      exact ⟨⟨c, hc⟩, by rw [hcw]; rfl⟩
    · intro w₁ w₂ hw
      apply Subtype.ext
      simpa using congrArg Subtype.val hw
  have : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  have : Fintype (Module.End.eigenspace (frattiniLinN p D t) 1) := Fintype.ofFinite _
  have hpow := Module.card_eq_pow_finrank (K := ZMod p)
    (V := Module.End.eigenspace (frattiniLinN p D t) 1)
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
  rw [hpow] at hcardE
  exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp hcardE

theorem false_of_frattiniLinN_eq_one (hDp : IsPGroup p D) (hp2 : p ≠ 2)
    [IsElementaryAbelian p (D ⧸ frattini D)]
    (hodd : Odd (Nat.card (Subgroup.centralizer (D : Set G))))
    {y : Subgroup.normalizer (D : Set G)} (hy2 : orderOf y = 2) (hy : frattiniLinN p D y = 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := D.normalizerMonoidHom y with hσ
  have hker : σ ∈ (quotientAutomorphism (frattini D)).ker := by
    rw [mem_quotientAutomorphism_kernel]
    intro x
    have h1 := congrArg (fun φ : Module.End (ZMod p) (Additive (D ⧸ frattini D)) =>
      φ (Additive.ofMul (x : D ⧸ frattini D))) hy
    simp only [frattiniLinN_apply, Module.End.one_apply] at h1
    exact Additive.ofMul.injective h1
  have hσ2 : σ ^ 2 = 1 := by rw [hσ, ← map_pow, ← hy2, pow_orderOf_eq_one, map_one]
  have hσ1 : σ = 1 := by
    by_contra hne
    have hord : orderOf σ = 2 := orderOf_eq_prime hσ2 hne
    exact hne (prime_order_frattini_kernel_trivial 2 σ hord
      (not_two_dvd_card_of_odd hp2 hDp) hker)
  have hyC : (y : G) ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 := congrArg (fun τ : MulAut D => ((τ ⟨d, hd⟩ : D) : G)) hσ1
    simp only [hσ, normalizerMonoidHom_coe, MulAut.one_apply] at h1
    calc d * (y : G) = (y : G) * d * (y : G)⁻¹ * y := by rw [h1]
      _ = y * d := by group
  have hy2' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy2
  have h1 : orderOf (y : G) ∣ Nat.card (Subgroup.centralizer (D : Set G)) := by
    rw [← Subgroup.orderOf_mk (y : G) hyC]
    exact orderOf_dvd_natCard _
  rw [hy2'] at h1
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)

end CFSG.RankThree.PartTwo.Sec13.Res7Proof
