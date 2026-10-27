module

public import CFSG.RankThree.PartOne.S9.OddCore.TorsionLinear
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankFrattini
public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.RankThree.PartOne.Torsion37

open CFSG CFSG.RankThree.PartOne.FixedRank36 Subgroup
open scoped commutatorElement IsMulCommutative

theorem isPGroup_zpowers_two {M : Type*} [Group M] {x : M} {n : ℕ} (hx : x ^ 2 ^ n = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  rintro ⟨g, hg⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  refine ⟨n, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem isPGroup_zpowers_map {S M : Type*} [Group S] [Group M] (hS : IsPGroup 2 S)
    (f : S →* M) (s : S) : IsPGroup 2 (Subgroup.zpowers (f s)) := by
  obtain ⟨k, hk⟩ := hS s
  refine isPGroup_zpowers_two (n := k) ?_
  rw [← map_pow, hk, map_one]

theorem two_ne_zero_zmod {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h')

theorem relIndex_inSubgroup_frattini_eq_card {G : Type*} [Group G] (D : Subgroup G) :
    (inSubgroup frattini D).relIndex D = Nat.card (↥D ⧸ frattini ↥D) := by
  have h : (Subgroup.map D.subtype (frattini ↥D)).subgroupOf D = frattini ↥D :=
    Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
  rw [Subgroup.relIndex, inSubgroup, h]
  rfl

@[expose] noncomputable def conjRep {G : Type*} [Group G] (R D : Subgroup G) [D.Normal] :
    ↥R →* MulAut ↥D :=
  MulAut.conjNormal.comp R.subtype

theorem coe_conjRep {G : Type*} [Group G] (R D : Subgroup G) [D.Normal] (r : R) (d : D) :
    ((conjRep R D r d : D) : G) = (r : G) * (d : G) * (r : G)⁻¹ := rfl

theorem frattini_module_facts {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {D R : Subgroup G} [D.Normal] (hD : IsPGroup q D)
    (hrel : (inSubgroup frattini D).relIndex D = q ^ 4)
    (hR : IsExtraspecialPGroup 2 R) (hR32 : Nat.card R = 32)
    (hRD : R ⊓ Subgroup.centralizer (D : Set G) = ⊥) :
    (∀ X : Subgroup G, inSubgroup frattini D ≤ X → X ≤ D → R ≤ Subgroup.normalizer (X : Set G) →
        X = inSubgroup frattini D ∨ X = D) ∧
    (∀ s ∈ R, orderOf s = 2 → s ∉ inSubgroup Subgroup.center R →
        ∃ x ∈ D, x ∉ inSubgroup frattini D ∧ x ∈ Subgroup.centralizer ({s} : Set G)) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hel : IsElementaryAbelian q (↥D ⧸ frattini ↥D) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hD).2.2.2.1
  have hfd : FiniteDimensional (ZMod q) (Additive (↥D ⧸ frattini ↥D)) := Module.Finite.of_finite
  set ρ : ↥R →* MulAut ↥D := conjRep R D with hρ
  have hR2 : IsPGroup 2 R := hR.1
  have hdim : Module.finrank (ZMod q) (Additive (↥D ⧸ frattini ↥D)) = 4 := by
    have h1 : Nat.card (↥D ⧸ frattini ↥D) = q ^ 4 := by
      rw [← relIndex_inSubgroup_frattini_eq_card, hrel]
    have h2 : Nat.card (Additive (↥D ⧸ frattini ↥D)) = q ^ 4 := by
      rw [← h1]
      exact Nat.card_congr Additive.toMul
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod] at h2
    exact Nat.pow_right_injective hq.two_le h2
  have hinj : Function.Injective (frattiniRep q ρ) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : ρ r = 1 :=
      frattiniRep_eq_one hD hq2 ρ r (isPGroup_zpowers_map hR2 ρ r) hr
    have hmem : (r : G) ∈ R ⊓ Subgroup.centralizer (D : Set G) := by
      refine ⟨r.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h := congrArg (fun f : MulAut ↥D => ((f ⟨g, hg⟩ : ↥D) : G)) h1
      simp only [hρ, coe_conjRep, MulAut.one_apply] at h
      calc g * (r : G) = ((r : G) * g * (r : G)⁻¹) * r := by rw [h]
        _ = r * g := by group
    rw [hRD, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨-, hirr, hfix⟩ := minimal_module_facts (two_ne_zero_zmod hq hq2) hR hR32
    (frattiniRep q ρ) hinj hdim
  refine ⟨fun X hΦX hXD hRX => ?_, fun s hs hs2 hsc => ?_⟩
  ·
    set E := ↥D ⧸ frattini ↥D with hE
    let Xq : Subgroup E := (X.subgroupOf D).map (QuotientGroup.mk' (frattini ↥D))
    let U : Submodule (ZMod q) (Additive E) :=
      { carrier := {v | Additive.toMul v ∈ Xq}
        add_mem' := fun {a b} ha hb => by
          change Additive.toMul (a + b) ∈ Xq
          rw [toMul_add]
          exact Xq.mul_mem ha hb
        zero_mem' := by
          change Additive.toMul (0 : Additive E) ∈ Xq
          rw [toMul_zero]
          exact Xq.one_mem
        smul_mem' := fun c v hv => by
          change Additive.toMul (c • v) ∈ Xq
          have hc : c • v = c.val • v := by
            rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_zmod_val]
          rw [hc, toMul_nsmul]
          exact Xq.pow_mem hv _ }
    have hmemU : ∀ x : ↥D, Additive.ofMul (x : E) ∈ U ↔ (x : G) ∈ X := by
      intro x
      change (x : E) ∈ Xq ↔ _
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hy' : (y : G) ∈ X := hy
        have h1 : y⁻¹ * x ∈ frattini ↥D := QuotientGroup.eq.1 hyx
        have h2 : (((y⁻¹ * x : ↥D)) : G) ∈ inSubgroup frattini D := ⟨_, h1, rfl⟩
        have h3 : (((y⁻¹ * x : ↥D)) : G) ∈ X := hΦX h2
        have h4 : (x : G) = (y : G) * ((y⁻¹ * x : ↥D) : G) := by simp
        rw [h4]
        exact X.mul_mem hy' h3
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hUinv : ∀ r : ↥R, ∀ v ∈ U, frattiniRep q ρ r v ∈ U := by
      intro r v hv
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      have hvx : v = Additive.ofMul (x : E) := by rw [hx]; rfl
      rw [hvx] at hv ⊢
      rw [frattiniRep_apply]
      rw [hmemU] at hv ⊢
      have h1 := (Subgroup.mem_normalizer_iff.1 (hRX r.2) (x : G)).1 hv
      exact h1
    rcases hirr U hUinv with hU | hU
    · left
      refine le_antisymm (fun x hx => ?_) hΦX
      have hxD := hXD hx
      have h1 : Additive.ofMul ((⟨x, hxD⟩ : ↥D) : E) ∈ U := (hmemU ⟨x, hxD⟩).2 hx
      rw [hU, Submodule.mem_bot, ofMul_eq_zero] at h1
      exact ⟨⟨x, hxD⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
    · right
      refine le_antisymm hXD (fun d hd => ?_)
      have h1 : Additive.ofMul ((⟨d, hd⟩ : ↥D) : E) ∈ U := by rw [hU]; exact Submodule.mem_top
      exact (hmemU ⟨d, hd⟩).1 h1
  ·
    have hsR : (⟨s, hs⟩ : ↥R) ∉ Subgroup.center ↥R := fun h => hsc ⟨⟨s, hs⟩, h, rfl⟩
    have hord : orderOf (⟨s, hs⟩ : ↥R) = 2 := by
      rw [← hs2]
      exact Subgroup.orderOf_mk s hs
    obtain ⟨v, hv0, hv⟩ := hfix ⟨s, hs⟩ hsR hord
    obtain ⟨x, hxfix, hxv⟩ := exists_fixed_lift hD hq2 ρ ⟨s, hs⟩
      (isPGroup_zpowers_map hR2 ρ _) v
      (by rw [Module.End.mem_eigenspace_iff, one_smul]; exact hv)
    refine ⟨(x : G), x.2, ?_, ?_⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      rw [hyx'] at hy
      apply hv0
      rw [← hxv, ofMul_eq_zero]
      exact (QuotientGroup.eq_one_iff x).2 hy
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg (fun f : ↥D => (f : G)) hxfix
      simp only [hρ, coe_conjRep] at h
      calc (x : G) * s = s * x * s⁻¹ * s := by rw [h]
        _ = s * x := by group

end CFSG.RankThree.PartOne.Torsion37
