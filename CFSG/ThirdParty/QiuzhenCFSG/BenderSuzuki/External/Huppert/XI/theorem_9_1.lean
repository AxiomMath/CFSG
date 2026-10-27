module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.FrobeniusKernel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_6_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.formula_1_15
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.InducedIrreducible
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Mackey
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_8
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.BrauerPermutation
import Mathlib.NumberTheory.Multiplicity

namespace CFSG
end CFSG
open CFSG

attribute [local simp] Representation.isTrivial_def

/-!
# Ito XI.9.1

This group-theoretic Frobenius-kernel leaf is independent of every other
unproved theorem used by XI.11.16.
-/

namespace CFSG.BenderSuzuki
namespace External

noncomputable section

open scoped BigOperators commutatorElement

open Section1

universe u v

private theorem xi91_involution_fixedPointFree_of_odd_stabilizer
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htrans : MulAction.IsPretransitive G Omega)
    (a : Omega)
    (hstabOdd : Odd (Nat.card (MulAction.stabilizer G a)))
    (t : G) (htorder : orderOf t = 2) :
    ∀ x : Omega, t • x ≠ x := by
  let : MulAction.IsPretransitive G Omega := htrans
  intro x hfix
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a x
  have hstabCard :
      Nat.card (MulAction.stabilizer G x) =
        Nat.card (MulAction.stabilizer G a) := by
    exact Nat.card_congr
      (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv.symm
  have hstabOddX : Odd (Nat.card (MulAction.stabilizer G x)) := by
    rw [hstabCard]
    exact hstabOdd
  let tx : MulAction.stabilizer G x := ⟨t, hfix⟩
  have htxorder : orderOf tx = 2 := by
    simpa [tx] using (Subgroup.orderOf_coe tx).symm.trans htorder
  have htwoDvd : 2 ∣ Nat.card (MulAction.stabilizer G x) := by
    rw [← htxorder]
    exact orderOf_dvd_natCard tx
  exact (Nat.not_even_iff_odd.mpr hstabOddX)
    (even_iff_two_dvd.mpr htwoDvd)

private theorem xi91_pointStabilizer_card_odd
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hFp : IsPGroup p F)
    (hDcardOdd : Odd (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    Odd (Nat.card (MulAction.stabilizer G a)) := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨k, hFcard⟩ := IsPGroup.iff_card.mp hFp
  have hFcardOdd : Odd (Nat.card F) := by
    rw [hFcard]
    exact (hp.odd_of_ne_two hp2).pow
  rw [← hFrob.isComplement'.card_mul_card]
  exact hFcardOdd.mul hDcardOdd

private theorem xi91_actor_card_dvd_group_card_sub_one
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hfree : ∀ a : A, a ≠ 1 → ∀ v : V, a • v = v → v = 1) :
    Nat.card A ∣ Nat.card V - 1 := by
  classical
  let V0 := {v : V // v ≠ 1}
  let : MulAction A V0 :=
    { smul := fun a v => ⟨a • (v : V), by
        intro h
        apply v.2
        have h' := congrArg (fun x : V => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro v
        apply Subtype.ext
        change (1 : A) • (v : V) = (v : V)
        simp
      mul_smul := by
        intro a b v
        apply Subtype.ext
        change (a * b) • (v : V) = a • (b • (v : V))
        rw [mul_smul] }
  have hstab : ∀ v : V0, MulAction.stabilizer A v = ⊥ := by
    intro v
    rw [eq_bot_iff]
    intro a ha
    have hav : a • v = v := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha1
    have hane : a ≠ 1 := by
      intro h
      apply ha1
      simp [h]
    exact v.2 (hfree a hane (v : V) (congrArg Subtype.val hav))
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardV0 : Nat.card V0 = Nat.card V - 1 := by
    let : Fintype V := Fintype.ofFinite V
    let : Fintype V0 := Fintype.ofFinite V0
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {v : V // v ≠ 1} = Fintype.card V - 1
    simp
  rw [hcardV0, Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A V0)), by
    rw [mul_comm]
    exact hcard⟩

/-- The elementary cardinal parameters of the Zassenhaus action, placed
before the XI.1.5 helpers that use them. -/
private theorem xi91_action_parameters_core
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    Fintype.card Omega = Nat.card F + 1 ∧
      Nat.card (MulAction.stabilizer G a) =
        Nat.card F * Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∧
      Nat.card G = Fintype.card Omega * Nat.card F * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∧
      Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∣
        Nat.card F - 1 := by
  classical
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change Fintype.card Omega = Nat.card F + 1 ∧
    Nat.card H = Nat.card F * Nat.card D ∧
    Nat.card G = Fintype.card Omega * Nat.card F * Nat.card D ∧
    Nat.card D ∣ Nat.card F - 1
  have hOmegaCard : 1 < Fintype.card Omega :=
    Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
  let n := Fintype.card Omega - 1
  have hdegree : Fintype.card Omega = n + 1 := by
    dsimp [n]
    omega
  have hFcard : Nat.card F = n :=
    huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
      n hdegree htwo a b hab F hFrob
  have hOmegaEq : Fintype.card Omega = Nat.card F + 1 := by
    rw [hFcard, ← hdegree]
  have hHcard : Nat.card H = Nat.card F * Nat.card D :=
    hFrob.isComplement'.card_mul_card.symm
  have hGcard : Nat.card G = Fintype.card Omega * Nat.card F * Nat.card D := by
    let : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    let : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hindex : H.index = Fintype.card Omega := by
      calc
        H.index = Nat.card Omega := MulAction.index_stabilizer_of_transitive G a
        _ = Fintype.card Omega := Nat.card_eq_fintype_card
    have hmul := H.card_mul_index
    rw [hindex] at hmul
    calc
      Nat.card G = Nat.card H * Fintype.card Omega := hmul.symm
      _ = Fintype.card Omega * Nat.card F * Nat.card D := by
        rw [hHcard]
        ac_rfl
  have hdiv : Nat.card D ∣ Nat.card F - 1 := by
    let : F.Normal := hFrob.normal
    let : MulDistribMulAction D F :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer D F
        (Subgroup.le_normalizer_of_normal (H := F))
    apply xi91_actor_card_dvd_group_card_sub_one
    intro d hd f hfix
    have hconj : (d : H) * (f : H) * (d : H)⁻¹ = (f : H) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hfix
    have hcomm : (d : H) * (f : H) = (f : H) * (d : H) := by
      have h := congrArg (fun x : H => x * (d : H)) hconj
      simpa [mul_assoc] using h
    have hfcent : (f : H) ∈ elementCentralizerIn F (d : H) :=
      ⟨f.property, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hcent : elementCentralizerIn F (d : H) = ⊥ :=
      (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob d hd
    have hfbot : (f : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcent] using hfcent
    exact Subtype.ext (by simpa using hfbot)
  exact ⟨hOmegaEq, hHcard, hGcard, hdiv⟩

/-- Membership in the ambient image of a two-point stabilizer is exactly
fixing both distinguished points. -/
private theorem xi91_twoPointStabilizer_map_mem_iff
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (a b : Omega) (hab : a ≠ b) (g : G) :
    g ∈
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype ↔
      g • a = a ∧ g • b = b := by
  constructor
  · rintro ⟨h, hhD, rfl⟩
    exact ⟨h.property,
      congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hhD)⟩
  · rintro ⟨hga, hgb⟩
    let h : MulAction.stabilizer G a := ⟨g, hga⟩
    let d : MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) :=
      ⟨h, by
        rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        exact hgb⟩
    exact ⟨d, d.property, rfl⟩

/-- An ambient normalizer element outside the two-point stabilizer
interchanges the two distinguished points. -/
private theorem xi91_twoPointStabilizer_normalizer_notMem_swaps
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (x : G)
    (hxnorm :
      x ∈ Subgroup.normalizer
        (((MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype : Subgroup G) : Set G))
    (hxnot :
      x ∉
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype) :
    x • a = b ∧ x • b = a := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  obtain ⟨z, hz⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.complement_ne_bot
  let zg : G := ((z : H) : G)
  have hzgD : zg ∈ Dg := by
    exact ⟨(z : H), z.property, rfl⟩
  have hzgne : zg ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hzga : zg • a = a := (z : H).property
  have hzgb : zg • b = b :=
    congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp z.property)
  have hxconjD : x * zg * x⁻¹ ∈ Dg :=
    (Subgroup.mem_normalizer_iff.mp (by simpa [H, D, Dg] using hxnorm) zg).mp hzgD
  have hxconjne : x * zg * x⁻¹ ≠ 1 := by
    intro h
    apply hzgne
    have := congrArg (fun q : G => x⁻¹ * q * x) h
    simpa [mul_assoc] using this
  have hxconjfix :=
    (xi91_twoPointStabilizer_map_mem_iff a b hab (x * zg * x⁻¹)).mp (by
      simpa [H, D, Dg] using hxconjD)
  have himage (c : Omega) (hzc : zg • c = c) :
      x • c = a ∨ x • c = b := by
    by_cases hca : x • c = a
    · exact Or.inl hca
    by_cases hcb : x • c = b
    · exact Or.inr hcb
    exfalso
    apply
      (hat_most_two_fixed_points
        (x * zg * x⁻¹) hxconjne a b (x • c)
        hab (Ne.symm hca) (Ne.symm hcb))
    refine ⟨hxconjfix.1, hxconjfix.2, ?_⟩
    calc
      (x * zg * x⁻¹) • (x • c) = x • (zg • c) := by
        simp only [mul_smul, inv_smul_smul]
      _ = x • c := by rw [hzc]
  have hxa := himage a hzga
  have hxb := himage b hzgb
  rcases hxa with hxa | hxa
  · have hxb' : x • b = b := by
      rcases hxb with hxba | hxbb
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxa, hxba]
      · exact hxbb
    exfalso
    apply hxnot
    apply (xi91_twoPointStabilizer_map_mem_iff a b hab x).mpr
    exact ⟨hxa, hxb'⟩
  · have hxb' : x • b = a := by
      rcases hxb with hxba | hxbb
      · exact hxba
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxa, hxbb]
    exact ⟨hxa, hxb'⟩

/-- The ambient normalizer of a nontrivial two-point stabilizer has index two
over that stabilizer: its elements either fix or interchange the two points. -/
private theorem xi91_twoPointStabilizer_normalizer_index_two
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    let H := MulAction.stabilizer G a
    let D := MulAction.stabilizer H
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
    let Dg := D.map H.subtype
    (Dg.subgroupOf (Subgroup.normalizer (Dg : Set G))).index = 2 := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change Dsub.index = 2
  obtain ⟨z, hz⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.complement_ne_bot
  let zg : G := ((z : H) : G)
  have hzgD : zg ∈ Dg := by
    exact ⟨(z : H), z.property, rfl⟩
  have hzgne : zg ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hzga : zg • a = a := (z : H).property
  have hzgb : zg • b = b :=
    congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp z.property)
  obtain ⟨s, hsa, hsb⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo) hab hab.symm
  have hsinva : s⁻¹ • a = b := by
    rw [← hsb, inv_smul_smul]
  have hsinvb : s⁻¹ • b = a := by
    rw [← hsa, inv_smul_smul]
  have hsT : s ∈ T := by
    rw [show T = Subgroup.normalizer (Dg : Set G) from rfl,
      Subgroup.mem_normalizer_iff]
    intro g
    rw [show g ∈ Dg ↔ g • a = a ∧ g • b = b by
      simpa [H, D, Dg] using xi91_twoPointStabilizer_map_mem_iff a b hab g]
    rw [show s * g * s⁻¹ ∈ Dg ↔
        (s * g * s⁻¹) • a = a ∧ (s * g * s⁻¹) • b = b by
      simpa [H, D, Dg] using
        xi91_twoPointStabilizer_map_mem_iff a b hab (s * g * s⁻¹)]
    constructor
    · rintro ⟨hga, hgb⟩
      constructor
      · simp only [mul_smul, hsinva, hgb, hsb]
      · simp only [mul_smul, hsinvb, hga, hsa]
    · rintro ⟨hcga, hcgb⟩
      constructor
      · calc
          g • a = s⁻¹ • ((s * g * s⁻¹) • (s • a)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = s⁻¹ • ((s * g * s⁻¹) • b) := by rw [hsa]
          _ = s⁻¹ • b := by rw [hcgb]
          _ = a := hsinvb
      · calc
          g • b = s⁻¹ • ((s * g * s⁻¹) • (s • b)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = s⁻¹ • ((s * g * s⁻¹) • a) := by rw [hsb]
          _ = s⁻¹ • a := by rw [hcga]
          _ = b := hsinva
  let sT : T := ⟨s, hsT⟩
  have hsTnot : sT ∉ Dsub := by
    intro hsD
    have hsDg : s ∈ Dg := hsD
    have hsfix :=
      (xi91_twoPointStabilizer_map_mem_iff a b hab s).mp (by
        simpa [H, D, Dg] using hsDg)
    exact hab (hsfix.1.symm.trans hsa)
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨sT, hsTnot, ?_⟩
  intro x
  by_cases hxD : (x : G) ∈ Dg
  · exact Or.inr hxD
  · have hxswap :
        (x : G) • a = b ∧ (x : G) • b = a := by
      exact xi91_twoPointStabilizer_normalizer_notMem_swaps
        hat_most_two_fixed_points a b hab F hFrob (x : G)
        x.property (by simpa [H, D, Dg] using hxD)
    left
    change ((x * sT : T) : G) ∈ Dg
    apply (xi91_twoPointStabilizer_map_mem_iff a b hab ((x * sT : T) : G)).mpr
    constructor
    · change ((x : G) * s) • a = a
      rw [mul_smul, hsa, hxswap.2]
    · change ((x : G) * s) • b = b
      rw [mul_smul, hsb, hxswap.1]

/-- When the two-point stabilizer has odd order, its index-two ambient
normalizer contains an involution interchanging the two points. -/
private theorem xi91_odd_twoPointStabilizer_exists_swap_involution
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    ∃ s : G, s ^ 2 = 1 ∧ s • a = b ∧ s • b = a := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      xi91_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  let : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  have hDgcard : Nat.card Dg = Nat.card D := by
    simpa [Dg] using
      (Subgroup.card_map_of_injective
        (K := D) (f := H.subtype) H.subtype_injective)
  have hDsubcard : Nat.card Dsub = Nat.card D := by
    calc
      Nat.card Dsub = Nat.card Dg :=
        natCard_subgroupOf_eq Dg T Subgroup.le_normalizer
      _ = Nat.card D := hDgcard
  have hcop : (Nat.card Dsub).Coprime Dsub.index := by
    rw [hindex, hDsubcard]
    simpa [D] using hodd.coprime_two_right
  obtain ⟨C, hC⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  have hCcard : Nat.card C = 2 :=
    hC.index_eq_card.symm.trans hindex
  have hCnontrivial : Nontrivial C :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial C := hCnontrivial
  obtain ⟨c, hcne⟩ := exists_ne (1 : C)
  have hcnotD : (c : T) ∉ Dsub := by
    intro hcD
    have hcone : (c : T) = 1 :=
      Subgroup.disjoint_def.mp hC.disjoint c.property hcD
    apply hcne
    exact Subtype.ext hcone
  have hcpowC : c ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa [hCcard] using orderOf_dvd_natCard c
  have hcpowG : (((c : C) : T) : G) ^ 2 = 1 := by
    simpa using congrArg (fun q : C => (((q : C) : T) : G)) hcpowC
  have hcswap :
      (((c : C) : T) : G) • a = b ∧
        (((c : C) : T) : G) • b = a := by
    apply xi91_twoPointStabilizer_normalizer_notMem_swaps
      hat_most_two_fixed_points a b hab F hFrob
    · exact (c : T).property
    · intro hcDg
      apply hcnotD
      exact hcDg
  exact ⟨(((c : C) : T) : G), hcpowG, hcswap⟩

/-- The normalizer of a nontrivial subgroup of the two-point stabilizer
already normalizes the whole two-point stabilizer.  This is the fixed-point
argument used in XI.1.5 before applying Burnside transfer. -/
private theorem zassenhaus_twoPointSubgroup_normalizer_le
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (Q : Subgroup G)
    (hQle :
      Q ≤
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype)
    (hQne : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer
        (((MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype : Subgroup G) : Set G) := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  change Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Dg : Set G)
  intro x hx
  obtain ⟨⟨z, hzQ⟩, hzne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  have hzD : z ∈ Dg := by simpa [H, D, Dg] using hQle hzQ
  have hzfix : z • a = a ∧ z • b = b :=
    (xi91_twoPointStabilizer_map_mem_iff a b hab z).mp (by
      simpa [H, D, Dg] using hzD)
  have hxzQ : x * z * x⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hx z).mp hzQ
  have hxzD : x * z * x⁻¹ ∈ Dg := by
    simpa [H, D, Dg] using hQle hxzQ
  have hxzne : x * z * x⁻¹ ≠ 1 := by
    intro h
    apply hzne
    have := congrArg (fun q : G => x⁻¹ * q * x) h
    simpa [mul_assoc] using this
  have hxzfix :
      (x * z * x⁻¹) • a = a ∧ (x * z * x⁻¹) • b = b :=
    (xi91_twoPointStabilizer_map_mem_iff a b hab (x * z * x⁻¹)).mp (by
      simpa [H, D, Dg] using hxzD)
  have himage (c : Omega) (hzc : z • c = c) :
      x • c = a ∨ x • c = b := by
    by_cases hca : x • c = a
    · exact Or.inl hca
    by_cases hcb : x • c = b
    · exact Or.inr hcb
    exfalso
    apply
      (hat_most_two_fixed_points (x * z * x⁻¹) hxzne a b (x • c)
        hab (Ne.symm hca) (Ne.symm hcb))
    refine ⟨hxzfix.1, hxzfix.2, ?_⟩
    calc
      (x * z * x⁻¹) • (x • c) = x • (z • c) := by
        simp only [mul_smul, inv_smul_smul]
      _ = x • c := by rw [hzc]
  have hxa := himage a hzfix.1
  have hxb := himage b hzfix.2
  have hxpair :
      (x • a = a ∧ x • b = b) ∨ (x • a = b ∧ x • b = a) := by
    rcases hxa with hxaa | hxab
    · left
      refine ⟨hxaa, ?_⟩
      rcases hxb with hxba | hxbb
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxaa, hxba]
      · exact hxbb
    · right
      refine ⟨hxab, ?_⟩
      rcases hxb with hxba | hxbb
      · exact hxba
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxab, hxbb]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [show g ∈ Dg ↔ g • a = a ∧ g • b = b by
    simpa [H, D, Dg] using xi91_twoPointStabilizer_map_mem_iff a b hab g]
  rw [show x * g * x⁻¹ ∈ Dg ↔
      (x * g * x⁻¹) • a = a ∧ (x * g * x⁻¹) • b = b by
    simpa [H, D, Dg] using
      xi91_twoPointStabilizer_map_mem_iff a b hab (x * g * x⁻¹)]
  rcases hxpair with ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩
  · have hxinva : x⁻¹ • a = a := by
      calc
        x⁻¹ • a = x⁻¹ • (x • a) := congrArg (fun y => x⁻¹ • y) hxa.symm
        _ = a := inv_smul_smul x a
    have hxinvb : x⁻¹ • b = b := by
      calc
        x⁻¹ • b = x⁻¹ • (x • b) := congrArg (fun y => x⁻¹ • y) hxb.symm
        _ = b := inv_smul_smul x b
    constructor
    · rintro ⟨hga, hgb⟩
      constructor
      · simp only [mul_smul, hxinva, hga, hxa]
      · simp only [mul_smul, hxinvb, hgb, hxb]
    · rintro ⟨hcga, hcgb⟩
      constructor
      · calc
          g • a = x⁻¹ • ((x * g * x⁻¹) • (x • a)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • a) := by rw [hxa]
          _ = x⁻¹ • a := by rw [hcga]
          _ = a := hxinva
      · calc
          g • b = x⁻¹ • ((x * g * x⁻¹) • (x • b)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • b) := by rw [hxb]
          _ = x⁻¹ • b := by rw [hcgb]
          _ = b := hxinvb
  · have hxinva : x⁻¹ • a = b := by rw [← hxb, inv_smul_smul]
    have hxinvb : x⁻¹ • b = a := by rw [← hxa, inv_smul_smul]
    constructor
    · rintro ⟨hga, hgb⟩
      constructor
      · simp only [mul_smul, hxinva, hgb, hxb]
      · simp only [mul_smul, hxinvb, hga, hxa]
    · rintro ⟨hcga, hcgb⟩
      constructor
      · calc
          g • a = x⁻¹ • ((x * g * x⁻¹) • (x • a)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • b) := by rw [hxa]
          _ = x⁻¹ • b := by rw [hcgb]
          _ = a := hxinvb
      · calc
          g • b = x⁻¹ • ((x * g * x⁻¹) • (x • b)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • a) := by rw [hxb]
          _ = x⁻¹ • a := by rw [hcga]
          _ = b := hxinva

/-- For odd two-point-stabilizer order, its index-two ambient normalizer is a
Z-group.  This packages the coprime extension step in XI.1.5. -/
private theorem xi91_odd_twoPointNormalizer_isZGroup
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    let H := MulAction.stabilizer G a
    let D := MulAction.stabilizer H
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
    let Dg : Subgroup G := D.map H.subtype
    IsZGroup (Subgroup.normalizer (Dg : Set G)) := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change IsZGroup T
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      xi91_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  let : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  have hDgcard : Nat.card Dg = Nat.card D := by
    simpa [Dg] using
      (Subgroup.card_map_of_injective
        (K := D) (f := H.subtype) H.subtype_injective)
  have hDsubcard : Nat.card Dsub = Nat.card D := by
    calc
      Nat.card Dsub = Nat.card Dg :=
        natCard_subgroupOf_eq Dg T Subgroup.le_normalizer
      _ = Nat.card D := hDgcard
  let : IsZGroup D :=
    isZGroup_of_frobenius_complement_of_odd F D (by
      simpa [D] using hFrob) hodd
  let eDg : D ≃* Dg :=
    Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  let eDsub : Dsub ≃* Dg :=
    Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  let eD : Dsub ≃* D := eDsub.trans eDg.symm
  let : IsZGroup Dsub :=
    IsZGroup.of_injective (f := eD.toMonoidHom) eD.injective
  have hquotCard : Nat.card (T ⧸ Dsub) = 2 := by
    rw [← Dsub.index_eq_card]
    exact hindex
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic (T ⧸ Dsub) :=
    isCyclic_of_card_dvd_prime (by rw [hquotCard])
  have hcop : (Nat.card Dsub).Coprime (Nat.card (T ⧸ Dsub)) := by
    rw [hDsubcard, hquotCard]
    simpa [D] using hodd.coprime_two_right
  exact isZGroup_of_coprime
    (f := Dsub.subtype) (f' := QuotientGroup.mk' Dsub)
    (by simp) hcop

/-- XI.1.5, cyclicity part: in a simple Zassenhaus group the odd two-point
stabilizer is cyclic. -/
private theorem xi91_odd_twoPointStabilizer_cyclic_and_commutator_eq
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    let H := MulAction.stabilizer G a
    let D := MulAction.stabilizer H
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
    let Dg : Subgroup G := D.map H.subtype
    let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
    IsCyclic D ∧ commutator T = Dg.subgroupOf T := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change IsCyclic D ∧ commutator T = Dsub
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      xi91_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  let : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  have hDgcard : Nat.card Dg = Nat.card D := by
    simpa [Dg] using
      (Subgroup.card_map_of_injective
        (K := D) (f := H.subtype) H.subtype_injective)
  have hDsubcard : Nat.card Dsub = Nat.card D := by
    calc
      Nat.card Dsub = Nat.card Dg :=
        natCard_subgroupOf_eq Dg T Subgroup.le_normalizer
      _ = Nat.card D := hDgcard
  have hTcard : Nat.card T = 2 * Nat.card D := by
    calc
      Nat.card T = Nat.card Dsub * Dsub.index := Dsub.card_mul_index.symm
      _ = 2 * Nat.card D := by rw [hDsubcard, hindex]; omega
  let : IsZGroup T := by
    simpa [H, D, Dg, T] using
      xi91_odd_twoPointNormalizer_isZGroup
        htwo hat_most_two_fixed_points a b hab F hFrob hodd
  have hcommCyclic : IsCyclic (commutator T) :=
    IsZGroup.isCyclic_commutator T
  have hquotCard : Nat.card (T ⧸ Dsub) = 2 := by
    rw [← Dsub.index_eq_card]
    exact hindex
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic (T ⧸ Dsub) :=
    isCyclic_of_card_dvd_prime (by rw [hquotCard])
  let : CommGroup (T ⧸ Dsub) := IsCyclic.commGroup
  have hcommLe : commutator T ≤ Dsub := by
    simpa using
      (Abelianization.commutator_subset_ker (QuotientGroup.mk' Dsub))
  have hnoOddPrime :
      ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ (commutator T).index := by
    intro q hq hqne hqindex
    let : Fact q.Prime := ⟨hq⟩
    have hqT : q ∣ Nat.card T :=
      hqindex.trans (commutator T).index_dvd_card
    have hqcommNot : ¬ q ∣ Nat.card (commutator T) := by
      apply hq.coprime_iff_not_dvd.mp
      exact Nat.Coprime.of_dvd_left hqindex
        (IsZGroup.coprime_commutator_index T).symm
    let Qd : Sylow q D := default
    let iotaD : D →* G := H.subtype.comp D.subtype
    have hiotaD : Function.Injective iotaD :=
      H.subtype_injective.comp D.subtype_injective
    let Qg : Subgroup G := (Qd : Subgroup D).map iotaD
    have hDgRange : iotaD.range = Dg := by
      ext x
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨(d : H), d.property, rfl⟩
      · rintro ⟨d, hdD, rfl⟩
        exact ⟨⟨d, hdD⟩, rfl⟩
    have hDgMapTop : Subgroup.map iotaD (⊤ : Subgroup D) = Dg := by
      calc
        Subgroup.map iotaD (⊤ : Subgroup D) = iotaD.range := by
          ext x
          constructor
          · rintro ⟨d, _hd, rfl⟩
            exact ⟨d, rfl⟩
          · rintro ⟨d, rfl⟩
            exact ⟨d, trivial, rfl⟩
        _ = Dg := hDgRange
    have hQgDg : Qg ≤ Dg := by
      simpa [Qg, hDgRange] using
        (Subgroup.map_le_range iotaD (Qd : Subgroup D))
    have hQgT : Qg ≤ T := hQgDg.trans Subgroup.le_normalizer
    have hQgP : IsPGroup q Qg := Qd.isPGroup'.map iotaD
    let QTsub : Subgroup T := Qg.subgroupOf T
    have hQTsubP : IsPGroup q QTsub :=
      hQgP.of_equiv (Subgroup.subgroupOfEquivOfLe hQgT).symm
    have hrelQD : Qg.relIndex Dg = Qd.index := by
      rw [show Qg = Subgroup.map iotaD (Qd : Subgroup D) from rfl,
        ← hDgMapTop,
        Subgroup.relIndex_map_map_of_injective
          (Qd : Subgroup D) (⊤ : Subgroup D) hiotaD,
        Subgroup.relIndex_top_right]
    have hrelQT : Qg.relIndex T = Qd.index * 2 := by
      calc
        Qg.relIndex T = Qg.relIndex Dg * Dg.relIndex T :=
          (Subgroup.relIndex_mul_relIndex Qg Dg T hQgDg
            Subgroup.le_normalizer).symm
        _ = Qd.index * Dsub.index := by rw [hrelQD]; rfl
        _ = Qd.index * 2 := by rw [hindex]
    have hQTsubIndex : QTsub.index = Qd.index * 2 := by
      change Qg.relIndex T = Qd.index * 2
      exact hrelQT
    have hqQTsubIndex : ¬ q ∣ QTsub.index := by
      rw [hQTsubIndex]
      intro hqmul
      rcases hq.dvd_mul.mp hqmul with hqQd | hq2
      · exact Qd.not_dvd_index hqQd
      · rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with hq1 | hq2eq
        · exact hq.ne_one hq1
        · exact hqne hq2eq
    let QT : Sylow q T := hQTsubP.toSylow hqQTsubIndex
    have hQTcoe : (QT : Subgroup T) = QTsub :=
      IsPGroup.toSylow_coe hQTsubP hqQTsubIndex
    have hnormalizerCentralT :
        Subgroup.normalizer ((QTsub : Subgroup T) : Set T) ≤
          Subgroup.centralizer (QTsub : Set T) := by
      rcases Sylow.normalizer_le_centralizer_or_le_commutator QT with hcent | hle
      · simpa [← hQTcoe] using hcent
      · exfalso
        apply hqcommNot
        exact (QT.dvd_card_of_dvd_card hqT).trans
          (Subgroup.card_dvd_of_le hle)
    obtain ⟨hOmegaCard, _hHcard, hGcard, hDdvd⟩ :=
      xi91_action_parameters_core htwo a b hab F hFrob
    have hqD : q ∣ Nat.card D := by
      have hq2D : q ∣ 2 * Nat.card D := by
        rw [← hTcard]
        exact hqT
      rcases hq.dvd_mul.mp hq2D with hq2 | hqD
      · rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with hq1 | hq2eq
        · exact (hq.ne_one hq1).elim
        · exact (hqne hq2eq).elim
      · exact hqD
    have hqFsub : q ∣ Nat.card F - 1 := hqD.trans (by simpa [D] using hDdvd)
    have hFcardGt : 1 < Nat.card F :=
      (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot |>
        Finite.one_lt_card_iff_nontrivial.mpr
    have hqFnot : ¬ q ∣ Nat.card F := by
      intro hqF
      have hqone : q ∣ 1 := by
        have := Nat.dvd_sub hqF hqFsub
        convert this using 1; omega
      exact hq.not_dvd_one hqone
    have hqFplusNot : ¬ q ∣ Nat.card F + 1 := by
      intro hqFplus
      have hqtwo : q ∣ 2 := by
        have := Nat.dvd_sub hqFplus hqFsub
        convert this using 1; omega
      rcases (Nat.dvd_prime Nat.prime_two).mp hqtwo with hq1 | hq2eq
      · exact hq.ne_one hq1
      · exact hqne hq2eq
    have hDgIndex : Dg.index = (Nat.card F + 1) * Nat.card F := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D))
      calc
        Nat.card D * Dg.index = Nat.card Dg * Dg.index := by rw [hDgcard]
        _ = Nat.card G := Dg.card_mul_index
        _ = Fintype.card Omega * Nat.card F * Nat.card D := by
          simpa [D] using hGcard
        _ = Nat.card D * ((Nat.card F + 1) * Nat.card F) := by
          rw [hOmegaCard]
          ring
    have hqDgIndex : ¬ q ∣ Dg.index := by
      rw [hDgIndex]
      intro hqmul
      rcases hq.dvd_mul.mp hqmul with hqFplus | hqF
      · exact hqFplusNot hqFplus
      · exact hqFnot hqF
    have hiotaKer : iotaD.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff iotaD).mpr hiotaD
    have hQgIndex : Qg.index = Qd.index * Dg.index := by
      calc
        Qg.index =
            ((Qd : Subgroup D) ⊔ iotaD.ker).index * iotaD.range.index :=
          Subgroup.index_map (Qd : Subgroup D) iotaD
        _ = Qd.index * Dg.index := by
          rw [hiotaKer, sup_bot_eq, hDgRange]
    have hqQgIndex : ¬ q ∣ Qg.index := by
      rw [hQgIndex]
      intro hqmul
      rcases hq.dvd_mul.mp hqmul with hqQd | hqDg
      · exact Qd.not_dvd_index hqQd
      · exact hqDgIndex hqDg
    let QG : Sylow q G := hQgP.toSylow hqQgIndex
    have hQGcoe : (QG : Subgroup G) = Qg :=
      IsPGroup.toSylow_coe hQgP hqQgIndex
    have hqG : q ∣ Nat.card G :=
      hqT.trans (Subgroup.card_subgroup_dvd_card T)
    have hQgNe : Qg ≠ ⊥ := by
      rw [← hQGcoe]
      exact Sylow.ne_bot_of_dvd_card QG hqG
    have hnormalizerLeT : Subgroup.normalizer (Qg : Set G) ≤ T := by
      simpa [H, D, Dg, T] using
        zassenhaus_twoPointSubgroup_normalizer_le
          hat_most_two_fixed_points a b hab Qg hQgDg hQgNe
    have hnormalizerCentralG :
        Subgroup.normalizer (Qg : Set G) ≤
          Subgroup.centralizer (Qg : Set G) := by
      intro x hx
      let xT : T := ⟨x, hnormalizerLeT hx⟩
      have hxNormT : xT ∈ Subgroup.normalizer (QTsub : Set T) := by
        rw [Subgroup.mem_normalizer_iff] at hx ⊢
        intro y
        change ((y : T) : G) ∈ Qg ↔
          (((xT * y * xT⁻¹ : T) : G) ∈ Qg)
        exact hx ((y : T) : G)
      have hxCentT : xT ∈ Subgroup.centralizer (QTsub : Set T) :=
        hnormalizerCentralT hxNormT
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let yT : T := ⟨y, hQgT hy⟩
      have hyQT : yT ∈ QTsub := hy
      have hcommT :=
        (Subgroup.mem_centralizer_iff.mp hxCentT) yT hyQT
      exact congrArg Subtype.val hcommT
    have hcentralG :
        Subgroup.normalizer ((QG : Subgroup G) : Set G) ≤
          Subgroup.centralizer ((QG : Subgroup G) : Set G) := by
      simpa [hQGcoe] using hnormalizerCentralG
    have hcomp := MonoidHom.ker_transferSylow_isComplement' QG hcentralG
    let K : Subgroup G := (MonoidHom.transferSylow QG hcentralG).ker
    have hQGne : (QG : Subgroup G) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card QG hqG
    obtain ⟨s, _hsq, hsa, _hsb⟩ :=
      xi91_odd_twoPointStabilizer_exists_swap_involution
        htwo hat_most_two_fixed_points a b hab F hFrob hodd
    have hQGtop : (QG : Subgroup G) ≠ ⊤ := by
      intro htop
      have hsQg : s ∈ Qg := by
        rw [← hQGcoe, htop]
        trivial
      have hsfix :=
        (xi91_twoPointStabilizer_map_mem_iff a b hab s).mp (hQgDg hsQg)
      exact hab (hsfix.1.symm.trans hsa)
    by_cases hKbot : K = ⊥
    · apply hQGtop
      apply Subgroup.isComplement'_bot_left.mp
      simpa [K, hKbot] using hcomp
    · have hKtop : K = ⊤ := hsimple K inferInstance hKbot
      apply hQGne
      apply Subgroup.isComplement'_top_left.mp
      simpa [K, hKtop] using hcomp
  have htwoDvd : 2 ∣ (commutator T).index := by
    rw [← hindex]
    exact Subgroup.index_dvd_of_le hcommLe
  have hcommIndexDvd : (commutator T).index ∣ 2 * Nat.card D := by
    rw [← hTcard]
    exact (commutator T).index_dvd_card
  obtain ⟨m, hm⟩ := htwoDvd
  have hmDvd : m ∣ Nat.card D := by
    obtain ⟨r, hr⟩ := hcommIndexDvd
    refine ⟨r, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by omega)
    calc
      2 * Nat.card D = (commutator T).index * r := hr
      _ = (2 * m) * r := by rw [hm]
      _ = 2 * (m * r) := by ring
  have hmOne : m = 1 := by
    by_contra hmne
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hmne
    have hqD : q ∣ Nat.card D := hqm.trans hmDvd
    have hqne : q ≠ 2 := by
      intro hqeq
      subst q
      exact (Nat.not_even_iff_odd.mpr (by simpa [D] using hodd))
        (even_iff_two_dvd.mpr (by simpa [D] using hqD))
    exact hnoOddPrime q hq hqne
      (hqm.trans (by rw [hm]; exact dvd_mul_left m 2))
  have hcommIndex : (commutator T).index = 2 := by
    rw [hm, hmOne]
  have hcommCard : Nat.card (commutator T) = Nat.card Dsub := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by omega)
    calc
      Nat.card (commutator T) * 2 = Nat.card T := by
        rw [← hcommIndex]
        exact (commutator T).card_mul_index
      _ = Nat.card Dsub * 2 := by
        rw [← hindex]
        exact Dsub.card_mul_index.symm
  have hcommEq : commutator T = Dsub :=
    Subgroup.eq_of_le_of_card_ge hcommLe (by rw [hcommCard])
  have hDsubCyclic : IsCyclic Dsub := by
    rw [hcommEq] at hcommCyclic
    exact hcommCyclic
  let eDg : D ≃* Dg :=
    Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  let eDsub : Dsub ≃* Dg :=
    Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  let eD : Dsub ≃* D := eDsub.trans eDg.symm
  exact ⟨isCyclic_of_surjective eD eD.surjective, hcommEq⟩

/-- Any element interchanging the distinguished points normalizes their
pointwise stabilizer. -/
private theorem xi91_swap_mem_twoPointStabilizer_normalizer
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (a b : Omega) (hab : a ≠ b) (s : G)
    (hsa : s • a = b) (hsb : s • b = a) :
    s ∈ Subgroup.normalizer
      (((MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
          (MulAction.stabilizer G a).subtype : Subgroup G) : Set G) := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  have hsinva : s⁻¹ • a = b := by
    calc
      s⁻¹ • a = s⁻¹ • (s • b) := by rw [hsb]
      _ = b := inv_smul_smul s b
  have hsinvb : s⁻¹ • b = a := by
    calc
      s⁻¹ • b = s⁻¹ • (s • a) := by rw [hsa]
      _ = a := inv_smul_smul s a
  change s ∈ Subgroup.normalizer (Dg : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [show g ∈ Dg ↔ g • a = a ∧ g • b = b by
    simpa [H, D, Dg] using xi91_twoPointStabilizer_map_mem_iff a b hab g]
  rw [show s * g * s⁻¹ ∈ Dg ↔
      (s * g * s⁻¹) • a = a ∧ (s * g * s⁻¹) • b = b by
    simpa [H, D, Dg] using
      xi91_twoPointStabilizer_map_mem_iff a b hab (s * g * s⁻¹)]
  constructor
  · rintro ⟨hga, hgb⟩
    constructor
    · simp only [mul_smul, hsinva, hgb, hsb]
    · simp only [mul_smul, hsinvb, hga, hsa]
  · rintro ⟨hcga, hcgb⟩
    constructor
    · calc
        g • a = s⁻¹ • ((s * g * s⁻¹) • (s • a)) := by
          simp only [mul_smul, inv_smul_smul]
        _ = s⁻¹ • ((s * g * s⁻¹) • b) := by rw [hsa]
        _ = s⁻¹ • b := by rw [hcgb]
        _ = a := hsinvb
    · calc
        g • b = s⁻¹ • ((s * g * s⁻¹) • (s • b)) := by
          simp only [mul_smul, inv_smul_smul]
        _ = s⁻¹ • ((s * g * s⁻¹) • a) := by rw [hsb]
        _ = s⁻¹ • a := by rw [hcga]
        _ = b := hsinva


/-- XI.1.5, cyclicity part: in a simple Zassenhaus group the odd two-point
stabilizer is cyclic. -/
private theorem xi91_odd_twoPointStabilizer_isCyclic
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    IsCyclic
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :=
  (xi91_odd_twoPointStabilizer_cyclic_and_commutator_eq
    htwo hat_most_two_fixed_points hsimple a b hab F hFrob hodd).1

private theorem xi91_isMulCommutative_sup_of_le_centralizer
    {Q : Type*} [Group Q] {A B : Subgroup Q}
    (hAcomm : IsMulCommutative A) (hBcomm : IsMulCommutative B)
    (hBcentral : B ≤ Subgroup.centralizer (A : Set Q)) :
    IsMulCommutative (A ⊔ B : Subgroup Q) := by
  rw [Subgroup.sup_eq_closure]
  apply Subgroup.isMulCommutative_closure
  intro x hx y hy _
  rcases hx with hxA | hxB
  · rcases hy with hyA | hyB
    · exact setLike_mul_comm (s := A) hxA hyA
    · exact Subgroup.mem_centralizer_iff.mp (hBcentral hyB) x hxA
  · rcases hy with hyA | hyB
    · exact (Subgroup.mem_centralizer_iff.mp (hBcentral hxB) y hyA).symm
    · exact setLike_mul_comm (s := B) hxB hyB

/-- XI.1.5, inversion part: every element interchanging the two points acts
by inversion on the odd cyclic two-point stabilizer. -/
private theorem xi91_odd_twoPointStabilizer_swap_inverts
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (s : G) (hsa : s • a = b) (hsb : s • b = a) :
    ∀ x : MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
        ((((x⁻¹ : MulAction.stabilizer
          (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
            MulAction.stabilizer G a) : G)) := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change ∀ x : D, s * (((x : H) : G)) * s⁻¹ = (((x⁻¹ : D) : H) : G)
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      xi91_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  let : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  obtain ⟨hDcyclic, hcommEq⟩ :=
    xi91_odd_twoPointStabilizer_cyclic_and_commutator_eq
      htwo hat_most_two_fixed_points hsimple a b hab F hFrob hodd
  let eDg : D ≃* Dg :=
    Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  let eDsub : Dsub ≃* Dg :=
    Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  let eDDsub : D ≃* Dsub := eDg.trans eDsub.symm
  let : IsCyclic D := hDcyclic
  let : IsCyclic Dsub :=
    isCyclic_of_surjective eDDsub eDDsub.surjective
  let : CommGroup Dsub := IsCyclic.commGroup
  have hDsubComm : IsMulCommutative Dsub := inferInstance
  have hDsubcard : Nat.card Dsub = Nat.card D :=
    Nat.card_congr eDDsub.symm.toEquiv
  obtain ⟨c, hcSq, hca, hcb⟩ :=
    xi91_odd_twoPointStabilizer_exists_swap_involution
      htwo hat_most_two_fixed_points a b hab F hFrob hodd
  have hcTmem : c ∈ T := by
    simpa [H, D, Dg, T] using
      xi91_swap_mem_twoPointStabilizer_normalizer a b hab c hca hcb
  let cT : T := ⟨c, hcTmem⟩
  have hcTnotD : cT ∉ Dsub := by
    intro hcD
    have hcDg : c ∈ Dg := hcD
    have hcfix :=
      (xi91_twoPointStabilizer_map_mem_iff a b hab c).mp hcDg
    exact hab (hcfix.1.symm.trans hca)
  have hcTne : cT ≠ 1 := by
    intro hcOne
    apply hcTnotD
    simp [hcOne]
  have hcTSq : cT ^ 2 = 1 := by
    apply Subtype.ext
    exact hcSq
  let R : Subgroup T := Subgroup.zpowers cT
  let : IsCyclic R := inferInstance
  let : CommGroup R := IsCyclic.commGroup
  have hRcomm : IsMulCommutative R := inferInstance
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcTorder : orderOf cT = 2 := orderOf_eq_prime hcTSq hcTne
  have hRcard : Nat.card R = 2 := by
    simp [R, hcTorder]
  have hsup : Dsub ⊔ R = ⊤ := by
    apply top_unique
    intro x _hx
    by_cases hxD : (x : T) ∈ Dsub
    · exact Subgroup.mem_sup_left hxD
    · have hxswap :
          ((x : T) : G) • a = b ∧ ((x : T) : G) • b = a := by
        have hxnotDg : ((x : T) : G) ∉ Dg := by
          intro hxDg
          exact hxD hxDg
        exact xi91_twoPointStabilizer_normalizer_notMem_swaps
          hat_most_two_fixed_points a b hab F hFrob ((x : T) : G)
          x.property hxnotDg
      have hxcDg : (((x * cT : T) : G)) ∈ Dg := by
        apply (xi91_twoPointStabilizer_map_mem_iff a b hab ((x * cT : T) : G)).mpr
        constructor
        · change (((x : T) : G) * c) • a = a
          rw [mul_smul, hca, hxswap.2]
        · change (((x : T) : G) * c) • b = b
          rw [mul_smul, hcb, hxswap.1]
      have hxcD : x * cT ∈ Dsub := by
        simpa [Dsub] using Subgroup.mem_subgroupOf.mpr hxcDg
      have hcR : cT ∈ R := Subgroup.mem_zpowers cT
      have hcMul : cT * cT = 1 := by simpa [pow_two] using hcTSq
      have hxrepr : x = (x * cT) * cT := by
        rw [mul_assoc, hcMul, mul_one]
      rw [hxrepr]
      exact (Dsub ⊔ R).mul_mem
        (Subgroup.mem_sup_left hxcD) (Subgroup.mem_sup_right hcR)
  have hRnormD : R ≤ Subgroup.normalizer (Dsub : Set T) := by
    simp [Dsub.normalizer_eq_top]
  let N : Subgroup T := ⁅Dsub, R⁆
  have : N.Normal := by
    have hNnormal := commutator_normal_in_sup Dsub R
    have hsupLe : Dsub ⊔ R ≤ Subgroup.normalizer (N : Set T) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := N) (K := Dsub ⊔ R)
          (by simpa [N] using commutator_le_sup Dsub R)).mp
        (by simpa [N] using hNnormal)
    have htopLe : (⊤ : Subgroup T) ≤ Subgroup.normalizer (N : Set T) := by
      simpa [hsup] using hsupLe
    exact Subgroup.normalizer_eq_top_iff.mp (top_unique htopLe)
  let pi : T →* T ⧸ N := QuotientGroup.mk' N
  let A : Subgroup (T ⧸ N) := Dsub.map pi
  let B : Subgroup (T ⧸ N) := R.map pi
  have hAcomm : IsMulCommutative A := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    rcases x.property with ⟨xT, hxD, hx⟩
    rcases y.property with ⟨yT, hyD, hy⟩
    change (x : T ⧸ N) * y = y * x
    rw [← hx, ← hy]
    exact congrArg pi
      (setLike_mul_comm (s := Dsub) hxD hyD)
  have hBcomm : IsMulCommutative B := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    rcases x.property with ⟨xT, hxR, hx⟩
    rcases y.property with ⟨yT, hyR, hy⟩
    change (x : T ⧸ N) * y = y * x
    rw [← hx, ← hy]
    exact congrArg pi
      (setLike_mul_comm (s := R) hxR hyR)
  have hBcentralA : B ≤ Subgroup.centralizer (A : Set (T ⧸ N)) := by
    intro rbar hrbar
    rcases hrbar with ⟨r, hrR, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro dbar hdbar
    rcases hdbar with ⟨d, hdD, rfl⟩
    have hdrN : ⁅d, r⁆ ∈ N :=
      Subgroup.commutator_mem_commutator
        (H₁ := Dsub) (H₂ := R) hdD hrR
    have hcomm : Commute (pi d) (pi r) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff ⁅d, r⁆).2 hdrN
    exact hcomm.eq
  have hABtop : A ⊔ B = ⊤ := by
    calc
      A ⊔ B = Subgroup.map pi (Dsub ⊔ R) :=
        (Subgroup.map_sup Dsub R pi).symm
      _ = Subgroup.map pi ⊤ := by rw [hsup]
      _ = pi.range := (MonoidHom.range_eq_map pi).symm
      _ = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  have hquotComm : IsMulCommutative (T ⧸ N) := by
    have h := xi91_isMulCommutative_sup_of_le_centralizer hAcomm hBcomm hBcentralA
    rw [hABtop] at h
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxy :
        (⟨x, trivial⟩ : (⊤ : Subgroup (T ⧸ N))) * ⟨y, trivial⟩ =
          ⟨y, trivial⟩ * ⟨x, trivial⟩ := h.is_comm.comm _ _
    exact congrArg Subtype.val hxy
  have hcommLeN : commutator T ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp
      hquotComm
  have hNleComm : N ≤ commutator T := by
    exact Subgroup.commutator_mono le_top le_top
  have hNeqD : N = Dsub :=
    (le_antisymm hNleComm hcommLeN).trans hcommEq
  let : Subgroup.Normalizes R Dsub := ⟨hRnormD⟩
  let : MulDistribMulAction R Dsub :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer R Dsub hRnormD
  have hactionMap :
      (commutatorAction (A := R) (G := Dsub)).map Dsub.subtype = N := by
    simpa [N] using
      commutatorAction_subgroup_conj_map_eq_commutator Dsub R hRnormD
  have hactionTop : commutatorAction (A := R) (G := Dsub) = ⊤ := by
    apply Subgroup.map_injective Dsub.subtype_injective
    calc
      Subgroup.map Dsub.subtype (commutatorAction (A := R) (G := Dsub)) = N :=
        hactionMap
      _ = Dsub := hNeqD
      _ = Dsub.subtype.range := (Dsub.range_subtype).symm
      _ = Subgroup.map Dsub.subtype ⊤ := MonoidHom.range_eq_map Dsub.subtype
  have hcop : (Nat.card R).Coprime (Nat.card Dsub) := by
    rw [hRcard, hDsubcard]
    exact (by simpa [D] using hodd.coprime_two_right.symm)
  have hcompl :
      IsCompl (fixedPointSubgroup R Dsub)
        (commutatorAction (A := R) (G := Dsub)) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm hDsubComm.is_comm.comm) hcop hDsubComm
  have hfixedBot : fixedPointSubgroup R Dsub = ⊥ := by
    apply bot_unique
    have hle := hcompl.disjoint.le_bot
    simpa [hactionTop] using hle
  have hcNorm : cT ∈ Subgroup.normalizer (Dsub : Set T) := by
    rw [Dsub.normalizer_eq_top]
    trivial
  let cN : Subgroup.normalizer (Dsub : Set T) := ⟨cT, hcNorm⟩
  let phi : MulAut Dsub := Dsub.normalizerMonoidHom cN
  have hphiSq : phi ^ 2 = 1 := by
    change (Dsub.normalizerMonoidHom cN) ^ 2 = 1
    have hcNSq : cN ^ 2 = 1 := by
      apply Subtype.ext
      exact hcTSq
    rw [← map_pow, hcNSq, map_one]
  have hphiInv : Function.Involutive phi := by
    intro x
    have hx := congrArg (fun psi : MulAut Dsub => psi x) hphiSq
    simpa [pow_two] using hx
  have hphiFree : MonoidHom.FixedPointFree phi := by
    intro x hx
    have hconjFix : cT * (x : T) * cT⁻¹ = (x : T) := by
      simpa [phi, cN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hx
    have hccomm : Commute cT (x : T) := by
      apply commutatorElement_eq_one_iff_commute.mp
      simp [commutatorElement_def, hconjFix]
    have hxFixed : x ∈ fixedPointSubgroup R Dsub := by
      change ∀ r : R, r • x = x
      intro r
      rcases Subgroup.mem_zpowers_iff.mp r.property with ⟨k, hk⟩
      have hrcomm : Commute (r : T) (x : T) := by
        rw [← hk]
        exact hccomm.zpow_left k
      apply Subtype.ext
      change (r : T) * (x : T) * (r : T)⁻¹ = (x : T)
      rw [hrcomm.eq]
      simp [mul_assoc]
    have hxBot : x ∈ (⊥ : Subgroup Dsub) := by
      simpa [hfixedBot] using hxFixed
    exact Subgroup.mem_bot.mp hxBot
  have hphiEqInv : ⇑phi = fun x : Dsub => x⁻¹ :=
    hphiFree.coe_eq_inv_of_involutive hphiInv
  have hcInverts (x : Dsub) :
      cT * (x : T) * cT⁻¹ = ((x⁻¹ : Dsub) : T) := by
    have hx := congrArg Subtype.val (congrFun hphiEqInv x)
    simpa [phi, cN, Subgroup.normalizerMonoidHom_apply_apply_coe] using hx
  have hsTmem : s ∈ T := by
    simpa [H, D, Dg, T] using
      xi91_swap_mem_twoPointStabilizer_normalizer a b hab s hsa hsb
  let sT : T := ⟨s, hsTmem⟩
  intro x
  let xDg : Dg := ⟨((x : H) : G), ⟨(x : H), x.property, rfl⟩⟩
  let xT : T := ⟨(xDg : G), Subgroup.le_normalizer xDg.property⟩
  let xDsub : Dsub := ⟨xT, xDg.property⟩
  have hscDg : (((sT * cT : T) : G)) ∈ Dg := by
    apply (xi91_twoPointStabilizer_map_mem_iff a b hab ((sT * cT : T) : G)).mpr
    constructor
    · change (s * c) • a = a
      rw [mul_smul, hca, hsb]
    · change (s * c) • b = b
      rw [mul_smul, hcb, hsa]
  let dT : Dsub := ⟨sT * cT, by simpa [Dsub] using Subgroup.mem_subgroupOf.mpr hscDg⟩
  have hcMul : cT * cT = 1 := by simpa [pow_two] using hcTSq
  have hsEq : sT = (dT : T) * cT := by
    change sT = (sT * cT) * cT
    rw [mul_assoc, hcMul, mul_one]
  have hdcomm : Commute (dT : T) (xDsub : T) := by
    exact setLike_mul_comm (s := Dsub) dT.property xDsub.property
  have hcalc :
      sT * (xDsub : T) * sT⁻¹ = ((xDsub⁻¹ : Dsub) : T) := by
    calc
      sT * (xDsub : T) * sT⁻¹ =
          ((dT : T) * cT) * (xDsub : T) * ((dT : T) * cT)⁻¹ := by
        rw [← hsEq]
      _ = (dT : T) * (cT * (xDsub : T) * cT⁻¹) * (dT : T)⁻¹ := by
        group
      _ = (dT : T) * ((xDsub⁻¹ : Dsub) : T) * (dT : T)⁻¹ := by
        rw [hcInverts]
      _ = ((xDsub⁻¹ : Dsub) : T) := by
        have hdcommInv : Commute (dT : T) ((xDsub⁻¹ : Dsub) : T) := by
          simpa using hdcomm.inv_right
        rw [hdcommInv.eq]
        simp [mul_assoc]
  have hcalcG := congrArg (fun z : T => (z : G)) hcalc
  simpa [sT, xDsub, xDg] using hcalcG


private theorem xi91_card_actor_dvd_of_fixedPointFree
    {A Omega : Type*} [Group A] [Finite A] [Finite Omega] [MulAction A Omega]
    (hfree : ∀ a : A, a ≠ 1 → ∀ x : Omega, a • x = x → False) :
    Nat.card A ∣ Nat.card Omega := by
  classical
  have hstab : ∀ x : Omega, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    have hax : a • x = x := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha1
    have hane : a ≠ 1 := by
      intro h
      apply ha1
      simp [h]
    exact hfree a hane x hax
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A Omega)), by
    rw [mul_comm]
    exact hcard⟩

private noncomputable def xi91_stabilizerCentralizerEquiv
    {G : Type*} [Group G] (g : G) :
    MulAction.stabilizer (ConjAct G) g ≃ {x : G // x * g = g * x} where
  toFun x :=
    ⟨ConjAct.ofConjAct x.1, by
      have hx : x.1 • g = g := x.2
      rw [ConjAct.smul_def] at hx
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hx)⟩
  invFun x :=
    ⟨ConjAct.toConjAct x.1, by
      change ConjAct.toConjAct x.1 • g = g
      rw [ConjAct.toConjAct_smul]
      exact mul_inv_eq_of_eq_mul x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

private theorem xi91_class_card_mul_centralizer_card
    {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier *
        Nat.card (Subgroup.centralizer ({g} : Set G)) = Nat.card G := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hst :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  have hst' : Fintype.card (ConjClasses.mk g).carrier *
      Fintype.card (MulAction.stabilizer (ConjAct G) g) = Fintype.card G := by
    simpa [ConjAct.orbit_eq_carrier_conjClasses] using hst
  have hstabCard :
      Nat.card (MulAction.stabilizer (ConjAct G) g) =
        Nat.card {x : G // x * g = g * x} :=
    Nat.card_congr (xi91_stabilizerCentralizerEquiv g)
  have hcentCard :
      Nat.card (Subgroup.centralizer ({g} : Set G)) =
        Nat.card {x : G // x * g = g * x} := by
    exact Nat.card_congr
      (Equiv.subtypeEquivRight (fun x =>
        Subgroup.mem_centralizer_singleton_iff))
  simp only [Nat.card_eq_fintype_card] at hstabCard hcentCard ⊢
  rw [hcentCard, ← hstabCard]
  exact hst'


private theorem xi91_eq_one_of_sq_eq_one_of_odd_card
    {X : Type*} [Group X] [Finite X] (hodd : Odd (Nat.card X))
    (x : X) (hx : x ^ 2 = 1) : x = 1 := by
  have hordTwo : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have hcop : Nat.Coprime 2 (Nat.card X) := hodd.coprime_two_left
  have hordOne : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hordTwo (orderOf_dvd_natCard x)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hordOne)

private theorem xi91_derangement_centralizer_fixedPointFree
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (hat_most_two_fixed_points :
      ∀ x : G, x ≠ 1 → ∀ a b c : Omega,
        a ≠ b → a ≠ c → b ≠ c →
          ¬ (x • a = a ∧ x • b = b ∧ x • c = c))
    (hpairOdd : ∀ a b : Omega, ∀ hab : a ≠ b,
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (hswapInverts :
      ∀ a b : Omega, ∀ hab : a ≠ b, ∀ s : G,
        s • a = b → s • b = a →
          ∀ x : MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
            s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
              ((((x⁻¹ : MulAction.stabilizer
                (MulAction.stabilizer G a)
                (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
                  MulAction.stabilizer G a) : G)))
    (g : G) (hg : ∀ x : Omega, g • x ≠ x) :
    ∀ c : Subgroup.centralizer ({g} : Set G), c ≠ 1 →
      ∀ a : Omega, (c : G) • a = a → False := by
  intro c hc a hca
  let b : Omega := g • a
  have hab : a ≠ b := Ne.symm (hg a)
  have hcne : (c : G) ≠ 1 := by
    intro h
    apply hc
    exact Subtype.ext h
  have hccomm : (c : G) * g = g * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.property
  have hcb : (c : G) • b = b := by
    dsimp [b]
    calc
      (c : G) • (g • a) = ((c : G) * g) • a := by rw [mul_smul]
      _ = (g * (c : G)) • a := by rw [hccomm]
      _ = g • ((c : G) • a) := by rw [mul_smul]
      _ = g • a := by rw [hca]
  have hcgb : (c : G) • (g • b) = g • b := by
    calc
      (c : G) • (g • b) = ((c : G) * g) • b := by rw [mul_smul]
      _ = (g * (c : G)) • b := by rw [hccomm]
      _ = g • ((c : G) • b) := by rw [mul_smul]
      _ = g • b := by rw [hcb]
  have hgba : g • b = a := by
    by_contra hga
    exact (hat_most_two_fixed_points (c : G) hcne a b (g • b)
      hab (Ne.symm hga) (Ne.symm (hg b))) ⟨hca, hcb, hcgb⟩
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  let cH : H := ⟨(c : G), hca⟩
  let cD : D := ⟨cH, by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    exact hcb⟩
  have hconjInv : g * (c : G) * g⁻¹ = (c : G)⁻¹ := by
    simpa [H, b', D, cH, cD] using
      hswapInverts a b hab g rfl hgba cD
  have hconjFixed : g * (c : G) * g⁻¹ = (c : G) := by
    calc
      g * (c : G) * g⁻¹ = ((c : G) * g) * g⁻¹ := by rw [← hccomm]
      _ = (c : G) := by simp [mul_assoc]
  have hcInv : (c : G) = (c : G)⁻¹ := hconjFixed.symm.trans hconjInv
  have hcSqG : (c : G) ^ 2 = 1 := by
    calc
      (c : G) ^ 2 = (c : G) * (c : G) := pow_two _
      _ = (c : G) * (c : G)⁻¹ := congrArg (fun x : G => (c : G) * x) hcInv
      _ = 1 := mul_inv_cancel _
  have hcSqD : cD ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hcSqG
  have hcDone : cD = 1 :=
    xi91_eq_one_of_sq_eq_one_of_odd_card
      (hpairOdd a b hab) cD hcSqD
  apply hc
  have := congrArg (fun x : D => (((x : H) : G))) hcDone
  simpa [cD, cH] using this


/-- A nonidentity element of the point-stabilizer Frobenius kernel fixes
exactly the base point. -/
private theorem xi91_frobeniusKernel_uniqueFixedPoint
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (z : F) (hzne : z ≠ 1) :
    ∀ c : Omega,
      ((((z : MulAction.stabilizer G a) : G) • c = c) ↔ c = a) := by
  intro c
  constructor
  · intro hzc
    by_contra hca
    let cSub : SubMulAction.ofStabilizer G a := ⟨c, hca⟩
    have hzcSub :
        (z : MulAction.stabilizer G a) • cSub = cSub := by
      exact Subtype.ext hzc
    let : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    let : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hstab_multi :
        MulAction.IsMultiplyPretransitive
            (MulAction.stabilizer G a)
            (SubMulAction.ofStabilizer G a) 1 :=
      (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := G) (a := a)).mp htwo
    have hpretrans :
        MulAction.IsPretransitive
          (MulAction.stabilizer G a)
          (SubMulAction.ofStabilizer G a) :=
      (MulAction.is_one_pretransitive_iff
        (G := MulAction.stabilizer G a)
        (α := SubMulAction.ofStabilizer G a)).mp hstab_multi
    have hregular :
        ∀ x y : SubMulAction.ofStabilizer G a,
          ∃! f : F, (f : MulAction.stabilizer G a) • x = y :=
      huppert_blackburn_XI_regular_of_isComplement_stabilizer
        hFrob.isComplement' hpretrans
    obtain ⟨k, _hk, hunique⟩ := hregular cSub cSub
    have hzk : z = k := hunique z hzcSub
    have honek : (1 : F) = k := hunique 1 (by simp)
    exact hzne (hzk.trans honek.symm)
  · intro hca
    rw [hca]
    exact (z : MulAction.stabilizer G a).property

/-- A normal subgroup of a Frobenius group either lies in the kernel or
contains the kernel. -/
private theorem xi91_frobenius_normal_subgroup_le_kernel_or_kernel_le
    {H : Type*} [Group H] [Finite H]
    (F D N : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hN : N.Normal) :
    N ≤ F ∨ F ≤ N := by
  classical
  by_cases hNF : N ≤ F
  · exact Or.inl hNF
  right
  obtain ⟨n, hnN, hnnotF⟩ := SetLike.not_le_iff_exists.mp hNF
  let : F.Normal := hFrob.normal
  have hcentD :
      ∀ r : D, r ≠ 1 → Section2.centralizerIn F (r : H) = ⊥ := by
    intro r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using
      ((lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob r hr)
  have hcentN : Section2.centralizerIn F n = ⊥ :=
    Section6.theorem_6_8_frobenius_complement_centralizerIn_eq_bot
      (K := F) (R := D) hFrob.isComplement' hcentD hnnotF
  let delta : F → F := fun a =>
    ⟨(a : H) * n * (a : H)⁻¹ * n⁻¹, by
      have hconjF : n * (a : H)⁻¹ * n⁻¹ ∈ F :=
        hFrob.normal.conj_mem ((a : H)⁻¹) (F.inv_mem a.2) n
      simpa [mul_assoc] using F.mul_mem a.2 hconjF⟩
  have hdelta_inj : Function.Injective delta := by
    intro a b hab
    have habH :
        (a : H) * n * (a : H)⁻¹ * n⁻¹ =
          (b : H) * n * (b : H)⁻¹ * n⁻¹ :=
      congrArg Subtype.val hab
    have hcomm :
        (b : H)⁻¹ * (a : H) * n =
          n * ((b : H)⁻¹ * (a : H)) := by
      have hab1 :
          (a : H) * n * (a : H)⁻¹ =
            (b : H) * n * (b : H)⁻¹ := by
        simpa [mul_assoc] using congrArg (fun t : H => t * n) habH
      have hab2 := congrArg (fun t : H => (b : H)⁻¹ * t * (a : H)) hab1
      simpa [mul_assoc] using hab2
    let c : F :=
      ⟨(b : H)⁻¹ * (a : H), F.mul_mem (F.inv_mem b.2) a.2⟩
    have hcCent : (c : H) ∈ Section2.centralizerIn F n := by
      refine ⟨c.2, ?_⟩
      change (c : H) ∈ Subgroup.centralizer ({n} : Set H)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (by simpa [c] using hcomm)
    have hcBot : (c : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcentN] using hcCent
    have hc_eq : (c : H) = 1 := by simpa using hcBot
    apply Subtype.ext
    have := congrArg (fun t : H => (b : H) * t) hc_eq
    simpa [c, mul_assoc] using this
  have hdelta_surj : Function.Surjective delta :=
    Finite.surjective_of_injective hdelta_inj
  intro k hk
  rcases hdelta_surj ⟨k, hk⟩ with ⟨a, ha⟩
  have haH : (a : H) * n * (a : H)⁻¹ * n⁻¹ = k :=
    congrArg Subtype.val ha
  rw [← haH]
  exact N.mul_mem (hN.conj_mem n hnN (a : H)) (N.inv_mem hnN)

/-- Every element outside a finite Frobenius kernel is conjugate by a kernel
element into the complement. -/
private theorem xi91_frobenius_not_mem_kernel_conjugate_mem_complement
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    {x : H} (hxnotF : x ∉ F) :
    ∃ a : F, ∃ r : D,
      (a : H)⁻¹ * x * (a : H) = (r : H) := by
  classical
  let : F.Normal := hFrob.normal
  have hxSup : x ∈ F ⊔ D := by
    simp [hFrob.isComplement'.sup_eq_top]
  rcases (Subgroup.mem_sup_of_normal_left (s := F) (t := D) (x := x)).1 hxSup with
    ⟨k, hkF, r, hrD, hkr⟩
  let rD : D := ⟨r, hrD⟩
  have hrne : rD ≠ 1 := by
    intro hr1
    apply hxnotF
    rw [← hkr]
    have hr_eq : r = 1 := by
      simpa [rD] using congrArg Subtype.val hr1
    simp [hr_eq, hkF]
  have hcent : elementCentralizerIn F (rD : H) = ⊥ :=
    (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob rD hrne
  let delta : F → F := fun a =>
    ⟨(a : H) * r * (a : H)⁻¹ * r⁻¹, by
      have hconjF : r * (a : H)⁻¹ * r⁻¹ ∈ F :=
        hFrob.normal.conj_mem ((a : H)⁻¹) (F.inv_mem a.2) r
      simpa [mul_assoc] using F.mul_mem a.2 hconjF⟩
  have hdelta_inj : Function.Injective delta := by
    intro a b hab
    have habH :
        (a : H) * r * (a : H)⁻¹ * r⁻¹ =
          (b : H) * r * (b : H)⁻¹ * r⁻¹ :=
      congrArg Subtype.val hab
    have hcomm :
        (b : H)⁻¹ * (a : H) * r =
          r * ((b : H)⁻¹ * (a : H)) := by
      have hab1 :
          (a : H) * r * (a : H)⁻¹ =
            (b : H) * r * (b : H)⁻¹ := by
        simpa [mul_assoc] using congrArg (fun t : H => t * r) habH
      have hab2 := congrArg (fun t : H => (b : H)⁻¹ * t * (a : H)) hab1
      simpa [mul_assoc] using hab2
    let c : F :=
      ⟨(b : H)⁻¹ * (a : H), F.mul_mem (F.inv_mem b.2) a.2⟩
    have hcCent : (c : H) ∈ elementCentralizerIn F (rD : H) := by
      refine ⟨c.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (by simpa [c, rD] using hcomm)
    have hcBot : (c : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcent] using hcCent
    have hc_eq : (c : H) = 1 := by simpa using hcBot
    apply Subtype.ext
    have := congrArg (fun t : H => (b : H) * t) hc_eq
    simpa [c, mul_assoc] using this
  have hdelta_surj : Function.Surjective delta :=
    Finite.surjective_of_injective hdelta_inj
  rcases hdelta_surj ⟨k, hkF⟩ with ⟨a, ha⟩
  have haH : (a : H) * r * (a : H)⁻¹ * r⁻¹ = k :=
    congrArg Subtype.val ha
  have hconj_x : (a : H)⁻¹ * x * (a : H) = r := by
    rw [← hkr]
    have hk_eq : k = (a : H) * r * (a : H)⁻¹ * r⁻¹ := haH.symm
    rw [hk_eq]
    group
  exact ⟨a, rD, by simpa [rD] using hconj_x⟩

/-- In a transitive Frobenius action with point-stabilizer complement, the
kernel consists exactly of the identity and the derangements. -/
private theorem xi91_frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
    {H X : Type*} [Group H] [Finite H] [MulAction H X]
    (htrans : MulAction.IsPretransitive H X) (a : X)
    (F : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer H a)) (x : H) :
    x ∈ F ↔ x = 1 ∨ ∀ y : X, x • y ≠ y := by
  let : MulAction.IsPretransitive H X := htrans
  constructor
  · intro hx
    by_cases hxone : x = 1
    · exact Or.inl hxone
    right
    intro y hxy
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H a y
    have hfix : (g⁻¹ * x * g) • a = a := by
      calc
        (g⁻¹ * x * g) • a = g⁻¹ • (x • (g • a)) := by
          simp only [mul_smul]
        _ = g⁻¹ • (x • y) := by rw [hg]
        _ = g⁻¹ • y := by rw [hxy]
        _ = a := by rw [← hg, inv_smul_smul]
    have hmemD : g⁻¹ * x * g ∈ MulAction.stabilizer H a :=
      MulAction.mem_stabilizer_iff.mpr hfix
    have hmemF : g⁻¹ * x * g ∈ F := by
      simpa using hFrob.normal.conj_mem x hx g⁻¹
    have hconjOne : g⁻¹ * x * g = 1 :=
      Subgroup.disjoint_def.mp hFrob.isComplement'.disjoint hmemF hmemD
    apply hxone
    have := congrArg (fun z : H => g * z * g⁻¹) hconjOne
    simpa [mul_assoc] using this
  · rintro (rfl | hfree)
    · simp
    by_contra hxF
    obtain ⟨f, r, hconj⟩ :=
      xi91_frobenius_not_mem_kernel_conjugate_mem_complement
        F (MulAction.stabilizer H a) hFrob hxF
    have hxEq : x = (f : H) * (r : H) * (f : H)⁻¹ := by
      have := congrArg (fun z : H => (f : H) * z * (f : H)⁻¹) hconj
      simpa [mul_assoc] using this
    apply hfree ((f : H) • a)
    calc
      x • ((f : H) • a) =
          ((f : H) * (r : H) * (f : H)⁻¹) • ((f : H) • a) := by
            rw [hxEq]
      _ = (f : H) • ((r : H) • a) := by
        simp only [mul_smul, inv_smul_smul]
      _ = (f : H) • a := by
        rw [MulAction.mem_stabilizer_iff.mp r.property]

/-- A Frobenius kernel inside an ambient normal subgroup is ambient-normal:
its elements are characterized as the identity and the derangements. -/
private theorem xi91_frobenius_kernel_map_normal_of_ambient_normal
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (N : Subgroup G) (hN : N.Normal) (a : X)
    (K : Subgroup N) (htrans : MulAction.IsPretransitive N X)
    (hFrob : IsFrobeniusGroupWithKernelComplement K
      (MulAction.stabilizer N a)) :
    (K.map N.subtype).Normal := by
  let Kmap : Subgroup G := K.map N.subtype
  change Kmap.Normal
  refine ⟨?_⟩
  intro x hx g
  rcases hx with ⟨k, hkK, hkx⟩
  have hxN : x ∈ N := by
    rw [← hkx]
    exact k.property
  let yN : N := ⟨g * x * g⁻¹, hN.conj_mem x hxN g⟩
  have hyK : yN ∈ K := by
    apply (xi91_frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
      htrans a K hFrob yN).2
    rcases (xi91_frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
      htrans a K hFrob k).1 hkK with hkone | hkfree
    · left
      apply Subtype.ext
      have hxone : x = 1 := by
        calc
          x = (k : G) := hkx.symm
          _ = 1 := by simpa using congrArg Subtype.val hkone
      simp [yN, hxone]
    · right
      intro z hyfix
      apply hkfree (g⁻¹ • z)
      have hyfixG : (g * x * g⁻¹) • z = z := by
        simpa [yN] using hyfix
      have hkxG : (k : G) = x := hkx
      change (k : G) • (g⁻¹ • z) = g⁻¹ • z
      rw [hkxG]
      calc
        x • (g⁻¹ • z) = (x * g⁻¹) • z := by rw [mul_smul]
        _ = (g⁻¹ * (g * x * g⁻¹)) • z := by group
        _ = g⁻¹ • ((g * x * g⁻¹) • z) := by rw [mul_smul]
        _ = g⁻¹ • z := by rw [hyfixG]
  exact ⟨yN, hyK, rfl⟩

/-- Every nontrivial ambient normal subgroup has point stabilizer containing
the point-stabilizer Frobenius kernel. -/
private theorem xi91_zassenhaus_normal_stabilizer_contains_frobeniusKernel
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Finite X]
    (htwo : MulAction.IsMultiplyPretransitive G X 2)
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (N : Subgroup G) (hNnormal : N.Normal) (hNne : N ≠ ⊥) :
    let H := MulAction.stabilizer G a
    F ≤ N.comap H.subtype := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Na : Subgroup H := N.comap H.subtype
  change F ≤ Na
  let : N.Normal := hNnormal
  let : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  let : MulAction.IsQuasiPreprimitive G X :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have hfixed_ne_univ : MulAction.fixedPoints N X ≠ Set.univ := by
    intro hfixed
    apply hNne
    rw [eq_bot_iff]
    intro n hn
    have hn_one : n = 1 :=
      (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G X)) n (by
        intro x
        have hx : x ∈ MulAction.fixedPoints N X := by
          rw [hfixed]
          trivial
        exact MulAction.mem_fixedPoints.mp hx ⟨n, hn⟩)
    exact Subgroup.mem_bot.mpr hn_one
  have hNtrans : MulAction.IsPretransitive N X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
  have hNaNormal : Na.Normal := by
    simpa [Na] using hNnormal.comap H.subtype
  rcases xi91_frobenius_normal_subgroup_le_kernel_or_kernel_le
      F D Na (by simpa [D] using hFrob) hNaNormal with hNaF | hFNa
  · exfalso
    let R := MulAction.stabilizer N a
    have hRne : R ≠ ⊥ := by
      intro hRbot
      apply hno_regular_normal
      refine ⟨N, hNnormal, hNne, ?_⟩
      have hcomp : (⊤ : Subgroup N).IsComplement' R := by
        rw [hRbot]
        exact Subgroup.isComplement'_top_bot
      have hregularTop :=
        huppert_blackburn_XI_regular_of_isComplement_stabilizer
          (a := a) hcomp hNtrans
      intro x y
      obtain ⟨r, hr, hrunique⟩ := hregularTop x y
      refine ⟨(r : N), ?_, ?_⟩
      · simpa [Subgroup.smul_def] using hr
      intro n hn
      let nTop : (⊤ : Subgroup N) := ⟨n, trivial⟩
      have hnTop : (nTop : N) • x = y := by
        simpa [nTop, Subgroup.smul_def] using hn
      have heq : nTop = r := hrunique nTop hnTop
      exact congrArg Subtype.val heq
    have hRproper : R ≠ ⊤ := by
      intro hRtop
      obtain ⟨n, hn⟩ := hNtrans.exists_smul_eq a b
      have hnR : n ∈ R := by rw [hRtop]; simp
      have hfix : n • a = a := MulAction.mem_stabilizer_iff.mp hnR
      exact hab (hfix.symm.trans hn)
    let rToH : R → H := fun r =>
      ⟨((r : N) : G), by
        have hfix : (r : N) • a = a := MulAction.mem_stabilizer_iff.mp r.property
        have hfix' : ((r : N) : G) • a = a := by simpa [Subgroup.smul_def] using hfix
        exact MulAction.mem_stabilizer_iff.mpr hfix'⟩
    have hRtoF : ∀ r : R, rToH r ∈ F := by
      intro r
      apply hNaF
      change ((rToH r : H) : G) ∈ N
      exact (r : N).property
    have hRTI : ∀ g : N, g ∉ R → Disjoint R (R.conjBy g) := by
      intro g hgR
      rw [Subgroup.disjoint_def]
      intro x hxR hxconj
      by_contra hxne
      let xF : F := ⟨rToH ⟨x, hxR⟩, hRtoF ⟨x, hxR⟩⟩
      have hxFne : xF ≠ 1 := by
        intro hxone
        apply hxne
        apply Subtype.ext
        simpa [xF, rToH] using
          congrArg Subtype.val (congrArg Subtype.val hxone)
      rw [Subgroup.conjBy, Subgroup.mem_map] at hxconj
      rcases hxconj with ⟨r, hrR, hrx⟩
      have hxfixga : ((x : N) : G) • (((g : N) : G) • a) =
          ((g : N) : G) • a := by
        have hrfix : (r : N) • a = a :=
          MulAction.mem_stabilizer_iff.mp hrR
        have hxval : (x : N) = g * r * g⁻¹ := hrx.symm
        have hxvalG : ((x : N) : G) =
            ((g : N) : G) * ((r : N) : G) * ((g : N) : G)⁻¹ := by
          exact congrArg Subtype.val hxval
        have hrfixG : ((r : N) : G) • a = a := by simpa [Subgroup.smul_def] using hrfix
        calc
          ((x : N) : G) • (((g : N) : G) • a) =
              (((g : N) : G) * ((r : N) : G) * ((g : N) : G)⁻¹) •
                (((g : N) : G) • a) := by rw [hxvalG]
          _ = ((g : N) : G) • (((r : N) : G) • a) := by
            simp only [mul_smul, inv_smul_smul]
          _ = ((g : N) : G) • a := by rw [hrfixG]
      have hga : ((g : N) : G) • a = a :=
        (xi91_frobeniusKernel_uniqueFixedPoint
          htwo a b hab F hFrob xF hxFne (((g : N) : G) • a)).mp (by simpa [xF, rToH] using hxfixga)
      apply hgR
      exact MulAction.mem_stabilizer_iff.mpr (by simpa [Subgroup.smul_def] using hga)
    obtain ⟨K, hKFrob⟩ :=
      Suzuki.VI.suzuki_ch6_theorem_2_3 R hRne hRproper hRTI
    let Kmap : Subgroup G := K.map N.subtype
    have hKmapNormal : Kmap.Normal := by
      simpa [Kmap] using
        xi91_frobenius_kernel_map_normal_of_ambient_normal
          N hNnormal a K hNtrans hKFrob
    have hKmapNe : Kmap ≠ ⊥ := by
      intro hKmapBot
      apply hKFrob.kernel_ne_bot
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := K) (f := N.subtype) N.subtype_injective).mp
          (by simpa [Kmap] using hKmapBot)
    apply hno_regular_normal
    refine ⟨Kmap, hKmapNormal, hKmapNe, ?_⟩
    have hKregular :=
      huppert_blackburn_XI_regular_of_isComplement_stabilizer
        (a := a) hKFrob.isComplement' hNtrans
    intro x y
    obtain ⟨k, hk, hkunique⟩ := hKregular x y
    let kg : Kmap := ⟨((k : N) : G), ⟨(k : N), k.property, rfl⟩⟩
    refine ⟨kg, by simpa [Kmap, kg, Subgroup.smul_def] using hk, ?_⟩
    intro z hz
    rcases z.property with ⟨n, hnK, hnz⟩
    let nK : K := ⟨n, hnK⟩
    have hnact : (nK : N) • x = y := by
      have hnzG : ((nK : N) : G) = (z : G) := by
        simpa [nK] using hnz
      calc
        (nK : N) • x = ((nK : N) : G) • x := rfl
        _ = (z : G) • x := by rw [hnzG]
        _ = y := hz
    have hnk : nK = k := hkunique nK hnact
    apply Subtype.ext
    calc
      (z : G) = (n : G) := hnz.symm
      _ = ((k : N) : G) := by rw [show n = (k : N) from congrArg Subtype.val hnk]
      _ = (kg : G) := rfl
  · exact hFNa

/-- Every nontrivial ambient normal subgroup is doubly transitive. -/
private theorem xi91_zassenhaus_nontrivial_normal_is_two_pretransitive
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Finite X]
    (htwo : MulAction.IsMultiplyPretransitive G X 2)
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (N : Subgroup G) (hNnormal : N.Normal) (hNne : N ≠ ⊥) :
    MulAction.IsMultiplyPretransitive N X 2 := by
  let H := MulAction.stabilizer G a
  let : N.Normal := hNnormal
  let : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  let : MulAction.IsQuasiPreprimitive G X :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have hfixed_ne_univ : MulAction.fixedPoints N X ≠ Set.univ := by
    intro hfixed
    apply hNne
    rw [eq_bot_iff]
    intro n hn
    have hn_one : n = 1 :=
      (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G X)) n (by
        intro x
        have hx : x ∈ MulAction.fixedPoints N X := by
          rw [hfixed]
          trivial
        exact MulAction.mem_fixedPoints.mp hx ⟨n, hn⟩)
    exact Subgroup.mem_bot.mpr hn_one
  have hNtrans : MulAction.IsPretransitive N X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
  have hFNa : F ≤ N.comap H.subtype := by
    simpa [H] using
      xi91_zassenhaus_normal_stabilizer_contains_frobeniusKernel
        htwo hno_regular_normal a b hab F hFrob N hNnormal hNne
  have hstab_multi :
      MulAction.IsMultiplyPretransitive H
        (SubMulAction.ofStabilizer G a) 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := a)).mp htwo
  have hHtrans :
      MulAction.IsPretransitive H (SubMulAction.ofStabilizer G a) :=
    (MulAction.is_one_pretransitive_iff
      (G := H) (α := SubMulAction.ofStabilizer G a)).mp hstab_multi
  have hFregular :
      ∀ x y : SubMulAction.ofStabilizer G a,
        ∃! f : F, (f : H) • x = y :=
    huppert_blackburn_XI_regular_of_isComplement_stabilizer
      hFrob.isComplement' hHtrans
  have htoBase : ∀ x y : X, x ≠ y →
      ∃ n : N, n • x = a ∧ n • y = b := by
    intro x y hxy
    obtain ⟨n0, hn0x⟩ := hNtrans.exists_smul_eq x a
    have hn0y_ne : n0 • y ≠ a := by
      intro hn0y
      apply hxy
      exact smul_left_cancel n0 (hn0x.trans hn0y.symm)
    let ySub : SubMulAction.ofStabilizer G a := ⟨n0 • y, hn0y_ne⟩
    let bSub : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
    obtain ⟨f, hf, _hfunique⟩ := hFregular ySub bSub
    have hfNmem : ((f : H) : G) ∈ N := by
      exact hFNa f.property
    let fN : N := ⟨((f : H) : G), hfNmem⟩
    have hfixa : fN • a = a := by
      change ((f : H) : G) • a = a
      exact MulAction.mem_stabilizer_iff.mp (f : H).property
    have hfY : fN • (n0 • y) = b := by
      simpa [fN, ySub, bSub, Subgroup.smul_def] using congrArg Subtype.val hf
    refine ⟨fN * n0, ?_, ?_⟩
    · rw [mul_smul, hn0x, hfixa]
    · rw [mul_smul, hfY]
  apply MulAction.is_two_pretransitive_iff.mpr
  intro x y u v hxy huv
  obtain ⟨p, hpx, hpy⟩ := htoBase x y hxy
  obtain ⟨q, hqu, hqv⟩ := htoBase u v huv
  refine ⟨q⁻¹ * p, ?_, ?_⟩
  · rw [mul_smul, hpx, ← hqu, inv_smul_smul]
  · rw [mul_smul, hpy, ← hqv, inv_smul_smul]

/-- Restrict a Frobenius decomposition to a subgroup containing its kernel. -/
private theorem xi91_frobenius_restrict_to_subgroup_containing_kernel
    {H : Type*} [Group H]
    (K R N : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement K R)
    (hKN : K ≤ N)
    (hRcap_ne : R.comap N.subtype ≠ ⊥) :
    IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf N) (R.comap N.subtype) := by
  have hKsub_normal : (K.subgroupOf N).Normal :=
    hFrob.normal.subgroupOf N
  have hKsub_ne : K.subgroupOf N ≠ ⊥ := by
    intro hbot
    apply hFrob.kernel_ne_bot
    rw [eq_bot_iff]
    intro k hk
    let kN : N := ⟨k, hKN hk⟩
    have hkSub : kN ∈ K.subgroupOf N := hk
    have hkBot : kN ∈ (⊥ : Subgroup N) := by simpa [hbot] using hkSub
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp hkBot))
  have hcomp :
      (K.subgroupOf N).IsComplement' (R.comap N.subtype) := by
    apply (Subgroup.isComplement_iff_existsUnique).mpr
    intro n
    obtain ⟨kr, hkr, huniq⟩ :=
      (Subgroup.isComplement_iff_existsUnique.mp hFrob.isComplement')
        (n : H)
    let kN : N := ⟨(kr.1 : H), hKN kr.1.property⟩
    have hrNmem : (kr.2 : H) ∈ N := by
      have hnmem : (n : H) ∈ N := n.property
      have hkInv : (kr.1 : H)⁻¹ ∈ N := N.inv_mem (hKN kr.1.property)
      have hEq : (kr.2 : H) = (kr.1 : H)⁻¹ * (n : H) := by
        rw [← hkr]
        simp
      rw [hEq]
      exact N.mul_mem hkInv hnmem
    let rN : N := ⟨(kr.2 : H), hrNmem⟩
    let kSub : K.subgroupOf N := ⟨kN, kr.1.property⟩
    let rSub : R.comap N.subtype := ⟨rN, kr.2.property⟩
    refine ⟨(kSub, rSub), ?_, ?_⟩
    · apply Subtype.ext
      exact hkr
    · intro yz hyz
      let yK : K := ⟨((yz.1 : N) : H), yz.1.property⟩
      let yR : R := ⟨((yz.2 : N) : H), yz.2.property⟩
      have hyzH : (yK : H) * (yR : H) = (n : H) :=
        congrArg Subtype.val hyz
      have hpair : (yK, yR) = kr := huniq (yK, yR) hyzH
      apply Prod.ext
      · apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun q : K × R => (q.1 : H)) hpair
      · apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun q : K × R => (q.2 : H)) hpair
  refine ⟨hKsub_normal, hcomp, ?_, hKsub_ne, hRcap_ne⟩
  intro g hgRcap
  have hgR : ((g : N) : H) ∉ R := by
    intro hg
    exact hgRcap hg
  rw [Subgroup.disjoint_def]
  intro x hxR hxconj
  have hxRH : ((x : N) : H) ∈ R := hxR
  have hxconjH : ((x : N) : H) ∈ R.conjBy ((g : N) : H) := by
    rw [Subgroup.conjBy, Subgroup.mem_map] at hxconj ⊢
    rcases hxconj with ⟨r, hr, hrx⟩
    refine ⟨((r : N) : H), hr, ?_⟩
    exact congrArg Subtype.val hrx
  have hxBot : ((x : N) : H) ∈ (⊥ : Subgroup H) :=
    (Subgroup.disjoint_def.mp
      (hFrob.disjoint_conjBy ((g : N) : H) hgR)) hxRH hxconjH
  apply Subtype.ext
  exact Subgroup.mem_bot.mp hxBot

/-- A nontrivial regular normal subgroup of a finite doubly transitive group
is elementary Abelian. -/
private theorem xi91_zassenhaus_regular_normal_elementaryAbelian
    {N X : Type*} [Group N] [Finite N] [MulAction N X]
    [FaithfulSMul N X]
    (htwo : MulAction.IsMultiplyPretransitive N X 2)
    (a : X) (M : Subgroup N) (hMnormal : M.Normal) (hMne : M ≠ ⊥)
    (hMregular :
      ∀ x y : X, ∃! m : M, (m : N) • x = y) :
    ∃ p : ℕ, Nat.Prime p ∧ IsElementaryAbelian p M := by
  classical
  let : M.Normal := hMnormal
  have hmove (m : M) (hm : m ≠ 1) : (m : N) • a ≠ a := by
    intro hma
    obtain ⟨m0, hm0, huniq⟩ := hMregular a a
    have hmm0 : m = m0 := huniq m hma
    have h1m0 : (1 : M) = m0 := huniq 1 (by simp)
    exact hm (hmm0.trans h1m0.symm)
  have hconj_transitive :
      ∀ x y : M, x ≠ 1 → y ≠ 1 →
        ∃ d : N, d * (x : N) * d⁻¹ = (y : N) := by
    intro x y hx hy
    obtain ⟨d, hda, hdxy⟩ :=
      MulAction.is_two_pretransitive_iff.mp htwo
        (hmove x hx) (hmove y hy)
    let xconj : M :=
      ⟨d * (x : N) * d⁻¹,
        hMnormal.conj_mem (x : N) x.property d⟩
    have hdia : d⁻¹ • a = a := by
      calc
        d⁻¹ • a = d⁻¹ • (d • a) := by rw [hdxy]
        _ = a := inv_smul_smul d a
    have hxconj_act : (xconj : N) • a = (y : N) • a := by
      change (d * (x : N) * d⁻¹) • a = (y : N) • a
      rw [mul_smul, mul_smul, hdia]
      exact hda
    obtain ⟨m0, hm0, huniq⟩ := hMregular a ((y : N) • a)
    have hxm0 : xconj = m0 := huniq xconj hxconj_act
    have hym0 : y = m0 := huniq y rfl
    exact ⟨d, congrArg Subtype.val (hxm0.trans hym0.symm)⟩
  let : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hMne
  have hMcard_ne_one : Nat.card M ≠ 1 :=
    ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hMcard_ne_one
  let : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hzne : z ≠ 1 := by
    intro hz
    have : p = 1 := by simpa [hz] using hzorder.symm
    exact hp.ne_one this
  have hprime_order (x : M) (hx : x ≠ 1) : orderOf x = p := by
    obtain ⟨d, hd⟩ := hconj_transitive x z hx hzne
    have hsemi : SemiconjBy d (x : N) (z : N) := by
      change d * (x : N) = (z : N) * d
      calc
        d * (x : N) = (d * (x : N) * d⁻¹) * d := by group
        _ = (z : N) * d := by rw [hd]
    calc
      orderOf x = orderOf (x : N) :=
        (orderOf_injective M.subtype M.subtype_injective x).symm
      _ = orderOf (z : N) := SemiconjBy.orderOf_eq d hsemi
      _ = orderOf z := orderOf_injective M.subtype M.subtype_injective z
      _ = p := hzorder
  have hMp : IsPGroup p M := (IsPGroup.iff_orderOf).2 (by
    intro x
    by_cases hx : x = 1
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [hprime_order x hx]⟩)
  have hMcomm : IsMulCommutative M := by
    let : Nontrivial (Subgroup.center M) := hMp.center_nontrivial
    obtain ⟨zc, hzc⟩ := exists_ne (1 : Subgroup.center M)
    let zM : M := zc
    have hzM_ne : zM ≠ 1 := by
      intro hzM
      apply hzc
      exact Subtype.ext hzM
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    by_cases hx : x = 1
    · simp [hx]
    obtain ⟨d, hd⟩ := hconj_transitive x zM hx hzM_ne
    let ydy : M :=
      ⟨d * (y : N) * d⁻¹,
        hMnormal.conj_mem (y : N) y.property d⟩
    have hz_comm : zM * ydy = ydy * zM :=
      ((Subgroup.mem_center_iff.mp zc.property) ydy).symm
    have hz_comm_N :
        (zM : N) * (d * (y : N) * d⁻¹) =
          (d * (y : N) * d⁻¹) * (zM : N) := by
      simpa [ydy, zM] using congrArg Subtype.val hz_comm
    apply Subtype.ext
    change (x : N) * (y : N) = (y : N) * (x : N)
    calc
      (x : N) * (y : N) =
          d⁻¹ * (zM : N) * d * (y : N) := by
            rw [← hd]
            group
      _ = d⁻¹ * ((zM : N) * (d * (y : N) * d⁻¹)) * d := by
            group
      _ = d⁻¹ * ((d * (y : N) * d⁻¹) * (zM : N)) * d := by
            rw [hz_comm_N]
      _ = (y : N) * (d⁻¹ * (zM : N) * d) := by
            group
      _ = (y : N) * (x : N) := by
            rw [← hd]
            group
  have hMelem : IsElementaryAbelian p M := by
    refine
      { toIsMulCommutative := hMcomm
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_ }
    intro x
    by_cases hx : x = 1
    · simp [hx]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hprime_order x hx]
  exact ⟨p, hp, hMelem⟩

/-- A finite faithful doubly transitive group has at most one nontrivial
regular normal subgroup. -/
private theorem xi91_zassenhaus_regular_normal_unique
    {N X : Type*} [Group N] [Finite N] [MulAction N X]
    [FaithfulSMul N X] [Finite X]
    (htwo : MulAction.IsMultiplyPretransitive N X 2)
    (a : X) (M R : Subgroup N)
    (hMnormal : M.Normal) (hRnormal : R.Normal)
    (hMne : M ≠ ⊥) (_hRne : R ≠ ⊥)
    (hMregular :
      ∀ x y : X, ∃! m : M, (m : N) • x = y)
    (hRregular :
      ∀ x y : X, ∃! r : R, (r : N) • x = y) :
    M = R := by
  classical
  let : M.Normal := hMnormal
  let : R.Normal := hRnormal
  let : MulAction.IsPreprimitive N X :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  let : MulAction.IsQuasiPreprimitive N X :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have normal_transitive (K : Subgroup N) (hKnormal : K.Normal)
      (hKne : K ≠ ⊥) : MulAction.IsPretransitive K X := by
    let : K.Normal := hKnormal
    apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
    intro hfixed
    apply hKne
    rw [eq_bot_iff]
    intro k hk
    have hk_one : k = 1 :=
      (faithfulSMul_iff.mp (inferInstance : FaithfulSMul N X)) k (by
        intro x
        have hx : x ∈ MulAction.fixedPoints K X := by
          rw [hfixed]
          trivial
        exact MulAction.mem_fixedPoints.mp hx ⟨k, hk⟩)
    exact Subgroup.mem_bot.mpr hk_one
  let J := M ⊓ R
  have hJnormal : J.Normal := by
    dsimp [J]
    infer_instance
  by_cases hJne : J ≠ ⊥
  · have hJtrans : MulAction.IsPretransitive J X :=
      normal_transitive J hJnormal hJne
    have hMleR : M ≤ R := by
      intro m hm
      let mM : M := ⟨m, hm⟩
      obtain ⟨j, hj⟩ := hJtrans.exists_smul_eq a (m • a)
      let jM : M := ⟨(j : N), j.property.1⟩
      obtain ⟨m0, hm0, huniq⟩ := hMregular a (m • a)
      have hjm0 : jM = m0 := huniq jM (by simpa [jM, Subgroup.smul_def] using hj)
      have hmm0 : mM = m0 := huniq mM rfl
      have hmj : m = (j : N) :=
        congrArg Subtype.val (hmm0.trans hjm0.symm)
      rw [hmj]
      exact j.property.2
    have hRleM : R ≤ M := by
      intro r hr
      let rR : R := ⟨r, hr⟩
      obtain ⟨j, hj⟩ := hJtrans.exists_smul_eq a (r • a)
      let jR : R := ⟨(j : N), j.property.2⟩
      obtain ⟨r0, hr0, huniq⟩ := hRregular a (r • a)
      have hjr0 : jR = r0 := huniq jR (by simpa [jR, Subgroup.smul_def] using hj)
      have hrr0 : rR = r0 := huniq rR rfl
      have hrj : r = (j : N) :=
        congrArg Subtype.val (hrr0.trans hjr0.symm)
      rw [hrj]
      exact j.property.1
    exact le_antisymm hMleR hRleM
  · have hJbot : J = ⊥ := not_ne_iff.mp hJne
    have hcomm_bot : ⁅M, R⁆ = ⊥ := by
      apply eq_bot_iff.mpr
      rw [← hJbot]
      exact Subgroup.commutator_le_inf M R
    have hMcentR : M ≤ Subgroup.centralizer R :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := M) (H₂ := R)).mp hcomm_bot
    obtain ⟨p, hp, hMelem⟩ :=
      xi91_zassenhaus_regular_normal_elementaryAbelian
        htwo a M hMnormal hMne hMregular
    let : IsMulCommutative M := hMelem.toIsMulCommutative
    have hRleM : R ≤ M := by
      intro r hr
      obtain ⟨m, hmact, _hmunique⟩ := hMregular a (r • a)
      have hrm : r = (m : N) := by
        apply eq_of_smul_eq_smul (α := X)
        intro x
        obtain ⟨k, hkact, _hkunique⟩ := hMregular a x
        have hrk : r * (k : N) = (k : N) * r :=
          (Subgroup.mem_centralizer_iff.mp (hMcentR k.property)) r hr
        have hkm : (k : N) * (m : N) = (m : N) * (k : N) :=
          congrArg Subtype.val (mul_comm' k m)
        calc
          r • x = r • ((k : N) • a) := by rw [hkact]
          _ = (r * (k : N)) • a := (mul_smul r (k : N) a).symm
          _ = ((k : N) * r) • a := by rw [hrk]
          _ = (k : N) • (r • a) := mul_smul (k : N) r a
          _ = (k : N) • ((m : N) • a) := by rw [hmact]
          _ = ((k : N) * (m : N)) • a :=
            (mul_smul (k : N) (m : N) a).symm
          _ = ((m : N) * (k : N)) • a := by rw [hkm]
          _ = (m : N) • ((k : N) • a) := mul_smul (m : N) (k : N) a
          _ = (m : N) • x := by rw [hkact]
      rw [hrm]
      exact m.property
    have hMleR : M ≤ R := by
      intro m hm
      let mM : M := ⟨m, hm⟩
      obtain ⟨r, hract, _hrunique⟩ := hRregular a (m • a)
      have hrM : (r : N) ∈ M := hRleM r.property
      let rM : M := ⟨(r : N), hrM⟩
      obtain ⟨m0, hm0, huniq⟩ := hMregular a (m • a)
      have hrm0 : rM = m0 := huniq rM (by simpa [rM] using hract)
      have hmm0 : mM = m0 := huniq mM rfl
      have hmr : m = (r : N) :=
        congrArg Subtype.val (hmm0.trans hrm0.symm)
      rw [hmr]
      exact r.property
    exact le_antisymm hMleR hRleM

/-- A nontrivial ambient normal subgroup inherits the absence of regular
normal subgroups. -/
private theorem xi91_zassenhaus_normal_subgroup_no_regular_normal
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Finite X]
    (N : Subgroup G) (hNnormal : N.Normal) (a : X)
    (hNtwo : MulAction.IsMultiplyPretransitive N X 2)
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y) :
    ¬ ∃ M : Subgroup N, M.Normal ∧ M ≠ ⊥ ∧
      ∀ x y : X, ∃! m : M, (m : N) • x = y := by
  classical
  let : N.Normal := hNnormal
  rintro ⟨M, hMnormal, hMne, hMregular⟩
  let : M.Normal := hMnormal
  have hMconj_eq (g : G) :
      M.map (MulAut.conjNormal (H := N) g) = M := by
    let phi : MulAut N := MulAut.conjNormal (H := N) g
    let Mg : Subgroup N := M.map phi
    have hMgnormal : Mg.Normal := by
      exact hMnormal.map phi.toMonoidHom phi.surjective
    have hMgne : Mg ≠ ⊥ := by
      intro hMgBot
      apply hMne
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := M) (f := phi) phi.injective).mp (by simpa [Mg] using hMgBot)
    have hMgregular :
        ∀ x y : X, ∃! mg : Mg, (mg : N) • x = y := by
      intro x y
      obtain ⟨m, hmact, hmunique⟩ :=
        hMregular (g⁻¹ • x) (g⁻¹ • y)
      let mg : Mg :=
        ⟨phi (m : N), ⟨(m : N), m.property, rfl⟩⟩
      have hmgact : (mg : N) • x = y := by
        change ((phi (m : N) : N) : G) • x = y
        change (g * ((m : N) : G) * g⁻¹) • x = y
        calc
          (g * ((m : N) : G) * g⁻¹) • x =
              g • (((m : N) : G) • (g⁻¹ • x)) := by
                simp only [mul_smul]
          _ = g • (g⁻¹ • y) := by
            simpa [Subgroup.smul_def] using congrArg (fun z => g • z) hmact
          _ = y := smul_inv_smul g y
      refine ⟨mg, hmgact, ?_⟩
      intro z hz
      rcases z.property with ⟨n, hnM, hnz⟩
      let nM : M := ⟨n, hnM⟩
      have hnzG :
          g * ((n : N) : G) * g⁻¹ = ((z : N) : G) := by
        simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using
          congrArg (fun q : N => (q : G)) hnz
      have hnact : (nM : N) • (g⁻¹ • x) = g⁻¹ • y := by
        change ((n : N) : G) • (g⁻¹ • x) = g⁻¹ • y
        calc
          ((n : N) : G) • (g⁻¹ • x) =
              (((n : N) : G) * g⁻¹) • x :=
                (mul_smul ((n : N) : G) g⁻¹ x).symm
          _ = (g⁻¹ * (g * ((n : N) : G) * g⁻¹)) • x := by
                congr 1
                group
          _ = g⁻¹ • ((g * ((n : N) : G) * g⁻¹) • x) :=
                mul_smul g⁻¹ (g * ((n : N) : G) * g⁻¹) x
          _ = g⁻¹ • (((z : N) : G) • x) := by rw [hnzG]
          _ = g⁻¹ • y := by
            simpa [Subgroup.smul_def] using congrArg (fun q => g⁻¹ • q) hz
      have hnm : nM = m := hmunique nM hnact
      apply Subtype.ext
      calc
        (z : N) = phi n := hnz.symm
        _ = phi (m : N) := by rw [show n = (m : N) from congrArg Subtype.val hnm]
        _ = (mg : N) := rfl
    have hEq : Mg = M :=
      (xi91_zassenhaus_regular_normal_unique
        hNtwo a M Mg hMnormal hMgnormal hMne hMgne hMregular hMgregular).symm
    simpa [Mg, phi] using hEq
  let K : Subgroup G := M.map N.subtype
  have hKnormal : K.Normal := by
    refine ⟨?_⟩
    intro x hx g
    rcases hx with ⟨n, hnM, hnx⟩
    let phi : MulAut N := MulAut.conjNormal (H := N) g
    have hphiM : phi n ∈ M := by
      have hmem : phi n ∈ M.map phi :=
        Subgroup.mem_map_of_mem phi.toMonoidHom hnM
      rw [hMconj_eq g] at hmem
      exact hmem
    refine ⟨phi n, hphiM, ?_⟩
    rw [← hnx]
    rfl
  have hKne : K ≠ ⊥ := by
    intro hKbot
    apply hMne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := M) (f := N.subtype) N.subtype_injective).mp
        (by simpa [K] using hKbot)
  apply hno_regular_normal
  refine ⟨K, hKnormal, hKne, ?_⟩
  intro x y
  obtain ⟨m, hmact, hmunique⟩ := hMregular x y
  let kg : K :=
    ⟨((m : N) : G), ⟨(m : N), m.property, rfl⟩⟩
  refine ⟨kg, by simpa [kg, Subgroup.smul_def] using hmact, ?_⟩
  intro z hz
  rcases z.property with ⟨n, hnM, hnz⟩
  let nM : M := ⟨n, hnM⟩
  have hnact : (nM : N) • x = y := by
    have hnzG : ((nM : N) : G) = (z : G) := by
      simpa [nM] using hnz
    calc
      (nM : N) • x = ((nM : N) : G) • x := rfl
      _ = (z : G) • x := by rw [hnzG]
      _ = y := hz
  have hnm : nM = m := hmunique nM hnact
  apply Subtype.ext
  calc
    (z : G) = (n : G) := hnz.symm
    _ = ((m : N) : G) := by rw [show n = (m : N) from congrArg Subtype.val hnm]
    _ = (kg : G) := rfl

attribute [local instance] Fintype.ofFinite

def xi91_matrixLeftMul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun := fun M => A * M
  map_add' _ _ := Matrix.mul_add _ _ _
  map_smul' c M := Matrix.mul_smul A c M

def xi91_matrixRightMul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun := fun M => M * A
  map_add' _ _ := Matrix.add_mul _ _ _
  map_smul' c M := Matrix.smul_mul c M A

lemma xi91_matrix_stdBasis_repr_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (i j : ι) :
    (Matrix.stdBasis ℂ ι ι).repr M (i, j) = M i j := by
  simp [Matrix.stdBasis]

lemma xi91_trace_matrix_flip_mulLeft_mulRight
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    LinearMap.trace ℂ (Matrix ι ι ℂ)
      ((LinearEquiv.toLinearMap (Matrix.transposeLinearEquiv ι ι ℂ ℂ)).comp
        ((xi91_matrixLeftMul (Matrix.transpose A)).comp
        (xi91_matrixRightMul A))) =
      Matrix.trace (A * A) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ ι ι), Matrix.trace]
  rw [Fintype.sum_prod_type]
  simp [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, Matrix.mul_apply,
    xi91_matrix_stdBasis_repr_apply, Matrix.trace]
  have hinner : ∀ x x' y' : ι,
      (∑ y : ι, if x' = x then if y = y' then A y x' else 0 else 0) =
        if x' = x then A y' x' else 0 := by
    intro x x' y'
    by_cases h : x' = x
    · simp [h]
    · simp [h]
  have hinner2 : ∀ x x₁ x₂ : ι,
      (∑ x₃ : ι, if x = x₂ ∧ x₁ = x₃ then A x₃ x else 0) =
        if x = x₂ then A x₁ x else 0 := by
    intro x x₁ x₂
    by_cases h : x = x₂
    · simp [h]
    · simp [h]
  simp [xi91_matrixLeftMul, xi91_matrixRightMul, Matrix.mul_apply, Matrix.single_apply, hinner2, mul_comm]

lemma xi91_bilinForm_toMatrix_flip
    {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*}
    [AddCommMonoid W] [Module ℂ W] (b : Module.Basis ι ℂ W)
    (B : LinearMap.BilinForm ℂ W) :
    LinearMap.BilinForm.toMatrix b
        (((LinearMap.BilinForm.flipHom :
            LinearMap.BilinForm ℂ W ≃ₗ[ℂ] LinearMap.BilinForm ℂ W).toLinearMap) B) =
      (LinearMap.BilinForm.toMatrix b B).transpose := by
  ext i j
  simp [LinearMap.BilinForm.flip_apply]

lemma xi91_representation_character_eq_inv_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hfixed : ρ.character = conjugateCharacter ρ.character) (g : G) :
    ρ.character g = ρ.character g⁻¹ := by
  have hreal : star (ρ.character g) = ρ.character g := by
    simpa [conjugateCharacter] using (congrFun hfixed g).symm
  calc
    ρ.character g = star (ρ.character g) := hreal.symm
    _ = ρ.character g⁻¹ := (Section1.representation_character_inv_eq_star_character ρ g).symm

lemma xi91_representation_dual_character_eq_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hfixed : ρ.character = conjugateCharacter ρ.character) :
    ρ.dual.character = ρ.character := by
  ext g
  rw [Representation.char_dual]
  symm
  exact xi91_representation_character_eq_inv_of_fixed_conjugate ρ hfixed g

lemma xi91_representation_self_dual_hom_finrank_eq_one_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (hfixed : ρ.character = conjugateCharacter ρ.character) :
    Module.finrank ℂ (Representation.IntertwiningMap ρ ρ.dual) = 1 := by
  classical
  have hchars : ρ.dual.character = ρ.character :=
    xi91_representation_dual_character_eq_of_fixed_conjugate ρ hfixed
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card G ≠ 0)
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  let : Representation.IsIrreducible ρ := hρ_irreducible
  have horth :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ = 1 := by
    have h := Representation.char_orthonormal (ρ := ρ) (σ := ρ)
    have hnonempty : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩
    simpa [hnonempty] using h
  have hscalar :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.dual.character g * ρ.character g⁻¹ =
        Module.finrank ℂ (Representation.IntertwiningMap ρ ρ.dual) := by
    simpa using
      (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρ) (σ := ρ.dual))
  rw [hchars, horth] at hscalar
  exact_mod_cast hscalar.symm


lemma xi91_representation_flip_linHom_dual_comm
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ((LinearMap.BilinForm.flipHom :
        LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap).comp
        ((Representation.linHom ρ ρ.dual) g) =
      ((Representation.linHom ρ ρ.dual) g).comp
        ((LinearMap.BilinForm.flipHom :
          LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap) := by
  ext B x y
  simp [Representation.linHom_apply, LinearMap.BilinForm.flip_apply, Module.Dual.transpose_apply]

lemma xi91_representation_linHom_dual_invariants_finrank_eq_one_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (hfixed : ρ.character = conjugateCharacter ρ.character) :
    Module.finrank ℂ
      (Representation.invariants (Representation.linHom ρ ρ.dual)) = 1 := by
  calc
    Module.finrank ℂ
        (Representation.invariants (Representation.linHom ρ ρ.dual)) =
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ.dual) := by
        simpa using
          (Representation.invariantsEquivIntertwiningMap (ρ := ρ) (σ := ρ.dual)).finrank_eq
    _ = 1 :=
      xi91_representation_self_dual_hom_finrank_eq_one_of_fixed_conjugate ρ hρ_irreducible hfixed

lemma xi91_representation_linHom_dual_apply_eq_comp
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G)
    (B : LinearMap.BilinForm ℂ V) :
    (Representation.linHom ρ ρ.dual g) B =
      B.comp (ρ g⁻¹) (ρ g⁻¹) := by
  ext x y
  rfl

lemma xi91_representation_trace_flip_linHom_dual_eq_character_inv_mul_inv
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ V)
      (((LinearMap.BilinForm.flipHom :
            LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap).comp
        ((Representation.linHom ρ ρ.dual) g)) =
      ρ.character (g⁻¹ * g⁻¹) := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℂ V
  let b : Module.Basis ι ℂ V := Module.Free.chooseBasis ℂ V
  let A : Matrix ι ι ℂ := LinearMap.toMatrix b b (ρ g⁻¹)
  let F :
      LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V :=
    (((LinearMap.BilinForm.flipHom :
        LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap).comp
      ((Representation.linHom ρ ρ.dual) g))
  calc
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ V) F =
        LinearMap.trace ℂ (Matrix ι ι ℂ)
          ((LinearMap.BilinForm.toMatrix b).conj F) := by
          symm
          exact LinearMap.trace_conj' F (LinearMap.BilinForm.toMatrix b)
    _ =
        LinearMap.trace ℂ (Matrix ι ι ℂ)
          ((LinearEquiv.toLinearMap (Matrix.transposeLinearEquiv ι ι ℂ ℂ)).comp
            ((xi91_matrixLeftMul (Matrix.transpose A)).comp (xi91_matrixRightMul A))) := by
          congr 1
          ext M i j
          simp only [LinearEquiv.conj_apply, F, LinearMap.comp_apply]
          rw [LinearMap.BilinForm.toMatrix_symm]
          rw [xi91_representation_linHom_dual_apply_eq_comp]
          have hflip :
              LinearMap.BilinForm.toMatrix b
                  (((LinearMap.BilinForm.flipHom :
                      LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap)
                    ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹))) =
                (LinearMap.BilinForm.toMatrix b
                  ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹))).transpose := by
            exact
              xi91_bilinForm_toMatrix_flip b
                ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹))
          have hcomp :
              LinearMap.BilinForm.toMatrix b
                  ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹)) =
                (LinearMap.toMatrix b b (ρ g⁻¹)).transpose * M *
                  LinearMap.toMatrix b b (ρ g⁻¹) := by
            simpa [LinearMap.BilinForm.toMatrix_symm, mul_assoc] using
              (LinearMap.BilinForm.toMatrix_comp (b := b) (c := b)
                (B := Matrix.toBilin b M) (l := ρ g⁻¹) (r := ρ g⁻¹))
          calc
            ((LinearMap.BilinForm.toMatrix b)
                (((LinearMap.BilinForm.flipHom :
                    LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap)
                  ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹)))) i j =
                ((LinearMap.BilinForm.toMatrix b
                  ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹))).transpose) i j := by
                    exact congrArg (fun N : Matrix ι ι ℂ => N i j) hflip
            _ = (((LinearMap.toMatrix b b (ρ g⁻¹)).transpose * M *
                    LinearMap.toMatrix b b (ρ g⁻¹)).transpose) i j := by
                    simpa using congrArg (fun N : Matrix ι ι ℂ => N j i) hcomp
            _ = ((A.transpose * (M * A)).transpose) i j := by
                    simp [A, mul_assoc]
            _ = (Matrix.transposeLinearEquiv ι ι ℂ ℂ
                  ((xi91_matrixLeftMul (Matrix.transpose A)) ((xi91_matrixRightMul A) M))) i j := by
                    rfl
    _ = Matrix.trace (A * A) := xi91_trace_matrix_flip_mulLeft_mulRight A
    _ = Matrix.trace (LinearMap.toMatrix b b ((ρ g⁻¹) * (ρ g⁻¹))) := by
          simp [A, LinearMap.toMatrix_mul]
    _ = LinearMap.trace ℂ V ((ρ g⁻¹) * (ρ g⁻¹)) := by
          symm
          exact LinearMap.trace_eq_matrix_trace ℂ b ((ρ g⁻¹) * (ρ g⁻¹))
    _ = LinearMap.trace ℂ V (ρ (g⁻¹ * g⁻¹)) := by
          rw [← MonoidHom.map_mul]
    _ = ρ.character (g⁻¹ * g⁻¹) := rfl


private noncomputable def xi91_classFunctionIndicator
    (G : Type*) [Group G] [Finite G] (theta : ClassFunction G) : ℂ := by
  classical
  exact (Nat.card G : ℂ)⁻¹ * ∑ g : G, theta (g⁻¹ * g⁻¹)

private theorem xi91_invSq_bijective_of_odd_card
    {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G)) :
    Function.Bijective (fun g : G => g⁻¹ * g⁻¹) := by
  have hsurj : Function.Surjective (fun g : G => g⁻¹ * g⁻¹) := by
    intro z
    have hoddOrder : Odd (orderOf z) :=
      Odd.of_dvd_nat hodd (orderOf_dvd_natCard z)
    rcases hoddOrder with ⟨m, hm⟩
    refine ⟨(z ^ (m + 1))⁻¹, ?_⟩
    simp only [inv_inv]
    calc
      z ^ (m + 1) * z ^ (m + 1) = z ^ ((m + 1) + (m + 1)) :=
        (pow_add z (m + 1) (m + 1)).symm
      _ = z ^ (2 * (m + 1)) := by congr 1; omega
      _ = z ^ (orderOf z + 1) := by congr 1; omega
      _ = z := by rw [pow_add, pow_orderOf_eq_one]; simp
  exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩

private noncomputable def xi91_inducedSquareTerm
    {G : Type*} [Group G] (H : Subgroup G)
    (theta : ClassFunction H) (y : G) : ℂ := by
  classical
  exact if hy : y⁻¹ * y⁻¹ ∈ H then
    theta ⟨y⁻¹ * y⁻¹, hy⟩
  else 0

private noncomputable def xi91_stabilizerSquareTerm
    {G : Type*} [Group G] (H : Subgroup G)
    (theta : ClassFunction H) (y : G) : ℂ := by
  classical
  exact if hy : y ∈ H then
    theta ⟨y⁻¹ * y⁻¹, H.mul_mem (H.inv_mem hy) (H.inv_mem hy)⟩
  else 0

private noncomputable def xi91_involutionTerm
    {G : Type*} [Group G] (c : ℂ) (y : G) : ℂ := by
  classical
  exact if orderOf y = 2 then c else 0

private theorem xi91_classFunctionIndicator_inducedCF
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (theta : ClassFunction H) :
    xi91_classFunctionIndicator G (inducedCF H theta) =
      (Nat.card H : ℂ)⁻¹ * ∑ y : G,
        xi91_inducedSquareTerm H theta y := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  let f : G → ℂ := fun y => xi91_inducedSquareTerm H theta y
  have hconj : ∀ x g : G,
      (if hx : x * (g⁻¹ * g⁻¹) * x⁻¹ ∈ H then
          theta ⟨x * (g⁻¹ * g⁻¹) * x⁻¹, hx⟩
        else 0) = f (MulAut.conj x g) := by
    intro x g
    simp only [f, xi91_inducedSquareTerm, MulAut.conj_apply]
    have heq :
        (x * g * x⁻¹)⁻¹ * (x * g * x⁻¹)⁻¹ =
          x * (g⁻¹ * g⁻¹) * x⁻¹ := by group
    rw [heq]
  have hsumConj : ∀ x : G, ∑ g : G, f (MulAut.conj x g) = ∑ g : G, f g := by
    intro x
    simpa using (Equiv.sum_comp (MulAut.conj x).toEquiv f)
  unfold xi91_classFunctionIndicator inducedCF inducedClassFunction
  simp_rw [hconj]
  rw [← Finset.mul_sum]
  have hswap :
      (∑ g : G, ∑ x : G, f (MulAut.conj x g)) =
        ∑ x : G, ∑ g : G, f (MulAut.conj x g) := by
    exact Finset.sum_comm
  rw [hswap]
  simp_rw [hsumConj]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have hcardG : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  simp only [nsmul_eq_mul, f]
  field_simp [hcardG]

private theorem xi91_sum_stabilizerSquareTerm_of_odd_card
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (hodd : Odd (Nat.card H))
    (theta : ClassFunction H) (hthetaSum : ∑ h : H, theta h = 0) :
    ∑ y : G, xi91_stabilizerSquareTerm H theta y = 0 := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let eH : H ≃ H := Equiv.ofBijective (fun h : H => h⁻¹ * h⁻¹)
    (xi91_invSq_bijective_of_odd_card hodd)
  have hthetaSqSum : ∑ h : H, theta (h⁻¹ * h⁻¹) = 0 := by
    calc
      (∑ h : H, theta (h⁻¹ * h⁻¹)) = ∑ h : H, theta h := by
        simpa [eH] using (Equiv.sum_comp eH theta)
      _ = 0 := hthetaSum
  have hsub := Finset.sum_subtype (p := fun y : G => y ∈ H)
    (F := Fintype.ofFinite H)
    (Finset.univ.filter fun y : G => y ∈ H)
    (by intro y; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (xi91_stabilizerSquareTerm H theta)
  calc
    (∑ y : G, xi91_stabilizerSquareTerm H theta y) =
        ∑ y ∈ Finset.univ.filter fun y : G => y ∈ H,
          xi91_stabilizerSquareTerm H theta y := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hyH : y ∈ H
      · simp only [xi91_stabilizerSquareTerm, dif_pos hyH, if_pos hyH]
      · simp only [xi91_stabilizerSquareTerm, dif_neg hyH, if_neg hyH]
    _ = ∑ h : H, xi91_stabilizerSquareTerm H theta h := hsub
    _ = ∑ h : H, theta (h⁻¹ * h⁻¹) := by
      apply Finset.sum_congr rfl
      intro h _hh
      simp only [xi91_stabilizerSquareTerm, dif_pos h.property]
      congr 1
    _ = 0 := hthetaSqSum

private theorem xi91_sum_involutionTerm
    {G : Type*} [Group G] [Finite G] (c : ℂ) :
    ∑ y : G, xi91_involutionTerm c y =
      (Nat.card {t : G // orderOf t = 2} : ℂ) * c := by
  classical
  let Inv := {t : G // orderOf t = 2}
  let : Fintype Inv := Fintype.ofFinite Inv
  have hsub := Finset.sum_subtype (p := fun y : G => orderOf y = 2)
    (F := inferInstance)
    (Finset.univ.filter fun y : G => orderOf y = 2)
    (by intro y; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (xi91_involutionTerm c)
  calc
    (∑ y : G, xi91_involutionTerm c y) =
        ∑ y ∈ Finset.univ.filter fun y : G => orderOf y = 2,
          xi91_involutionTerm c y := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hyOrder : orderOf y = 2
      · simp only [xi91_involutionTerm, if_pos hyOrder]
      · simp only [xi91_involutionTerm, if_neg hyOrder]
    _ = ∑ t : Inv, xi91_involutionTerm c (t : G) := hsub
    _ = ∑ _t : Inv, c := by
      apply Finset.sum_congr rfl
      intro t _ht
      simp only [xi91_involutionTerm, if_pos t.property]
    _ = (Nat.card Inv : ℂ) * c := by
      rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
      simp [nsmul_eq_mul]

private theorem xi91_irreducible_nonprincipal_sum_eq_zero
    {G : Type*} [Group G] [Finite G]
    (theta : ClassFunction G)
    (hirr : IsIrreducibleCharacterOnGroup theta)
    (hne : theta ≠ principalCharacter G) :
    ∑ g : G, theta g = 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have horth : scalarProduct G theta (principalCharacter G) = 0 :=
    scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne hirr hne
  have hcardG : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have horth' : (Nat.card G : ℂ)⁻¹ * ∑ g : G, theta g = 0 := by
    simpa [scalarProduct, principalCharacter] using horth
  field_simp [hcardG] at horth'
  simpa using horth'

private noncomputable def xi91_frobeniusSchurIndicator
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, rho.character (g⁻¹ * g⁻¹)

private theorem xi91_classFunctionIndicator_representation
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    xi91_classFunctionIndicator G rho.character =
      xi91_frobeniusSchurIndicator rho := rfl

private theorem xi91_frobeniusSchurIndicator_eq_trace
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    xi91_frobeniusSchurIndicator rho =
      LinearMap.trace ℂ (LinearMap.BilinForm ℂ V)
        (((LinearMap.BilinForm.flipHom :
            LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap).comp
          (Representation.averageMap (Representation.linHom rho rho.dual))) := by
  classical
  let rhoh : Representation ℂ G (LinearMap.BilinForm ℂ V) :=
    Representation.linHom rho rho.dual
  let flip : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V :=
    ((LinearMap.BilinForm.flipHom :
      LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap)
  change (Nat.card G : ℂ)⁻¹ * ∑ g : G, rho.character (g⁻¹ * g⁻¹) =
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ V)
      (flip.comp (Representation.averageMap rhoh))
  symm
  calc
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ V)
        (flip.comp (Representation.averageMap rhoh)) =
        ((Nat.card G : ℂ)⁻¹ * ∑ g : G, rho.character (g⁻¹ * g⁻¹)) := by
      have hcomp_smul :
          flip.comp (((Nat.card G : ℂ)⁻¹ : ℂ) • ∑ g : G, rhoh g) =
            (((Nat.card G : ℂ)⁻¹ : ℂ) • ∑ g : G, flip.comp (rhoh g)) := by
        ext x
        simp [LinearMap.comp_apply]
      rw [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum]
      simp [Representation.asAlgebraHom_def]
      rw [← Nat.card_eq_fintype_card]
      rw [hcomp_smul, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro g hg
      exact xi91_representation_trace_flip_linHom_dual_eq_character_inv_mul_inv rho g
    _ = _ := rfl


private noncomputable def xi91_invariantFlip
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    Representation.invariants (Representation.linHom rho rho.dual) →ₗ[ℂ]
      Representation.invariants (Representation.linHom rho rho.dual) := by
  let rhoh : Representation ℂ G (LinearMap.BilinForm ℂ V) :=
    Representation.linHom rho rho.dual
  let flip : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V :=
    ((LinearMap.BilinForm.flipHom :
      LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap)
  exact flip.restrict (by
    intro x hx
    rw [Representation.mem_invariants] at hx ⊢
    intro g
    calc
      rhoh g (flip x) = flip (rhoh g x) := by
        have hcomm := congrArg
          (fun f : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V => f x)
          (xi91_representation_flip_linHom_dual_comm rho g)
        simpa [flip, rhoh] using hcomm.symm
      _ = flip x := by rw [hx g])

private theorem xi91_trace_flip_average_eq_trace_invariantFlip
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ V)
        (((LinearMap.BilinForm.flipHom :
            LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap).comp
          (Representation.averageMap (Representation.linHom rho rho.dual))) =
      LinearMap.trace ℂ
        (Representation.invariants (Representation.linHom rho rho.dual))
        (xi91_invariantFlip rho) := by
  classical
  let rhoh : Representation ℂ G (LinearMap.BilinForm ℂ V) :=
    Representation.linHom rho rho.dual
  let p : Submodule ℂ (LinearMap.BilinForm ℂ V) := Representation.invariants rhoh
  let avg : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V :=
    Representation.averageMap rhoh
  let flip : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V :=
    ((LinearMap.BilinForm.flipHom :
      LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap)
  let : Module.Free ℂ p := Module.Free.of_basis (Module.Basis.ofVectorSpace ℂ p)
  let : Module.Finite ℂ p := Module.Finite.of_basis (Module.Basis.ofVectorSpace ℂ p)
  have havgProj : LinearMap.IsProj p avg := by
    simpa [p, avg, rhoh] using (Representation.isProj_averageMap rhoh)
  let flipP : p →ₗ[ℂ] p := xi91_invariantFlip rho
  let avgToP : LinearMap.BilinForm ℂ V →ₗ[ℂ] p := havgProj.codRestrict
  let inclFlip : p →ₗ[ℂ] LinearMap.BilinForm ℂ V := p.subtype.comp flipP
  have hfactor : flip.comp avg = inclFlip.comp avgToP := by
    ext x
    rfl
  have hcod : avgToP.comp p.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact havgProj.codRestrict_apply_cod x
  change LinearMap.trace ℂ (LinearMap.BilinForm ℂ V) (flip.comp avg) =
    LinearMap.trace ℂ p flipP
  rw [hfactor]
  calc
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ V) (inclFlip.comp avgToP) =
        LinearMap.trace ℂ p (avgToP.comp inclFlip) := by
      simpa [LinearMap.comp_assoc] using
        (LinearMap.trace_comp_comm' (R := ℂ) (M := LinearMap.BilinForm ℂ V)
          (N := p) avgToP inclFlip)
    _ = LinearMap.trace ℂ p ((avgToP.comp p.subtype).comp flipP) := by
      rw [LinearMap.comp_assoc]
    _ = LinearMap.trace ℂ p (LinearMap.id.comp flipP) := by rw [hcod]
    _ = LinearMap.trace ℂ p flipP := by simp


private theorem xi91_invariants_finrank_eq_zero_of_not_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V)
    (hirr : Representation.IsIrreducible rho)
    (hnot : rho.character ≠ conjugateCharacter rho.character) :
    Module.finrank ℂ
      (Representation.invariants (Representation.linHom rho rho.dual)) = 0 := by
  classical
  have hdualirr : Representation.IsIrreducible rho.dual :=
    Section1.representation_dual_irreducible_of rho hirr
  have hhomzero : ∀ f : Representation.IntertwiningMap rho rho.dual, f = 0 := by
    intro f
    let : Representation.IsIrreducible rho := hirr
    let : Representation.IsIrreducible rho.dual := hdualirr
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hbij | hzero
    · let e : rho.Equiv rho.dual := f.ofBijective hbij
      exfalso
      apply hnot
      calc
        rho.character = rho.dual.character := (Representation.char_iso e)
        _ = conjugateCharacter rho.character :=
          (Section1.conjugateCharacter_representationCharacter_eq_dual rho).symm
    · exact hzero
  have hsub : Subsingleton (Representation.IntertwiningMap rho rho.dual) := by
    exact ⟨fun f g => (hhomzero f).trans (hhomzero g).symm⟩
  have hhomfin :
      Module.finrank ℂ (Representation.IntertwiningMap rho rho.dual) = 0 :=
    Module.finrank_zero_of_subsingleton
  calc
    Module.finrank ℂ
        (Representation.invariants (Representation.linHom rho rho.dual)) =
      Module.finrank ℂ (Representation.IntertwiningMap rho rho.dual) := by
        simpa using
          (Representation.invariantsEquivIntertwiningMap
            (ρ := rho) (σ := rho.dual)).finrank_eq
    _ = 0 := hhomfin

private theorem xi91_frobeniusSchurIndicator_eq_zero_of_not_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V)
    (hirr : Representation.IsIrreducible rho)
    (hnot : rho.character ≠ conjugateCharacter rho.character) :
    xi91_frobeniusSchurIndicator rho = 0 := by
  classical
  let p : Submodule ℂ (LinearMap.BilinForm ℂ V) :=
    Representation.invariants (Representation.linHom rho rho.dual)
  have hpfin : Module.finrank ℂ p = 0 := by
    simpa [p] using
      xi91_invariants_finrank_eq_zero_of_not_fixed_conjugate rho hirr hnot
  have hpzero (x : p) : x = 0 :=
    (finrank_zero_iff_forall_zero.mp hpfin) x
  have : Subsingleton p := ⟨fun x y => (hpzero x).trans (hpzero y).symm⟩
  rw [xi91_frobeniusSchurIndicator_eq_trace,
    xi91_trace_flip_average_eq_trace_invariantFlip]
  have hflipzero : xi91_invariantFlip rho = 0 := Subsingleton.elim _ _
  rw [hflipzero]
  simp


private theorem xi91_invariantFlip_involutive
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    Function.Involutive (xi91_invariantFlip rho) := by
  intro x
  apply Subtype.ext
  ext u v
  rfl


private theorem xi91_frobeniusSchurIndicator_sq_eq_one_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V)
    (hirr : Representation.IsIrreducible rho)
    (hfixed : rho.character = conjugateCharacter rho.character) :
    xi91_frobeniusSchurIndicator rho ^ 2 = 1 := by
  classical
  let p : Submodule ℂ (LinearMap.BilinForm ℂ V) :=
    Representation.invariants (Representation.linHom rho rho.dual)
  let flipP : p →ₗ[ℂ] p := xi91_invariantFlip rho
  let : Module.Free ℂ p := Module.Free.of_basis (Module.Basis.ofVectorSpace ℂ p)
  let : Module.Finite ℂ p := Module.Finite.of_basis (Module.Basis.ofVectorSpace ℂ p)
  have hpfin : Module.finrank ℂ p = 1 := by
    simpa [p] using
      xi91_representation_linHom_dual_invariants_finrank_eq_one_of_fixed_conjugate
        rho hirr hfixed
  have hp_nonzero : ∃ x : p, x ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hsub : Subsingleton p := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    have hfinzero : Module.finrank ℂ p = 0 :=
      @Module.finrank_zero_of_subsingleton ℂ p _ _ _ _ hsub
    omega
  rcases hp_nonzero with ⟨x, hx⟩
  have hspan := (finrank_eq_one_iff_of_nonzero' (K := ℂ) (V := p) x hx).mp hpfin
  rcases hspan (flipP x) with ⟨c, hc⟩
  let b : Module.Basis Unit ℂ p := FiniteDimensional.basisSingleton Unit hpfin x hx
  have htrace_eq_c : LinearMap.trace ℂ p flipP = c := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    have hxrepr_ne :
        (Module.basisUnique Unit hpfin).repr x PUnit.unit ≠ 0 := by
      exact mt (Module.basisUnique_repr_eq_zero_iff (ι := Unit) (h := hpfin)
        (v := x) (i := PUnit.unit)).mp hx
    have hrepr :
        (Module.basisUnique Unit hpfin).repr (flipP x) PUnit.unit =
          c * (Module.basisUnique Unit hpfin).repr x PUnit.unit := by
      simpa using (congrArg
        (fun y : p => (Module.basisUnique Unit hpfin).repr y PUnit.unit) hc).symm
    simp [LinearMap.toMatrix_apply, b, FiniteDimensional.basisSingleton_apply, hrepr,
      hxrepr_ne]
  have hcsq : c ^ 2 = 1 := by
    apply smul_left_injective (M := p) ℂ hx
    calc
      (c ^ 2) • x = c • (c • x) := by rw [pow_two, mul_smul]
      _ = c • flipP x := congrArg (fun y : p => c • y) hc
      _ = flipP (c • x) := by simp
      _ = flipP (flipP x) := congrArg flipP hc
      _ = x := xi91_invariantFlip_involutive rho x
      _ = (1 : ℂ) • x := by simp
  rw [xi91_frobeniusSchurIndicator_eq_trace,
    xi91_trace_flip_average_eq_trace_invariantFlip, show xi91_invariantFlip rho = flipP from rfl,
    htrace_eq_c, hcsq]


private theorem xi91_frobeniusSchurIndicator_eq_zero_or_one_or_neg_one
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V)
    (hirr : Representation.IsIrreducible rho) :
    xi91_frobeniusSchurIndicator rho = 0 ∨
      xi91_frobeniusSchurIndicator rho = 1 ∨
        xi91_frobeniusSchurIndicator rho = -1 := by
  by_cases hfixed : rho.character = conjugateCharacter rho.character
  · rcases sq_eq_one_iff.mp
      (xi91_frobeniusSchurIndicator_sq_eq_one_of_fixed_conjugate
        rho hirr hfixed) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl
      (xi91_frobeniusSchurIndicator_eq_zero_of_not_fixed_conjugate
        rho hirr hfixed)

private theorem xi91_frobeniusSchurIndicator_eq_zero_iff_not_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V)
    (hirr : Representation.IsIrreducible rho) :
    xi91_frobeniusSchurIndicator rho = 0 ↔
      rho.character ≠ conjugateCharacter rho.character := by
  constructor
  · intro hzero hfixed
    have hsq := xi91_frobeniusSchurIndicator_sq_eq_one_of_fixed_conjugate
      rho hirr hfixed
    rw [hzero] at hsq
    norm_num at hsq
  · exact xi91_frobeniusSchurIndicator_eq_zero_of_not_fixed_conjugate rho hirr


private theorem xi91_scalarProduct_weightedFamilySum_self
    {G I : Type*} [Group G] [Finite G] [Finite I] [DecidableEq I]
    (w : I → ℂ) (psi : I → ClassFunction G)
    (horth : ∀ i j : I,
      scalarProduct G (psi i) (psi j) = if i = j then 1 else 0) :
    scalarProduct G (weightedFamilySum w psi) (weightedFamilySum w psi) =
      ∑ i : I, w i * star (w i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  rw [scalarProduct_weightedFamilySum_left]
  simp_rw [scalarProduct_weightedFamilySum_right]
  simp [horth]

private theorem xi91_classFunctionIndicator_weightedFamilySum
    {G I : Type*} [Group G] [Finite G] [Finite I]
    (w : I → ℂ) (psi : I → ClassFunction G) :
    xi91_classFunctionIndicator G (weightedFamilySum w psi) =
      ∑ i : I, w i * xi91_classFunctionIndicator G (psi i) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype I := Fintype.ofFinite I
  unfold xi91_classFunctionIndicator weightedFamilySum
  have hswap :
      (∑ g : G, ∑ i : I, w i * psi i (g⁻¹ * g⁻¹)) =
        ∑ i : I, ∑ g : G, w i * psi i (g⁻¹ * g⁻¹) := Finset.sum_comm
  calc
    (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, ∑ i : I, w i * psi i (g⁻¹ * g⁻¹) =
        (Nat.card G : ℂ)⁻¹ *
          ∑ i : I, ∑ g : G, w i * psi i (g⁻¹ * g⁻¹) :=
      congrArg ((Nat.card G : ℂ)⁻¹ * ·) hswap
    _ = ∑ i : I, w i *
        ((Nat.card G : ℂ)⁻¹ * ∑ g : G, psi i (g⁻¹ * g⁻¹)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.mul_sum]
      ring

private theorem xi91_unique_zero_indicator_arithmetic
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → ℕ) (hepos : ∀ i, 0 < e i)
    (nu : I → ℤ)
    (hnu : ∀ i, nu i = 0 ∨ nu i = 1 ∨ nu i = -1)
    (d : ℕ)
    (hnorm : ∑ i : I, (e i : ℤ) ^ 2 = (d : ℤ) + 1)
    (hindicator : ∑ i : I, (e i : ℤ) * nu i = (d : ℤ)) :
    ∃ i0 : I,
      e i0 = 1 ∧ nu i0 = 0 ∧
        ∀ i : I, i ≠ i0 → e i = 1 ∧ nu i = 1 := by
  classical
  let t : I → ℤ := fun i => (e i : ℤ) * ((e i : ℤ) - nu i)
  have htNonneg : ∀ i, 0 ≤ t i := by
    intro i
    rcases hnu i with h0 | h1 | hm1
    · simp [t, h0]
      positivity
    · simp [t, h1]
      have he : (1 : ℤ) ≤ e i := by exact_mod_cast hepos i
      nlinarith
    · simp [t, hm1]
  have htSum : ∑ i : I, t i = 1 := by
    calc
      (∑ i : I, t i) =
          (∑ i : I, (e i : ℤ) ^ 2) -
            ∑ i : I, (e i : ℤ) * nu i := by
              simp only [t, mul_sub, pow_two, Finset.sum_sub_distrib]
      _ = ((d : ℤ) + 1) - d := by rw [hnorm, hindicator]
      _ = 1 := by ring
  let u : I → ℕ := fun i => (t i).toNat
  have huCast : ∀ i, (u i : ℤ) = t i := by
    intro i
    exact Int.toNat_of_nonneg (htNonneg i)
  have huSum : ∑ i : I, u i = 1 := by
    have huSumZ : ∑ i : I, (u i : ℤ) = 1 := by
      calc
        (∑ i : I, (u i : ℤ)) = ∑ i : I, t i := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact huCast i
        _ = 1 := htSum
    exact_mod_cast huSumZ
  have hex : ∃ i : I, u i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have : ∑ i : I, u i = 0 := by simp [hnone]
    omega
  obtain ⟨i0, hi0ne⟩ := hex
  have hi0le : u i0 ≤ ∑ i : I, u i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
  have hi0 : u i0 = 1 := by omega
  have hsumErase : ∑ i ∈ (Finset.univ.erase i0), u i = 0 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset I) u
      (Finset.mem_univ i0)
    rw [hi0, huSum] at hsplit
    omega
  have hother : ∀ i : I, i ≠ i0 → u i = 0 := by
    intro i hine
    have himem : i ∈ (Finset.univ.erase i0) := by simp [hine]
    have hile : u i ≤ ∑ j ∈ (Finset.univ.erase i0), u j :=
      Finset.single_le_sum (f := fun j => u j)
        (fun _ _ => Nat.zero_le (u _)) himem
    omega
  have htI0 : t i0 = 1 := by
    rw [← huCast i0, hi0]
    norm_num
  have hi0data : e i0 = 1 ∧ nu i0 = 0 := by
    rcases hnu i0 with h0 | h1 | hm1
    · constructor
      · simp [t, h0] at htI0
        have he : (1 : ℤ) ≤ e i0 := by exact_mod_cast hepos i0
        nlinarith
      · exact h0
    · simp [t, h1] at htI0
      have he : 0 < e i0 := hepos i0
      have heCases : e i0 = 1 ∨ 2 ≤ e i0 := by omega
      rcases heCases with heOne | heTwo
      · norm_num [heOne] at htI0
      · have heTwoZ : (2 : ℤ) ≤ e i0 := by exact_mod_cast heTwo
        nlinarith
    · simp [t, hm1] at htI0
      have he : (1 : ℤ) ≤ e i0 := by exact_mod_cast hepos i0
      nlinarith
  refine ⟨i0, hi0data.1, hi0data.2, ?_⟩
  intro i hine
  have htI : t i = 0 := by
    rw [← huCast i, hother i hine]
    norm_num
  rcases hnu i with h0 | h1 | hm1
  · simp [t, h0] at htI
    have he : (1 : ℤ) ≤ e i := by exact_mod_cast hepos i
    nlinarith
  · refine ⟨?_, h1⟩
    simp [t, h1] at htI
    rcases htI with heZero | heOne
    · have heposi : 0 < e i := hepos i
      omega
    · have hei : (e i : ℤ) = 1 := sub_eq_zero.mp heOne
      exact_mod_cast hei
  · simp [t, hm1] at htI
    rcases htI with heZero | heNeg
    · have heposi : 0 < e i := hepos i
      omega
    · have he : (1 : ℤ) ≤ e i := by exact_mod_cast hepos i
      omega

private theorem xi91_classFunctionIndicator_eq_zero_or_one_or_neg_one
    {G : Type*} [Group G] [Finite G]
    (psi : ClassFunction G) (hpsi : IsBookIrreducibleCharacter psi) :
    xi91_classFunctionIndicator G psi = 0 ∨
      xi91_classFunctionIndicator G psi = 1 ∨
      xi91_classFunctionIndicator G psi = -1 := by
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      psi hpsi with ⟨V, _hadd, _hmod, _hfd, rho, hchar, hirr⟩
  rw [hchar, xi91_classFunctionIndicator_representation]
  exact xi91_frobeniusSchurIndicator_eq_zero_or_one_or_neg_one rho hirr

private theorem xi91_classFunctionIndicator_eq_zero_iff_not_fixed_conjugate
    {G : Type*} [Group G] [Finite G]
    (psi : ClassFunction G) (hpsi : IsBookIrreducibleCharacter psi) :
    xi91_classFunctionIndicator G psi = 0 ↔
      psi ≠ conjugateCharacter psi := by
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      psi hpsi with ⟨V, _hadd, _hmod, _hfd, rho, hchar, hirr⟩
  rw [hchar, xi91_classFunctionIndicator_representation]
  exact xi91_frobeniusSchurIndicator_eq_zero_iff_not_fixed_conjugate rho hirr

private noncomputable def xi91_indicatorInt
    (G : Type*) [Group G] [Finite G] (psi : ClassFunction G) : ℤ := by
  classical
  exact if xi91_classFunctionIndicator G psi = 0 then 0
    else if xi91_classFunctionIndicator G psi = 1 then 1 else -1

private theorem xi91_indicatorInt_cast
    {G : Type*} [Group G] [Finite G]
    (psi : ClassFunction G) (hpsi : IsBookIrreducibleCharacter psi) :
    (xi91_indicatorInt G psi : ℂ) = xi91_classFunctionIndicator G psi := by
  rcases xi91_classFunctionIndicator_eq_zero_or_one_or_neg_one psi hpsi with
    h0 | h1 | hm1
  · simp [xi91_indicatorInt, h0]
  · simp [xi91_indicatorInt, h1]
  · have hm10 : xi91_classFunctionIndicator G psi ≠ 0 := by
      rw [hm1]
      norm_num
    have hm11 : xi91_classFunctionIndicator G psi ≠ 1 := by
      rw [hm1]
      norm_num
    unfold xi91_indicatorInt
    rw [if_neg hm10, if_neg hm11, hm1]
    norm_num

private theorem xi91_indicatorInt_cases
    {G : Type*} [Group G] [Finite G]
    (psi : ClassFunction G) (hpsi : IsBookIrreducibleCharacter psi) :
    xi91_indicatorInt G psi = 0 ∨
      xi91_indicatorInt G psi = 1 ∨ xi91_indicatorInt G psi = -1 := by
  rcases xi91_classFunctionIndicator_eq_zero_or_one_or_neg_one psi hpsi with
    h0 | h1 | hm1
  · left; simp [xi91_indicatorInt, h0]
  · right; left; simp [xi91_indicatorInt, h1]
  · right; right
    have hm10 : xi91_classFunctionIndicator G psi ≠ 0 := by
      rw [hm1]
      norm_num
    have hm11 : xi91_classFunctionIndicator G psi ≠ 1 := by
      rw [hm1]
      norm_num
    unfold xi91_indicatorInt
    rw [if_neg hm10, if_neg hm11]

private theorem xi91_positive_decomposition_unique_nonreal
    {G I : Type*} [Group G] [Finite G] [Fintype I] [DecidableEq I]
    (Phi : ClassFunction G) (e : I → ℕ) (psi : I → ClassFunction G)
    (hepos : ∀ i, 0 < e i)
    (hpsi : ∀ i, IsBookIrreducibleCharacter (psi i))
    (hpair : Pairwise fun i j : I => psi i ≠ psi j)
    (hdecomp : Phi = weightedFamilySum (fun i => (e i : ℂ)) psi)
    (d : ℕ)
    (hnorm : scalarProduct G Phi Phi = (d + 1 : ℂ))
    (hindicator : xi91_classFunctionIndicator G Phi = (d : ℂ)) :
    ∃ i0 : I,
      e i0 = 1 ∧ psi i0 ≠ conjugateCharacter (psi i0) ∧
        ∀ i : I, i ≠ i0 →
          e i = 1 ∧ psi i = conjugateCharacter (psi i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have horth : ∀ i j : I,
      scalarProduct G (psi i) (psi j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [scalarProduct_irreducibleCharacter_self
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi i) (hpsi i))]
    · rw [if_neg hij]
      exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi i) (hpsi i))
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi j) (hpsi j))
        (hpair hij)
  have hnormSumC : ∑ i : I, ((e i : ℂ) ^ 2) = (d + 1 : ℂ) := by
    calc
      (∑ i : I, ((e i : ℂ) ^ 2)) =
          ∑ i : I, (e i : ℂ) * star (e i : ℂ) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [star_natCast]
            ring
      _ = scalarProduct G (weightedFamilySum (fun i => (e i : ℂ)) psi)
          (weightedFamilySum (fun i => (e i : ℂ)) psi) :=
            (xi91_scalarProduct_weightedFamilySum_self
              (fun i => (e i : ℂ)) psi horth).symm
      _ = scalarProduct G Phi Phi := by rw [← hdecomp]
      _ = (d + 1 : ℂ) := hnorm
  have hnormSumZ : ∑ i : I, (e i : ℤ) ^ 2 = (d : ℤ) + 1 := by
    exact_mod_cast hnormSumC
  let nu : I → ℤ := fun i => xi91_indicatorInt G (psi i)
  have hnuCast : ∀ i, (nu i : ℂ) = xi91_classFunctionIndicator G (psi i) := by
    intro i
    exact xi91_indicatorInt_cast (psi i) (hpsi i)
  have hnuCases : ∀ i, nu i = 0 ∨ nu i = 1 ∨ nu i = -1 := by
    intro i
    exact xi91_indicatorInt_cases (psi i) (hpsi i)
  have hindicatorSumC :
      ∑ i : I, (e i : ℂ) * (nu i : ℂ) = (d : ℂ) := by
    calc
      (∑ i : I, (e i : ℂ) * (nu i : ℂ)) =
          ∑ i : I, (e i : ℂ) *
            xi91_classFunctionIndicator G (psi i) := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [hnuCast i]
      _ = xi91_classFunctionIndicator G
          (weightedFamilySum (fun i => (e i : ℂ)) psi) :=
            (xi91_classFunctionIndicator_weightedFamilySum
              (fun i => (e i : ℂ)) psi).symm
      _ = xi91_classFunctionIndicator G Phi := by rw [← hdecomp]
      _ = (d : ℂ) := hindicator
  have hindicatorSumZ : ∑ i : I, (e i : ℤ) * nu i = (d : ℤ) := by
    exact_mod_cast hindicatorSumC
  obtain ⟨i0, hei0, hnui0, hother⟩ :=
    xi91_unique_zero_indicator_arithmetic
      e hepos nu hnuCases d hnormSumZ hindicatorSumZ
  have hpsi0NotFixed : psi i0 ≠ conjugateCharacter (psi i0) := by
    apply (xi91_classFunctionIndicator_eq_zero_iff_not_fixed_conjugate
      (psi i0) (hpsi i0)).mp
    rw [← hnuCast i0, hnui0]
    norm_num
  refine ⟨i0, hei0, hpsi0NotFixed, ?_⟩
  intro i hine
  have hei := (hother i hine).1
  have hnui := (hother i hine).2
  refine ⟨hei, ?_⟩
  by_contra hnotFixed
  have hzero :=
    (xi91_classFunctionIndicator_eq_zero_iff_not_fixed_conjugate
      (psi i) (hpsi i)).mpr hnotFixed
  have hone : xi91_classFunctionIndicator G (psi i) = 1 := by
    rw [← hnuCast i, hnui]
    norm_num
  rw [hone] at hzero
  norm_num at hzero

set_option backward.isDefEq.respectTransparency false in
/-- A nonidentity element of a Frobenius complement fixes only the principal
irreducible character of the kernel.  This is the Brauer-permutation input
used in XI.6.4--XI.6.5. -/
private theorem xi91_complement_fixes_only_principal_irreducible
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H) [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (d : D) (hd : d ≠ 1)
    (chi : Theory.Character.ConjClassFunction F)
    (hchiIrr : Theory.Character.IsIrreducibleConjCharacter chi)
    (hchiFix :
      Theory.Character.classFunctionConjLinearEquiv F (d : H) chi = chi) :
    chi =
      Theory.Character.characterClassFunction
        (Representation.trivial ℂ F ℂ) := by
  let psi : Theory.Character.ConjClassFunction F :=
    Theory.Character.characterClassFunction
      (Representation.trivial ℂ F ℂ)
  have htrivIrr :
      Representation.IsIrreducible
        (Representation.trivial ℂ F ℂ) := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule,
      isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one
      (K := ℂ) (A := MonoidAlgebra ℂ F)
      (V := (Representation.trivial ℂ F ℂ).asModule)
      (CommSemiring.finrank_self ℂ)
  have hpsiIrr : Theory.Character.IsIrreducibleConjCharacter psi :=
    Theory.Character.isIrreducibleCharacter_characterClassFunction
      (Representation.trivial ℂ F ℂ) htrivIrr
  have hpsiFix :
      Theory.Character.classFunctionConjLinearEquiv F (d : H) psi = psi := by
    rw [Theory.Character.classFunctionConjLinearEquiv_characterClassFunction]
    ext c
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    rfl
  change chi = psi
  by_contra hne
  obtain ⟨x, hxne, hxconj⟩ :=
    Theory.Character.exists_nontrivial_fixed_conjClass_of_two_fixed_irreducible
      F (d : H) hchiIrr hpsiIrr hchiFix hpsiFix hne
  rcases isConj_iff.mp hxconj with ⟨y, hy⟩
  let h : H := (y : H) * (d : H)
  have hhnotF : h ∉ F := by
    intro hhF
    have hdF : (d : H) ∈ F := by
      have := F.mul_mem (F.inv_mem y.property) hhF
      simpa [h, mul_assoc] using this
    have hdBot : (d : H) ∈ (⊥ : Subgroup H) :=
      hFrob.isComplement'.disjoint.le_bot ⟨hdF, d.property⟩
    apply hd
    apply Subtype.ext
    simpa using hdBot
  have hcentD :
      ∀ r : D, r ≠ 1 → Section2.centralizerIn F (r : H) = ⊥ := by
    intro r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using
      ((lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob r hr)
  have hcentH : Section2.centralizerIn F h = ⊥ :=
    Section6.theorem_6_8_frobenius_complement_centralizerIn_eq_bot
      (K := F) (R := D) hFrob.isComplement' hcentD hhnotF
  have hhconj : h * (x : H) * h⁻¹ = (x : H) := by
    simpa [h, Theory.Character.normalSubgroupConjMulEquiv, mul_assoc] using
      congrArg (fun z : F => (z : H)) hy
  have hhcomm : h * (x : H) = (x : H) * h := by
    have := congrArg (fun z : H => z * h) hhconj
    simpa [mul_assoc] using this
  have hxcent : (x : H) ∈ Section2.centralizerIn F h := by
    refine ⟨x.property, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hhcomm.symm
  have hxbot : (x : H) ∈ (⊥ : Subgroup H) := by
    simpa [hcentH] using hxcent
  apply hxne
  apply Subtype.ext
  simpa using hxbot


/-- The nonidentity Frobenius-kernel carrier is a relative TI subset of the
point stabilizer in the ambient Zassenhaus group. -/
private theorem xi91_kernelCarrier_relativeTI
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    let H := MulAction.stabilizer G a
    let K : Set G := (F.map H.subtype : Set G)
    Suzuki.VI.IsTISubsetRelative H K := by
  let H := MulAction.stabilizer G a
  let Fg : Subgroup G := F.map H.subtype
  change Suzuki.VI.IsTISubsetRelative H (Fg : Set G)
  have hFgH : (Fg : Set G) ⊆ H := by
    intro x hx
    rcases hx with ⟨f, hf, rfl⟩
    exact f.property
  have hHnorm : H ≤ Subgroup.normalizer (Fg : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    let hH : H := ⟨h, hh⟩
    constructor
    · intro hx
      rcases hx with ⟨f, hf, hfx⟩
      let cF : F := ⟨hH * f * hH⁻¹,
        hFrob.normal.conj_mem f hf hH⟩
      refine ⟨(cF : H), cF.property, ?_⟩
      change ((cF : H) : G) = h * x * h⁻¹
      simp only [cF, hH]
      rw [← hfx]
      rfl
    · intro hx
      rcases hx with ⟨f, hf, hfx⟩
      let cF : F := ⟨hH⁻¹ * f * hH, by
        simpa using hFrob.normal.conj_mem f hf hH⁻¹⟩
      refine ⟨(cF : H), cF.property, ?_⟩
      have hfx' : ((f : H) : G) = h * x * h⁻¹ := hfx
      calc
        ((cF : H) : G) = h⁻¹ * ((f : H) : G) * h := rfl
        _ = h⁻¹ * (h * x * h⁻¹) * h := by rw [hfx']
        _ = x := by group
  have hKnontrivial : ∃ k : G, k ∈ (Fg : Set G) ∧ k ≠ 1 := by
    obtain ⟨f, hfne⟩ :=
      (Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.kernel_ne_bot)
    refine ⟨((f : H) : G), ?_, ?_⟩
    · exact ⟨f, f.property, rfl⟩
    · intro hf
      apply hfne
      exact Subtype.ext (Subtype.ext hf)
  apply
    (Suzuki.VI.suzuki_ch6_proposition_2_8
      H (Fg : Set G) hFgH hHnorm hKnontrivial).2
  intro g hgH z hz
  rcases hz with ⟨⟨x, hxFg, rfl⟩, hzxFg⟩
  simp only [Set.mem_singleton_iff]
  by_contra hzne
  rcases hxFg with ⟨xf, hxfF, hxfval⟩
  rcases hzxFg with ⟨zf, hzfF, hzfval⟩
  let xF : F := ⟨xf, hxfF⟩
  let zF : F := ⟨zf, hzfF⟩
  have hxFne : xF ≠ 1 := by
    intro hxone
    apply hzne
    have hxvalOne : x = 1 := by
      rw [← hxfval]
      simpa [xF] using congrArg Subtype.val hxone
    simp [hxvalOne]
  have hzFne : zF ≠ 1 := by
    intro hzone
    apply hzne
    calc
      g * x * g⁻¹ = ((zF : H) : G) := hzfval.symm
      _ = 1 := by simpa using congrArg Subtype.val hzone
  have hxfixa : x • a = a := by
    rw [← hxfval]
    exact xf.property
  have hzfval' : ((zF : H) : G) = g * x * g⁻¹ := hzfval
  have hzfixga : ((zF : H) : G) • (g • a) = g • a := by
    calc
      ((zF : H) : G) • (g • a) =
          (g * x * g⁻¹) • (g • a) := by rw [hzfval']
      _ = g • (x • a) := by simp only [mul_smul, inv_smul_smul]
      _ = g • a := by rw [hxfixa]
  have hga : g • a = a :=
    (xi91_frobeniusKernel_uniqueFixedPoint
      htwo a b hab F hFrob zF hzFne (g • a)).mp hzfixga
  exact hgH (MulAction.mem_stabilizer_iff.mpr hga)


@[expose] public noncomputable def xi91_linearCharacterRepresentation
    {G : Type*} [Group G] (chi : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := (chi g : ℂ) • LinearMap.id
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp [mul_smul, mul_comm]

private theorem xi91_linearCharacterRepresentation_character
    {G : Type*} [Group G] (chi : G →* ℂˣ) (g : G) :
    (xi91_linearCharacterRepresentation chi).character g = (chi g : ℂ) := by
  rw [Representation.character]
  simp [xi91_linearCharacterRepresentation]

private theorem xi91_linearCharacterRepresentation_irreducible
    {G : Type*} [Group G] (chi : G →* ℂˣ) :
    Representation.IsIrreducible (xi91_linearCharacterRepresentation chi) := by
  refine { eq_bot_or_eq_top := ?_ }
  intro S
  have hsimple : IsSimpleOrder (Submodule ℂ ℂ) := by infer_instance
  rcases hsimple.eq_bot_or_eq_top S.toSubmodule with hbot | htop
  · left
    have hbot' : S.toSubmodule = (⊥ : Subrepresentation (xi91_linearCharacterRepresentation chi)).toSubmodule :=
      hbot
    exact Subrepresentation.toSubmodule_injective hbot'
  · right
    have htop' : S.toSubmodule = (⊤ : Subrepresentation (xi91_linearCharacterRepresentation chi)).toSubmodule :=
      htop
    exact Subrepresentation.toSubmodule_injective htop'

private theorem xi91_complement_fixes_only_principal_section1
    {H V : Type*} [Group H] [Finite H]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (F D : Subgroup H) [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (d : D) (hd : d ≠ 1)
    (rho : Representation ℂ F V)
    (hirr : Representation.IsIrreducible rho)
    (hfix : conjugateOnNormal F rho.character (d : H) = rho.character) :
    rho.character = principalCharacter F := by
  let chi : Theory.Character.ConjClassFunction F :=
    Theory.Character.characterClassFunction rho
  have hchiIrr : Theory.Character.IsIrreducibleConjCharacter chi :=
    Theory.Character.isIrreducibleCharacter_characterClassFunction rho hirr
  have hmem : (d : H) ∈ inertiaSubgroup F rho.character := by
    exact hfix
  have hfixInv :
      conjugateOnNormal F rho.character (d : H)⁻¹ = rho.character :=
    (inertiaSubgroup F rho.character).inv_mem hmem
  have hchiFix :
      Theory.Character.classFunctionConjLinearEquiv F (d : H) chi = chi := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    have hx := congrFun hfixInv x
    have hchi_apply (y : F) : chi (ConjClasses.mk y) = rho.character y := by
      rfl
    calc
      (Theory.Character.classFunctionConjLinearEquiv F (d : H) chi) (ConjClasses.mk x)
          = chi ((Theory.Character.conjClassesConjPerm F (d : H)).symm (ConjClasses.mk x)) := rfl
      _ = chi (ConjClasses.mk ((Theory.Character.normalSubgroupConjMulEquiv F (d : H)).symm x)) := by
        simp [Theory.Character.conjClassesConjPerm_symm_mk]
      _ = rho.character ((Theory.Character.normalSubgroupConjMulEquiv F (d : H)).symm x) :=
        hchi_apply ((Theory.Character.normalSubgroupConjMulEquiv F (d : H)).symm x)
      _ = rho.character x := by
        simpa [conjugateOnNormal, Theory.Character.normalSubgroupConjMulEquiv, mul_assoc] using hx
      _ = chi (ConjClasses.mk x) := (hchi_apply x).symm
  have htriv := xi91_complement_fixes_only_principal_irreducible
    F D hFrob d hd chi hchiIrr hchiFix
  ext x
  have hx := congrFun htriv (ConjClasses.mk x)
  change rho.character x = principalCharacter F x
  change rho.character x = (1 : ℂ)
  change rho.character x =
    (Representation.trivial ℂ F ℂ).character x at hx
  simpa [Representation.character] using hx

private theorem xi91_linearCharacter_inertia_eq_kernel
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H) [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (chi : F →* ℂˣ) (hchi : chi ≠ 1) :
    inertiaSubgroup F (xi91_linearCharacterRepresentation chi).character = F := by
  let rho := xi91_linearCharacterRepresentation chi
  have hirr : Representation.IsIrreducible rho :=
    xi91_linearCharacterRepresentation_irreducible chi
  have hcharNe : rho.character ≠ principalCharacter F := by
    intro hprincipal
    apply hchi
    apply MonoidHom.ext
    intro f
    apply Units.ext
    have hf := congrFun hprincipal f
    have hfchar : rho.character f = (chi f : ℂ) :=
      xi91_linearCharacterRepresentation_character chi f
    rw [hfchar] at hf
    simpa [principalCharacter] using hf
  apply le_antisymm
  · intro x hx
    obtain ⟨fd, hfd, _huniq⟩ := hFrob.isComplement'.existsUnique x
    have hFleI : F ≤ inertiaSubgroup F rho.character := by
      intro f hf
      change conjugateOnNormal F rho.character f = rho.character
      let fF : F := ⟨f, hf⟩
      ext z
      have hchar_conj := Representation.char_conj (ρ := rho) z (fF : F)
      have h_eq : (fF * z * fF⁻¹ : F) = (⟨(f : H) * (z.1 : H) * (f : H)⁻¹,
        hFrob.normal.conj_mem (z.1 : H) z.2 (f : H)⟩ : F) := by
        apply Subtype.ext
        simp [fF, mul_assoc]
      simpa [conjugateOnNormal, fF, h_eq, mul_assoc] using hchar_conj
    have hfI : (fd.1 : H) ∈ inertiaSubgroup F rho.character :=
      hFleI fd.1.property
    have hdI : (fd.2 : H) ∈ inertiaSubgroup F rho.character := by
      have hdEq : (fd.2 : H) = (fd.1 : H)⁻¹ * x := by
        rw [← hfd]
        simp
      rw [hdEq]
      exact (inertiaSubgroup F rho.character).mul_mem
        ((inertiaSubgroup F rho.character).inv_mem hfI) hx
    by_cases hdOne : fd.2 = 1
    · have hxEq : x = (fd.1 : H) := by
        rw [← hfd, hdOne]
        simp
      rw [hxEq]
      exact fd.1.property
    · have hfix : conjugateOnNormal F rho.character (fd.2 : H) = rho.character :=
        hdI
      exact (hcharNe
        (xi91_complement_fixes_only_principal_section1
          F D hFrob fd.2 hdOne rho hirr hfix)).elim
  · intro f hf
    change conjugateOnNormal F rho.character f = rho.character
    let fF : F := ⟨f, hf⟩
    ext z
    have hchar_conj := Representation.char_conj (ρ := rho) z (fF : F)
    have h_eq : (fF * z * fF⁻¹ : F) = (⟨(f : H) * (z.1 : H) * (f : H)⁻¹,
      hFrob.normal.conj_mem (z.1 : H) z.2 (f : H)⟩ : F) := by
      apply Subtype.ext
      simp [fF, mul_assoc]
    simpa [conjugateOnNormal, fF, h_eq, mul_assoc] using hchar_conj

private theorem xi91_relativeTI_induced_scalarProduct_self
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (K : Set G)
    (hTI : Suzuki.VI.IsTISubsetRelative H K)
    (theta : ClassFunction H)
    (hthetaVirtual : Theory.Character.IsVirtualCharacter theta)
    (hthetaSupport : ∀ h : H, (h : G) ∉ K → theta h = 0) :
    scalarProduct G (inducedCF H theta) (inducedCF H theta) =
      scalarProduct H theta theta +
        (Nat.card H : ℂ)⁻¹ * ((H.index : ℂ) - 1) *
          theta 1 * star (theta 1) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hthetaClass : IsClassFunction theta :=
    isVirtualCharacter_isClassFunction hthetaVirtual
  have hprop := Suzuki.VI.suzuki_ch6_proposition_2_9
    H K hTI theta hthetaVirtual hthetaSupport
  rw [inducedClassFunction_frobenius_general H theta (inducedCF H theta)
    (inducedCF_isClassFunction H theta)]
  have hterm : ∀ h : H,
      theta h * star (inducedCF H theta (h : G)) =
        theta h * star (theta h) +
          if h = 1 then
            ((H.index : ℂ) - 1) * theta 1 * star (theta 1)
          else 0 := by
    intro h
    by_cases hhOne : h = 1
    · subst h
      have hdeg := degree_inducedClassFunction H theta
      change inducedCF H theta 1 = (H.index : ℂ) * theta 1 at hdeg
      have hdeg' : inducedCF H theta ((1 : H) : G) =
          (H.index : ℂ) * theta 1 := by simpa using hdeg
      rw [hdeg']
      simp
      ring
    · by_cases hhK : (h : G) ∈ K
      · have hhOneG : (h : G) ≠ 1 := by
          intro hh
          apply hhOne
          exact Subtype.ext hh
        have happ := hprop.1 (h : G) hhK hhOneG
        have hsub : (⟨(h : G), hTI.1 hhK⟩ : H) = h := by ext; rfl
        rw [happ]
        simp [hhOne, hsub]
      · rw [hthetaSupport h hhK]
        simp [hhOne]
  unfold scalarProduct subgroupRestriction
  have hsum :
      (∑ h : H, theta h * star (inducedCF H theta (h : G))) =
        (∑ h : H, theta h * star (theta h)) +
          ((H.index : ℂ) - 1) * theta 1 * star (theta 1) := by
    calc
      (∑ h : H, theta h * star (inducedCF H theta (h : G))) =
          ∑ h : H, (theta h * star (theta h) +
            if h = 1 then
              ((H.index : ℂ) - 1) * theta 1 * star (theta 1)
            else 0) := by
              apply Finset.sum_congr rfl
              intro h _hh
              exact hterm h
      _ = (∑ h : H, theta h * star (theta h)) +
          ∑ h : H, if h = 1 then
            ((H.index : ℂ) - 1) * theta 1 * star (theta 1)
          else 0 := Finset.sum_add_distrib
      _ = (∑ h : H, theta h * star (theta h)) +
          ((H.index : ℂ) - 1) * theta 1 * star (theta 1) := by simp
  calc
    (Nat.card H : ℂ)⁻¹ *
          ∑ g : H, theta g * star (inducedCF H theta (g : G)) =
        (Nat.card H : ℂ)⁻¹ *
          ((∑ g : H, theta g * star (theta g)) +
            ((H.index : ℂ) - 1) * theta 1 * star (theta 1)) := by
              exact congrArg (fun z : ℂ => (Nat.card H : ℂ)⁻¹ * z) hsum
    _ = (Nat.card H : ℂ)⁻¹ * ∑ g : H, theta g * star (theta g) +
        (Nat.card H : ℂ)⁻¹ * ((H.index : ℂ) - 1) *
          theta 1 * star (theta 1) := by ring

private theorem xi91_induced_linearCharacter_support
    {H : Type*} [Group H] [Finite H]
    (F : Subgroup H) [F.Normal] (chi : F →* ℂˣ) :
    ∀ h : H, h ∉ F →
      inducedCF F (xi91_linearCharacterRepresentation chi).character h = 0 := by
  classical
  intro h hhF
  unfold inducedCF inducedClassFunction
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro x _hx
  split
  next hxF =>
    have hhmem : h ∈ F := by
      have hconj := (inferInstance : F.Normal).conj_mem (x * h * x⁻¹) hxF x⁻¹
      simpa [mul_assoc] using hconj
    exact (hhF hhmem).elim
  next => rfl

private theorem xi91_induced_linearCharacter_degree
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H) [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (chi : F →* ℂˣ) :
    inducedCF F (xi91_linearCharacterRepresentation chi).character 1 =
      (Nat.card D : ℂ) := by
  have hdeg := degree_inducedClassFunction F
    (xi91_linearCharacterRepresentation chi).character
  rw [hFrob.isComplement'.symm.index_eq_card] at hdeg
  simpa [degree, xi91_linearCharacterRepresentation_character] using hdeg

/-- A nontrivial linear character of a Frobenius kernel induces
irreducibly to the kernel-complement group. -/
private theorem xi91_linearCharacter_induced_irreducible
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H) [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (chi : F →* ℂˣ) (hchi : chi ≠ 1) :
    IsIrreducibleCharacterOnGroup
      (inducedCF F (xi91_linearCharacterRepresentation chi).character) := by
  have hirr : Representation.IsIrreducible
      (xi91_linearCharacterRepresentation chi) :=
    xi91_linearCharacterRepresentation_irreducible chi
  have hI : inertiaSubgroup F
      (xi91_linearCharacterRepresentation chi).character = F :=
    xi91_linearCharacter_inertia_eq_kernel F D hFrob chi hchi
  apply proposition_1_5_b_irreducible_rep_orbit_relIndex_canonical F
    (xi91_linearCharacterRepresentation chi) hirr
  rw [hI]
  simp [Subgroup.relIndex]

/-- The induction to the ambient Zassenhaus group of a nontrivial
linear kernel character has squared norm `|D| + 1`. -/
private theorem xi91_linearCharacter_ambient_induced_norm
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (n : ℕ) (hdegree : Fintype.card Omega = n + 1)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFcard : Nat.card F = n)
    (chi : F →* ℂˣ) (hchi : chi ≠ 1) :
    let H := MulAction.stabilizer G a
    let lambda : ClassFunction H :=
      inducedCF F (xi91_linearCharacterRepresentation chi).character
    scalarProduct G (inducedCF H lambda) (inducedCF H lambda) =
      (Nat.card (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) + 1 : ℂ) := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let K : Set G := (F.map H.subtype : Set G)
  let lambda : ClassFunction H :=
    inducedCF F (xi91_linearCharacterRepresentation chi).character
  let : F.Normal := hFrob.normal
  have hlambdaIrr : IsIrreducibleCharacterOnGroup lambda := by
    exact xi91_linearCharacter_induced_irreducible F D hFrob chi hchi
  have hlambdaVirtual : Theory.Character.IsVirtualCharacter lambda :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hlambdaIrr
  have hTI : Suzuki.VI.IsTISubsetRelative H K := by
    simpa [H, K] using xi91_kernelCarrier_relativeTI
      (G := G) (Omega := Omega) htwo a b hab F hFrob
  have hlambdaSupport : ∀ h : H, (h : G) ∉ K → lambda h = 0 := by
    intro h hhK
    apply xi91_induced_linearCharacter_support F chi h
    intro hhF
    apply hhK
    exact ⟨h, hhF, rfl⟩
  have hnorm := xi91_relativeTI_induced_scalarProduct_self
    H K hTI lambda hlambdaVirtual hlambdaSupport
  have hlambdaSelf : scalarProduct H lambda lambda = 1 :=
    scalarProduct_irreducibleCharacter_self hlambdaIrr
  have hlambdaOne : lambda 1 = (Nat.card D : ℂ) := by
    have h := xi91_induced_linearCharacter_degree F D hFrob chi
    simpa [lambda] using h
  have hHindex : H.index = n + 1 := by
    calc
      H.index = Nat.card Omega := by
        let : MulAction.IsPretransitive G Omega :=
          MulAction.isPretransitive_of_is_two_pretransitive
        exact MulAction.index_stabilizer_of_transitive G a
      _ = Fintype.card Omega := Nat.card_eq_fintype_card
      _ = n + 1 := hdegree
  have hHcard : Nat.card H = n * Nat.card D := by
    rw [← hFrob.isComplement'.card_mul_card, hFcard]
  have hnpos : 0 < n := by
    rw [← hFcard]
    exact Nat.card_pos
  rw [hlambdaSelf, hlambdaOne, hHindex, hHcard] at hnorm
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hdne : (Nat.card D : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := D)).ne'
  change scalarProduct G (inducedCF H lambda) (inducedCF H lambda) =
    (Nat.card D + 1 : ℂ)
  rw [hnorm]
  field_simp [hnne, hdne]
  rw [star_natCast]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring


private theorem xi91_inducedSquareTerm_decomposition
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hpointOdd : Odd (Nat.card (MulAction.stabilizer G a)))
    (chi : F →* ℂˣ) :
    let H := MulAction.stabilizer G a
    let lambda : ClassFunction H :=
      inducedCF F (xi91_linearCharacterRepresentation chi).character
    ∀ y : G, xi91_inducedSquareTerm H lambda y =
      xi91_stabilizerSquareTerm H lambda y +
        xi91_involutionTerm (lambda 1) y := by
  classical
  dsimp only
  let H := MulAction.stabilizer G a
  let lambda : ClassFunction H :=
    inducedCF F (xi91_linearCharacterRepresentation chi).character
  let : F.Normal := hFrob.normal
  intro y
  by_cases hyH : y ∈ H
  · have hyOrderOdd : Odd (orderOf y) := by
      have hdiv : orderOf y ∣ Nat.card H := by
        let yH : H := ⟨y, hyH⟩
        simpa [yH] using orderOf_dvd_natCard yH
      exact Odd.of_dvd_nat hpointOdd hdiv
    have hyOrderNe : orderOf y ≠ 2 := by
      intro hy2
      rcases hyOrderOdd with ⟨k, hk⟩
      omega
    have hySqH : y⁻¹ * y⁻¹ ∈ H :=
      H.mul_mem (H.inv_mem hyH) (H.inv_mem hyH)
    unfold xi91_inducedSquareTerm xi91_stabilizerSquareTerm
      xi91_involutionTerm
    rw [dif_pos hySqH, dif_pos hyH, if_neg hyOrderNe, add_zero]
  · by_cases hyOrder : orderOf y = 2
    · have hySq : y⁻¹ * y⁻¹ = 1 := by
        have hpow := pow_orderOf_eq_one y
        rw [hyOrder] at hpow
        have hsq : y * y = 1 := by simpa [pow_two] using hpow
        have hinv := congrArg Inv.inv hsq
        rw [mul_inv_rev, inv_one] at hinv
        exact hinv
      unfold xi91_inducedSquareTerm xi91_stabilizerSquareTerm
        xi91_involutionTerm
      simp [hySq, H, hyH, hyOrder]
      rfl
    · have hzero : xi91_inducedSquareTerm H lambda y = 0 := by
        unfold xi91_inducedSquareTerm
        split
        next hySqH =>
          let ySqH : H := ⟨y⁻¹ * y⁻¹, hySqH⟩
          by_cases hySqOne : ySqH = 1
          · have hySq : y * y = 1 := by
              have hval := congrArg Subtype.val hySqOne
              have hinv := congrArg Inv.inv hval
              simpa [ySqH, mul_inv_rev] using hinv
            have hyne : y ≠ 1 := by
              intro hyone
              apply hyH
              simp [hyone]
            exact (hyOrder (orderOf_eq_prime
              (by simpa [pow_two] using hySq) hyne)).elim
          · apply xi91_induced_linearCharacter_support F chi ySqH
            intro hySqF
            let z : F := ⟨ySqH, hySqF⟩
            have hzNe : z ≠ 1 := by
              intro hz
              apply hySqOne
              apply Subtype.ext
              exact congrArg Subtype.val (congrArg Subtype.val hz)
            have hzFixA : (((z : F) : H) : G) • a = a := z.1.property
            have hzFixYA : (((z : F) : H) : G) • (y • a) = y • a := by
              calc
                (((z : F) : H) : G) • (y • a) =
                    y • ((((z : F) : H) : G) • a) := by
                      simp only [← mul_smul]
                      congr 1
                      change (y⁻¹ * y⁻¹) * y = y * (y⁻¹ * y⁻¹)
                      group
                _ = y • a := by rw [hzFixA]
            have hyFix : y • a = a :=
              (xi91_frobeniusKernel_uniqueFixedPoint
                htwo a b hab F hFrob z hzNe (y • a)).mp hzFixYA
            exact hyH (MulAction.mem_stabilizer_iff.mpr hyFix)
        next => rfl
      unfold xi91_stabilizerSquareTerm xi91_involutionTerm
      rw [dif_neg hyH, if_neg hyOrder, hzero, zero_add]

set_option maxHeartbeats 800000 in
/-- The Frobenius--Schur indicator of the ambient induction of a
nontrivial linear Frobenius-kernel character is `|D|`. -/
private theorem xi91_linearCharacter_ambient_induced_indicator
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (n : ℕ) (hFcard : Nat.card F = n)
    (hpointOdd : Odd (Nat.card (MulAction.stabilizer G a)))
    (hinvolutionCard : Nat.card {t : G // orderOf t = 2} =
      n * Nat.card (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (chi : F →* ℂˣ) (hchi : chi ≠ 1) :
    let H := MulAction.stabilizer G a
    let lambda : ClassFunction H :=
      inducedCF F (xi91_linearCharacterRepresentation chi).character
    xi91_classFunctionIndicator G (inducedCF H lambda) =
      (Nat.card (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) : ℂ) := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let lambda : ClassFunction H :=
    inducedCF F (xi91_linearCharacterRepresentation chi).character
  let : F.Normal := hFrob.normal
  let : Fintype H := Fintype.ofFinite H
  have hlambdaIrr : IsIrreducibleCharacterOnGroup lambda :=
    xi91_linearCharacter_induced_irreducible F D hFrob chi hchi
  have hlambdaOne : lambda 1 = (Nat.card D : ℂ) := by
    have h := xi91_induced_linearCharacter_degree F D hFrob chi
    simpa [lambda] using h
  have hterm : ∀ y : G,
      xi91_inducedSquareTerm H lambda y =
        xi91_stabilizerSquareTerm H lambda y +
          xi91_involutionTerm (lambda 1) y :=
    xi91_inducedSquareTerm_decomposition
      htwo a b hab F hFrob hpointOdd chi
  have hlambdaNePrincipal : lambda ≠ principalCharacter H := by
    intro heq
    have hDcardNe : Nat.card D ≠ 1 := by
      intro hcard
      let : Nontrivial D :=
        (Subgroup.nontrivial_iff_ne_bot (H := D)).2 hFrob.complement_ne_bot
      exact not_subsingleton D (Nat.card_eq_one_iff_unique.mp hcard).1
    have hone := congrFun heq 1
    rw [hlambdaOne] at hone
    have hone' : (Nat.card D : ℂ) = 1 := by
      simpa [principalCharacter] using hone
    apply hDcardNe
    exact_mod_cast hone'
  have hlambdaSum : ∑ h : H, lambda h = 0 :=
    xi91_irreducible_nonprincipal_sum_eq_zero
      lambda hlambdaIrr hlambdaNePrincipal
  have hsumTermH :
      ∑ y : G, xi91_stabilizerSquareTerm H lambda y = 0 :=
    xi91_sum_stabilizerSquareTerm_of_odd_card H hpointOdd lambda hlambdaSum
  have hsumTermInv :
      ∑ y : G, xi91_involutionTerm (lambda 1) y =
        (Nat.card {t : G // orderOf t = 2} : ℂ) * lambda 1 :=
    xi91_sum_involutionTerm (lambda 1)
  have hsumTerm : ∑ y : G, xi91_inducedSquareTerm H lambda y =
      (n * Nat.card D : ℂ) * Nat.card D := by
    calc
      (∑ y : G, xi91_inducedSquareTerm H lambda y) =
          ∑ y : G, (xi91_stabilizerSquareTerm H lambda y +
            xi91_involutionTerm (lambda 1) y) := by
            apply Finset.sum_congr rfl
            intro y _hy
            exact hterm y
      _ = (∑ y : G, xi91_stabilizerSquareTerm H lambda y) +
          ∑ y : G, xi91_involutionTerm (lambda 1) y :=
        Finset.sum_add_distrib
      _ = (Nat.card {t : G // orderOf t = 2} : ℂ) * lambda 1 := by
        rw [hsumTermH, hsumTermInv, zero_add]
      _ = (n * Nat.card D : ℂ) * Nat.card D := by
        rw [hinvolutionCard, hlambdaOne]
        simp only [Nat.cast_mul]
        rfl
  have hHcard : Nat.card H = n * Nat.card D := by
    rw [← hFrob.isComplement'.card_mul_card, hFcard]
  change xi91_classFunctionIndicator G (inducedCF H lambda) =
    (Nat.card D : ℂ)
  rw [xi91_classFunctionIndicator_inducedCF H lambda, hsumTerm, hHcard]
  have hnpos : 0 < n := by
    rw [← hFcard]
    exact Nat.card_pos
  have hdpos : 0 < Nat.card D := Nat.card_pos
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hdne : (Nat.card D : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  rw [Nat.cast_mul]
  field_simp [hnne, hdne]

/-- XI.9.2(d): a nonidentity element of the point-stabilizer
Frobenius kernel is not a product of two ambient involutions. -/
private theorem xi91_frobeniusKernel_nontrivial_not_product_involutions
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hinvolutionFree :
      ∀ t : G, orderOf t = 2 → ∀ x : Omega, t • x ≠ x)
    (z : F) (hzne : z ≠ 1) :
    ¬ ∃ t₁ t₂ : G,
      orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧
        t₁ * t₂ = (((z : MulAction.stabilizer G a) : G)) := by
  rintro ⟨t₁, t₂, ht₁, ht₂, hprod⟩
  have ht₁sq : t₁ ^ 2 = 1 := by
    rw [← ht₁]
    exact pow_orderOf_eq_one t₁
  have ht₂sq : t₂ ^ 2 = 1 := by
    rw [← ht₂]
    exact pow_orderOf_eq_one t₂
  have ht₁inv : t₁⁻¹ = t₁ := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using ht₁sq
  have ht₂inv : t₂⁻¹ = t₂ := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using ht₂sq
  let zg : G := ((z : MulAction.stabilizer G a) : G)
  have hconj : t₁ * zg * t₁⁻¹ = zg⁻¹ := by
    dsimp [zg]
    rw [← hprod]
    rw [mul_inv_rev, ht₁inv, ht₂inv]
    have ht₁mul : t₁ * t₁ = 1 := by simpa [pow_two] using ht₁sq
    simp [← mul_assoc, ht₁mul]
  have hrel : zg * t₁ = t₁ * zg⁻¹ := by
    calc
      zg * t₁ = t₁ * (t₁ * zg * t₁⁻¹) := by
        rw [ht₁inv]
        have ht₁mul : t₁ * t₁ = 1 := by simpa [pow_two] using ht₁sq
        simp [← mul_assoc, ht₁mul]
      _ = t₁ * zg⁻¹ := by rw [hconj]
  have hzfix : zg • a = a := (z : MulAction.stabilizer G a).property
  have hzinvfix : zg⁻¹ • a = a := by
    calc
      zg⁻¹ • a = zg⁻¹ • (zg • a) := by rw [hzfix]
      _ = a := inv_smul_smul zg a
  have hfix_t₁a : zg • (t₁ • a) = t₁ • a := by
    calc
      zg • (t₁ • a) = (zg * t₁) • a := (mul_smul zg t₁ a).symm
      _ = (t₁ * zg⁻¹) • a := by rw [hrel]
      _ = t₁ • (zg⁻¹ • a) := mul_smul t₁ zg⁻¹ a
      _ = t₁ • a := by rw [hzinvfix]
  have ht₁fix : t₁ • a = a :=
    (xi91_frobeniusKernel_uniqueFixedPoint
      htwo a b hab F hFrob z hzne (t₁ • a)).mp hfix_t₁a
  exact hinvolutionFree t₁ ht₁ a ht₁fix

/-- XI.9.2(e), upper bound: distinct involutions occupy distinct
left cosets of the Frobenius kernel, and none of those cosets lies in the
point stabilizer. -/
private theorem xi91_involutions_card_le_kernel_mul_complement
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hinvolutionFree :
      ∀ t : G, orderOf t = 2 → ∀ x : Omega, t • x ≠ x)
    (hnoProd :
      ∀ z : F, z ≠ 1 →
        ¬ ∃ t₁ t₂ : G,
          orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧
            t₁ * t₂ = (((z : MulAction.stabilizer G a) : G))) :
    Nat.card {t : G // orderOf t = 2} ≤
      Nat.card F * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Fg : Subgroup G := F.map H.subtype
  let Inv := {t : G // orderOf t = 2}
  have hFgH : Fg ≤ H := by
    intro x hx
    rcases hx with ⟨f, hf, rfl⟩
    exact f.property
  let qInv : Inv → G ⧸ Fg := fun t => QuotientGroup.mk t.1
  have hqInv : Function.Injective qInv := by
    intro t₁ t₂ heq
    have hrel : t₁.1⁻¹ * t₂.1 ∈ Fg := QuotientGroup.eq.mp heq
    rcases hrel with ⟨f, hf, hfeq⟩
    let z : F := ⟨f, hf⟩
    have ht₁sq : t₁.1 ^ 2 = 1 := by
      simpa only [t₁.property] using pow_orderOf_eq_one t₁.1
    have ht₁inv : t₁.1⁻¹ = t₁.1 := by
      apply inv_eq_of_mul_eq_one_right
      simpa [pow_two] using ht₁sq
    have hprod : t₁.1 * t₂.1 = (((z : H) : G)) := by
      rw [← ht₁inv]
      exact hfeq.symm
    by_cases hz : z = 1
    · apply Subtype.ext
      have hprodOne : t₁.1 * t₂.1 = 1 := by simpa [hz] using hprod
      have ht₂eq : t₂.1 = t₁.1⁻¹ := eq_inv_of_mul_eq_one_right hprodOne
      exact (ht₂eq.trans ht₁inv).symm
    · exact (hnoProd z hz ⟨t₁.1, t₂.1, t₁.property, t₂.property, hprod⟩).elim
  let qH : H ⧸ F → G ⧸ Fg :=
    Quotient.map' H.subtype (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      exact ⟨x⁻¹ * y, hxy, rfl⟩)
  have hqH : Function.Injective qH := by
    refine Quotient.ind₂' ?_
    intro x y heq
    apply QuotientGroup.eq.mpr
    have hrel : (x : G)⁻¹ * (y : G) ∈ Fg := QuotientGroup.eq.mp heq
    rcases hrel with ⟨f, hf, hfeq⟩
    have hfeqH : f = x⁻¹ * y := H.subtype_injective hfeq
    rw [← hfeqH]
    exact hf
  have hcross : ∀ t : Inv, ∀ q : H ⧸ F, qInv t ≠ qH q := by
    intro t
    refine Quotient.ind' ?_
    intro h heq
    have hrel : t.1⁻¹ * (h : G) ∈ Fg := QuotientGroup.eq.mp heq
    have hrelH : t.1⁻¹ * (h : G) ∈ H := hFgH hrel
    have htinvH : t.1⁻¹ ∈ H := by
      have := H.mul_mem hrelH (H.inv_mem h.property)
      simpa [mul_assoc] using this
    have htH : t.1 ∈ H := by
      have := H.inv_mem htinvH
      simpa using this
    exact hinvolutionFree t.1 t.property a htH
  let e : Sum Inv (H ⧸ F) → G ⧸ Fg
    | Sum.inl t => qInv t
    | Sum.inr q => qH q
  have he : Function.Injective e := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (hqInv hxy)
        | inr y => exact (hcross x y hxy).elim
    | inr x =>
        cases y with
        | inl y => exact (hcross y x hxy.symm).elim
        | inr y => exact congrArg Sum.inr (hqH hxy)
  have hcard := Nat.card_le_card_of_injective e he
  have hHindex : H.index = Fintype.card Omega := by
    let : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    let : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    calc
      H.index = Nat.card Omega := MulAction.index_stabilizer_of_transitive G a
      _ = Fintype.card Omega := Nat.card_eq_fintype_card
  have hFindex : F.index = Nat.card D := by
    simpa [D] using hFrob.isComplement'.symm.index_eq_card
  have hFgindex : Fg.index = Nat.card D * Fintype.card Omega := by
    calc
      Fg.index = F.index * H.index := by
        simpa [Fg] using Subgroup.index_map_subtype F
      _ = Nat.card D * Fintype.card Omega := by rw [hFindex, hHindex]
  have hOmega : Fintype.card Omega = Nat.card F + 1 :=
    (xi91_action_parameters_core htwo a b hab F hFrob).1
  change Nat.card Inv ≤ Nat.card F * Nat.card D
  rw [Nat.card_sum, show Nat.card (H ⧸ F) = F.index from rfl,
    show Nat.card (G ⧸ Fg) = Fg.index from rfl, hFindex, hFgindex, hOmega] at hcard
  rw [Nat.mul_add, Nat.mul_one] at hcard
  have hcomm : Nat.card D * Nat.card F = Nat.card F * Nat.card D :=
    Nat.mul_comm _ _
  rw [hcomm] at hcard
  omega

/-- XI.9.2(e), lower bound: the centralizer of a fixed-point-free
involution acts freely, so its conjugacy class has at least `|F| |D|`
elements. -/
private theorem xi91_involution_class_card_ge_kernel_mul_complement
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (s : G) (_hsfree : ∀ x : Omega, s • x ≠ x)
    (hcentralizerFree :
      ∀ c : Subgroup.centralizer ({s} : Set G), c ≠ 1 →
        ∀ x : Omega, (c : G) • x = x → False) :
    Nat.card F * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ≤
      Nat.card (ConjClasses.mk s).carrier := by
  classical
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let C := Subgroup.centralizer ({s} : Set G)
  have hCdiv : Nat.card C ∣ Fintype.card Omega := by
    simpa [Nat.card_eq_fintype_card] using
      xi91_card_actor_dvd_of_fixedPointFree
        (A := C) (Omega := Omega) (by
          intro c hc x hfix
          exact hcentralizerFree c hc x hfix)
  obtain ⟨u, hu⟩ := hCdiv
  let : Nonempty Omega := ⟨a⟩
  have hOmegaPos : 0 < Fintype.card Omega := Fintype.card_pos
  have huPos : 0 < u := by
    by_contra hu0
    have huEq : u = 0 := Nat.eq_zero_of_not_pos hu0
    rw [huEq, mul_zero] at hu
    omega
  have hGcard : Nat.card G = Fintype.card Omega * Nat.card F * Nat.card D := by
    simpa [D] using (xi91_action_parameters_core htwo a b hab F hFrob).2.2.1
  have hclassMul :
      Nat.card (ConjClasses.mk s).carrier * Nat.card C = Nat.card G := by
    simpa [C] using xi91_class_card_mul_centralizer_card s
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hclassEq :
      Nat.card (ConjClasses.mk s).carrier = u * Nat.card F * Nat.card D := by
    apply Nat.eq_of_mul_eq_mul_right hCpos
    calc
      Nat.card (ConjClasses.mk s).carrier * Nat.card C = Nat.card G := hclassMul
      _ = Fintype.card Omega * Nat.card F * Nat.card D := hGcard
      _ = (Nat.card C * u) * Nat.card F * Nat.card D := by rw [hu]
      _ = (u * Nat.card F * Nat.card D) * Nat.card C := by ring
  rw [hclassEq]
  nlinarith

/-- Complex conjugation commutes with induction; the normality assumption on
the older Section 1 wrapper is not needed for the character-sum formula. -/
private theorem xi91_conjugateCharacter_inducedCF
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H]
    (theta : ClassFunction H) :
    conjugateCharacter (inducedCF H theta) =
      inducedCF H (conjugateCharacter theta) := by
  classical
  funext g
  unfold conjugateCharacter inducedCF inducedClassFunction
  calc
    star ((Nat.card H : ℂ)⁻¹ *
        ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then
          theta ⟨x * g * x⁻¹, hx⟩ else 0)) =
      (Nat.card H : ℂ)⁻¹ *
        star (∑ x : G, (if hx : x * g * x⁻¹ ∈ H then
          theta ⟨x * g * x⁻¹, hx⟩ else 0)) := by simp
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G, star (if hx : x * g * x⁻¹ ∈ H then
          theta ⟨x * g * x⁻¹, hx⟩ else 0) := by rw [star_sum]
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then
          conjugateCharacter theta ⟨x * g * x⁻¹, hx⟩ else 0) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hmem : x * g * x⁻¹ ∈ H
      · simp [hmem]
        rfl
      · simp [hmem]

set_option maxHeartbeats 800000 in
/-- The class-sum test function used in XI.9.4(h).  Its coefficient at an
irreducible character `chi` is `chi(s)^2 / chi(1)`, and it vanishes at every
element which is not a product of two involutions. -/
private theorem xi91_exists_involution_classSumTest
    {G : Type u} [Group G] [Finite G]
    (s : G) (hsorder : orderOf s = 2) :
    ∃ omega : ClassFunction G,
      IsClassFunction omega ∧
      (∀ chi : ClassFunction G,
        IsIrreducibleCharacterOnGroup chi →
          scalarProduct G chi omega = chi s ^ 2 / chi 1) ∧
      ∀ mu : ClassFunction G,
        (∀ g : G, mu g ≠ 0 →
          ¬ ∃ t₁ t₂ : G,
            orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧ t₁ * t₂ = g) →
        scalarProduct G mu omega = 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, xi, hxi, _basis, _hbasis⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  let chi : ι → ClassFunction G := fun j => ofConjClassFunction (xi j)
  let Cs : ConjClasses G := ConjClasses.mk s
  let C1 : ConjClasses G := ConjClasses.mk (1 : G)
  let a : ι → ℂ := fun j => xi j Cs * xi j Cs / xi j C1
  let omega : ClassFunction G :=
    weightedFamilySum (fun j => star (a j)) chi
  have hchiClass : ∀ j, IsClassFunction (chi j) := by
    intro j
    exact ofConjClassFunction_isClassFunction (xi j)
  have homegaClass : IsClassFunction omega := by
    intro x g
    unfold omega weightedFamilySum
    refine Finset.sum_congr rfl ?_
    intro j _hj
    simp [hchiClass j x g]
  have homegaZero : ∀ g : G,
      (¬ ∃ t₁ t₂ : G,
        orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧ t₁ * t₂ = g) →
      omega g = 0 := by
    intro g hnoProd
    let PairType :=
      {p : Cs.carrier × Cs.carrier // p.1.1 * p.2.1 = g}
    have hPairEmpty : IsEmpty PairType := by
      refine ⟨?_⟩
      intro p
      have hp1Order : orderOf p.1.1.1 = 2 := by
        have hmk := ConjClasses.mem_carrier_iff_mk_eq.mp p.1.1.2
        rcases ConjClasses.mk_eq_mk_iff_isConj.mp hmk with ⟨c, hc⟩
        exact hc.orderOf_eq.trans hsorder
      have hp2Order : orderOf p.1.2.1 = 2 := by
        have hmk := ConjClasses.mem_carrier_iff_mk_eq.mp p.1.2.2
        rcases ConjClasses.mk_eq_mk_iff_isConj.mp hmk with ⟨c, hc⟩
        exact hc.orderOf_eq.trans hsorder
      exact hnoProd ⟨p.1.1.1, p.1.2.1, hp1Order, hp2Order, p.2⟩
    have hcount : Nat.card PairType = 0 :=
      (Nat.card_eq_zero).2 (Or.inl hPairEmpty)
    have hformula := Suzuki.VI.suzuki_ch6_formula_1_15 xi hxi Cs Cs
      (ConjClasses.mk g) g
      ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
    have hCsNonempty : Nonempty Cs.carrier :=
      ⟨⟨s, (ConjClasses.mem_carrier_iff_mk_eq).2 (by simp [Cs])⟩⟩
    let : Nonempty Cs.carrier := hCsNonempty
    have hCsCard : (Nat.card Cs.carrier : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := Cs.carrier)).ne'
    have hGCard : (Nat.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := G)).ne'
    have hfactor :
        (Nat.card Cs.carrier : ℂ) * (Nat.card Cs.carrier : ℂ) /
            (Nat.card G : ℂ) ≠ 0 :=
      div_ne_zero (mul_ne_zero hCsCard hCsCard) hGCard
    have hcharSum :
        (∑ j : ι,
          xi j Cs * xi j Cs * star (xi j (ConjClasses.mk g)) /
            xi j C1) = 0 := by
      have hzeroProduct :
          ((Nat.card Cs.carrier : ℂ) * (Nat.card Cs.carrier : ℂ) /
              (Nat.card G : ℂ)) *
            (∑ j : ι,
              xi j Cs * xi j Cs * star (xi j (ConjClasses.mk g)) /
                xi j C1) = 0 := by
        simpa [PairType, hcount, C1] using hformula.symm
      exact (mul_eq_zero.mp hzeroProduct).resolve_left hfactor
    apply star_eq_zero.mp
    calc
      star (omega g) =
          ∑ j : ι,
            xi j Cs * xi j Cs * star (xi j (ConjClasses.mk g)) /
              xi j C1 := by
        simp [omega, weightedFamilySum, a, chi, mul_assoc]
        rw [show @Finset.univ ι (Fintype.ofFinite ι) =
          @Finset.univ ι hι by ext; simp]
        apply Finset.sum_congr rfl
        intro j _hj
        change xi j Cs * xi j Cs / xi j C1 *
            star (xi j (ConjClasses.mk g)) =
          xi j Cs * (xi j Cs * star (xi j (ConjClasses.mk g))) /
            xi j C1
        ring
      _ = 0 := hcharSum
  have hchiOrth : ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0 := by
    intro i j
    calc
      scalarProduct G (chi i) (chi j) =
          Theory.Character.classFunctionInner (xi i) (xi j) := by
        symm
        simpa [chi, toConjClassFunction_ofConjClassFunction] using
          (classFunctionInner_toConjClassFunction
            (chi i) (chi j) (hchiClass i) (hchiClass j))
      _ = if i = j then 1 else 0 :=
        representation_completeFamily_orthonormal hxi i j
  have hspChiBasis : ∀ j : ι,
      scalarProduct G (chi j) omega = a j := by
    intro j
    unfold omega
    rw [scalarProduct_weightedFamilySum_right]
    simp [hchiOrth, a]
  have hchiIndex : ∀ theta : ClassFunction G,
      IsIrreducibleCharacterOnGroup theta → ∃ j : ι, chi j = theta := by
    intro theta htheta
    have hthetaClass : IsClassFunction theta :=
      isCharacter_isClassFunction theta
        (isCharacter_of_isIrreducibleCharacterOnGroup htheta)
    have hirr :=
      toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        hthetaClass htheta
    rcases hxi.2.1 (toConjClassFunction theta hthetaClass) hirr with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    ext g
    have hg := congrFun hj (ConjClasses.mk g)
    simpa [chi, toConjClassFunction_apply, ofConjClassFunction] using hg
  have hspIrreducible : ∀ theta : ClassFunction G,
      IsIrreducibleCharacterOnGroup theta →
        scalarProduct G theta omega = theta s ^ 2 / theta 1 := by
    intro theta htheta
    obtain ⟨j, hj⟩ := hchiIndex theta htheta
    have hjS : xi j Cs = theta s := by
      change chi j s = theta s
      rw [hj]
    have hjOne : xi j C1 = theta 1 := by
      change chi j 1 = theta 1
      rw [hj]
    calc
      scalarProduct G theta omega = scalarProduct G (chi j) omega := by rw [hj]
      _ = a j := hspChiBasis j
      _ = theta s ^ 2 / theta 1 := by simp [a, hjS, hjOne, pow_two]
  refine ⟨omega, homegaClass, hspIrreducible, ?_⟩
  intro mu hsupport
  unfold scalarProduct
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro g _hg
  by_cases hmu : mu g = 0
  · simp [hmu]
  · rw [homegaZero g (hsupport g hmu)]
    simp

private theorem xi91_principalCharacter_isBookIrreducible
    {G : Type u} [Group G] [Finite G] :
    IsBookIrreducibleCharacter (principalCharacter G) := by
  constructor
  · refine ⟨ULift.{u} ℂ, inferInstance, inferInstance, inferInstance,
      uliftRepresentation (G := G) (V := ℂ)
        (Representation.trivial ℂ G ℂ), ?_⟩
    ext g
    rw [uliftRepresentation_character]
    simp [principalCharacter, Representation.character]
  · simp [IsIrreducibleCharacter, scalarProduct, principalCharacter]

/-- A character of norm two containing the principal character once is the
sum of the principal character and one distinct irreducible character. -/
private theorem xi91_norm_two_principal_split
    {G : Type u} [Group G] [Finite G]
    (Pi : ClassFunction G)
    (hPiChar : IsCharacter Pi)
    (hPiNorm : scalarProduct G Pi Pi = 2)
    (hPiPrincipal : scalarProduct G Pi (principalCharacter G) = 1) :
    ∃ alpha : ClassFunction G,
      IsBookIrreducibleCharacter alpha ∧
      alpha ≠ principalCharacter G ∧
      Pi = principalCharacter G + alpha := by
  classical
  have hPiNe : Pi ≠ 0 := by
    intro hzero
    rw [hzero] at hPiNorm
    simp [scalarProduct] at hPiNorm
  obtain ⟨J, hJFintype, hJDecidable, m, theta, _jBase,
      hmpos, htheta, hpair, hdecomp⟩ :=
    exists_positive_irreducible_decomposition_of_character Pi hPiChar hPiNe
  let : Fintype J := hJFintype
  let : DecidableEq J := hJDecidable
  have hprincipalBook :
      IsBookIrreducibleCharacter (principalCharacter G) := by
    exact xi91_principalCharacter_isBookIrreducible
  have hthetaOrth : ∀ i j : J,
      scalarProduct G (theta i) (theta j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [scalarProduct_irreducibleCharacter_self
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (theta i) (htheta i))]
    · rw [if_neg hij]
      exact scalarProduct_isBookIrreducible_ne
        (theta i) (theta j) (htheta i) (htheta j) (hpair hij)
  have hnormSumC : ∑ i : J, ((m i : ℂ) ^ 2) = 2 := by
    calc
      (∑ i : J, ((m i : ℂ) ^ 2)) =
          ∑ i : J, (m i : ℂ) * star (m i : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [star_natCast]
        ring
      _ = scalarProduct G
          (weightedFamilySum (fun i => (m i : ℂ)) theta)
          (weightedFamilySum (fun i => (m i : ℂ)) theta) :=
        by
        have hself := (xi91_scalarProduct_weightedFamilySum_self
          (fun i => (m i : ℂ)) theta hthetaOrth).symm
        rw [show @Finset.univ J (Fintype.ofFinite J) =
          @Finset.univ J hJFintype by ext; simp] at hself
        exact hself
      _ = scalarProduct G Pi Pi := by rw [← hdecomp]
      _ = 2 := hPiNorm
  have hnormSum : ∑ i : J, m i ^ 2 = 2 := by
    exact_mod_cast hnormSumC
  have hthetaPrincipal : ∀ i : J,
      scalarProduct G (theta i) (principalCharacter G) =
        if theta i = principalCharacter G then 1 else 0 := by
    intro i
    by_cases hi : theta i = principalCharacter G
    · rw [if_pos hi, hi]
      exact scalarProduct_irreducibleCharacter_self
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (principalCharacter G) hprincipalBook)
    · rw [if_neg hi]
      exact scalarProduct_isBookIrreducible_ne
        (theta i) (principalCharacter G) (htheta i) hprincipalBook hi
  let P : Finset J :=
    Finset.univ.filter (fun i => theta i = principalCharacter G)
  have hprincipalSumC : ∑ i ∈ P, (m i : ℂ) = 1 := by
    calc
      (∑ i ∈ P, (m i : ℂ)) =
          ∑ i : J, (m i : ℂ) *
            scalarProduct G (theta i) (principalCharacter G) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hthetaPrincipal i]
        by_cases h : theta i = principalCharacter G <;> simp [h]
      _ = scalarProduct G
          (weightedFamilySum (fun i => (m i : ℂ)) theta)
          (principalCharacter G) := by
        have hsum := scalarProduct_weightedFamilySum_left
          (fun i => (m i : ℂ)) theta (principalCharacter G)
        rw [show @Finset.univ J (Fintype.ofFinite J) =
          @Finset.univ J hJFintype by ext; simp] at hsum
        exact hsum.symm
      _ = scalarProduct G Pi (principalCharacter G) := by rw [← hdecomp]
      _ = 1 := hPiPrincipal
  have hprincipalSum : ∑ i ∈ P, m i = 1 := by
    exact_mod_cast hprincipalSumC
  have hPnonempty : P.Nonempty := by
    by_contra hPempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hPempty] at hprincipalSum
    simp at hprincipalSum
  obtain ⟨ip, hip⟩ := hPnonempty
  have hPsubset : P ⊆ {ip} := by
    intro j hj
    have hjPrincipal : theta j = principalCharacter G :=
      (Finset.mem_filter.mp hj).2
    have hipPrincipal : theta ip = principalCharacter G :=
      (Finset.mem_filter.mp hip).2
    simp only [Finset.mem_singleton]
    by_contra hjip
    exact hpair hjip (hjPrincipal.trans hipPrincipal.symm)
  have hPeq : P = {ip} := by
    apply Finset.Subset.antisymm hPsubset
    simpa using hip
  have hmip : m ip = 1 := by
    simpa [hPeq] using hprincipalSum
  have hthetaIp : theta ip = principalCharacter G :=
    (Finset.mem_filter.mp hip).2
  let R : Finset J := Finset.univ.erase ip
  have hsumR : ∑ i ∈ R, m i ^ 2 = 1 := by
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset J)) (f := fun i => m i ^ 2)
      (Finset.mem_univ ip)
    change (∑ i ∈ R, m i ^ 2) + m ip ^ 2 =
      ∑ i : J, m i ^ 2 at hsplit
    rw [hmip, hnormSum] at hsplit
    omega
  have hRnonempty : R.Nonempty := by
    by_contra hRempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hRempty] at hsumR
    simp at hsumR
  have hRcardLe : R.card ≤ 1 := by
    calc
      R.card = ∑ _i ∈ R, 1 := by simp
      _ ≤ ∑ i ∈ R, m i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        have hmi : 1 ≤ m i := hmpos i
        nlinarith
      _ = 1 := hsumR
  have hRcard : R.card = 1 := by
    have hpos : 0 < R.card := Finset.card_pos.mpr hRnonempty
    omega
  obtain ⟨ia, hReq⟩ := Finset.card_eq_one.mp hRcard
  have hiaR : ia ∈ R := by simp [hReq]
  have hiaNe : ia ≠ ip := (Finset.mem_erase.mp hiaR).1
  have hmia : m ia = 1 := by
    have hsumIa : m ia ^ 2 = 1 := by simpa [hReq] using hsumR
    have hmiaPos := hmpos ia
    nlinarith
  have huniv : (Finset.univ : Finset J) = {ip, ia} := by
    have hins := Finset.insert_erase (Finset.mem_univ ip)
    change Finset.univ.erase ip = {ia} at hReq
    rw [hReq] at hins
    exact hins.symm
  have hunivOfFinite : @Finset.univ J (Fintype.ofFinite J) = {ip, ia} := by
    rw [show @Finset.univ J (Fintype.ofFinite J) =
      @Finset.univ J hJFintype by ext; simp]
    exact huniv
  refine ⟨theta ia, htheta ia, ?_, ?_⟩
  · intro hiaPrincipal
    exact hpair hiaNe (hiaPrincipal.trans hthetaIp.symm)
  · rw [hdecomp]
    ext g
    unfold weightedFamilySum
    rw [hunivOfFinite]
    have hip_not_mem_ia : ip ∉ ({ia} : Finset J) := by
      simpa using Ne.symm hiaNe
    calc
      ∑ x ∈ ({ip, ia} : Finset J), (m x : ℂ) * theta x g
          = ((m ip : ℂ) * theta ip g) + ((m ia : ℂ) * theta ia g) := by
        simp [Finset.sum_insert hip_not_mem_ia, Finset.sum_singleton]
      _ = ((1 : ℂ) * ((principalCharacter G) g)) + ((1 : ℂ) * theta ia g) := by
        simp [hmip, hmia, hthetaIp]
      _ = (1 : ℂ) * (1 : ℂ) + theta ia g := by simp
      _ = 1 + theta ia g := by ring

/-- Locate an irreducible constituent of multiplicity one in a positive
decomposition from its scalar product. -/
private theorem xi91_decomposition_index_of_scalar_one
    {G I : Type*} [Group G] [Finite G] [Fintype I] [DecidableEq I]
    (Phi : ClassFunction G) (e : I → ℕ) (psi : I → ClassFunction G)
    (_hepos : ∀ i, 0 < e i)
    (hpsi : ∀ i, IsBookIrreducibleCharacter (psi i))
    (hpair : Pairwise fun i j : I => psi i ≠ psi j)
    (hdecomp : Phi = weightedFamilySum (fun i => (e i : ℂ)) psi)
    (alpha : ClassFunction G) (halpha : IsBookIrreducibleCharacter alpha)
    (hscalar : scalarProduct G Phi alpha = 1) :
    ∃ i : I, psi i = alpha ∧ e i = 1 := by
  classical
  have hsp : ∀ i : I,
      scalarProduct G (psi i) alpha = if psi i = alpha then 1 else 0 := by
    intro i
    by_cases hi : psi i = alpha
    · rw [if_pos hi, hi]
      exact scalarProduct_irreducibleCharacter_self
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          alpha halpha)
    · rw [if_neg hi]
      exact scalarProduct_isBookIrreducible_ne
        (psi i) alpha (hpsi i) halpha hi
  let S : Finset I := Finset.univ.filter (fun i => psi i = alpha)
  have hsumC : ∑ i ∈ S, (e i : ℂ) = 1 := by
    calc
      (∑ i ∈ S, (e i : ℂ)) =
          ∑ i : I, (e i : ℂ) * scalarProduct G (psi i) alpha := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hsp i]
        by_cases h : psi i = alpha <;> simp [h]
      _ = scalarProduct G
          (weightedFamilySum (fun i => (e i : ℂ)) psi) alpha :=
        by
        have hsum := (scalarProduct_weightedFamilySum_left
          (fun i => (e i : ℂ)) psi alpha).symm
        rw [show @Finset.univ I (Fintype.ofFinite I) =
          (Finset.univ : Finset I) by ext; simp] at hsum
        exact hsum
      _ = scalarProduct G Phi alpha := by rw [← hdecomp]
      _ = 1 := hscalar
  have hsum : ∑ i ∈ S, e i = 1 := by exact_mod_cast hsumC
  have hSne : S.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsum
    simp at hsum
  obtain ⟨i, hiS⟩ := hSne
  have hSsub : S ⊆ {i} := by
    intro j hj
    have hji : psi j = psi i :=
      (Finset.mem_filter.mp hj).2.trans
        (Finset.mem_filter.mp hiS).2.symm
    simp only [Finset.mem_singleton]
    by_contra hne
    exact hpair hne hji
  have hSeq : S = {i} := by
    apply Finset.Subset.antisymm hSsub
    simpa using hiS
  refine ⟨i, (Finset.mem_filter.mp hiS).2, ?_⟩
  simpa [hSeq] using hsum

/-- Pointwise products of ordinary characters are tensor-product characters. -/
private theorem xi91_isCharacter_mul
    {G : Type u} [Group G] [Finite G]
    (phi psi : ClassFunction G)
    (hphi : IsCharacter phi) (hpsi : IsCharacter psi) :
    IsCharacter (phi * psi) := by
  rcases hphi with ⟨V, _haddV, _hmodV, _hfdV, rho, hphiRho⟩
  rcases hpsi with ⟨W, _haddW, _hmodW, _hfdW, sigma, hpsiSigma⟩
  refine ⟨TensorProduct ℂ V W, inferInstance, inferInstance, inferInstance,
    Representation.tprod rho sigma, ?_⟩
  rw [Representation.char_tensor, ← hphiRho, ← hpsiSigma]

/-- Move a real-valued right factor across the character scalar product. -/
private theorem xi91_scalarProduct_mul_conjugate_transfer
    {G : Type*} [Group G] [Finite G]
    (phi theta : ClassFunction G)
    (htheta : theta = conjugateCharacter theta) :
    scalarProduct G (phi * conjugateCharacter phi) theta =
      scalarProduct G (phi * theta) phi := by
  classical
  unfold scalarProduct
  congr 1
  apply Finset.sum_congr rfl
  intro g _hg
  have hthetaG := congrFun htheta g
  change theta g = star (theta g) at hthetaG
  simp only [Pi.mul_apply, conjugateCharacter]
  rw [← hthetaG]
  ring

/-- The least positive exponent with `d ∣ p^e - 1` divides every other
such exponent.  This is the elementary multiplicative-order step in XI.9.4(k),
stated without introducing `ZMod` units. -/
private theorem xi91_minimal_exponent_factorization
    (p d f : ℕ) (hfPos : 0 < f) (hdivF : d ∣ p ^ f - 1) :
    ∃ e k : ℕ,
      0 < e ∧
      f = e * k ∧
      d ∣ p ^ e - 1 ∧
      ∀ r : ℕ, d ∣ p ^ r - 1 → e ∣ r := by
  classical
  let P : ℕ → Prop := fun r => 0 < r ∧ d ∣ p ^ r - 1
  have hPex : ∃ r : ℕ, P r := ⟨f, hfPos, hdivF⟩
  let e : ℕ := Nat.find hPex
  have heSpec : P e := Nat.find_spec hPex
  have heDivides : ∀ r : ℕ, d ∣ p ^ r - 1 → e ∣ r := by
    intro r hr
    by_cases hrZero : r = 0
    · simp [hrZero]
    · have hmodDiv : d ∣ (p ^ r - 1) % (p ^ e - 1) :=
        (Nat.dvd_mod_iff heSpec.2).2 hr
      rw [Nat.pow_sub_one_mod_pow_sub_one] at hmodDiv
      have hremZero : r % e = 0 := by
        by_contra hremNe
        have hPRem : P (r % e) :=
          ⟨Nat.pos_of_ne_zero hremNe, hmodDiv⟩
        have hminLe : e ≤ r % e := Nat.find_min' hPex hPRem
        have hremLt : r % e < e := Nat.mod_lt r heSpec.1
        omega
      exact Nat.dvd_of_mod_eq_zero hremZero
  obtain ⟨k, hfEq⟩ := heDivides f hdivF
  exact ⟨e, k, heSpec.1, hfEq, heSpec.2, heDivides⟩

/-- Pure arithmetic core of XI.9.4(k).  The upper degree bound from (i),
the tensor lower bound from (j), and `d ∣ p^e - 1` force `f / e ≤ 2`. -/
private theorem xi91_exponent_quotient_le_two
    (n p d f e k degree0 x : ℕ)
    (hdOdd : Odd d) (hdGt : 1 < d)
    (hpOdd : Odd p) (hpGt : 1 < p) (hePos : 0 < e)
    (hfEq : f = e * k) (hnPow : n = p ^ f)
    (hDdiv : d ∣ p ^ e - 1)
    (hdegreeEq : degree0 = d * x) (hxLe : x ≤ d)
    (hlower : 1 + ((d - 1) / 2) * (n + 1) ≤ degree0 ^ 2) :
    k ≤ 2 := by
  let q : ℕ := (d - 1) / 2
  have hdPos : 0 < d := by omega
  have hdNeTwo : d ≠ 2 := by
    intro hdEq
    subst d
    rcases hdOdd with ⟨m, hm⟩
    omega
  have hdThree : 3 ≤ d := by omega
  have hsubEven : Even (d - 1) := by
    apply (Nat.even_sub' (by omega : 1 ≤ d)).2
    exact ⟨fun _ => odd_one, fun _ => hdOdd⟩
  have hqEq : 2 * q = d - 1 := by
    have hcancel := Nat.div_mul_cancel (even_iff_two_dvd.mp hsubEven)
    simpa [q, Nat.mul_comm] using hcancel
  have hqPos : 0 < q := by omega
  have hdLtFourQ : d < 4 * q := by omega
  have hdegreeLe : degree0 ≤ d ^ 2 := by
    rw [hdegreeEq, pow_two]
    exact Nat.mul_le_mul_left d hxLe
  have hdegreeSquareLe : degree0 ^ 2 ≤ d ^ 4 := by
    calc
      degree0 ^ 2 ≤ (d ^ 2) ^ 2 := Nat.pow_le_pow_left hdegreeLe 2
      _ = d ^ 4 := by ring
  have hlower' : 1 + q * (n + 1) ≤ degree0 ^ 2 := by
    simpa [q] using hlower
  have hqProdLt : q * (n + 1) < d ^ 4 := by omega
  have hleft : d * (n + 1) < (4 * q) * (n + 1) :=
    Nat.mul_lt_mul_of_pos_right hdLtFourQ (by omega)
  have hright : (4 * q) * (n + 1) < 4 * d ^ 4 := by
    have hfour := (Nat.mul_lt_mul_left (by omega : 0 < 4)).2 hqProdLt
    simpa [mul_assoc] using hfour
  have hmul : d * (n + 1) < d * (4 * d ^ 3) := by
    have htrans := hleft.trans hright
    have hEq : d * (4 * d ^ 3) = 4 * d ^ 4 := by
      calc
        d * (4 * d ^ 3) = 4 * (d * d ^ 3) := by
          ring
        _ = 4 * d ^ 4 := by simp [pow_succ, mul_assoc]
    calc
      d * (n + 1) < 4 * d ^ 4 := htrans
      _ = d * (4 * d ^ 3) := by symm; exact hEq
  have hnSuccLt : n + 1 < 4 * d ^ 3 :=
    Nat.lt_of_mul_lt_mul_left hmul
  have hnLt : n < 4 * d ^ 3 := by omega
  have hpPowOdd : Odd (p ^ e) := hpOdd.pow
  have hpPowGt : 1 < p ^ e := one_lt_pow₀ hpGt hePos.ne'
  have hpowSubEven : Even (p ^ e - 1) := by
    apply (Nat.even_sub' (by omega : 1 ≤ p ^ e)).2
    exact ⟨fun _ => odd_one, fun _ => hpPowOdd⟩
  have htwoDvd : 2 ∣ p ^ e - 1 := even_iff_two_dvd.mp hpowSubEven
  have htwoDDvd : 2 * d ∣ p ^ e - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hdOdd.coprime_two_left
      htwoDvd hDdiv
  have htwoDLe : 2 * d ≤ p ^ e - 1 :=
    Nat.le_of_dvd (by omega) htwoDDvd
  have hbaseLe : 1 + 2 * d ≤ p ^ e := by omega
  by_contra hkNot
  have hkThree : 3 ≤ k := by omega
  have hbasePow : (1 + 2 * d) ^ 3 ≤ (1 + 2 * d) ^ k :=
    Nat.pow_le_pow_right (by omega) hkThree
  have hpowMonotone : (1 + 2 * d) ^ k ≤ (p ^ e) ^ k :=
    Nat.pow_le_pow_left hbaseLe k
  have hpowEq : (p ^ e) ^ k = n := by
    rw [← pow_mul, ← hfEq, ← hnPow]
  have hcubeLeN : (1 + 2 * d) ^ 3 ≤ n := by
    rw [← hpowEq]
    exact hbasePow.trans hpowMonotone
  have hcubeGt : 4 * d ^ 3 < (1 + 2 * d) ^ 3 := by
    calc
      4 * d ^ 3 <
          4 * d ^ 3 + (1 + 6 * d + 12 * d ^ 2 + 4 * d ^ 3) :=
        Nat.lt_add_of_pos_right (by omega)
      _ = (1 + 2 * d) ^ 3 := by ring
  omega

private theorem xi91_frobenius_kernel_centralizer_le
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (z : F) (hzne : z ≠ 1) :
    Subgroup.centralizer ({(z : H)} : Set H) ≤ F := by
  intro x hx
  by_contra hxF
  obtain ⟨a, r, hconj⟩ :=
    xi91_frobenius_not_mem_kernel_conjugate_mem_complement F D hFrob hxF
  let za : F :=
    ⟨(a : H)⁻¹ * (z : H) * (a : H), by
      simpa using hFrob.normal.conj_mem (z : H) z.property (a : H)⁻¹⟩
  have hzaNe : za ≠ 1 := by
    intro hza
    apply hzne
    apply Subtype.ext
    have hzaH : (a : H)⁻¹ * (z : H) * (a : H) = 1 :=
      congrArg Subtype.val hza
    have := congrArg (fun y : H => (a : H) * y * (a : H)⁻¹) hzaH
    simpa [za, mul_assoc] using this
  have hxcomm : x * (z : H) = (z : H) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hrcomm : (r : H) * (za : H) = (za : H) * (r : H) := by
    rw [← hconj]
    dsimp [za]
    calc
      (a : H)⁻¹ * x * (a : H) * ((a : H)⁻¹ * (z : H) * (a : H)) =
          (a : H)⁻¹ * (x * (z : H)) * (a : H) := by group
      _ = (a : H)⁻¹ * ((z : H) * x) * (a : H) := by rw [hxcomm]
      _ = (a : H)⁻¹ * (z : H) * (a : H) *
          ((a : H)⁻¹ * x * (a : H)) := by group
  have hzaCent : (za : H) ∈ elementCentralizerIn F (r : H) :=
    ⟨za.property, Subgroup.mem_centralizer_singleton_iff.mpr hrcomm.symm⟩
  have hrne : r ≠ 1 := by
    intro hr
    have hrH : (r : H) = 1 := congrArg Subtype.val hr
    have hconjOne : (a : H)⁻¹ * x * (a : H) = 1 := hconj.trans hrH
    have := congrArg (fun y : H => (a : H) * y * (a : H)⁻¹) hconjOne
    have hxone : x = 1 := by simpa [mul_assoc] using this
    exact hxF (by simp [hxone])
  have hcent : elementCentralizerIn F (r : H) = ⊥ :=
    (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob r hrne
  have hzaOne : za = 1 := by
    apply Subtype.ext
    have : (za : H) ∈ (⊥ : Subgroup H) := by simpa [hcent] using hzaCent
    simpa using this
  exact hzaNe hzaOne

private theorem xi91_frobenius_irreducible_eq_induced_of_not_kernel
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (chi : ClassFunction H)
    (hchi : IsIrreducibleCharacterOnGroup chi)
    (hnotker : ¬ subgroupInKernel' chi F) :
    ∃ theta : ClassFunction F,
      IsIrreducibleCharacterOnGroup theta ∧ chi = inducedCF F theta := by
  let : F.Normal := hFrob.normal
  rcases hchi with ⟨m, rho, hrho, hchiEq⟩
  have hnotkerRho : ¬ F ≤ rho.ker := by
    intro hle
    apply hnotker
    rw [hchiEq]
    apply (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho F).2
    intro f
    exact hle f.property
  have hcentralizer : ∀ z : F, z ≠ 1 →
      Subgroup.centralizer ({(z : H)} : Set H) ≤ F :=
    fun z hz => xi91_frobenius_kernel_centralizer_le F D hFrob z hz
  obtain ⟨V, instAddV, instModuleV, instFiniteV, phi, hphi, e⟩ :=
    (Theory.Representation.isaacs_theorem_6_34.{u, 0, 0, 0}
      F hcentralizer).2 rho hrho hnotkerRho
  rcases e with ⟨e⟩
  refine ⟨phi.character,
    isIrreducibleCharacterOnGroup_of_representation phi hphi, ?_⟩
  rw [hchiEq, inducedCF_eq_representation_character]
  exact Representation.char_iso e.toRepresentationEquiv

private theorem xi91_involution_character_trace_int
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (s : G) (hs : s ^ 2 = 1) :
    ∃ r : ℕ, rho.character s =
      (2 * r : ℤ) - Module.finrank ℂ V := by
  let T : Module.End ℂ V := rho s
  have hT : T * T = 1 := by
    change rho s * rho s = 1
    rw [← map_mul, ← pow_two, hs, map_one]
  let P : Module.End ℂ V := (2 : ℂ)⁻¹ • (1 + T)
  have hP : IsIdempotentElem P := by
    rw [isIdempotentElem_iff]
    ext v
    change ((2 : ℂ)⁻¹ • (1 + T)) (((2 : ℂ)⁻¹ • (1 + T)) v) =
      ((2 : ℂ)⁻¹ • (1 + T)) v
    simp only [LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply]
    have hTv := LinearMap.congr_fun hT v
    change T (T v) = v at hTv
    rw [map_smul, map_add, hTv]
    module
  have htrace :=
    (LinearMap.IsIdempotentElem.isProj_range P hP).trace
  let r := Module.finrank ℂ (LinearMap.range P)
  refine ⟨r, ?_⟩
  have htraceP : LinearMap.trace ℂ V P = (r : ℂ) := by
    simpa [r] using htrace
  have htraceFormula :
      LinearMap.trace ℂ V P = (2 : ℂ)⁻¹ *
        ((Module.finrank ℂ V : ℂ) + LinearMap.trace ℂ V T) := by
    simp [P, LinearMap.trace_one]
    ring
  have hchar : rho.character s = LinearMap.trace ℂ V T := by rfl
  rw [htraceFormula, ← hchar] at htraceP
  push_cast
  linear_combination 2 * htraceP

private theorem xi91_involution_value_divisibility_core
    {G : Type*} [Group G] [Finite G]
    (chi : ClassFunction G) (hchi : IsBookIrreducibleCharacter chi)
    (s : G) (hssq : s ^ 2 = 1)
    (degree0 d x n p f : ℕ)
    (hdegree0 : degree chi = (degree0 : ℂ))
    (hdegreeEq : degree0 = d * x)
    (hdOdd : Odd d) (hxOdd : Odd x) (hxPos : 0 < x)
    (hclassCard : Nat.card (ConjClasses.mk s).carrier = n * d)
    (hxCoprime : Nat.Coprime x p) (hnPow : n = p ^ f) :
    ∃ value0 : ℕ, 0 < value0 ∧
      |(chi s).re| = (value0 : ℝ) ∧ x ∣ value0 := by
  obtain ⟨V, _hadd, _hmod, _hfd, rho, hchiRho, hrhoIrr⟩ :=
    isBookIrreducibleCharacter_representation_witness_irreducible chi hchi
  obtain ⟨r, htrace⟩ := xi91_involution_character_trace_int rho s hssq
  have hfinrank : Module.finrank ℂ V = degree0 := by
    have hdeg : (Module.finrank ℂ V : ℂ) = (degree0 : ℂ) := by
      calc
        (Module.finrank ℂ V : ℂ) = rho.character 1 := by
          simp [Representation.character]
        _ = chi 1 := by rw [hchiRho]
        _ = (degree0 : ℂ) := by simpa [degree] using hdegree0
    exact_mod_cast hdeg
  let z : ℤ := 2 * (r : ℤ) - degree0
  have hvalueComplex : chi s = (z : ℂ) := by
    rw [hchiRho, htrace, hfinrank]
    simp [z]
  have hvalueReal : (chi s).re = (z : ℝ) := by
    rw [hvalueComplex]
    simp
  have hdegreeOdd : Odd degree0 := by
    rw [hdegreeEq]
    exact hdOdd.mul hxOdd
  have hzOdd : Odd z := by
    rcases hdegreeOdd with ⟨m, hm⟩
    refine ⟨(r : ℤ) - (m : ℤ) - 1, ?_⟩
    dsimp [z]
    have hmZ : (degree0 : ℤ) = 2 * (m : ℤ) + 1 := by
      exact_mod_cast hm
    rw [hmZ]
    ring
  have hzNe : z ≠ 0 := by
    intro hz
    subst z
    rcases hzOdd with ⟨m, hm⟩
    omega
  let value0 := z.natAbs
  have hvaluePos : 0 < value0 := by
    simpa [value0, Int.natAbs_pos] using hzNe
  have hvalueAbs : |(chi s).re| = (value0 : ℝ) := by
    rw [hvalueReal]
    simp [value0, Nat.cast_natAbs]
  let : Representation.IsIrreducible rho := hrhoIrr
  have hclassIntegral :=
    Theory.Character.classSumScalar_isIntegral rho (ConjClasses.mk s)
  rw [Theory.Character.classSumScalar_eq_card_mul_character_div rho
      (ConjClasses.mk s) (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl),
    hclassCard, ← hchiRho, hvalueComplex,
    show chi 1 = (degree0 : ℂ) by simpa [degree] using hdegree0,
    hdegreeEq] at hclassIntegral
  have hquotientIntegral :
      IsIntegral ℤ ((((n : ℤ) * z : ℤ) : ℂ) / ((x : ℤ) : ℂ)) := by
    convert hclassIntegral using 1
    have hdNe : (d : ℂ) ≠ 0 := by
      exact_mod_cast (Odd.pos hdOdd).ne'
    have hxNe : (x : ℂ) ≠ 0 := by exact_mod_cast hxPos.ne'
    push_cast
    field_simp [hdNe, hxNe]
  have hxdvdInt : (x : ℤ) ∣ (n : ℤ) * z :=
    Theory.Character.integer_division_of_integral_quotient
      (by exact_mod_cast hxPos.ne') hquotientIntegral
  have hxdvdNat : x ∣ n * value0 := by
    have habs := (Int.natAbs_dvd_natAbs).2 hxdvdInt
    rw [Int.natAbs_mul] at habs
    simpa [value0] using habs
  have hxCoprimeN : Nat.Coprime x n := by
    rw [hnPow]
    exact hxCoprime.pow_right f
  exact ⟨value0, hvaluePos, hvalueAbs,

    hxCoprimeN.dvd_of_dvd_mul_left hxdvdNat⟩
private theorem xi91_positive_decomposition_index_of_scalar_ne_zero
    {G I : Type*} [Group G] [Finite G] [Fintype I]
    (Phi : ClassFunction G) (e : I → ℕ)
    (psi : I → ClassFunction G)
    (hpsi : ∀ i, IsBookIrreducibleCharacter (psi i))
    (hdecomp : Phi = weightedFamilySum (fun i => (e i : ℂ)) psi)
    (alpha : ClassFunction G)
    (halpha : IsBookIrreducibleCharacter alpha)
    (hscalar : scalarProduct G Phi alpha ≠ 0) :
    ∃ i : I, psi i = alpha := by
  classical
  by_contra hnone
  push Not at hnone
  apply hscalar
  rw [hdecomp, scalarProduct_weightedFamilySum_left]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [scalarProduct_isBookIrreducible_ne
    (psi i) alpha (hpsi i) halpha (hnone i)]
  simp
set_option maxHeartbeats 800000 in
private theorem xi91_nonreal_restriction_constituent_induced
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (F D : Subgroup H) [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hDcyclic : IsCyclic D)
    (psi0 alpha : ClassFunction G)
    (hpsi0Book : IsBookIrreducibleCharacter psi0)
    (hpsi0Nonreal : psi0 ≠ conjugateCharacter psi0)
    (halphaBook : IsBookIrreducibleCharacter alpha)
    (hpsi0NeAlpha : psi0 ≠ alpha)
    (hPiSplit : inducedCF H (principalCharacter H) =
      principalCharacter G + alpha)
    (B : Finset (ClassFunction G))
    (hBirr : ∀ beta : B,
      IsIrreducibleCharacterOnGroup (beta : ClassFunction G))
    (hBmem : ∀ beta : ClassFunction G,
      beta ∈ B ↔
        ∃ eta : (H ⧸ F) →* ℂˣ,
          eta ≠ 1 ∧
            inducedCF H
              (characterInflationByHom (QuotientGroup.mk' F) eta) = beta)
    (hBreal : ∀ beta : B,
      (beta : ClassFunction G) =
        conjugateCharacter (beta : ClassFunction G))
    (theta : ClassFunction H)
    (hthetaIrr : IsIrreducibleCharacterOnGroup theta)
    (hcoeffNe : scalarProduct H (subgroupRestriction H psi0) theta ≠ 0) :
    ∃ source : ClassFunction F,
      IsIrreducibleCharacterOnGroup source ∧
        theta = inducedCF F source := by
  classical
  have hpsi0Irr : IsIrreducibleCharacterOnGroup psi0 :=
    isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      psi0 hpsi0Book
  have hpsi0Class : IsClassFunction psi0 :=
    isBookIrreducibleCharacter_isClassFunction psi0 hpsi0Book
  have hprincipalGBook :
      IsBookIrreducibleCharacter (principalCharacter G) :=
    xi91_principalCharacter_isBookIrreducible
  have hpsi0NePrincipal : psi0 ≠ principalCharacter G := by
    intro heq
    apply hpsi0Nonreal
    calc
      psi0 = principalCharacter G := heq
      _ = conjugateCharacter (principalCharacter G) :=
        conjugateCharacter_principalCharacter.symm
      _ = conjugateCharacter psi0 :=
        congrArg conjugateCharacter heq.symm
  have hpsi0Principal :
      scalarProduct G psi0 (principalCharacter G) = 0 := by
    exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
      hpsi0Irr
      (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        (principalCharacter G) hprincipalGBook)
      hpsi0NePrincipal
  have hpsi0Alpha : scalarProduct G psi0 alpha = 0 := by
    exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
      hpsi0Irr
      (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        alpha halphaBook)
      hpsi0NeAlpha
  have hpsi0Pi :
      scalarProduct G psi0 (inducedCF H (principalCharacter H)) = 0 := by
    rw [hPiSplit, Section5.scalarProduct_add_right,
      hpsi0Principal, hpsi0Alpha]
    norm_num
  let Q := H ⧸ F
  let q : H →* Q := QuotientGroup.mk' F
  let eQ : Q ≃* D := hFrob.isComplement'.symm.QuotientMulEquiv
  have hQcyclic : IsCyclic Q := eQ.isCyclic.mpr hDcyclic
  let : IsCyclic Q := hQcyclic
  let : CommGroup Q := IsMulCommutative.instCommGroup
  have hthetaNotKer : ¬ subgroupInKernel' theta F := by
    intro hthetaKer
    have hkernelPairZero :
        scalarProduct G psi0 (inducedCF H theta) = 0 := by
      by_cases hprincipal : theta = principalCharacter H
      · simpa [hprincipal] using hpsi0Pi
      · have hthetaDegree : degree theta = 1 :=
          huppert_XI_5_3_degree_one_of_quotient_commutative
            F theta hthetaIrr hthetaKer
        obtain ⟨linear, hthetaLinear⟩ :=
          exists_linearCharacter_of_irreducible_degree_one
            hthetaIrr hthetaDegree
        have hFle : F ≤ linear.ker := by
          intro f hf
          change linear f = 1
          apply Units.ext
          have hvalue := hthetaKer ⟨f, hf⟩
          rw [hthetaLinear] at hvalue
          simpa [degree, hthetaDegree] using hvalue
        let eta : Q →* ℂˣ := QuotientGroup.lift F linear hFle
        have hthetaInflate :
            theta = characterInflationByHom q eta := by
          ext h
          rw [hthetaLinear]
          exact congrArg Units.val
            (QuotientGroup.lift_mk' (N := F) (φ := linear) hFle h).symm
        have hetaNe : eta ≠ 1 := by
          intro heta
          apply hprincipal
          rw [hthetaInflate, heta]
          ext h
          simp [q, characterInflationByHom, principalCharacter]
        have hbetaMem : inducedCF H theta ∈ B := by
          apply (hBmem (inducedCF H theta)).2
          refine ⟨eta, hetaNe, ?_⟩
          rw [hthetaInflate]
        let beta : B := ⟨inducedCF H theta, hbetaMem⟩
        have hpsi0NeBeta : psi0 ≠ (beta : ClassFunction G) := by
          intro heq
          apply hpsi0Nonreal
          calc
            psi0 = (beta : ClassFunction G) := heq
            _ = conjugateCharacter (beta : ClassFunction G) := hBreal beta
            _ = conjugateCharacter psi0 :=
              congrArg conjugateCharacter heq.symm
        exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
          hpsi0Irr (hBirr beta) hpsi0NeBeta
    have hcoeffAmbient :
        scalarProduct G psi0 (inducedCF H theta) =
          scalarProduct H (subgroupRestriction H psi0) theta :=
      inducedClassFunction_frobenius_right H theta psi0 hpsi0Class
    exact hcoeffNe (hcoeffAmbient.symm.trans hkernelPairZero)
  exact xi91_frobenius_irreducible_eq_induced_of_not_kernel
    F D hFrob theta hthetaIrr hthetaNotKer
private theorem xi91_scalarProduct_conjugate_left
    {G : Type*} [Finite G] (phi psi : ClassFunction G) :
    scalarProduct G (conjugateCharacter phi) psi =
      star (scalarProduct G phi (conjugateCharacter psi)) := by
  simp [scalarProduct, conjugateCharacter]

set_option maxHeartbeats 800000 in
private theorem xi91_other_source_conjugate_pairing
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (K : Set G)
    (hTI : Suzuki.VI.IsTISubsetRelative H K)
    (d : ℕ)
    (lambda lambda' : ClassFunction H)
    (hlambdaIrr : IsIrreducibleCharacterOnGroup lambda)
    (hlambda'Irr : IsIrreducibleCharacterOnGroup lambda')
    (hlambdaDegree : degree lambda = (d : ℂ))
    (hlambdaSupport : ∀ h : H, (h : G) ∉ K → lambda h = 0)
    (hlambda'Support : ∀ h : H, (h : G) ∉ K → lambda' h = 0)
    (psi0 chi2 : ClassFunction G)
    (hpsi0Char : IsCharacter psi0)
    (hchi2Def : chi2 = conjugateCharacter psi0)
    (hPhiDiff :
      inducedCF H lambda - conjugateCharacter (inducedCF H lambda) =
        psi0 - chi2)
    (hlambda'Ne : lambda' ≠ lambda)
    (hlambda'NeConj : lambda' ≠ conjugateCharacter lambda) :
    scalarProduct G psi0
        (inducedCF H (conjugateCharacter lambda')) =
      scalarProduct G psi0 (inducedCF H lambda') := by
  classical
  let eta : ClassFunction H := lambda - conjugateCharacter lambda
  have hlambdaConjIrr :
      IsIrreducibleCharacterOnGroup (conjugateCharacter lambda) :=
    isIrreducibleCharacterOnGroup_conjugateCharacter hlambdaIrr
  have hlambdaVirtual : Theory.Character.IsVirtualCharacter lambda :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hlambdaIrr
  have hlambdaConjVirtual :
      Theory.Character.IsVirtualCharacter (conjugateCharacter lambda) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      hlambdaConjIrr
  have hetaVirtual : Theory.Character.IsVirtualCharacter eta :=
    Section3.isVirtualCharacter_sub hlambdaVirtual hlambdaConjVirtual
  have hetaOne : eta 1 = 0 := by
    have hlambdaOne : lambda 1 = (d : ℂ) := by
      simpa [degree] using hlambdaDegree
    simp [eta, conjugateCharacter, hlambdaOne]
  have hetaSupport : ∀ h : H, (h : G) ∉ K → eta h = 0 := by
    intro h hhK
    rw [show eta h = lambda h - star (lambda h) by rfl,
      hlambdaSupport h hhK]
    simp
  have hlambda'Virtual : Theory.Character.IsVirtualCharacter lambda' :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hlambda'Irr
  have hpairTI :=
    (Suzuki.VI.suzuki_ch6_proposition_2_9
      H K hTI eta hetaVirtual hetaSupport).2.2
      hetaOne lambda' hlambda'Virtual hlambda'Support
  have hIndEta :
      inducedCF H eta =
        inducedCF H lambda - conjugateCharacter (inducedCF H lambda) := by
    calc
      inducedCF H eta = inducedCFLinear H eta :=
        (inducedCFLinear_apply H eta).symm
      _ = inducedCFLinear H lambda -
          inducedCFLinear H (conjugateCharacter lambda) := by
        rw [show eta = lambda - conjugateCharacter lambda by rfl, map_sub]
      _ = inducedCF H lambda - inducedCF H (conjugateCharacter lambda) := by
        rw [inducedCFLinear_apply, inducedCFLinear_apply]
      _ = inducedCF H lambda - conjugateCharacter (inducedCF H lambda) := by
        rw [xi91_conjugateCharacter_inducedCF H lambda]
  have hsourceZero : scalarProduct H eta lambda' = 0 := by
    rw [show eta = lambda - conjugateCharacter lambda by rfl,
      Section5.scalarProduct_sub_left,
      scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hlambdaIrr hlambda'Irr (Ne.symm hlambda'Ne),
      scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hlambdaConjIrr hlambda'Irr (Ne.symm hlambda'NeConj)]
    norm_num
  have hdiffPair :
      scalarProduct G
        (inducedCF H lambda - conjugateCharacter (inducedCF H lambda))
        (inducedCF H lambda') = 0 := by
    rw [← hIndEta, hpairTI, hsourceZero]
  have hcoefficientEq :
      scalarProduct G psi0 (inducedCF H lambda') =
        scalarProduct G chi2 (inducedCF H lambda') := by
    rw [hPhiDiff] at hdiffPair
    rw [Section5.scalarProduct_sub_left] at hdiffPair
    exact sub_eq_zero.mp hdiffPair
  have hlambda'ConjIrr :
      IsIrreducibleCharacterOnGroup (conjugateCharacter lambda') :=
    isIrreducibleCharacterOnGroup_conjugateCharacter hlambda'Irr
  have hconjAmbientChar :
      IsCharacter (inducedCF H (conjugateCharacter lambda')) :=
    isCharacter_inducedCF_of_isCharacter H (conjugateCharacter lambda')
      (isCharacter_of_isIrreducibleCharacterOnGroup hlambda'ConjIrr)
  obtain ⟨r, hr⟩ := scalarProduct_character_character_eq_nat
    psi0 (inducedCF H (conjugateCharacter lambda'))
      hpsi0Char hconjAmbientChar
  have hconjTransfer :
      scalarProduct G chi2 (inducedCF H lambda') =
        scalarProduct G psi0
          (inducedCF H (conjugateCharacter lambda')) := by
    rw [hchi2Def]
    have h := xi91_scalarProduct_conjugate_left
      (G := G) psi0 (inducedCF H lambda')
    rw [xi91_conjugateCharacter_inducedCF H lambda'] at h
    rw [hr] at h
    calc
      scalarProduct G (conjugateCharacter psi0) (inducedCF H lambda') =
          (r : ℂ) := by simpa using h
      _ = scalarProduct G psi0
          (inducedCF H (conjugateCharacter lambda')) := hr.symm
  exact hconjTransfer.symm.trans hcoefficientEq.symm


set_option maxHeartbeats 800000 in
private theorem xi91_other_linear_source_pairing_zero
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (K : Set G)
    (hTI : Suzuki.VI.IsTISubsetRelative H K)
    (d : ℕ)
    (lambda lambda' : ClassFunction H)
    (hlambdaIrr : IsIrreducibleCharacterOnGroup lambda)
    (hlambda'Irr : IsIrreducibleCharacterOnGroup lambda')
    (hlambdaDegree : degree lambda = (d : ℂ))
    (hlambdaSupport : ∀ h : H, (h : G) ∉ K → lambda h = 0)
    (hlambda'Support : ∀ h : H, (h : G) ∉ K → lambda' h = 0)
    (psi0 chi2 : ClassFunction G)
    (hpsi0Book : IsBookIrreducibleCharacter psi0)
    (hchi2Book : IsBookIrreducibleCharacter chi2)
    (hpsi0Nonreal : psi0 ≠ conjugateCharacter psi0)
    (hchi2Nonreal : chi2 ≠ conjugateCharacter chi2)
    (hchi2Ne : chi2 ≠ psi0)
    (hPhiDiff :
      inducedCF H lambda - conjugateCharacter (inducedCF H lambda) =
        psi0 - chi2)
    (_hpsi0Phi : scalarProduct G psi0 (inducedCF H lambda) = 1)
    (hPhi'Char : IsCharacter (inducedCF H lambda'))
    (hPhi'Norm :
      scalarProduct G (inducedCF H lambda') (inducedCF H lambda') =
        (d + 1 : ℂ))
    (hPhi'Indicator :
      xi91_classFunctionIndicator G (inducedCF H lambda') = (d : ℂ))
    (hlambda'Ne : lambda' ≠ lambda)
    (hlambda'NeConj : lambda' ≠ conjugateCharacter lambda) :
    scalarProduct G psi0 (inducedCF H lambda') = 0 := by
  classical
  let eta : ClassFunction H := lambda - conjugateCharacter lambda
  have hlambdaConjIrr :
      IsIrreducibleCharacterOnGroup (conjugateCharacter lambda) :=
    isIrreducibleCharacterOnGroup_conjugateCharacter hlambdaIrr
  have hlambdaVirtual : Theory.Character.IsVirtualCharacter lambda :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hlambdaIrr
  have hlambdaConjVirtual :
      Theory.Character.IsVirtualCharacter (conjugateCharacter lambda) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      hlambdaConjIrr
  have hetaVirtual : Theory.Character.IsVirtualCharacter eta :=
    Section3.isVirtualCharacter_sub hlambdaVirtual hlambdaConjVirtual
  have hetaOne : eta 1 = 0 := by
    have hlambdaOne : lambda 1 = (d : ℂ) := by
      simpa [degree] using hlambdaDegree
    simp [eta, conjugateCharacter, hlambdaOne]
  have hetaSupport : ∀ h : H, (h : G) ∉ K → eta h = 0 := by
    intro h hhK
    rw [show eta h = lambda h - star (lambda h) by rfl,
      hlambdaSupport h hhK]
    simp
  have hlambda'Virtual : Theory.Character.IsVirtualCharacter lambda' :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hlambda'Irr
  have hpairTI :=
    (Suzuki.VI.suzuki_ch6_proposition_2_9
      H K hTI eta hetaVirtual hetaSupport).2.2
      hetaOne lambda' hlambda'Virtual hlambda'Support
  have hIndEta :
      inducedCF H eta =
        inducedCF H lambda - conjugateCharacter (inducedCF H lambda) := by
    calc
      inducedCF H eta = inducedCFLinear H eta :=
        (inducedCFLinear_apply H eta).symm
      _ = inducedCFLinear H lambda -
          inducedCFLinear H (conjugateCharacter lambda) := by
        rw [show eta = lambda - conjugateCharacter lambda by rfl, map_sub]
      _ = inducedCF H lambda - inducedCF H (conjugateCharacter lambda) := by
        rw [inducedCFLinear_apply, inducedCFLinear_apply]
      _ = inducedCF H lambda - conjugateCharacter (inducedCF H lambda) := by
        rw [xi91_conjugateCharacter_inducedCF H lambda]
  have hsourceZero : scalarProduct H eta lambda' = 0 := by
    rw [show eta = lambda - conjugateCharacter lambda by rfl,
      Section5.scalarProduct_sub_left,
      scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hlambdaIrr hlambda'Irr (Ne.symm hlambda'Ne),
      scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hlambdaConjIrr hlambda'Irr (Ne.symm hlambda'NeConj)]
    norm_num
  have hdiffPair :
      scalarProduct G
        (inducedCF H lambda - conjugateCharacter (inducedCF H lambda))
        (inducedCF H lambda') = 0 := by
    rw [← hIndEta, hpairTI, hsourceZero]
  have hcoefficientEq :
      scalarProduct G psi0 (inducedCF H lambda') =
        scalarProduct G chi2 (inducedCF H lambda') := by
    rw [hPhiDiff] at hdiffPair
    rw [Section5.scalarProduct_sub_left] at hdiffPair
    exact sub_eq_zero.mp hdiffPair
  have hPhi'Ne : inducedCF H lambda' ≠ 0 := by
    intro hzero
    have hz : (0 : ℂ) = (d + 1 : ℂ) := by
      simpa [hzero, scalarProduct] using hPhi'Norm
    have hzNat : 0 = d + 1 := by exact_mod_cast hz
    omega
  obtain ⟨I, hIFintype, hIDecidable, e, psi, _iBase,
      hepos, hpsi, hpair, hdecomp⟩ :=
    exists_positive_irreducible_decomposition_of_character
      (inducedCF H lambda') hPhi'Char hPhi'Ne
  let : Fintype I := hIFintype
  let : DecidableEq I := hIDecidable
  obtain ⟨iNonreal, _heiNonreal, hiNonreal, hotherReal⟩ :=
    xi91_positive_decomposition_unique_nonreal
      (inducedCF H lambda') e psi hepos hpsi hpair hdecomp d
        hPhi'Norm hPhi'Indicator
  by_contra hpsiCoeff
  have hchi2Coeff :
      scalarProduct G chi2 (inducedCF H lambda') ≠ 0 := by
    rw [← hcoefficientEq]
    exact hpsiCoeff
  have hpsiRight :
      scalarProduct G (inducedCF H lambda') psi0 ≠ 0 := by
    intro hzero
    have hstar :
        star (scalarProduct G psi0 (inducedCF H lambda')) = 0 := by
      simpa [hzero] using
        (scalarProduct_star_swap
          (G := G) (phi := inducedCF H lambda') (psi := psi0))
    have := congrArg star hstar
    exact hpsiCoeff (by simpa using this)
  have hchi2Right :
      scalarProduct G (inducedCF H lambda') chi2 ≠ 0 := by
    intro hzero
    have hstar :
        star (scalarProduct G chi2 (inducedCF H lambda')) = 0 := by
      simpa [hzero] using
        (scalarProduct_star_swap
          (G := G) (phi := inducedCF H lambda') (psi := chi2))
    have := congrArg star hstar
    exact hchi2Coeff (by simpa using this)
  obtain ⟨iPsi, hiPsi⟩ :=
    xi91_positive_decomposition_index_of_scalar_ne_zero
      (inducedCF H lambda') e psi hpsi hdecomp
        psi0 hpsi0Book hpsiRight
  obtain ⟨iChi2, hiChi2⟩ :=
    xi91_positive_decomposition_index_of_scalar_ne_zero
      (inducedCF H lambda') e psi hpsi hdecomp
        chi2 hchi2Book hchi2Right
  have hiPsiEq : iPsi = iNonreal := by
    by_contra hne
    have hreal := (hotherReal iPsi hne).2
    rw [hiPsi] at hreal
    exact hpsi0Nonreal hreal
  have hiChi2Eq : iChi2 = iNonreal := by
    by_contra hne
    have hreal := (hotherReal iChi2 hne).2
    rw [hiChi2] at hreal
    exact hchi2Nonreal hreal
  apply hchi2Ne
  calc
    chi2 = psi iChi2 := hiChi2.symm
    _ = psi iNonreal := congrArg psi hiChi2Eq
    _ = psi iPsi := congrArg psi hiPsiEq.symm
    _ = psi0 := hiPsi
private theorem xi91_even_sum_of_fixedPointFree_pairing
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (pair : ι → ι) (n : ι → ℕ)
    (hpair_mem : ∀ i, i ∈ s → pair i ∈ s)
    (hpair_pair : ∀ i, i ∈ s → pair (pair i) = i)
    (hpair_ne : ∀ i, i ∈ s → pair i ≠ i)
    (hnpair : ∀ i, i ∈ s → n (pair i) = n i) :
    ∃ m : ℕ, (∑ i ∈ s, n i) = 2 * m := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ s : Finset ι, s.card = k →
      (∀ i, i ∈ s → pair i ∈ s) →
      (∀ i, i ∈ s → pair (pair i) = i) →
      (∀ i, i ∈ s → pair i ≠ i) →
      (∀ i, i ∈ s → n (pair i) = n i) →
      ∃ m : ℕ, (∑ i ∈ s, n i) = 2 * m
  have hmain : ∀ k, P k := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih s hcard hmem hinv hne hn
    by_cases hsempty : s = ∅
    · subst hsempty
      exact ⟨0, by simp⟩
    · rcases Finset.nonempty_iff_ne_empty.mpr hsempty with ⟨x, hx⟩
      let y := pair x
      have hy : y ∈ s := hmem x hx
      have hyx : y ≠ x := hne x hx
      let t : Finset ι := (s.erase x).erase y
      have hysx : y ∈ s.erase x := by simp [y, hy, hyx]
      have htCardLt : t.card < s.card := by
        have htSub : t ⊆ s.erase x := by
          intro z hz
          exact (Finset.mem_erase.mp hz).2
        exact lt_of_le_of_lt (Finset.card_le_card htSub)
          (Finset.card_erase_lt_of_mem hx)
      have hmemT : ∀ i, i ∈ t → pair i ∈ t := by
        intro i hi
        have hiS : i ∈ s :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
        have hpiS : pair i ∈ s := hmem i hiS
        have hpiNeX : pair i ≠ x := by
          intro hfix
          have hix : i = y := by
            calc
              i = pair (pair i) := (hinv i hiS).symm
              _ = pair x := by rw [hfix]
              _ = y := rfl
          exact (Finset.mem_erase.mp hi).1 hix
        have hpiNeY : pair i ≠ y := by
          intro hfix
          have hpairY : pair y = x := by simpa [y] using hinv x hx
          have hix : i = x := by
            calc
              i = pair (pair i) := (hinv i hiS).symm
              _ = pair y := by rw [hfix]
              _ = x := hpairY
          exact (Finset.mem_erase.mp
            (Finset.mem_erase.mp hi).2).1 hix
        simp [t, hpiS, hpiNeX, hpiNeY]
      have hinvT : ∀ i, i ∈ t → pair (pair i) = i := by
        intro i hi
        exact hinv i ((Finset.mem_erase.mp
          (Finset.mem_erase.mp hi).2).2)
      have hneT : ∀ i, i ∈ t → pair i ≠ i := by
        intro i hi
        exact hne i ((Finset.mem_erase.mp
          (Finset.mem_erase.mp hi).2).2)
      have hnT : ∀ i, i ∈ t → n (pair i) = n i := by
        intro i hi
        exact hn i ((Finset.mem_erase.mp
          (Finset.mem_erase.mp hi).2).2)
      rcases ih t.card (by simpa [hcard] using htCardLt)
          t rfl hmemT hinvT hneT hnT with ⟨m, hm⟩
      have hsumS :
          (∑ i ∈ s, n i) = n x + n y + ∑ i ∈ t, n i := by
        calc
          (∑ i ∈ s, n i) = ∑ i ∈ insert x (s.erase x), n i := by
            rw [Finset.insert_erase hx]
          _ = n x + ∑ i ∈ s.erase x, n i := by simp [-Finset.insert_erase_eq_insert]
          _ = n x + (n y + ∑ i ∈ t, n i) := by
            rw [show (∑ i ∈ s.erase x, n i) =
                ∑ i ∈ insert y t, n i by
              rw [Finset.insert_erase hysx]]
            simp [t, -Finset.insert_erase_eq_insert]
          _ = n x + n y + ∑ i ∈ t, n i := by ring
      have hny : n y = n x := hn x hx
      refine ⟨n x + m, ?_⟩
      rw [hsumS, hny, hm]
      ring
  exact hmain s.card s rfl hpair_mem hpair_pair hpair_ne hnpair


private theorem xi91_odd_irreducible_self_conjugate_eq_principal
    {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    (theta : ClassFunction G)
    (hthetaIrr : IsIrreducibleCharacterOnGroup theta)
    (hthetaReal : theta = conjugateCharacter theta) :
    theta = principalCharacter G := by
  classical
  by_contra hne
  have hprincipalIrr :
      IsIrreducibleCharacterOnGroup (principalCharacter G) :=
    isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (principalCharacter G) xi91_principalCharacter_isBookIrreducible
  have horth : scalarProduct G theta (principalCharacter G) = 0 :=
    scalarProduct_irreducibleCharacter_eq_zero_of_ne
      hthetaIrr hprincipalIrr hne
  have hcardNe : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hinvNe : (Nat.card G : ℂ)⁻¹ ≠ 0 := inv_ne_zero hcardNe
  have hsumZero : ∑ g : G, theta g = 0 := by
    unfold scalarProduct principalCharacter at horth
    simp only [star_one, mul_one] at horth
    exact (mul_eq_zero.mp horth).resolve_left hinvNe
  let sqInv : G ≃ G := Equiv.ofBijective
    (fun g : G => g⁻¹ * g⁻¹) (xi91_invSq_bijective_of_odd_card hodd)
  have hsqSum : ∑ g : G, theta (g⁻¹ * g⁻¹) = 0 := by
    calc
      (∑ g : G, theta (g⁻¹ * g⁻¹)) = ∑ g : G, theta g := by
        simpa [sqInv] using (Equiv.sum_comp sqInv theta)
      _ = 0 := hsumZero
  have hindicatorZero : xi91_classFunctionIndicator G theta = 0 := by
    unfold xi91_classFunctionIndicator
    rw [hsqSum, mul_zero]
  have hnotReal :=
    (xi91_classFunctionIndicator_eq_zero_iff_not_fixed_conjugate
      theta
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        hthetaIrr)).mp hindicatorZero
  exact hnotReal hthetaReal


set_option maxHeartbeats 800000 in

private theorem xi91_nonreal_restriction_degree_multiple
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (F D : Subgroup H) [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hDcyclic : IsCyclic D)
    (psi0 alpha : ClassFunction G)
    (hpsi0Book : IsBookIrreducibleCharacter psi0)
    (hpsi0Nonreal : psi0 ≠ conjugateCharacter psi0)
    (halphaBook : IsBookIrreducibleCharacter alpha)
    (hpsi0NeAlpha : psi0 ≠ alpha)
    (hPiSplit : inducedCF H (principalCharacter H) =
      principalCharacter G + alpha)
    (B : Finset (ClassFunction G))
    (hBirr : ∀ beta : B,
      IsIrreducibleCharacterOnGroup (beta : ClassFunction G))
    (hBmem : ∀ beta : ClassFunction G,
      beta ∈ B ↔
        ∃ eta : (H ⧸ F) →* ℂˣ,
          eta ≠ 1 ∧
            inducedCF H
              (characterInflationByHom (QuotientGroup.mk' F) eta) = beta)
    (hBreal : ∀ beta : B,
      (beta : ClassFunction G) =
        conjugateCharacter (beta : ClassFunction G))
    (degree0 : ℕ) (hdegree0Pos : 0 < degree0)
    (hdegree0 : degree psi0 = (degree0 : ℂ)) :
    ∃ x : ℕ, 0 < x ∧ degree0 = Nat.card D * x := by
  classical
  let res : ClassFunction H := subgroupRestriction H psi0
  have hresChar : IsCharacter res := by
    rcases Section1.subgroupRestriction_eq_representation_character_of_isCharacter
        H psi0 hpsi0Book.1 with
      ⟨V, hVadd, hVmodule, hVfinite, rho, hrho⟩
    exact ⟨V, hVadd, hVmodule, hVfinite, rho, by
      simpa [res] using hrho⟩
  obtain ⟨J, hJFintype, hJDecidable, m, theta,
      hthetaBook, hthetaPair, hresDecomp⟩ :=
    character_irreducible_decomposition_all res hresChar
  let : Fintype J := hJFintype
  let : DecidableEq J := hJDecidable
  have hthetaIrr : ∀ j : J,
      IsIrreducibleCharacterOnGroup (theta j) := by
    intro j
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (theta j) (hthetaBook j)
  have hthetaOrth : ∀ j k : J,
      scalarProduct H (theta j) (theta k) =
        if j = k then 1 else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst k
      simp [scalarProduct_irreducibleCharacter_self (hthetaIrr j)]
    · rw [if_neg hjk]
      exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hthetaIrr j) (hthetaIrr k) (hthetaPair hjk)
  have hcoefficient : ∀ j : J,
      scalarProduct H res (theta j) = (m j : ℂ) := by
    intro j
    exact proposition_1_7_multiplicity_from_decomposition
      m theta res hthetaOrth hresDecomp j
  have htermMultiple : ∀ j : J, ∃ q0 : ℕ,
      (m j : ℂ) * degree (theta j) =
        (Nat.card D * q0 : ℕ) := by
    intro j
    by_cases hmzero : m j = 0
    · exact ⟨0, by simp [hmzero]⟩
    · have hmcast : (m j : ℂ) ≠ 0 := by exact_mod_cast hmzero
      have hcoeffNe : scalarProduct H res (theta j) ≠ 0 := by
        rw [hcoefficient j]
        exact hmcast
      obtain ⟨source, hsourceIrr, hthetaInduced⟩ :=
        xi91_nonreal_restriction_constituent_induced
          H F D hFrob hDcyclic psi0 alpha hpsi0Book
          hpsi0Nonreal halphaBook hpsi0NeAlpha hPiSplit
          B hBirr hBmem hBreal (theta j) (hthetaIrr j)
          (by simpa [res] using hcoeffNe)
      obtain ⟨z, _hzpos, hsourceDegree⟩ :=
        Section6.theorem_6_6_positive_degree_nat_of_irreducible
          hsourceIrr
      refine ⟨m j * z, ?_⟩
      rw [hthetaInduced, degree_inducedClassFunction,
        hFrob.isComplement'.symm.index_eq_card, hsourceDegree]
      push_cast
      ring
  choose q0 hq0 using htermMultiple
  have hdegreeSum :
      (degree0 : ℂ) =
        ∑ j : J, (m j : ℂ) * degree (theta j) := by
    calc
      (degree0 : ℂ) = degree psi0 := hdegree0.symm
      _ = degree res := by simp [res, subgroupRestriction, degree]
      _ = degree (weightedFamilySum (fun j => (m j : ℂ)) theta) :=
        congrArg degree hresDecomp
      _ = ∑ j : J, (m j : ℂ) * degree (theta j) := by
        simp only [degree, weightedFamilySum]
        apply Finset.sum_congr
        · ext j
          simp
        · intro j _hj
          rfl
  have hdegreeSumMultiple :
      (degree0 : ℂ) =
        ((Nat.card D * ∑ j : J, q0 j : ℕ) : ℂ) := by
    calc
      (degree0 : ℂ) =
          ∑ j : J, (m j : ℂ) * degree (theta j) := hdegreeSum
      _ = ∑ j : J, ((Nat.card D * q0 j : ℕ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact hq0 j
      _ = ((Nat.card D * ∑ j : J, q0 j : ℕ) : ℂ) := by
        push_cast
        rw [Finset.mul_sum]
  have hdegreeNat :
      degree0 = Nat.card D * ∑ j : J, q0 j := by
    exact_mod_cast hdegreeSumMultiple
  have hsumPos : 0 < ∑ j : J, q0 j := by
    by_contra hnotpos
    have hsumZero : ∑ j : J, q0 j = 0 :=
      Nat.eq_zero_of_not_pos hnotpos
    rw [hsumZero] at hdegreeNat
    simp at hdegreeNat
    omega
  exact ⟨∑ j : J, q0 j, hsumPos, hdegreeNat⟩
set_option maxHeartbeats 800000 in
private theorem xi91_nonreal_restriction_degree_coprime
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (F D : Subgroup H) [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hDcyclic : IsCyclic D)
    (hDgt : 1 < Nat.card D)
    (p : ℕ) (hp : Nat.Prime p) (hFp : IsPGroup p F)
    (lambda : ClassFunction H)
    (hlambdaIrr : IsIrreducibleCharacterOnGroup lambda)
    (hlambdaDegree : degree lambda = (Nat.card D : ℂ))
    (hlambdaSupport : ∀ h : H,
      (h : G) ∉ (F.map H.subtype : Set G) → lambda h = 0)
    (hTI : Suzuki.VI.IsTISubsetRelative H
      (F.map H.subtype : Set G))
    (hAmbientNorm : ∀ eta : F →* ℂˣ, eta ≠ 1 →
      scalarProduct G
        (inducedCF H
          (inducedCF F (xi91_linearCharacterRepresentation eta).character))
        (inducedCF H
          (inducedCF F (xi91_linearCharacterRepresentation eta).character)) =
        (Nat.card D + 1 : ℂ))
    (hAmbientIndicator : ∀ eta : F →* ℂˣ, eta ≠ 1 →
      xi91_classFunctionIndicator G
        (inducedCF H
          (inducedCF F (xi91_linearCharacterRepresentation eta).character)) =
        (Nat.card D : ℂ))
    (psi0 chi2 alpha : ClassFunction G)
    (hpsi0Book : IsBookIrreducibleCharacter psi0)
    (hchi2Book : IsBookIrreducibleCharacter chi2)
    (hpsi0Nonreal : psi0 ≠ conjugateCharacter psi0)
    (hchi2Nonreal : chi2 ≠ conjugateCharacter chi2)
    (hchi2Ne : chi2 ≠ psi0)
    (halphaBook : IsBookIrreducibleCharacter alpha)
    (hpsi0NeAlpha : psi0 ≠ alpha)
    (hPhiDiff :
      inducedCF H lambda - conjugateCharacter (inducedCF H lambda) =
        psi0 - chi2)
    (hpsi0Phi : scalarProduct G psi0 (inducedCF H lambda) = 1)
    (hPiSplit : inducedCF H (principalCharacter H) =
      principalCharacter G + alpha)
    (B : Finset (ClassFunction G))
    (hBirr : ∀ beta : B,
      IsIrreducibleCharacterOnGroup (beta : ClassFunction G))
    (hBmem : ∀ beta : ClassFunction G,
      beta ∈ B ↔
        ∃ eta : (H ⧸ F) →* ℂˣ,
          eta ≠ 1 ∧
            inducedCF H
              (characterInflationByHom (QuotientGroup.mk' F) eta) = beta)
    (hBreal : ∀ beta : B,
      (beta : ClassFunction G) =
        conjugateCharacter (beta : ClassFunction G))
    (degree0 x : ℕ) (hdegree0Pos : 0 < degree0)
    (hdegree0 : degree psi0 = (degree0 : ℂ))
    (hdegreeEq : degree0 = Nat.card D * x) :
    Nat.Coprime x p := by
  classical
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let Q := H ⧸ F
  let eQ : Q ≃* D := hFrob.isComplement'.symm.QuotientMulEquiv
  have hQcyclic : IsCyclic Q := eQ.isCyclic.mpr hDcyclic
  let : IsCyclic Q := hQcyclic
  let : CommGroup Q := IsMulCommutative.instCommGroup
  have hpsi0Irr : IsIrreducibleCharacterOnGroup psi0 :=
    isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      psi0 hpsi0Book
  have hchi2Irr : IsIrreducibleCharacterOnGroup chi2 :=
    isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      chi2 hchi2Book
  have hpsi0Class : IsClassFunction psi0 :=
    isBookIrreducibleCharacter_isClassFunction psi0 hpsi0Book
  have hpsi0Self : scalarProduct G psi0 psi0 = 1 :=
    scalarProduct_irreducibleCharacter_self hpsi0Irr
  have hpsi0Chi2 : scalarProduct G psi0 chi2 = 0 :=
    scalarProduct_irreducibleCharacter_eq_zero_of_ne
      hpsi0Irr hchi2Irr (Ne.symm hchi2Ne)
  have hpsi0ConjPhi :
      scalarProduct G psi0 (conjugateCharacter (inducedCF H lambda)) = 0 := by
    have hpair := congrArg (fun phi : ClassFunction G =>
      scalarProduct G psi0 phi) hPhiDiff
    change scalarProduct G psi0
      (inducedCF H lambda - conjugateCharacter (inducedCF H lambda)) =
        scalarProduct G psi0 (psi0 - chi2) at hpair
    rw [Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right, hpsi0Phi,
      hpsi0Self, hpsi0Chi2] at hpair
    exact sub_right_inj.mp hpair
  let res : ClassFunction H := subgroupRestriction H psi0
  have hresChar : IsCharacter res := by
    rcases Section1.subgroupRestriction_eq_representation_character_of_isCharacter
        H psi0 hpsi0Book.1 with
      ⟨V, hVadd, hVmodule, hVfinite, rho, hrho⟩
    exact ⟨V, hVadd, hVmodule, hVfinite, rho, by
      simpa [res] using hrho⟩
  have hresNe : res ≠ 0 := by
    intro hzero
    have hvalue := congrFun hzero (1 : H)
    have hdegZero : degree psi0 = 0 := by
      simpa [res, subgroupRestriction, degree] using hvalue
    rw [hdegree0] at hdegZero
    have : degree0 = 0 := by exact_mod_cast hdegZero
    omega
  obtain ⟨J, hJFintype, hJDecidable, m, theta, _jBase,
      hmpos, hthetaBook, hthetaPair, hresDecomp⟩ :=
    exists_positive_irreducible_decomposition_of_character
      res hresChar hresNe
  let : Fintype J := hJFintype
  let : DecidableEq J := hJDecidable
  have hthetaIrr : ∀ j : J,
      IsIrreducibleCharacterOnGroup (theta j) := by
    intro j
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (theta j) (hthetaBook j)
  have hthetaOrth : ∀ j k : J,
      scalarProduct H (theta j) (theta k) =
        if j = k then 1 else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst k
      simp [scalarProduct_irreducibleCharacter_self (hthetaIrr j)]
    · rw [if_neg hjk]
      exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hthetaIrr j) (hthetaIrr k) (hthetaPair hjk)
  have hcoefficient : ∀ j : J,
      scalarProduct H res (theta j) = (m j : ℂ) := by
    intro j
    exact proposition_1_7_multiplicity_from_decomposition
      m theta res hthetaOrth hresDecomp j
  have hlambdaBook : IsBookIrreducibleCharacter lambda :=
    isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hlambdaIrr
  have hresLambda : scalarProduct H res lambda = 1 := by
    calc
      scalarProduct H res lambda =
          scalarProduct G psi0 (inducedCF H lambda) := by
        simpa [res] using
          (inducedClassFunction_frobenius_right
            H lambda psi0 hpsi0Class).symm
      _ = 1 := hpsi0Phi
  obtain ⟨jLambda, hthetaLambda, hmLambda⟩ :=
    xi91_decomposition_index_of_scalar_one
      res m theta hmpos hthetaBook hthetaPair hresDecomp
        lambda hlambdaBook hresLambda
  obtain ⟨f, hFpow⟩ := (IsPGroup.iff_card.mp hFp)
  have htermData : ∀ j : J, ∃ q0 : ℕ,
      (m j : ℂ) * degree (theta j) =
        (Nat.card D * q0 : ℕ) ∧
      (j = jLambda → q0 = 1) ∧
      (j ≠ jLambda → p ∣ q0) := by
    intro j
    have hmcast : (m j : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hmpos j))
    have hcoeffNe : scalarProduct H res (theta j) ≠ 0 := by
      rw [hcoefficient j]
      exact hmcast
    obtain ⟨source, hsourceIrr, hthetaInduced⟩ :=
      xi91_nonreal_restriction_constituent_induced
        H F D hFrob hDcyclic psi0 alpha hpsi0Book
        hpsi0Nonreal halphaBook hpsi0NeAlpha hPiSplit
        B hBirr hBmem hBreal (theta j) (hthetaIrr j)
        (by simpa [res] using hcoeffNe)
    obtain ⟨z, hzPos, hsourceDegree⟩ :=
      Section6.theorem_6_6_positive_degree_nat_of_irreducible
        hsourceIrr
    obtain ⟨z', hsourceDegree', hz'Dvd⟩ :=
      degree_nat_dvd_card_of_isBookIrreducibleCharacter source
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
          hsourceIrr)
    have hzz' : z' = z := by
      exact_mod_cast hsourceDegree'.symm.trans hsourceDegree
    subst z'
    refine ⟨m j * z, ?_, ?_, ?_⟩
    · rw [hthetaInduced, degree_inducedClassFunction,
        hFrob.isComplement'.symm.index_eq_card, hsourceDegree]
      push_cast
      ring
    · intro hj
      subst j
      have hdegEq := congrArg degree
        (hthetaLambda.symm.trans hthetaInduced)
      rw [hlambdaDegree, degree_inducedClassFunction,
        hFrob.isComplement'.symm.index_eq_card, hsourceDegree] at hdegEq
      have hdegNat : Nat.card D = Nat.card D * z := by
        exact_mod_cast hdegEq
      have hzOne : z = 1 := by
        apply Nat.eq_of_mul_eq_mul_left
          (n := Nat.card D) (m := z) (k := 1) (Nat.card_pos (α := D))
        simpa only [mul_one] using hdegNat.symm
      simp [hmLambda, hzOne]
    · intro hjNe
      have hzNe : z ≠ 1 := by
        intro hzOne
        obtain ⟨eta, hsourceLinear⟩ :=
          exists_linearCharacter_of_irreducible_degree_one
            hsourceIrr (hsourceDegree.trans (by simp [hzOne]))
        let lambda' : ClassFunction H :=
          inducedCF F (xi91_linearCharacterRepresentation eta).character
        have hsourceRep :
            source = (xi91_linearCharacterRepresentation eta).character := by
          ext y
          have hy := congrFun hsourceLinear y
          simpa [xi91_linearCharacterRepresentation_character] using hy
        have hthetaLambda' : theta j = lambda' := by
          calc
            theta j = inducedCF F source := hthetaInduced
            _ = inducedCF F
                (xi91_linearCharacterRepresentation eta).character :=
              congrArg (inducedCF F) hsourceRep
            _ = lambda' := rfl
        have hetaNe : eta ≠ 1 := by
          intro heta
          have hthetaKer : subgroupInKernel' (theta j) F := by
            rw [hthetaLambda']
            intro y
            change lambda' y = lambda' 1
            dsimp [lambda']
            unfold inducedCF inducedClassFunction
            congr 1
            apply Finset.sum_congr rfl
            intro g _hg
            have hgy : (g : H) * (y : H) * (g : H)⁻¹ ∈ F :=
              hFrob.normal.conj_mem (y : H) y.property (g : H)
            simp [hgy, heta, xi91_linearCharacterRepresentation_character]
          have hthetaDegreeOne : degree (theta j) = 1 :=
            huppert_XI_5_3_degree_one_of_quotient_commutative
              F (theta j) (hthetaIrr j) hthetaKer
          have hthetaDegreeD : degree (theta j) = (Nat.card D : ℂ) := by
            rw [hthetaInduced, degree_inducedClassFunction,
              hFrob.isComplement'.symm.index_eq_card,
              hsourceDegree, hzOne]
            norm_num
          rw [hthetaDegreeD] at hthetaDegreeOne
          have hDone : Nat.card D = 1 := by exact_mod_cast hthetaDegreeOne
          omega
        have hlambda'Irr : IsIrreducibleCharacterOnGroup lambda' := by
          rw [← hthetaLambda']
          exact hthetaIrr j
        have hlambda'Support : ∀ h : H,
            (h : G) ∉ (F.map H.subtype : Set G) → lambda' h = 0 := by
          intro h hhK
          apply xi91_induced_linearCharacter_support F eta h
          intro hhF
          apply hhK
          exact ⟨h, hhF, rfl⟩
        have hambientCoeff :
            scalarProduct G psi0 (inducedCF H lambda') = (m j : ℂ) := by
          calc
            scalarProduct G psi0 (inducedCF H lambda') =
                scalarProduct H res lambda' := by
              simpa [res] using
                inducedClassFunction_frobenius_right
                  H lambda' psi0 hpsi0Class
            _ = scalarProduct H res (theta j) := by rw [hthetaLambda']
            _ = (m j : ℂ) := hcoefficient j
        by_cases hlambdaEq : lambda' = lambda
        · apply (hthetaPair hjNe)
          exact hthetaLambda'.trans (hlambdaEq.trans hthetaLambda.symm)
        by_cases hlambdaConj : lambda' = conjugateCharacter lambda
        · have hzero :
              scalarProduct G psi0 (inducedCF H lambda') = 0 := by
            rw [hlambdaConj,
              ← xi91_conjugateCharacter_inducedCF H lambda]
            exact hpsi0ConjPhi
          rw [hzero] at hambientCoeff
          exact hmcast hambientCoeff.symm
        · have hPhi'Char : IsCharacter (inducedCF H lambda') :=
            isCharacter_inducedCF_of_isCharacter H lambda'
              (isCharacter_of_isIrreducibleCharacterOnGroup hlambda'Irr)
          have hzero := xi91_other_linear_source_pairing_zero
            H (F.map H.subtype : Set G) hTI (Nat.card D)
            lambda lambda' hlambdaIrr hlambda'Irr hlambdaDegree
            hlambdaSupport hlambda'Support psi0 chi2 hpsi0Book
            hchi2Book hpsi0Nonreal hchi2Nonreal hchi2Ne hPhiDiff
            hpsi0Phi hPhi'Char (by simpa [lambda'] using hAmbientNorm eta hetaNe)
            (by simpa [lambda'] using hAmbientIndicator eta hetaNe)
            hlambdaEq hlambdaConj
          rw [hzero] at hambientCoeff
          exact hmcast hambientCoeff.symm
      have hzDvdPow : z ∣ p ^ f := by
        rw [← hFpow]
        simpa [Nat.card_eq_fintype_card] using hz'Dvd
      rcases (Nat.dvd_prime_pow hp).mp hzDvdPow with
        ⟨k, _hkLe, hzPow⟩
      have hkNe : k ≠ 0 := by
        intro hk
        subst k
        simp at hzPow
        exact hzNe hzPow
      apply dvd_mul_of_dvd_right
      rw [hzPow]
      exact dvd_pow_self p hkNe
  choose q0 hqTerm hqLambda hqDiv using htermData
  have hdegreeSum :
      (degree0 : ℂ) =
        ∑ j : J, (m j : ℂ) * degree (theta j) := by
    calc
      (degree0 : ℂ) = degree psi0 := hdegree0.symm
      _ = degree res := by simp [res, subgroupRestriction, degree]
      _ = degree (weightedFamilySum (fun j => (m j : ℂ)) theta) :=
        congrArg degree hresDecomp
      _ = ∑ j : J, (m j : ℂ) * degree (theta j) := by
        simp only [degree, weightedFamilySum]
        apply Finset.sum_congr
        · ext j
          simp
        · intro j _hj
          rfl
  have hdegreeSumMultiple :
      (degree0 : ℂ) =
        ((Nat.card D * ∑ j : J, q0 j : ℕ) : ℂ) := by
    calc
      (degree0 : ℂ) =
          ∑ j : J, (m j : ℂ) * degree (theta j) := hdegreeSum
      _ = ∑ j : J, ((Nat.card D * q0 j : ℕ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact hqTerm j
      _ = ((Nat.card D * ∑ j : J, q0 j : ℕ) : ℂ) := by
        push_cast
        rw [Finset.mul_sum]
  have hdegreeNat :
      degree0 = Nat.card D * ∑ j : J, q0 j := by
    exact_mod_cast hdegreeSumMultiple
  have hxSum : x = ∑ j : J, q0 j := by
    rw [hdegreeEq] at hdegreeNat
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hdegreeNat
  let R : Finset J := Finset.univ.erase jLambda
  have hqLambdaOne : q0 jLambda = 1 := hqLambda jLambda rfl
  have hsumSplit :
      (∑ j ∈ R, q0 j) + q0 jLambda = ∑ j : J, q0 j := by
    simpa [R] using
      Finset.sum_erase_add (s := (Finset.univ : Finset J)) q0
        (Finset.mem_univ jLambda)
  have hsumRDiv : p ∣ ∑ j ∈ R, q0 j := by
    apply Finset.dvd_sum
    intro j hj
    exact hqDiv j (Finset.mem_erase.mp hj).1
  obtain ⟨k, hk⟩ := hsumRDiv
  have hxShape : x = 1 + p * k := by
    rw [hxSum, ← hsumSplit, hqLambdaOne, hk]
    omega
  rw [hxShape]
  exact (Nat.coprime_add_mul_left_left 1 p k).2
    (Nat.coprime_one_left p)
set_option maxHeartbeats 800000 in
private theorem xi91_nonreal_restriction_degree_odd
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (F D : Subgroup H) [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hDcyclic : IsCyclic D)
    (hDgt : 1 < Nat.card D)
    (hHodd : Odd (Nat.card H))
    (lambda : ClassFunction H)
    (hlambdaIrr : IsIrreducibleCharacterOnGroup lambda)
    (hlambdaDegree : degree lambda = (Nat.card D : ℂ))
    (hlambdaSupport : ∀ h : H,
      (h : G) ∉ (F.map H.subtype : Set G) → lambda h = 0)
    (hTI : Suzuki.VI.IsTISubsetRelative H
      (F.map H.subtype : Set G))
    (psi0 chi2 alpha : ClassFunction G)
    (hpsi0Book : IsBookIrreducibleCharacter psi0)
    (hchi2Def : chi2 = conjugateCharacter psi0)
    (hchi2Book : IsBookIrreducibleCharacter chi2)
    (hchi2Ne : chi2 ≠ psi0)
    (hpsi0Nonreal : psi0 ≠ conjugateCharacter psi0)
    (halphaBook : IsBookIrreducibleCharacter alpha)
    (hpsi0NeAlpha : psi0 ≠ alpha)
    (hPhiDiff :
      inducedCF H lambda - conjugateCharacter (inducedCF H lambda) =
        psi0 - chi2)
    (hpsi0Phi : scalarProduct G psi0 (inducedCF H lambda) = 1)
    (hPiSplit : inducedCF H (principalCharacter H) =
      principalCharacter G + alpha)
    (B : Finset (ClassFunction G))
    (hBirr : ∀ beta : B,
      IsIrreducibleCharacterOnGroup (beta : ClassFunction G))
    (hBmem : ∀ beta : ClassFunction G,
      beta ∈ B ↔
        ∃ eta : (H ⧸ F) →* ℂˣ,
          eta ≠ 1 ∧
            inducedCF H
              (characterInflationByHom (QuotientGroup.mk' F) eta) = beta)
    (hBreal : ∀ beta : B,
      (beta : ClassFunction G) =
        conjugateCharacter (beta : ClassFunction G))
    (degree0 x : ℕ) (hdegree0Pos : 0 < degree0)
    (hdegree0 : degree psi0 = (degree0 : ℂ))
    (hdegreeEq : degree0 = Nat.card D * x) :
    Odd x := by
  classical
  have hpsi0Irr : IsIrreducibleCharacterOnGroup psi0 :=
    isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      psi0 hpsi0Book
  have hchi2Irr : IsIrreducibleCharacterOnGroup chi2 :=
    isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      chi2 hchi2Book
  have hpsi0Class : IsClassFunction psi0 :=
    isBookIrreducibleCharacter_isClassFunction psi0 hpsi0Book
  have hpsi0Self : scalarProduct G psi0 psi0 = 1 :=
    scalarProduct_irreducibleCharacter_self hpsi0Irr
  have hpsi0Chi2 : scalarProduct G psi0 chi2 = 0 :=
    scalarProduct_irreducibleCharacter_eq_zero_of_ne
      hpsi0Irr hchi2Irr (Ne.symm hchi2Ne)
  have hpsi0ConjPhi :
      scalarProduct G psi0 (conjugateCharacter (inducedCF H lambda)) = 0 := by
    have hpair := congrArg (fun phi : ClassFunction G =>
      scalarProduct G psi0 phi) hPhiDiff
    change scalarProduct G psi0
      (inducedCF H lambda - conjugateCharacter (inducedCF H lambda)) =
        scalarProduct G psi0 (psi0 - chi2) at hpair
    rw [Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right, hpsi0Phi,
      hpsi0Self, hpsi0Chi2] at hpair
    exact sub_right_inj.mp hpair
  let res : ClassFunction H := subgroupRestriction H psi0
  have hresChar : IsCharacter res := by
    rcases Section1.subgroupRestriction_eq_representation_character_of_isCharacter
        H psi0 hpsi0Book.1 with
      ⟨V, hVadd, hVmodule, hVfinite, rho, hrho⟩
    exact ⟨V, hVadd, hVmodule, hVfinite, rho, by
      simpa [res] using hrho⟩
  have hresNe : res ≠ 0 := by
    intro hzero
    have hvalue := congrFun hzero (1 : H)
    have hdegZero : degree psi0 = 0 := by
      simpa [res, subgroupRestriction, degree] using hvalue
    rw [hdegree0] at hdegZero
    have : degree0 = 0 := by exact_mod_cast hdegZero
    omega
  obtain ⟨J, hJFintype, hJDecidable, m, theta, _jBase,
      hmpos, hthetaBook, hthetaPair, hresDecomp⟩ :=
    exists_positive_irreducible_decomposition_of_character
      res hresChar hresNe
  let : Fintype J := hJFintype
  let : DecidableEq J := hJDecidable
  have hthetaIrr : ∀ j : J,
      IsIrreducibleCharacterOnGroup (theta j) := by
    intro j
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (theta j) (hthetaBook j)
  have hthetaInjective : Function.Injective theta := by
    intro i j hij
    by_contra hne
    exact (hthetaPair hne) hij
  have hthetaOrth : ∀ j k : J,
      scalarProduct H (theta j) (theta k) =
        if j = k then 1 else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst k
      simp [scalarProduct_irreducibleCharacter_self (hthetaIrr j)]
    · rw [if_neg hjk]
      exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hthetaIrr j) (hthetaIrr k) (hthetaPair hjk)
  have hcoefficient : ∀ j : J,
      scalarProduct H res (theta j) = (m j : ℂ) := by
    intro j
    exact proposition_1_7_multiplicity_from_decomposition
      m theta res hthetaOrth hresDecomp j
  have hlambdaBook : IsBookIrreducibleCharacter lambda :=
    isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hlambdaIrr
  have hresLambda : scalarProduct H res lambda = 1 := by
    calc
      scalarProduct H res lambda =
          scalarProduct G psi0 (inducedCF H lambda) := by
        simpa [res] using
          (inducedClassFunction_frobenius_right
            H lambda psi0 hpsi0Class).symm
      _ = 1 := hpsi0Phi
  obtain ⟨jLambda, hthetaLambda, hmLambda⟩ :=
    xi91_decomposition_index_of_scalar_one
      res m theta hmpos hthetaBook hthetaPair hresDecomp
        lambda hlambdaBook hresLambda
  choose source hsourceIrr hthetaInduced using fun j : J =>
    xi91_nonreal_restriction_constituent_induced
      H F D hFrob hDcyclic psi0 alpha hpsi0Book
      hpsi0Nonreal halphaBook hpsi0NeAlpha hPiSplit
      B hBirr hBmem hBreal (theta j) (hthetaIrr j)
      (by
        rw [hcoefficient j]
        exact_mod_cast (Nat.ne_of_gt (hmpos j)))
  choose z hzPos hsourceDegree using fun j : J =>
    Section6.theorem_6_6_positive_degree_nat_of_irreducible
      (hsourceIrr j)
  let q0 : J → ℕ := fun j => m j * z j
  have hterm : ∀ j : J,
      (m j : ℂ) * degree (theta j) =
        (Nat.card D * q0 j : ℕ) := by
    intro j
    rw [hthetaInduced j, degree_inducedClassFunction,
      hFrob.isComplement'.symm.index_eq_card, hsourceDegree j]
    simp only [q0]
    push_cast
    ring
  have hqLambdaOne : q0 jLambda = 1 := by
    have hdegEq := congrArg degree
      (hthetaLambda.symm.trans (hthetaInduced jLambda))
    rw [hlambdaDegree, degree_inducedClassFunction,
      hFrob.isComplement'.symm.index_eq_card,
      hsourceDegree jLambda] at hdegEq
    have hdegNat : Nat.card D = Nat.card D * z jLambda := by
      exact_mod_cast hdegEq
    have hzOne : z jLambda = 1 := by
      apply Nat.eq_of_mul_eq_mul_left
        (n := Nat.card D) (m := z jLambda) (k := 1)
        (Nat.card_pos (α := D))
      simpa only [mul_one] using hdegNat.symm
    simp [q0, hmLambda, hzOne]
  have hpartnerExists : ∀ j : J, j ≠ jLambda →
      ∃ k : J,
        k ≠ jLambda ∧ k ≠ j ∧ q0 k = q0 j ∧
          theta k = conjugateCharacter (theta j) := by
    intro j hjNe
    have hthetaNeLambda : theta j ≠ lambda := by
      intro hEq
      exact (hthetaPair hjNe) (hEq.trans hthetaLambda.symm)
    have hambientCoeff :
        scalarProduct G psi0 (inducedCF H (theta j)) = (m j : ℂ) := by
      calc
        scalarProduct G psi0 (inducedCF H (theta j)) =
            scalarProduct H res (theta j) := by
          simpa [res] using
            inducedClassFunction_frobenius_right
              H (theta j) psi0 hpsi0Class
        _ = (m j : ℂ) := hcoefficient j
    have hthetaNeConjLambda : theta j ≠ conjugateCharacter lambda := by
      intro hEq
      have hzero : scalarProduct G psi0 (inducedCF H (theta j)) = 0 := by
        rw [hEq, ← xi91_conjugateCharacter_inducedCF H lambda]
        exact hpsi0ConjPhi
      rw [hzero] at hambientCoeff
      have hmNe : (m j : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (hmpos j))
      exact hmNe hambientCoeff.symm
    have hthetaSupport : ∀ h : H,
        (h : G) ∉ (F.map H.subtype : Set G) → theta j h = 0 := by
      intro h hhK
      rw [hthetaInduced j]
      apply inducedClassFunction_eq_zero_of_not_mem_of_normal F (source j)
      intro hhF
      apply hhK
      exact ⟨h, hhF, rfl⟩
    have hpairConj := xi91_other_source_conjugate_pairing
      H (F.map H.subtype : Set G) hTI (Nat.card D)
      lambda (theta j) hlambdaIrr (hthetaIrr j) hlambdaDegree
      hlambdaSupport hthetaSupport psi0 chi2 hpsi0Book.1 hchi2Def
      hPhiDiff hthetaNeLambda hthetaNeConjLambda
    have hconjCoeff :
        scalarProduct H res (conjugateCharacter (theta j)) = (m j : ℂ) := by
      calc
        scalarProduct H res (conjugateCharacter (theta j)) =
            scalarProduct G psi0
              (inducedCF H (conjugateCharacter (theta j))) := by
          simpa [res] using
            (inducedClassFunction_frobenius_right
              H (conjugateCharacter (theta j)) psi0 hpsi0Class).symm
        _ = scalarProduct G psi0 (inducedCF H (theta j)) := hpairConj
        _ = (m j : ℂ) := hambientCoeff
    have hconjBook :
        IsBookIrreducibleCharacter (conjugateCharacter (theta j)) :=
      isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (isIrreducibleCharacterOnGroup_conjugateCharacter (hthetaIrr j))
    have hconjCoeffNe :
        scalarProduct H res (conjugateCharacter (theta j)) ≠ 0 := by
      rw [hconjCoeff]
      exact_mod_cast (Nat.ne_of_gt (hmpos j))
    obtain ⟨k, hkTheta⟩ :=
      xi91_positive_decomposition_index_of_scalar_ne_zero
        res m theta hthetaBook hresDecomp
          (conjugateCharacter (theta j)) hconjBook hconjCoeffNe
    have hmEq : m k = m j := by
      have hcast : (m k : ℂ) = (m j : ℂ) := by
        rw [← hcoefficient k, hkTheta]
        exact hconjCoeff
      exact_mod_cast hcast
    have hthetaDegree : degree (theta j) =
        (Nat.card D * z j : ℕ) := by
      rw [hthetaInduced j, degree_inducedClassFunction,
        hFrob.isComplement'.symm.index_eq_card, hsourceDegree j]
      push_cast
      ring
    have hthetaNePrincipal : theta j ≠ principalCharacter H := by
      intro hEq
      have hdegEq := congrArg degree hEq
      rw [hthetaDegree] at hdegEq
      simp [degree, principalCharacter] at hdegEq
      have hnatF : Fintype.card D * z j = 1 := by
        exact_mod_cast hdegEq
      have hnat : Nat.card D * z j = 1 := by
        simpa [Nat.card_eq_fintype_card] using hnatF
      have hcardLeOne : Nat.card D ≤ 1 := by
        calc
          Nat.card D = Nat.card D * 1 := by simp
          _ ≤ Nat.card D * z j := Nat.mul_le_mul_left _ (hzPos j)
          _ = 1 := hnat
      omega
    have hthetaNonreal : theta j ≠ conjugateCharacter (theta j) := by
      intro hreal
      exact hthetaNePrincipal
        (xi91_odd_irreducible_self_conjugate_eq_principal
          hHodd (theta j) (hthetaIrr j) hreal)
    have hkNeJ : k ≠ j := by
      intro hEq
      subst k
      exact hthetaNonreal hkTheta
    have hkNeLambda : k ≠ jLambda := by
      intro hEq
      subst k
      apply hthetaNeConjLambda
      calc
        theta j = conjugateCharacter (conjugateCharacter (theta j)) := by
          ext g
          simp [conjugateCharacter]
        _ = conjugateCharacter lambda :=
          congrArg conjugateCharacter (hkTheta.symm.trans hthetaLambda)
    have hdegreeEq : degree (theta k) = degree (theta j) := by
      rw [hkTheta]
      change star (theta j 1) = theta j 1
      have hdeg := hthetaDegree
      change theta j 1 = (Nat.card D * z j : ℕ) at hdeg
      rw [hdeg]
      simp
    have hqEq : q0 k = q0 j := by
      have hcast : ((Nat.card D * q0 k : ℕ) : ℂ) =
          ((Nat.card D * q0 j : ℕ) : ℂ) := by
        rw [← hterm k, ← hterm j, hmEq, hdegreeEq]
      have hnat : Nat.card D * q0 k = Nat.card D * q0 j := by
        exact_mod_cast hcast
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hnat
    exact ⟨k, hkNeLambda, hkNeJ, hqEq, hkTheta⟩
  let partner : J → J := fun j =>
    if hj : j = jLambda then jLambda
    else Classical.choose (hpartnerExists j hj)
  have hpartnerSpec : ∀ j : J, j ≠ jLambda →
      partner j ≠ jLambda ∧ partner j ≠ j ∧
        q0 (partner j) = q0 j ∧
          theta (partner j) = conjugateCharacter (theta j) := by
    intro j hj
    simp [partner, hj]
    exact Classical.choose_spec (hpartnerExists j hj)
  let R : Finset J := Finset.univ.erase jLambda
  have hpartnerMem : ∀ j, j ∈ R → partner j ∈ R := by
    intro j hj
    have hjNe := (Finset.mem_erase.mp hj).1
    exact Finset.mem_erase.mpr
      ⟨(hpartnerSpec j hjNe).1, Finset.mem_univ _⟩
  have hpartnerPair : ∀ j, j ∈ R → partner (partner j) = j := by
    intro j hj
    have hjNe := (Finset.mem_erase.mp hj).1
    have hpNe := (hpartnerSpec j hjNe).1
    apply hthetaInjective
    rw [(hpartnerSpec (partner j) hpNe).2.2.2,
      (hpartnerSpec j hjNe).2.2.2]
    ext g
    simp [conjugateCharacter]
  have hpartnerNe : ∀ j, j ∈ R → partner j ≠ j := by
    intro j hj
    exact (hpartnerSpec j (Finset.mem_erase.mp hj).1).2.1
  have hqPartner : ∀ j, j ∈ R → q0 (partner j) = q0 j := by
    intro j hj
    exact (hpartnerSpec j (Finset.mem_erase.mp hj).1).2.2.1
  obtain ⟨r, hr⟩ := xi91_even_sum_of_fixedPointFree_pairing
    R partner q0 hpartnerMem hpartnerPair hpartnerNe hqPartner
  have hdegreeSum :
      (degree0 : ℂ) =
        ∑ j : J, (m j : ℂ) * degree (theta j) := by
    calc
      (degree0 : ℂ) = degree psi0 := hdegree0.symm
      _ = degree res := by simp [res, subgroupRestriction, degree]
      _ = degree (weightedFamilySum (fun j => (m j : ℂ)) theta) :=
        congrArg degree hresDecomp
      _ = ∑ j : J, (m j : ℂ) * degree (theta j) := by
        simp only [degree, weightedFamilySum]
        apply Finset.sum_congr
        · ext j
          simp
        · intro j _hj
          rfl
  have hdegreeSumMultiple :
      (degree0 : ℂ) =
        ((Nat.card D * ∑ j : J, q0 j : ℕ) : ℂ) := by
    calc
      (degree0 : ℂ) =
          ∑ j : J, (m j : ℂ) * degree (theta j) := hdegreeSum
      _ = ∑ j : J, ((Nat.card D * q0 j : ℕ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact hterm j
      _ = ((Nat.card D * ∑ j : J, q0 j : ℕ) : ℂ) := by
        push_cast
        rw [Finset.mul_sum]
  have hdegreeNat : degree0 = Nat.card D * ∑ j : J, q0 j := by
    exact_mod_cast hdegreeSumMultiple
  have hxSum : x = ∑ j : J, q0 j := by
    rw [hdegreeEq] at hdegreeNat
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hdegreeNat
  have hsumSplit :
      (∑ j ∈ R, q0 j) + q0 jLambda = ∑ j : J, q0 j := by
    simpa [R] using
      Finset.sum_erase_add (s := (Finset.univ : Finset J)) q0
        (Finset.mem_univ jLambda)
  refine ⟨r, ?_⟩
  rw [hxSum, ← hsumSplit, hqLambdaOne, hr]


set_option maxHeartbeats 800000 in
private theorem xi91_zassenhaus_restriction_degree_coprime
    {G : Type u} {Omega : Type v} {I : Type*}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    [Fintype I] [DecidableEq I]
    (n : ℕ) (hdegree : Fintype.card Omega = n + 1)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (p : ℕ) (hp : Nat.Prime p) (hFp : IsPGroup p F)
    (hDcyclic : IsCyclic
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hDgt : 1 < Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFcard : Nat.card F = n)
    (hpointOdd : Odd (Nat.card (MulAction.stabilizer G a)))
    (hinvolutionCard : Nat.card {t : G // orderOf t = 2} =
      n * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (chi : F →* ℂˣ)
    (lambda : ClassFunction (MulAction.stabilizer G a))
    (hlambdaDef : lambda =
      inducedCF F (xi91_linearCharacterRepresentation chi).character)
    (hlambdaIrr : IsIrreducibleCharacterOnGroup lambda)
    (hlambdaDegree : degree lambda =
      (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) : ℂ))
    (Phi : ClassFunction G)
    (hPhiDef : Phi = inducedCF (MulAction.stabilizer G a) lambda)
    (e : I → ℕ) (psi : I → ClassFunction G) (i0 : I)
    (hpsi : ∀ i : I, IsBookIrreducibleCharacter (psi i))
    (hpair : Pairwise fun i j : I => psi i ≠ psi j)
    (hdecomp : Phi = weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hei0 : e i0 = 1)
    (hpsi0Nonreal : psi i0 ≠ conjugateCharacter (psi i0))
    (chi2 : ClassFunction G)
    (hchi2Def : chi2 = conjugateCharacter (psi i0))
    (hchi2Book : IsBookIrreducibleCharacter chi2)
    (hchi2Ne : chi2 ≠ psi i0)
    (alpha : ClassFunction G)
    (halphaBook : IsBookIrreducibleCharacter alpha)
    (hpsi0NeAlpha : psi i0 ≠ alpha)
    (hPhiDiff : Phi - conjugateCharacter Phi = psi i0 - chi2)
    (Pi : ClassFunction G)
    (hPiDef : Pi =
      inducedCF (MulAction.stabilizer G a)
        (principalCharacter (MulAction.stabilizer G a)))
    (hPiSplit : Pi = principalCharacter G + alpha)
    (B : Finset (ClassFunction G))
    (hBirr : ∀ beta : B,
      IsIrreducibleCharacterOnGroup (beta : ClassFunction G))
    (hBmem : ∀ beta : ClassFunction G,
      beta ∈ B ↔
        ∃ eta : (MulAction.stabilizer G a ⧸ F) →* ℂˣ,
          eta ≠ 1 ∧
            inducedCF (MulAction.stabilizer G a)
              (characterInflationByHom (QuotientGroup.mk' F) eta) = beta)
    (hBreal : ∀ beta : B,
      (beta : ClassFunction G) =
        conjugateCharacter (beta : ClassFunction G))
    (degree0 x : ℕ) (hdegree0Pos : 0 < degree0)
    (hdegree0 : degree (psi i0) = (degree0 : ℂ))
    (hdegreeEq : degree0 =
      Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) * x) :
    Nat.Coprime x p := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  have hlambdaSupportK : ∀ h : H,
      (h : G) ∉ (F.map H.subtype : Set G) → lambda h = 0 := by
    intro h hhK
    rw [hlambdaDef]
    apply xi91_induced_linearCharacter_support F chi h
    intro hhF
    apply hhK
    exact ⟨h, hhF, rfl⟩
  have hkernelTI : Suzuki.VI.IsTISubsetRelative H
      (F.map H.subtype : Set G) := by
    simpa [H] using
      xi91_kernelCarrier_relativeTI
        (G := G) (Omega := Omega) htwo a b hab F hFrob
  have hAmbientNormAll : ∀ eta : F →* ℂˣ, eta ≠ 1 →
      scalarProduct G
        (inducedCF H
          (inducedCF F (xi91_linearCharacterRepresentation eta).character))
        (inducedCF H
          (inducedCF F (xi91_linearCharacterRepresentation eta).character)) =
        (Nat.card D + 1 : ℂ) := by
    intro eta heta
    simpa [H, D] using
      xi91_linearCharacter_ambient_induced_norm
        htwo n hdegree a b hab F hFrob hFcard eta heta
  have hAmbientIndicatorAll : ∀ eta : F →* ℂˣ, eta ≠ 1 →
      xi91_classFunctionIndicator G
        (inducedCF H
          (inducedCF F (xi91_linearCharacterRepresentation eta).character)) =
        (Nat.card D : ℂ) := by
    intro eta heta
    simpa [H, D] using
      xi91_linearCharacter_ambient_induced_indicator
        htwo a b hab F hFrob n hFcard hpointOdd
          hinvolutionCard eta heta
  have hchi2Nonreal : chi2 ≠ conjugateCharacter chi2 := by
    have hconjChi2 : conjugateCharacter chi2 = psi i0 := by
      rw [hchi2Def]
      ext g
      simp [conjugateCharacter]
    intro hEq
    exact hchi2Ne (hEq.trans hconjChi2)
  have hpsiOrth : ∀ i j : I,
      scalarProduct G (psi i) (psi j) =
        if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [scalarProduct_irreducibleCharacter_self
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi i) (hpsi i))]
    · rw [if_neg hij]
      exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi i) (hpsi i))
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi j) (hpsi j))
        (hpair hij)
  have hPhiPsi0 : scalarProduct G Phi (psi i0) = 1 := by
    rw [proposition_1_7_multiplicity_from_decomposition
      e psi Phi hpsiOrth hdecomp i0, hei0]
    norm_num
  have hpsi0Phi : scalarProduct G (psi i0) Phi = 1 := by
    have hswap := scalarProduct_star_swap
      (G := G) (phi := psi i0) (psi := Phi)
    simpa [hPhiPsi0] using hswap.symm
  exact xi91_nonreal_restriction_degree_coprime
    H F D (by simpa [D] using hFrob) (by simpa [D] using hDcyclic)
    hDgt p hp hFp lambda hlambdaIrr
    hlambdaDegree hlambdaSupportK hkernelTI
    hAmbientNormAll hAmbientIndicatorAll
    (psi i0) chi2 alpha (hpsi i0) hchi2Book
    hpsi0Nonreal hchi2Nonreal hchi2Ne halphaBook hpsi0NeAlpha
    (by rw [← hPhiDef]; simpa using hPhiDiff)
    (by rw [← hPhiDef]; exact hpsi0Phi)
    (by rw [← hPiDef]; exact hPiSplit)
    B hBirr hBmem hBreal degree0 x hdegree0Pos hdegree0
    hdegreeEq


set_option maxHeartbeats 800000 in
private theorem xi91_zassenhaus_restriction_degree_odd
    {G : Type u} {Omega : Type v} {I : Type*}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    [Fintype I] [DecidableEq I]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    [F.Normal]
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hDcyclic : IsCyclic
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hDgt : 1 < Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hpointOdd : Odd (Nat.card (MulAction.stabilizer G a)))
    (chi : F →* ℂˣ)
    (lambda : ClassFunction (MulAction.stabilizer G a))
    (hlambdaDef : lambda =
      inducedCF F (xi91_linearCharacterRepresentation chi).character)
    (hlambdaIrr : IsIrreducibleCharacterOnGroup lambda)
    (hlambdaDegree : degree lambda =
      (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) : ℂ))
    (Phi : ClassFunction G)
    (hPhiDef : Phi = inducedCF (MulAction.stabilizer G a) lambda)
    (e : I → ℕ) (psi : I → ClassFunction G) (i0 : I)
    (hpsi : ∀ i : I, IsBookIrreducibleCharacter (psi i))
    (hpair : Pairwise fun i j : I => psi i ≠ psi j)
    (hdecomp : Phi = weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hei0 : e i0 = 1)
    (hpsi0Nonreal : psi i0 ≠ conjugateCharacter (psi i0))
    (chi2 : ClassFunction G)
    (hchi2Def : chi2 = conjugateCharacter (psi i0))
    (hchi2Book : IsBookIrreducibleCharacter chi2)
    (hchi2Ne : chi2 ≠ psi i0)
    (alpha : ClassFunction G)
    (halphaBook : IsBookIrreducibleCharacter alpha)
    (hpsi0NeAlpha : psi i0 ≠ alpha)
    (hPhiDiff : Phi - conjugateCharacter Phi = psi i0 - chi2)
    (Pi : ClassFunction G)
    (hPiDef : Pi =
      inducedCF (MulAction.stabilizer G a)
        (principalCharacter (MulAction.stabilizer G a)))
    (hPiSplit : Pi = principalCharacter G + alpha)
    (B : Finset (ClassFunction G))
    (hBirr : ∀ beta : B,
      IsIrreducibleCharacterOnGroup (beta : ClassFunction G))
    (hBmem : ∀ beta : ClassFunction G,
      beta ∈ B ↔
        ∃ eta : (MulAction.stabilizer G a ⧸ F) →* ℂˣ,
          eta ≠ 1 ∧
            inducedCF (MulAction.stabilizer G a)
              (characterInflationByHom (QuotientGroup.mk' F) eta) = beta)
    (hBreal : ∀ beta : B,
      (beta : ClassFunction G) =
        conjugateCharacter (beta : ClassFunction G))
    (degree0 x : ℕ) (hdegree0Pos : 0 < degree0)
    (hdegree0 : degree (psi i0) = (degree0 : ℂ))
    (hdegreeEq : degree0 =
      Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) * x) :
    Odd x := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  have hlambdaSupportK : ∀ h : H,
      (h : G) ∉ (F.map H.subtype : Set G) → lambda h = 0 := by
    intro h hhK
    rw [hlambdaDef]
    apply xi91_induced_linearCharacter_support F chi h
    intro hhF
    apply hhK
    exact ⟨h, hhF, rfl⟩
  have hkernelTI : Suzuki.VI.IsTISubsetRelative H
      (F.map H.subtype : Set G) := by
    simpa [H] using
      xi91_kernelCarrier_relativeTI
        (G := G) (Omega := Omega) htwo a b hab F hFrob
  have hpsiOrth : ∀ i j : I,
      scalarProduct G (psi i) (psi j) =
        if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [scalarProduct_irreducibleCharacter_self
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi i) (hpsi i))]
    · rw [if_neg hij]
      exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi i) (hpsi i))
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi j) (hpsi j))
        (hpair hij)
  have hPhiPsi0 : scalarProduct G Phi (psi i0) = 1 := by
    rw [proposition_1_7_multiplicity_from_decomposition
      e psi Phi hpsiOrth hdecomp i0, hei0]
    norm_num
  have hpsi0Phi : scalarProduct G (psi i0) Phi = 1 := by
    have hswap := scalarProduct_star_swap
      (G := G) (phi := psi i0) (psi := Phi)
    simpa [hPhiPsi0] using hswap.symm
  exact xi91_nonreal_restriction_degree_odd
    H F D hFrob hDcyclic
    hDgt hpointOdd
    lambda hlambdaIrr hlambdaDegree
    hlambdaSupportK hkernelTI (psi i0) chi2 alpha (hpsi i0)
    hchi2Def hchi2Book hchi2Ne hpsi0Nonreal halphaBook hpsi0NeAlpha
    (by rw [← hPhiDef]; simpa using hPhiDiff)
    (by rw [← hPhiDef]; exact hpsi0Phi)
    (by rw [← hPiDef]; exact hPiSplit)
    B hBirr hBmem hBreal degree0 x hdegree0Pos hdegree0
    hdegreeEq


set_option maxHeartbeats 800000 in
/-- Ito XI.9.1 in its Zassenhaus-group context: if the point-stabilizer
Frobenius kernel is a noncommutative `p`-group and the two-point stabilizer is
a Z-group, then `p = 2`.

The ambient action hypotheses are essential.  The corresponding assertion for
an arbitrary Frobenius group is false (for example, an order-three scalar
action on the Heisenberg group over `F_7`). -/
private theorem huppert_XI_9_1_noncommutativeKernel_zGroupComplement_aux
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (n : ℕ) (hdegree : Fintype.card Omega = n + 1)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (p : ℕ) (hp : Nat.Prime p)
    (hFnoncomm : ¬ IsMulCommutative F)
    (hFp : IsPGroup p F)
    (hDZ : IsZGroup
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    p = 2 := by
  classical
  let SharpTriple : Prop :=
    ∀ a b c a' b' c' : Omega,
      a ≠ b → a ≠ c → b ≠ c →
      a' ≠ b' → a' ≠ c' → b' ≠ c' →
      ∃! g : G,
        g • a = a' ∧ g • b = b' ∧ g • c = c'
  have hnot_sharp : ¬ SharpTriple := by
    intro hsharp
    apply hFnoncomm
    rcases huppert_blackburn_XI_sharpTriple_kernel_elementaryAbelian
        n hdegree htwo_transitive hsharp a b hab F hFrob with
      ⟨_, _, _, _, _, hFelem⟩
    exact hFelem.toIsMulCommutative
  by_cases hp2 : p = 2
  · exact hp2
  let D : Subgroup (MulAction.stabilizer G a) :=
    MulAction.stabilizer (MulAction.stabilizer G a)
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  have hDcardOdd : Odd (Nat.card D) := by
    apply Nat.not_even_iff_odd.mp
    intro hDcardEven
    have htwoD : 2 ∣ Nat.card D := even_iff_two_dvd.mp hDcardEven
    obtain ⟨t, htorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := D) 2 htwoD
    have htne : t ≠ 1 := by
      intro ht
      subst t
      simp at htorder
    have htsq : t ^ 2 = 1 := by
      rw [← htorder]
      exact pow_orderOf_eq_one t
    have htsq_stabilizer :
        (t : MulAction.stabilizer G a) ^ 2 = 1 := by
      simpa using congrArg Subtype.val htsq
    let : F.Normal := hFrob.normal
    let phi : MulAut F :=
      MulAut.conjNormal (H := F) (t : MulAction.stabilizer G a)
    have hphi_sq : phi ^ 2 = 1 := by
      change (MulAut.conjNormal (H := F)
        (t : MulAction.stabilizer G a)) ^ 2 = 1
      rw [← map_pow, htsq_stabilizer, map_one]
    have hphi_involutive : Function.Involutive phi := by
      intro x
      have hx := congrArg (fun psi : MulAut F => psi x) hphi_sq
      simpa [pow_two] using hx
    have hphi_fixedPointFree : MonoidHom.FixedPointFree phi := by
      intro x hx
      have hconj :
          (t : MulAction.stabilizer G a) *
                (x : MulAction.stabilizer G a) *
              (t : MulAction.stabilizer G a)⁻¹ =
            (x : MulAction.stabilizer G a) := by
        simpa [phi] using congrArg Subtype.val hx
      have hcomm :
          (t : MulAction.stabilizer G a) *
              (x : MulAction.stabilizer G a) =
            (x : MulAction.stabilizer G a) *
              (t : MulAction.stabilizer G a) := by
        calc
          (t : MulAction.stabilizer G a) *
                (x : MulAction.stabilizer G a) =
              ((t : MulAction.stabilizer G a) *
                  (x : MulAction.stabilizer G a) *
                (t : MulAction.stabilizer G a)⁻¹) *
                  (t : MulAction.stabilizer G a) := by
            simp [mul_assoc]
          _ = (x : MulAction.stabilizer G a) *
                (t : MulAction.stabilizer G a) := by rw [hconj]
      have hcent :=
        (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
          hFrob.normal hFrob.isComplement').mp hFrob t htne
      have hxcent :
          (x : MulAction.stabilizer G a) ∈
            elementCentralizerIn F (t : MulAction.stabilizer G a) :=
        ⟨x.property,
          Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
      rw [hcent] at hxcent
      exact Subtype.ext (Subgroup.mem_bot.mp hxcent)
    apply hFnoncomm
    refine ⟨⟨fun x y => ?_⟩⟩
    exact (hphi_fixedPointFree.commute_all_of_involutive
      hphi_involutive x y).eq
  have hpointStabilizerOdd :
      Odd (Nat.card (MulAction.stabilizer G a)) :=
    xi91_pointStabilizer_card_odd
      a b hab F hFrob p hp hp2 hFp hDcardOdd
  have hpretransitive : MulAction.IsPretransitive G Omega := by
    let : MulAction.IsMultiplyPretransitive G Omega 2 :=
      htwo_transitive
    exact MulAction.isPretransitive_of_is_two_pretransitive
  have hinvolution_fixedPointFree :
      ∀ t : G, orderOf t = 2 → ∀ x : Omega, t • x ≠ x := by
    intro t ht
    exact xi91_involution_fixedPointFree_of_odd_stabilizer
      hpretransitive a hpointStabilizerOdd t ht
  obtain ⟨s, hssq, hsa, hsb⟩ :=
    xi91_odd_twoPointStabilizer_exists_swap_involution
      htwo_transitive hat_most_two_fixed_points
      a b hab F hFrob hDcardOdd
  have hsne : s ≠ 1 := by
    intro hs
    apply hab
    simpa [hs] using hsa
  have hsorder : orderOf s = 2 := orderOf_eq_prime hssq hsne
  have hsfixedPointFree : ∀ x : Omega, s • x ≠ x :=
    hinvolution_fixedPointFree s hsorder
  have hsimple :
      ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤ := by
    by_contra hsimple
    push Not at hsimple
    obtain ⟨N, hNnormal, hNne, hNtop⟩ := hsimple
    have hNtwo : MulAction.IsMultiplyPretransitive N Omega 2 :=
      xi91_zassenhaus_nontrivial_normal_is_two_pretransitive
        htwo_transitive hno_regular_normal a b hab F hFrob
        N hNnormal hNne
    have hatN :
        ∀ g : N, g ≠ 1 →
          ∀ x y z : Omega,
            x ≠ y → x ≠ z → y ≠ z →
              ¬ (g • x = x ∧ g • y = y ∧ g • z = z) := by
      intro g hg x y z hxy hxz hyz hfix
      apply hat_most_two_fixed_points ((g : N) : G)
      · intro hgG
        apply hg
        apply Subtype.ext
        exact hgG
      · exact hxy
      · exact hxz
      · exact hyz
      · exact hfix
    have hnoN :
        ¬ ∃ R : Subgroup N, R.Normal ∧ R ≠ ⊥ ∧
          ∀ x y : Omega, ∃! r : R, (r : N) • x = y :=
      xi91_zassenhaus_normal_subgroup_no_regular_normal
        N hNnormal a hNtwo hno_regular_normal
    obtain ⟨Fother, hFother⟩ :=
      huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
        hNtwo hatN hnoN a b hab
    let H := MulAction.stabilizer G a
    let Na : Subgroup (MulAction.stabilizer G a) := N.comap H.subtype
    have hFNa : F ≤ Na := by
      simpa [H, Na] using
        xi91_zassenhaus_normal_stabilizer_contains_frobeniusKernel
          htwo_transitive hno_regular_normal a b hab F hFrob
          N hNnormal hNne
    let HN := MulAction.stabilizer N a
    let eNa : Na ≃* HN := normalSubgroup_pointStabilizerEquiv N a
    let DNa : Subgroup Na := D.comap Na.subtype
    let DN : Subgroup HN :=
      MulAction.stabilizer HN
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer N a)
    have hDmap : DNa.map eNa.toMonoidHom = DN := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hyD, hyx⟩
        apply MulAction.mem_stabilizer_iff.mpr
        apply Subtype.ext
        have hyfix := MulAction.mem_stabilizer_iff.mp hyD
        have hyfixOmega :
            (((y : Na) : H) : G) • b = b :=
          congrArg Subtype.val hyfix
        rw [← hyx]
        calc
          ((eNa.toMonoidHom y : HN) : G) • b = (((y : Na) : H) : G) • b := by
            dsimp [eNa, normalSubgroup_pointStabilizerEquiv]
            rfl
          _ = b := hyfixOmega
      · intro hx
        let y : Na := eNa.symm x
        refine ⟨y, ?_, eNa.apply_symm_apply x⟩
        change ((y : Na) : H) ∈ D
        apply MulAction.mem_stabilizer_iff.mpr
        apply Subtype.ext
        have hxfix := MulAction.mem_stabilizer_iff.mp hx
        have hxfixOmega : (((x : HN) : N) : G) • b = b :=
          congrArg Subtype.val hxfix
        calc
          (((y : Na) : H) : G) • b = ((eNa.symm x : Na) : G) • b := rfl
          _ = (((x : HN) : N) : G) • b := by
            dsimp [eNa, normalSubgroup_pointStabilizerEquiv]
            rfl
          _ = b := hxfixOmega
    have hDNne : DN ≠ ⊥ := by
      simpa [HN, DN] using hFother.complement_ne_bot
    have hDNa_ne : DNa ≠ ⊥ := by
      intro hbot
      apply hDNne
      rw [← hDmap, hbot]
      simp
    have hFrobNa :
        IsFrobeniusGroupWithKernelComplement
          (F.subgroupOf Na) DNa := by
      simpa [H, DNa] using
        xi91_frobenius_restrict_to_subgroup_containing_kernel
          F D Na hFrob hFNa (by simpa [DNa] using hDNa_ne)
    let FN : Subgroup HN := (F.subgroupOf Na).map eNa.toMonoidHom
    have hFrobN : IsFrobeniusGroupWithKernelComplement FN DN := by
      have hmap := hFrobNa.map_mulEquiv eNa
      rw [hDmap] at hmap
      simpa [FN] using hmap
    let eFsub : F.subgroupOf Na ≃* F :=
      Subgroup.subgroupOfEquivOfLe hFNa
    let eFN : F.subgroupOf Na ≃* FN := by
      simpa [FN] using
        (Subgroup.equivMapOfInjective
          (F.subgroupOf Na) eNa.toMonoidHom eNa.injective)
    let eFtoFN : F ≃* FN := eFsub.symm.trans eFN
    have hFNnoncomm : ¬ IsMulCommutative FN := by
      intro hFNcomm
      apply hFnoncomm
      let : IsMulCommutative FN := hFNcomm
      refine ⟨⟨fun x y => ?_⟩⟩
      apply eFtoFN.injective
      simpa only [map_mul] using mul_comm' (eFtoFN x) (eFtoFN y)
    have hFNp : IsPGroup p FN := by
      have hFsubp : IsPGroup p (F.subgroupOf Na) :=
        hFp.of_equiv eFsub.symm
      exact hFsubp.of_equiv eFN
    have hDNZ : IsZGroup DN := by
      let : IsZGroup D := by simpa [D] using hDZ
      let iDNa : DNa →* D :=
        { toFun := fun x => ⟨((x : DNa) : Na), x.property⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hiDNa : Function.Injective iDNa := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : D => (z : H)) hxy
      let : IsZGroup DNa :=
        IsZGroup.of_injective (f := iDNa) hiDNa
      rw [← hDmap]
      exact IsZGroup.of_injective
        (f := (Subgroup.equivMapOfInjective
          DNa eNa.toMonoidHom eNa.injective).symm.toMonoidHom)
        (Subgroup.equivMapOfInjective
          DNa eNa.toMonoidHom eNa.injective).symm.injective
    have hcardN : Nat.card N < Nat.card G := by
      have hNlt : N < (⊤ : Subgroup G) :=
        lt_of_le_of_ne le_top hNtop
      simpa using natCard_lt_of_subgroup_lt hNlt
    have hpN2 :=
      huppert_XI_9_1_noncommutativeKernel_zGroupComplement_aux
        n hdegree hNtwo hatN hnoN a b hab FN hFrobN
        p hp hFNnoncomm hFNp hDNZ
    exact hp2 hpN2
  have hDcyclic : IsCyclic D := by
    simpa [D] using
      xi91_odd_twoPointStabilizer_isCyclic
        htwo_transitive hat_most_two_fixed_points hsimple
        a b hab F hFrob hDcardOdd
  have hsInvertsD :
      ∀ x : D,
        s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
          ((((x⁻¹ : D) : MulAction.stabilizer G a) : G)) := by
    exact xi91_odd_twoPointStabilizer_swap_inverts
      htwo_transitive hat_most_two_fixed_points hsimple
      a b hab F hFrob hDcardOdd s hsa hsb
  have hpointStabilizerOddAll :
      ∀ x : Omega, Odd (Nat.card (MulAction.stabilizer G x)) := by
    intro x
    let : MulAction.IsPretransitive G Omega := hpretransitive
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a x
    rw [show Nat.card (MulAction.stabilizer G x) =
        Nat.card (MulAction.stabilizer G a) by
      exact Nat.card_congr
        (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv.symm]
    exact hpointStabilizerOdd
  have hpairOdd :
      ∀ x y : Omega, ∀ hxy : x ≠ y,
        Odd (Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G x)
            (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x))) := by
    intro x y hxy
    apply Nat.not_even_iff_odd.mp
    intro heven
    have htwoD : 2 ∣ Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G x)
          (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x)) :=
      even_iff_two_dvd.mp heven
    have htwoH : 2 ∣ Nat.card (MulAction.stabilizer G x) :=
      htwoD.trans (Subgroup.card_subgroup_dvd_card
        (MulAction.stabilizer (MulAction.stabilizer G x)
          (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x)))
    exact (Nat.not_even_iff_odd.mpr (hpointStabilizerOddAll x))
      (even_iff_two_dvd.mpr htwoH)
  have hswapInverts :
      ∀ x y : Omega, ∀ hxy : x ≠ y, ∀ t : G,
        t • x = y → t • y = x →
          ∀ z : MulAction.stabilizer (MulAction.stabilizer G x)
            (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x),
            t * (((z : MulAction.stabilizer G x) : G)) * t⁻¹ =
              ((((z⁻¹ : MulAction.stabilizer
                (MulAction.stabilizer G x)
                (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x)) :
                  MulAction.stabilizer G x) : G)) := by
    intro x y hxy t htx hty
    obtain ⟨Fxy, hFxy⟩ :=
      huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
        htwo_transitive hat_most_two_fixed_points hno_regular_normal
        x y hxy
    exact xi91_odd_twoPointStabilizer_swap_inverts
      htwo_transitive hat_most_two_fixed_points hsimple
      x y hxy Fxy hFxy (hpairOdd x y hxy) t htx hty
  have hcentralizerFree :
      ∀ g : G, (∀ x : Omega, g • x ≠ x) →
        ∀ c : Subgroup.centralizer ({g} : Set G), c ≠ 1 →
          ∀ x : Omega, (c : G) • x = x → False :=
    xi91_derangement_centralizer_fixedPointFree
      hat_most_two_fixed_points hpairOdd hswapInverts
  have hnoProdF :
      ∀ z : F, z ≠ 1 →
        ¬ ∃ t₁ t₂ : G,
          orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧
            t₁ * t₂ = (((z : MulAction.stabilizer G a) : G)) :=
    xi91_frobeniusKernel_nontrivial_not_product_involutions
      htwo_transitive a b hab F hFrob hinvolution_fixedPointFree
  have hinvolutionCardUpper :
      Nat.card {t : G // orderOf t = 2} ≤ Nat.card F * Nat.card D := by
    simpa [D] using
      xi91_involutions_card_le_kernel_mul_complement
        htwo_transitive a b hab F hFrob hinvolution_fixedPointFree hnoProdF
  have hclassCardLower :
      Nat.card F * Nat.card D ≤ Nat.card (ConjClasses.mk s).carrier := by
    simpa [D] using
      xi91_involution_class_card_ge_kernel_mul_complement
        htwo_transitive a b hab F hFrob s hsfixedPointFree
        (hcentralizerFree s hsfixedPointFree)
  let Inv := {t : G // orderOf t = 2}
  let classToInv : (ConjClasses.mk s).carrier → Inv := fun x =>
    ⟨x.1, by
      have hmk := ConjClasses.mem_carrier_iff_mk_eq.mp x.2
      rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hmk) with ⟨c, hc⟩
      exact hc.orderOf_eq.trans hsorder⟩
  have hclassToInv : Function.Injective classToInv := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Inv => (z : G)) hxy
  have hclassCardUpper :
      Nat.card (ConjClasses.mk s).carrier ≤ Nat.card Inv :=
    Nat.card_le_card_of_injective classToInv hclassToInv
  have hinvolutionCard : Nat.card Inv = Nat.card F * Nat.card D := by
    apply Nat.le_antisymm hinvolutionCardUpper
    exact hclassCardLower.trans hclassCardUpper
  have hclassSurj : Function.Surjective classToInv :=
    (hclassToInv.bijective_of_nat_card_le
      (hinvolutionCardUpper.trans hclassCardLower)).2
  have hallInvolutionsConj :
      ∀ t : G, orderOf t = 2 → IsConj t s := by
    intro t ht
    obtain ⟨x, hx⟩ := hclassSurj ⟨t, ht⟩
    have hxt : x.1 = t := congrArg Subtype.val hx
    have hxconj : IsConj x.1 s :=
      ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)
    simpa [hxt] using hxconj
  have hFcard : Nat.card F = n := by
    exact huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
      n hdegree htwo_transitive a b hab F hFrob
  have hinvolutionCardND : Nat.card Inv = n * Nat.card D := by
    rw [hinvolutionCard, hFcard]
  let H := MulAction.stabilizer G a
  let : F.Normal := hFrob.normal
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let : Group.IsNilpotent F :=
    IsPGroup.isNilpotent (p := p) (G := F) hFp
  let : Group.IsSolvable F := IsNilpotent.to_isSolvable
  let : Nontrivial F :=
    (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot
  obtain ⟨chi, hchi⟩ :=
    Section6.exists_nontrivial_linear_character_of_solvable F
  let lambda : ClassFunction H :=
    inducedCF F (xi91_linearCharacterRepresentation chi).character
  let Phi : ClassFunction G := inducedCF H lambda
  have hlambdaIrr : IsIrreducibleCharacterOnGroup lambda := by
    exact xi91_linearCharacter_induced_irreducible F D hFrob chi hchi
  have hPhiChar : IsCharacter Phi := by
    exact isCharacter_inducedCF_of_isCharacter H lambda
      (isCharacter_of_isIrreducibleCharacterOnGroup hlambdaIrr)
  have hPhiNorm : scalarProduct G Phi Phi = (Nat.card D + 1 : ℂ) := by
    simpa [H, D, lambda, Phi] using
      xi91_linearCharacter_ambient_induced_norm
        htwo_transitive n hdegree a b hab F hFrob hFcard chi hchi
  have hPhiIndicator : xi91_classFunctionIndicator G Phi = (Nat.card D : ℂ) := by
    simpa [H, D, lambda, Phi] using
      xi91_linearCharacter_ambient_induced_indicator
        htwo_transitive a b hab F hFrob n hFcard hpointStabilizerOdd
          hinvolutionCardND chi hchi
  have hPhiNe : Phi ≠ 0 := by
    intro hzero
    have hz : (0 : ℂ) = (Nat.card D + 1 : ℂ) := by
      simpa [hzero, scalarProduct] using hPhiNorm
    have hzNat : 0 = Nat.card D + 1 := by exact_mod_cast hz
    omega
  obtain ⟨I, hIFintype, hIDecidable, e, psi, iBase,
      hepos, hpsi, hpair, hdecomp⟩ :=
    exists_positive_irreducible_decomposition_of_character Phi hPhiChar hPhiNe
  let : Fintype I := hIFintype
  let : DecidableEq I := hIDecidable
  obtain ⟨i0, hei0, hpsi0Nonreal, hpsiOtherReal⟩ :=
    xi91_positive_decomposition_unique_nonreal
      Phi e psi hepos hpsi hpair hdecomp (Nat.card D)
        hPhiNorm hPhiIndicator
  let chi2 : ClassFunction G := conjugateCharacter (psi i0)
  have hchi2Irr : IsBookIrreducibleCharacter chi2 := by
    apply isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
    exact isIrreducibleCharacterOnGroup_conjugateCharacter
      (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        (psi i0) (hpsi i0))
  have hchi2Ne : chi2 ≠ psi i0 := by
    intro hEq
    exact hpsi0Nonreal hEq.symm
  have hPhiDiff :
      Phi - conjugateCharacter Phi = psi i0 - chi2 := by
    ext g
    rw [hdecomp]
    simp only [Pi.sub_apply, weightedFamilySum, conjugateCharacter]
    rw [star_sum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i0]
    · simp [hei0, chi2, conjugateCharacter]
    · intro i _hi hine
      rw [(hpsiOtherReal i hine).1]
      have hreal := congrFun (hpsiOtherReal i hine).2 g
      change psi i g = star (psi i g) at hreal
      exact sub_eq_zero.mpr (by simpa using hreal)
    · intro hi
      simp at hi
  obtain ⟨B, hBirr, hBcard, hBmem⟩ :=
    huppert_XI_5_3_nonprincipal_induced_family
      htwo_transitive a b hab F D hFrob rfl hDcyclic hDcardOdd
        s hsa hsb hsInvertsD
  have hHindex : H.index = n + 1 := by
    calc
      H.index = Nat.card Omega := by
        exact MulAction.index_stabilizer_of_transitive G a
      _ = Fintype.card Omega := Nat.card_eq_fintype_card
      _ = n + 1 := hdegree
  have hBdegree : ∀ beta : B,
      degree (beta : ClassFunction G) = (n + 1 : ℂ) := by
    intro beta
    rcases (hBmem (beta : ClassFunction G)).mp beta.property with
      ⟨eta, heta, hbeta⟩
    rw [← hbeta]
    have hdeg := degree_inducedClassFunction H
      (characterInflationByHom (QuotientGroup.mk' F) eta)
    rw [hHindex] at hdeg
    simpa [degree, characterInflationByHom] using hdeg
  have hBreal : ∀ beta : B,
      (beta : ClassFunction G) =
        conjugateCharacter (beta : ClassFunction G) := by
    intro beta
    rcases (hBmem (beta : ClassFunction G)).mp beta.property with
      ⟨eta, heta, hbeta⟩
    let Q := MulAction.stabilizer G a ⧸ F
    let q : MulAction.stabilizer G a →* Q := QuotientGroup.mk' F
    let inflate : (Q →* ℂˣ) → ClassFunction H :=
      fun z => characterInflationByHom q z
    let ind : (Q →* ℂˣ) → ClassFunction G :=
      fun z => inducedCF H (inflate z)
    have hpair : ∀ z w : Q →* ℂˣ,
        scalarProduct G (ind z) (ind w) =
          (if z = w then 1 else 0) + (if z = w⁻¹ then 1 else 0) := by
      intro z w
      simpa [H, q, inflate, ind] using
        (huppert_XI_5_3_quotient_linear_induced_pairing
          htwo_transitive a b hab F D hFrob s hsa hsb rfl
            hsInvertsD z w)
    have hirrEta : IsIrreducibleCharacterOnGroup (ind eta) := by
      change IsIrreducibleCharacterOnGroup
        (inducedCF H
          (characterInflationByHom (QuotientGroup.mk' F) eta))
      rw [hbeta]
      exact hBirr beta
    have hetaInvNe : eta ≠ eta⁻¹ := by
      intro hfix
      have hnorm := hpair eta eta
      rw [if_pos rfl, if_pos hfix] at hnorm
      have hirrNorm := scalarProduct_irreducibleCharacter_self hirrEta
      rw [hirrNorm] at hnorm
      norm_num at hnorm
    have hetaInvOne : eta⁻¹ ≠ 1 := by
      intro h
      apply heta
      calc
        eta = (eta⁻¹)⁻¹ := by
          ext x; simp
        _ = 1⁻¹ := by rw [h]
        _ = 1 := by ext x; simp
    have hInvMem : ind eta⁻¹ ∈ B := by
      apply (hBmem (ind eta⁻¹)).mpr
      exact ⟨eta⁻¹, hetaInvOne, by rfl⟩
    have hirrInv : IsIrreducibleCharacterOnGroup (ind eta⁻¹) :=
      hBirr ⟨ind eta⁻¹, hInvMem⟩
    have hpairInv : scalarProduct G (ind eta) (ind eta⁻¹) = 1 := by
      rw [hpair, if_neg hetaInvNe, if_pos (inv_inv eta).symm]
      norm_num
    have hIndInv : ind eta⁻¹ = ind eta := by
      by_contra hne
      have hzero := scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hirrEta hirrInv (Ne.symm hne)
      rw [hpairInv] at hzero
      norm_num at hzero
    have hconj : conjugateCharacter (ind eta) = ind eta⁻¹ := by
      have h := xi91_conjugateCharacter_inducedCF H (inflate eta)
      rw [huppert_XI_5_3_characterInflationByHom_conjugate_eq_inv] at h
      simpa [ind, inflate, q] using h
    calc
      (beta : ClassFunction G) = ind eta := hbeta.symm
      _ = ind eta⁻¹ := hIndInv.symm
      _ = conjugateCharacter (ind eta) := hconj.symm
      _ = conjugateCharacter (beta : ClassFunction G) :=
        congrArg conjugateCharacter hbeta
  have hPhiBetaProduct : ∀ beta : B,
      (Phi - conjugateCharacter Phi) *
        ((beta : ClassFunction G) - principalCharacter G) = 0 := by
    intro beta
    rcases (hBmem (beta : ClassFunction G)).mp beta.property with
      ⟨eta, _heta, hbeta⟩
    ext g
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply]
    by_cases hgOne : g = 1
    · subst g
      rcases hPhiChar with ⟨V, _hadd, _hmod, _hfd, rho, hPhiEq⟩
      have hPhiOne : star (Phi 1) = Phi 1 := by
        rw [hPhiEq]
        simp [Representation.character]
      rw [show conjugateCharacter Phi 1 = star (Phi 1) by rfl, hPhiOne]
      simp
    by_cases hex : ∃ x : G, ∃ hxH : x * g * x⁻¹ ∈ H,
        (⟨x * g * x⁻¹, hxH⟩ : H) ∈ F
    · rcases hex with ⟨x, hxH, hxF⟩
      let zH : H := ⟨x * g * x⁻¹, hxH⟩
      let z : F := ⟨zH, hxF⟩
      have hzNe : z ≠ 1 := by
        intro hz
        apply hgOne
        have hzG : x * g * x⁻¹ = 1 := by
          simpa [z, zH] using congrArg (fun w : F => (((w : H) : G))) hz
        have := congrArg (fun w : G => x⁻¹ * w * x) hzG
        simpa [mul_assoc] using this
      have hyData : ∀ y : G, ∀ hyH : y * g * y⁻¹ ∈ H,
          y * x⁻¹ ∈ H ∧
            (⟨y * g * y⁻¹, hyH⟩ : H) ∈ F := by
        intro y hyH
        have hygFixA : (y * g * y⁻¹) • a = a := hyH
        have hgFix : g • (y⁻¹ • a) = y⁻¹ • a := by
          apply (MulAction.toPerm y).injective
          simpa [mul_smul] using hygFixA
        have hzFix : (((z : H) : G)) • (x • (y⁻¹ • a)) =
            x • (y⁻¹ • a) := by
          calc
            (((z : H) : G)) • (x • (y⁻¹ • a)) =
                x • (g • (y⁻¹ • a)) := by
                  simp only [z, zH, mul_smul, inv_smul_smul]
            _ = x • (y⁻¹ • a) := by rw [hgFix]
        have hpoint : x • (y⁻¹ • a) = a :=
          (xi91_frobeniusKernel_uniqueFixedPoint
            htwo_transitive a b hab F hFrob z hzNe
              (x • (y⁻¹ • a))).mp hzFix
        have hxyPoint : y⁻¹ • a = x⁻¹ • a := by
          calc
            y⁻¹ • a = x⁻¹ • (x • (y⁻¹ • a)) := by simp
            _ = x⁻¹ • a := by rw [hpoint]
        have hkH : y * x⁻¹ ∈ H := by
          change (y * x⁻¹) • a = a
          simp only [mul_smul]
          rw [← hxyPoint, smul_inv_smul]
        let k : H := ⟨y * x⁻¹, hkH⟩
        have hyEq : (⟨y * g * y⁻¹, hyH⟩ : H) =
            k * (z : H) * k⁻¹ := by
          apply Subtype.ext
          simp only [k, z, zH, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        refine ⟨hkH, ?_⟩
        rw [hyEq]
        exact hFrob.normal.conj_mem (z : H) z.property k
      let S := {y : G // y * g * y⁻¹ ∈ H}
      let eS : H ≃ S :=
        { toFun := fun h => ⟨(h : G) * x, by
            show ((h : G) * x) * g * ((h : G) * x)⁻¹ ∈ H
            have hzH : x * g * x⁻¹ ∈ H := hxH
            have hconj : ((h : G) * x) * g * ((h : G) * x)⁻¹ =
                (h : G) * (x * g * x⁻¹) * (h : G)⁻¹ := by group
            rw [hconj]
            exact H.mul_mem (H.mul_mem h.property hzH) (H.inv_mem h.property)⟩
          invFun := fun y => ⟨y.1 * x⁻¹, (hyData y.1 y.2).1⟩
          left_inv := by
            intro h
            apply Subtype.ext
            simp
          right_inv := by
            intro y
            apply Subtype.ext
            simp }
      have hsum :
          (∑ y : G, if hyH : y * g * y⁻¹ ∈ H then
              characterInflationByHom (QuotientGroup.mk' F) eta
                ⟨y * g * y⁻¹, hyH⟩ else 0) =
            (Nat.card H : ℂ) := by
        calc
          (∑ y : G, if hyH : y * g * y⁻¹ ∈ H then
              characterInflationByHom (QuotientGroup.mk' F) eta
                ⟨y * g * y⁻¹, hyH⟩ else 0) =
              ∑ y : G, if y * g * y⁻¹ ∈ H then (1 : ℂ) else 0 := by
                apply Finset.sum_congr rfl
                intro y _hy
                split
                next hyH =>
                  have hyF := (hyData y hyH).2
                  have hq :
                      (QuotientGroup.mk' F)
                        (⟨y * g * y⁻¹, hyH⟩ : H) = 1 :=
                    (QuotientGroup.eq_one_iff (N := F) _).2 hyF
                  simp [characterInflationByHom, hq]
                next => rfl
          _ = ∑ y ∈ (Finset.univ.filter
                (fun y : G => y * g * y⁻¹ ∈ H)), (1 : ℂ) := by
            rw [Finset.sum_filter]
          _ = (Nat.card S : ℂ) := by
            simp [S, Nat.card_eq_fintype_card, Fintype.card_subtype]
          _ = (Nat.card H : ℂ) := by
            exact_mod_cast (Nat.card_congr eS).symm
      have hbetaOne : (beta : ClassFunction G) g = 1 := by
        rw [← hbeta]
        change (Nat.card H : ℂ)⁻¹ *
            (∑ y : G, if hyH : y * g * y⁻¹ ∈ H then
              characterInflationByHom (QuotientGroup.mk' F) eta
                ⟨y * g * y⁻¹, hyH⟩ else 0) = 1
        rw [hsum]
        field_simp [show (Nat.card H : ℂ) ≠ 0 by
          exact_mod_cast (Nat.card_pos (α := H)).ne']
      simp [hbetaOne, principalCharacter]
    · have hPhiZero : Phi g = 0 := by
        change (Nat.card H : ℂ)⁻¹ *
            (∑ x : G, if hxH : x * g * x⁻¹ ∈ H then
              lambda ⟨x * g * x⁻¹, hxH⟩ else 0) = 0
        apply mul_eq_zero_of_right
        apply Finset.sum_eq_zero
        intro x _hx
        split
        next hxH =>
          apply xi91_induced_linearCharacter_support F chi
          intro hxF
          exact hex ⟨x, hxH, hxF⟩
        next => rfl
      rw [show conjugateCharacter Phi g = star (Phi g) by rfl,
        hPhiZero]
      simp
  let Pi : ClassFunction G := inducedCF H (principalCharacter H)
  have hprincipalHBook :
      IsBookIrreducibleCharacter (principalCharacter H) :=
    xi91_principalCharacter_isBookIrreducible
  have hprincipalGBook :
      IsBookIrreducibleCharacter (principalCharacter G) :=
    xi91_principalCharacter_isBookIrreducible
  have hprincipalDBook :
      IsBookIrreducibleCharacter (principalCharacter D) :=
    xi91_principalCharacter_isBookIrreducible
  have hPiChar : IsCharacter Pi := by
    exact isCharacter_inducedCF_of_isCharacter H (principalCharacter H)
      hprincipalHBook.1
  have hprincipalHSelf :
      scalarProduct H (principalCharacter H) (principalCharacter H) = 1 :=
    scalarProduct_irreducibleCharacter_self
      (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        (principalCharacter H) hprincipalHBook)
  have hprincipalDSelf :
      scalarProduct D (principalCharacter D) (principalCharacter D) = 1 :=
    scalarProduct_irreducibleCharacter_self
      (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        (principalCharacter D) hprincipalDBook)
  have hPiNorm : scalarProduct G Pi Pi = 2 := by
    have hpairPi := huppert_XI_5_3_ambient_induced_pairing
      htwo_transitive a b hab s hsa hsb hsInvertsD
        (principalCharacter H) (principalCharacter H)
        (isBookIrreducibleCharacter_isClassFunction
          (principalCharacter H) hprincipalHBook)
        (isBookIrreducibleCharacter_isClassFunction
          (principalCharacter H) hprincipalHBook)
        hprincipalHBook.1
    have hcross :
        scalarProduct D
          (subgroupRestriction D (principalCharacter H))
          (conjugateCharacter
            (subgroupRestriction D (principalCharacter H))) = 1 := by
      have hresPrincipal :
          subgroupRestriction D (principalCharacter H) =
            principalCharacter D := by
        ext z
        rfl
      rw [hresPrincipal, conjugateCharacter_principalCharacter]
      exact hprincipalDSelf
    calc
      scalarProduct G Pi Pi = 1 + 1 := by
        simpa [Pi, H, D, hprincipalHSelf, hcross] using hpairPi
      _ = 2 := by norm_num
  have hPiPrincipal :
      scalarProduct G Pi (principalCharacter G) = 1 := by
    calc
      scalarProduct G Pi (principalCharacter G) =
          scalarProduct H (principalCharacter H)
            (subgroupRestriction H (principalCharacter G)) := by
        exact scalarProduct_inducedCF_left H (principalCharacter H)
          (principalCharacter G)
          (isBookIrreducibleCharacter_isClassFunction
            (principalCharacter G) hprincipalGBook)
      _ = 1 := by
        have hsub : subgroupRestriction H (principalCharacter G) = principalCharacter H := by
          ext x; simp [subgroupRestriction, principalCharacter]
        simpa [hsub] using hprincipalHSelf
  obtain ⟨alpha, halphaBook, halphaNePrincipal, hPiSplit⟩ :=
    xi91_norm_two_principal_split Pi hPiChar hPiNorm hPiPrincipal
  have hDgt : 1 < Nat.card D :=
    (Subgroup.one_lt_card_iff_ne_bot D).2 hFrob.complement_ne_bot
  have hlambdaDegree : degree lambda = (Nat.card D : ℂ) := by
    simpa [degree, lambda] using
      xi91_induced_linearCharacter_degree F D hFrob chi
  have hlambdaNePrincipal : lambda ≠ principalCharacter H := by
    intro hEq
    have hdegEq := congrArg degree hEq
    rw [hlambdaDegree] at hdegEq
    simp [degree, principalCharacter] at hdegEq
    have hDcardOneF : Fintype.card D = 1 := by
      exact_mod_cast hdegEq
    have hDcardOne : Nat.card D = 1 := by
      simpa [Nat.card_eq_fintype_card] using hDcardOneF
    exact (Nat.ne_of_gt hDgt) hDcardOne
  have hlambdaPrincipal :
      scalarProduct H lambda (principalCharacter H) = 0 := by
    exact scalarProduct_isBookIrreducible_ne lambda (principalCharacter H)
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hlambdaIrr)
      hprincipalHBook hlambdaNePrincipal
  have hPhiPrincipal :
      scalarProduct G Phi (principalCharacter G) = 0 := by
    calc
      scalarProduct G Phi (principalCharacter G) =
          scalarProduct H lambda
            (subgroupRestriction H (principalCharacter G)) := by
        exact scalarProduct_inducedCF_left H lambda (principalCharacter G)
          (isBookIrreducibleCharacter_isClassFunction
            (principalCharacter G) hprincipalGBook)
      _ = 0 := by
        have hsub : subgroupRestriction H (principalCharacter G) = principalCharacter H := by
          ext x; simp [subgroupRestriction, principalCharacter]
        simpa [hsub] using hlambdaPrincipal
  have hlambdaOnD : ∀ z : D,
      subgroupRestriction D lambda z =
        if z = 1 then (Nat.card D : ℂ) else 0 := by
    intro z
    by_cases hz : z = 1
    · subst z
      rw [if_pos rfl]
      simpa [subgroupRestriction, degree] using hlambdaDegree
    · rw [if_neg hz]
      apply xi91_induced_linearCharacter_support F chi
      intro hzF
      have hzbot : ((z : H) : H) ∈ (⊥ : Subgroup H) :=
        hFrob.isComplement'.disjoint.le_bot ⟨hzF, z.property⟩
      apply hz
      apply Subtype.ext
      simpa using hzbot
  have hresLambdaPrincipal :
      scalarProduct D (subgroupRestriction D lambda)
        (conjugateCharacter
          (subgroupRestriction D (principalCharacter H))) = 1 := by
    unfold scalarProduct
    simp only [subgroupRestriction, conjugateCharacter, principalCharacter,
      star_one, mul_one]
    have hsum :
        (∑ z : D, lambda (z : H)) = (Nat.card D : ℂ) := by
      simp_rw [show ∀ z : D, lambda (z : H) =
          if z = 1 then (Nat.card D : ℂ) else 0 by
        intro z
        simpa [subgroupRestriction] using hlambdaOnD z]
      simp
    rw [show @Finset.univ D (Fintype.ofFinite D) =
        (Finset.univ : Finset D) by ext; simp]
    rw [hsum]
    exact inv_mul_cancel₀ (by
      exact_mod_cast (Nat.card_pos (α := D)).ne')
  have hPhiPi : scalarProduct G Phi Pi = 1 := by
    have hpairPhiPi := huppert_XI_5_3_ambient_induced_pairing
      htwo_transitive a b hab s hsa hsb hsInvertsD
        lambda (principalCharacter H)
        (isCharacter_isClassFunction lambda
          (isCharacter_of_isIrreducibleCharacterOnGroup hlambdaIrr))
        (isBookIrreducibleCharacter_isClassFunction
          (principalCharacter H) hprincipalHBook)
        hprincipalHBook.1
    have hpairPhiPi' :
        scalarProduct G Phi Pi =
          scalarProduct H lambda (principalCharacter H) +
            scalarProduct D (subgroupRestriction D lambda)
              (conjugateCharacter
                (subgroupRestriction D (principalCharacter H))) := by
      simpa only [Phi, Pi, H, D] using hpairPhiPi
    rw [hpairPhiPi', hlambdaPrincipal, hresLambdaPrincipal]
    norm_num
  have hPhiAlpha : scalarProduct G Phi alpha = 1 := by
    rw [hPiSplit, Section5.scalarProduct_add_right,
      hPhiPrincipal] at hPhiPi
    simpa using hPhiPi
  obtain ⟨iAlpha, hpsiAlpha, heAlpha⟩ :=
    xi91_decomposition_index_of_scalar_one
      Phi e psi hepos hpsi hpair hdecomp alpha halphaBook hPhiAlpha
  have hPiReal : Pi = conjugateCharacter Pi := by
    rw [xi91_conjugateCharacter_inducedCF H (principalCharacter H),
      conjugateCharacter_principalCharacter]
  have halphaReal : alpha = conjugateCharacter alpha := by
    ext g
    have hreal := congrFun hPiReal g
    rw [hPiSplit] at hreal
    change 1 + alpha g = star (1 + alpha g) at hreal
    simpa [conjugateCharacter] using congrArg (fun z : ℂ => z - 1) hreal
  have hiAlphaNe : iAlpha ≠ i0 := by
    intro hEq
    apply hpsi0Nonreal
    subst iAlpha
    rw [hpsiAlpha]
    exact halphaReal
  obtain ⟨degree0, hdegree0Pos, hdegree0⟩ :=
    Section6.theorem_6_6_positive_degree_nat_of_irreducible
      (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        (psi i0) (hpsi i0))
  /- XI.9.4(h), eigenvalue part: an involution has only `±1` eigenvalues. -/
  have hpsi0InvolutionValueReal : (psi i0 s).im = 0 := by
    obtain ⟨V, _hadd, _hmod, _hfd, rho, hpsiRho, _hrhoIrr⟩ :=
      isBookIrreducibleCharacter_representation_witness_irreducible
        (psi i0) (hpsi i0)
    have hsInv : s⁻¹ = s := inv_eq_self_of_orderOf_eq_two hsorder
    have hstar : star (psi i0 s) = psi i0 s := by
      calc
        star (psi i0 s) = rho.character s⁻¹ := by
          rw [hpsiRho]
          exact (representation_character_inv_eq_star_character rho s).symm
        _ = rho.character s := by rw [hsInv]
        _ = psi i0 s := by rw [hpsiRho]
    have him := congrArg Complex.im hstar
    simp at him
    linarith
  /- XI.9.4(h), support core: apply the involution class-sum test to the
  degree-zero difference between `lambda` and the inflated quotient-regular
  character.  The nonprincipal quotient terms vanish at the derangement `s`,
  leaving the same class-sum pairing for `Phi` and `Pi`. -/
  obtain ⟨omega, homegaClass, homegaCoefficient, hPhiOmegaEqPiOmega⟩ :
      ∃ omega : ClassFunction G,
        IsClassFunction omega ∧
        (∀ theta : ClassFunction G,
          IsIrreducibleCharacterOnGroup theta →
            scalarProduct G theta omega = theta s ^ 2 / theta 1) ∧
        scalarProduct G Phi omega = scalarProduct G Pi omega := by
    let Q := H ⧸ F
    let q : H →* Q := QuotientGroup.mk' F
    let inflate : (Q →* ℂˣ) → ClassFunction H := fun eta =>
      characterInflationByHom q eta
    let regH : ClassFunction H := familySum inflate
    let MuH : ClassFunction H := lambda - regH
    let Mu : ClassFunction G := inducedCF H MuH
    let eQD : Q ≃* D := hFrob.isComplement'.symm.QuotientMulEquiv
    have hQcyclic : IsCyclic Q := eQD.isCyclic.mpr hDcyclic
    let : IsCyclic Q := hQcyclic
    let : CommGroup Q := IsMulCommutative.instCommGroup
    let : Fintype (Q →* ℂˣ) := Fintype.ofFinite (Q →* ℂˣ)
    let : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) := by
      have : NeZero (Monoid.exponent Q) := by infer_instance
      exact complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
    have hker : ∀ z : H, q z = 1 ↔ z ∈ F := by
      intro z
      exact QuotientGroup.eq_one_iff (N := F) z
    have hFindex : F.index = Nat.card D :=
      hFrob.isComplement'.symm.index_eq_card
    have hMuSupport :
        ∀ g : G, Mu g ≠ 0 →
          ¬ ∃ t₁ t₂ : G,
            orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧ t₁ * t₂ = g := by
      intro g hMuNe hprod
      rcases hprod with ⟨t₁, t₂, ht₁, ht₂, htprod⟩
      apply hMuNe
      change (Nat.card H : ℂ)⁻¹ *
          (∑ y : G, if hyH : y * g * y⁻¹ ∈ H then
            MuH ⟨y * g * y⁻¹, hyH⟩ else 0) = 0
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro y _hy
      split
      next hyH =>
        let zH : H := ⟨y * g * y⁻¹, hyH⟩
        by_cases hzF : zH ∈ F
        · let z : F := ⟨zH, hzF⟩
          by_cases hzOne : z = 1
          · have hzHOne : zH = 1 := by
              apply Subtype.ext
              simpa [z] using congrArg (fun w : F => ((w : H) : G)) hzOne
            have hregular := characterInflationByHom_regular_sum
              F q hker rfl zH
            rw [if_pos hzF, hFindex] at hregular
            change lambda zH - regH zH = 0
            rw [hzHOne] at hregular ⊢
            change degree lambda - regH 1 = 0
            rw [hlambdaDegree]
            simpa [regH, inflate, familySum]
              using congrArg (fun w : ℂ => (Nat.card D : ℂ) - w) hregular
          · exfalso
            apply hnoProdF z hzOne
            refine ⟨y * t₁ * y⁻¹, y * t₂ * y⁻¹, ?_, ?_, ?_⟩
            · simpa [MulAut.conj_apply] using
                ((MulAut.conj y).orderOf_eq t₁).trans ht₁
            · simpa [MulAut.conj_apply] using
                ((MulAut.conj y).orderOf_eq t₂).trans ht₂
            · change (y * t₁ * y⁻¹) * (y * t₂ * y⁻¹) =
                y * g * y⁻¹
              rw [← htprod]
              group
        · have hlambdaZero : lambda zH = 0 :=
            xi91_induced_linearCharacter_support F chi zH hzF
          have hregular := characterInflationByHom_regular_sum
            F q hker rfl zH
          rw [if_neg hzF] at hregular
          change lambda zH - regH zH = 0
          rw [hlambdaZero]
          simpa [regH, inflate, familySum] using hregular
      next => rfl
    obtain ⟨omega, homegaClass, homegaCoefficient, homegaZero⟩ :=
      xi91_exists_involution_classSumTest s hsorder
    have hMuOmega : scalarProduct G Mu omega = 0 :=
      homegaZero Mu hMuSupport
    have hMuEq : Mu = Phi - inducedCF H regH := by
      change (inducedCFLinear H) (lambda - regH) =
        (inducedCFLinear H) lambda - (inducedCFLinear H) regH
      exact map_sub (inducedCFLinear H) lambda regH
    have hPhiEqReg :
        scalarProduct G Phi omega =
          scalarProduct G (inducedCF H regH) omega := by
      rw [hMuEq, Section5.scalarProduct_sub_left] at hMuOmega
      exact sub_eq_zero.mp hMuOmega
    have hinducedAtSZero :
        ∀ theta : ClassFunction H, inducedCF H theta s = 0 := by
      intro theta
      change (Nat.card H : ℂ)⁻¹ *
          (∑ y : G, if hyH : y * s * y⁻¹ ∈ H then
            theta ⟨y * s * y⁻¹, hyH⟩ else 0) = 0
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro y _hy
      split
      next hyH =>
        exfalso
        apply hsfixedPointFree (y⁻¹ • a)
        apply (MulAction.toPerm y).injective
        have hyFix : (y * s * y⁻¹) • a = a := hyH
        simpa [mul_smul] using hyFix
      next => rfl
    have hRegEqPi :
        scalarProduct G (inducedCF H regH) omega =
          scalarProduct G Pi omega := by
      rw [show inducedCF H regH =
          familySum (fun eta : Q →* ℂˣ => inducedCF H (inflate eta)) by
        simpa [regH] using inducedCF_familySum H inflate]
      unfold familySum
      rw [Section1.scalarProduct_fintype_sum_left]
      rw [Finset.sum_eq_single (1 : Q →* ℂˣ)]
      · have hIndOne : inducedCF H (inflate 1) = Pi := by
          change inducedCF H (inflate 1) =
            inducedCF H (principalCharacter H)
          congr 1
        rw [hIndOne]
      · intro eta _heta hne
        have hmem : inducedCF H (inflate eta) ∈ B := by
          apply (hBmem (inducedCF H (inflate eta))).2
          exact ⟨eta, hne, by rfl⟩
        have hirr := hBirr ⟨inducedCF H (inflate eta), hmem⟩
        rw [homegaCoefficient (inducedCF H (inflate eta)) hirr,
          hinducedAtSZero]
        simp
      · intro hnot
        exact (hnot (Finset.mem_univ 1)).elim
    exact ⟨omega, homegaClass, homegaCoefficient,
      hPhiEqReg.trans hRegEqPi⟩
  /- XI.9.4(h), class-sum part after cancelling the standard constituent:
  the remaining real constituents contribute a nonnegative remainder. -/
  have hclassSumRemainder :
      ∃ r : ℝ, 0 ≤ r ∧
        1 = (psi i0 s).re ^ 2 / (degree0 : ℝ) + r := by
    let T : I → ℂ := fun i => scalarProduct G (psi i) omega
    have heOne : ∀ i : I, e i = 1 := by
      intro i
      by_cases hi : i = i0
      · simpa [hi] using hei0
      · exact (hpsiOtherReal i hi).1
    have hPhiExpand : scalarProduct G Phi omega = ∑ i : I, T i := by
      rw [hdecomp, scalarProduct_weightedFamilySum_left]
      rw [show @Finset.univ I (Fintype.ofFinite I) =
          @Finset.univ I hIFintype by ext; simp]
      simp [T, heOne]
    have hprincipalOmega :
        scalarProduct G (principalCharacter G) omega = 1 := by
      rw [homegaCoefficient (principalCharacter G)
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (principalCharacter G) hprincipalGBook)]
      simp [principalCharacter]
    have hPiExpand : scalarProduct G Pi omega = 1 + T iAlpha := by
      rw [hPiSplit, Section1.scalarProduct_add_left, hprincipalOmega]
      simpa [T] using congrArg (fun theta : ClassFunction G =>
        scalarProduct G theta omega) hpsiAlpha.symm
    have htotal : ∑ i : I, T i = 1 + T iAlpha := by
      rw [← hPhiExpand, ← hPiExpand]
      exact hPhiOmegaEqPiOmega
    let S : Finset I := Finset.univ.erase iAlpha
    have hsumS : ∑ i ∈ S, T i = 1 := by
      have hsplit := Finset.sum_erase_add
        (s := (Finset.univ : Finset I)) T (Finset.mem_univ iAlpha)
      change (∑ i ∈ S, T i) + T iAlpha = ∑ i : I, T i at hsplit
      rw [htotal] at hsplit
      exact add_right_cancel hsplit
    have hi0S : i0 ∈ S := by
      dsimp [S]
      rw [Finset.mem_erase]
      exact ⟨Ne.symm hiAlphaNe, Finset.mem_univ _⟩
    let R : Finset I := S.erase i0
    have hsumR : T i0 + ∑ i ∈ R, T i = 1 := by
      have hsplit := Finset.sum_erase_add (s := S) T hi0S
      change (∑ i ∈ R, T i) + T i0 = ∑ i ∈ S, T i at hsplit
      rw [hsumS] at hsplit
      simpa [add_comm] using hsplit
    have hT0Re : (T i0).re =
        (psi i0 s).re ^ 2 / (degree0 : ℝ) := by
      rw [show T i0 = (psi i0 s) ^ 2 / psi i0 1 by
        exact homegaCoefficient (psi i0)
          (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
            (psi i0) (hpsi i0))]
      change ((psi i0 s) ^ 2 / degree (psi i0)).re = _
      rw [hdegree0]
      simp [Complex.div_re, hpsi0InvolutionValueReal, pow_two]
      field_simp
    have htermNonneg : ∀ i ∈ R, 0 ≤ (T i).re := by
      intro i hiR
      have hiS : i ∈ S := (Finset.mem_erase.mp hiR).2
      have hine0 : i ≠ i0 := (Finset.mem_erase.mp hiR).1
      have hreal := congrFun (hpsiOtherReal i hine0).2 s
      change psi i s = star (psi i s) at hreal
      have him : (psi i s).im = 0 := by
        have := congrArg Complex.im hreal
        simp at this
        linarith
      obtain ⟨di, hdiPos, hdi⟩ :=
        Section6.theorem_6_6_positive_degree_nat_of_irreducible
          (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
            (psi i) (hpsi i))
      rw [show T i = (psi i s) ^ 2 / psi i 1 by
        exact homegaCoefficient (psi i)
          (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
            (psi i) (hpsi i))]
      change 0 ≤ ((psi i s) ^ 2 / degree (psi i)).re
      rw [hdi]
      have hvalueFormula :
          (((psi i s) ^ 2 / (di : ℂ)).re) =
            (psi i s).re ^ 2 / (di : ℝ) := by
        simp [Complex.div_re, him, pow_two]
        field_simp
      rw [hvalueFormula]
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg di)
    refine ⟨(∑ i ∈ R, T i).re, ?_, ?_⟩
    · rw [Complex.re_sum]
      exact Finset.sum_nonneg htermNonneg
    · have hre := congrArg Complex.re hsumR
      simp [Complex.re_sum] at hre
      rw [hT0Re] at hre
      rw [Complex.re_sum]
      exact hre.symm
  have hinvolutionSquareBound :
      (psi i0 s).re ^ 2 ≤ (degree0 : ℝ) := by
    rcases hclassSumRemainder with ⟨r, hr, heq⟩
    have hdegree0PosR : (0 : ℝ) < degree0 := by exact_mod_cast hdegree0Pos
    have hquotientLe :
        (psi i0 s).re ^ 2 / (degree0 : ℝ) ≤ 1 := by
      nlinarith
    simpa using (div_le_iff₀ hdegree0PosR).mp hquotientLe
  /- XI.9.4(d)--(g), degree endpoint of the restriction calculation. -/
  have hrestrictionDegreeData :
      ∃ x : ℕ,
        0 < x ∧
        degree0 = Nat.card D * x ∧
        Nat.Coprime x p ∧
        Odd x := by
    /- XI.9.4(g): the restriction contains `lambda` once and every other
    constituent has degree divisible by the complement order. -/
    have hdegreeMultiple : ∃ x : ℕ,
        0 < x ∧ degree0 = Nat.card D * x := by
      have hpsi0NeAlpha : psi i0 ≠ alpha := by
        rw [← hpsiAlpha]
        exact hpair (Ne.symm hiAlphaNe)
      exact xi91_nonreal_restriction_degree_multiple
        H F D hFrob hDcyclic
        (psi i0) alpha (hpsi i0) hpsi0Nonreal
        halphaBook hpsi0NeAlpha
        (by simpa [Pi] using hPiSplit)
        B hBirr (by simpa [H] using hBmem) hBreal
        degree0 hdegree0Pos hdegree0
    obtain ⟨x, hxPos, hdegreeEq⟩ := hdegreeMultiple
    /- XI.9.4(g): after the unique linear orbit, every remaining source
    degree is a nontrivial `p`-power, so the quotient is prime to `p`. -/
    have hxCoprime : Nat.Coprime x p := by
      have hpsi0NeAlpha : psi i0 ≠ alpha := by
        rw [← hpsiAlpha]
        exact hpair (Ne.symm hiAlphaNe)
      exact xi91_zassenhaus_restriction_degree_coprime
        n hdegree htwo_transitive a b hab F hFrob p hp hFp
        hDcyclic hDgt hFcard hpointStabilizerOdd hinvolutionCardND
        chi lambda rfl hlambdaIrr hlambdaDegree Phi rfl
        e psi i0 hpsi hpair hdecomp hei0 hpsi0Nonreal
        chi2 rfl hchi2Irr hchi2Ne alpha halphaBook hpsi0NeAlpha
        hPhiDiff Pi rfl hPiSplit B hBirr hBmem hBreal
        degree0 x hdegree0Pos hdegree0 hdegreeEq
    /- XI.9.4(d)--(g): the remaining constituents occur in conjugate pairs,
    while the distinguished `lambda` occurs once. -/
    have hxOdd : Odd x := by
      have hpsi0NeAlpha : psi i0 ≠ alpha := by
        rw [← hpsiAlpha]
        exact hpair (Ne.symm hiAlphaNe)
      exact xi91_zassenhaus_restriction_degree_odd
        htwo_transitive a b hab F hFrob hDcyclic hDgt
        hpointStabilizerOdd chi lambda rfl hlambdaIrr hlambdaDegree
        Phi rfl e psi i0 hpsi hpair hdecomp hei0 hpsi0Nonreal
        chi2 rfl hchi2Irr hchi2Ne alpha halphaBook hpsi0NeAlpha
        hPhiDiff Pi rfl hPiSplit B hBirr hBmem hBreal
        degree0 x hdegree0Pos hdegree0 hdegreeEq
    exact ⟨x, hxPos, hdegreeEq, hxCoprime, hxOdd⟩
  obtain ⟨x, hxPos, hdegree0Eq, hxCoprime, hxOdd⟩ :=
    hrestrictionDegreeData
  /- XI.9.4(i), integral involution value and class-sum divisibility. -/
  have hinvolutionValueDivisibility :
      ∃ value0 : ℕ,
        0 < value0 ∧
        |(psi i0 s).re| = (value0 : ℝ) ∧
        x ∣ value0 := by
    have hclassCard :
        Nat.card (ConjClasses.mk s).carrier = n * Nat.card D := by
      apply Nat.le_antisymm
      · exact hclassCardUpper.trans_eq hinvolutionCardND
      · have hlower := hclassCardLower
        rw [hFcard] at hlower
        exact hlower
    obtain ⟨f0, hf0Pos, hFpow0⟩ :=
      (IsPGroup.nontrivial_iff_card (p := p) (G := F) (hG := hFp)).mp
        (inferInstance : Nontrivial F)
    have hnPow0 : n = p ^ f0 := hFcard.symm.trans hFpow0
    exact xi91_involution_value_divisibility_core
      (psi i0) (hpsi i0) s hssq degree0 (Nat.card D) x n p f0
      hdegree0 hdegree0Eq hDcardOdd hxOdd hxPos hclassCard
      hxCoprime hnPow0
  obtain ⟨value0, hvalue0Pos, hvalue0Abs, hxDvdValue⟩ :=
    hinvolutionValueDivisibility
  have hxLeD : x ≤ Nat.card D := by
    have hxLeValue : x ≤ value0 := Nat.le_of_dvd hvalue0Pos hxDvdValue
    have hvalueSquareLeR : (value0 : ℝ) ^ 2 ≤ (degree0 : ℝ) := by
      rw [← hvalue0Abs]
      simpa [sq_abs] using hinvolutionSquareBound
    have hvalueSquareLe : value0 ^ 2 ≤ degree0 := by
      exact_mod_cast hvalueSquareLeR
    rw [hdegree0Eq] at hvalueSquareLe
    nlinarith
  have hdegreeArithmetic :
      0 < x ∧
      degree0 = Nat.card D * x ∧
      Nat.Coprime x p ∧
      Odd x ∧
      x ≤ Nat.card D :=
    ⟨hxPos, hdegree0Eq, hxCoprime, hxOdd, hxLeD⟩
  let tensorChar : ClassFunction G := psi i0 * chi2
  have htensorCharacter : IsCharacter tensorChar := by
    exact xi91_isCharacter_mul (psi i0) chi2 (hpsi i0).1 hchi2Irr.1
  /- XI.9.4(j), coefficient core: the product identity with every beta
  forces a strictly positive integral beta coefficient in `tensorChar`. -/
  have hbetaTensorMultiplicity :
      ∀ beta : B, ∃ m : ℕ,
        0 < m ∧
        scalarProduct G tensorChar (beta : ClassFunction G) = (m : ℂ) := by
    intro beta
    have hproduct := hPhiBetaProduct beta
    rw [hPhiDiff] at hproduct
    have hfunction :
        psi i0 * (beta : ClassFunction G) + chi2 =
          chi2 * (beta : ClassFunction G) + psi i0 := by
      ext g
      have hg := congrFun hproduct g
      change (psi i0 g - chi2 g) * ((beta : ClassFunction G) g - 1) = 0 at hg
      change psi i0 g * (beta : ClassFunction G) g + chi2 g =
        chi2 g * (beta : ClassFunction G) g + psi i0 g
      linear_combination hg
    have hchi2Psi : scalarProduct G chi2 (psi i0) = 0 := by
      exact scalarProduct_isBookIrreducible_ne chi2 (psi i0)
        hchi2Irr (hpsi i0) hchi2Ne
    have hpsiSelf : scalarProduct G (psi i0) (psi i0) = 1 :=
      scalarProduct_irreducibleCharacter_self
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi i0) (hpsi i0))
    have hspEq :
        scalarProduct G (psi i0 * (beta : ClassFunction G)) (psi i0) =
          scalarProduct G (chi2 * (beta : ClassFunction G)) (psi i0) + 1 := by
      have h := congrArg
        (fun theta : ClassFunction G => scalarProduct G theta (psi i0))
        hfunction
      change scalarProduct G
          (psi i0 * (beta : ClassFunction G) + chi2) (psi i0) =
        scalarProduct G
          (chi2 * (beta : ClassFunction G) + psi i0) (psi i0) at h
      rw [Section1.scalarProduct_add_left,
        Section1.scalarProduct_add_left, hchi2Psi, hpsiSelf] at h
      simpa using h
    have hbetaChar : IsCharacter (beta : ClassFunction G) :=
      isCharacter_of_isIrreducibleCharacterOnGroup (hBirr beta)
    have hotherChar :
        IsCharacter (chi2 * (beta : ClassFunction G)) :=
      xi91_isCharacter_mul chi2 (beta : ClassFunction G)
        hchi2Irr.1 hbetaChar
    obtain ⟨m, hm⟩ := scalarProduct_character_character_eq_nat
      (chi2 * (beta : ClassFunction G)) (psi i0)
      hotherChar (hpsi i0).1
    have htransfer :
        scalarProduct G tensorChar (beta : ClassFunction G) =
          scalarProduct G (psi i0 * (beta : ClassFunction G)) (psi i0) := by
      simpa [tensorChar, chi2] using
        xi91_scalarProduct_mul_conjugate_transfer
          (psi i0) (beta : ClassFunction G) (hBreal beta)
    refine ⟨m + 1, by omega, ?_⟩
    rw [htransfer, hspEq, hm]
    norm_num
  /- XI.9.4(j): the character `chi1 * conjugate chi1` contains the
  principal character and every member of the beta family. -/
  have htensorDegreeLowerBound :
      1 + ((Nat.card D - 1) / 2) * (n + 1) ≤ degree0 ^ 2 := by
    have htensorDegree : degree tensorChar = ((degree0 ^ 2 : ℕ) : ℂ) := by
      change psi i0 1 * star (psi i0 1) = _
      rw [show psi i0 1 = (degree0 : ℂ) by
        simpa [degree] using hdegree0]
      simp [pow_two]
    obtain ⟨J, hJFintype, hJDecidable, mult, theta,
        hthetaBook, hthetaPair, htensorDecomp⟩ :=
      character_irreducible_decomposition_all tensorChar htensorCharacter
    let : Fintype J := hJFintype
    let : DecidableEq J := hJDecidable
    have hthetaIrr : ∀ j : J,
        IsIrreducibleCharacterOnGroup (theta j) := by
      intro j
      exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        (theta j) (hthetaBook j)
    have hthetaOrth : ∀ i j : J,
        scalarProduct G (theta i) (theta j) =
          if i = j then 1 else 0 := by
      intro i j
      by_cases hij : i = j
      · subst j
        simp [scalarProduct_irreducibleCharacter_self (hthetaIrr i)]
      · rw [if_neg hij]
        exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
          (hthetaIrr i) (hthetaIrr j) (hthetaPair hij)
    have hmultTheta : ∀ j : J,
        scalarProduct G tensorChar (theta j) = (mult j : ℂ) := by
      intro j
      exact proposition_1_7_multiplicity_from_decomposition
        mult theta tensorChar hthetaOrth htensorDecomp j
    let degreeTheta : J → ℕ := fun j =>
      Classical.choose
        (degree_nat_dvd_card_of_isBookIrreducibleCharacter
          (theta j) (hthetaBook j))
    have hdegreeTheta : ∀ j : J,
        degree (theta j) = (degreeTheta j : ℂ) := by
      intro j
      exact (Classical.choose_spec
        (degree_nat_dvd_card_of_isBookIrreducibleCharacter
          (theta j) (hthetaBook j))).1
    have hdegreeSum : ∑ j : J, mult j * degreeTheta j = degree0 ^ 2 := by
      exact_mod_cast (show
        (∑ j : J, ((mult j * degreeTheta j : ℕ) : ℂ)) =
            ((degree0 ^ 2 : ℕ) : ℂ) by
        calc
          (∑ j : J, ((mult j * degreeTheta j : ℕ) : ℂ)) =
              ∑ j : J, (mult j : ℂ) * degree (theta j) := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [hdegreeTheta j]
            push_cast
            rfl
          _ = degree
                (weightedFamilySum (fun j => (mult j : ℂ)) theta) := by
            unfold degree weightedFamilySum
            apply Finset.sum_congr
            · ext j
              simp
            · intro j _hj
              rfl
          _ = degree tensorChar := by rw [← htensorDecomp]
          _ = ((degree0 ^ 2 : ℕ) : ℂ) := htensorDegree)
    let selected : Option B → ClassFunction G
      | none => principalCharacter G
      | some beta => (beta : ClassFunction G)
    let selectedDegree : Option B → ℕ
      | none => 1
      | some _beta => n + 1
    have hselectedBook : ∀ z : Option B,
        IsBookIrreducibleCharacter (selected z) := by
      intro z
      cases z with
      | none => simpa [selected] using hprincipalGBook
      | some beta =>
          simpa [selected] using
            (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
              (hBirr beta))
    have hprincipalTensor :
        scalarProduct G tensorChar (principalCharacter G) = 1 := by
      have htransfer := xi91_scalarProduct_mul_conjugate_transfer
        (psi i0) (principalCharacter G)
        (conjugateCharacter_principalCharacter (G := G)).symm
      have hself := scalarProduct_irreducibleCharacter_self
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (psi i0) (hpsi i0))
      have hmulPrincipal :
          psi i0 * principalCharacter G = psi i0 := by
        ext g
        simp [principalCharacter]
      rw [hmulPrincipal] at htransfer
      simpa [tensorChar, chi2] using htransfer.trans hself
    have hselectedCoeff : ∀ z : Option B, ∃ m : ℕ,
        0 < m ∧ scalarProduct G tensorChar (selected z) = (m : ℂ) := by
      intro z
      cases z with
      | none => exact ⟨1, by omega, by simpa [selected] using hprincipalTensor⟩
      | some beta =>
          simpa [selected] using hbetaTensorMultiplicity beta
    have hexIndex : ∀ z : Option B, ∃ j : J, theta j = selected z := by
      intro z
      by_contra hnone
      push Not at hnone
      have hzero : scalarProduct G tensorChar (selected z) = 0 := by
        rw [htensorDecomp, scalarProduct_weightedFamilySum_left]
        apply Finset.sum_eq_zero
        intro j _hj
        rw [scalarProduct_irreducibleCharacter_eq_zero_of_ne
          (hthetaIrr j)
          (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
            (selected z) (hselectedBook z))
          (hnone j)]
        simp
      obtain ⟨m, hmPos, hm⟩ := hselectedCoeff z
      rw [hm] at hzero
      exact (Nat.ne_of_gt hmPos) (by exact_mod_cast hzero)
    let index : Option B → J := fun z => Classical.choose (hexIndex z)
    have hindexEq : ∀ z : Option B, theta (index z) = selected z := by
      intro z
      exact Classical.choose_spec (hexIndex z)
    have hnPos : 0 < n := by
      rw [← hFcard]
      exact Nat.card_pos
    have hindexInj : Function.Injective index := by
      intro z w hzw
      have hselEq : selected z = selected w := by
        calc
          selected z = theta (index z) := (hindexEq z).symm
          _ = theta (index w) := by rw [hzw]
          _ = selected w := hindexEq w
      cases z with
      | none =>
          cases w with
          | none => rfl
          | some beta =>
              exfalso
              have hdegEq := congrArg degree hselEq
              rw [show degree (selected none) = 1 by
                    simp [selected, degree_apply, principalCharacter_apply],
                  show degree (selected (some beta)) = (n + 1 : ℂ) by
                    simpa [selected] using hBdegree beta] at hdegEq
              have : (1 : ℕ) = n + 1 := by exact_mod_cast hdegEq
              omega
      | some beta =>
          cases w with
          | none =>
              exfalso
              have hdegEq := congrArg degree hselEq
              rw [show degree (selected (some beta)) = (n + 1 : ℂ) by
                    simpa [selected] using hBdegree beta,
                  show degree (selected none) = 1 by
                    simp [selected, degree_apply, principalCharacter_apply]] at hdegEq
              have : n + 1 = 1 := by exact_mod_cast hdegEq
              omega
          | some gamma =>
              congr 1
              apply Subtype.ext
              simpa [selected] using hselEq
    have hindexCoeffPos : ∀ z : Option B, 0 < mult (index z) := by
      intro z
      obtain ⟨m, hmPos, hm⟩ := hselectedCoeff z
      have hcoeffEq : (mult (index z) : ℂ) = (m : ℂ) := by
        rw [← hmultTheta (index z), hindexEq z, hm]
      have hcoeffNat : mult (index z) = m := by exact_mod_cast hcoeffEq
      rw [hcoeffNat]
      exact hmPos
    have hindexDegree : ∀ z : Option B,
        degreeTheta (index z) = selectedDegree z := by
      intro z
      cases z with
      | none =>
          have hdegreeComplex : (degreeTheta (index none) : ℂ) = 1 := by
            calc
              (degreeTheta (index none) : ℂ) = degree (theta (index none)) :=
                (hdegreeTheta (index none)).symm
              _ = degree (selected none) :=
                congrArg degree (hindexEq none)
              _ = 1 := by simp [selected, degree_apply, principalCharacter_apply]
          have hdegreeNat : degreeTheta (index none) = 1 := by
            exact_mod_cast hdegreeComplex
          simpa [selectedDegree] using hdegreeNat
      | some beta =>
          have hdegreeComplex :
              (degreeTheta (index (some beta)) : ℂ) = (n + 1 : ℂ) := by
            calc
              (degreeTheta (index (some beta)) : ℂ) =
                  degree (theta (index (some beta))) :=
                (hdegreeTheta (index (some beta))).symm
              _ = degree (selected (some beta)) :=
                congrArg degree (hindexEq (some beta))
              _ = (n + 1 : ℂ) := by
                simpa [selected] using hBdegree beta
          have hdegreeNat : degreeTheta (index (some beta)) = n + 1 := by
            exact_mod_cast hdegreeComplex
          simpa [selectedDegree] using hdegreeNat
    have hselectedTermLe : ∀ z : Option B,
        selectedDegree z ≤ mult (index z) * degreeTheta (index z) := by
      intro z
      rw [hindexDegree z]
      have honeLe : 1 ≤ mult (index z) := hindexCoeffPos z
      calc
        selectedDegree z = 1 * selectedDegree z := by simp
        _ ≤ mult (index z) * selectedDegree z :=
          Nat.mul_le_mul_right (selectedDegree z) honeLe
    have hselectedSum :
        (∑ z : Option B, selectedDegree z) =
          1 + B.card * (n + 1) := by
      rw [Fintype.sum_option]
      simp [selectedDegree]
    calc
      1 + ((Nat.card D - 1) / 2) * (n + 1) =
          ∑ z : Option B, selectedDegree z := by
        rw [hselectedSum, hBcard]
      _ ≤ ∑ z : Option B,
          mult (index z) * degreeTheta (index z) := by
        exact Finset.sum_le_sum fun z _hz => hselectedTermLe z
      _ = ∑ j ∈ (Finset.univ : Finset (Option B)).image index,
          mult j * degreeTheta j := by
        exact (Finset.sum_image
          (f := fun j : J => mult j * degreeTheta j) (g := index)
          hindexInj.injOn).symm
      _ ≤ ∑ j : J, mult j * degreeTheta j := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _)
          (fun j _hj _hnot => Nat.zero_le (mult j * degreeTheta j))
      _ = degree0 ^ 2 := hdegreeSum
  obtain ⟨f, hfPos, hFpow⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := F) (hG := hFp)).mp
      (inferInstance : Nontrivial F)
  have hDdivFsub : Nat.card D ∣ p ^ f - 1 := by
    obtain ⟨_hOmegaCard, _hHcard, _hGcard, hdiv⟩ :=
      huppert_XI_6_1_action_parameters
        htwo_transitive a b hab F hFrob
    rw [hFpow] at hdiv
    simpa [D] using hdiv
  /- XI.9.4(k), multiplicative-order core: choose the least positive
  exponent `e0` with `d ∣ p^e0 - 1`; then `e0 ∣ f`. -/
  have hminimalExponentFactorization :
      ∃ e0 k : ℕ,
        0 < e0 ∧
        f = e0 * k ∧
        Nat.card D ∣ p ^ e0 - 1 ∧
        ∀ r : ℕ, Nat.card D ∣ p ^ r - 1 → e0 ∣ r := by
    exact xi91_minimal_exponent_factorization
      p (Nat.card D) f hfPos hDdivFsub
  obtain ⟨e0, k, he0Pos, hfEq, hDdiv, he0Minimal⟩ :=
    hminimalExponentFactorization
  /- XI.9.4(k), inequality core: (i) and (j), together with
  `p^e0 ≥ 1 + 2*d`, exclude `k ≥ 3`. -/
  have hkLe : k ≤ 2 := by
    exact xi91_exponent_quotient_le_two
      n p (Nat.card D) f e0 k degree0 x
      hDcardOdd hDgt (hp.odd_of_ne_two hp2) hp.one_lt he0Pos
      hfEq (hFcard.symm.trans hFpow) hDdiv hdegree0Eq hxLeD
      htensorDegreeLowerBound
  have hkPos : 0 < k := by
    by_contra hk
    have hkZero : k = 0 := Nat.eq_zero_of_not_pos hk
    rw [hkZero, mul_zero] at hfEq
    omega
  have hkCases : k = 1 ∨ k = 2 := by omega
  /- XI.9.4(k), terminal `k = 2` branch: every involution is an odd
  fixed-point-free permutation, contradicting simplicity via the sign map. -/
  have hexponentTwoImpossible : k = 2 → False := by
    intro hkTwo
    let sigma : Equiv.Perm Omega := (MulAction.toPermHom G Omega) s
    have hsigmaSq : sigma ^ 2 = 1 := by
      change ((MulAction.toPermHom G Omega) s) ^ 2 = 1
      rw [← map_pow, hssq, map_one]
    have hfixedEmpty : IsEmpty (Function.fixedPoints sigma) := by
      refine ⟨?_⟩
      intro y
      apply hsfixedPointFree y.1
      have hy := y.2
      change s • y.1 = y.1 at hy
      exact hy
    let : IsEmpty (Function.fixedPoints sigma) := hfixedEmpty
    have hfixedCard :
        Fintype.card (Function.fixedPoints sigma) = 0 :=
      Fintype.card_eq_zero
    have hnSquare : n = (p ^ e0) ^ 2 := by
      calc
        n = p ^ f := hFcard.symm.trans hFpow
        _ = p ^ (e0 * 2) := by rw [hfEq, hkTwo]
        _ = (p ^ e0) ^ 2 := by rw [pow_mul]
    have hpPowOdd : Odd (p ^ e0) := (hp.odd_of_ne_two hp2).pow
    have hEight : 8 ∣ (p ^ e0) ^ 2 - 1 :=
      Nat.eight_dvd_sq_sub_one_of_odd hpPowOdd
    obtain ⟨t, ht⟩ := hEight
    have hnForm : n = 8 * t + 1 := by
      rw [hnSquare]
      have honeLe : 1 ≤ (p ^ e0) ^ 2 :=
        Nat.one_le_iff_ne_zero.mpr
          (pow_ne_zero 2 (pow_ne_zero e0 hp.ne_zero))
      calc
        (p ^ e0) ^ 2 = (p ^ e0) ^ 2 - 1 + 1 :=
          (Nat.sub_add_cancel honeLe).symm
        _ = 8 * t + 1 := by rw [ht]
    have hhalfOdd : Odd ((n + 1) / 2) := by
      refine ⟨2 * t, ?_⟩
      rw [hnForm]
      omega
    have hsigmaSign : Equiv.Perm.sign sigma = -1 := by
      rw [Equiv.Perm.sign_of_pow_two_eq_one hsigmaSq,
        hfixedCard, hdegree]
      simpa using hhalfOdd.neg_one_pow (α := ℤˣ)
    have hcommNeBot : commutator G ≠ ⊥ := by
      intro hcommBot
      have hcenterTop : Subgroup.center G = ⊤ :=
        (commutator_eq_bot_iff_center_eq_top (G := G)).mp hcommBot
      have hGcomm : ∀ x y : G, x * y = y * x := by
        intro x y
        have hy : y ∈ Subgroup.center G := by
          rw [hcenterTop]
          exact Subgroup.mem_top y
        exact Subgroup.mem_center_iff.mp hy x
      apply hFnoncomm
      refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      apply H.subtype_injective
      calc
        H.subtype (↑x * ↑y) = (x : G) * (y : G) := by simp
        _ = (y : G) * (x : G) := hGcomm (x : G) (y : G)
        _ = H.subtype (↑y * ↑x) := by simp
    have hcommTop : commutator G = ⊤ :=
      hsimple (commutator G) (inferInstance : (commutator G).Normal)
        hcommNeBot
    let signHom : G →* ℤˣ :=
      Equiv.Perm.sign.comp (MulAction.toPermHom G Omega)
    have hcommLe : commutator G ≤ signHom.ker :=
      Abelianization.commutator_subset_ker signHom
    rw [hcommTop] at hcommLe
    have hkerTop : signHom.ker = ⊤ := top_unique hcommLe
    have hsignHomOne : signHom = 1 :=
      MonoidHom.ker_eq_top_iff.mp hkerTop
    have hsigmaSignOne : Equiv.Perm.sign sigma = 1 := by
      simpa [signHom, sigma] using congrArg (fun f : G →* ℤˣ => f s)
        hsignHomOne
    rw [hsigmaSign] at hsigmaSignOne
    norm_num at hsigmaSignOne
  /- XI.9.4(l), terminal `k = 1` branch: the complement acts freely on
  `F / F'`; minimality of `e0` forces `F' = 1`, contrary to noncommutativity. -/
  have hexponentOneImpossible : k = 1 → False := by
    intro hkOne
    have hfEqE0 : f = e0 := by simpa [hkOne] using hfEq
    let : MulDistribMulAction D F :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer D F
        (Subgroup.le_normalizer_of_normal (H := F))
    have hDFree :
        ∀ d : D, d ≠ 1 → ∀ z : F, d • z = z → z = 1 := by
      intro d hd z hfix
      have hconj : (d : H) * (z : H) * (d : H)⁻¹ = (z : H) := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg Subtype.val hfix
      have hcomm : (d : H) * (z : H) = (z : H) * (d : H) := by
        have h := congrArg (fun x : H => x * (d : H)) hconj
        simpa [mul_assoc] using h
      have hzcent : (z : H) ∈ elementCentralizerIn F (d : H) :=
        ⟨z.property, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
      have hcent : elementCentralizerIn F (d : H) = ⊥ :=
        (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
          hFrob.normal hFrob.isComplement').mp hFrob d hd
      have hzbot : (z : H) ∈ (⊥ : Subgroup H) := by
        simpa [hcent] using hzcent
      exact Subtype.ext (by simpa using hzbot)
    have hpPowPos : 0 < p ^ f := pow_pos hp.pos f
    have hpPowSplit : p ^ f = 1 + (p ^ f - 1) := by omega
    have hpredCoprime : Nat.Coprime (p ^ f - 1) (p ^ f) := by
      conv_rhs => rw [hpPowSplit]
      rw [Nat.coprime_add_self_right]
      exact Nat.coprime_one_right _
    have hcopDF : Nat.Coprime (Nat.card D) (Nat.card F) := by
      rw [hFpow]
      exact Nat.Coprime.of_dvd_left hDdivFsub hpredCoprime
    let C := commutator F
    let hCinv : IsInvariant D F C :=
      isInvariant_of_characteristic (A := D) (G := F) C
    let : MulDistribMulAction D (F ⧸ C) :=
      quotientMulDistribMulAction (A := D) (G := F) C hCinv
    have hfreeAb :
        ∀ d : D, d ≠ 1 → ∀ x : F ⧸ C, d • x = x → x = 1 := by
      intro d hd x hx
      let S := Subgroup.zpowers d
      have hScardDvd : Nat.card S ∣ Nat.card D :=
        Subgroup.card_subgroup_dvd_card S
      have hcopSF : Nat.Coprime (Nat.card S) (Nat.card F) :=
        Nat.Coprime.of_dvd_left hScardDvd hcopDF
      let hCinvS : IsInvariant S F C :=
        isInvariant_of_characteristic (A := S) (G := F) C
      let : MulDistribMulAction S (F ⧸ C) :=
        quotientMulDistribMulAction (A := S) (G := F) C hCinvS
      have hquot := fixedPointSubgroup_quotient_eq_map_of_solvable_coprime
        (G := F) (A := S) (inferInstance : Group.IsSolvable F) hcopSF C hCinvS
      have hfixF : fixedPointSubgroup (↥S) F = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro z hz
        have hzd : d • (z : F) = z := by
          simpa [S] using hz (⟨d, Subgroup.mem_zpowers d⟩ : S)
        exact hDFree d hd z hzd
      rw [hfixF] at hquot
      have hfixQuot : fixedPointSubgroup (↥S) (F ⧸ C) = ⊥ := by
        simpa [C] using hquot
      set_option synthInstance.maxHeartbeats 200000 in
      have hxS : x ∈ fixedPointSubgroup (↥S) (F ⧸ C) := by
        change ∀ s : S, s • x = x
        intro s
        apply smul_eq_self_of_mem_zpowers
          (y := (⟨d, Subgroup.mem_zpowers d⟩ : S))
        · rcases Subgroup.mem_zpowers_iff.mp s.property with ⟨m, hm⟩
          exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext hm⟩
        · simpa [S] using hx
      rw [hfixQuot] at hxS
      simpa [C] using hxS
    have hDdivAb : Nat.card D ∣ Nat.card (F ⧸ C) - 1 :=
      xi91_actor_card_dvd_group_card_sub_one hfreeAb
    have hAbOneLt : 1 < Nat.card (F ⧸ C) := by
      have hcommLt : C < (⊤ : Subgroup F) := by
        change commutator F < (⊤ : Subgroup F)
        exact Group.IsSolvable.commutator_lt_top_of_nontrivial F
      have hindex : 1 < C.index :=
        Subgroup.one_lt_index_of_ne_top hcommLt.ne
      rw [Subgroup.index_eq_card] at hindex
      exact hindex
    let : Nontrivial (F ⧸ C) :=
      Finite.one_lt_card_iff_nontrivial.mp hAbOneLt
    have hAbP : IsPGroup p (F ⧸ C) := by
      exact hFp.to_quotient C
    obtain ⟨r, hrPos, hAbPow⟩ :=
      (IsPGroup.nontrivial_iff_card (p := p) (G := F ⧸ C) hAbP).mp
        (inferInstance : Nontrivial (F ⧸ C))
    have he0DvdR : e0 ∣ r := he0Minimal r (by
      rw [← hAbPow]
      exact hDdivAb)
    have he0LeR : e0 ≤ r := Nat.le_of_dvd hrPos he0DvdR
    have hpowDvd : p ^ r ∣ p ^ f := by
      rw [← hAbPow, ← hFpow]
      exact Subgroup.card_quotient_dvd_card C
    have hrLeF : r ≤ f :=
      (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpowDvd
    have hrEq : r = f := by omega
    have hAbCardEq : Nat.card (F ⧸ C) = Nat.card F := by
      rw [hAbPow, hFpow, hrEq]
    have hcardMul := Subgroup.card_eq_card_quotient_mul_card_subgroup C
    rw [hAbCardEq] at hcardMul
    have hCcard : Nat.card C = 1 := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F))
      calc
        Nat.card F * Nat.card C = Nat.card F := hcardMul.symm
        _ = Nat.card F * 1 := by simp
    have hCbot : C = ⊥ := Subgroup.card_eq_one.mp hCcard
    have hcenterTop : Subgroup.center F = ⊤ :=
      (commutator_eq_bot_iff_center_eq_top F).mp (by simpa [C] using hCbot)
    apply hFnoncomm
    exact ⟨⟨fun x y => by
      have hy : y ∈ Subgroup.center F := by
        rw [hcenterTop]
        exact Subgroup.mem_top y
      exact Subgroup.mem_center_iff.mp hy x⟩⟩
  exact (hkCases.elim hexponentOneImpossible hexponentTwoImpossible).elim
termination_by Nat.card G
decreasing_by simpa using hcardN

/-- Ito XI.9.1 in its Zassenhaus-group context: if the point-stabilizer
Frobenius kernel is a noncommutative `p`-group and the two-point stabilizer is
a Z-group, then `p = 2`. -/
public theorem huppert_XI_9_1_noncommutativeKernel_zGroupComplement
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (n : ℕ) (hdegree : Fintype.card Omega = n + 1)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (p : ℕ) (hp : Nat.Prime p)
    (hFnoncomm : ¬ IsMulCommutative F)
    (hFp : IsPGroup p F)
    (hDZ : IsZGroup
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    p = 2 := by
  exact huppert_XI_9_1_noncommutativeKernel_zGroupComplement_aux
    n hdegree htwo_transitive hat_most_two_fixed_points hno_regular_normal
    a b hab F hFrob p hp hFnoncomm hFp hDZ

end

end External
end CFSG.BenderSuzuki
