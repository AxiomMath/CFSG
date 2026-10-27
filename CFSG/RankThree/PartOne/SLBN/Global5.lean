module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.Assembly.Defs
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

namespace CFSG.RankThree.PartOne.SLBN

open Subgroup CFSG CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

variable {Y : Type*} [Group Y] [Finite Y]

@[expose] noncomputable def frattiniConj (K : Subgroup Y) [K.Normal] :
    Y →* MulAut (↥K ⧸ frattini ↥K) :=
  (quotientAutomorphism (frattini ↥K)).comp MulAut.conjNormal

omit [Finite Y] in
theorem frattiniConj_mk (K : Subgroup Y) [K.Normal] (y : Y) (k : K) :
    frattiniConj K y (k : ↥K ⧸ frattini ↥K) =
      ((MulAut.conjNormal y k : ↥K) : ↥K ⧸ frattini ↥K) :=
  quotientAutomorphism_apply (frattini ↥K) (MulAut.conjNormal y) k

theorem isElementaryAbelian_frattini_quotient (K : Subgroup Y) (hK : IsPGroup 3 K) :
    IsElementaryAbelian 3 (↥K ⧸ frattini ↥K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 ↥K) := ⟨hK⟩
  exact CFSG.isElementaryAbelian_quotient_frattini (R := ↥K) (p := 3)

theorem frattiniConj_eq_one_of_mem (K : Subgroup Y) [K.Normal] (hK : IsPGroup 3 K) {k : Y}
    (hk : k ∈ K) : frattiniConj K k = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 ↥K) := ⟨hK⟩
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [frattiniConj_mk, MulAut.one_apply, QuotientGroup.eq]
  have e : (MulAut.conjNormal k x : ↥K)⁻¹ * x = ⁅(⟨k, hk⟩ : K), x⁻¹⁆ := by
    apply Subtype.ext
    simp [MulAut.conjNormal_apply, commutatorElement_def, mul_assoc]
  rw [e]
  exact CFSG.commutator_le_frattini_of_isPGroup (R := ↥K) (p := 3)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem exists_mem_centralizer_of_fixed (K : Subgroup Y) [K.Normal] (hK : IsPGroup 3 K) {b : Y}
    (hb : b ^ 2 = 1) {q : ↥K ⧸ frattini ↥K} (hq : frattiniConj K b q = q) :
    ∃ c : ↥K, (c : Y) ∈ Subgroup.centralizer ({b} : Set Y) ∧
      q = (c : ↥K ⧸ frattini ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsPGroup 2 (Subgroup.zpowers b) := by
    have h1 : Nat.card (Subgroup.zpowers b) = orderOf b := Nat.card_zpowers b
    have hd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one hb
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h1, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [h1, h]; simp)
  let α : Subgroup.zpowers b →* MulAut ↥K :=
    MulAut.conjNormal.comp (Subgroup.zpowers b).subtype
  have hN : ∀ a : Subgroup.zpowers b, ∀ n ∈ frattini ↥K, α a n ∈ frattini ↥K := by
    intro a n hn
    have h := (inferInstance : (frattini ↥K).Characteristic).fixed (α a)
    have hn' : n ∈ (frattini ↥K).comap (α a).toMonoidHom := by rw [h]; exact hn
    exact hn'
  have hcop : ¬ 2 ∣ Nat.card (frattini ↥K) := by
    obtain ⟨n, hn⟩ := (hK.to_subgroup (frattini ↥K)).exists_card_eq
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have key := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hA α (frattini ↥K) hN hcop
  have hstab : ∀ a : Subgroup.zpowers b, frattiniConj K (a : Y) q = q := by
    intro a
    let S₀ : Subgroup Y := (MulAction.stabilizer (MulAut (↥K ⧸ frattini ↥K)) q).comap
      (frattiniConj K)
    have hb₀ : b ∈ S₀ := hq
    have := (Subgroup.zpowers_le).2 hb₀ a.2
    exact this
  have hmem : q ∈ {q : ↥K ⧸ frattini ↥K | ∀ a : Subgroup.zpowers b,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini ↥K) hN a q = q} := by
    intro a
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective q
    have h1 := hstab a
    rw [← hx] at h1 ⊢
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    rw [frattiniConj_mk] at h1
    exact h1
  rw [key] at hmem
  obtain ⟨c, hc, hcq⟩ := hmem
  refine ⟨c, ?_, hcq.symm⟩
  have hbc := hc ⟨b, Subgroup.mem_zpowers b⟩
  have h2 : b * (c : Y) * b⁻¹ = (c : Y) := congrArg Subtype.val hbc
  rw [Subgroup.mem_centralizer_singleton_iff]
  symm
  calc b * (c : Y) = (b * (c : Y) * b⁻¹) * b := by group
    _ = (c : Y) * b := by rw [h2]

theorem card_range_le_three {Q C : Type*} [Group Q] [Group C] [IsCyclic C]
    (hpow : ∀ x : Q, x ^ 3 = 1) (f : C →* Q) : Nat.card f.range ≤ 3 := by
  have hcyc : IsCyclic f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h1 : Monoid.exponent f.range ∣ 3 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    apply Subtype.ext
    simpa using hpow (x : Q)
  have h2 : Nat.card f.range ∣ 3 := by rw [← hcyc.exponent_eq_card]; exact h1
  exact Nat.le_of_dvd (by norm_num) h2

theorem card_fixed_le_three (K : Subgroup Y) [K.Normal] (hK : IsPGroup 3 K) {b : Y}
    (hb : b ^ 2 = 1) (hc : IsCyclic ↥(K ⊓ Subgroup.centralizer ({b} : Set Y))) :
    Nat.card {q : ↥K ⧸ frattini ↥K | frattiniConj K b q = q} ≤ 3 := by
  have hel := isElementaryAbelian_frattini_quotient K hK
  have hpow : ∀ x : ↥K ⧸ frattini ↥K, x ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 _)
  let f : ↥(K ⊓ Subgroup.centralizer ({b} : Set Y)) →* ↥K ⧸ frattini ↥K :=
    (QuotientGroup.mk' (frattini ↥K)).comp (Subgroup.inclusion inf_le_left)
  have hsub : {q : ↥K ⧸ frattini ↥K | frattiniConj K b q = q} ⊆ (f.range : Set _) := by
    intro q hq
    obtain ⟨c, hcC, hcq⟩ := exists_mem_centralizer_of_fixed K hK hb hq
    exact ⟨⟨(c : Y), c.2, hcC⟩, by rw [hcq]; rfl⟩
  have h1 := card_range_le_three hpow f
  have h2 : Nat.card {q : ↥K ⧸ frattini ↥K | frattiniConj K b q = q} ≤ Nat.card f.range :=
    Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  exact h2.trans h1

end CFSG.RankThree.PartOne.SLBN
