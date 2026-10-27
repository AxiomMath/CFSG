module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankFrattini
import CFSG.RankThree.PartOne.S9.OddCore.TorsionModule
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.RankThree.PartOne.FiveCritical

open Subgroup CFSG CFSG.RankThree.PartOne.FixedRank36
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem frattini_class_eq_iff {D : Subgroup G} (x y : ↥D) :
    (x : ↥D ⧸ frattini ↥D) = (y : ↥D ⧸ frattini ↥D) ↔
      (x : G)⁻¹ * (y : G) ∈ inSubgroup frattini D := by
  rw [QuotientGroup.eq]
  exact (Subgroup.mem_map_iff_mem D.subtype_injective (K := frattini ↥D)
    (x := x⁻¹ * y)).symm

theorem smul_eq_ofMul_pow {q : ℕ} [Fact q.Prime] {D : Subgroup G}
    [IsElementaryAbelian q (↥D ⧸ frattini ↥D)] (c : ZMod q)
    (v : Additive (↥D ⧸ frattini ↥D)) :
    c • v = Additive.ofMul (Additive.toMul v ^ c.val) := by
  have hc : c • v = c.val • v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_zmod_val]
  rw [hc]
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  rfl

theorem frattiniRep_eq_smul_of_scalar {q : ℕ} [Fact q.Prime] {D : Subgroup G}
    [IsElementaryAbelian q (↥D ⧸ frattini ↥D)] (b : normalizer (D : Set G)) {k : ℕ}
    (hk : ∀ d ∈ D, ((b : G) * d * (b : G)⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D)
    (v : Additive (↥D ⧸ frattini ↥D)) :
    frattiniRep q D.normalizerMonoidHom b v = (k : ZMod q) • v := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : v = Additive.ofMul (x : ↥D ⧸ frattini ↥D) := by rw [hx]; rfl
  rw [hv, frattiniRep_apply, Nat.cast_smul_eq_nsmul]
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  change ((D.normalizerMonoidHom b x : ↥D) : ↥D ⧸ frattini ↥D) = (x : ↥D ⧸ frattini ↥D) ^ k
  rw [← QuotientGroup.mk_pow, frattini_class_eq_iff]
  simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using hk x x.2

theorem scalar_of_frattiniRep_eq_smul {q : ℕ} [Fact q.Prime] {D : Subgroup G}
    [IsElementaryAbelian q (↥D ⧸ frattini ↥D)] (b : normalizer (D : Set G)) (c : ZMod q)
    (h : ∀ v, frattiniRep q D.normalizerMonoidHom b v = c • v) :
    ∀ d ∈ D, ((b : G) * d * (b : G)⁻¹)⁻¹ * d ^ c.val ∈ inSubgroup frattini D := by
  intro d hd
  have h1 := h (Additive.ofMul ((⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D))
  rw [frattiniRep_apply, smul_eq_ofMul_pow] at h1
  have h2 := Additive.ofMul.injective h1
  rw [toMul_ofMul, ← QuotientGroup.mk_pow] at h2
  have h3 := (frattini_class_eq_iff _ _).mp h2
  simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h3

theorem frattiniRep_eq_one_of_pow_eq_one {q : ℕ} [hq : Fact q.Prime] {P : Type*} [Group P]
    [Finite P] {L : Type*} [Group L] [IsElementaryAbelian q (P ⧸ frattini P)] (hP : IsPGroup q P)
    (ρ : L →* MulAut P) (l : L) {m : ℕ} (hcop : Nat.Coprime q m) (hm : (ρ l) ^ m = 1)
    (h : frattiniRep q ρ l = 1) : ρ l = 1 := by
  have hker : ρ l ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini P)).ker := by
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    have h1 := congrArg (fun f : Module.End (ZMod q) (Additive (P ⧸ frattini P)) =>
      f (Additive.ofMul (x : P ⧸ frattini P))) h
    simp only [frattiniRep_apply, Module.End.one_apply] at h1
    exact congrArg Additive.toMul h1
  have hqker := CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup
    q hP
  obtain ⟨k, hk⟩ := hqker ⟨ρ l, hker⟩
  have hk' : (ρ l) ^ q ^ k = 1 := congrArg Subtype.val hk
  have := pow_gcd_eq_one.2 ⟨hk', hm⟩
  rwa [Nat.Coprime.pow_left k hcop |>.gcd_eq_one, pow_one] at this

theorem exists_frattini_scalar_character [Finite G] {q : ℕ} (hq : q.Prime) (hq5 : q ≠ 5)
    {D E : Subgroup G} {c : G} (hD : IsPGroup q D) (hEN : E ≤ normalizer (D : Set G))
    (hE5 : ∀ t ∈ E, t ^ 5 = 1) (hEcard : Nat.card E = 25)
    (hrel : (inSubgroup frattini D).relIndex D = q ^ 4)
    (hscalar : ∀ e ∈ E, ∃ k : ℕ, ∀ d ∈ D, (e * d * e⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D)
    (hcE : c ∈ E) (hc1 : c ≠ 1) (hcD : c ∈ centralizer (D : Set G)) (hED : ⁅E, D⁆ ≠ ⊥) :
    ∃ χ : ↥E →* (ZMod q)ˣ,
      (∀ (t : E) (d : G), d ∈ D →
        ((t : G) * d * (t : G)⁻¹)⁻¹ * d ^ ((χ t : ZMod q).val) ∈ inSubgroup frattini D) ∧
      Nat.card χ.range = 5 ∧ χ.ker.map E.subtype = zpowers c ∧
      E ⊓ centralizer (D : Set G) = zpowers c := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hel : IsElementaryAbelian q (↥D ⧸ frattini ↥D) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hD).2.2.2.1
  have hVnt : Nontrivial (Additive (↥D ⧸ frattini ↥D)) := by
    have h1 : Nat.card (↥D ⧸ frattini ↥D) = q ^ 4 := by
      rw [← Torsion37.relIndex_inSubgroup_frattini_eq_card, hrel]
    have h2 : 1 < Nat.card (Additive (↥D ⧸ frattini ↥D)) := by
      change 1 < Nat.card (↥D ⧸ frattini ↥D)
      rw [h1]
      exact Nat.one_lt_pow (by norm_num) hq.one_lt
    exact Finite.one_lt_card_iff_nontrivial.mp h2
  set rep : Representation (ZMod q) ↥E (Additive (↥D ⧸ frattini ↥D)) :=
    (frattiniRep q D.normalizerMonoidHom).comp (Subgroup.inclusion hEN) with hrep
  choose! k hk using hscalar
  have hrepapp : ∀ (t : E) (v : Additive (↥D ⧸ frattini ↥D)), rep t v = (k t : ZMod q) • v :=
    fun t v => frattiniRep_eq_smul_of_scalar (Subgroup.inclusion hEN t) (hk t t.2) v
  have hφinj : Function.Injective (Units.map (algebraMap (ZMod q)
      (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))).toMonoidHom) :=
    Units.map_injective (algebraMap (ZMod q) (Module.End (ZMod q)
      (Additive (↥D ⧸ frattini ↥D)))).injective
  set φ := Units.map (algebraMap (ZMod q) (Module.End (ZMod q)
    (Additive (↥D ⧸ frattini ↥D)))).toMonoidHom with hφ
  have hk0 : ∀ t : E, (k t : ZMod q) ≠ 0 := by
    intro t h0
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : Additive (↥D ⧸ frattini ↥D))
    apply hv₀
    have h1 : rep t (rep t⁻¹ v₀) = v₀ := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hrepapp, h0, zero_smul] at h1
    exact h1.symm
  have hmem : ∀ t : E, rep.asGroupHom t ∈ φ.range := by
    intro t
    refine ⟨Units.mk0 (k t : ZMod q) (hk0 t), Units.ext ?_⟩
    rw [hφ, Units.coe_map, Representation.asGroupHom_apply]
    apply LinearMap.ext
    intro v
    rw [hrepapp]
    exact (Module.algebraMap_end_apply (ZMod q) (ZMod q) _ _ _).symm
  set χ : ↥E →* (ZMod q)ˣ := (MonoidHom.ofInjective hφinj).symm.toMonoidHom.comp
    (rep.asGroupHom.codRestrict φ.range hmem) with hχ
  have hχφ : ∀ t : E, φ (χ t) = rep.asGroupHom t := fun t =>
    MonoidHom.apply_ofInjective_symm hφinj _
  have hχrep : ∀ (t : E) (v : Additive (↥D ⧸ frattini ↥D)), rep t v = (χ t : ZMod q) • v := by
    intro t v
    have h := congrArg (fun u : (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))ˣ =>
      (u : Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D))) v) (hχφ t)
    simpa [hφ, Representation.asGroupHom_apply, Module.algebraMap_end_apply] using h.symm
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : Additive (↥D ⧸ frattini ↥D))
  have hsmul_eq : ∀ a : ZMod q, a • v₀ = v₀ → a = 1 := fun a h =>
    smul_left_injective (ZMod q) hv₀ (show a • v₀ = (1 : ZMod q) • v₀ by rw [h, one_smul])
  have hχ1 : ∀ t : E, χ t = 1 ↔ (t : G) ∈ centralizer (D : Set G) := by
    intro t
    constructor
    · intro h1
      have hrep1 : frattiniRep q D.normalizerMonoidHom (Subgroup.inclusion hEN t) = 1 := by
        apply LinearMap.ext
        intro v
        have h := hχrep t v
        rw [h1, Units.val_one, one_smul] at h
        rw [Module.End.one_apply]
        exact h
      have h5 : (Subgroup.inclusion hEN t) ^ 5 = 1 := Subtype.ext (hE5 t t.2)
      have hρ := frattiniRep_eq_one_of_pow_eq_one hD D.normalizerMonoidHom
        (Subgroup.inclusion hEN t) (m := 5) ((Nat.coprime_primes hq (by norm_num)).mpr hq5)
        (by rw [← map_pow, h5, map_one]) hrep1
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h := congrArg (fun f : MulAut ↥D => ((f ⟨d, hd⟩ : ↥D) : G)) hρ
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h
      calc d * t = (t * d * (t : G)⁻¹) * t := by rw [show (t : G) * d * (t : G)⁻¹ = d from h]
        _ = t * d := by group
    · intro hc
      refine Units.ext (hsmul_eq _ ?_)
      rw [← hχrep]
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v₀)
      have hv : v₀ = Additive.ofMul (x : ↥D ⧸ frattini ↥D) := by rw [hx]; rfl
      rw [hv]
      change frattiniRep q D.normalizerMonoidHom (Subgroup.inclusion hEN t)
        (Additive.ofMul (x : ↥D ⧸ frattini ↥D)) = _
      rw [frattiniRep_apply]
      congr 2
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have h := Subgroup.mem_centralizer_iff.mp hc x x.2
      change (t : G) * x * (t : G)⁻¹ = x
      calc (t : G) * x * (t : G)⁻¹ = x * t * (t : G)⁻¹ := by rw [h]
        _ = x := by group
  have hker : ∀ t : E, t ∈ χ.ker ↔ (t : G) ∈ centralizer (D : Set G) := fun t =>
    (MonoidHom.mem_ker).trans (hχ1 t)
  have hRcyc : IsCyclic χ.range := by
    have := ZMod.isCyclic_units_prime hq
    infer_instance
  have hRdvd : Nat.card χ.range ∣ 5 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := χ.range)
    rw [← hg]
    apply orderOf_dvd_of_pow_eq_one
    obtain ⟨t, ht⟩ := g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ht, ← map_pow]
    have h5 : t ^ 5 = 1 := Subtype.ext (hE5 t t.2)
    rw [h5, map_one]
    rfl
  have hRne : Nat.card χ.range ≠ 1 := by
    intro h1
    apply hED
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g hg
    have hbot : χ.range = ⊥ := Subgroup.card_eq_one.mp h1
    have h2 : χ ⟨g, hg⟩ ∈ (⊥ : Subgroup (ZMod q)ˣ) := hbot ▸ MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩
    exact (hχ1 ⟨g, hg⟩).mp (Subgroup.mem_bot.mp h2)
  have hR5 : Nat.card χ.range = 5 :=
    ((Nat.dvd_prime (by norm_num)).mp hRdvd).resolve_left hRne
  have hK5 : Nat.card χ.ker = 5 := by
    have h := Subgroup.card_ker_mul_card_range χ
    rw [hEcard, hR5] at h
    omega
  have hcK : (⟨c, hcE⟩ : E) ∈ χ.ker := (hker _).mpr hcD
  have hle : zpowers c ≤ χ.ker.map E.subtype := by
    rw [Subgroup.zpowers_le]
    exact ⟨⟨c, hcE⟩, hcK, rfl⟩
  have hordc : orderOf c = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime (hE5 c hcE) hc1
  have hmapeq : χ.ker.map E.subtype = zpowers c := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective E.subtype_injective, hK5, Nat.card_zpowers, hordc]
  have hinf : E ⊓ centralizer (D : Set G) = χ.ker.map E.subtype := by
    ext g
    constructor
    · rintro ⟨hgE, hgC⟩
      exact ⟨⟨g, hgE⟩, (hker _).mpr hgC, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.2, (hker t).mp ht⟩
  exact ⟨χ, fun t d hd => scalar_of_frattiniRep_eq_smul (Subgroup.inclusion hEN t)
    (χ t : ZMod q) (hχrep t) d hd, hR5, hmapeq, hinf.trans hmapeq⟩

end CFSG.RankThree.PartOne.FiveCritical
