module

import CFSG.RankThree.Coprime.InvolutionFixedRankBound
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.RankThree.PartTwo.Sec4.Census
open scoped commutatorElement

theorem card_le_eight_of_faithful {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {D E : Subgroup G} (hDp : IsPGroup p D) (hDexp : ∀ x ∈ D, x ^ p = 1)
    (hDclass : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hEc : ∀ a b : E, a * b = b * a)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hEN : E ≤ Subgroup.normalizer (D : Set G))
    (hfaith : ∀ e ∈ E, e ≠ 1 → ∃ d ∈ D, e * d * e⁻¹ ≠ d)
    (hrank : ∀ e ∈ E, e ≠ 1 → ∀ H : Subgroup G, H ≤ D → (∀ h ∈ H, h * e = e * h) →
      CFSG.pRank p H ≤ 2)
    {n : ℕ} (hn : Nat.card E = 2 ^ n) : n ≤ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eE⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := E) hEc
    (fun a => Subtype.ext (hE2 a a.2)) hn
  set ι : Multiplicative (Fin n → ZMod 2) →* E := eE.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := eE.symm.injective
  let ι' : Multiplicative (Fin n → ZMod 2) →* Subgroup.normalizer (D : Set G) :=
    (Subgroup.inclusion hEN).comp ι
  let act : MulDistribMulAction (Multiplicative (Fin n → ZMod 2)) D :=
    MulDistribMulAction.compHom D ι'
  have hsmul : ∀ (a : Multiplicative (Fin n → ZMod 2)) (d : D),
      ((a • d : D) : G) = (ι a : G) * d * (ι a : G)⁻¹ := fun a d => rfl
  have hA2 : ∀ a : Multiplicative (Fin n → ZMod 2), a ^ 2 = 1 := by
    intro a
    obtain ⟨e, rfl⟩ := eE.surjective a
    rw [← map_pow, show e ^ 2 = 1 from Subtype.ext (hE2 e e.2), map_one]
  have hfaithful : FaithfulSMul (Multiplicative (Fin n → ZMod 2)) D := by
    refine ⟨fun {a₁ a₂} h => hι ?_⟩
    set c : E := (ι a₁)⁻¹ * ι a₂ with hc
    by_contra hne
    have hc1 : c ≠ 1 := fun h1 => hne (by
      rw [hc, inv_mul_eq_one] at h1
      exact h1)
    obtain ⟨d, hd, hcd⟩ := hfaith (c : G) c.2 (fun h1 => hc1 (Subtype.ext h1))
    apply hcd
    have h1 := congrArg Subtype.val (h ⟨d, hd⟩)
    rw [hsmul, hsmul] at h1
    have hcG : (c : G) = ((ι a₁ : E) : G)⁻¹ * (ι a₂ : G) := by simp [hc]
    calc (c : G) * d * (c : G)⁻¹
        = ((ι a₁ : E) : G)⁻¹ * ((ι a₂ : G) * d * (ι a₂ : G)⁻¹) * (ι a₁ : G) := by
          rw [hcG]; group
      _ = ((ι a₁ : E) : G)⁻¹ * ((ι a₁ : G) * d * (ι a₁ : G)⁻¹) * (ι a₁ : G) := by rw [h1]
      _ = d := by group
  have hexp : Monoid.exponent D ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hDcl : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    have := hDclass a a.2 b b.2 d d.2
    simp only [commutatorElement_def] at this ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact this.symm
  have hclass : (⊤ : Subgroup D).lowerCentralSeries 2 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one,
      Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ]
    exact hDcl
  have hm : ∀ a : Multiplicative (Fin n → ZMod 2), a ≠ 1 →
      CFSG.pRank p (CFSG.fixedPointSubgroup (Subgroup.zpowers a) D) ≤ 2 := by
    intro a ha
    set C := CFSG.fixedPointSubgroup (Subgroup.zpowers a) D
    have ha1 : (ι a : E) ≠ 1 := fun h => ha (hι (by rw [h, map_one]))
    have hC : ∀ c ∈ C.map D.subtype, c * (ι a : G) = (ι a : G) * c := by
      rintro _ ⟨c, hc, rfl⟩
      have hfix : a • c = c := hc ⟨a, Subgroup.mem_zpowers a⟩
      have h1 := congrArg Subtype.val hfix
      rw [hsmul] at h1
      change (c : G) * (ι a : G) = (ι a : G) * c
      calc (c : G) * (ι a : G) = (ι a : G) * c * (ι a : G)⁻¹ * (ι a : G) := by rw [h1]
        _ = (ι a : G) * c := by group
    have h1 := hrank (ι a : G) (ι a).2 (fun h => ha1 (Subtype.ext h)) (C.map D.subtype)
      (Subgroup.map_subtype_le C) hC
    rwa [← CFSG.RankThree.PartTwo.pRank_congr_mulEquiv hp.out.one_lt
      (C.equivMapOfInjective D.subtype D.subtype_injective)] at h1
  have hA : Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n := by
    rw [← Nat.card_congr eE.toEquiv, hn]
  have h2x : ∀ x : Additive (Multiplicative (Fin n → ZMod 2)), 2 • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow]
    exact (congrArg Additive.ofMul (hA2 (Additive.toMul x))).trans ofMul_one
  have hbound := (@CFSG.RankThree.Coprime.class_two_involution_fixed_rank_bound p hp
    (hp.out.odd_of_ne_two hp2) D _ _ hDp hexp hclass
    (Multiplicative (Fin n → ZMod 2)) _ _ (AddCommGroup.zmodModule (n := 2) h2x) n 2 hA act
    hfaithful hm).1
  omega

end CFSG.RankThree.PartTwo.Sec21.Hering233i
