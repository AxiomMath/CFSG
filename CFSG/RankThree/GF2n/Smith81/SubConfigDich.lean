module

import CFSG.RankThree.GF2n.Smith81.OrthTensorModel
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.GF2n.Smith81.SubCfg

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

theorem card_dvd_or_eq_of_normal_prod {A B Ω : Type} [Group A] [Group B] [Group Ω] [Finite A]
    [Finite B] [IsSimpleGroup Ω] [IsSimpleGroup B] {P : Subgroup (A × B)} (hP : P.Normal)
    (e : ↥P ≃* Ω) : Nat.card Ω ∣ Nat.card A ∨ Nat.card Ω = Nat.card B := by
  haveI : IsSimpleGroup ↥P := e.isSimpleGroup
  let π₂ : ↥P →* B := (MonoidHom.snd A B).comp P.subtype
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π₂.ker with h | h
  · have hinj : Function.Injective π₂ := (MonoidHom.ker_eq_bot_iff π₂).mp h
    haveI hn : π₂.range.Normal := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact hP.map _ fun b => ⟨(1, b), rfl⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π₂.range with h' | h'
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥P)
      apply hx
      apply hinj
      have : π₂ x ∈ π₂.range := ⟨x, rfl⟩
      rw [h', Subgroup.mem_bot] at this
      rw [this, map_one]
    · right
      rw [← Nat.card_congr e.toEquiv, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, h',
        Subgroup.card_top]
  · left
    let π₁ : ↥P →* A := (MonoidHom.fst A B).comp P.subtype
    have hπ₂ : ∀ x : ↥P, π₂ x = 1 := fun x => by
      rw [← MonoidHom.mem_ker, h]
      trivial
    have hinj : Function.Injective π₁ := by
      intro x y hxy
      exact Subtype.ext (Prod.ext hxy ((hπ₂ x).trans (hπ₂ y).symm))
    rw [← Nat.card_congr e.toEquiv, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _

theorem dichotomy {X R : Type} [Group X] [Group R] (N₀ : Subgroup R) [N₀.Normal]
    [IsSimpleGroup (R ⧸ N₀)] {P Q' S' Mn : Subgroup X} (s : R →* ↥P)
    (hs : Function.Surjective s) (hsQ : ∀ x, ((s x : ↥P) : X) ∈ Q' ↔ x ∈ N₀) (hQS : Q' ≤ S')
    (hPM : P ≤ Mn) (hNP : S' ≤ Subgroup.normalizer (P : Set X))
    (hNS : Mn ≤ Subgroup.normalizer (S' : Set X)) :
    (∀ h ∈ P, ∀ y ∈ S', ⁅h, y⁆ ∈ Q') ∨ P ≤ S' := by
  let T : Subgroup R := S'.comap (P.subtype.comp s)
  have hT : T.Normal := by
    constructor
    intro x hx r
    show ((s (r * x * r⁻¹) : ↥P) : X) ∈ S'
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hNS (hPM (s r).2)) _).mp hx
  have hNT : N₀ ≤ T := fun x hx => hQS ((hsQ x).mpr hx)
  haveI : (T.map (QuotientGroup.mk' N₀)).Normal := hT.map _ (QuotientGroup.mk'_surjective N₀)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.map (QuotientGroup.mk' N₀)) with h | h
  · left
    have hTN : T ≤ N₀ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    intro p hp y hy
    have hpS : ⁅p, y⁆ ∈ S' := by
      rw [commutatorElement_def]
      exact S'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNS (hPM hp)) y).mp hy)
        (S'.inv_mem hy)
    have hpP : ⁅p, y⁆ ∈ P := by
      have h1 : y * p⁻¹ * y⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hNP hy) p⁻¹).mp (P.inv_mem hp)
      have h2 := P.mul_mem hp h1
      rw [commutatorElement_def]
      simpa only [mul_assoc] using h2
    obtain ⟨x, hx⟩ := hs ⟨⁅p, y⁆, hpP⟩
    have hxT : x ∈ T := by
      show ((s x : ↥P) : X) ∈ S'
      rw [hx]
      exact hpS
    have := (hsQ x).mpr (hTN hxT)
    rw [hx] at this
    exact this
  · right
    intro p hp
    obtain ⟨x, hx⟩ := hs ⟨p, hp⟩
    have hxT : x ∈ T := by
      have hmem : QuotientGroup.mk' N₀ x ∈ T.map (QuotientGroup.mk' N₀) := by
        rw [h]
        trivial
      obtain ⟨y, hyT, hyx⟩ := hmem
      have hyx' : y⁻¹ * x ∈ N₀ := QuotientGroup.eq.mp hyx
      have := T.mul_mem hyT (hNT hyx')
      simpa using this
    have : ((s x : ↥P) : X) ∈ S' := hxT
    rw [hx] at this
    exact this

theorem card_omegaPlus_eq_ordD {K : Type} [Field K] [Finite K] [CharP K 2] {m f : ℕ}
    (hm : 3 ≤ m) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    Nat.card ↥(StatedOmega (StatedQuadPlus m K)) = ordD m (2 ^ f) := by
  rw [ordD, Timmesfeld.ClassicalOrders.gcd_four_eq_one
    (Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hf (by omega)), Nat.div_one]
  apply Nat.cast_injective (R := ℤ)
  rw [card_statedOmega_plus_eq hm, hK]
  have hq : 1 ≤ (2 ^ f) ^ m := Nat.one_le_pow _ _ (by positivity)
  push_cast [hq,
    Timmesfeld.ClassicalOrders.cast_prod_pow_sub_one (Nat.one_le_pow f 2 (by norm_num))]
  rfl

end CFSG.RankThree.GF2n.Smith81.SubCfg
