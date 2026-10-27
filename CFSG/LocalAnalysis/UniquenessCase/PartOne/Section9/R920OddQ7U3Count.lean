module

public import Mathlib.GroupTheory.Index
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Subgroup MulAction

theorem relIndex_modEq_one {G : Type*} [Group G] [Finite G] {W B Z : Subgroup G}
    (hZW : Z ≤ W) (hZB : Z ≤ B)
    (hfix : ∀ ζ ∈ Z, ζ ≠ 1 → ∀ w ∈ W, w⁻¹ * ζ * w ∈ B → w ∈ B) :
    B.relIndex W ≡ 1 [MOD Nat.card Z] := by
  classical
  set H : Subgroup W := B.subgroupOf W with hH
  set Z' : Subgroup W := Z.subgroupOf W with hZ'
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (W ⧸ H) := Fintype.ofFinite _
  haveI : Fintype Z' := Fintype.ofFinite _
  haveI : ∀ g : Z', Fintype (fixedBy (W ⧸ H) g) := fun g => Fintype.ofFinite _
  haveI : Fintype (orbitRel.Quotient Z' (W ⧸ H)) := Fintype.ofFinite _
  have hburn := sum_card_fixedBy_eq_card_orbits_mul_card_group Z' (W ⧸ H)
  have hone : ∀ g : Z', g ≠ 1 → Fintype.card (fixedBy (W ⧸ H) g) = 1 := by
    intro g hg
    rw [Fintype.card_eq_one_iff]
    have hgZ : ((g : W) : G) ∈ Z := g.2
    have hg1 : ((g : W) : G) ≠ 1 := fun h => hg (Subtype.ext (Subtype.ext h))
    refine ⟨⟨(1 : W), ?_⟩, ?_⟩
    · show (g : W) • ((1 : W) : W ⧸ H) = (1 : W)
      change (((g : W) * 1 : W) : W ⧸ H) = ((1 : W) : W ⧸ H)
      rw [QuotientGroup.eq]
      simpa [hH, Subgroup.mem_subgroupOf] using hZB hgZ
    · rintro ⟨y, hy⟩
      induction y using QuotientGroup.induction_on with
      | H w =>
        refine Subtype.ext ?_
        change (w : W ⧸ H) = ((1 : W) : W ⧸ H)
        have hy' : (g : W) • (w : W ⧸ H) = w := hy
        change (((g : W) * w : W) : W ⧸ H) = (w : W ⧸ H) at hy'
        rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf] at hy'
        have hconj : (w : G)⁻¹ * ((g : W) : G) * (w : G) ∈ B := by
          have := inv_mem hy'
          simpa [mul_assoc] using this
        have hwB : (w : G) ∈ B := hfix _ hgZ hg1 (w : G) w.2 hconj
        rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf]
        simpa using hwB
  have hall : ∀ g : Z', Fintype.card (fixedBy (W ⧸ H) g) =
      1 + (if g = 1 then Fintype.card (W ⧸ H) - 1 else 0) := by
    intro g
    by_cases hg : g = 1
    · subst hg
      have : fixedBy (W ⧸ H) (1 : Z') = Set.univ := by
        ext y
        simp [mem_fixedBy]
      have hpos : 0 < Fintype.card (W ⧸ H) := Fintype.card_pos
      simp only [this, if_true]
      rw [Fintype.card_setUniv]
      omega
    · rw [hone g hg, if_neg hg]
  simp only [hall, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hburn
  have hcardZ : Fintype.card Z' = Nat.card Z := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv
  have hcardY : Fintype.card (W ⧸ H) = B.relIndex W := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcardZ, hcardY] at hburn
  have hpos : 0 < B.relIndex W := by
    rw [← hcardY]; exact Fintype.card_pos
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  generalize Fintype.card (Quotient (orbitRel (↥Z') (↥W ⧸ H))) = k at hburn
  have hsum : B.relIndex W + Nat.card Z = Nat.card Z * k + 1 := by
    rw [mul_comm]
    omega
  show B.relIndex W % Nat.card Z = 1 % Nat.card Z
  have h3 : (B.relIndex W + Nat.card Z) % Nat.card Z = (Nat.card Z * k + 1) % Nat.card Z := by
    rw [hsum]
  rwa [Nat.add_mod_right, Nat.mul_add_mod] at h3

theorem exists_mul_of_relIndex_eq {G : Type*} [Group G] [Finite G] {W B : Subgroup G}
    (h : B.relIndex W = B.index) (g : G) : ∃ w ∈ W, ∃ b ∈ B, g = w * b := by
  classical
  let f : W ⧸ B.subgroupOf W → G ⧸ B :=
    Quotient.map' (fun w : W => (w : G)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact Subgroup.mem_subgroupOf.1 hab)
  have hinj : Function.Injective f := by
    intro u v huv
    induction u using QuotientGroup.induction_on with
    | H a =>
      induction v using QuotientGroup.induction_on with
      | H b =>
        have h1 : ((a : G) : G ⧸ B) = ((b : G) : G ⧸ B) := huv
        rw [QuotientGroup.eq] at h1 ⊢
        exact Subgroup.mem_subgroupOf.2 h1
  have hcard : Nat.card (G ⧸ B) ≤ Nat.card (W ⧸ B.subgroupOf W) := by
    rw [Subgroup.index] at h
    rw [← Subgroup.index, ← Subgroup.index]
    exact (le_of_eq h.symm)
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨u, hu⟩ := hbij.2 (g : G ⧸ B)
  induction u using QuotientGroup.induction_on with
  | H w =>
    have h1 : ((w : G) : G ⧸ B) = (g : G ⧸ B) := hu
    rw [QuotientGroup.eq] at h1
    exact ⟨w, w.2, (w : G)⁻¹ * g, h1, by simp⟩

theorem eq_or_eq_of_modEq_one {q n : ℕ} (hq : 2 ≤ q) (h1 : n % q = 1) (h2 : (q + 1) ∣ n)
    (h3 : n ∣ q ^ 2 * (q ^ 3 + 1)) : n = q + 1 ∨ n = q ^ 3 + 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hcop : Nat.Coprime (r + 1) n := by
    rw [Nat.Coprime, Nat.gcd_rec, h1, Nat.gcd_one_left]
  have h4 : n ∣ (r + 1) ^ 3 + 1 :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left 2 hcop).symm h3
  obtain ⟨k, rfl⟩ := h2
  have hqm : (r + 1) ^ 3 + 1 = (r + 1 + 1) * ((r + 1) * r + 1) := by ring
  rw [hqm] at h4
  obtain ⟨l, hl⟩ := Nat.dvd_of_mul_dvd_mul_left (by omega) h4
  have hkq : k % (r + 1) = 1 := by
    have e : (r + 1 + 1) * k = k + (r + 1) * k := by ring
    rw [e, Nat.add_mul_mod_self_left] at h1
    exact h1
  have hmq : ((r + 1) * r + 1) % (r + 1) = 1 := by
    rw [add_comm, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hlq : l % (r + 1) = 1 := by
    have := hmq
    rw [hl, Nat.mul_mod, hkq, one_mul, Nat.mod_mod] at this
    exact this
  have hk' : k = (r + 1) * (k / (r + 1)) + 1 := by
    have := Nat.div_add_mod k (r + 1)
    omega
  have hl' : l = (r + 1) * (l / (r + 1)) + 1 := by
    have := Nat.div_add_mod l (r + 1)
    omega
  set a := k / (r + 1)
  set b := l / (r + 1)
  have hprod : ((r + 1) * a + 1) * ((r + 1) * b + 1) = (r + 1) * r + 1 := by
    rw [← hk', ← hl', ← hl]
  have h5 : (r + 1) * ((r + 1) * a * b + a + b) = (r + 1) * r := by
    nlinarith [hprod]
  have h6 : (r + 1) * a * b + a + b = r := Nat.eq_of_mul_eq_mul_left (by omega) h5
  rcases Nat.eq_zero_or_pos a with ha | ha
  · left
    rw [hk', ha]
    simp
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · right
      have hl1 : l = 1 := by rw [hl', hb]; simp
      rw [hl1, mul_one] at hl
      rw [← hl, hqm]
    · exfalso
      have : r + 1 ≤ (r + 1) * a * b := by
        calc r + 1 = (r + 1) * 1 * 1 := by ring
          _ ≤ (r + 1) * a * b := Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) ha) hb
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
