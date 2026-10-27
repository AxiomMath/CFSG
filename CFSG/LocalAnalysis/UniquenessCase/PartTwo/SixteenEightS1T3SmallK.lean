module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCEngine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallKA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallKB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def T3ParabK {W : Type} [CommGroup W] (L K T : Subgroup (MulAut W)) (a : ℕ) : Prop :=
  ∃ J : Subgroup (MulAut W), T ≤ J ∧ J ≤ L ⊔ K ⊔ T ∧ Nat.card ↥J = 3 ^ a * Nat.card ↥T ∧
    ∀ x ∈ J, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1

theorem T3ParabK.of_kBar {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}
    (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    (hK : Nat.card ↥(s1t3KBar A L) = 168) {a : ℕ} (hP : T3Parab L T a) :
    T3ParabK L (s1t3KBar A L) T (a + 1) :=
  s16t3_kBar_of_parab h h7 hK hP

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.exists_permuting_of_parabolic_two (h : S16gRowCtx D V₀ V L hV)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k)
    {Kb : Subgroup (MulAut (Vtil V₀ V hV))} (hKM : Kb ≤ Mbar D.M V₀ V hV)
    (hKN : (Kb.subgroupOf (Mbar D.M V₀ V hV)).Normal) (hKs : IsSimpleGroup ↥Kb)
    (hKnc : ¬ IsMulCommutative ↥Kb)
    (hKmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥Kb) = 2 ^ k)
    (hLK : lBar V₀ V hV L ⊓ Kb = ⊥)
    {J : Subgroup (MulAut (Vtil V₀ V hV))} {a : ℕ} (hTJ : barSub V₀ V hV D.T ≤ J)
    (hJL : J ≤ lBar V₀ V hV L ⊔ Kb ⊔ barSub V₀ V hV D.T)
    (hJcard : Nat.card ↥J = 3 ^ a * Nat.card ↥(barSub V₀ V hV D.T))
    (hJexp : ∀ x ∈ J, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1) (ha : 2 ≤ a) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧ Nat.card ↥Y = 3 ^ a ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧ Permutes Y D.T :=
  s16t3_exists_permuting_of_parabolic_two h hsimple hmult hKM hKN hKs hKnc hKmult hLK hTJ hJL
    hJcard hJexp ha

theorem S16gRowCtx.false_of_parabolic_two (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hm : MBarGT D.M V₀ V 2) (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k)
    {Kb : Subgroup (MulAut (Vtil V₀ V hV))} (hKM : Kb ≤ Mbar D.M V₀ V hV)
    (hKN : (Kb.subgroupOf (Mbar D.M V₀ V hV)).Normal) (hKs : IsSimpleGroup ↥Kb)
    (hKnc : ¬ IsMulCommutative ↥Kb)
    (hKmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥Kb) = 2 ^ k)
    (hLK : lBar V₀ V hV L ⊓ Kb = ⊥)
    {J : Subgroup (MulAut (Vtil V₀ V hV))} {a : ℕ} (hTJ : barSub V₀ V hV D.T ≤ J)
    (hJL : J ≤ lBar V₀ V hV L ⊔ Kb ⊔ barSub V₀ V hV D.T)
    (hJcard : Nat.card ↥J = 3 ^ a * Nat.card ↥(barSub V₀ V hV D.T))
    (hJexp : ∀ x ∈ J, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1) (ha : 2 ≤ a)
    (hcase : V₀ ≠ ⊥ ∨ 3 ≤ a ∨
      ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧ Subgroup.centralizer ({v} : Set G) ≤ D.M) :
    False := by
  obtain ⟨Y, hYM, hY3, hYcard, hYexp, hYnc, hperm⟩ :=
    h.exists_permuting_of_parabolic_two hsimple hmult hKM hKN hKs hKnc hKmult hLK hTJ hJL hJcard
      hJexp ha
  refine h.false_of_permuting_three_of_good h3 hm hYM hY3 hYexp hYnc hperm ?_
  rcases hcase with hne | ha3 | hgood
  · exact Or.inl hne
  · refine Or.inr (Or.inl ?_)
    rw [hYcard]
    calc 9 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
  · exact Or.inr (Or.inr hgood)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
