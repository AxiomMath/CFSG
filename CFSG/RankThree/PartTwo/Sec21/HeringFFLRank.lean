module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFPaperReduce
public import CFSG.RankThree.PartTwo.Sec21.HeringFFNormal
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Open (IsElemAbelian IsTwoLocal)

private theorem ffL_false_of_central_three {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥X)) (e : ↥X) (he : e ∈ Subgroup.center ↥X)
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let z : ↥(Subgroup.center ↥X) := ⟨e, he⟩
  have hz3 : z ^ 3 = 1 := Subtype.ext he3
  have hz1 : z ≠ 1 := fun h => he1 (congrArg (fun w : ↥(Subgroup.center ↥X) => (w : ↥X)) h)
  exact hZ3 ((orderOf_eq_prime hz3 hz1) ▸ orderOf_dvd_natCard z)

theorem exists_elemAbelian_card_mul {H : Type} [Group H] [Finite H] {N P Q : Subgroup H}
    (hP : IsElemAbelian 3 P) (hQ : IsElemAbelian 3 Q) (hPN : P ≤ N) (hQN : Q ≤ N)
    (hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) (hdisj : ∀ x ∈ P, x ∈ Q → x = 1) :
    ∃ K ≤ N, IsElemAbelian 3 K ∧ Nat.card K = Nat.card P * Nat.card Q := by
  have hPc : ∀ x₁ x₂ : P, Commute (x₁ : H) (x₂ : H) := fun x₁ x₂ =>
    congrArg Subtype.val (hP.1.is_comm.comm x₁ x₂)
  have hQc : ∀ y₁ y₂ : Q, Commute (y₁ : H) (y₂ : H) := fun y₁ y₂ =>
    congrArg Subtype.val (hQ.1.is_comm.comm y₁ y₂)
  have hPQc : ∀ x : P, ∀ y : Q, Commute (x : H) (y : H) := fun x y => hcomm x x.2 y y.2
  set φ : P × Q →* H := P.subtype.noncommCoprod Q.subtype (fun x y => hPQc x y) with hφ
  have hφapp : ∀ p : P × Q, φ p = (p.1 : H) * (p.2 : H) := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    rw [MonoidHom.mem_ker, hφapp] at hxy
    have hx : (x : H) = ((y : H))⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hx1 : (x : H) = 1 := hdisj x x.2 (by rw [hx]; exact Q.inv_mem y.2)
    have hy1 : (y : H) = 1 := by rw [hx1, one_mul] at hxy; exact hxy
    exact Subgroup.mem_bot.mpr (Prod.ext (Subtype.ext hx1) (Subtype.ext hy1))
  have hRc : ∀ p q : P × Q, Commute (φ p) (φ q) := by
    rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    rw [hφapp, hφapp]
    exact Commute.mul_left (Commute.mul_right (hPc x₁ x₂) (hPQc x₁ y₂))
      (Commute.mul_right (hPQc x₂ y₁).symm (hQc y₁ y₂))
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [hφapp]
    exact Subgroup.mul_mem _ (hPN x.2) (hQN y.2)
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun r hr => ?_⟩
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      obtain ⟨p, rfl⟩ := ha
      obtain ⟨q, rfl⟩ := hb
      exact Subtype.ext (hRc p q).eq
    · obtain ⟨⟨x, y⟩, rfl⟩ := hr
      show ((x : H) * (y : H)) ^ 3 = 1
      rw [(hPQc x y).mul_pow, hP.2 x x.2, hQ.2 y y.2, mul_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

theorem ffLocalRankC_of_kE9 (hK : FFKE9) : FFLocalRankC := by
  intro G _ _ A a X hpt hX hXq _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ := Sec6.isQuasisimple_of_mem_thetaComponentsAt hpt.mem_theta
  have hmodel := ff_statedModel_center hXq hX hQ
  have hZ3 := ff_not_three_dvd_card_center hXq hX hQ
  obtain ⟨E₀, V₀, hE₀, hE₀9, hV₀, hV₀2, hE₀V₀⟩ := hK ↥X hXq hZ3 hmodel
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hpt.mem_theta
  have hAab := hpt.mem_S.1.1
  have ha3 : a ^ 3 = 1 := hAab.2 a hpt.mem
  have ha1 : a ≠ 1 := hpt.ne_one
  have h3 : localRank 3 G = 3 := hpt.standing.toTheoremFourHyp.localRank_three
  refine le_antisymm ?_ (localRank_subgroup_le Nat.prime_three _)
  rw [h3]
  have haC : a ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hCdef
  set a' : ↥C := ⟨a, haC⟩ with ha'def
  have ha'C : a' ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hZc : Subgroup.zpowers a' ≤ Subgroup.center ↥C := Subgroup.zpowers_le.mpr ha'C
  have ha'3 : a' ^ 3 = 1 := Subtype.ext ha3
  have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hZcard : Nat.card (Subgroup.zpowers a') = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha'3 ha'1]
  have hZab : IsElemAbelian 3 (Subgroup.zpowers a') := CFSG.Open.isElemAbelian_zpowers ha'3
  set ι : ↥X →* ↥C := Subgroup.inclusion hXC with hι
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective hXC
  set E : Subgroup ↥C := E₀.map ι with hE
  set V : Subgroup ↥C := V₀.map ι with hV
  have hEab : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.map hE₀ ι
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective hιinj]
    exact hE₀9
  have hVne : V ≠ ⊥ := fun h => hV₀ ((Subgroup.map_eq_bot_iff_of_injective V₀ hιinj).mp h)
  have hV2 : IsPGroup 2 V := hV₀2.map ι
  have hEN : E ≤ Subgroup.normalizer (V : Set ↥C) :=
    (Subgroup.map_mono hE₀V₀).trans (Subgroup.le_normalizer_map ι)
  have hZN : Subgroup.zpowers a' ≤ Subgroup.normalizer (V : Set ↥C) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h _ => Subgroup.mem_center_iff.mp ha'C h))
  have hdisj : ∀ x ∈ E, x ∈ Subgroup.zpowers a' → x = 1 := by
    rintro x hxE hxZ
    obtain ⟨e, he, rfl⟩ := hxE
    by_contra hne
    have hec : e ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp (hZc hxZ) (ι k))
      exact h
    exact ffL_false_of_central_three hZ3 e hec (hE₀.2 e he)
      (fun h => hne (by rw [h, map_one]))
  have hcomm : ∀ x ∈ E, ∀ y ∈ Subgroup.zpowers a', x * y = y * x :=
    fun x _ y hy => Subgroup.mem_center_iff.mp (hZc hy) x
  obtain ⟨K, hKN, hKab, hKcard⟩ :=
    exists_elemAbelian_card_mul (N := Subgroup.normalizer (V : Set ↥C)) hEab hZab hEN hZN
      hcomm hdisj
  have hK27 : Nat.card K = 3 ^ 3 := by rw [hKcard, hE9, hZcard]; norm_num
  have hH2 : IsTwoLocal (Subgroup.normalizer (V : Set ↥C)) := ⟨V, hVne, hV2, rfl⟩
  have hp3 : 3 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (V : Set ↥C)) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three
      (Subgroup.normalizer (V : Set ↥C))) ⟨K, hKN, hKab, hK27⟩
  have hbdd : BddAbove {k | ∃ H : Subgroup ↥C, IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} := by
    refine ⟨Nat.card ↥C, ?_⟩
    rintro _ ⟨Z, -, rfl⟩
    exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card 3 Nat.prime_three Z).trans
      (Subgroup.card_le_card_group Z)
  exact hp3.trans (le_csSup hbdd ⟨_, hH2, rfl⟩)

end CFSG.RankThree.PartTwo.Sec21
