module

public import CFSG.Quasithin.Background.F918K1
public import CFSG.Quasithin.Vol2.Ch10SecQ1SU3
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders
  CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

variable {X : Type} [Group X]

private theorem ns3_exists_quotient_surjective {G : Type} [Group G] (hX : NSGroup X)
    (Z : Subgroup G) [Z.Normal] (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (π : G →* X)
    (hπ : Function.Surjective π) : ∃ φ : G ⧸ Z →* X, Function.Surjective φ := by
  have hle := le_ker_of_commute hX.isSimple hX.noncomm Z hZ π hπ
  refine ⟨QuotientGroup.lift Z π hle, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := hπ x
  exact ⟨QuotientGroup.mk g, rfl⟩

private theorem ns3_nonempty_mulEquiv_quotient {G : Type} [Group G] (hX : NSGroup X)
    (Z : Subgroup G) [Z.Normal] (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (hGZ : IsSimpleGroup (G ⧸ Z)) (π : G →* X) (hπ : Function.Surjective π) :
    Nonempty (G ⧸ Z ≃* X) := by
  obtain ⟨φ, hφ⟩ := ns3_exists_quotient_surjective hX Z hZ π hπ
  have := hX.isSimple.toNontrivial
  exact nonempty_mulEquiv_of_surjective hGZ φ hφ

private theorem ns3_scalars_comm {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) :
    ∀ x ∈ (StatedScalars ι K).subgroupOf H, ∀ y ∈ (StatedScalars ι K).subgroupOf H,
      x * y = y * x :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_mul_comm H

theorem isShapeGroup_of_surjective_statedSL_two [Nontrivial X]
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (π : ↥(StatedSL 2 K) →* X) (hπ : Function.Surjective π) : Vol2.Ch10.SecA.IsShapeGroup X := by
  have := CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL2 hn hK
  have hsimple : IsSimpleGroup ↥(StatedSL 2 K) :=
    (specialLinearGroupEquivStatedSL 2 K).symm.isSimpleGroup
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective hsimple π hπ
  exact Or.inl ⟨n, hn, K, inferInstance, inferInstance, hK,
    ⟨e.symm.trans (specialLinearGroupEquivStatedSL 2 K).symm⟩⟩

theorem NSGroup.false_of_surjective_su3 (hX : NSGroup X)
    {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = (2 ^ a) ^ 2)
    (π : ↥(StatedSU 3 (2 ^ a) K) →* X) (hπ : Function.Surjective π) : False := by
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := ns3_scalars_comm (StatedSU 3 (2 ^ a) K)
  have : ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ a) K)).Normal :=
    Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 3) K) _
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  ·
    obtain ⟨φ, hφ⟩ := ns3_exists_quotient_surjective hX _ hZ π hπ
    have hcard : Nat.card (StatedProj (StatedSU 3 (2 ^ a) K)) = 72 := by
      rw [card_psu3 ha hK, show a = 1 by omega]
      norm_num
    have hdvd : Nat.card X ∣ 72 := by
      rw [← hcard, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    exact not_nsCard_of_dvd_smooth (a := 3) (b := 2) (c := 0) (d := 0)
      (hdvd.trans (by norm_num)) hX.card
  ·
    have hsimple : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ a) K)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 a hK 3 le_rfl
        (fun h => by
          have h2 : 2 ^ a = 2 := congrArg Prod.snd h
          have h4 : 4 ≤ 2 ^ a :=
            (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) ha2
          omega)
    obtain ⟨e⟩ := ns3_nonempty_mulEquiv_quotient hX _ hZ hsimple π hπ
    apply not_nsCard_psu3 ha2
    rw [← card_psu3 ha hK, Nat.card_congr e.toEquiv]
    exact hX.card

theorem NSGroup.false_of_surjective_sl3 (hX : NSGroup X)
    {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m))
    (π : ↥(StatedSL 3 K) →* X) (hπ : Function.Surjective π) : False := by
  have hZ := ns3_scalars_comm (StatedSL 3 K)
  have : ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)).Normal :=
    Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 3) K) _
  have := (CFSG.LinearGroups.linear_projective_simple (n := 3) (K := K) (by norm_num)
    (Or.inl le_rfl)).2.1
  have hsimple : IsSimpleGroup (StatedProj (StatedSL 3 K)) :=
    (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.isSimpleGroup
  obtain ⟨e⟩ := ns3_nonempty_mulEquiv_quotient hX _ hZ hsimple π hπ
  have hcard : Nat.card X = ordA 2 (2 ^ (2 * m)) := by
    rw [← Nat.card_congr e.toEquiv, card_statedProj_statedSL (by norm_num), hK]
    rfl
  exact not_nsCard_psl3 (e := 2 * m) (by omega) (hcard ▸ hX.card)

theorem NSGroup.false_of_surjective_sp4 (hX : NSGroup X)
    {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m))
    (π : ↥(StatedSp 2 K) →* X) (hπ : Function.Surjective π) : False := by
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr h4))
  have hbij : Function.Bijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  have hsimple' : IsSimpleGroup ↥(StatedSp 2 K) := (MulEquiv.ofBijective _ hbij).isSimpleGroup
  have := hX.isSimple.toNontrivial
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective hsimple' π hπ
  have hcard : Nat.card X =
      2 ^ (4 * (2 * m)) * ((2 ^ (2 * (2 * m)) - 1) * (2 ^ (4 * (2 * m)) - 1)) := by
    rw [← Nat.card_congr e.toEquiv, card_Sp4_pow hK]
  exact not_nsCard_Sp4 (n := 2 * m) (by omega) (hcard ▸ hX.card)

end CFSG.Quasithin
