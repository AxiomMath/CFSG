module

public import CFSG.RankThree.PartOne.KF.ClsLift
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.KF.U4Model

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover Matrix Subgroup

theorem isPerfect_sl2 {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) K) := by
  have : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    have hle : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact h4
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  exact (CFSG.RankThree.Classical.isQuasisimple_SL2 this).1

theorem exceptionalOrders_psl_two {f : ℕ} :
    Blueprint.Multiplier.exceptionalOrders .PSL 2 2 f = (2, 1) ∨
      Blueprint.Multiplier.exceptionalOrders .PSL 2 2 f = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem genericOrders_psl_two {f : ℕ} (hf : 1 ≤ f) :
    Blueprint.Multiplier.genericOrders .PSL 2 2 f = (1, 1) := by
  have hodd : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hm : (2 ^ f - 1) % 2 = 1 := by omega
    rw [Nat.gcd_rec, hm]
    rfl
  show (Nat.gcd 2 (2 ^ f - 1), 1) = (1, 1)
  rw [hodd]

theorem card_hopfMultiplier_sl2_dvd_two
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    Nat.card (hopfMultiplier (SpecialLinearGroup (Fin 2) K)) ∣ 2 := by
  have hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  obtain ⟨e⟩ := nonempty_SL2_mulEquiv_statedProj (F := K)
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hadm : StatedLieAdmissible .PSL 2 2 f := by
    refine ⟨Nat.prime_two, by omega, le_refl 2, ?_, ?_⟩
    · intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
    · intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
  have hm : Models.LieModel (SpecialLinearGroup (Fin 2) K) .PSL 2 2 f :=
    ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e⟩⟩⟩
  have hcard := (card_hopfMultiplier_of_model hGA hm).2
  have hgen := genericOrders_psl_two (f := f) (by omega)
  have hexc := exceptionalOrders_psl_two (f := f)
  rw [hcard]
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen]
  rcases hexc with h | h <;> rw [h] <;> simp

theorem exists_lift_four_commuting_sl2
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {L X : Type} [Group L] [Group X] (π : L →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center L) (hodd : Nat.Coprime 2 (Nat.card π.ker))
    (φ : Fin 4 → SpecialLinearGroup (Fin 2) K →* X) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A) :
    ∃ φ' : Fin 4 → SpecialLinearGroup (Fin 2) K →* L, (∀ i, Function.Injective (φ' i)) ∧
      ∀ i j, i ≠ j → ∀ A B, φ' i A * φ' j B = φ' j B * φ' i A := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) := isPerfect_sl2 h4
  have hdvd := card_hopfMultiplier_sl2_dvd_two hGA hf hK
  obtain ⟨k, hk⟩ := hdvd
  have hM : ∀ m ∈ hopfMultiplier (SpecialLinearGroup (Fin 2) K), m ^ 2 = 1 := by
    intro m hm
    have h1 : (⟨m, hm⟩ : hopfMultiplier (SpecialLinearGroup (Fin 2) K)) ^
        Nat.card (hopfMultiplier (SpecialLinearGroup (Fin 2) K)) = 1 := pow_card_eq_one'
    have h2 : m ^ Nat.card (hopfMultiplier (SpecialLinearGroup (Fin 2) K)) = 1 :=
      congrArg Subtype.val h1
    have h3 : m ^ (Nat.card (hopfMultiplier (SpecialLinearGroup (Fin 2) K)) * k) = 1 := by
      rw [pow_mul, h2, one_pow]
    rwa [← hk] at h3
  have hZ : ∀ z ∈ π.ker, z ^ Nat.card π.ker = 1 := by
    intro z hz
    have h1 : (⟨z, hz⟩ : π.ker) ^ Nat.card π.ker = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  choose σ hσ using fun i =>
    exists_lift_of_coprime (φ i) π hπ hker hodd hM hZ
  have hσA : ∀ i A, π (σ i A) = φ i A := fun i A => DFunLike.congr_fun (hσ i) A
  refine ⟨σ, fun i => ?_, fun i j hij A B => ?_⟩
  · intro A B hAB
    exact hφ i (by rw [← hσA, ← hσA, hAB])
  · refine commute_of_central_commute π hker (σ i) (σ j) (fun A B => ?_) A B
    rw [hσA, hσA]
    exact hcomm i j hij A B

end CFSG.RankThree.PartOne.KFU
