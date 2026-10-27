module

public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley (adjointGroup ModGL entrywise entrywiseHom TwistTag)

open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor fieldActorHom fieldActor_one)

private theorem k1566l5b_two_le_pow {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    (2 : ℤ) ≤ (p : ℤ) ^ f := by
  have h1 : (1 : ℤ) < (p : ℤ) ^ f := by
    exact_mod_cast (Nat.one_lt_pow (n := f) (a := p) (by omega) hp.one_lt : 1 < p ^ f)
  omega

private theorem k1566l5b_sub_ne_zero {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) : eps * (p : ℤ) ^ f - 1 ≠ 0 := by
  have h := k1566l5b_two_le_pow hp hf
  rcases heps with rfl | rfl <;> omega

private theorem k1566l5b_natAbs_eq {p f : ℕ} {eps : ℤ} (heps : eps = 1 ∨ eps = -1) :
    Int.natAbs (eps * (p : ℤ) ^ f - 1) = Int.natAbs ((p : ℤ) ^ f - eps) := by
  rcases heps with rfl | rfl
  · rw [one_mul]
  · rw [show (-1 : ℤ) * (p : ℤ) ^ f - 1 = -((p : ℤ) ^ f + 1) by ring, Int.natAbs_neg]
    rw [show (p : ℤ) ^ f - (-1) = (p : ℤ) ^ f + 1 by ring]

private theorem k1566l5b_zmod_actor {p f : ℕ} {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    (h : (p : ZMod 3) ^ f = (eps : ZMod 3)) :
    ((eps * (p : ℤ) ^ f : ℤ) : ZMod 3) = 1 := by
  rcases heps with rfl | rfl
  · rw [one_mul]
    push_cast
    rw [h]
    decide
  · push_cast
    rw [h]
    decide

theorem numerics_d4 {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    {eps : ℤ} (heps : eps = 1 ∨ eps = -1) (h : (p : ZMod 3) ^ f = (eps : ZMod 3)) :
    ((eps * (p : ℤ) ^ f : ℤ) : ZMod 3) = 1 ∧
      ¬ (3 : ℤ) ^ max (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)) + 1)
          (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) ∣ eps * (p : ℤ) ^ f - 1 := by
  have _ := hp3
  refine ⟨k1566l5b_zmod_actor heps h, ?_⟩
  rw [max_eq_left (Nat.le_succ _)]
  have hN : Int.natAbs (eps * (p : ℤ) ^ f - 1) ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact k1566l5b_sub_ne_zero hp hf heps
  have hkey : ¬ (3 : ℕ) ^ (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)) + 1) ∣
      Int.natAbs ((p : ℤ) ^ f - eps) := by
    have hk := pow_succ_padicValNat_not_dvd (p := 3)
      (n := Int.natAbs (eps * (p : ℤ) ^ f - 1)) hN
    rw [k1566l5b_natAbs_eq heps] at hk
    exact hk
  intro hdvd
  refine hkey ?_
  have h1 := Int.natAbs_dvd_natAbs.mpr hdvd
  rw [Int.natAbs_pow, show (3 : ℤ).natAbs = 3 by norm_num,
    k1566l5b_natAbs_eq heps] at h1
  exact h1

theorem d4_actor_cube {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ (p ^ f)) :
    fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext (fun c => ?_)
    have := Fintype.ofFinite K
    have hc := FiniteField.pow_card c
    have hcard : Fintype.card K = (p ^ f) ^ 3 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK
    rw [hcard] at hc
    have h1 : (σ ^ 3) c = σ (σ (σ c)) := by
      simp [pow_succ, RingAut.mul_apply]
    have h2 : σ (σ (σ c)) = c ^ ((p ^ f) ^ 3) := by
      rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
      congr 1
      ring
    show (σ ^ 3) c = c
    rw [h1, h2]
    exact hc
  have h3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = fieldActor (t := TwistTag.D4) σ (σ ^ 3) :=
    (map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3).symm
  rw [h3, hσ3]
  exact fieldActor_one σ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
