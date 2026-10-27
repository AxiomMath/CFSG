module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.Q1327F

open CFSG CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders

theorem pow_dvd_card_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type}
    [Field K] [Finite K] {p m : ℕ} (hp : p.Prime) (hK : Nat.card K = p)
    (M : Subgroup (GL ι K)) (h : p ^ m ∣ Nat.card M) : p ^ m ∣ Nat.card (StatedProj M) := by
  classical
  set Z : Subgroup M := (StatedScalars ι K).subgroupOf M with hZ
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hZd : Nat.card Z ∣ Nat.card Kˣ := by
    have h1 : Z.map M.subtype ≤ StatedScalars ι K := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have h2 : Nat.card (Z.map M.subtype) ∣ Nat.card (StatedScalars ι K) :=
      Subgroup.card_dvd_of_le h1
    rw [Subgroup.card_map_of_injective M.subtype_injective] at h2
    have h3 : Nat.card (StatedScalars ι K) = Nat.card Kˣ := by
      have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar ι : Kˣ →* GL ι K) := by
        intro a b hab
        obtain ⟨i⟩ := ‹Nonempty ι›
        have := congrArg (fun A : GL ι K => ((A : GL ι K) : Matrix ι ι K) i i) hab
        exact Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar] using this)
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rwa [h3] at h2
  have hKu : Nat.card Kˣ = p - 1 := by
    rw [Nat.card_units, hK]
  have hcop : Nat.Coprime (p ^ m) (Nat.card Z) := by
    refine Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_)
    have h1 : p ∣ p - 1 := by
      rw [← hKu]
      exact hd.trans hZd
    have h2 := Nat.le_of_dvd (by have := hp.two_le; omega) h1
    have := hp.two_le
    omega
  rw [hc] at h
  exact hcop.dvd_of_dvd_mul_right h

theorem p_cube_dvd_card_psl_four {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) : p ^ 3 ∣ Nat.card (StatedProj (StatedSL 4 K)) := by
  rw [card_statedProj_statedSL (by norm_num), hK]
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hg : Nat.gcd 4 (p - 1) ∣ ∏ j ∈ Finset.Icc 2 4, (p ^ j - 1) := by
    refine (Nat.gcd_dvd_right 4 (p - 1)).trans ?_
    refine (show p - 1 ∣ p ^ 2 - 1 by
      have := Nat.sub_dvd_pow_sub_pow p 1 2
      simpa using this).trans ?_
    exact Finset.dvd_prod_of_mem (fun j => p ^ j - 1) (by decide : 2 ∈ Finset.Icc 2 4)
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.dvd.mul_right (pow_dvd_pow p (by norm_num)) _

theorem p_cube_dvd_card_psp_two {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) : p ^ 3 ∣ Nat.card (StatedProj (StatedSp 2 K)) := by
  refine pow_dvd_card_statedProj (ι := Fin 2 ⊕ Fin 2) hp hK _ ?_
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
  exact Dvd.dvd.mul_right (pow_dvd_pow p (by norm_num)) _

theorem p_cube_dvd_card_psu_four {K : Type} [Field K] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = (ℓ ^ 1) ^ 2) :
    ℓ ^ 3 ∣ Nat.card (StatedProj (StatedSU 4 (ℓ ^ 1) K)) := by
  rw [card_statedProj_statedSU hℓ le_rfl hK (by norm_num)]
  have hp1 : 1 ≤ ℓ := hℓ.one_lt.le
  have hg : Nat.gcd 4 (ℓ ^ 1 + 1) ∣
      ∏ i ∈ Finset.Icc 2 4, ((((ℓ ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) := by
    refine (Nat.gcd_dvd_right 4 (ℓ ^ 1 + 1)).trans ?_
    have h2 : (ℓ ^ 1 + 1) ∣ ((((ℓ ^ 1 : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat) := by
      have : ((((ℓ ^ 1 : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat) = (ℓ ^ 1 + 1) * (ℓ - 1) := by
        rw [pow_one]
        have h3 : (((ℓ : ℤ) ^ 2 - (-1) ^ 2) : ℤ) = ((ℓ + 1) * (ℓ - 1) : ℕ) := by
          push_cast [Nat.cast_sub hp1]
          ring
        rw [h3, Int.toNat_natCast]
      exact ⟨ℓ - 1, this⟩
    exact h2.trans (Finset.dvd_prod_of_mem (fun i => ((((ℓ ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat))
      (by decide : 2 ∈ Finset.Icc 2 4))
  rw [Nat.mul_div_assoc _ hg]
  refine Dvd.dvd.mul_right ?_ _
  rw [pow_one]
  exact pow_dvd_pow ℓ (by norm_num)

end CFSG.RankThree.PartOne.Q1327F
