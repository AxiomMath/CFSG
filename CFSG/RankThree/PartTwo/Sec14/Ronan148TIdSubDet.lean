module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseIc

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree slPi glPi Type123)
open Matrix (GeneralLinearGroup)

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

private theorem three_coprime_qSubPi {π : Bool} {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hNM : ¬ ModThree π (p ^ f)) : Nat.Coprime 3 (Sec4.qSubPi π (p ^ f)) := by
  have h0 : ¬ 3 ∣ p ^ f := fun h => hp3 <|
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h)).symm
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  cases π
  · change ¬ (p ^ f % 3 = 2) at hNM
    change ¬ 3 ∣ p ^ f + 1
    generalize p ^ f = q at h0 hNM ⊢
    omega
  · change ¬ (p ^ f % 3 = 1) at hNM
    change ¬ 3 ∣ p ^ f - 1
    generalize p ^ f = q at h0 hNM ⊢
    omega

private theorem cube_surjective_rootsOfUnity [Finite K] {n : ℕ} (hn : Nat.Coprime 3 n) :
    Function.Surjective (fun x : rootsOfUnity n K => x ^ 3) := by
  have hinj : Function.Injective (powMonoidHom 3 : rootsOfUnity n K →* rootsOfUnity n K) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h3 : (x : Kˣ) ^ 3 = 1 := congrArg Subtype.val hx
    have hxn : (x : Kˣ) ^ n = 1 := (mem_rootsOfUnity n (x : Kˣ)).mp x.2
    have hg : (x : Kˣ) ^ Nat.gcd 3 n = 1 := pow_gcd_eq_one.mpr ⟨h3, hxn⟩
    have hg1 : Nat.gcd 3 n = 1 := hn
    rw [hg1, pow_one] at hg
    exact Subtype.ext hg
  exact Finite.injective_iff_surjective.mp hinj

theorem exists_slPi_mul_scalar_of_not_modThree (hK : PiField π p f K) (hp3 : p ≠ 3)
    (hNM : ¬ ModThree π (p ^ f)) {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K) :
    ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z : Kˣ, y = l * GeneralLinearGroup.scalar (Fin 3) z := by
  haveI : Finite K := hK.finite
  obtain ⟨μ, hμ⟩ := cube_surjective_rootsOfUnity (three_coprime_qSubPi hK.prime hp3 hNM)
    ⟨GeneralLinearGroup.det y, Sec4.det_mem_rootsOfUnity hK hy⟩
  have hμ3 : (μ : Kˣ) ^ 3 = GeneralLinearGroup.det y := congrArg Subtype.val hμ
  have hdet : (y : Matrix (Fin 3) (Fin 3) K).det = ((μ : Kˣ) : K) ^ 3 := by
    rw [← GeneralLinearGroup.val_det_apply, ← hμ3, Units.val_pow_eq_pow_val]
  obtain ⟨l, hl, hz, -⟩ := Sec4.exists_inner_of_det_eq_cube hK hy
    ((Sec4.scalar_mem_glPi_iff hK (μ : Kˣ)).mpr μ.2) hdet
  exact ⟨l, hl, hz⟩

theorem exists_pow_mul_slPi_mul_scalar (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y y' : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K) (hy' : y' ∈ glPi π 3 (p ^ f) K)
    (h3 : Type123 π (p ^ f) K y 3) :
    ∃ k : ℕ, ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z : Kˣ,
      y ^ k * y' = l * GeneralLinearGroup.scalar (Fin 3) z := by
  haveI : Finite K := hK.finite
  let β : rootsOfUnity (Sec4.qSubPi π (p ^ f)) K :=
    ⟨GeneralLinearGroup.det y, Sec4.det_mem_rootsOfUnity hK hy⟩
  let α : rootsOfUnity (Sec4.qSubPi π (p ^ f)) K :=
    ⟨GeneralLinearGroup.det y', Sec4.det_mem_rootsOfUnity hK hy'⟩
  have hβ : ∀ μ : rootsOfUnity (Sec4.qSubPi π (p ^ f)) K, μ ^ 3 ≠ β := by
    intro μ hμ
    have hμ3 : (μ : Kˣ) ^ 3 = GeneralLinearGroup.det y := congrArg Subtype.val hμ
    have hdet : (y : Matrix (Fin 3) (Fin 3) K).det = ((μ : Kˣ) : K) ^ 3 := by
      rw [← GeneralLinearGroup.val_det_apply, ← hμ3, Units.val_pow_eq_pow_val]
    obtain ⟨l, hl, -, hin⟩ := Sec4.exists_inner_of_det_eq_cube hK hy
      ((Sec4.scalar_mem_glPi_iff hK (μ : Kˣ)).mpr μ.2) hdet
    exact Sec4.not_inner_of_type3 hK hq hy h3 ⟨l, hl, fun m _ => hin m⟩
  obtain ⟨k, μ, hkμ⟩ := Sec4.exists_mul_pow_eq_cube α hβ
  have hkμ' : GeneralLinearGroup.det y' * GeneralLinearGroup.det y ^ k = (μ : Kˣ) ^ 3 :=
    congrArg Subtype.val hkμ
  have hyy : y ^ k * y' ∈ glPi π 3 (p ^ f) K := mul_mem (pow_mem hy k) hy'
  have hdetU : GeneralLinearGroup.det (y ^ k * y') = (μ : Kˣ) ^ 3 := by
    rw [map_mul, map_pow, mul_comm, hkμ']
  have hdet : ((y ^ k * y' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((μ : Kˣ) : K) ^ 3 := by
    rw [← GeneralLinearGroup.val_det_apply, hdetU, Units.val_pow_eq_pow_val]
  obtain ⟨l, hl, hz, -⟩ := Sec4.exists_inner_of_det_eq_cube hK hyy
    ((Sec4.scalar_mem_glPi_iff hK (μ : Kˣ)).mpr μ.2) hdet
  exact ⟨k, l, hl, hz⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
