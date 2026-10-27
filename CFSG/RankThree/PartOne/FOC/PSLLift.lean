module

public import CFSG.RankThree.PartOne.FOC.TorusHom
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.RankThree.PartOne.FOC

open CFSG
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Lift

variable {n : ℕ} {K : Type} [Field K]

theorem eq_one_of_mem_scalars_pow {p : ℕ} (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (scalars n K))
    {z : Matrix.SpecialLinearGroup (Fin n) K} (hz : z ∈ scalars n K) (hzp : z ^ p = 1) :
    z = 1 := by
  have hzs : ((⟨z, hz⟩ : scalars n K)) ^ p = 1 := Subtype.ext hzp
  have hdvd : orderOf (⟨z, hz⟩ : scalars n K) ∣ p := orderOf_dvd_of_pow_eq_one hzs
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · have : (⟨z, hz⟩ : scalars n K) = 1 := orderOf_eq_one_iff.mp h1
    exact congrArg Subtype.val this
  · exfalso
    apply hZ
    rw [← h1]
    exact orderOf_dvd_natCard _

theorem commute_of_proj_commute {p : ℕ} (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (scalars n K))
    {A B : Matrix.SpecialLinearGroup (Fin n) K} (hAp : A ^ p = 1)
    (hc : proj n K A * proj n K B = proj n K B * proj n K A) : A * B = B * A := by
  set z : Matrix.SpecialLinearGroup (Fin n) K := B * A * B⁻¹ * A⁻¹ with hz
  have hzs : z ∈ scalars n K := by
    rw [← ker_proj, MonoidHom.mem_ker, hz]
    simp only [map_mul, map_inv]
    rw [← hc]
    group
  have hzc : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    rw [← scalars_eq_center n K]
    exact hzs
  have hBA : B * A * B⁻¹ = z * A := by rw [hz]; group
  have hcomm : Commute z A := Subgroup.mem_center_iff.mp hzc A |>.symm
  have h1 : (z * A) ^ p = z ^ p := by
    rw [hcomm.mul_pow, hAp, mul_one]
  have h2 : (z * A) ^ p = 1 := by
    rw [← hBA, conj_pow, hAp]
    simp
  have hzp : z ^ p = 1 := h1.symm.trans h2
  have hz1 : z = 1 := eq_one_of_mem_scalars_pow hp hZ hzs hzp
  rw [hz1, one_mul] at hBA
  exact (mul_inv_eq_iff_eq_mul.mp hBA).symm

theorem exists_lift_pow_eq_one {p : ℕ} (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (scalars n K))
    {x : projectiveSL n K} (hxp : x ^ p = 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) K, proj n K A = x ∧ A ^ p = 1 := by
  obtain ⟨A₀, rfl⟩ := proj_surjective n K x
  have hA0 : A₀ ^ p ∈ scalars n K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_pow]
    exact hxp
  set z : ℕ := Nat.card (scalars n K) with hzdef
  have hcop : Nat.Coprime z p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hZ).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨A₀ ^ (z * m), ?_, ?_⟩
  · rw [map_pow]
    have h1 : z * m = p * (z * m / p) + 1 := by
      have := Nat.div_add_mod (z * m) p
      rw [hm] at this
      omega
    rw [h1, pow_add, pow_mul, hxp, one_pow, one_mul, pow_one]
  · have h2 : (⟨A₀ ^ p, hA0⟩ : scalars n K) ^ z = 1 := pow_card_eq_one'
    have h3 : (A₀ ^ p) ^ z = 1 := congrArg Subtype.val h2
    calc (A₀ ^ (z * m)) ^ p = ((A₀ ^ p) ^ z) ^ m := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [h3, one_pow]

theorem not_dvd_card_scalars_of_localRankLeTwo [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 1 ≤ n) (hrank : LocalRankLeTwo p (projectiveSL n K)) :
    ¬ p ∣ Nat.card (scalars n K) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := scalars n K) p hdvd
  obtain ⟨c, hc, hmat⟩ := z.2
  have hzp : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : (z : Matrix.SpecialLinearGroup (Fin n) K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hcp : c ^ p = 1 := by
    have h2 : ((z : Matrix.SpecialLinearGroup (Fin n) K)) ^ p = 1 := by
      rw [← Subgroup.coe_pow, hzp]
      rfl
    have h3 : ((z : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, h2]
      rfl
    rw [hmat, ← map_pow] at h3
    have h4 : ((c : K) ^ p) = 1 := by
      have i0 : Fin n := ⟨0, hn⟩
      have h5 := congrFun (congrFun h3 i0) i0
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h5
    exact Units.ext (by simpa using h4)
  have hc1 : c ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    rw [hmat, h, Units.val_one, map_one]
    rfl
  have hordc : orderOf c = p := orderOf_eq_prime hcp hc1
  have hpn : p ∣ n := hordc ▸ orderOf_dvd_of_pow_eq_one hc
  have hpK : p ∣ Nat.card Kˣ := hordc ▸ orderOf_dvd_natCard c
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn hpn)
  exact not_localRankLeTwo_of_SL_hom hp hn5 hpK (proj n K) (fun s hs => by
    rw [← scalars_eq_center, ← ker_proj]
    exact hs) hrank

end Lift

end CFSG.RankThree.PartOne.FOC
