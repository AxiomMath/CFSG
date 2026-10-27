module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSL3A
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.RankThree.PartOne.CTP.ExtA
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompA

public section

namespace CFSG.Quasithin.H13.S126C

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [Finite F]

theorem exists_sl3_inv_of_involution_sl {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hFc : Nat.card F = p) {ν : MulAut (SpecialLinearGroup (Fin 3) F)} (hν2 : ν ^ 2 = 1)
    (hν1 : ν ≠ 1) : ∃ T : SpecialLinearGroup (Fin 3) F, orderOf T = p ∧ ν T = T⁻¹ := by
  have hinj := CFSG.RankThree.PartOne.AUTSL.descendAut_injective (n := 3) (K := F) (by norm_num)
  obtain ⟨T, hT, -, hνT⟩ := exists_sl3_inv_of_involution hp hp2 hFc
    (ν := descendAut 3 F ν) (by rw [← map_pow, hν2, map_one])
    (fun h1 => hν1 (hinj (h1.trans (map_one _).symm)))
  refine ⟨T, hT, ?_⟩
  rw [descendAut_proj] at hνT
  set z := ν T * T with hz
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
    rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, hz, map_mul, hνT, map_inv,
      inv_mul_cancel]
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨a, ha, hm⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzc
    have ha3 : a ^ 3 = 1 := by simpa using ha
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hm]
    rw [← map_pow, ha3, map_one]
  have hνz : ν T = z * T⁻¹ := by rw [hz, mul_inv_cancel_right]
  have hzp : z ^ p = 1 := by
    have hTp : T ^ p = 1 := by rw [← hT]; exact pow_orderOf_eq_one T
    have h1 : (ν T) ^ p = 1 := by rw [← map_pow, hTp, map_one]
    have hcomm : Commute z T⁻¹ := ((Subgroup.mem_center_iff.mp hzc) T⁻¹).symm
    rw [hνz, hcomm.mul_pow, inv_pow, hTp, inv_one, mul_one] at h1
    exact h1
  have hz1 : z = 1 := by
    have h3 := orderOf_dvd_of_pow_eq_one hz3
    have hpd := orderOf_dvd_of_pow_eq_one hzp
    have hcop : Nat.Coprime 3 p :=
      (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h3 hpd)
  rw [hνz, hz1, one_mul]

theorem eq_three_or_five_of_autConf_psl3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hFc : Nat.card F = p) {ν : MulAut (projectiveSL 3 F)}
    {Lb Pb : Subgroup (MulAut (projectiveSL 3 F))} (h : AutConf (projectiveSL 3 F) ν Lb Pb) :
    p = 3 ∨ p = 5 := by
  obtain ⟨T, -, hTo, hνT⟩ := exists_sl3_inv_of_involution hp hp2 hFc h.sq h.ne_one
  rw [map_inv] at hνT
  rcases h.inv _ (by rw [hTo]; exact hp.odd_of_ne_two hp2) hνT with h3 | h5
  · have := orderOf_dvd_of_pow_eq_one h3
    rw [hTo] at this
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this)
  · have := orderOf_dvd_of_pow_eq_one h5
    rw [hTo] at this
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)

theorem eq_three_or_five_of_autConf_sl3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hFc : Nat.card F = p) {ν : MulAut (SpecialLinearGroup (Fin 3) F)}
    {Lb Pb : Subgroup (MulAut (SpecialLinearGroup (Fin 3) F))}
    (h : AutConf (SpecialLinearGroup (Fin 3) F) ν Lb Pb) : p = 3 ∨ p = 5 := by
  by_cases hp3 : p = 3
  · exact Or.inl hp3
  obtain ⟨T, hTo, hνT⟩ := exists_sl3_inv_of_involution_sl hp hp2 hp3 hFc h.sq h.ne_one
  rcases h.inv _ (by rw [hTo]; exact hp.odd_of_ne_two hp2) hνT with h3 | h5
  · have := orderOf_dvd_of_pow_eq_one h3
    rw [hTo] at this
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this)
  · have := orderOf_dvd_of_pow_eq_one h5
    rw [hTo] at this
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem Conf12626.eq_three_or_five_of_psl3 (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL3 : StatedClassicalModel ↥K .PSL 3 p 1) : p = 3 ∨ p = 5 := by
  have := hQ.finite
  obtain ⟨-, F, _, _, hFc, ⟨e⟩⟩ := hL3
  rw [pow_one] at hFc
  exact eq_three_or_five_of_autConf_psl3 hp hp2 hFc
    (h.autConf.map (e.trans (CFSG.RankThree.PartOne.CTP.projectiveSLEquivStated 3 F).symm))

theorem Conf12626.eq_three_or_five_of_sl3 (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hSL : IsSLEps3 true p ↥K) : p = 3 ∨ p = 5 := by
  have := hQ.finite
  obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hSL
  exact eq_three_or_five_of_autConf_sl3 hp hp2 hFc
    (h.autConf.map (e.trans (specialLinearGroupEquivStatedSL 3 F).symm))

end CFSG.Quasithin.H13.S126C
