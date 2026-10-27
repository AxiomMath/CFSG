module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.Quasithin

theorem isTransvection_of_rkIdx_lt {B : Type} [CommGroup B] [Finite B] (hB : ∀ b : B, b ^ 2 = 1)
    {s : MulAut B} (hs : s ≠ 1) (h : rkIdx (fixV (Subgroup.zpowers s)) < 2) :
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsTransvection s := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (commHom s).ker = fixV (Subgroup.zpowers s) := ker_commHom s
  have hidx_lt : padicValNat 2 (commHom s).ker.index < 2 := by
    simpa [rkIdx, hker] using h
  have hrange : Subgroup.closure (Set.range fun v : B => s v * v⁻¹) = (commHom s).range := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro x ⟨v, rfl⟩
      exact ⟨v, rfl⟩
    · rintro x ⟨v, rfl⟩
      exact Subgroup.subset_closure ⟨v, rfl⟩
  have hBcard : Nat.card B = 2 ^ rk B :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hB)
  have hdvd : (commHom s).ker.index ∣ 2 ^ rk B := by
    rw [← hBcard]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hjlt : j < 2 := by
    have h2 : padicValNat 2 (2 ^ j) < 2 := by rw [← hj]; exact hidx_lt
    rwa [padicValNat.prime_pow] at h2
  have hjne : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    have htop : (commHom s).ker = ⊤ := Subgroup.index_eq_one.mp hj
    have htriv : commHom s = 1 := by
      ext v
      exact MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top v)
    apply hs
    ext v
    have hv : (commHom s) v = 1 := congrArg (fun f => f v) htriv
    rw [commHom_apply, mul_inv_eq_one] at hv
    simpa using hv
  have hj1 : j = 1 := by omega
  have hcard : Nat.card (commHom s).range = 2 := by
    rw [← Subgroup.index_ker]
    rw [hj, hj1, pow_one]
  refine ⟨hs, ?_⟩
  rw [hrange, hcard]

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
