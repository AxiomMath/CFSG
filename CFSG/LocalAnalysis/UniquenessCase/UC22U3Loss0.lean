module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
import CFSG.LocalAnalysis.UniquenessCase.UCKPOut
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.U3Loss

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem isSU3_of_isU3 {X : Type} [Group X] {n : ℕ} (hX : IsU3 X n) :
    IsSU3 X n ∧ center X = ⊥ := by
  haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 hX
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 hX
  have hnc : ¬ IsMulCommutative X := fun hc => hab (hc.is_comm.comm a b)
  have hc := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  haveI := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
  let e : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact ⟨⟨⟨Group.IsPerfect.commutator_eq_top, e.isSimpleGroup⟩,
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm hX⟩, hc⟩

theorem exists_equiv_primeFormP {X : Type} [Group X] {n : ℕ} (hX : IsU3 X n) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 n K),
      Nonempty (X ≃* primeFormP h (1 : Matrix (Fin 3) (Fin 3) K)) := by
  obtain ⟨⟨-, hn1, -, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.statedClassicalModel_of_lieModel_PSU3 hX
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn1, by rw [hK, ← pow_mul, mul_comm]⟩
  exact ⟨CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hX, K, inferInstance, h,
    ⟨e.trans (CFSG.ComponentClassification.Burgoyne.U.uTransport h (by norm_num))⟩⟩

theorem exists_pow_mul_mem_inner_u3 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU3 X n)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {x y : MulAut X} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x * y = y * x) (hxi : x ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ k : ℕ, x ^ k * y ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨N, hN, -, hcyc, hcube, -⟩ := UCK.u3OutShape X n (isSU3_of_isU3 hX).1
  have hinn : ∀ φ ∈ N, φ ^ p = 1 → φ ∈ (MulAut.conj : X →* MulAut X).range := by
    intro φ hφN hφ
    have hcop : Nat.Coprime 3 (orderOf φ) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hφ)
        ((Nat.coprime_primes Nat.prime_three hp).2 hp3.symm)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ (hcube φ hφN) m
  set π := QuotientGroup.mk' N with hπ
  have hker : ∀ z : MulAut X, π z = 1 ↔ z ∈ N := fun z => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hx1 : π x ≠ 1 := fun h1 => hxi (hinn x ((hker x).1 h1) hx)
  obtain ⟨k, hk⟩ := P22y.exists_pow_eq_of_isCyclic hp (a := π x) (b := π y)
    (by rw [← map_pow, hx, map_one]) hx1 (by rw [← map_pow, hy, map_one])
  refine ⟨(p - 1) * k, hinn _ ((hker _).1 ?_) ?_⟩
  · rw [map_mul, map_pow, ← hk, ← pow_add, show (p - 1) * k + k = p * k by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_lt.le], pow_mul,
      ← map_pow, hx, map_one, one_pow]
  · have hc : Commute (x ^ ((p - 1) * k)) y := Commute.pow_left hxy _
    rw [hc.mul_pow, ← pow_mul, mul_comm ((p - 1) * k) p, pow_mul, hx, one_pow, one_mul, hy]

end CFSG.LocalAnalysis.UniquenessCase.UC22.U3Loss
