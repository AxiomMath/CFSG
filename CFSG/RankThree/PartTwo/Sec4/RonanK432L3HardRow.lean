module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardMat
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3Easy
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
import CFSG.Open.PGLModelStated

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.PGLModel (projImage)
open CFSG.Assembly.RankThreeEven (projSL projSU)

instance finite_projImage_fin {n : ℕ} {K : Type} [Field K] [Finite K]
    (H : Subgroup (GL (Fin n) K)) : Finite (projImage H) := by
  haveI : Finite (Matrix.ProjGenLinGroup (Fin n) K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin n) K →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

theorem listRow_projImage_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ListRow (projImage (slPi π 3 (p ^ f) K)) := by
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 3) K →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  refine L3Hard.listRow_map_of_witness
    (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 3) K →* _)
    (slPi π 3 (p ^ f) K) ?_
  intro x hxL ho
  have hx1 : Matrix.ProjGenLinGroup.mk x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ho
    omega
  have hx3 : Matrix.ProjGenLinGroup.mk (x ^ 3) = 1 := by
    rw [map_pow]
    have := pow_orderOf_eq_one (Matrix.ProjGenLinGroup.mk x)
    rwa [ho] at this
  exact L3Hard.exists_witness_of_order_three hK hq hxL
    (fun h => hx1 (mk_eq_one_iff_mem_statedScalars.mpr h))
    (mk_eq_one_iff_mem_statedScalars.mp hx3)

theorem listRow_projSL_three_of_mod_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 1) : ListRow (projSL 3 K) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hcard' : Nat.card K = ringChar K ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hPi : PiField true (ringChar K) (n : ℕ) K := ⟨hp, n.pos, by simpa [piCard] using hcard'⟩
  have hq : ModThree true (ringChar K ^ (n : ℕ)) := by
    change ringChar K ^ (n : ℕ) % 3 = 1
    rw [← hcard']
    exact hK
  exact ListRow.of_mulEquiv (MulEquiv.subgroupCongr (CFSG.PGLModel.projImage_statedSL 3 K))
    (listRow_projImage_slPi hPi hq)

theorem listRow_projSL_three_galoisField_of_mod_one {p e : ℕ} [Fact p.Prime] (he : e ≠ 0)
    (hmod : p ^ e % 3 = 1) : ListRow (projSL 3 (GaloisField p e)) :=
  listRow_projSL_three_of_mod_one (by rw [GaloisField.card p e he]; exact hmod)

theorem listRow_projSU_three_of_mod_two {p f : ℕ} [Fact p.Prime] (hf : f ≠ 0)
    (hq : p ^ f % 3 = 2) : ListRow (projSU 3 p f) := by
  have hPi : PiField false p f (GaloisField p (2 * f)) :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf, by
      rw [GaloisField.card p (2 * f) (by omega)]
      change p ^ (2 * f) = (p ^ f) ^ 2
      rw [← pow_mul, mul_comm]⟩
  exact ListRow.of_mulEquiv (MulEquiv.subgroupCongr (CFSG.PGLModel.projImage_statedSU 3 p f))
    (listRow_projImage_slPi hPi (show ModThree false (p ^ f) from hq))

theorem two_pow_mod_three_of_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem listRow_projSL_three_two_pow_of_even {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    ListRow (projSL 3 (GaloisField 2 n)) :=
  listRow_projSL_three_galoisField_of_mod_one hn0 (two_pow_mod_three_of_even hn)

theorem listRow_projSU_three_two_pow_of_odd {n : ℕ} (hn : Odd n) : ListRow (projSU 3 2 n) :=
  listRow_projSU_three_of_mod_two hn.pos.ne' (two_pow_mod_three_of_odd hn)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
