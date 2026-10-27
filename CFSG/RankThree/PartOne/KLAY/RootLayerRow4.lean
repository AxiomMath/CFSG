module

public import CFSG.RankThree.PartOne.KLAY.Sz
public import CFSG.RankThree.PartOne.KLAY.RootLayer

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem rootLayer_row4_s1
    {p a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hP : F4Param p a K)
    (v : Fin 2 → rootsOfUnity p K) (hv1 : v ≠ 1) (hv : (v 1 : Kˣ) = (v 0 : Kˣ) ^ 2) :
    RootLayer (F4.reeGamma K a) p (tp4M hP v)
      (2 ^ (2 * a + 1) * ((2 ^ (2 * a + 1)) ^ 2 - 1)) := by
  classical
  have hK := hP.card
  have hp := hP.prime
  have h5 := hP.five_le
  have hvz : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  have hz1 : v 0 ≠ 1 := fun h => hv1 (by
    have h1 : v 1 = 1 := Subtype.ext (by rw [hv, h]; simp)
    rw [hvz, h, h1]
    funext i
    fin_cases i <;> rfl)
  have hzp : ((v 0 : rootsOfUnity p K) : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).1 (v 0).2
  have hz1' : ((v 0 : rootsOfUnity p K) : Kˣ) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have : Fact p.Prime := ⟨hp⟩
  have hzprim : IsPrimitiveRoot ((v 0 : rootsOfUnity p K) : Kˣ) p := by
    have := IsPrimitiveRoot.orderOf ((v 0 : rootsOfUnity p K) : Kˣ)
    rwa [orderOf_eq_prime hzp hz1'] at this
  have hpf : p ≤ 2 ^ (2 * a + 1) - 1 := Nat.le_of_dvd (by
    have := Nat.one_lt_two_pow (n := 2 * a + 1) (by omega)
    omega) hP.dvd
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    omega
  have hSL := f4_SL2Torus hP hzprim
  have hD := f4_layerD hP (z := v 0) (z2 := v 1) hzprim hv
  rw [hvz]
  have hchar : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact RootLayer.of_SL2Torus hSL hp h4 (by rw [hK]; exact hP.dvd) hD (by rw [hK])

theorem rootLayer_row4_s2
    {p a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hP : F4Param p a K)
    (v : Fin 2 → rootsOfUnity p K) (hv1 : v ≠ 1)
    (hv : (v 1 : Kˣ) = (v 0 : Kˣ) ^ (1 + 2 ^ a)) :
    RootLayer (F4.reeGamma K a) p (tp4M hP v)
      ((2 ^ (2 * a + 1)) ^ 2 * (((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1))) := by
  classical
  have hK := hP.card
  have hp := hP.prime
  have hvz : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  have hz1 : v 0 ≠ 1 := fun h => hv1 (by
    have h1 : v 1 = 1 := Subtype.ext (by rw [hv, h]; simp)
    rw [hvz, h, h1]
    funext i
    fin_cases i <;> rfl)
  have hzp : ((v 0 : rootsOfUnity p K) : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).1 (v 0).2
  have hz1' : ((v 0 : rootsOfUnity p K) : Kˣ) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have : Fact p.Prime := ⟨hp⟩
  have hzprim : IsPrimitiveRoot ((v 0 : rootsOfUnity p K) : Kˣ) p := by
    have := IsPrimitiveRoot.orderOf ((v 0 : rootsOfUnity p K) : Kˣ)
    rwa [orderOf_eq_prime hzp hz1'] at this
  have hfacts := reeLocalBlock_subgroupOf_facts (K := K) (a := a) hP.one_le hK
  have hD := f4_layerD_sz hP (z := v 0) (z2 := v 1) hzprim hv
  rw [hvz]
  refine RootLayer.of_layerD hp hD hfacts.1 ?_ ?_
  · rw [hfacts.2.2, mul_assoc, mul_comm (2 ^ (2 * a + 1) - 1)]
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hP.dvd _) _

end CFSG.RankThree.PartOne.KLAY
