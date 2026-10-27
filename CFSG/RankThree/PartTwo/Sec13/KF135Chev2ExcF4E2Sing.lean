module

public import CFSG.LieType.Ree.FixedSubgroupData
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Main

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.LieType.Ree CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

section Plane

private theorem exists_singular_of_plane {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] {a p : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hp : p.Prime) (hp3 : 3 < p)
    (hsh : ∃ e, CFSG.RankThree.PartOne.K1214.SylowShape p 2 e (ReeTag.F4.reeGamma K a))
    (P : ReePlane K a p) {A : Subgroup (ReeTag.F4.reeGamma K a)}
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    ∃ x ∈ A, x ≠ 1 ∧ ∃ w : ReeTag.F4.reeGamma K a, w ≠ 1 ∧ w ^ 2 = 1 ∧ x * w = w * x := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Finite (CFSG.Blueprint.Chevalley.ModGL ReeTag.F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨γ, hγ⟩ := exists_conj_plane hp hp2 hsh P A hA.2 hAc
  have hβ : (Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈
      CFSG.Blueprint.Chevalley.rootFinset ReeTag.F4.tag :=
    CFSG.Blueprint.Chevalley.mem_rootFinset.2 (CFSG.Blueprint.Chevalley.isRoot_single _ 0)
  obtain ⟨z, hz, hzβ⟩ := exists_planeElt_kernel hp hp2 P hβ
  obtain ⟨A', Sg, -, -, -, hsup, -, hty⟩ :=
    plane_layer hK hp hp3 P hz (Set.nonempty_iff_ne_empty.1 ⟨_, hzβ⟩)
  have h2 : 2 ∣ Nat.card Sg := by
    have hQ : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
    rcases hty with he | he
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, suzuki_order hK]
      exact ((dvd_pow hQ two_ne_zero).mul_right _).mul_right _
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
      exact hQ.mul_right _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hs1 : (s : ReeTag.F4.reeGamma K a) ≠ 1 := by
    intro h
    rw [show s = 1 from Subtype.ext h, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hs2 : (s : ReeTag.F4.reeGamma K a) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hs, pow_orderOf_eq_one, Subgroup.coe_one]
  have hsC : P.Ψ z * s = s * P.Ψ z := by
    have h : (s : ReeTag.F4.reeGamma K a) ∈
        Subgroup.centralizer ({P.Ψ z} : Set (ReeTag.F4.reeGamma K a)) := by
      rw [← hsup]
      exact (le_sup_right : Sg ≤ A' ⊔ Sg) s.2
    exact (Subgroup.mem_centralizer_singleton_iff.1 h).symm
  refine ⟨γ * P.Ψ z * γ⁻¹, ?_, ?_, γ * s * γ⁻¹, ?_, ?_, ?_⟩
  · rw [hγ, CFSG.RankThree.PartOne.SEITZ3.mem_cj]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    exact ⟨z, rfl⟩
  · intro h
    apply hz
    apply P.Ψinj
    rw [map_one, show P.Ψ z = γ⁻¹ * (γ * P.Ψ z * γ⁻¹) * γ by group, h]
    group
  · intro h
    apply hs1
    rw [show (s : ReeTag.F4.reeGamma K a) = γ⁻¹ * (γ * s * γ⁻¹) * γ by group, h]
    group
  · calc (γ * s * γ⁻¹) ^ 2 = γ * (s : ReeTag.F4.reeGamma K a) ^ 2 * γ⁻¹ := by
          rw [sq, sq]; group
      _ = 1 := by rw [hs2]; group
  · calc γ * P.Ψ z * γ⁻¹ * (γ * s * γ⁻¹) = γ * (P.Ψ z * s) * γ⁻¹ := by group
      _ = γ * (s * P.Ψ z) * γ⁻¹ := by rw [hsC]
      _ = γ * s * γ⁻¹ * (γ * P.Ψ z * γ⁻¹) := by group

end Plane

section Main


theorem exists_singular_reeF4_E2 {k : Type} [Field k] [Finite k]
    [CharP k CFSG.LieType.Ree.ReeTag.F4.prime] {b : ℕ} (hk : Nat.card k = 2 ^ (2 * b + 1))
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hd : p ∣ (2 ^ (2 * b + 1)) ^ 4 - 1) (hd1 : ¬ p ∣ 2 ^ (2 * b + 1) - 1)
    {A : Subgroup ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma k b)}
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    ∃ x ∈ A, x ≠ 1 ∧ ∃ w : ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma k b),
      w ≠ 1 ∧ w ^ 2 = 1 ∧ x * w = w * x := by
  have hp3 : 3 < p := by omega
  have hp5 : 5 ≤ p := by omega
  have hle : 2 ^ (b + 1) ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases dvd_cases_of_dvd_pow_four_sub_one hp hd with h | h | h
  · exact absurd h hd1
  · have hmM : (p : ℤ) ∣ 2 ^ (2 * b + 1) + 1 := by
      have := Int.natCast_dvd_natCast.2 h
      exact_mod_cast this
    obtain ⟨P⟩ := exists_plane_phi2 hk hp hp3 hmM
    exact exists_singular_of_plane hk hp hp3
      ⟨_, CFSG.RankThree.PartOne.K128.sylowShape_ree_phi2 hk hp hp5 h⟩ P hA hAc
  · have hsh := CFSG.RankThree.PartOne.K128.sylowShape_ree_phi4 hk hp hp5 h
    rcases CFSG.RankThree.PartOne.KLR.dvd_phi4_cases hp hp3 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · have hmM : (p : ℤ) ∣ 2 ^ (2 * b + 1) + 2 ^ (b + 1) + 1 := by
        have := Int.natCast_dvd_natCast.2 h1
        exact_mod_cast this
      obtain ⟨P⟩ := exists_plane_phi4p hk hp hp3 hmM
      exact exists_singular_of_plane hk hp hp3 ⟨_, hsh⟩ P hA hAc
    · have hmM : (p : ℤ) ∣ 2 ^ (2 * b + 1) - 2 ^ (b + 1) + 1 := by
        have := CFSG.RankThree.PartOne.K128.int_dvd_sub_add_one' hle h1
        exact_mod_cast this
      obtain ⟨P⟩ := exists_plane_phi4m hk hp hp3 hmM
      exact exists_singular_of_plane hk hp hp3 ⟨_, hsh⟩ P hA hAc

end Main

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
