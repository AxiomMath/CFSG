module

public import CFSG.Quasithin.EmptyFaithful.T1521SBlkAutLift
public import CFSG.Quasithin.EmptyFaithful.T1521SSzAbs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamL2

public section

namespace CFSG.Quasithin.E9.Blk

open CFSG.Open CFSG.QuasithinUnique CFSG.PSL2Table CFSG.Quasithin CFSG.Quasithin.L21521
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem exists_torus [Finite G] {L P : Subgroup G} {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F]
    [Finite F] (hK : Nat.card F = 2 ^ n) (α : ↥L →* SL(2, F)) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) (hP : IsSylowTwoOf P L) :
    ∃ z : ↥L, (z : G) ∈ Subgroup.normalizer (P : Set G) ∧ Odd (orderOf z) ∧
      (∀ β : MulAut PSL(2, F), (∀ x ∈ P.subgroupOf L, β (mk (α x)) = mk (α x)) →
        β (mk (α (z ^ 3))) = mk (α (z ^ 3)) → β = 1) ∧
      (∀ x ∈ P.subgroupOf L, x * z ^ 3 = z ^ 3 * x → α x = 1) ∧
      ∃ (A : SL(2, F)) (a : Fˣ), (a : F) ≠ 1 ∧ α (z ^ 3) = A * diag a * A⁻¹ := by
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have hmkinj : Function.Injective (mk : SL(2, F) →* PSL(2, F)) := mk_injective_of_charTwo1521
  let π : ↥L →* PSL(2, F) := (mk : SL(2, F) →* PSL(2, F)).comp α
  have hπ : Function.Surjective π := mk_surjective.comp hαs
  have hπα : ∀ x : ↥L, π x = mk (α x) := fun x => rfl
  have hkerπ : π.ker = CFSG.pCore 2 ↥L := by
    rw [← hαk]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπα, ← map_one (mk : SL(2, F) →* PSL(2, F))]
    exact hmkinj.eq_iff
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 PSL(2, F) := (A4.toSylow hP).mapSurjective (f := π) hπ
  have hQ : (Q : Subgroup PSL(2, F)) = (P.subgroupOf L).map π := rfl
  obtain ⟨g, hg⟩ := exists_conj_unipotent_of_sylow (by omega) hK Q
  obtain ⟨c, hc⟩ := L2.exists_unit_cube_sq_ne_one hn hK
  have hodd : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units, hK]
    exact odd_two_pow_sub_one' (by omega)
  have hMN : g * mk (diag c) * g⁻¹ ∈ Subgroup.normalizer
      (((P.subgroupOf L).map π : Subgroup PSL(2, F)) : Set PSL(2, F)) := by
    rw [← hQ]
    exact conj_mem_normalizer_of_conj hg (mk_diag_mem_normalizer c)
  rw [← map_normalizer_eq_normalizer_map1521 hP hπ hkerπ] at hMN
  obtain ⟨b, hb, hbM⟩ := hMN
  have hZ : IsPGroup 2 π.ker := hkerπ ▸ CFSG.pCore_isPGroup
  have hord : Odd (orderOf (b : ↥L ⧸ π.ker)) := by
    have h1 := orderOf_injective (QuotientGroup.kerLift π) (QuotientGroup.kerLift_injective π)
      (QuotientGroup.mk b)
    have h2 : QuotientGroup.kerLift π (QuotientGroup.mk b) = g * mk (diag c) * g⁻¹ := hbM
    rw [h2, ← MulAut.conj_apply, MulEquiv.orderOf_eq] at h1
    rw [← h1]
    exact odd_orderOf_mk_diag hodd c
  obtain ⟨k, hk, hkπ⟩ := SzQuot1521.exists_odd_pow_lift hZ hord
  have hπz : π (b ^ k) = g * mk (diag c) * g⁻¹ := by
    have := congrArg (QuotientGroup.kerLift π) hkπ
    rw [← hbM]
    exact this
  have hzN : ((b ^ k : ↥L) : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_subgroupOf.mp hb).2 k
  have ht3 : (g * mk (diag c) * g⁻¹) ^ 3 = g * mk (diag (c ^ 3)) * g⁻¹ := by
    rw [conj_pow, diag_pow, map_pow]
  have hπz3 : π ((b ^ k) ^ 3) = g * mk (diag (c ^ 3)) * g⁻¹ := by
    rw [map_pow, hπz, ht3]
  have hc3 : ((c ^ 3 : Fˣ) : F) ≠ 1 := fun h => hc (by rw [h]; norm_num)
  refine ⟨b ^ k, hzN, hk, ?_, ?_, ?_⟩
  · intro β hβP hβz
    refine L2.eq_one_of_fixes_conj hc g β ?_ ?_
    · intro u hu
      have hmem : g * u * g⁻¹ ∈ (Q : Subgroup PSL(2, F)) := by
        rw [hg]
        simpa [mul_assoc] using hu
      rw [hQ] at hmem
      obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp hmem
      rw [← hyu]
      exact hβP y hy
    · rw [← hπz3]
      exact hβz
  · intro x hx hxz
    have hmem : π x ∈ (Q : Subgroup PSL(2, F)) := by
      rw [hQ]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨s, hs⟩ := (mem_unipotent_iff_exists _).mp ((hg _).mp hmem)
    have hxe : π x = g * mk (unip s) * g⁻¹ := by
      have := congrArg (fun w => g * w * g⁻¹) hs
      simpa [mul_assoc] using this
    have hcomm : π x * (g * mk (diag (c ^ 3)) * g⁻¹) = (g * mk (diag (c ^ 3)) * g⁻¹) * π x := by
      rw [← hπz3, ← map_mul, ← map_mul, hxz]
    rw [hxe] at hcomm
    have hs0 : s = 0 := by
      refine L2.unip_eq_zero_of_commute_diag (a := c ^ 3) hc ?_
      have := congrArg (fun w => g⁻¹ * w * g) hcomm
      simpa [mul_assoc] using this
    have hx1 : π x = 1 := by
      rw [hxe, hs0, unip_zero, map_one]
      group
    exact hmkinj (hx1.trans (map_one _).symm)
  · obtain ⟨A, rfl⟩ := mk_surjective g
    refine ⟨A, c ^ 3, hc3, ?_⟩
    apply hmkinj
    rw [← hπα, hπz3, map_mul, map_mul, map_inv]

end CFSG.Quasithin.E9.Blk
