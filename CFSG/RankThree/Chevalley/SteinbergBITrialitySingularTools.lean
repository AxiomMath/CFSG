module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools
public import CFSG.RankThree.Chevalley.SteinbergBID4RootSL2Trace

public noncomputable section

namespace CFSG.RankThree.Chevalley

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open scoped MatrixGroups

theorem mem_center_iff_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (y : G) :
    y ∈ Subgroup.center G ↔ e y ∈ Subgroup.center H := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul, h w]
  · intro h w
    apply e.injective
    rw [map_mul, map_mul, h (e w)]

theorem mem_center_SL_iff {k : Type*} [Field k] (A : SL(3, k)) :
    A ∈ Subgroup.center (SL(3, k)) ↔
      ∃ c : k, (A : Matrix (Fin 3) (Fin 3) k) = scalar (Fin 3) c := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, -, hr⟩
    exact ⟨r, hr.symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, hc.symm⟩
    have h : (A : Matrix (Fin 3) (Fin 3) k).det = 1 := A.2
    rw [hc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ] at h
    exact h

theorem odd_relIndex_of_pow_mem {G : Type*} [Group G] [Finite G] {R D : Subgroup G}
    (hN : (R.subgroupOf D).Normal) {d : ℕ} (hd : Odd d) (hpow : ∀ y ∈ D, y ^ d ∈ R) :
    Odd (R.relIndex D) := by
  rw [Subgroup.relIndex, Subgroup.index, Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ Nat.card (D ⧸ R.subgroupOf D) := Nat.dvd_of_mod_eq_zero (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  have hzd : (QuotientGroup.mk y : D ⧸ R.subgroupOf D) ^ d = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hpow y y.2
  have := orderOf_dvd_of_pow_eq_one hzd
  rw [hz] at this
  exact (Nat.not_even_iff_odd.2 hd) (even_iff_two_dvd.2 this)

theorem blockSL_eq_sl2BlockSL3 {Ω : Type} [Field Ω] (A : SL(2, Ω)) :
    (blockSL Ω 2 1 A : SL(3, Ω)) = sl2BlockSL3 Ω A := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [coe_sl2BlockSL3, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_blockSL,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_blockGL]
  fin_cases i <;> fin_cases j <;> rfl

theorem commutator_inf_eq {G : Type*} [Group G] {M Q F : Subgroup G} (hQM : Q ≤ M)
    (hder : ⁅M, M⁆ = Q) (hperf : ⁅Q ⊓ F, Q ⊓ F⁆ = Q ⊓ F) : ⁅M ⊓ F, M ⊓ F⁆ = Q ⊓ F := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · rw [← hder]
    exact Subgroup.commutator_mono inf_le_left inf_le_left
  · exact (Subgroup.commutator_le_self _).trans inf_le_right
  · calc Q ⊓ F = ⁅Q ⊓ F, Q ⊓ F⁆ := hperf.symm
      _ ≤ ⁅M ⊓ F, M ⊓ F⁆ :=
        Subgroup.commutator_mono (inf_le_inf_right F hQM) (inf_le_inf_right F hQM)

end CFSG.RankThree.Chevalley
