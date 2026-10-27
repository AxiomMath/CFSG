module

public import CFSG.RankThree.PartOne.K159.KleinModel
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusGeneric
public import CFSG.RankThree.PartOne.KC.OrthogonalHypCoordinates
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.RankThree.PartOne.K159.Klein

open Matrix CFSG.LocalAnalysis CFSG.LieType.Universal.Spin CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Classification

variable {K : Type} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_isometry_quadPlus_three (Q : QuadraticForm K W)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : Module.finrank K W = 6)
    (hts : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Nonempty (Q.IsometryEquiv (quadPlus 3 K)) := by
  obtain ⟨U, hU, hUs⟩ := hts
  obtain ⟨P, -, hP, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.exists_hypPairs_of_flag_of_le 3 ⊤
      (CFSG.ClassicalGroups.Orthogonal.polarNondegOn_top hQ) U le_top hUs hU.ge 0 (by omega)
      (fun _ => ⊥) bot_le (fun i hi => by
        obtain rfl : i = 0 := by omega
        exact finrank_bot K W) (fun i hi => absurd hi (Nat.not_lt_zero _))
      (fun x hx => by
        rw [Submodule.mem_bot] at hx
        rw [hx]
        exact QuadraticMap.map_zero Q)
  have hperp : CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.pairsPerp P = ⊥ := by
    have h := CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.finrank_pairsPerp hP hQ
    have h0 : Module.finrank K (CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.pairsPerp P) =
        0 := by omega
    exact Submodule.finrank_eq_zero.1 h0
  exact ⟨hypCoordSplitIsometry hP hperp⟩

end Classification

section SL4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem center_sl4_eq_bot : Subgroup.center (SpecialLinearGroup (Fin 4) K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr
  have e : (r + 1) ^ 4 = r ^ 4 + 1 := by
    calc (r + 1) ^ 4 = ((r + 1) ^ 2) ^ 2 := by ring
      _ = (r ^ 2 + 1 ^ 2) ^ 2 := by rw [CharTwo.add_sq]
      _ = (r ^ 2) ^ 2 + (1 ^ 2) ^ 2 := CharTwo.add_sq _ _
      _ = r ^ 4 + 1 := by ring
  have h4 : (r + 1) ^ 4 = 0 := by
    rw [e, hr]
    exact CharTwo.add_self_eq_zero 1
  have h1 : r + 1 = 0 := (pow_eq_zero_iff (by norm_num)).1 h4
  have hr1 : r = 1 := CharTwo.add_eq_zero.1 h1
  apply Subtype.ext
  rw [← hrz, hr1, map_one]
  rfl

omit [Finite K] in
theorem sl4_isSimpleGroup_and_perfect :
    IsSimpleGroup (SpecialLinearGroup (Fin 4) K) ∧ Group.IsPerfect (SpecialLinearGroup (Fin 4) K) := by
  obtain ⟨hperf, hsimple, -⟩ :=
    CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (K := K) (n := 4) (by norm_num)
  refine ⟨?_, hperf⟩
  let e : SpecialLinearGroup (Fin 4) K ≃*
      SpecialLinearGroup (Fin 4) K ⧸ Subgroup.center (SpecialLinearGroup (Fin 4) K) :=
    (QuotientGroup.quotientBot (G := SpecialLinearGroup (Fin 4) K)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq center_sl4_eq_bot.symm)
  exact e.isSimpleGroup

@[expose] noncomputable def g₀ : SpecialLinearGroup (Fin 4) K :=
  ⟨Matrix.transvection 0 2 1, Matrix.det_transvection_of_ne _ _ (by decide) _⟩

omit [Finite K] in
theorem rho_g₀_ne_one : Klein.rho (g₀ (K := K)) ≠ 1 := by
  intro h
  have h1 : Klein.rho (g₀ (K := K)) (Pi.single (Sum.inr 0) 1) = Pi.single (Sum.inr 0) 1 := by
    rw [h]
    rfl
  have h2 : cong (g₀ (K := K) : Matrix (Fin 4) (Fin 4) K) (Pi.single (Sum.inr 0) 1) (Sum.inl 2) =
      (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K) (Sum.inl 2) := congrFun h1 (Sum.inl 2)
  simp [cong_apply, coords, alt, antiMat, g₀, Matrix.transvection, Matrix.mul_apply,
    Fin.sum_univ_four, Matrix.single_apply] at h2

omit [Finite K] in
theorem rho_injective : Function.Injective (Klein.rho : SpecialLinearGroup (Fin 4) K →* _) := by
  obtain ⟨hs, -⟩ := sl4_isSimpleGroup_and_perfect (K := K)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Klein.rho : SpecialLinearGroup (Fin 4) K →* _).ker
    with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exact absurd (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top (g₀ (K := K)))) rho_g₀_ne_one

end SL4

section Orders

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_orthogonalGroup_quadPlus_three :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) =
      2 * Nat.card (SpecialLinearGroup (Fin 4) K) := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have h1 := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K) 2).2
  have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := 4)
    (by norm_num)
  apply Nat.cast_injective (R := ℤ)
  rw [h1, Nat.cast_mul, h2]
  have hsub : ∀ j : ℕ, ((Nat.card K ^ j - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ j - 1 := fun j => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    push_cast
    ring
  have e12 : Finset.Icc 1 2 = {1, 2} := by decide
  have e24 : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [e12, e24]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod, hsub, Nat.cast_ofNat]
  simp [Finset.prod_insert]
  ring

end Orders

theorem klein_commutator_orthogonal_six {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K W = 6)
    (hts : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (_hK : 4 ≤ Nat.card K) :
    Nonempty (commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≃* StatedSL 4 K) := by
  obtain ⟨e⟩ := exists_isometry_quadPlus_three Q hQ hd hts
  obtain ⟨hs, hp⟩ := sl4_isSimpleGroup_and_perfect (K := K)
  have hρinj := transportHom_injective e (Klein.rho : SpecialLinearGroup (Fin 4) K →* _)
    rho_injective
  have hρmem := transportHom_mem e (Klein.rho : SpecialLinearGroup (Fin 4) K →* _) rho_mem
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set ρ := transportHom e (Klein.rho : SpecialLinearGroup (Fin 4) K →* _) with hρ
  have hle : ρ.range ≤ O := by
    rintro _ ⟨g, rfl⟩
    exact hρmem g
  have hcard : Nat.card O = 2 * Nat.card (SpecialLinearGroup (Fin 4) K) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e,
      card_orthogonalGroup_quadPlus_three]
  obtain ⟨-, -, -, -, -, -, hcomm, -⟩ := derived_of_index_two_model O ρ hρinj hle hcard
  have h1 : (commutator ↥O).map O.subtype = ρ.range := by
    rw [Subgroup.map_subtype_commutator, hcomm]
  let e1 : commutator ↥O ≃* ρ.range :=
    (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr h1)
  let e2 : ρ.range ≃* SpecialLinearGroup (Fin 4) K := (MonoidHom.ofInjective hρinj).symm
  exact ⟨e1.trans (e2.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K))⟩

end CFSG.RankThree.PartOne.K159.Klein
