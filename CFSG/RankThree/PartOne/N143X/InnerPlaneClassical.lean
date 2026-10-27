module

public import CFSG.RankThree.PartOne.S11c.PlaneSp
public import CFSG.RankThree.PartOne.S11c.HigherUnitarySmall

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.CatFactsL4U4 (det_eq_one_of_mem_statedSL)
open scoped MatrixGroups

theorem planeCentralizes_inner_psl {T : Type} [Group T] [Finite T]
    (hZ : Subgroup.center T = ⊥) {n ℓ f : ℕ} (hn : 3 ≤ n) (hn4 : n ≤ 4) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hmod : StatedClassicalModel T .PSL n ℓ f) {p : ℕ}
    {E : Subgroup (MulAut T)} {U : Subgroup T} (hplane : PlaneOn p E U)
    (hE : E ≤ (MulAut.conj : T →* MulAut T).range) (hA : DegreeFourPlane) :
    PlaneCentralizes E U := by
  classical
  have hf : 1 ≤ f := hmod.1.2.1
  have hp := hplane.prime
  have hp3 := hplane.three_lt
  have hp5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    omega
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p E := hplane.elementary
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
  have hdn : Nat.gcd n (ℓ ^ f - 1) ∣ n := Nat.gcd_dvd_left _ _
  have hdpos : 0 < Nat.gcd n (ℓ ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hpd : ¬ p ∣ Nat.gcd n (ℓ ^ f - 1) := fun h => by
    have h1 := Nat.le_of_dvd hdpos h
    have h2 := Nat.le_of_dvd (by omega) hdn
    omega
  have h2 : (2 : K) ≠ 0 := by
    have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
    intro h0
    have h1 := (CharP.cast_eq_zero_iff K ℓ 2).mp (by exact_mod_cast h0)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1)
  refine planeCentralizes_of_matrix_model hZ (StatedSL n K) e hplane hE
    (d := Nat.gcd n (ℓ ^ f - 1)) ?_ hpd ?_
  · intro c hc
    have hdet := det_eq_one_of_mem_statedSL (n := n) hc
    have h1 : c ^ n = 1 := by
      have := congrArg Units.val (Matrix.GeneralLinearGroup.det_scalar (n := Fin n) c)
      rw [Matrix.GeneralLinearGroup.val_det_apply, Fintype.card_fin] at this
      exact Units.ext (by rw [Units.val_one]; exact this.symm.trans hdet)
    have h2 : c ^ (ℓ ^ f - 1) = 1 := by
      have := pow_card_eq_one' (G := Kˣ) (x := c)
      rwa [Nat.card_units, hK] at this
    exact (pow_gcd_eq_one (a := c)).2 ⟨h1, h2⟩
  · intro F V hFM hFel hFcard hV2 hFnorm x hx u hu
    have hdet : ∀ y ∈ F, (y : Matrix (Fin n) (Fin n) K).det = 1 := fun y hy =>
      det_eq_one_of_mem_statedSL (hFM hy)
    have : Finite V := Finite.of_injective (Subgroup.subtype V) (Subgroup.subtype_injective V)
    have hcomm : ⁅F, V⁆ = ⊥ := hA K h2 n hn4 V F hV2 p hp hp3 hdet hFel hFcard hFnorm
    have := Subgroup.commutator_mem_commutator hx hu
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this

theorem planeCentralizes_inner_psu {T : Type} [Group T] [Finite T]
    (hZ : Subgroup.center T = ⊥) {n ℓ f : ℕ} (hn : 3 ≤ n) (hn4 : n ≤ 4) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hmod : StatedClassicalModel T .PSU n ℓ f) {p : ℕ}
    {E : Subgroup (MulAut T)} {U : Subgroup T} (hplane : PlaneOn p E U)
    (hE : E ≤ (MulAut.conj : T →* MulAut T).range) (hA : DegreeFourPlane) :
    PlaneCentralizes E U := by
  classical
  have hf : 1 ≤ f := hmod.1.2.1
  have hp := hplane.prime
  have hp3 := hplane.three_lt
  have hp5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    omega
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p E := hplane.elementary
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hdn : Nat.gcd n (ℓ ^ f + 1) ∣ n := Nat.gcd_dvd_left _ _
  have hdpos : 0 < Nat.gcd n (ℓ ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hpd : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := fun h' => by
    have h1 := Nat.le_of_dvd hdpos h'
    have h2 := Nat.le_of_dvd (by omega) hdn
    omega
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_ne_two h hℓ2
  refine planeCentralizes_of_matrix_model hZ (StatedSU n (ℓ ^ f) K) e hplane hE
    (d := Nat.gcd n (ℓ ^ f + 1)) ?_ hpd ?_
  · intro c hc
    have hc' := (mem_unitarySU_iff h).1 hc
    have hdet := hc'.1
    have h1 : c ^ n = 1 := by
      have := congrArg Units.val (Matrix.GeneralLinearGroup.det_scalar (n := Fin n) c)
      rw [Matrix.GeneralLinearGroup.val_det_apply, Fintype.card_fin] at this
      exact Units.ext (by rw [Units.val_one]; exact this.symm.trans hdet)
    have h0 : h.bar (c : K) * (c : K) = 1 := by
      have := congrFun (congrFun hc'.2 ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.diagonal_apply] using this
    have h3 : c ^ (ℓ ^ f + 1) = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
      rw [UnitaryFieldData.bar_apply] at h0
      exact h0
    exact (pow_gcd_eq_one (a := c)).2 ⟨h1, h3⟩
  · intro F V hFM hFel hFcard hV2 hFnorm x hx u hu
    have hdet : ∀ y ∈ F, (y : Matrix (Fin n) (Fin n) K).det = 1 := fun y hy =>
      CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU (hFM hy)
    have : Finite V := Finite.of_injective (Subgroup.subtype V) (Subgroup.subtype_injective V)
    have hcomm : ⁅F, V⁆ = ⊥ := hA K h2 n hn4 V F hV2 p hp hp3 hdet hFel hFcard hFnorm
    have := Subgroup.commutator_mem_commutator hx hu
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this

theorem planeCentralizes_inner_psp_four {T : Type} [Group T] [Finite T]
    (hZ : Subgroup.center T = ⊥) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hmod : StatedClassicalModel T .PSp 2 ℓ f) {p : ℕ} {E : Subgroup (MulAut T)}
    {U : Subgroup T} (hplane : PlaneOn p E U)
    (hE : E ≤ (MulAut.conj : T →* MulAut T).range) (hA : DegreeFourPlane) :
    PlaneCentralizes E U := by
  classical
  have hf : 1 ≤ f := hmod.1.2.1
  have hp := hplane.prime
  have hp3 := hplane.three_lt
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p E := hplane.elementary
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have h2 : (2 : K) ≠ 0 := by
    have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
    intro h0
    have h1 := (CharP.cast_eq_zero_iff K ℓ 2).mp (by exact_mod_cast h0)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1)
  have hpd : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  refine planeCentralizes_of_matrix_model hZ (StatedSp 2 K) e hplane hE (d := 2) ?_ hpd ?_
  · intro c hc
    have hJ := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 hc
    have h := congrFun (congrFun hJ (Sum.inl 0)) (Sum.inr 0)
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.fromBlocks, Fintype.sum_sum_type] using h
  · intro F V hFM hFel hFcard hV2 hFnorm x hx u hu
    let e4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv.trans (finCongr (by norm_num))
    let τ : GL (Fin 2 ⊕ Fin 2) K ≃* GL (Fin 4) K :=
      CFSG.ComponentClassification.ClassicalModelStatedBridge.glReindex K e4
    have hdet : ∀ y ∈ F.map τ.toMonoidHom,
        (y : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      have hyp : y ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian y hy
      have := det_eq_one_of_odd_order h2 (hFM hy) (hp.odd_of_ne_two (by omega)) hyp
      rw [MulEquiv.coe_toMonoidHom,
        CFSG.ComponentClassification.ClassicalModelStatedBridge.coe_glReindex,
        Matrix.det_reindex_self]
      exact this
    have hel : IsElementaryAbelian p (F.map τ.toMonoidHom) :=
      IsElementaryAbelian.map (A := F) τ.toMonoidHom
    have hcard : Nat.card (F.map τ.toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (show Function.Injective τ.toMonoidHom from τ.injective)]
      exact hFcard
    have hV'2 : IsPGroup 2 (V.map τ.toMonoidHom) := hV2.map _
    have : Finite (V.map τ.toMonoidHom) := Finite.of_surjective
      (fun v : V => (⟨τ v, v, v.2, rfl⟩ : V.map τ.toMonoidHom)) (by
        rintro ⟨_, v, hv, rfl⟩
        exact ⟨⟨v, hv⟩, rfl⟩)
    have hnorm : F.map τ.toMonoidHom ≤ Subgroup.normalizer
        ((V.map τ.toMonoidHom : Subgroup (GL (Fin 4) K)) : Set (GL (Fin 4) K)) :=
      (Subgroup.map_mono hFnorm).trans (Subgroup.le_normalizer_map _)
    have hcomm := hA K h2 4 le_rfl (V.map τ.toMonoidHom) (F.map τ.toMonoidHom) hV'2 p hp hp3
      hdet hel hcard hnorm
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem τ.toMonoidHom hx)
      (Subgroup.mem_map_of_mem τ.toMonoidHom hu)
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact τ.injective (by rw [map_mul, map_mul]; exact this)

end CFSG.RankThree.PartOne.N143X
