module

public import CFSG.RankThree.PartOne.S11c.PlaneHigherLinear
public import CFSG.RankThree.GroupTheory.SteinbergCEOddSymplecticRankFour
public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer inner_normal)
open scoped MatrixGroups

theorem det_eq_one_of_odd_order {r : ℕ} {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {g : GL (Fin r ⊕ Fin r) K} (hg : g ∈ StatedSp r K) {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) :
    (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det = 1 := by
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det ≠ 0 := by
    intro h0
    have h1 : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        (Matrix.fromBlocks 0 (-1) 1 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
      rw [Matrix.fromBlocks_multiply]
      simp [Matrix.fromBlocks_one]
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hsq : (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det ^ 2 = 1 := by
    have := congrArg Matrix.det
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 hg)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
    apply mul_right_cancel₀ hJ
    linear_combination this
  have hpow : ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det) ^ m = 1 := by
    have := congrArg
      (fun x : GL (Fin r ⊕ Fin r) K => (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det) hgm
    simpa [Units.val_pow_eq_pow_val, Matrix.det_pow] using this
  have hsq2 : (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det *
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det = 1 := by rw [← sq]; exact hsq
  rcases mul_self_eq_one_iff.1 hsq2 with h | h
  · exact h
  · exfalso
    rw [h, Odd.neg_one_pow hm] at hpow
    apply h2
    linear_combination -hpow

section Prime

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.Classical.SteinbergBY

theorem sp_prime_order_inner {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf3 : f ≤ 3)
    (β : MulAut (StatedProj (StatedSp 2 K))) (hβ : orderOf β = p) :
    β ∈ inner (StatedProj (StatedSp 2 K)) := by
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hprime⟩ :=
    symplectic_prime_semilinear_field_descent hℓ hf le_rfl hK
  obtain ⟨j, hj⟩ := hp.odd_of_ne_two (by omega)
  have hβp : β ^ p = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  have hsq : ∀ (G : Type) [Group G] (H : Subgroup G) [H.Normal] (g : G), H.index ∣ 2 →
      g ^ p = 1 → g ^ 2 ∈ H → g ∈ H := fun G _ H _ g _ hgp h2 => by
    have : g = (g ^ 2) ^ (j + 1) := by
      calc g = g ^ p * g := by rw [hgp, one_mul]
        _ = g ^ (2 * j + 1 + 1) := by rw [← pow_succ, hj]
        _ = (g ^ 2) ^ (j + 1) := by rw [← pow_mul]; congr 1
    rw [this]
    exact H.pow_mem h2 _
  have hpow : ∀ (G : Type) [Group G] (H : Subgroup G) [H.Normal] (g : G), H.index ∣ 2 →
      g ^ 2 ∈ H := fun G _ H _ g hH => by
    have h1 : g ^ H.index ∈ H := Subgroup.pow_index_mem H g
    rcases (Nat.dvd_prime Nat.prime_two).1 hH with h | h
    · rw [h, pow_one] at h1
      exact H.pow_mem h1 2
    · rwa [h] at h1
  have hE : β ∈ spSemilinearAutGroup 2 K := by
    set E := spSemilinearAutGroup 2 K
    have hEn : E.Normal := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
      · rw [Subgroup.index_eq_one.1 h]
        infer_instance
      · exact Subgroup.normal_of_index_eq_two h
    exact hsq _ E β hidx hβp (hpow _ E β hidx)
  have hD : β ∈ spLinearAutGroup 2 K := by
    by_contra hD
    obtain ⟨hpf, -⟩ := hprime p hp β hE hD hβ
    have := Nat.le_of_dvd (by omega) hpf
    omega
  have hrel2 : ((inner (StatedProj (StatedSp 2 K))).subgroupOf (spLinearAutGroup 2 K)).index ∣ 2 :=
    hrel.trans (Nat.gcd_dvd_left _ _)
  have hN : ((inner (StatedProj (StatedSp 2 K))).subgroupOf (spLinearAutGroup 2 K)).Normal :=
    Subgroup.Normal.subgroupOf (inner_normal _) _
  have hgp : (⟨β, hD⟩ : spLinearAutGroup 2 K) ^ p = 1 := Subtype.ext hβp
  exact hsq (spLinearAutGroup 2 K)
    ((inner (StatedProj (StatedSp 2 K))).subgroupOf (spLinearAutGroup 2 K)) ⟨β, hD⟩ hrel2 hgp
    (hpow _ _ _ hrel2)

end Prime

theorem planeCentralizes_psp {H : Type} [Group H] [Finite H] {X : Subgroup H}
    (hXqs : CFSG.IsQuasisimple X) {n ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSp n ℓ f)
    (hrank : localRank ℓ H ≤ 3) {p : ℕ} {E : Subgroup (MulAut (↥X ⧸ Subgroup.center ↥X))}
    {U : Subgroup (↥X ⧸ Subgroup.center ↥X)} (hplane : PlaneOn p E U)
    (hA : DegreeFourPlane) : PlaneCentralizes E U := by
  classical
  obtain ⟨hn2, hf3⟩ :=
    (CFSG.RankThree.GroupTheory.odd_symplectic_actual_cover_rank_four_and_small_parameters.{0}
      (p := ℓ) (f := f) hℓ hℓ2).2 H X n (Or.inr (Or.inr hrank)) hmod
  subst hn2
  have hf : 1 ≤ f := hmod.1.2.1
  have hp := hplane.prime
  have hp3 := hplane.three_lt
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p E := hplane.elementary
  have hZ := center_eq_bot_of_isQuasisimple hXqs
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hEinner : E ≤ inner (↥X ⧸ Subgroup.center ↥X) := by
    intro β hβ
    have hβp : β ^ p = 1 := by
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E) ⟨β, hβ⟩
      simpa using congrArg Subtype.val this
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hβp) with h1 | h1
    · rw [orderOf_eq_one_iff.1 h1]
      exact ⟨1, map_one _⟩
    ·
      have hβ' : orderOf (MulAut.congr e β) = p := by rw [MulEquiv.orderOf_eq, h1]
      have := sp_prime_order_inner hℓ hf hK hp hp3 hf3 _ hβ'
      have hmap := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
      have hmem : MulAut.congr e β ∈ (inner (↥X ⧸ Subgroup.center ↥X)).map
          (MulAut.congr e).toMonoidHom := by rw [hmap]; exact this
      obtain ⟨γ, hγ, hγβ⟩ := hmem
      have : γ = β := (MulAut.congr e).injective hγβ
      exact this ▸ hγ
  have h2 : (2 : K) ≠ 0 := by
    have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
    intro h0
    have h1 := (CharP.cast_eq_zero_iff K ℓ 2).mp (by exact_mod_cast h0)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1)
  have hpd : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  refine planeCentralizes_of_matrix_model hZ (StatedSp 2 K) e hplane hEinner (d := 2) ?_ hpd ?_
  ·
    intro c hc
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

end CFSG.RankThree.PartOne
