module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsFrame
public import CFSG.Sporadic.Suz.Setup

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace WitSpNs

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical (spEnd spLin spLin_injective spLin_mem spForm_isAlt
  spForm_nondegenerate range_spLin)
open scoped MatrixGroups

theorem exists_symplecticPlaneFrame {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ}
    (hn : 1 ≤ n) (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) (P : StatedSp n K → Prop)
    (hPc : ∀ X X', P X → P X' → Commute X X') (hPp : ∀ X, P X → X ^ p = 1)
    (hmax : ∀ Y : StatedSp n K, (∀ X, P X → Commute Y X) → Y ^ p = 1 → P Y) :
    ∃ (A₀ : StatedSp n K) (T : SL(2, K)),
      (T : Matrix (Fin 2) (Fin 2) K) ^ p = 1 ∧
      (∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit ((T : Matrix (Fin 2) (Fin 2) K) ^ j - c • 1)) ∧
      (∀ k : Fin n → ℕ, ∃ Dk : StatedSp n K,
        mat n K Dk = planeMat (fun j => (T : Matrix (Fin 2) (Fin 2) K) ^ k j) ∧
          P (A₀ * Dk * A₀⁻¹)) ∧
      ∀ X, P X → ∃ (k : Fin n → ℕ) (Dk : StatedSp n K),
        mat n K Dk = planeMat (fun j => (T : Matrix (Fin 2) (Fin 2) K) ^ k j) ∧
          X = A₀ * Dk * A₀⁻¹ := by
  classical
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpq
  have hK : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpq
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpK : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have hne : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have hζo := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  have hζp : AdjoinRoot.root g ^ p = 1 := hζo.pow_eq_one
  have hζ1 : AdjoinRoot.root g ≠ 1 := hζo.ne_one hp.one_lt
  have hdeg := SpNS.rootPB_dim_eq_two hp hp2 hpK hgd hpq
  have hnorm : Algebra.norm K (AdjoinRoot.root g) = 1 := SpNS.norm_root_eq_one hp hp2 hpK hgd hpq
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Module.Basis (Fin 2) K (AdjoinRoot g),
      b₀ = (CoordSL.rootPB g).basis.reindex (finCongr hdeg) := ⟨_, rfl⟩
  set S : Set (Module.End K (Fin n ⊕ Fin n → K)) := {y | ∃ X, P X ∧ spEnd X = y} with hS
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨X', hX', rfl⟩
    show spEnd X * spEnd X' = spEnd X' * spEnd X
    rw [← spEnd_mul, ← spEnd_mul, (hPc X X' hX hX').eq]
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨X, hX, rfl⟩
    rw [← spEnd_pow, hPp X hX]
    show Units.val (spLin n K 1) = 1
    rw [map_one, Units.val_one]
  have hSB : ∀ x ∈ S, ∀ u w, CFSG.RankThree.Classical.spForm n K (x u) (x w) =
      CFSG.RankThree.Classical.spForm n K u w := by
    rintro _ ⟨X, -, rfl⟩ u w
    exact mem_sesqUnitaryGroup.mp (spLin_mem X) u w
  obtain ⟨s, κ, _, Φ, β, hβalt, hact, hdec⟩ := SpNS.exists_nframe hp hp2 hpK hgd hdeg
    (SpNS.aeval_root_pow_pred hp hpK hgd hpq) spForm_isAlt spForm_nondegenerate S hSc hSp hSB
  have hactP : ∀ X, P X → ∃ k : Fin s → ℕ, ∀ d w,
      mat n K X *ᵥ Φ (d, w) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w) :=
    fun X hX => hact _ ⟨X, hX, rfl⟩
  have hdet₀ : (rootMat b₀ (AdjoinRoot.root g)).det = 1 := by rw [det_rootMat, hnorm]
  have hT₀p : mkSL (rootMat b₀ (AdjoinRoot.root g)) hdet₀ ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_mkSL, rootMat_pow, hζp, rootMat_one,
      Matrix.SpecialLinearGroup.coe_one]
  have hT₀fix : ¬ ((mkSL (rootMat b₀ (AdjoinRoot.root g)) hdet₀ : Matrix (Fin 2) (Fin 2) K) 0 0 = 1
      ∧ (mkSL (rootMat b₀ (AdjoinRoot.root g)) hdet₀ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) := by
    rintro ⟨h0, h1⟩
    rw [coe_mkSL] at h0 h1
    have h := mul_basis b₀ (AdjoinRoot.root g) 0
    rw [h0, h1, one_smul, zero_smul, add_zero] at h
    apply hζ1
    have h2 : (AdjoinRoot.root g - 1) * b₀ 0 = 0 := by rw [sub_mul, h, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right (b₀.ne_zero 0))
  have hκ : IsEmpty κ := by
    refine isEmpty_of_frame hn Φ (fun w d' w' => ?_) P (fun X hX w => ?_) hmax _ hT₀p hT₀fix
    · rw [← spForm_eq_form, ← spForm_eq_form]
      exact frame_form_zero_left hdec w d' w'
    · obtain ⟨k, hk⟩ := hactP X hX
      rw [hk 0 w]
      congr 2
      funext i
      simp
  have hdimL : Module.finrank K (AdjoinRoot g) = 2 := by
    rw [(CoordSL.rootPB g).finrank, hdeg]
  have hsn : s = n := by
    have h1 := LinearEquiv.finrank_eq Φ
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self, hdimL,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_sum, smul_eq_mul, mul_one,
      Fintype.card_eq_zero_iff.mpr hκ] at h1
    omega
  subst hsn
  have hβnd : ∀ u, (∀ v, β u v = 0) → u = 0 := fun u hu =>
    frame_block_nondegenerate spForm_nondegenerate hdec ⟨0, by omega⟩ u hu
  have hβ0 := SpNS.alt_two_ne_zero b₀ hβalt hβnd
  obtain ⟨bu, hbu⟩ : ∃ bu : Module.Basis (Fin 2) K (AdjoinRoot g),
      bu = b₀.unitsSMul ![1, (Units.mk0 _ hβ0)⁻¹] := ⟨_, rfl⟩
  have hbu0 : bu 0 = b₀ 0 := by
    rw [hbu, Module.Basis.unitsSMul_apply]
    simp
  have hbu1 : bu 1 = (β (b₀ 0) (b₀ 1))⁻¹ • b₀ 1 := by
    rw [hbu, Module.Basis.unitsSMul_apply]
    simp [Units.smul_def]
  have hβbu : β (bu 0) (bu 1) = 1 := by
    rw [hbu0, hbu1, LinearMap.map_smul, smul_eq_mul, inv_mul_cancel₀ hβ0]
  have hdet : (rootMat bu (AdjoinRoot.root g)).det = 1 := by rw [det_rootMat, hnorm]
  have hframe : IsPlaneFrame (fun k => Φ (Pi.single k (bu 0), 0))
      (fun k => Φ (Pi.single k (bu 1), 0)) := by
    refine ⟨fun k l => ?_, fun k l => ?_, fun k l => ?_⟩
    · rw [← spForm_eq_form, frame_form_single hdec, hβbu]
    · rw [← spForm_eq_form, frame_form_single hdec, hβalt.self_eq_zero, ite_self]
    · rw [← spForm_eq_form, frame_form_single hdec, hβalt.self_eq_zero, ite_self]
  obtain ⟨A₀, hA₀⟩ := hframe.exists_sp_apply
  have hζβ : ∀ u v, β (AdjoinRoot.root g * u) (AdjoinRoot.root g * v) = β u v := fun u v => by
    have h1 := SpNS.bilin_apply_det b₀ hβalt
      (Algebra.lmul K (AdjoinRoot g) (AdjoinRoot.root g)) u v
    rw [← Algebra.norm_apply, hnorm, one_mul] at h1
    exact h1
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : StatedSp s K ≃*
      ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm s K)),
      e₂ = (MonoidHom.ofInjective spLin_injective).trans
        (MulEquiv.subgroupCongr range_spLin) := ⟨_, rfl⟩
  have he₂coe : ∀ X, ((e₂ X : ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm s K))) :
      LinearMap.GeneralLinearGroup K (Fin s ⊕ Fin s → K)) = spLin s K X := by
    intro X
    rw [he₂]
    rfl
  obtain ⟨Xk, hXkdef⟩ : ∃ Xk : (Fin s → ℕ) → StatedSp s K, ∀ k, Xk k =
      e₂.symm (SpNS.torHom (K := K) hζp hdec hζβ
        (fun j => Multiplicative.ofAdd ((k j : ℕ) : ZMod p))) := ⟨_, fun _ => rfl⟩
  have hXk : ∀ k d w, mat s K (Xk k) *ᵥ Φ (d, w) =
      Φ (fun i => AdjoinRoot.root g ^ k i * d i, w) := by
    intro k d w
    have h1 : spLin s K (Xk k) = ((SpNS.torHom (K := K) hζp hdec hζβ
        (fun j => Multiplicative.ofAdd ((k j : ℕ) : ZMod p)) :
          ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm s K))) :
        LinearMap.GeneralLinearGroup K (Fin s ⊕ Fin s → K)) := by
      rw [← he₂coe, hXkdef, MulEquiv.apply_symm_apply]
    rw [← spEnd_eq_mulVec]
    show Units.val (spLin s K (Xk k)) (Φ (d, w)) = _
    rw [h1, SpNS.coe_torHom, SpNS.frameUnit_apply, SpNS.torEquiv_apply]
    congr 2
    funext i
    rw [toAdd_ofAdd, ZMod.val_natCast, ← pow_eq_pow_mod _ hζp]
  have hXkmul : ∀ k k', Commute (Xk k) (Xk k') := by
    intro k k'
    show Xk k * Xk k' = Xk k' * Xk k
    rw [hXkdef, hXkdef, ← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm]
  have hXkp : ∀ k, Xk k ^ p = 1 := by
    intro k
    rw [hXkdef, ← map_pow, ← map_pow]
    have h1 : (fun j => Multiplicative.ofAdd ((k j : ℕ) : ZMod p)) ^ p = 1 := by
      funext j
      rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        ofAdd_zero]
    rw [h1, map_one, map_one]
  have hall : ∀ X, P X → ∃ k, X = Xk k := by
    intro X hX
    obtain ⟨k, hk⟩ := hactP X hX
    refine ⟨k, spEnd_injective (LinearMap.ext fun v => ?_)⟩
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [spEnd_eq_mulVec, spEnd_eq_mulVec, hk, hXk]
  have hXkP : ∀ k, P (Xk k) := by
    intro k
    refine hmax _ (fun X hX => ?_) (hXkp k)
    obtain ⟨k', rfl⟩ := hall X hX
    exact hXkmul k k'
  have hmat : ∀ k, mat s K (A₀⁻¹ * Xk k * A₀) =
      planeMat (fun j => (rootMat bu (AdjoinRoot.root g)) ^ k j) := by
    intro k
    refine eq_planeMat_of_mulVec (fun j => ?_) (fun j => ?_)
    · rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hA₀ j).1, hXk,
        mul_single_eq, mul_basis bu, ← rootMat_pow, frame_single_comb, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, ← (hA₀ j).1, ← (hA₀ j).2, mulVec_inv_mulVec,
        mulVec_inv_mulVec]
    · rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hA₀ j).2, hXk,
        mul_single_eq, mul_basis bu, ← rootMat_pow, frame_single_comb, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, ← (hA₀ j).1, ← (hA₀ j).2, mulVec_inv_mulVec,
        mulVec_inv_mulVec]
  refine ⟨A₀, mkSL (rootMat bu (AdjoinRoot.root g)) hdet, ?_, fun j hj c => ?_,
    fun k => ⟨A₀⁻¹ * Xk k * A₀, hmat k, ?_⟩, fun X hX => ?_⟩
  · rw [coe_mkSL, rootMat_pow, hζp, rootMat_one]
  · exact isUnit_rootMat_pow_sub hp hK bu hζp hζ1 j hj c
  · rw [show A₀ * (A₀⁻¹ * Xk k * A₀) * A₀⁻¹ = Xk k by group]
    exact hXkP k
  · obtain ⟨k, rfl⟩ := hall X hX
    exact ⟨k, A₀⁻¹ * Xk k * A₀, hmat k, by group⟩

end WitSpNs

end CFSG.StandardType
