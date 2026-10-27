module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUKFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.RankThree.PartTwo.CTU6.Nodes
public import CFSG.RankThree.PartOne.CTP.SpNode
public import CFSG.RankThree.PartOne.CTP.SpPos

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

open Matrix Multiplicative CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.RankThree.PartTwo.CTU6
open CFSG.ClassicalInvolution.WeakCT (blk torusHom coe_torusHom
  coe_blockSL_three_zero coe_blockSL_three_one)
open scoped MatrixGroups

section NativeBlocks

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ z, σ (σ z) = z)

private theorem su_diagonal_pair (d : Fin 6 → F) :
    diagonal d = pairMat (diagonal ![d 0, d 1, d 2]) (diagonal ![d 3, d 4, d 5]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, pairMat_apply]

private theorem su_lowBlk_apply (M : SL(3, F)) (i j : Fin 3) :
    lowBlk σ M i j = σ ((M⁻¹ : SL(3, F)) (Fin.rev j) (Fin.rev i)) := by
  fin_cases i <;> fin_cases j <;>
    simp [lowBlk, conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_succ, Fin.rev]

private theorem su_commute_embSL3_of_diagonal {t : SU σ 6} {d : Fin 6 → F}
    (ht : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = diagonal d)
    (M : SL(3, F))
    (hpos : diagonal ![d 0, d 1, d 2] * (M : Matrix (Fin 3) (Fin 3) F) =
      (M : Matrix (Fin 3) (Fin 3) F) * diagonal ![d 0, d 1, d 2])
    (hneg : diagonal ![d 3, d 4, d 5] * lowBlk σ M =
      lowBlk σ M * diagonal ![d 3, d 4, d 5]) : Commute t (embSL3 σ hσ M) := by
  change t * embSL3 σ hσ M = embSL3 σ hσ M * t
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSL3, embSL3Mat]
  rw [ht, su_diagonal_pair, pairMat_mul, pairMat_mul, hpos, hneg]

private theorem su_commute_rS0_of_diagonal {t : SU σ 6} {d : Fin 6 → F}
    (ht : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = diagonal d)
    (h01 : d 0 = d 1) (h45 : d 4 = d 5) (m : SL(2, F)) :
    Commute t (rS0 σ hσ m) := by
  have hM : (blk F 0 m : Matrix (Fin 3) (Fin 3) F) =
      !![m 0 0, m 0 1, 0; m 1 0, m 1 1, 0; 0, 0, 1] := by
    simpa only [blk] using coe_blockSL_three_zero m
  have hI : (((blk F 0 m)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![(m⁻¹ : SL(2, F)) 0 0, (m⁻¹ : SL(2, F)) 0 1, 0;
        (m⁻¹ : SL(2, F)) 1 0, (m⁻¹ : SL(2, F)) 1 1, 0; 0, 0, 1] := by
    rw [← map_inv]
    simpa only [blk] using coe_blockSL_three_zero (m⁻¹)
  change Commute t (embSL3 σ hσ (blk F 0 m))
  apply su_commute_embSL3_of_diagonal hσ ht
  · rw [hM]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal_mul, mul_diagonal, h01, mul_comm]
  · ext i j
    simp only [diagonal_mul, mul_diagonal, su_lowBlk_apply]
    rw [hI]
    fin_cases i <;> fin_cases j <;> simp [Fin.rev, h45, mul_comm]

private theorem su_commute_rS1_of_diagonal {t : SU σ 6} {d : Fin 6 → F}
    (ht : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = diagonal d)
    (h12 : d 1 = d 2) (h34 : d 3 = d 4) (m : SL(2, F)) :
    Commute t (rS1 σ hσ m) := by
  have hM : (blk F 1 m : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, m 0 0, m 0 1; 0, m 1 0, m 1 1] := by
    simpa only [blk] using coe_blockSL_three_one m
  have hI : (((blk F 1 m)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, (m⁻¹ : SL(2, F)) 0 0, (m⁻¹ : SL(2, F)) 0 1;
        0, (m⁻¹ : SL(2, F)) 1 0, (m⁻¹ : SL(2, F)) 1 1] := by
    rw [← map_inv]
    simpa only [blk] using coe_blockSL_three_one (m⁻¹)
  change Commute t (embSL3 σ hσ (blk F 1 m))
  apply su_commute_embSL3_of_diagonal hσ ht
  · rw [hM]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal_mul, mul_diagonal, h12, mul_comm]
  · ext i j
    simp only [diagonal_mul, mul_diagonal, su_lowBlk_apply]
    rw [hI]
    fin_cases i <;> fin_cases j <;> simp [Fin.rev, h34, mul_comm]

private theorem su_rS0_torus_diagonal (u : Fˣ) :
    ∃ d : Fin 6 → F,
      ((rS0 σ hσ (torusHom F u) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
        diagonal d := by
  refine ⟨![(u : F), (u : F)⁻¹, 1, 1, σ (u : F), (σ (u : F))⁻¹], ?_⟩
  have hM := coe_blockSL_three_zero (torusHom F u)
  have hI : (((blk F 0 (torusHom F u))⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![(torusHom F u⁻¹) 0 0, (torusHom F u⁻¹) 0 1, 0;
        (torusHom F u⁻¹) 1 0, (torusHom F u⁻¹) 1 1, 0; 0, 0, 1] := by
    rw [← map_inv, ← map_inv]
    simpa only [blk] using coe_blockSL_three_zero (torusHom F u⁻¹)
  simp only [rS0, MonoidHom.comp_apply, coe_embSL3, embSL3Mat, lowBlk]
  rw [show (blk F 0 (torusHom F u) : Matrix (Fin 3) (Fin 3) F) = _ from hM, hI]
  simp only [coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, pairMat_apply, conjTr, antidiag, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.rev]

private theorem su_rS1_torus_diagonal (u : Fˣ) :
    ∃ d : Fin 6 → F,
      ((rS1 σ hσ (torusHom F u) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
        diagonal d := by
  refine ⟨![1, (u : F), (u : F)⁻¹, σ (u : F), (σ (u : F))⁻¹, 1], ?_⟩
  have hM := coe_blockSL_three_one (torusHom F u)
  have hI : (((blk F 1 (torusHom F u))⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, (torusHom F u⁻¹) 0 0, (torusHom F u⁻¹) 0 1;
        0, (torusHom F u⁻¹) 1 0, (torusHom F u⁻¹) 1 1] := by
    rw [← map_inv, ← map_inv]
    simpa only [blk] using coe_blockSL_three_one (torusHom F u⁻¹)
  simp only [rS1, MonoidHom.comp_apply, coe_embSL3, embSL3Mat, lowBlk]
  rw [show (blk F 1 (torusHom F u) : Matrix (Fin 3) (Fin 3) F) = _ from hM, hI]
  simp only [coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, pairMat_apply, conjTr, antidiag, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.rev]

private theorem su_commute_of_diagonal {s t : SU σ 6} {d e : Fin 6 → F}
    (hs : ((s : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = diagonal d)
    (ht : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = diagonal e) : Commute s t := by
  change s * t = t * s
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hs, ht, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  exact mul_comm d e

end NativeBlocks

section HypCoordinates

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a p : ℕ}
  (h : UnitaryFieldData 2 a F)

private theorem su_hyp_six_low (i : Fin 3) :
    hypEquivFin 3 0 (.inl i) = lowIdx (n := 6) i := by
  rw [hypEquivFin_apply_inl]
  rfl

private theorem su_hyp_torus_diagonal {ζ : F}
    {τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0}
    (hτ : ∀ t, (((τ (ofAdd t) : hypSU h 3 0) : GL (HypIndex 3 0) F) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) F) = diagonal (hypEntries ζ t))
    (t : Fin 3 → ZMod p) :
    ∃ d : Fin 6 → F,
      (((SuSplitRootGen.hypSUEquiv h (by decide) (τ (ofAdd t))) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) = diagonal d ∧
      (∀ i : Fin 3, d (lowIdx (n := 6) i) = ζ ^ (t i).val) ∧
      ∀ i : Fin 3, d (Fin.rev (lowIdx (n := 6) i)) = (ζ ^ (t i).val)⁻¹ := by
  let d : Fin 6 → F := fun j => hypEntries ζ t ((hypEquivFin 3 0).symm j)
  refine ⟨d, ?_, ?_, ?_⟩
  · rw [SuSplitRootGen.coe_hypSUEquiv, hτ]
    ext i j
    simp [Matrix.reindex_apply, diagonal, d]
  · intro i
    have he : (hypEquivFin 3 0).symm (lowIdx (n := 6) i) = .inl i := by
      apply (hypEquivFin 3 0).symm_apply_eq.mpr
      exact (su_hyp_six_low i).symm
    change hypEntries ζ t ((hypEquivFin 3 0).symm (lowIdx (n := 6) i)) = _
    rw [he]
    rfl
  · intro i
    have he : hypEquivFin 3 0 (hypPartner (.inl i)) = Fin.rev (lowIdx (n := 6) i) := by
      rw [hypEquivFin_hypPartner (by decide), su_hyp_six_low]
    change hypEntries ζ t ((hypEquivFin 3 0).symm (Fin.rev (lowIdx (n := 6) i))) = _
    rw [← he, Equiv.symm_apply_apply]
    rfl

end HypCoordinates

section ReflectionCommutators

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
  {a n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
  (h : UnitaryFieldData 2 a F)
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin 4 ≃ Fin n}
  {κ : hypSU h 3 0 →* G} {ζ : F} (hζ : IsPrimitiveRoot ζ p)
  {τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0}
  (hτ : ∀ t, (((τ (ofAdd t) : hypSU h 3 0) : GL (HypIndex 3 0) F) :
    Matrix (HypIndex 3 0) (HypIndex 3 0) F) = diagonal (hypEntries ζ t))
  {c : ZMod p}
  (hact : ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
    κ (τ (ofAdd (fun i => c * toAdd (eta b (π i.succ)))) * u *
      (τ (ofAdd (fun i => c * toAdd (eta b (π i.succ)))))⁻¹))

include hR hζ hτ hact

private theorem su_short_le_reflComm
    (i j : Fin 4)
    (r : SL(2, F) →* SU (unitaryInvolution F 2 a) 6)
    (hrT : ∀ u : Fˣ, ∃ d : Fin 6 → F,
      ((r (torusHom F u) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = diagonal d)
    (hr : ∀ b : ↥Bs, eta b (π i) = eta b (π j) → ∀ m : SL(2, F),
      Commute (SuSplitRootGen.hypSUEquiv h (by decide)
        (τ (ofAdd (fun k => c * toAdd (eta b (π k.succ)))))) (r m)) :
    ((κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom).comp r).range ≤
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π i) (π j) : Set G), Bs⁆ := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  let e : hypSU h 3 0 ≃* SU (unitaryInvolution F 2 a) 6 :=
    SuSplitRootGen.hypSUEquiv h (by decide)
  let φ := (κ.comp e.symm.toMonoidHom).comp r
  let u : Fˣ := Units.mk0 ζ (hζ.ne_zero hp.ne_zero)
  have hup : u ^ p = 1 := by
    apply Units.ext
    simpa [u] using hζ.pow_eq_one
  have hu2 : (u : F) ^ 2 ≠ 1 := by
    intro h2
    have hpdiv : p ∣ 2 := hζ.dvd_of_pow_eq_one 2 h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv)
  have hconj (b : ↥Bs) (m : SL(2, F))
      (hm : Commute (e (τ (ofAdd (fun k => c * toAdd (eta b (π k.succ)))))) (r m)) :
      (b : G) * φ m * (b : G)⁻¹ = φ m := by
    have hf : τ (ofAdd (fun k => c * toAdd (eta b (π k.succ)))) * e.symm (r m) *
        (τ (ofAdd (fun k => c * toAdd (eta b (π k.succ)))))⁻¹ = e.symm (r m) := by
      apply e.injective
      have hc : e (τ (ofAdd (fun k => c * toAdd (eta b (π k.succ))))) * r m *
          (e (τ (ofAdd (fun k => c * toAdd (eta b (π k.succ))))))⁻¹ = r m := by
        rw [hm]
        group
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hc
    change (b : G) * κ (e.symm (r m)) * (b : G)⁻¹ = κ (e.symm (r m))
    rw [hact, hf]
  have hRC : φ.range ≤
      Subgroup.centralizer (ggBsCoordEq Bs eta (π i) (π j) : Set G) := by
    rintro _ ⟨m, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbB : b ∈ Bs := ggBsCoordEq_le (π i) (π j) hb
    have hη : eta ⟨b, hbB⟩ (π i) = eta ⟨b, hbB⟩ (π j) :=
      (coe_mem_ggBsCoordEq (b := ⟨b, hbB⟩)).mp hb
    have hc := hconj ⟨b, hbB⟩ m (hr ⟨b, hbB⟩ hη m)
    calc b * φ m = (b * φ m * b⁻¹) * b := by group
      _ = φ m * b := by rw [hc]
  have htB : φ (torusHom F u) ∈ Bs := by
    apply hR.1.1.2.1.2.2.2
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨d, hd, -, -⟩ := su_hyp_torus_diagonal h hτ
        (fun k => c * toAdd (eta ⟨b, hb⟩ (π k.succ)))
      obtain ⟨d', hd'⟩ := hrT u
      have hc := hconj ⟨b, hb⟩ (torusHom F u) (su_commute_of_diagonal hd hd')
      calc b * φ (torusHom F u) = (b * φ (torusHom F u) * b⁻¹) * b := by group
        _ = φ (torusHom F u) * b := by rw [hc]
    · rw [← map_pow, ← map_pow, hup, map_one, map_one]
  exact (ggRange_le_commutator_zpowers_torusHom φ hu2).trans
    (Subgroup.commutator_mono hRC (Subgroup.zpowers_le.mpr htB))

theorem ggSecFiveBPermSU_rS0_le_reflComm :
    ((κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom).comp
      (rS0 (unitaryInvolution F 2 a) (unitaryInvolution_involutive h.card_eq_sq))).range ≤
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 1) (π 2) : Set G), Bs⁆ := by
  apply su_short_le_reflComm hR h hζ hτ hact 1 2 _
    (su_rS0_torus_diagonal (unitaryInvolution_involutive h.card_eq_sq))
  intro b hb m
  obtain ⟨d, hd, hlow, hrev⟩ := su_hyp_torus_diagonal h hτ
    (fun k => c * toAdd (eta b (π k.succ)))
  apply su_commute_rS0_of_diagonal (unitaryInvolution_involutive h.card_eq_sq) hd
  · change d (lowIdx (n := 6) (0 : Fin 3)) = d (lowIdx (n := 6) (1 : Fin 3))
    rw [hlow, hlow]
    change ζ ^ (c * toAdd (eta b (π 1))).val = ζ ^ (c * toAdd (eta b (π 2))).val
    rw [hb]
  · change d (Fin.rev (lowIdx (n := 6) (1 : Fin 3))) =
      d (Fin.rev (lowIdx (n := 6) (0 : Fin 3)))
    rw [hrev, hrev]
    change (ζ ^ (c * toAdd (eta b (π 2))).val)⁻¹ =
      (ζ ^ (c * toAdd (eta b (π 1))).val)⁻¹
    rw [hb]

theorem ggSecFiveBPermSU_rS1_le_reflComm :
    ((κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom).comp
      (rS1 (unitaryInvolution F 2 a) (unitaryInvolution_involutive h.card_eq_sq))).range ≤
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 2) (π 3) : Set G), Bs⁆ := by
  apply su_short_le_reflComm hR h hζ hτ hact 2 3 _
    (su_rS1_torus_diagonal (unitaryInvolution_involutive h.card_eq_sq))
  intro b hb m
  obtain ⟨d, hd, hlow, hrev⟩ := su_hyp_torus_diagonal h hτ
    (fun k => c * toAdd (eta b (π k.succ)))
  apply su_commute_rS1_of_diagonal (unitaryInvolution_involutive h.card_eq_sq) hd
  · change d (lowIdx (n := 6) (1 : Fin 3)) = d (lowIdx (n := 6) (2 : Fin 3))
    rw [hlow, hlow]
    change ζ ^ (c * toAdd (eta b (π 2))).val = ζ ^ (c * toAdd (eta b (π 3))).val
    rw [hb]
  · change d (Fin.rev (lowIdx (n := 6) (2 : Fin 3))) =
      d (Fin.rev (lowIdx (n := 6) (1 : Fin 3)))
    rw [hrev, hrev]
    change (ζ ^ (c * toAdd (eta b (π 3))).val)⁻¹ =
      (ζ ^ (c * toAdd (eta b (π 2))).val)⁻¹
    rw [hb]

end ReflectionCommutators

section OriginalCell


theorem ggSecFiveBPermSU_exists_calibrated_frame_short_commutators
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hMp : GGInnerDiagMpInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n a : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G} {i0 : Fin n}
    (hcell : GGSecFiveBPermSUCell p Bs L 𝒦 n eta a K i0) :
    ∃ h : UnitaryFieldData 2 a (GaloisField 2 (2 * a)),
      ∃ ζ : GaloisField 2 (2 * a), IsPrimitiveRoot ζ p ∧ h.bar ζ = ζ ∧
      ∃ τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0,
        (∀ t, (((τ (ofAdd t) : hypSU h 3 0) : GL (HypIndex 3 0) (GaloisField 2 (2 * a))) :
          Matrix (HypIndex 3 0) (HypIndex 3 0) (GaloisField 2 (2 * a))) =
            diagonal (hypEntries ζ t)) ∧
      ∃ π : Fin 4 ≃ Fin n, π 0 = i0 ∧ ∃ c : ZMod p, c ≠ 0 ∧
      ∃ κ : hypSU h 3 0 →* G,
        Function.Injective κ ∧ κ.range = K ∧
        (∃ (eK : ↥K ≃* SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6)
          (k : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6),
          κ = ((K.subtype.comp eK.symm.toMonoidHom).comp (MulAut.conj k).toMonoidHom).comp
            (SuSplitRootGen.hypSUEquiv h (by decide)).toMonoidHom) ∧
        (∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
          κ (τ (ofAdd (fun i => c * toAdd (eta b (π i.succ)))) * u *
            (τ (ofAdd (fun i => c * toAdd (eta b (π i.succ)))))⁻¹)) ∧
        ((κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom).comp
          (rS0 (unitaryInvolution (GaloisField 2 (2 * a)) 2 a)
            (unitaryInvolution_involutive h.card_eq_sq))).range ≤
          ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 1) (π 2) : Set G), Bs⁆ ∧
        ((κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom).comp
          (rS1 (unitaryInvolution (GaloisField 2 (2 * a)) 2 a)
            (unitaryInvolution_involutive h.card_eq_sq))).range ≤
          ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 2) (π 3) : Set G), Bs⁆ := by
  obtain ⟨h, ζ, hζ, hbar, τ, hτ, π, hπ, c, hc, κ, hκ, hκK, hκrep, hact⟩ :=
    ggSecFiveBPermSU_exists_calibrated_frame hMp hR eta hcell
  exact ⟨h, ζ, hζ, hbar, τ, hτ, π, hπ, c, hc, κ, hκ, hκK, hκrep, hact,
    ggSecFiveBPermSU_rS0_le_reflComm hR h hζ hτ hact,
    ggSecFiveBPermSU_rS1_le_reflComm hR h hζ hτ hact⟩

end OriginalCell

end CFSG.StandardType
