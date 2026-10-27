module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.StandardType

namespace GGSpRad

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {r : ℕ} {K : Type} [Field K]

private def mat (g : StatedSp r K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)

private lemma mat_mul (g h : StatedSp r K) : mat (g * h) = mat g * mat h := by
  simp only [mat, Subgroup.coe_mul, Units.val_mul]

private lemma mat_one : mat (1 : StatedSp r K) = 1 := by
  simp only [mat, Subgroup.coe_one, Units.val_one]

private lemma mat_mul_inv (g : StatedSp r K) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

private lemma mat_inv_mul (g : StatedSp r K) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

private lemma form_mulVec (g : StatedSp r K) (u v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (mat g *ᵥ u) (mat g *ᵥ v) = pairedSympForm K r u v := by
  have hg := SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  simp only [mat, pairedSympForm, Matrix.toBilin'_apply'] at hg ⊢
  rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc, hg,
    ← dotProduct_mulVec]

private lemma map_mem_of_mem_stabilizer {W : Submodule K (Fin r ⊕ Fin r → K)} {g : StatedSp r K}
    (hg : g ∈ stabilizer r K W) {v : Fin r ⊕ Fin r → K} (hv : v ∈ W) : mat g *ᵥ v ∈ W := by
  have h := mem_stabilizer.mp hg
  have h' : W.map (mulVecLin (mat g)) = W := h
  have : mat g *ᵥ v ∈ W.map (mulVecLin (mat g)) := ⟨v, hv, by rw [mulVecLin_apply]⟩
  rwa [h'] at this

private lemma perp_mapsTo {W : Submodule K (Fin r ⊕ Fin r → K)} {g : StatedSp r K}
    (hg : g ∈ stabilizer r K W) {y : Fin r ⊕ Fin r → K}
    (hy : y ∈ (pairedSympForm K r).orthogonal W) :
    mat g *ᵥ y ∈ (pairedSympForm K r).orthogonal W := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy ⊢
  intro w hw
  have hw' : mat g⁻¹ *ᵥ w ∈ W := map_mem_of_mem_stabilizer (inv_mem hg) hw
  calc pairedSympForm K r w (mat g *ᵥ y)
      = pairedSympForm K r (mat g *ᵥ (mat g⁻¹ *ᵥ w)) (mat g *ᵥ y) := by
        rw [mulVec_mulVec, mat_mul_inv, one_mulVec]
      _ = pairedSympForm K r (mat g⁻¹ *ᵥ w) y := form_mulVec g _ _
      _ = 0 := hy _ hw'

private lemma sub_one_mem_perp {W : Submodule K (Fin r ⊕ Fin r → K)} {g : StatedSp r K}
    (hgW : ∀ w ∈ W, mat g *ᵥ w = w) (v : Fin r ⊕ Fin r → K) :
    mat g *ᵥ v - v ∈ (pairedSympForm K r).orthogonal W := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  rw [map_sub]
  have h1 : pairedSympForm K r w (mat g *ᵥ v) = pairedSympForm K r w v := by
    conv_lhs => rw [← hgW w hw]
    exact form_mulVec g w v
  rw [h1, sub_self]

private lemma eq_zero_of_forall_mulVec_eq_zero
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hN : ∀ v, N *ᵥ v = 0) : N = 0 := by
  ext i j
  have h1 := congrFun (hN (Pi.single j 1)) i
  rwa [mulVec_single_one, col_apply] at h1

private lemma eq_of_forall_mulVec_eq {M N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_mulVec_eq_zero fun v => by rw [sub_mulVec, h v, sub_self]

private lemma sub_one_pow_three_eq_zero {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hM : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v)) -
      (M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v)) = 0) : (M - 1) ^ 3 = 0 := by
  refine eq_zero_of_forall_mulVec_eq_zero fun v => ?_
  rw [pow_three, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [sub_mulVec, one_mulVec]
  exact hM v

@[expose] def spRadical (W : Submodule K (Fin r ⊕ Fin r → K)) : Subgroup (StatedSp r K) where
  carrier := {g | (∀ w ∈ W,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w = w) ∧
    ∀ y ∈ (pairedSympForm K r).orthogonal W,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y - y ∈ W}
  one_mem' := by
    refine ⟨fun w _ => ?_, fun y _ => ?_⟩
    · change mat (1 : StatedSp r K) *ᵥ w = w
      rw [mat_one, one_mulVec]
    · change mat (1 : StatedSp r K) *ᵥ y - y ∈ W
      rw [mat_one, one_mulVec, sub_self]
      exact W.zero_mem
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hh1, hh2⟩ := hh
    have hg1' : ∀ w ∈ W, mat g *ᵥ w = w := fun w hw => hg1 w hw
    have hg2' : ∀ y ∈ (pairedSympForm K r).orthogonal W, mat g *ᵥ y - y ∈ W :=
      fun y hy => hg2 y hy
    have hh1' : ∀ w ∈ W, mat h *ᵥ w = w := fun w hw => hh1 w hw
    have hh2' : ∀ y ∈ (pairedSympForm K r).orthogonal W, mat h *ᵥ y - y ∈ W :=
      fun y hy => hh2 y hy
    refine ⟨fun w hw => ?_, fun y hy => ?_⟩
    · change mat (g * h) *ᵥ w = w
      rw [mat_mul, ← mulVec_mulVec, hh1' w hw, hg1' w hw]
    · change mat (g * h) *ᵥ y - y ∈ W
      have hz : mat h *ᵥ y - y ∈ W := hh2' y hy
      have hgy : mat g *ᵥ y - y ∈ W := hg2' y hy
      have hgz : mat g *ᵥ (mat h *ᵥ y - y) ∈ W := by rw [hg1' _ hz]; exact hz
      have hsplit : mat h *ᵥ y = y + (mat h *ᵥ y - y) := (add_sub_cancel y (mat h *ᵥ y)).symm
      have key : mat (g * h) *ᵥ y - y =
          (mat g *ᵥ y - y) + mat g *ᵥ (mat h *ᵥ y - y) := by
        rw [mat_mul, ← mulVec_mulVec]
        nth_rewrite 1 [hsplit]
        rw [mulVec_add]
        abel
      rw [key]
      exact add_mem hgy hgz
  inv_mem' := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := hg
    have hg1' : ∀ w ∈ W, mat g *ᵥ w = w := fun w hw => hg1 w hw
    have hg2' : ∀ y ∈ (pairedSympForm K r).orthogonal W, mat g *ᵥ y - y ∈ W :=
      fun y hy => hg2 y hy
    have hginv1 : ∀ w ∈ W, mat g⁻¹ *ᵥ w = w := by
      intro w hw
      have h := congrArg (fun v => mat g⁻¹ *ᵥ v) (hg1' w hw)
      simpa only [mulVec_mulVec, mat_inv_mul, one_mulVec] using h.symm
    refine ⟨fun w hw => ?_, fun y hy => ?_⟩
    · change mat g⁻¹ *ᵥ w = w
      exact hginv1 w hw
    · change mat g⁻¹ *ᵥ y - y ∈ W
      have hz : mat g *ᵥ y - y ∈ W := hg2' y hy
      have key : mat g⁻¹ *ᵥ y - y = -(mat g *ᵥ y - y) := by
        calc mat g⁻¹ *ᵥ y - y
            = mat g⁻¹ *ᵥ y - mat g⁻¹ *ᵥ (mat g *ᵥ y) := by
              rw [mulVec_mulVec, mat_inv_mul, one_mulVec]
          _ = mat g⁻¹ *ᵥ (y - mat g *ᵥ y) := (mulVec_sub _ _ _).symm
          _ = mat g⁻¹ *ᵥ (-(mat g *ᵥ y - y)) := by rw [neg_sub]
          _ = -(mat g⁻¹ *ᵥ (mat g *ᵥ y - y)) := by rw [mulVec_neg]
          _ = -(mat g *ᵥ y - y) := by rw [hginv1 _ hz]
      rw [key]
      exact neg_mem hz

private theorem mem_spRadical' {W : Submodule K (Fin r ⊕ Fin r → K)} {g : StatedSp r K} :
    g ∈ spRadical W ↔ (∀ w ∈ W, mat g *ᵥ w = w) ∧
      ∀ y ∈ (pairedSympForm K r).orthogonal W, mat g *ᵥ y - y ∈ W :=
  Iff.rfl

private lemma sub_one_pow_three_of_mem_spRadical {W : Submodule K (Fin r ⊕ Fin r → K)}
    {g : StatedSp r K} (hg : g ∈ spRadical W) : (mat g - 1) ^ 3 = 0 := by
  obtain ⟨hg1, hg2⟩ := mem_spRadical'.mp hg
  refine sub_one_pow_three_eq_zero fun v => ?_
  have h1 : mat g *ᵥ v - v ∈ (pairedSympForm K r).orthogonal W := sub_one_mem_perp hg1 v
  have h2 : mat g *ᵥ (mat g *ᵥ v - v) - (mat g *ᵥ v - v) ∈ W := hg2 _ h1
  rw [hg1 _ h2, sub_self]

private lemma conj_mem_spRadical {W : Submodule K (Fin r ⊕ Fin r → K)} {s u : StatedSp r K}
    (hs : s ∈ stabilizer r K W) (hu : u ∈ spRadical W) : s * u * s⁻¹ ∈ spRadical W := by
  obtain ⟨hu1, hu2⟩ := mem_spRadical'.mp hu
  refine mem_spRadical'.mpr ⟨fun w hw => ?_, fun y hy => ?_⟩
  · rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    have hs' : mat s⁻¹ *ᵥ w ∈ W := map_mem_of_mem_stabilizer (inv_mem hs) hw
    rw [hu1 _ hs', mulVec_mulVec, mat_mul_inv, one_mulVec]
  · have hs'y : mat s⁻¹ *ᵥ y ∈ (pairedSympForm K r).orthogonal W :=
      perp_mapsTo (inv_mem hs) hy
    have hz : mat u *ᵥ (mat s⁻¹ *ᵥ y) - (mat s⁻¹ *ᵥ y) ∈ W := hu2 _ hs'y
    have hsz : mat s *ᵥ (mat u *ᵥ (mat s⁻¹ *ᵥ y) - (mat s⁻¹ *ᵥ y)) ∈ W :=
      map_mem_of_mem_stabilizer hs hz
    have hs'' : mat s *ᵥ (mat s⁻¹ *ᵥ y) = y := by rw [mulVec_mulVec, mat_mul_inv, one_mulVec]
    have key : mat (s * u * s⁻¹) *ᵥ y - y =
        mat s *ᵥ (mat u *ᵥ (mat s⁻¹ *ᵥ y) - (mat s⁻¹ *ᵥ y)) := by
      rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_sub, hs'']
    rw [key]
    exact hsz

theorem spRadical_le_stabilizer (W : Submodule K (Fin r ⊕ Fin r → K)) :
    spRadical W ≤ stabilizer r K W := by
  intro g hg
  obtain ⟨hg1, hg2⟩ := mem_spRadical'.mp hg
  rw [mem_stabilizer]
  change W.map (mulVecLin (mat g)) = W
  refine le_antisymm ?_ fun w hw => ⟨w, hw, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [mulVecLin_apply, hg1 v hv]
    exact hv
  · rw [mulVecLin_apply]
    exact hg1 w hw

theorem spRadical_normal (W : Submodule K (Fin r ⊕ Fin r → K)) :
    ((spRadical W).subgroupOf (stabilizer r K W)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hmem : (g : StatedSp r K) * (n : StatedSp r K) * (g : StatedSp r K)⁻¹ ∈ spRadical W :=
    conj_mem_spRadical g.2 hn
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmem

theorem isPGroup_spRadical (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : Submodule K (Fin r ⊕ Fin r → K)) : IsPGroup p (spRadical W) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨2, ?_⟩
  have hN : (mat (g : StatedSp r K) - 1) ^ 3 = 0 := sub_one_pow_three_of_mem_spRadical g.2
  have hcomm : Commute (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      (mat (g : StatedSp r K) - 1) := Commute.one_left _
  obtain ⟨r', hr'⟩ := hcomm.exists_add_pow_prime_pow_eq (Fact.out : Nat.Prime p) 2
  have hp2 : 3 ≤ p ^ 2 := by
    have hp2' : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    nlinarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hp2
  have hNpow : (mat (g : StatedSp r K) - 1) ^ p ^ 2 = 0 := by
    rw [hm, pow_add, hN, zero_mul]
  have hpM : ((p : ℕ) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 := by
    ext i j
    rw [Matrix.natCast_apply]
    by_cases h : i = j
    · simp [h, CharP.cast_eq_zero K p]
    · simp [h]
  have hone : mat (g : StatedSp r K) ^ p ^ 2 = 1 := by
    rw [← add_sub_cancel (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (mat (g : StatedSp r K)),
      hr', one_pow, hNpow, hpM]
    simp
  have hpow : (g : StatedSp r K) ^ p ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
    simpa only [mat] using hone
  refine Subtype.ext ?_
  simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hpow

private lemma pairedSympForm_antisymm (u v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r u v + pairedSympForm K r v u = 0 := by
  have h := pairedSympForm_isAlt (u + v)
  simp only [map_add, LinearMap.add_apply, pairedSympForm_self, zero_add, add_zero] at h
  rwa [add_comm] at h

private lemma pairedSympForm_swap (u v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r v u = -pairedSympForm K r u v := by
  rw [eq_neg_iff_add_eq_zero]
  exact pairedSympForm_antisymm v u

private lemma pairedSympForm_toBilin'_conj (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (u v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (A *ᵥ u) (A *ᵥ v) =
      Matrix.toBilin' (Aᵀ * (fromBlocks 0 1 (-1) 0) * A) u v := by
  simp only [pairedSympForm, Matrix.toBilin'_apply']
  rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc,
    ← dotProduct_mulVec]

private lemma mem_statedSp_of_form (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hA : ∀ u v, pairedSympForm K r (A *ᵥ u) (A *ᵥ v) = pairedSympForm K r u v) :
    Aᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * A =
      fromBlocks 0 1 (-1) 0 := by
  apply Matrix.toBilin'.injective
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  rw [← pairedSympForm_toBilin'_conj A u v, hA]
  rfl

private def tvRow (w : Fin r ⊕ Fin r → K) : Fin r ⊕ Fin r → K :=
  (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w

private lemma tvRow_dotProduct (w v : Fin r ⊕ Fin r → K) :
    tvRow w ⬝ᵥ v = pairedSympForm K r v w := by
  rw [dotProduct_comm, tvRow]
  exact (Matrix.toBilin'_apply' (fromBlocks 0 1 (-1) 0 :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) v w).symm

private def transvection (w : Fin r ⊕ Fin r → K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  1 + vecMulVec w (tvRow w)

private def transvectionInv (w : Fin r ⊕ Fin r → K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  1 - vecMulVec w (tvRow w)

private lemma transvection_mulVec (w v : Fin r ⊕ Fin r → K) :
    transvection w *ᵥ v = v + pairedSympForm K r v w • w := by
  simp only [transvection, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    tvRow_dotProduct]

private lemma transvectionInv_mulVec (w v : Fin r ⊕ Fin r → K) :
    transvectionInv w *ᵥ v = v - pairedSympForm K r v w • w := by
  simp only [transvectionInv, sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    tvRow_dotProduct]

private lemma transvection_mul_inv (w : Fin r ⊕ Fin r → K) :
    transvection w * transvectionInv w = 1 := by
  refine eq_of_forall_mulVec_eq fun v => ?_
  rw [← mulVec_mulVec, transvectionInv_mulVec, transvection_mulVec, one_mulVec]
  have h : pairedSympForm K r (v - pairedSympForm K r v w • w) w = pairedSympForm K r v w := by
    simp [map_sub, map_smul, pairedSympForm_self]
  rw [h, sub_add_cancel]

private lemma transvection_inv_mul (w : Fin r ⊕ Fin r → K) :
    transvectionInv w * transvection w = 1 := by
  refine eq_of_forall_mulVec_eq fun v => ?_
  rw [← mulVec_mulVec, transvection_mulVec, transvectionInv_mulVec, one_mulVec]
  have h : pairedSympForm K r (v + pairedSympForm K r v w • w) w = pairedSympForm K r v w := by
    simp [map_add, map_smul, pairedSympForm_self]
  rw [h]
  abel

private lemma transvection_preserves (w : Fin r ⊕ Fin r → K) :
    ∀ u v, pairedSympForm K r (transvection w *ᵥ u) (transvection w *ᵥ v) =
      pairedSympForm K r u v := by
  intro u v
  rw [transvection_mulVec, transvection_mulVec]
  have hww : pairedSympForm K r w w = 0 := pairedSympForm_self w
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hww,
    mul_zero, add_zero, zero_add]
  rw [pairedSympForm_swap v w]
  ring

private def transvectionSp (w : Fin r ⊕ Fin r → K) : StatedSp r K :=
  ⟨Units.mk (transvection w) (transvectionInv w) (transvection_mul_inv w) (transvection_inv_mul w),
    SymplecticTorusWeyl.mem_statedSp_iff.mpr (mem_statedSp_of_form (transvection w)
      (transvection_preserves w))⟩

private lemma mat_transvectionSp (w : Fin r ⊕ Fin r → K) :
    mat (transvectionSp w) = transvection w := rfl

private lemma transvectionSp_mem_spRadical {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) {w : Fin r ⊕ Fin r → K} (hw : w ∈ W) :
    transvectionSp w ∈ spRadical W := by
  refine mem_spRadical'.mpr ⟨fun w' hw' => ?_, fun y hy => ?_⟩
  · rw [mat_transvectionSp, transvection_mulVec, hW w' hw' w hw, zero_smul, add_zero]
  · rw [mat_transvectionSp, transvection_mulVec]
    have hyw : pairedSympForm K r y w = 0 := by
      rw [pairedSympForm_swap w y, (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) w hw, neg_zero]
    rw [hyw, zero_smul, add_zero, sub_self]
    exact W.zero_mem

private def eichler (w y : Fin r ⊕ Fin r → K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  1 + vecMulVec y (tvRow w) + vecMulVec w (tvRow y)

private def eichlerInv (w y : Fin r ⊕ Fin r → K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  1 - vecMulVec y (tvRow w) - vecMulVec w (tvRow y)

private lemma eichler_mulVec (w y v : Fin r ⊕ Fin r → K) :
    eichler w y *ᵥ v = v + pairedSympForm K r v w • y + pairedSympForm K r v y • w := by
  simp only [eichler, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, tvRow_dotProduct]

private lemma eichlerInv_mulVec (w y v : Fin r ⊕ Fin r → K) :
    eichlerInv w y *ᵥ v = v - pairedSympForm K r v w • y - pairedSympForm K r v y • w := by
  simp only [eichlerInv, sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    tvRow_dotProduct]

private lemma eichler_mul_inv {w y : Fin r ⊕ Fin r → K}
    (hwy : pairedSympForm K r w y = 0) : eichler w y * eichlerInv w y = 1 := by
  have hyw : pairedSympForm K r y w = 0 := by
    rw [pairedSympForm_swap w y, hwy, neg_zero]
  refine eq_of_forall_mulVec_eq fun v => ?_
  rw [← mulVec_mulVec, eichlerInv_mulVec, eichler_mulVec, one_mulVec]
  have h1 : pairedSympForm K r (v - pairedSympForm K r v w • y - pairedSympForm K r v y • w) w =
      pairedSympForm K r v w := by
    simp [map_sub, map_smul, pairedSympForm_self, hwy, hyw]
  have h2 : pairedSympForm K r (v - pairedSympForm K r v w • y - pairedSympForm K r v y • w) y =
      pairedSympForm K r v y := by
    simp [map_sub, map_smul, pairedSympForm_self, hwy, hyw]
  rw [h1, h2]
  abel

private lemma eichler_inv_mul {w y : Fin r ⊕ Fin r → K}
    (hwy : pairedSympForm K r w y = 0) : eichlerInv w y * eichler w y = 1 := by
  have hyw : pairedSympForm K r y w = 0 := by
    rw [pairedSympForm_swap w y, hwy, neg_zero]
  refine eq_of_forall_mulVec_eq fun v => ?_
  rw [← mulVec_mulVec, eichler_mulVec, eichlerInv_mulVec, one_mulVec]
  have h1 : pairedSympForm K r (v + pairedSympForm K r v w • y + pairedSympForm K r v y • w) w =
      pairedSympForm K r v w := by
    simp [map_add, map_smul, pairedSympForm_self, hwy, hyw]
  have h2 : pairedSympForm K r (v + pairedSympForm K r v w • y + pairedSympForm K r v y • w) y =
      pairedSympForm K r v y := by
    simp [map_add, map_smul, pairedSympForm_self, hwy, hyw]
  rw [h1, h2]
  abel

private lemma eichler_preserves {w y : Fin r ⊕ Fin r → K}
    (hwy : pairedSympForm K r w y = 0) :
    ∀ u v, pairedSympForm K r (eichler w y *ᵥ u) (eichler w y *ᵥ v) =
      pairedSympForm K r u v := by
  intro u v
  rw [eichler_mulVec, eichler_mulVec]
  have hyw : pairedSympForm K r y w = 0 := by
    rw [pairedSympForm_swap w y, hwy, neg_zero]
  have hyv : pairedSympForm K r y v = -pairedSympForm K r v y := pairedSympForm_swap v y
  have hwv : pairedSympForm K r w v = -pairedSympForm K r v w := pairedSympForm_swap v w
  have hyu : pairedSympForm K r y u = -pairedSympForm K r u y := pairedSympForm_swap u y
  have hwu : pairedSympForm K r w u = -pairedSympForm K r u w := pairedSympForm_swap u w
  have hww : pairedSympForm K r w w = 0 := pairedSympForm_self w
  have hyy : pairedSympForm K r y y = 0 := pairedSympForm_self y
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hww, hyy,
    hwy, hyw, mul_zero, add_zero, zero_add]
  rw [pairedSympForm_swap v y, pairedSympForm_swap v w]
  ring

private def eichlerSp {w y : Fin r ⊕ Fin r → K} (hwy : pairedSympForm K r w y = 0) :
    StatedSp r K :=
  ⟨Units.mk (eichler w y) (eichlerInv w y) (eichler_mul_inv hwy) (eichler_inv_mul hwy),
    SymplecticTorusWeyl.mem_statedSp_iff.mpr (mem_statedSp_of_form (eichler w y)
      (eichler_preserves hwy))⟩

private lemma mat_eichlerSp {w y : Fin r ⊕ Fin r → K} (hwy : pairedSympForm K r w y = 0) :
    mat (eichlerSp hwy) = eichler w y := rfl

private lemma eichlerSp_mem_spRadical {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) {w y : Fin r ⊕ Fin r → K}
    (hw : w ∈ W) (hy : y ∈ (pairedSympForm K r).orthogonal W)
    (hwy : pairedSympForm K r w y = 0) : eichlerSp hwy ∈ spRadical W := by
  refine mem_spRadical'.mpr ⟨fun w' hw' => ?_, fun y' hy' => ?_⟩
  · rw [mat_eichlerSp, eichler_mulVec]
    have h1 : pairedSympForm K r w' w = 0 := hW w' hw' w hw
    have h2 : pairedSympForm K r w' y = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) w' hw'
    rw [h1, h2, zero_smul, zero_smul, add_zero, add_zero]
  · rw [mat_eichlerSp, eichler_mulVec]
    have h1 : pairedSympForm K r y' w = 0 := by
      rw [pairedSympForm_swap w y',
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hy') w hw, neg_zero]
    rw [h1, zero_smul, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ hw

private lemma commute_mat_of_mem_radical {W : Submodule K (Fin r ⊕ Fin r → K)}
    {w₀ : Fin r ⊕ Fin r → K} (hw₀ : w₀ ∈ W) (hw₀0 : w₀ ≠ 0) {s : StatedSp r K}
    (hs : s ∈ stabilizer r K W)
    (hc : ∀ u ∈ spRadical W, s * u * s⁻¹ * u⁻¹ ∈ SymplecticHigher.spScalars r K)
    {u : StatedSp r K} (hu : u ∈ spRadical W) : mat s * mat u = mat u * mat s := by
  obtain ⟨hu1, _⟩ := mem_spRadical'.mp hu
  obtain ⟨huinv1, _⟩ := mem_spRadical'.mp (inv_mem hu)
  have hsp : s * u * s⁻¹ * u⁻¹ ∈ SymplecticHigher.spScalars r K := hc u hu
  rw [SymplecticHigher.spScalars, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hsp
  obtain ⟨c, hc⟩ := hsp
  have hw0fix : mat (s * u * s⁻¹ * u⁻¹) *ᵥ w₀ = w₀ := by
    rw [mat_mul, mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      huinv1 w₀ hw₀, hu1 _ (map_mem_of_mem_stabilizer (inv_mem hs) hw₀), mulVec_mulVec,
      mat_mul_inv, one_mulVec]
  have hcw : c • w₀ = w₀ := by
    have h : (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : Matrix (Fin r ⊕ Fin r)
        (Fin r ⊕ Fin r) K) *ᵥ w₀ = w₀ := by
      rw [hc]
      exact hw0fix
    rwa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have hc1 : c = 1 := by
    have hck : (c : K) = 1 := by
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hw₀0
      have hx1 : (c : K) * w₀ x = w₀ x := by
        have := congrFun hcw x
        simpa [Pi.smul_apply, Units.smul_def, smul_eq_mul] using this
      exact mul_right_cancel₀ hx (by rw [one_mul]; exact hx1)
    exact Units.ext hck
  have hmat1 : mat (s * u * s⁻¹ * u⁻¹) = 1 := by
    have h := congrArg (fun g : GL (Fin r ⊕ Fin r) K =>
      ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) hc.symm
    change ((↑(s * u * s⁻¹ * u⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1
    rw [h, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hc1]
    simp
  have hx1 : s * u * s⁻¹ * u⁻¹ = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa only [mat, Subgroup.coe_one, Units.val_one] using hmat1
  have hsueq : s * u = u * s := by
    calc s * u = s * u * s⁻¹ * u⁻¹ * (u * s) := by group
      _ = u * s := by rw [hx1, one_mul]
  rw [← mat_mul, ← mat_mul, hsueq]

theorem exists_scalar_mul_mem_spRadical {W : Submodule K (Fin r ⊕ Fin r → K)} (h0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) {s : StatedSp r K}
    (hs : s ∈ stabilizer r K W)
    (hc : ∀ u ∈ spRadical W, s * u * s⁻¹ * u⁻¹ ∈ SymplecticHigher.spScalars r K) :
    ∃ z ∈ SymplecticHigher.spScalars r K, ∃ q ∈ spRadical W, s = z * q := by
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hstar : ∀ {w : Fin r ⊕ Fin r → K}, w ∈ W → ∀ v,
      pairedSympForm K r v w • (mat s *ᵥ w) = pairedSympForm K r (mat s *ᵥ v) w • w := by
    intro w hw v
    have hmem : transvectionSp w ∈ spRadical W := transvectionSp_mem_spRadical hW hw
    have hcomm := commute_mat_of_mem_radical hw₀ hw₀0 hs hc hmem
    rw [mat_transvectionSp] at hcomm
    have h1 := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K => M *ᵥ v) hcomm
    simp only [← mulVec_mulVec, transvection_mulVec, mulVec_add, mulVec_smul, one_mulVec] at h1
    exact add_left_cancel h1
  have hnondeg : ∀ {w : Fin r ⊕ Fin r → K}, w ≠ 0 →
      ∃ v, pairedSympForm K r v w ≠ 0 := by
    intro w hw
    by_contra! hcon
    have horth : w ∈ (pairedSympForm K r).orthogonal ⊤ := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n _
      exact hcon n
    have hbot := congrArg (fun N : Submodule K (Fin r ⊕ Fin r → K) => w ∈ N)
      (LinearMap.BilinForm.orthogonal_top_eq_bot
        SymplecticFlag.pairedSympForm_nondegenerate)
    rw [hbot, Submodule.mem_bot] at horth
    exact hw horth
  have heig : ∀ {w : Fin r ⊕ Fin r → K}, w ∈ W → ∃ c : K, mat s *ᵥ w = c • w := by
    intro w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · exact ⟨0, by simp⟩
    · obtain ⟨v, hv⟩ := hnondeg hw0
      have h := hstar hw v
      refine ⟨pairedSympForm K r (mat s *ᵥ v) w / pairedSympForm K r v w, ?_⟩
      have h' : mat s *ᵥ w = (pairedSympForm K r v w)⁻¹ •
          ((pairedSympForm K r v w) • (mat s *ᵥ w)) := (inv_smul_smul₀ hv _).symm
      rw [h', h, smul_smul]
      congr 1
      rw [div_eq_mul_inv, mul_comm]
  have h_SW : ∀ x ∈ W, mulVecLin (mat s) x ∈ W := fun x hx => map_mem_of_mem_stabilizer hs hx
  let f : W →ₗ[K] W := (mat s).mulVecLin.restrict h_SW
  have hnotLI : ∀ w : W, ¬LinearIndependent K ![w, f w] := by
    intro w hli
    obtain ⟨c, hcstar⟩ := heig w.2
    have hfw : f w = c • w := by
      apply Subtype.ext
      change mat s *ᵥ (w : Fin r ⊕ Fin r → K) = c • (w : Fin r ⊕ Fin r → K)
      exact hcstar
    have hrel : c • w + (-1 : K) • f w = 0 := by
      rw [hfw]
      module
    have hcontra := (LinearIndependent.pair_iff.mp hli) c (-1) hrel
    exact one_ne_zero (neg_eq_zero.mp hcontra.2)
  obtain ⟨μ, hμ⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hnotLI
  have hμw : ∀ w ∈ W, mat s *ᵥ w = μ • w := by
    intro w hw
    have h1 := LinearMap.congr_fun hμ ⟨w, hw⟩
    have h2 := congrArg Subtype.val h1
    simpa [f, LinearMap.smul_apply, Matrix.mulVecLin_apply] using h2
  have hμne : μ ≠ 0 := by
    intro hμ0
    have hz : mat s *ᵥ w₀ = 0 := by rw [hμw w₀ hw₀, hμ0, zero_smul]
    have h1 := congrArg (fun v => mat s⁻¹ *ᵥ v) hz
    rw [mulVec_mulVec, mat_inv_mul, one_mulVec, mulVec_zero] at h1
    exact hw₀0 h1
  have hstar' : ∀ {w : Fin r ⊕ Fin r → K}, w ∈ W → ∀ v,
      pairedSympForm K r (mat s *ᵥ v) w = μ * pairedSympForm K r v w := by
    intro w hw v
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · have h := hstar hw v
      rw [hμw w hw, smul_smul] at h
      have h' : pairedSympForm K r (mat s *ᵥ v) w = pairedSympForm K r v w * μ := by
        have hh : (fun x : K => x • w) (pairedSympForm K r v w * μ)
            = (fun x : K => x • w) (pairedSympForm K r (mat s *ᵥ v) w) := h
        exact (smul_left_injective K hw0 hh).symm
      rw [h', mul_comm]
  have hμ2 : μ ^ 2 = 1 := by
    obtain ⟨v, hv⟩ := hnondeg hw₀0
    have hiso := form_mulVec s v w₀
    rw [hμw w₀ hw₀] at hiso
    rw [map_smul, smul_eq_mul] at hiso
    rw [hstar' hw₀ v, ← mul_assoc] at hiso
    have hfin : (μ * μ) * pairedSympForm K r v w₀ = 1 * pairedSympForm K r v w₀ := by
      rw [one_mul]
      exact hiso
    have hcancel := mul_right_cancel₀ hv hfin
    rw [sq]
    exact hcancel
  have hSy : ∀ y ∈ (pairedSympForm K r).orthogonal W, mat s *ᵥ y - μ • y ∈ W := by
    intro y hy
    have hwy : pairedSympForm K r w₀ y = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) w₀ hw₀
    have hmem : eichlerSp hwy ∈ spRadical W := eichlerSp_mem_spRadical hW hw₀ hy hwy
    have hcomm := commute_mat_of_mem_radical hw₀ hw₀0 hs hc hmem
    rw [mat_eichlerSp] at hcomm
    obtain ⟨v, hv⟩ := hnondeg hw₀0
    have h1 := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K => M *ᵥ v) hcomm
    simp only [← mulVec_mulVec, eichler_mulVec, mulVec_add, mulVec_smul, one_mulVec] at h1
    have h2 : pairedSympForm K r v w₀ • (mat s *ᵥ y)
          + pairedSympForm K r v y • (mat s *ᵥ w₀)
        = pairedSympForm K r (mat s *ᵥ v) w₀ • y
          + pairedSympForm K r (mat s *ᵥ v) y • w₀ := by
      have h := h1
      simp only [add_assoc] at h
      exact add_left_cancel h
    rw [hμw w₀ hw₀, hstar' hw₀ v] at h2
    have key : pairedSympForm K r v w₀ • (mat s *ᵥ y - μ • y)
        = (pairedSympForm K r (mat s *ᵥ v) y - μ * pairedSympForm K r v y) • w₀ := by
      have h2' := h2
      rw [smul_smul] at h2'
      have hX : pairedSympForm K r v w₀ • (mat s *ᵥ y)
          = (μ * pairedSympForm K r v w₀) • y + pairedSympForm K r (mat s *ᵥ v) y • w₀
            - (pairedSympForm K r v y * μ) • w₀ := by
        rw [eq_sub_iff_add_eq]
        exact h2'
      rw [smul_sub, smul_smul, hX]
      rw [sub_smul, mul_comm μ (pairedSympForm K r v w₀),
        mul_comm (pairedSympForm K r v y) μ]
      abel
    have hfin : mat s *ᵥ y - μ • y
        = (pairedSympForm K r v w₀)⁻¹ •
          ((pairedSympForm K r (mat s *ᵥ v) y - μ * pairedSympForm K r v y) • w₀) := by
      rw [← key, inv_smul_smul₀ hv]
    rw [hfin]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hw₀)
  have hμsq : μ * μ = 1 := by rw [sq] at hμ2; exact hμ2
  have hμform : ∀ u v, pairedSympForm K r
      ((μ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ u)
      ((μ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ v) =
      pairedSympForm K r u v := by
    intro u v
    have h1 : (μ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ u = μ • u := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 : (μ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ v = μ • v := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h1, h2]
    have h3 : pairedSympForm K r (μ • u) = μ • pairedSympForm K r u := map_smul _ μ u
    have h4 : pairedSympForm K r u (μ • v) = μ • pairedSympForm K r u v := map_smul _ μ v
    rw [h3, LinearMap.smul_apply, h4, smul_eq_mul, smul_eq_mul, ← mul_assoc, hμsq, one_mul]
  let uμ : Kˣ := Units.mk0 μ hμne
  have hscalar : (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) uμ) ∈ StatedSp r K :=
    SymplecticTorusWeyl.mem_statedSp_iff.mpr (by
      have h : (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) uμ : Matrix (Fin r ⊕ Fin r)
          (Fin r ⊕ Fin r) K) = (μ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := by
        rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal]
        rfl
      rw [h]
      exact mem_statedSp_of_form (μ • 1) hμform)
  let z : StatedSp r K := ⟨Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) uμ, hscalar⟩
  have hzsp : z ∈ SymplecticHigher.spScalars r K := by
    rw [SymplecticHigher.spScalars, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    exact ⟨uμ, rfl⟩
  have hmatz : mat z = μ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    change ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) uμ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = μ • 1
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
    rfl
  let q : StatedSp r K := z⁻¹ * s
  have hzq : z * q = s := by dsimp only [q]; group
  have hmul : (μ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) * mat q = mat s := by
    rw [← hmatz, ← mat_mul, hzq]
  have hq : q ∈ spRadical W := by
    refine mem_spRadical'.mpr ⟨fun w hw => ?_, fun y hy => ?_⟩
    · have h := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K => M *ᵥ w) hmul
      rw [← mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
      rw [hμw w hw] at h
      have hh : (fun x : Fin r ⊕ Fin r → K => μ • x) (mat q *ᵥ w)
          = (fun x : Fin r ⊕ Fin r → K => μ • x) w := h
      exact smul_right_injective (Fin r ⊕ Fin r → K) hμne hh
    · have h := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K => M *ᵥ y) hmul
      rw [← mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
      have hy' : mat q *ᵥ y = μ⁻¹ • (mat s *ᵥ y) := by
        have h' : mat q *ᵥ y = μ⁻¹ • (μ • (mat q *ᵥ y)) := (inv_smul_smul₀ hμne _).symm
        rw [h] at h'
        exact h'
      rw [hy']
      have hz := hSy y hy
      have hkey : μ⁻¹ • (mat s *ᵥ y) - y = μ⁻¹ • (mat s *ᵥ y - μ • y) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hμne, one_smul]
      rw [hkey]
      exact Submodule.smul_mem _ _ hz
  exact ⟨z, hzsp, q, hq, by dsimp only [q]; group⟩

end GGSpRad

end CFSG.StandardType
