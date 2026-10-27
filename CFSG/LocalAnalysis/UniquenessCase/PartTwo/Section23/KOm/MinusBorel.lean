module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusPlane
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.PlaneIsometry

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix
open CFSG.ClassicalGroups.Orthogonal (rootGroupGL lineStabilizer isometry_inv
  mem_lineStabilizer_iff)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K]

theorem planeHom_mem_planeO (b c : K)
    (g : ↥(lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K))) : planeHom b c g ∈ planeO b c := by
  rw [mem_planeO]
  intro w
  rw [coe_planeHom]
  exact binaryForm_planeBlock_mulVec g.2 w

private theorem odd_orderOf_planeHom {b c : K} {g : GL ιM K}
    (hg : g ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)) (hodd : Odd (orderOf g)) :
    Odd (orderOf (planeHom b c ⟨g, hg⟩)) := by
  refine Odd.of_dvd_nat hodd ?_
  have h := orderOf_map_dvd (planeHom b c)
    (⟨g, hg⟩ : ↥(lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)))
  rwa [Subgroup.orderOf_mk] at h

theorem pow_card_add_one_mem_rootGroupGL [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {g : GL ιM K}
    (hg : g ∈ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) (hodd : Odd (orderOf g)) :
    g ^ (Nat.card K + 1) ∈ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) := by
  have hgL : g ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K) :=
    isoFix_le_lineStabilizer b c hg
  have hGodd : Odd (orderOf (planeHom b c ⟨g, hgL⟩)) := odd_orderOf_planeHom hgL hodd
  have hGmem : planeHom b c ⟨g, hgL⟩ ∈ planeO b c := planeHom_mem_planeO b c ⟨g, hgL⟩
  have hGpow : planeHom b c ⟨g, hgL⟩ ^ (Nat.card K + 1) = 1 :=
    pow_card_add_one_eq_one hirr hGmem hGodd
  have hblk : planeBlock ((g ^ (Nat.card K + 1) : GL ιM K) : Matrix ιM ιM K) = 1 := by
    have h : ((planeHom b c ⟨g ^ (Nat.card K + 1), pow_mem hgL (Nat.card K + 1)⟩ :
        GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      have h1 : (⟨g ^ (Nat.card K + 1), pow_mem hgL (Nat.card K + 1)⟩ :
          ↥(lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K))) =
          ⟨g, hgL⟩ ^ (Nat.card K + 1) := Subtype.ext rfl
      rw [h1, map_pow, hGpow, Units.val_one]
    rwa [coe_planeHom b c ⟨g ^ (Nat.card K + 1), pow_mem hgL (Nat.card K + 1)⟩] at h
  exact (planeBlock_eq_one_iff hirr (pow_mem hg (Nat.card K + 1))).mp hblk

theorem conj_mul_inv_pow_card_mem_rootGroupGL [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {t g : GL ιM K}
    (ht : t ∈ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K))
    (htU : t ∉ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) {k : ℕ} (htk : t ^ 2 ^ k = 1)
    (hg : g ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)) (hodd : Odd (orderOf g)) :
    t * g * t⁻¹ * (g ^ Nat.card K)⁻¹ ∈ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let L : Subgroup (GL ιM K) := lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)
  have htL : t ∈ L := isoFix_le_lineStabilizer b c ht
  let t' : ↥L := ⟨t, htL⟩
  let g' : ↥L := ⟨g, hg⟩
  obtain ⟨hgQ, lam, hge⟩ := (mem_lineStabilizer_iff (Q := quadMinus 2 K b c)).mp hg
  have hpow : ∀ n : ℕ, ((g ^ n : GL ιM K) : Matrix ιM ιM K) *ᵥ KTabC.e1M K =
      lam ^ n • KTabC.e1M K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hge,
        smul_smul, ← pow_succ]
  have hgq1 : ((g ^ Nat.card K : GL ιM K) : Matrix ιM ιM K) *ᵥ KTabC.e1M K =
      lam • KTabC.e1M K := by
    rw [hpow (Nat.card K), Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hlam0 : lam ≠ 0 := by
    intro h0
    have h1 : ((g⁻¹ : GL ιM K) : Matrix ιM ιM K) *ᵥ
        ((g : Matrix ιM ιM K) *ᵥ KTabC.e1M K) = 0 := by
      rw [hge, h0, zero_smul, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h1
    exact e1M_ne_zero h1
  have hinv : (((g ^ Nat.card K)⁻¹ : GL ιM K) : Matrix ιM ιM K) *ᵥ KTabC.e1M K =
      lam⁻¹ • KTabC.e1M K := by
    have h := congrArg
      (fun w => (((g ^ Nat.card K)⁻¹ : GL ιM K) : Matrix ιM ιM K) *ᵥ w) hgq1
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec] at h
    have h2 := congrArg (fun w => lam⁻¹ • w) h
    simpa [smul_smul, inv_mul_cancel₀ hlam0] using h2.symm
  have htinv1 : ((t⁻¹ : GL ιM K) : Matrix ιM ιM K) *ᵥ KTabC.e1M K = KTabC.e1M K := by
    have h := congrArg (fun w => ((t⁻¹ : GL ιM K) : Matrix ιM ιM K) *ᵥ w) ht.2
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm
  set z : GL ιM K := t * g * t⁻¹ * (g ^ Nat.card K)⁻¹ with hz
  have hzL : z ∈ L := by
    rw [hz]
    exact mul_mem (mul_mem (mul_mem htL hg) (inv_mem htL)) (inv_mem (pow_mem hg (Nat.card K)))
  let z' : ↥L := ⟨z, hzL⟩
  have hz1 : (z : Matrix ιM ιM K) *ᵥ KTabC.e1M K = KTabC.e1M K := by
    rw [hz, Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, Matrix.mulVec_smul, htinv1,
      Matrix.mulVec_smul, hge, smul_smul, inv_mul_cancel₀ hlam0, one_smul, ht.2]
  have htQ : ∀ v, quadMinus 2 K b c ((t : Matrix ιM ιM K) *ᵥ v) = quadMinus 2 K b c v :=
    isoFix_isometry ht
  have hzQ : ∀ v, quadMinus 2 K b c ((z : Matrix ιM ιM K) *ᵥ v) = quadMinus 2 K b c v := by
    intro v
    have hgqinvQ : ∀ u, quadMinus 2 K b c
        ((((g ^ Nat.card K)⁻¹ : GL ιM K) : Matrix ιM ιM K) *ᵥ u) = quadMinus 2 K b c u :=
      ((mem_lineStabilizer_iff (Q := quadMinus 2 K b c)).mp
        (inv_mem (pow_mem hg (Nat.card K)))).1
    rw [hz, Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [htQ, hgQ, isometry_inv (Q := quadMinus 2 K b c) htQ, hgqinvQ]
  have hzfix : z ∈ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) := by
    rw [mem_isoFix]
    refine ⟨?_, hz1⟩
    intro v
    rw [← coe_quadMinus 2 K b c]
    exact hzQ v
  have hTmem : planeHom b c t' ∈ planeO b c := planeHom_mem_planeO b c t'
  have hGmem : planeHom b c g' ∈ planeO b c := planeHom_mem_planeO b c g'
  have ht'pow : t' ^ 2 ^ k = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact htk
  have hT2 : planeHom b c t' ^ 2 = 1 := by
    refine sq_eq_one_of_pow_two_pow_eq_one (k := k) hirr hTmem ?_
    rw [← map_pow, ht'pow, map_one]
  have hT1 : planeHom b c t' ≠ 1 := by
    intro hT
    apply htU
    have h : ((planeHom b c t' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [hT, Units.val_one]
    rw [coe_planeHom b c t'] at h
    exact (planeBlock_eq_one_iff hirr ht).mp h
  have hGold : Odd (orderOf (planeHom b c g')) := odd_orderOf_planeHom hg hodd
  have hGpow : planeHom b c g' ^ (Nat.card K + 1) = 1 :=
    pow_card_add_one_eq_one hirr hGmem hGold
  have hGq : planeHom b c g' ^ Nat.card K = (planeHom b c g')⁻¹ := by
    have h : planeHom b c g' ^ Nat.card K * planeHom b c g' = 1 := by
      rw [← pow_succ]
      exact hGpow
    exact eq_inv_of_mul_eq_one_left h
  have hconj : planeHom b c t' * planeHom b c g' * (planeHom b c t')⁻¹ =
      (planeHom b c g')⁻¹ := conj_eq_inv hirr hTmem hT2 hT1 hGmem hGold
  have hz'eq : z' = t' * g' * t'⁻¹ * (g' ^ Nat.card K)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv, Subgroup.coe_pow]
  have hzG : planeHom b c z' = 1 := by
    rw [hz'eq, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hconj, hGq, inv_inv,
      inv_mul_cancel]
  have hzblk : planeBlock (z : Matrix ιM ιM K) = 1 := by
    have h := coe_planeHom b c z'
    rw [hzG] at h
    simpa using h.symm
  exact (planeBlock_eq_one_iff hirr hzfix).mp hzblk

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
