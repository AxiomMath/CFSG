module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusL4Tools
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char
import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSL2
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.Adapters.RankTwoModelTransports
import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projImage)
open scoped MatrixGroups

namespace Item211Res4Proof

open Item228Census3Proof Item228Census5Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

set_option hygiene false in
local notation "SL₄" => (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker

set_option hygiene false in
local notation "PSL₄" => projImage (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker

variable {K : Type} [Field K]

@[expose] noncomputable def coordZ (Z : GL V₄ K) : GL (Fin 4) K ≃* GL V₄ K :=
  (reindexV₄ K).symm.trans (MulAut.conj Z)

theorem coordZ_apply (Z : GL V₄ K) (X : GL (Fin 4) K) :
    coordZ Z X = Z * (reindexV₄ K).symm X * Z⁻¹ :=
  rfl

theorem coordZ_neg_one (Z : GL V₄ K) : coordZ Z (-1) = -1 := by
  rw [coordZ_apply]
  have e : (reindexV₄ K).symm (-1 : GL (Fin 4) K) = -1 := by
    apply Units.ext
    change (Matrix.reindexAlgEquiv K K idxV₄).symm (-1) = -1
    rw [map_neg, map_one]
  rw [e]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_neg, Units.val_one, Matrix.mul_neg, Matrix.mul_one,
    Matrix.neg_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem coordZ_rel (Z : GL V₄ K) {X Y : GL (Fin 4) K}
    (h : (X : Matrix (Fin 4) (Fin 4) K) * Y = Y * X ∨
      (X : Matrix (Fin 4) (Fin 4) K) * Y = -((Y : Matrix (Fin 4) (Fin 4) K) * X)) :
    ((coordZ Z X : GL V₄ K) : Matrix V₄ V₄ K) * (coordZ Z Y : GL V₄ K) =
        (coordZ Z Y : GL V₄ K) * (coordZ Z X : GL V₄ K) ∨
      ((coordZ Z X : GL V₄ K) : Matrix V₄ V₄ K) * (coordZ Z Y : GL V₄ K) =
        -(((coordZ Z Y : GL V₄ K) : Matrix V₄ V₄ K) * (coordZ Z X : GL V₄ K)) := by
  rcases h with h | h
  · left
    have h' : X * Y = Y * X := Units.ext h
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, h']
  · right
    have h' : X * Y = -1 * (Y * X) := Units.ext (by
      rw [Units.val_mul, h, Units.val_mul, Units.val_neg, Units.val_one, Matrix.neg_mul,
        Matrix.one_mul, Units.val_mul])
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, h', map_mul, coordZ_neg_one]
    rw [Units.val_mul, Units.val_neg, Units.val_one, Matrix.neg_mul, Matrix.one_mul]

theorem coordZ_reindex (Z X : GL V₄ K) : coordZ Z (reindexV₄ K X) = Z * X * Z⁻¹ := by
  rw [coordZ_apply, MulEquiv.symm_apply_apply]

@[expose] noncomputable def psiZ (Z : GL V₄ K) : SL(2, K) →* GL (Fin 4) K :=
  (reindexV₄ K : GL V₄ K →* GL (Fin 4) K).comp ((MulAut.conj Z⁻¹).toMonoidHom.comp blkDiag)

theorem coordZ_psiZ (Z : GL V₄ K) (B : SL(2, K)) : coordZ Z (psiZ Z B) = blkDiag B := by
  change coordZ Z (reindexV₄ K (MulAut.conj Z⁻¹ (blkDiag B))) = _
  rw [coordZ_reindex, MulAut.conj_apply, inv_inv]
  group

theorem psiZ_mem (Z : GL V₄ K) (B : SL(2, K)) : psiZ Z B ∈ SL₄ := by
  change reindexV₄ K (MulAut.conj Z⁻¹ (blkDiag B)) ∈ _
  rw [← mem_ker_det_reindex_iff, MulAut.conj_apply, ← mem_ker_det_conj_iff]
  exact blkDiag_mem_ker B

theorem phiCube_neg_one (P : GL V₄ K) : phiCube P (-1) = -1 := by
  have e : iotaCube (-1 : SL(2, cubeAlg K)) = -1 := by
    apply Units.ext
    rw [coe_iotaCube, Units.val_neg, Units.val_one, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, ← fromBlocks_one, fromBlocks_neg]
    simp
  change reindexV₄ K (MulAut.conj P⁻¹ (iotaCube (-1))) = -1
  rw [e, MulAut.conj_apply]
  apply Units.ext
  rw [coe_reindexV₄, Units.val_mul, Units.val_mul, Units.val_neg, Units.val_one, Matrix.mul_neg,
    Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Units.val_neg,
    Units.val_one]
  ext i j
  simp [Matrix.reindex_apply, Matrix.one_apply]

@[expose] def cubeSL : SL(2, K) := ⟨cubeMat K, det_cubeMat⟩

theorem cubeSL_pow_three : (cubeSL : SL(2, K)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change cubeMat K ^ 3 = 1
  rw [pow_three', cubeMat_cube]

theorem quat_blk_conj {a c : K} {x : Matrix V₄ V₄ K}
    (hx : x = 1 ∨ x = quatBlockU a c ∨ x = quatBlockV ∨ x = quatBlockU a c * quatBlockV)
    {y yi : Matrix (Fin 2) (Fin 2) K} (hy : yi * y = 1) (B : Matrix (Fin 2) (Fin 2) K) :
    x * fromBlocks y 0 0 y * fromBlocks B 0 0 B =
      fromBlocks (y * B * yi) 0 0 (y * B * yi) * (x * fromBlocks y 0 0 y) := by
  have hD : ∀ M N : Matrix (Fin 2) (Fin 2) K,
      fromBlocks M 0 0 M * fromBlocks N 0 0 N = fromBlocks (M * N) 0 0 (M * N) := fun M N => by
    rw [fromBlocks_multiply]
    simp
  rw [← Matrix.mul_assoc (fromBlocks (y * B * yi) 0 0 (y * B * yi)) x, ← quat_elem_commute hx,
    Matrix.mul_assoc x (fromBlocks (y * B * yi) 0 0 (y * B * yi)), hD, Matrix.mul_assoc x, hD,
    Matrix.mul_assoc (y * B), hy, Matrix.mul_one]

set_option maxHeartbeats 400000 in
theorem excMinus_L4_cube [Finite K] (hK : ∀ s : K, s * s + s + 1 ≠ 0) (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) {a c : K} (hac : a * a + c * c = -1)
    [Group.IsPerfect (SL(2, cubeAlg K))] (hZ : Subgroup.center PSL₄ = ⊥)
    {D T : Subgroup (MulAut PSL₄)} (hDi : D ≤ (MulAut.conj : PSL₄ →* MulAut PSL₄).range)
    (hTi : T ≤ (MulAut.conj : PSL₄ →* MulAut PSL₄).range)
    (hDe : IsElemAbelian 3 D) (hTe : IsElemAbelian 2 T) (hT4 : Nat.card T = 4)
    (hTD : ⁅T, D⁆ = T) {A : SL₄} (hA3 : A ^ 3 = 1) {P : GL V₄ K}
    (hD : ((P * (reindexV₄ K).symm (A : GL (Fin 4) K) * P⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks (cubeMat K) 0 0 (cubeMat K))
    (hfD : MulAut.conj (projRestrict SL₄ A) ∈ D)
    (hfT : MulAut.conj (projRestrict SL₄ A) ∈ Subgroup.centralizer (T : Set (MulAut PSL₄)))
    {u : MulAut PSL₄} (hu : u ∈ T) (hu1 : u ≠ 1) {q : MulAut PSL₄}
    (hq : q ∈ inSubgroup (CFSG.pCore 2)
      (threeGen ((MulAut.conj : PSL₄ →* MulAut PSL₄).range ⊓
        Subgroup.centralizer ({u} : Set (MulAut PSL₄))) ⊓
          Subgroup.centralizer (T : Set (MulAut PSL₄)))) :
    q * MulAut.conj (projRestrict SL₄ A) = MulAut.conj (projRestrict SL₄ A) * q := by
  classical
  have hZ4 : ∀ s : Kˣ, GeneralLinearGroup.scalar (Fin 4) s ∈ SL₄ → s ^ 4 = 1 :=
    fun s hs => pow_four_eq_one_of_scalar_mem_ker hs
  have hinj := Item211Lie2Proof.conj_injective' hZ
  obtain ⟨hφ, hker, hdec⟩ := cube_data_L4 hK hD
  obtain ⟨-, hcomm, -⟩ := bridge _ hZ hZ4 hA3 (phiCube P) hφ hdec hDi hDe hfD
  have hTC : T ≤ (MulAut.conj : PSL₄ →* MulAut PSL₄).range ⊓
      Subgroup.centralizer ({MulAut.conj (projRestrict SL₄ A)} : Set (MulAut PSL₄)) :=
    fun t ht => Subgroup.mem_inf.mpr ⟨hTi ht, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hfT t ht)⟩
  have hDC := le_inf_centralizer hDe hfD hDi
  have hTr := le_range_of_commutator_eq hTC hDC hTD hcomm
  have : IsDomain (cubeAlg K) := (isField_cubeAlg hK).isDomain
  have h2R : (2 : cubeAlg K) ≠ 0 := by
    intro h
    have e := congrArg (fun x : cubeAlg K => (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp at e
    exact h2 e
  set ι4 := iotaOf _ (phiCube P) hφ.1 with hι4
  have hιker : ∀ x, ι4 x = 1 ↔ x = 1 ∨ x = -1 := fun x => by
    rw [hι4, iotaOf_eq_one_iff _ hZ, hker]
    refine ⟨sl2_eq_one_or_neg_one_of_mem_center, ?_⟩
    rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (by simp)
  obtain ⟨t₂, ht₂T, ht₂1, ht₂u⟩ := exists_ne_one_ne hT4 u
  obtain ⟨U, hUu⟩ := hTr hu
  obtain ⟨V, hVt⟩ := hTr ht₂T
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hTe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ T, x * x = 1 := fun x hx => by rw [← sq]; exact hTe.2 x hx
  obtain ⟨hUm, hVm, hUVm⟩ := quat_of_commuting_involutions h2R ι4 hιker (U := U) (V := V)
    (by rw [hUu]; exact hsq u hu) (by rw [hVt]; exact hsq t₂ ht₂T)
    (by rw [hUu, hVt]; exact hTcomm u hu t₂ ht₂T) (by rw [hUu]; exact hu1)
    (by rw [hVt]; exact ht₂1) (by rw [hUu, hVt]; exact ht₂u)
  set a' := algebraMap K (cubeAlg K) a with ha'
  set c' := algebraMap K (cubeAlg K) c with hc'
  have hac' : a' * a' + c' * c' = -1 := by
    rw [ha', hc', ← map_mul, ← map_mul, ← map_add, hac, map_neg, map_one]
  have hunit : ∀ r : cubeAlg K, r ≠ 0 → IsUnit r := fun r hr => by
    obtain ⟨s, hs⟩ := (isField_cubeAlg hK).mul_inv_cancel hr
    exact IsUnit.of_mul_eq_one s hs
  obtain ⟨PR, PiR, hPP, hPP', hUq, hVq⟩ := exists_quat_normal_form hunit h2R hac' hUm hVm hUVm
  have hu0 : cubeBlockHom (!![-a', -c'; -c', a'] : Matrix (Fin 2) (Fin 2) (cubeAlg K)) =
      quatBlockU a c := by
    have e : (!![-a', -c'; -c', a'] : Matrix (Fin 2) (Fin 2) (cubeAlg K)) =
        (!![-a, -c; -c, a] : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (cubeAlg K)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha', hc']
    rw [e, cubeBlockHom_algebraMap, quatBlockU]
    simp
  have hj0 : cubeBlockHom (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (cubeAlg K)) = quatBlockV := by
    have e : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (cubeAlg K)) =
        (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (cubeAlg K)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [e, cubeBlockHom_algebraMap, quatBlockV]
    simp
  have hP4 : cubeBlockHom PR * cubeBlockHom PiR = 1 := by rw [← map_mul, hPP, map_one]
  have hP4' : cubeBlockHom PiR * cubeBlockHom PR = 1 := by rw [← map_mul, hPP', map_one]
  let Z₄ : GL V₄ K := ⟨cubeBlockHom PR, cubeBlockHom PiR, hP4, hP4'⟩
  set Z : GL V₄ K := Z₄ * P with hZdef
  have hZφ : ∀ X : SL(2, cubeAlg K), coordZ Z (phiCube P X) = Z₄ * iotaCube X * Z₄⁻¹ := by
    intro X
    change coordZ Z (reindexV₄ K (MulAut.conj P⁻¹ (iotaCube X))) = _
    rw [coordZ_reindex, MulAut.conj_apply, hZdef, inv_inv]
    group
  have hUZ : ((coordZ Z (phiCube P U) : GL V₄ K) : Matrix V₄ V₄ K) = quatBlockU a c := by
    rw [hZφ, Units.val_mul, Units.val_mul]
    have e := congrArg cubeBlockHom hUq
    rw [map_mul, map_mul, hu0] at e
    change cubeBlockHom PR * cubeBlockHom (U : Matrix (Fin 2) (Fin 2) (cubeAlg K)) *
      cubeBlockHom PiR = _
    rw [Matrix.mul_assoc, e, ← Matrix.mul_assoc, hP4, Matrix.one_mul]
  have hVZ : ((coordZ Z (phiCube P V) : GL V₄ K) : Matrix V₄ V₄ K) = quatBlockV := by
    rw [hZφ, Units.val_mul, Units.val_mul]
    have e := congrArg cubeBlockHom hVq
    rw [map_mul, map_mul, hj0] at e
    change cubeBlockHom PR * cubeBlockHom (V : Matrix (Fin 2) (Fin 2) (cubeAlg K)) *
      cubeBlockHom PiR = _
    rw [Matrix.mul_assoc, e, ← Matrix.mul_assoc, hP4, Matrix.one_mul]
  have hAZ : coordZ Z (A : GL (Fin 4) K) = blkDiag cubeSL := by
    apply Units.ext
    rw [coordZ_apply, hZdef, coe_blkDiag]
    have e : (Z₄ * P * (reindexV₄ K).symm (A : GL (Fin 4) K) * (Z₄ * P)⁻¹ : GL V₄ K) =
        Z₄ * (P * (reindexV₄ K).symm (A : GL (Fin 4) K) * P⁻¹) * Z₄⁻¹ := by group
    rw [e, Units.val_mul, Units.val_mul, hD]
    change cubeBlockHom PR * fromBlocks (cubeMat K) 0 0 (cubeMat K) * cubeBlockHom PiR = _
    rw [cubeBlockHom_commute, Matrix.mul_assoc, hP4, Matrix.mul_one]
    rfl
  set κ := iotaOf _ (psiZ Z) (psiZ_mem Z) with hκ
  have hκa : ∀ B, κ B = MulAut.conj (projRestrict SL₄ ⟨psiZ Z B, psiZ_mem Z B⟩) := fun B => rfl
  have hκf : κ cubeSL = MulAut.conj (projRestrict SL₄ A) := by
    rw [hκa]
    congr 2
    apply Subtype.ext
    apply (coordZ Z).injective
    change coordZ Z (psiZ Z cubeSL) = _
    rw [coordZ_psiZ, hAZ]
  have hκker : ∀ B, κ B = 1 → B = 1 ∨ B = -1 := by
    intro B hB
    rw [hκ, iotaOf_eq_one_iff _ hZ] at hB
    have hB' : B ∈ (ProjGenLinGroup.mk.comp blkDiag).ker := by
      have e : (ProjGenLinGroup.mk.comp (psiZ Z)).ker =
          (ProjGenLinGroup.mk.comp blkDiag).ker := by
        rw [psiZ, ker_mk_reindexV₄, ker_mk_conj]
      rwa [e] at hB
    exact eq_one_or_neg_one_of_mk_blkDiag hB'
  have hcommZ : ∀ (B : SL(2, K)) (X : GL (Fin 4) K) (hX : X ∈ SL₄),
      ((coordZ Z X : GL V₄ K) : Matrix V₄ V₄ K) * blkDiag B = blkDiag B * (coordZ Z X : GL V₄ K) →
      κ B * MulAut.conj (projRestrict SL₄ ⟨X, hX⟩) =
        MulAut.conj (projRestrict SL₄ ⟨X, hX⟩) * κ B := by
    intro B X hX h
    rw [hκa, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    apply (coordZ Z).injective
    apply Units.ext
    change ((coordZ Z (psiZ Z B * X) : GL V₄ K) : Matrix V₄ V₄ K) =
      ((coordZ Z (X * psiZ Z B) : GL V₄ K) : Matrix V₄ V₄ K)
    rw [map_mul, map_mul, coordZ_psiZ, Units.val_mul, Units.val_mul, h]
  have hκU : ∀ B, κ B * u = u * κ B := by
    intro B
    rw [← hUu]
    refine hcommZ B _ (hφ.1 U) ?_
    rw [hUZ, coe_blkDiag]
    exact (quatBlockU_commute a c _).symm
  have hκV : ∀ B, κ B * t₂ = t₂ * κ B := by
    intro B
    rw [← hVt]
    refine hcommZ B _ (hφ.1 V) ?_
    rw [hVZ, coe_blkDiag]
    exact (quatBlockV_commute _).symm
  have hκT : ∀ B, κ B ∈ Subgroup.centralizer (T : Set (MulAut PSL₄)) := by
    intro B
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rcases four_group_cases hTe hT4 hu ht₂T hu1 ht₂1 ht₂u t ht with h | h | h | h
    · rw [h, one_mul, mul_one]
    · rw [h, hκU]
    · rw [h, hκV]
    · rw [h]
      calc u * t₂ * κ B = u * (t₂ * κ B) := mul_assoc _ _ _
        _ = u * (κ B * t₂) := by rw [hκV]
        _ = (u * κ B) * t₂ := (mul_assoc _ _ _).symm
        _ = (κ B * u) * t₂ := by rw [hκU]
        _ = κ B * (u * t₂) := mul_assoc _ _ _
  set Δ := threeGen ((MulAut.conj : PSL₄ →* MulAut PSL₄).range ⊓
    Subgroup.centralizer ({u} : Set (MulAut PSL₄))) with hΔ
  set H := Δ ⊓ Subgroup.centralizer (T : Set (MulAut PSL₄)) with hH
  set Q := inSubgroup (CFSG.pCore 2) H with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map H.subtype
  have hQN : H ≤ Subgroup.normalizer (Q : Set (MulAut PSL₄)) := fun b hb =>
    CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H hb
  have hΔInn : Δ ≤ (MulAut.conj : PSL₄ →* MulAut PSL₄).range :=
    (Subgroup.closure_le _).mpr fun x hx => (Subgroup.mem_inf.mp hx.1).1
  have hκu : ∀ B, κ B ∈ (MulAut.conj : PSL₄ →* MulAut PSL₄).range ⊓
      Subgroup.centralizer ({u} : Set (MulAut PSL₄)) := fun B =>
    Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr (hκU B)⟩
  have hfΔ : MulAut.conj (projRestrict SL₄ A) ∈ Δ := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, ?_⟩, 1, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hfT u hu).symm
    · rw [pow_one, ← map_pow, ← map_pow, hA3, map_one, map_one]
  have hκΔ : ∀ B, κ B ∈ Δ := fun B =>
    Item211Lie3Proof.mem_of_normalizer hK4 h2 κ (fun b => mem_normalizer_threeGen (hκu b))
      (X := cubeSL) (Item211Lie3Proof.not_isScalar2_of_root h3 det_cubeMat cubeMat_sq_add)
      cubeSL_pow_three (z := 1) (fun b => by rw [mul_one, one_mul])
      (by rw [mul_one, hκf]; exact hfΔ) B
  have hκH : ∀ B, κ B ∈ H := fun B => Subgroup.mem_inf.mpr ⟨hκΔ B, hκT B⟩
  have hqH : q ∈ H := Subgroup.map_subtype_le _ hq
  obtain ⟨y, rfl⟩ := hΔInn (Subgroup.mem_inf.mp hqH).1
  obtain ⟨X, rfl⟩ := projRestrict_surjective SL₄ y
  have hqT := (Subgroup.mem_inf.mp hqH).2
  have hXW : ∀ W : SL(2, cubeAlg K), W * W = -1 → ι4 W ∈ T →
      ((coordZ Z (X : GL (Fin 4) K) : GL V₄ K) : Matrix V₄ V₄ K) * (coordZ Z (phiCube P W)) =
          (coordZ Z (phiCube P W) : GL V₄ K) * (coordZ Z (X : GL (Fin 4) K) : GL V₄ K) ∨
        ((coordZ Z (X : GL (Fin 4) K) : GL V₄ K) : Matrix V₄ V₄ K) * (coordZ Z (phiCube P W)) =
          -(((coordZ Z (phiCube P W) : GL V₄ K) : Matrix V₄ V₄ K) *
            (coordZ Z (X : GL (Fin 4) K) : GL V₄ K)) := by
    intro W hW hWT
    have hc : projRestrict SL₄ X * projRestrict SL₄ ⟨phiCube P W, hφ.1 W⟩ =
        projRestrict SL₄ ⟨phiCube P W, hφ.1 W⟩ * projRestrict SL₄ X := hinj (by
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp hqT _ hWT).symm)
    have hh : ((phiCube P W : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (phiCube P W : GL (Fin 4) K) = -1 := by
      rw [← Units.val_mul, ← map_mul, hW, phiCube_neg_one, Units.val_neg, Units.val_one]
    exact coordZ_rel Z (X := (X : GL (Fin 4) K)) (Y := phiCube P W)
      (commute_or_anticommute_of_mk SL₄ hc hh)
  have hUU : U * U = -1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, hUm, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one])
  have hVV : V * V = -1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, hVm, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one])
  have hgU := hXW U hUU (by rw [hUu]; exact hu)
  have hgV := hXW V hVV (by rw [hVt]; exact ht₂T)
  rw [hUZ] at hgU
  rw [hVZ] at hgV
  obtain ⟨x, Y, hx, hXY⟩ := quat_centralizer_decomp h2 hac _ hgU hgV
  have hβ : ∀ B, κ (CFSG.GH74.Generic.S3.glConj Y B) =
      MulAut.conj (projRestrict SL₄ X) * κ B * (MulAut.conj (projRestrict SL₄ X))⁻¹ := by
    intro B
    have hmat : ((coordZ Z (X : GL (Fin 4) K) : GL V₄ K) : Matrix V₄ V₄ K) *
        (blkDiag B : GL V₄ K) = (blkDiag (CFSG.GH74.Generic.S3.glConj Y B) : GL V₄ K) *
          (coordZ Z (X : GL (Fin 4) K) : GL V₄ K) := by
      rw [hXY, coe_blkDiag, coe_blkDiag, CFSG.GH74.Generic.S3.coe_glConj]
      exact quat_blk_conj hx (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) _
    have hGL : coordZ Z (X : GL (Fin 4) K) * blkDiag B * (coordZ Z (X : GL (Fin 4) K))⁻¹ =
        blkDiag (CFSG.GH74.Generic.S3.glConj Y B) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Units.ext hmat
    have e : MulAut.conj (projRestrict SL₄ X) * κ B * (MulAut.conj (projRestrict SL₄ X))⁻¹ =
        MulAut.conj (projRestrict SL₄ (X * ⟨psiZ Z B, psiZ_mem Z B⟩ * X⁻¹)) := by
      rw [hκa]
      simp only [map_mul, map_inv]
    rw [e, hκa]
    congr 2
    apply Subtype.ext
    apply (coordZ Z).injective
    change coordZ Z (psiZ Z (CFSG.GH74.Generic.S3.glConj Y B)) =
      coordZ Z ((X : GL (Fin 4) K) * psiZ Z B * (X : GL (Fin 4) K)⁻¹)
    rw [map_mul, map_mul, map_inv, coordZ_psiZ, coordZ_psiZ, hGL]
  rw [← hκf]
  exact centralizes_of_sl2_normal hK4 κ hκH hκker hQ2 hQN hq
    (CFSG.GH74.Generic.S3.glConj Y) hβ cubeSL

theorem excMinusFor_L4 [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    (hp2 : p % 3 = 2) (hKc : Nat.card K = p) : Item211Lie2Proof.ExcMinusFor PSL₄ := by
  classical
  have hp' : p.Prime := Fact.out
  have hq3 : Nat.card K % 3 = 2 := by rw [hKc]; exact hp2
  have hK : ∀ s : K, s * s + s + 1 ≠ 0 := no_root_of_card_mod_three hq3
  have h3 : (3 : K) ≠ 0 := by
    have h := hK 1
    norm_num at h
    exact h
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hK4 : 4 ≤ Nat.card K := by omega
  have hZ : Subgroup.center PSL₄ = ⊥ := center_projSL_four_eq_bot
  have hZ4 : ∀ s : Kˣ, GeneralLinearGroup.scalar (Fin 4) s ∈ SL₄ → s ^ 4 = 1 :=
    fun s hs => pow_four_eq_one_of_scalar_mem_ker hs
  have hinj := Item211Lie2Proof.conj_injective' hZ
  intro D T hDi hTi hDe _ hTe hT4 _ hTD u hu hu1 f hf
  obtain ⟨hfD, hfT⟩ := Subgroup.mem_inf.mp hf
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  by_cases hf1 : f = 1
  · rw [hf1, mul_one, one_mul]
  obtain ⟨y, rfl⟩ := hDi hfD
  have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hDe.2 _ hfD, map_one])
  have hy1 : y ≠ 1 := fun h => hf1 (by rw [h, map_one])
  obtain ⟨A, rfl, hA3, hA1⟩ := exists_lift_cube SL₄ hZ4 y (orderOf_eq_prime hy3 hy1)
  have hA'3 : (reindexV₄ K).symm (A : GL (Fin 4) K) ^ 3 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, hA3, Subgroup.coe_one, map_one]
  have hA'1 : (reindexV₄ K).symm (A : GL (Fin 4) K) ≠ 1 := fun h => hA1 (Subtype.ext (by
    have e := congrArg (reindexV₄ K) h
    rwa [MulEquiv.apply_symm_apply, map_one] at e))
  obtain ⟨P, hD | hD⟩ := exists_normal_form_GL4 hK hq3 hA'3 hA'1
  ·
    exfalso
    obtain ⟨hφ, hker, hdec⟩ := plane_data_L4 hK h3 hD
    obtain ⟨-, hcomm, -⟩ := bridge _ hZ hZ4 hA3 (phiPlane P) hφ hdec hDi hDe hfD
    have hTC : T ≤ (MulAut.conj : PSL₄ →* MulAut PSL₄).range ⊓
        Subgroup.centralizer ({MulAut.conj (projRestrict SL₄ A)} : Set (MulAut PSL₄)) :=
      fun t ht => Subgroup.mem_inf.mpr ⟨hTi ht, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hfT t ht)⟩
    have hTr := le_range_of_commutator_eq hTC (le_inf_centralizer hDe hfD hDi) hTD hcomm
    have hιinj : Function.Injective (iotaOf _ (phiPlane P) hφ.1) := by
      rw [injective_iff_map_eq_one]
      intro s hs
      rw [iotaOf_eq_one_iff _ hZ, hker] at hs
      exact Subgroup.mem_bot.mp hs
    have := card_le_two_of_le_range_sl2 h2 hιinj hTe hTr
    omega
  ·
    have hcard2 : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
    obtain ⟨ψ⟩ := nonempty_ringEquiv_cubeAlg hK (GaloisField p 2) (by rw [hcard2, hKc])
    let e2 := CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2) ψ
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) (GaloisField p 2)) :=
      CFSG.ClassicalInvolution.sl2_isPerfect (by
        rw [hcard2]
        have := Nat.pow_le_pow_left (show 2 ≤ p by omega) 2
        omega)
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) (cubeAlg K)) :=
      Group.IsPerfect.ofSurjective (f := e2.symm.toMonoidHom) e2.symm.surjective
    have : NeZero p := ⟨hp'.ne_zero⟩
    obtain ⟨a, c, hac⟩ := CharP.sq_add_sq K p (-1)
    have hac' : (a : K) * a + (c : K) * c = -1 := by
      rw [← sq, ← sq, hac]
      push_cast
      rfl
    exact excMinus_L4_cube hK h2 h3 hK4 hac' hZ hDi hTi hDe hTe hT4 hTD hA3 hD hfD hfT hu hu1 hq

end Item211Res4Proof

open Item211Res4Proof

theorem ks211ExcMinusL4_holds : KS211ExcMinusL4 := by
  intro p _ hp3 hp2
  have hKc : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have : Finite (GaloisField p 1) :=
    Nat.finite_of_card_ne_zero (by rw [hKc]; exact (Fact.out : p.Prime).ne_zero)
  exact excMinusFor_L4 hp3 hp2 hKc

end CFSG.RankThree.PartTwo.Sec21
