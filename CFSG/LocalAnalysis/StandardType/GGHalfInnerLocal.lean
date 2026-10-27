module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

@[expose] noncomputable def tEps (m e : ℕ) (hm : 1 ≤ m) :
    SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 :=
  omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * omegaBlock (m + 1 + 1) ⟨2, by omega⟩ ^ e

private theorem ggHalfInnerLocal_negOneF2 : (-1 : F2) = 1 := by
  rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]

private noncomputable def ggHalfInnerLocalTheta (n : ℕ) :
    SpecialLinearGroup (Fin n) (ZMod 2) →* SpecialLinearGroup (Fin n) F2 :=
  SpecialLinearGroup.map
    ((GaloisField.equivZmodP (p := 2)).toRingEquiv.symm : ZMod 2 →+* F2)

private theorem ggHalfInnerLocalTheta_injective (n : ℕ) :
    Function.Injective (ggHalfInnerLocalTheta n) := by
  intro A B h
  apply Subtype.ext
  have h1 : ((ggHalfInnerLocalTheta n A : SpecialLinearGroup (Fin n) F2) :
      Matrix (Fin n) (Fin n) F2) =
      ((ggHalfInnerLocalTheta n B : SpecialLinearGroup (Fin n) F2) :
        Matrix (Fin n) (Fin n) F2) :=
    congrArg Subtype.val h
  change (A : Matrix (Fin n) (Fin n) (ZMod 2)).map
      ((GaloisField.equivZmodP (p := 2)).toRingEquiv.symm : ZMod 2 →+* F2) =
    (B : Matrix (Fin n) (Fin n) (ZMod 2)).map
      ((GaloisField.equivZmodP (p := 2)).toRingEquiv.symm : ZMod 2 →+* F2) at h1
  exact Matrix.map_injective
    ((GaloisField.equivZmodP (p := 2)).toRingEquiv.symm).injective h1

private noncomputable def ggHalfInnerLocalOmegaZ (n : ℕ) (k : Fin n) :
    SpecialLinearGroup (Fin (n + 1)) (ZMod 2) :=
  weylRep n (ZMod 2) k *
    SpecialLinearGroup.transvection
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : ZMod 2)

private theorem ggHalfInnerLocalTheta_omegaZ (n : ℕ) (k : Fin n) :
    ggHalfInnerLocalTheta (n + 1) (ggHalfInnerLocalOmegaZ n k) = omegaBlock n k := by
  simp only [ggHalfInnerLocalOmegaZ, omegaBlock, weylRep, ggHalfInnerLocalTheta, map_mul,
    SpecialLinearGroup.map_transvection, map_neg, map_one, ggHalfInnerLocal_negOneF2]

private def ggHalfInnerLocalAMat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 1, 1, 1, 0; 1, 0, 0, 1]

private def ggHalfInnerLocalBMat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 1; 1, 1, 1, 1; 1, 1, 0, 0; 1, 0, 0, 0]

private theorem ggHalfInnerLocalAMat_det : ggHalfInnerLocalAMat.det = 1 := by decide

private theorem ggHalfInnerLocalBMat_det : ggHalfInnerLocalBMat.det = 1 := by decide

private noncomputable def ggHalfInnerLocalA :
    SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨ggHalfInnerLocalAMat, ggHalfInnerLocalAMat_det⟩

private noncomputable def ggHalfInnerLocalB :
    SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨ggHalfInnerLocalBMat, ggHalfInnerLocalBMat_det⟩

private noncomputable def ggHalfInnerLocalRz1 :
    Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  Subgroup.closure {ggHalfInnerLocalA, ggHalfInnerLocalB}

private theorem ggHalfInnerLocalA_mem : ggHalfInnerLocalA ∈ ggHalfInnerLocalRz1 := by
  rw [ggHalfInnerLocalRz1]
  exact Subgroup.subset_closure (by simp)

private theorem ggHalfInnerLocalB_mem : ggHalfInnerLocalB ∈ ggHalfInnerLocalRz1 := by
  rw [ggHalfInnerLocalRz1]
  exact Subgroup.subset_closure (by simp)

private theorem ggHalfInnerLocalA_comm :
    (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB) *
        (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB * ggHalfInnerLocalA) =
      ggHalfInnerLocalA *
        (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB * ggHalfInnerLocalA) *
        (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB) := by
  decide

private theorem ggHalfInnerLocalB_comm :
    (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB) *
        (ggHalfInnerLocalA * ggHalfInnerLocalB * ggHalfInnerLocalA) =
      ggHalfInnerLocalB *
        (ggHalfInnerLocalA * ggHalfInnerLocalB * ggHalfInnerLocalA) *
        (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB) := by
  decide

private theorem ggHalfInnerLocal_commutator_mem {G : Type*} [Group G] {H : Subgroup G}
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y * x⁻¹ * y⁻¹ ∈ ⁅H, H⁆ :=
  Subgroup.commutator_mem_commutator hx hy

private theorem ggHalfInnerLocalRz1_perfect :
    ⁅ggHalfInnerLocalRz1, ggHalfInnerLocalRz1⁆ = ggHalfInnerLocalRz1 := by
  apply le_antisymm (Subgroup.commutator_le_self ggHalfInnerLocalRz1)
  let K : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    ⁅ggHalfInnerLocalRz1, ggHalfInnerLocalRz1⁆
  change ggHalfInnerLocalRz1 ≤ K
  rw [ggHalfInnerLocalRz1, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · have hx1 : ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB ∈
        ggHalfInnerLocalRz1 :=
      Subgroup.mul_mem ggHalfInnerLocalRz1 (Subgroup.mul_mem ggHalfInnerLocalRz1
        (Subgroup.pow_mem ggHalfInnerLocalRz1 ggHalfInnerLocalB_mem 2)
        ggHalfInnerLocalA_mem) ggHalfInnerLocalB_mem
    have hx2 : ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB *
        ggHalfInnerLocalA ∈ ggHalfInnerLocalRz1 :=
      Subgroup.mul_mem ggHalfInnerLocalRz1 hx1 ggHalfInnerLocalA_mem
    have hAz : ggHalfInnerLocalA =
        (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB) *
          (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB *
            ggHalfInnerLocalA) *
          (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB)⁻¹ *
          (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB *
            ggHalfInnerLocalA)⁻¹ := by
      rw [ggHalfInnerLocalA_comm]; group
    rw [hAz]
    exact ggHalfInnerLocal_commutator_mem hx1 hx2
  · have hx1 : ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB ∈
        ggHalfInnerLocalRz1 :=
      Subgroup.mul_mem ggHalfInnerLocalRz1 (Subgroup.mul_mem ggHalfInnerLocalRz1
        (Subgroup.pow_mem ggHalfInnerLocalRz1 ggHalfInnerLocalB_mem 2)
        ggHalfInnerLocalA_mem) ggHalfInnerLocalB_mem
    have hx2 : ggHalfInnerLocalA * ggHalfInnerLocalB * ggHalfInnerLocalA ∈
        ggHalfInnerLocalRz1 :=
      Subgroup.mul_mem ggHalfInnerLocalRz1 (Subgroup.mul_mem ggHalfInnerLocalRz1
        ggHalfInnerLocalA_mem ggHalfInnerLocalB_mem) ggHalfInnerLocalA_mem
    have hBz : ggHalfInnerLocalB =
        (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB) *
          (ggHalfInnerLocalA * ggHalfInnerLocalB * ggHalfInnerLocalA) *
          (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB)⁻¹ *
          (ggHalfInnerLocalA * ggHalfInnerLocalB * ggHalfInnerLocalA)⁻¹ := by
      rw [ggHalfInnerLocalB_comm]; group
    rw [hBz]
    exact ggHalfInnerLocal_commutator_mem hx1 hx2

private theorem ggHalfInnerLocalRz1_element_order :
    orderOf (ggHalfInnerLocalA * ggHalfInnerLocalB * ggHalfInnerLocalB) = 3 := by
  apply orderOf_eq_prime
  · decide
  · decide

private theorem ggHalfInnerLocalRz1_three_dvd : 3 ∣ Nat.card ggHalfInnerLocalRz1 := by
  have hw : ggHalfInnerLocalA * ggHalfInnerLocalB * ggHalfInnerLocalB ∈
      ggHalfInnerLocalRz1 :=
    Subgroup.mul_mem ggHalfInnerLocalRz1 (Subgroup.mul_mem ggHalfInnerLocalRz1
      ggHalfInnerLocalA_mem ggHalfInnerLocalB_mem) ggHalfInnerLocalB_mem
  have h := Subgroup.orderOf_dvd_natCard ggHalfInnerLocalRz1 hw
  rwa [ggHalfInnerLocalRz1_element_order] at h

private noncomputable def ggHalfInnerLocalTz (e : ℕ) :
    SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ggHalfInnerLocalOmegaZ 3 ⟨0, by omega⟩ * ggHalfInnerLocalOmegaZ 3 ⟨2, by omega⟩ ^ e

private theorem ggHalfInnerLocalA_comm_T1z :
    ggHalfInnerLocalA * ggHalfInnerLocalTz 1 = ggHalfInnerLocalTz 1 * ggHalfInnerLocalA := by
  decide

private theorem ggHalfInnerLocalB_comm_T1z :
    ggHalfInnerLocalB * ggHalfInnerLocalTz 1 = ggHalfInnerLocalTz 1 * ggHalfInnerLocalB := by
  decide

private theorem ggHalfInnerLocalRz1_le_centralizer_T1z :
    ggHalfInnerLocalRz1 ≤
      Subgroup.centralizer ({ggHalfInnerLocalTz 1} : Set (SpecialLinearGroup (Fin 4) (ZMod 2))) := by
  rw [ggHalfInnerLocalRz1, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr ggHalfInnerLocalA_comm_T1z
  · exact Subgroup.mem_centralizer_singleton_iff.mpr ggHalfInnerLocalB_comm_T1z

private theorem ggHalfInnerLocal_omegaZ_word :
    ggHalfInnerLocalOmegaZ 3 ⟨2, by omega⟩ =
      (ggHalfInnerLocalB ^ 2 * ggHalfInnerLocalA * ggHalfInnerLocalB) *
        (ggHalfInnerLocalTz 1) ^ 2 := by
  decide

private theorem ggHalfInnerLocalRz1_omega_mem :
    ggHalfInnerLocalOmegaZ 3 ⟨2, by omega⟩ ∈
      ggHalfInnerLocalRz1 ⊔ Subgroup.zpowers (ggHalfInnerLocalTz 1) := by
  rw [ggHalfInnerLocal_omegaZ_word]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left
      (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ ggHalfInnerLocalB_mem 2) ggHalfInnerLocalA_mem)
        ggHalfInnerLocalB_mem))
    (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2))

private def ggHalfInnerLocalSMat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

private theorem ggHalfInnerLocalSMat_det : ggHalfInnerLocalSMat.det = 1 := by decide

private noncomputable def ggHalfInnerLocalS :
    SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨ggHalfInnerLocalSMat, ggHalfInnerLocalSMat_det⟩

private noncomputable def ggHalfInnerLocalA2 :
    SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ggHalfInnerLocalS * ggHalfInnerLocalA * ggHalfInnerLocalS

private noncomputable def ggHalfInnerLocalB2 :
    SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ggHalfInnerLocalS * ggHalfInnerLocalB * ggHalfInnerLocalS

private noncomputable def ggHalfInnerLocalRz2 :
    Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  Subgroup.closure {ggHalfInnerLocalA2, ggHalfInnerLocalB2}

private theorem ggHalfInnerLocalA2_mem : ggHalfInnerLocalA2 ∈ ggHalfInnerLocalRz2 := by
  rw [ggHalfInnerLocalRz2]
  exact Subgroup.subset_closure (by simp)

private theorem ggHalfInnerLocalB2_mem : ggHalfInnerLocalB2 ∈ ggHalfInnerLocalRz2 := by
  rw [ggHalfInnerLocalRz2]
  exact Subgroup.subset_closure (by simp)

private theorem ggHalfInnerLocalA2_comm :
    (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2) *
        (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2 *
          ggHalfInnerLocalA2) =
      ggHalfInnerLocalA2 *
        (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2 *
          ggHalfInnerLocalA2) *
        (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2) := by
  decide

private theorem ggHalfInnerLocalB2_comm :
    (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2) *
        (ggHalfInnerLocalA2 * ggHalfInnerLocalB2 * ggHalfInnerLocalA2) =
      ggHalfInnerLocalB2 *
        (ggHalfInnerLocalA2 * ggHalfInnerLocalB2 * ggHalfInnerLocalA2) *
        (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2) := by
  decide

private theorem ggHalfInnerLocalRz2_perfect :
    ⁅ggHalfInnerLocalRz2, ggHalfInnerLocalRz2⁆ = ggHalfInnerLocalRz2 := by
  apply le_antisymm (Subgroup.commutator_le_self ggHalfInnerLocalRz2)
  let K : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    ⁅ggHalfInnerLocalRz2, ggHalfInnerLocalRz2⁆
  change ggHalfInnerLocalRz2 ≤ K
  rw [ggHalfInnerLocalRz2, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · have hx1 : ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2 ∈
        ggHalfInnerLocalRz2 :=
      Subgroup.mul_mem ggHalfInnerLocalRz2 (Subgroup.mul_mem ggHalfInnerLocalRz2
        (Subgroup.pow_mem ggHalfInnerLocalRz2 ggHalfInnerLocalB2_mem 2)
        ggHalfInnerLocalA2_mem) ggHalfInnerLocalB2_mem
    have hx2 : ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2 *
        ggHalfInnerLocalA2 ∈ ggHalfInnerLocalRz2 :=
      Subgroup.mul_mem ggHalfInnerLocalRz2 hx1 ggHalfInnerLocalA2_mem
    have hAz : ggHalfInnerLocalA2 =
        (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2) *
          (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2 *
            ggHalfInnerLocalA2) *
          (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2)⁻¹ *
          (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2 *
            ggHalfInnerLocalA2)⁻¹ := by
      rw [ggHalfInnerLocalA2_comm]; group
    rw [hAz]
    exact ggHalfInnerLocal_commutator_mem hx1 hx2
  · have hx1 : ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2 ∈
        ggHalfInnerLocalRz2 :=
      Subgroup.mul_mem ggHalfInnerLocalRz2 (Subgroup.mul_mem ggHalfInnerLocalRz2
        (Subgroup.pow_mem ggHalfInnerLocalRz2 ggHalfInnerLocalB2_mem 2)
        ggHalfInnerLocalA2_mem) ggHalfInnerLocalB2_mem
    have hx2 : ggHalfInnerLocalA2 * ggHalfInnerLocalB2 * ggHalfInnerLocalA2 ∈
        ggHalfInnerLocalRz2 :=
      Subgroup.mul_mem ggHalfInnerLocalRz2 (Subgroup.mul_mem ggHalfInnerLocalRz2
        ggHalfInnerLocalA2_mem ggHalfInnerLocalB2_mem) ggHalfInnerLocalA2_mem
    have hBz : ggHalfInnerLocalB2 =
        (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2) *
          (ggHalfInnerLocalA2 * ggHalfInnerLocalB2 * ggHalfInnerLocalA2) *
          (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2)⁻¹ *
          (ggHalfInnerLocalA2 * ggHalfInnerLocalB2 * ggHalfInnerLocalA2)⁻¹ := by
      rw [ggHalfInnerLocalB2_comm]; group
    rw [hBz]
    exact ggHalfInnerLocal_commutator_mem hx1 hx2

private theorem ggHalfInnerLocalRz2_element_order :
    orderOf (ggHalfInnerLocalA2 * ggHalfInnerLocalB2 * ggHalfInnerLocalB2) = 3 := by
  apply orderOf_eq_prime
  · decide
  · decide

private theorem ggHalfInnerLocalRz2_three_dvd : 3 ∣ Nat.card ggHalfInnerLocalRz2 := by
  have hw : ggHalfInnerLocalA2 * ggHalfInnerLocalB2 * ggHalfInnerLocalB2 ∈
      ggHalfInnerLocalRz2 :=
    Subgroup.mul_mem ggHalfInnerLocalRz2 (Subgroup.mul_mem ggHalfInnerLocalRz2
      ggHalfInnerLocalA2_mem ggHalfInnerLocalB2_mem) ggHalfInnerLocalB2_mem
  have h := Subgroup.orderOf_dvd_natCard ggHalfInnerLocalRz2 hw
  rwa [ggHalfInnerLocalRz2_element_order] at h

private theorem ggHalfInnerLocalA2_comm_T2z :
    ggHalfInnerLocalA2 * ggHalfInnerLocalTz 2 = ggHalfInnerLocalTz 2 * ggHalfInnerLocalA2 := by
  decide

private theorem ggHalfInnerLocalB2_comm_T2z :
    ggHalfInnerLocalB2 * ggHalfInnerLocalTz 2 = ggHalfInnerLocalTz 2 * ggHalfInnerLocalB2 := by
  decide

private theorem ggHalfInnerLocalRz2_le_centralizer_T2z :
    ggHalfInnerLocalRz2 ≤
      Subgroup.centralizer ({ggHalfInnerLocalTz 2} : Set (SpecialLinearGroup (Fin 4) (ZMod 2))) := by
  rw [ggHalfInnerLocalRz2, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr ggHalfInnerLocalA2_comm_T2z
  · exact Subgroup.mem_centralizer_singleton_iff.mpr ggHalfInnerLocalB2_comm_T2z

private theorem ggHalfInnerLocal_omegaZ_word2 :
    ggHalfInnerLocalOmegaZ 3 ⟨2, by omega⟩ =
      (ggHalfInnerLocalB2 ^ 2 * ggHalfInnerLocalA2 * ggHalfInnerLocalB2) ^ 2 *
        ggHalfInnerLocalTz 2 := by
  decide

private theorem ggHalfInnerLocalRz2_omega_mem :
    ggHalfInnerLocalOmegaZ 3 ⟨2, by omega⟩ ∈
      ggHalfInnerLocalRz2 ⊔ Subgroup.zpowers (ggHalfInnerLocalTz 2) := by
  rw [ggHalfInnerLocal_omegaZ_word2]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.pow_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ ggHalfInnerLocalB2_mem 2) ggHalfInnerLocalA2_mem)
        ggHalfInnerLocalB2_mem) 2))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

private noncomputable def ggHalfInnerLocalT1 :
    SpecialLinearGroup (Fin 4) F2 :=
  omegaBlock 3 ⟨0, by omega⟩ * omegaBlock 3 ⟨2, by omega⟩

private noncomputable def ggHalfInnerLocalT2 :
    SpecialLinearGroup (Fin 4) F2 :=
  omegaBlock 3 ⟨0, by omega⟩ * omegaBlock 3 ⟨2, by omega⟩ ^ 2

private noncomputable def ggHalfInnerLocalR1 :
    Subgroup (SpecialLinearGroup (Fin 4) F2) :=
  ggHalfInnerLocalRz1.map (ggHalfInnerLocalTheta 4)

private noncomputable def ggHalfInnerLocalR2 :
    Subgroup (SpecialLinearGroup (Fin 4) F2) :=
  ggHalfInnerLocalRz2.map (ggHalfInnerLocalTheta 4)

private theorem ggHalfInnerLocalTheta_T1 :
    ggHalfInnerLocalTheta 4 (ggHalfInnerLocalTz 1) = ggHalfInnerLocalT1 := by
  unfold ggHalfInnerLocalTz ggHalfInnerLocalT1
  rw [map_mul, map_pow, ggHalfInnerLocalTheta_omegaZ, ggHalfInnerLocalTheta_omegaZ,
    pow_one]

private theorem ggHalfInnerLocalTheta_T2 :
    ggHalfInnerLocalTheta 4 (ggHalfInnerLocalTz 2) = ggHalfInnerLocalT2 := by
  unfold ggHalfInnerLocalTz ggHalfInnerLocalT2
  rw [map_mul, map_pow, ggHalfInnerLocalTheta_omegaZ, ggHalfInnerLocalTheta_omegaZ]

private theorem ggHalfInnerLocalR1_three_dvd : 3 ∣ Nat.card ggHalfInnerLocalR1 := by
  unfold ggHalfInnerLocalR1
  rw [Subgroup.card_map_of_injective (ggHalfInnerLocalTheta_injective 4)]
  exact ggHalfInnerLocalRz1_three_dvd

private theorem ggHalfInnerLocalR1_le_centralizer_T1 :
    ggHalfInnerLocalR1 ≤ Subgroup.centralizer ({ggHalfInnerLocalT1} : Set _) := by
  intro r hr
  unfold ggHalfInnerLocalR1 at hr
  obtain ⟨rz, hrz, rfl⟩ := Subgroup.mem_map.mp hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [← ggHalfInnerLocalTheta_T1, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.mp
      (ggHalfInnerLocalRz1_le_centralizer_T1z hrz)]

private theorem ggHalfInnerLocalR1_omega_mem :
    omegaBlock 3 ⟨2, by omega⟩ ∈
      ggHalfInnerLocalR1 ⊔ Subgroup.zpowers ggHalfInnerLocalT1 := by
  have hmem := Subgroup.mem_map_of_mem (ggHalfInnerLocalTheta 4)
    ggHalfInnerLocalRz1_omega_mem
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, ggHalfInnerLocalTheta_T1] at hmem
  rw [ggHalfInnerLocalTheta_omegaZ] at hmem
  exact hmem

private theorem ggHalfInnerLocalR2_three_dvd : 3 ∣ Nat.card ggHalfInnerLocalR2 := by
  unfold ggHalfInnerLocalR2
  rw [Subgroup.card_map_of_injective (ggHalfInnerLocalTheta_injective 4)]
  exact ggHalfInnerLocalRz2_three_dvd

private theorem ggHalfInnerLocalR2_le_centralizer_T2 :
    ggHalfInnerLocalR2 ≤ Subgroup.centralizer ({ggHalfInnerLocalT2} : Set _) := by
  intro r hr
  unfold ggHalfInnerLocalR2 at hr
  obtain ⟨rz, hrz, rfl⟩ := Subgroup.mem_map.mp hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [← ggHalfInnerLocalTheta_T2, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.mp
      (ggHalfInnerLocalRz2_le_centralizer_T2z hrz)]

private theorem ggHalfInnerLocalR2_omega_mem :
    omegaBlock 3 ⟨2, by omega⟩ ∈
      ggHalfInnerLocalR2 ⊔ Subgroup.zpowers ggHalfInnerLocalT2 := by
  have hmem := Subgroup.mem_map_of_mem (ggHalfInnerLocalTheta 4)
    ggHalfInnerLocalRz2_omega_mem
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, ggHalfInnerLocalTheta_T2] at hmem
  rw [ggHalfInnerLocalTheta_omegaZ] at hmem
  exact hmem

private noncomputable def ggHalfInnerLocalEmb : (m : ℕ) →
    SpecialLinearGroup (Fin 4) F2 →* SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2
  | 0 => 1
  | 1 => MonoidHom.id _
  | (n + 2) => (slUpperBlockHom (n + 4) F2).comp (ggHalfInnerLocalEmb (n + 1))

private theorem ggHalfInnerLocalEmb_succ (m : ℕ) (hm : 1 ≤ m) :
    ggHalfInnerLocalEmb (m + 1) =
      (slUpperBlockHom (m + 3) F2).comp (ggHalfInnerLocalEmb m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  rfl

private theorem ggHalfInnerLocalEmb_injective_succ : ∀ d : ℕ,
    Function.Injective (ggHalfInnerLocalEmb (d + 1))
  | 0 => by
      intro x y h
      simpa [ggHalfInnerLocalEmb] using h
  | (d + 1) => by
      rw [ggHalfInnerLocalEmb_succ (d + 1) (by omega)]
      exact slUpperBlockHom_injective.comp (ggHalfInnerLocalEmb_injective_succ d)

private theorem ggHalfInnerLocalEmb_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (ggHalfInnerLocalEmb m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  exact ggHalfInnerLocalEmb_injective_succ d

private theorem ggHalfInnerLocal_slUpper_omegaBlock (n : ℕ) (k : Fin n) :
    slUpperBlockHom (n + 1) F2 (omegaBlock n k) = omegaBlock (n + 1) k.castSucc := by
  simp only [omegaBlock, weylRep, map_mul, slUpperBlockHom_transvection,
    ggHalfInnerLocal_negOneF2]

private theorem ggHalfInnerLocalEmb_omegaBlock_succ : ∀ d : ℕ, ∀ k : Fin 3,
    ggHalfInnerLocalEmb (d + 1) (omegaBlock 3 k) =
      omegaBlock ((d + 1) + 1 + 1) ⟨k.val, by omega⟩
  | 0 => by
      intro k
      simp only [ggHalfInnerLocalEmb, MonoidHom.id_apply]
  | (d + 1) => by
      intro k
      rw [ggHalfInnerLocalEmb_succ (d + 1) (by omega)]
      simp only [MonoidHom.comp_apply]
      rw [ggHalfInnerLocalEmb_omegaBlock_succ d k]
      rw [ggHalfInnerLocal_slUpper_omegaBlock]
      congr 1

private theorem ggHalfInnerLocalEmb_omegaBlock (m : ℕ) (hm : 1 ≤ m) (k : Fin 3) :
    ggHalfInnerLocalEmb m (omegaBlock 3 k) =
      omegaBlock (m + 1 + 1) ⟨k.val, by omega⟩ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  exact ggHalfInnerLocalEmb_omegaBlock_succ d k

private theorem ggHalfInnerLocalEmb_T1 (m : ℕ) (hm : 1 ≤ m) :
    ggHalfInnerLocalEmb m ggHalfInnerLocalT1 = tEps m 1 hm := by
  unfold ggHalfInnerLocalT1 tEps
  rw [map_mul, ggHalfInnerLocalEmb_omegaBlock m hm, ggHalfInnerLocalEmb_omegaBlock m hm,
    pow_one]

private theorem ggHalfInnerLocalEmb_T2 (m : ℕ) (hm : 1 ≤ m) :
    ggHalfInnerLocalEmb m ggHalfInnerLocalT2 = tEps m 2 hm := by
  unfold ggHalfInnerLocalT2 tEps
  rw [map_mul, map_pow, ggHalfInnerLocalEmb_omegaBlock m hm, ggHalfInnerLocalEmb_omegaBlock m hm]

private theorem ggHalfInnerLocal_transvection_mem_slOn {N : ℕ} {S : Set (Fin N)}
    {a b : Fin N} (hab : a ≠ b) (c : F2) (ha : a ∈ S) (hb : b ∈ S) :
    SpecialLinearGroup.transvection hab c ∈ slOn N S :=
  Subgroup.subset_closure ⟨a, b, hab, c, ha, hb, rfl⟩

private theorem ggHalfInnerLocal_slOn_univ (N : ℕ) : slOn N Set.univ = ⊤ := by
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin N) (K := F2)]
  rw [Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_def]
  exact ggHalfInnerLocal_transvection_mem_slOn t.hij t.c (Set.mem_univ _) (Set.mem_univ _)

private theorem ggHalfInnerLocal_castSucc_image (N : ℕ) (hN : 4 ≤ N) :
    Fin.castSucc '' {i : Fin N | i.val < 4} = {i : Fin (N + 1) | i.val < 4} := by
  ext i
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hi
    exact ⟨⟨i.val, lt_of_lt_of_le hi hN⟩, hi, Fin.ext rfl⟩

private theorem ggHalfInnerLocal_slUpper_map_slOn (n : ℕ) (S : Set (Fin n)) :
    (slOn n S).map (slUpperBlockHom n F2) = slOn (n + 1) (Fin.castSucc '' S) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, slOn, Subgroup.closure_le]
    rintro t ⟨a, b, hab, c, ha, hb, rfl⟩
    change slUpperBlockHom n F2 (SpecialLinearGroup.transvection hab c) ∈
      slOn (n + 1) (Fin.castSucc '' S)
    rw [slUpperBlockHom_transvection]
    exact ggHalfInnerLocal_transvection_mem_slOn _ _
      (Set.mem_image_of_mem _ ha) (Set.mem_image_of_mem _ hb)
  · rw [slOn, Subgroup.closure_le]
    rintro t ⟨a, b, hab, c, ⟨a0, ha0, rfl⟩, ⟨b0, hb0, rfl⟩, rfl⟩
    refine Subgroup.mem_map.mpr ⟨SpecialLinearGroup.transvection
      (fun h : a0 = b0 => hab (congrArg Fin.castSucc h)) c, ?_, ?_⟩
    · exact ggHalfInnerLocal_transvection_mem_slOn _ _ ha0 hb0
    · rw [slUpperBlockHom_transvection]

private theorem ggHalfInnerLocalEmb_map_slOn_succ : ∀ d : ℕ,
    (slOn 4 Set.univ).map (ggHalfInnerLocalEmb (d + 1)) ≤
      slOn ((d + 1) + 1 + 1 + 1) {i | i.val < 4}
  | 0 => by
      rw [show ggHalfInnerLocalEmb (0 + 1) = MonoidHom.id _ from rfl]
      rw [Subgroup.map_id]
      apply le_of_eq
      congr 1
      ext i
      simp
  | (d + 1) => by
      rw [ggHalfInnerLocalEmb_succ (d + 1) (by omega)]
      rw [← Subgroup.map_map]
      refine le_trans (Subgroup.map_mono (ggHalfInnerLocalEmb_map_slOn_succ d)) ?_
      rw [ggHalfInnerLocal_slUpper_map_slOn,
        ggHalfInnerLocal_castSucc_image ((d + 1) + 3) (by omega)]

private theorem ggHalfInnerLocalEmb_map_slOn (m : ℕ) (hm : 1 ≤ m) :
    (slOn 4 Set.univ).map (ggHalfInnerLocalEmb m) ≤
      slOn (m + 1 + 1 + 1) {i | i.val < 4} := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  exact ggHalfInnerLocalEmb_map_slOn_succ d

theorem exists_local_sl24 {m : ℕ} (hm : 1 ≤ m) (e : ℕ) (he : e = 1 ∨ e = 2) :
    ∃ R : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2),
      R ≤ slOn (m + 1 + 1 + 1) {i | i.val < 4} ∧ ⁅R, R⁆ = R ∧ 3 ∣ Nat.card R ∧
      (∀ r ∈ R, r * tEps m e hm = tEps m e hm * r) ∧
      omegaBlock (m + 1 + 1) ⟨2, by omega⟩ ∈ R ⊔ Subgroup.zpowers (tEps m e hm) := by
  rcases he with rfl | rfl
  · refine ⟨ggHalfInnerLocalR1.map (ggHalfInnerLocalEmb m), ?_, ?_, ?_, ?_, ?_⟩
    · refine le_trans (Subgroup.map_mono ?_) (ggHalfInnerLocalEmb_map_slOn m hm)
      rw [ggHalfInnerLocal_slOn_univ]
      exact le_top
    · unfold ggHalfInnerLocalR1
      rw [Subgroup.map_map, ← Subgroup.map_commutator ggHalfInnerLocalRz1
        ggHalfInnerLocalRz1 ((ggHalfInnerLocalEmb m).comp (ggHalfInnerLocalTheta 4)),
        ggHalfInnerLocalRz1_perfect]
    · rw [Subgroup.card_map_of_injective (ggHalfInnerLocalEmb_injective m hm)]
      exact ggHalfInnerLocalR1_three_dvd
    · intro r hr
      rw [Subgroup.mem_map] at hr
      obtain ⟨x, hx, rfl⟩ := hr
      rw [← ggHalfInnerLocalEmb_T1 m hm, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp
          (ggHalfInnerLocalR1_le_centralizer_T1 hx)]
    · have hmem := Subgroup.mem_map_of_mem (ggHalfInnerLocalEmb m)
        ggHalfInnerLocalR1_omega_mem
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, ggHalfInnerLocalEmb_T1 m hm] at hmem
      rw [ggHalfInnerLocalEmb_omegaBlock m hm] at hmem
      exact hmem
  · refine ⟨ggHalfInnerLocalR2.map (ggHalfInnerLocalEmb m), ?_, ?_, ?_, ?_, ?_⟩
    · refine le_trans (Subgroup.map_mono ?_) (ggHalfInnerLocalEmb_map_slOn m hm)
      rw [ggHalfInnerLocal_slOn_univ]
      exact le_top
    · unfold ggHalfInnerLocalR2
      rw [Subgroup.map_map, ← Subgroup.map_commutator ggHalfInnerLocalRz2
        ggHalfInnerLocalRz2 ((ggHalfInnerLocalEmb m).comp (ggHalfInnerLocalTheta 4)),
        ggHalfInnerLocalRz2_perfect]
    · rw [Subgroup.card_map_of_injective (ggHalfInnerLocalEmb_injective m hm)]
      exact ggHalfInnerLocalR2_three_dvd
    · intro r hr
      rw [Subgroup.mem_map] at hr
      obtain ⟨x, hx, rfl⟩ := hr
      rw [← ggHalfInnerLocalEmb_T2 m hm, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp
          (ggHalfInnerLocalR2_le_centralizer_T2 hx)]
    · have hmem := Subgroup.mem_map_of_mem (ggHalfInnerLocalEmb m)
        ggHalfInnerLocalR2_omega_mem
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, ggHalfInnerLocalEmb_T2 m hm] at hmem
      rw [ggHalfInnerLocalEmb_omegaBlock m hm] at hmem
      exact hmem

end CFSG.StandardType

end
