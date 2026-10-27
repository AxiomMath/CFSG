module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped commutatorElement

private abbrev k328r4g_M : Matrix (Fin 2) (Fin 2) (ZMod 2) := rhoOmega (ZMod 2)

private def k328r4g_z : GL (Fin 6) (ZMod 2) :=
  ⟨blockDiag3 (ZMod 2) 6 k328r4g_M k328r4g_M k328r4g_M,
    blockDiag3 (ZMod 2) 6 (k328r4g_M ^ 2) (k328r4g_M ^ 2) (k328r4g_M ^ 2),
    by decide +kernel, by decide +kernel⟩

private def k328r4g_t : GL (Fin 6) (ZMod 2) :=
  ⟨blockDiag3 (ZMod 2) 6 k328r4g_M (k328r4g_M ^ 2) 1,
    blockDiag3 (ZMod 2) 6 (k328r4g_M ^ 2) k328r4g_M 1,
    by decide +kernel, by decide +kernel⟩

private abbrev k328r4g_T (i j : Fin 6) (h : i ≠ j := by decide) : GL (Fin 6) (ZMod 2) :=
  Matrix.GeneralLinearGroup.transvection i j h 1

private def k328r4g_J : Subgroup (GL (Fin 6) (ZMod 2)) :=
  Subgroup.centralizer {k328r4g_z} ⊔ Subgroup.centralizer {k328r4g_t} ⊔
    Subgroup.centralizer {k328r4g_z * k328r4g_t} ⊔
    Subgroup.centralizer {k328r4g_z * k328r4g_t ^ 2}

private theorem k328r4g_comm_mem {G : Type*} [Group G] {J : Subgroup G} {a b : G} (ha : a ∈ J)
    (hb : b ∈ J) : ⁅a, b⁆ ∈ J := by
  rw [commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)

private theorem k328r4g_mem_z {x : GL (Fin 6) (ZMod 2)} (h : k328r4g_z * x = x * k328r4g_z) :
    x ∈ k328r4g_J :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.2 h.symm)))

private theorem k328r4g_mem_t {x : GL (Fin 6) (ZMod 2)} (h : k328r4g_t * x = x * k328r4g_t) :
    x ∈ k328r4g_J :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.2 h.symm)))

private theorem k328r4g_mem_zt {x : GL (Fin 6) (ZMod 2)}
    (h : k328r4g_z * k328r4g_t * x = x * (k328r4g_z * k328r4g_t)) : x ∈ k328r4g_J :=
  Subgroup.mem_sup_left
    (Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.2 h.symm))

private theorem k328r4g_mem_ztt {x : GL (Fin 6) (ZMod 2)}
    (h : k328r4g_z * k328r4g_t ^ 2 * x = x * (k328r4g_z * k328r4g_t ^ 2)) : x ∈ k328r4g_J :=
  Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.2 h.symm)

private theorem k328r4g_inblock :
    k328r4g_T 0 1 ∈ k328r4g_J ∧ k328r4g_T 1 0 ∈ k328r4g_J ∧ k328r4g_T 2 3 ∈ k328r4g_J ∧
    k328r4g_T 3 2 ∈ k328r4g_J ∧ k328r4g_T 4 5 ∈ k328r4g_J ∧ k328r4g_T 5 4 ∈ k328r4g_J :=
  ⟨k328r4g_mem_ztt (by decide +kernel), k328r4g_mem_ztt (by decide +kernel),
    k328r4g_mem_zt (by decide +kernel), k328r4g_mem_zt (by decide +kernel),
    k328r4g_mem_t (by decide +kernel), k328r4g_mem_t (by decide +kernel)⟩

private theorem k328r4g_cross :
    k328r4g_T 0 2 * k328r4g_T 1 3 ∈ k328r4g_J ∧ k328r4g_T 2 4 * k328r4g_T 3 5 ∈ k328r4g_J ∧
    k328r4g_T 4 0 * k328r4g_T 5 1 ∈ k328r4g_J :=
  ⟨k328r4g_mem_z (by decide +kernel), k328r4g_mem_z (by decide +kernel),
    k328r4g_mem_z (by decide +kernel)⟩

private theorem k328r4g_T12 : k328r4g_T 1 2 ∈ k328r4g_J := by
  obtain ⟨-, h10, h23, h32, -, -⟩ := k328r4g_inblock
  have h := (k328r4g_cross).1
  have e : k328r4g_T 1 2 =
      ⁅k328r4g_T 1 0, ⁅⁅k328r4g_T 0 2 * k328r4g_T 1 3, k328r4g_T 2 3⁆, k328r4g_T 3 2⁆⁆ := by
    decide +kernel
  rw [e]
  exact k328r4g_comm_mem h10 (k328r4g_comm_mem (k328r4g_comm_mem h h23) h32)

private theorem k328r4g_T34 : k328r4g_T 3 4 ∈ k328r4g_J := by
  obtain ⟨-, -, -, h32, h45, h54⟩ := k328r4g_inblock
  have h := (k328r4g_cross).2.1
  have e : k328r4g_T 3 4 =
      ⁅k328r4g_T 3 2, ⁅⁅k328r4g_T 2 4 * k328r4g_T 3 5, k328r4g_T 4 5⁆, k328r4g_T 5 4⁆⁆ := by
    decide +kernel
  rw [e]
  exact k328r4g_comm_mem h32 (k328r4g_comm_mem (k328r4g_comm_mem h h45) h54)

private theorem k328r4g_T50 : k328r4g_T 5 0 ∈ k328r4g_J := by
  obtain ⟨h01, h10, -, -, -, h54⟩ := k328r4g_inblock
  have h := (k328r4g_cross).2.2
  have e : k328r4g_T 5 0 =
      ⁅k328r4g_T 5 4, ⁅⁅k328r4g_T 4 0 * k328r4g_T 5 1, k328r4g_T 0 1⁆, k328r4g_T 1 0⁆⁆ := by
    decide +kernel
  rw [e]
  exact k328r4g_comm_mem h54 (k328r4g_comm_mem (k328r4g_comm_mem h h01) h10)

private theorem k328r4g_det (A : GL (Fin 6) (ZMod 2)) :
    (A : Matrix (Fin 6) (Fin 6) (ZMod 2)).det = 1 := by
  have hu : IsUnit (A : Matrix (Fin 6) (Fin 6) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
  rw [isUnit_iff_ne_zero] at hu
  revert hu
  generalize (A : Matrix (Fin 6) (Fin 6) (ZMod 2)).det = d
  revert d
  decide

private theorem k328r4g_top_of_cyclic (J : Subgroup (GL (Fin 6) (ZMod 2)))
    (hrot : ∀ i : Fin 6, i ≠ finRotate 6 i)
    (h : ∀ i : Fin 6, Matrix.GeneralLinearGroup.transvection i (finRotate 6 i) (hrot i) 1 ∈ J) :
    J = ⊤ := by
  have hdet : {A : GL (Fin 6) (ZMod 2) | (A : Matrix (Fin 6) (Fin 6) (ZMod 2)).det = 1} =
      Set.univ := Set.eq_univ_of_forall k328r4g_det
  have hcl := CFSG.ClassicalGroups.SpecialLinear.closure_cyclic_transvections_GL (m := 6)
    (by norm_num) (ZMod 2) hrot
  rw [hdet, Subgroup.closure_univ] at hcl
  refine top_unique ?_
  rw [← hcl]
  refine (Subgroup.closure_le J).2 ?_
  rintro _ ⟨i, c, rfl⟩
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide
  rcases hc with rfl | rfl
  · have : Matrix.GeneralLinearGroup.transvection i (finRotate 6 i) (hrot i) (0 : ZMod 2) = 1 :=
      Units.ext (by simp [Matrix.transvection])
    rw [this]
    exact J.one_mem
  · exact h i

private theorem k328r4g_gen_two : k328r4g_J = ⊤ := by
  refine k328r4g_top_of_cyclic _ (CFSG.ClassicalGroups.SpecialLinear.finRotate_ne_self
    (by norm_num)) fun i => ?_
  obtain ⟨h01, -, h23, -, h45, -⟩ := k328r4g_inblock
  fin_cases i
  · exact h01
  · exact k328r4g_T12
  · exact h23
  · exact k328r4g_T34
  · exact h45
  · exact k328r4g_T50

private theorem k328r4g_map_blockDiag3 {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) (A B C : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    ι.mapMatrix (blockDiag3 (ZMod 2) 6 A B C) =
      blockDiag3 F 6 (ι.mapMatrix A) (ι.mapMatrix B) (ι.mapMatrix C) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, blockDiag3, Matrix.of_apply]
  split_ifs <;> simp [Matrix.one_apply]

private theorem k328r4g_map_rho {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) : ι.mapMatrix (rhoOmega (ZMod 2)) = rhoOmega F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rhoOmega]

private theorem k328r4g_map_z {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) (z₀ : GL (Fin 6) F)
    (hz : (z₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F)) :
    Matrix.GeneralLinearGroup.map ι k328r4g_z = z₀ := by
  apply Units.ext
  rw [hz]
  show ι.mapMatrix (blockDiag3 (ZMod 2) 6 k328r4g_M k328r4g_M k328r4g_M) = _
  rw [k328r4g_map_blockDiag3, k328r4g_map_rho]

private theorem k328r4g_map_t {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) (t₀ : GL (Fin 6) F)
    (ht : (t₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F ^ 2) 1) :
    Matrix.GeneralLinearGroup.map ι k328r4g_t = t₀ := by
  apply Units.ext
  rw [ht]
  show ι.mapMatrix (blockDiag3 (ZMod 2) 6 k328r4g_M (k328r4g_M ^ 2) 1) = _
  rw [k328r4g_map_blockDiag3, map_pow, map_one, k328r4g_map_rho]

private theorem k328r4g_map_symm {F : Type} [Field F] (e : ZMod 2 ≃+* F) (g : GL (Fin 6) F) :
    Matrix.GeneralLinearGroup.map e.toRingHom
      (Matrix.GeneralLinearGroup.map e.symm.toRingHom g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
  exact e.apply_symm_apply _

private theorem k328r4g_map_cent {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (s : G)
    (s' : G') (hs : φ s = s') :
    (Subgroup.centralizer {s}).map φ ≤ Subgroup.centralizer {s'} := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← hs, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.1 hx]

theorem row4_gen (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) (z₀ t₀ : GL (Fin 6) F)
    (hz : (z₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (ht : (t₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F ^ 2) 1) :
    GenLeaf (StatedSL 6 F) z₀ t₀ := by
  have hcard : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card]; exact hF
  have hH : StatedSL 6 F = ⊤ := CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hcard 6
  let e : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hF
  let φ : GL (Fin 6) (ZMod 2) →* GL (Fin 6) F := Matrix.GeneralLinearGroup.map e.toRingHom
  let ψ : GL (Fin 6) F →* GL (Fin 6) (ZMod 2) := Matrix.GeneralLinearGroup.map e.symm.toRingHom
  have hφψ : ∀ g, φ (ψ g) = g := k328r4g_map_symm e
  have hφz : φ k328r4g_z = z₀ := k328r4g_map_z e.toRingHom z₀ hz
  have hφt : φ k328r4g_t = t₀ := k328r4g_map_t e.toRingHom t₀ ht
  have hle : k328r4g_J.map φ ≤ Subgroup.centralizer {z₀} ⊔ Subgroup.centralizer {t₀} ⊔
      Subgroup.centralizer {z₀ * t₀} ⊔ Subgroup.centralizer {z₀ * t₀ ^ 2} := by
    unfold k328r4g_J
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le_sup (sup_le_sup (sup_le_sup ?_ ?_) ?_) ?_
    · exact k328r4g_map_cent φ _ _ hφz
    · exact k328r4g_map_cent φ _ _ hφt
    · exact k328r4g_map_cent φ _ _ (by rw [map_mul, hφz, hφt])
    · exact k328r4g_map_cent φ _ _ (by rw [map_mul, map_pow, hφz, hφt])
  unfold GenLeaf
  simp only [hH, top_inf_eq]
  refine top_unique fun g _ => ?_
  have hg : ψ g ∈ k328r4g_J := by
    rw [k328r4g_gen_two]
    exact Subgroup.mem_top _
  have hmem := Subgroup.mem_map_of_mem φ hg
  rw [hφψ] at hmem
  exact hle hmem

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
