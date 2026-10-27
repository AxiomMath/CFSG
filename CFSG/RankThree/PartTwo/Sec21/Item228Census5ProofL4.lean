module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofOdd
public import CFSG.RankThree.PartTwo.Sec21.Item228Census5ProofGL4
public import CFSG.RankThree.PartTwo.Sec21.Item228Census5ProofSL4
import CFSG.ClassicalInvolution.SL2Facts
import CFSG.Adapters.RankTwoModelTransports
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projSL projImage)

namespace Item228Census5Proof

open Item228Census3Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem isCentData_map_equiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (E : GL ι K ≃* GL κ K) {G : Subgroup (GL ι K)} {G' : Subgroup (GL κ K)}
    (hG : ∀ g, g ∈ G ↔ E g ∈ G') {A : GL ι K} {X : Type*} [Group X] {φ : X →* GL ι K}
    (h : IsCentData G A φ) : IsCentData G' (E A) ((E : GL ι K →* GL κ K).comp φ) := by
  obtain ⟨hmem, hcomm, hcom⟩ := h
  refine ⟨fun x => (hG _).mp (hmem x), fun x => ?_, fun g hg k hk hgA hkA => ?_⟩
  · change E (φ x) * E A = E A * E (φ x)
    rw [← map_mul, ← map_mul, hcomm x]
  · have hg' : E.symm g ∈ G := (hG _).mpr (by rwa [MulEquiv.apply_symm_apply])
    have hk' : E.symm k ∈ G := (hG _).mpr (by rwa [MulEquiv.apply_symm_apply])
    have hgA' : E.symm g * A = A * E.symm g := by
      apply E.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hgA]
    have hkA' : E.symm k * A = A * E.symm k := by
      apply E.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hkA]
    obtain ⟨x, hx⟩ := hcom _ hg' _ hk' hgA' hkA'
    refine ⟨x, ?_⟩
    change E (φ x) = _
    rw [hx, map_mul, map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]

theorem det_reindexV₄ (g : GL V₄ K) :
    GeneralLinearGroup.det (reindexV₄ K g) = GeneralLinearGroup.det g := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, coe_reindexV₄,
    Matrix.det_reindex_self]

theorem reindexV₄_scalar (u : Kˣ) :
    reindexV₄ K (GeneralLinearGroup.scalar V₄ u) = GeneralLinearGroup.scalar (Fin 4) u := by
  apply Units.ext
  rw [coe_reindexV₄, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.reindex_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem ker_mk_reindexV₄ {X : Type*} [Group X] (φ : X →* GL V₄ K) :
    (ProjGenLinGroup.mk.comp (((reindexV₄ K) : GL V₄ K →* GL (Fin 4) K).comp φ)).ker =
      (ProjGenLinGroup.mk.comp φ).ker := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range, MonoidHom.coe_ofClass]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (reindexV₄ K).injective (by rw [reindexV₄_scalar]; exact hu)⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [← hu, reindexV₄_scalar]⟩

theorem pow_four_eq_one_of_scalar_mem_ker {u : Kˣ}
    (hu : GeneralLinearGroup.scalar (Fin 4) u ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker) :
    u ^ 4 = 1 := by
  have h := congrArg Units.val (MonoidHom.mem_ker.mp hu)
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Units.val_one] at h
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)

end Item228Census5Proof

open Item228Census3Proof Item228Census5Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem l4OddCentThree_holds : L4OddCentThree := by
  intro p _ hp hp2 y hy
  have hp' : p.Prime := Fact.out
  set K := GaloisField p 1
  have hKc : Nat.card K = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have hq : Nat.card K % 3 = 2 := by rw [hKc]; exact hp2
  have hK : ∀ s : K, s * s + s + 1 ≠ 0 := no_root_of_card_mod_three hq
  have h3 : (3 : K) ≠ 0 := by
    have h := hK 1
    norm_num at h
    exact h
  set G := (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker with hG
  have hZ4 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈ G → u ^ 4 = 1 :=
    fun u hu => pow_four_eq_one_of_scalar_mem_ker hu
  have hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈ G → u ^ 3 = 1 → u = 1 :=
    fun u hu h3' => by
      calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
        _ = 1 := by rw [hZ4 u hu, h3', inv_one, one_mul]
  obtain ⟨A, hAy, hA3, hA1⟩ := exists_lift_cube G hZ4 y hy
  set A' : GL V₄ K := (reindexV₄ K).symm (A : GL (Fin 4) K) with hA'
  have hA'3 : A' ^ 3 = 1 := by
    rw [hA', ← map_pow, ← Subgroup.coe_pow, hA3, Subgroup.coe_one, map_one]
  have hA'1 : A' ≠ 1 := fun h => hA1 (Subtype.ext (by
    have e := congrArg (reindexV₄ K) h
    rwa [hA', MulEquiv.apply_symm_apply, map_one] at e))
  have hGmap : ∀ g : GL V₄ K, g ∈ (GeneralLinearGroup.det : GL V₄ K →* Kˣ).ker ↔
      reindexV₄ K g ∈ G := fun g => by
    rw [hG, MonoidHom.mem_ker, MonoidHom.mem_ker, det_reindexV₄]
  have hRA : reindexV₄ K A' = (A : GL (Fin 4) K) := MulEquiv.apply_symm_apply _ _
  obtain ⟨P, hD | hD⟩ := exists_normal_form_GL4 hK hq hA'3 hA'1
  ·
    left
    have hφ := isCentData_map_equiv (reindexV₄ K) hGmap
      ((isCentData_det_plane h3 det_cubeMat cubeMat_sq_add hD).conj (mem_ker_det_conj_iff P) rfl)
    rw [hRA] at hφ
    have hker : (ProjGenLinGroup.mk.comp (((reindexV₄ K) : GL V₄ K →* GL (Fin 4) K).comp
        ((MulAut.conj P⁻¹).toMonoidHom.comp iotaPlane))).ker = ⊥ := by
      rw [ker_mk_reindexV₄, ker_mk_conj, ker_mk_iotaPlane]
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
      CFSG.ClassicalInvolution.sl2_isPerfect (by rw [hKc]; omega)
    obtain ⟨e⟩ := nonempty_perfectResidual_equiv_of_ker_bot G A hA3 hZ3 _ hφ hker
    rw [hAy] at e
    exact ⟨e⟩
  ·
    right
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
    have hφ := isCentData_map_equiv (reindexV₄ K) hGmap
      ((isCentData_det_cube hD).conj (mem_ker_det_conj_iff P) rfl)
    rw [hRA] at hφ
    have hker : (ProjGenLinGroup.mk.comp (((reindexV₄ K) : GL V₄ K →* GL (Fin 4) K).comp
        ((MulAut.conj P⁻¹).toMonoidHom.comp iotaCube))).ker =
          Subgroup.center (SpecialLinearGroup (Fin 2) (cubeAlg K)) := by
      rw [ker_mk_reindexV₄, ker_mk_conj, ker_mk_iotaCube hK]
    obtain ⟨e⟩ := nonempty_perfectResidual_equiv_projSL G A hA3 hZ3 _ hφ hker e2
    rw [hAy] at e
    exact ⟨e⟩

theorem census228L4Odd_holds : Census228L4Odd :=
  census228L4Odd_of l4OddCentThree_holds

end CFSG.RankThree.PartTwo.Sec21
