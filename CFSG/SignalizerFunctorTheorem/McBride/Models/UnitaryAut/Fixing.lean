module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryAut.Core
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryAut.Model

public section

open CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Open Matrix

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryAut

open UnitaryHeisenberg

variable {p : ℕ}

theorem exists_std_frame (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ (ω : GaloisField 2 (2 * p)) (hω : ω ^ 3 = 1) (_ : ω ≠ 1)
      (O : GL (Fin 3) (GaloisField 2 (2 * p)))
      (ha : O * aGL hω * O⁻¹ ∈ SU3 hp.one_le) (hb : O * bGL * O⁻¹ ∈ SU3 hp.one_le),
      Nat.card ((Subgroup.closure {(⟨_, ha⟩ : SU3 hp.one_le), ⟨_, hb⟩}).map
        (proj hp.one_le)) = 9 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  set h := unitaryFieldData_galoisField hp.one_le with hh
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root h
  have hbar : h.bar ω * ω = 1 := bar_mul_self_eq_one h hodd hω3
  obtain ⟨O, hO⟩ := exists_frame h
  set J := antidiagGram (GaloisField 2 (2 * p)) with hJ
  have hOOi : (O : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) *
      ((O⁻¹ : GL (Fin 3) (GaloisField 2 (2 * p))) :
        Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconjmem : ∀ A : GL (Fin 3) (GaloisField 2 (2 * p)),
      (((A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))).map h.bar)ᵀ *
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) = 1) →
      (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))).det = 1 →
      O * A * O⁻¹ ∈ gramSU h J := by
    intro A hA hdet
    refine mem_gramSU.mpr ⟨?_, ?_⟩
    · simp only [Units.val_mul]
      exact unitary_conj h.bar J (O : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p)))
        ((O⁻¹ : GL (Fin 3) (GaloisField 2 (2 * p))) :
          Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p)))
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) hO hOOi hA
    · simp only [Units.val_mul, Matrix.det_mul]
      have := congrArg Matrix.det hOOi
      rw [Matrix.det_mul, Matrix.det_one] at this
      calc _ = (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))).det *
          ((O : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))).det *
          ((O⁻¹ : GL (Fin 3) (GaloisField 2 (2 * p))) :
            Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))).det) := by ring
        _ = _ := by rw [this, mul_one, hdet]
  have haMem : O * aGL hω3 * O⁻¹ ∈ gramSU h J :=
    hconjmem _ (by rw [coe_aGL]; exact aMat_unitary h.bar hbar)
      (by rw [coe_aGL]; exact det_aMat hω3)
  have hbMem : O * bGL * O⁻¹ ∈ gramSU h J :=
    hconjmem _ (by rw [coe_bGL]; exact bMat_unitary h.bar) (by rw [coe_bGL]; exact det_bMat)
  have hζMem : ζGL hω3 ∈ gramSU h J := by
    refine mem_gramSU.mpr ⟨?_, ?_⟩
    · rw [coe_ζGL]
      ext i j
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite h.bar]
      linear_combination J i j * hbar
    · rw [coe_ζGL, Matrix.det_smul]
      simpa using hω3
  have hpair := ((isHeisPair_GL hω3 hω1).conj O).subgroup (gramSU h J) haMem hbMem hζMem
  have hker : ∀ g : SU3 hp.one_le, proj hp.one_le g = 1 ↔
      g ∈ Subgroup.zpowers (⟨ζGL hω3, hζMem⟩ : SU3 hp.one_le) := by
    intro g
    have h1 : proj hp.one_le g = 1 ↔
        (g : GL (Fin 3) (GaloisField 2 (2 * p))) ∈
          Subgroup.center (GL (Fin 3) (GaloisField 2 (2 * p))) := by
      rw [Subtype.ext_iff, coe_proj, Subgroup.coe_one, ProjGenLinGroup.mk_eq_one]
    rw [h1]
    constructor
    · intro hg
      rw [GeneralLinearGroup.center_eq_range_scalar] at hg
      obtain ⟨u, hu⟩ := hg
      refine mem_zpowers_of_coe (mem_zpowers_ζGL_of_scalar hω3 hω1 (c := (u : _)) ?_
        (mem_gramSU.mp g.2).2)
      rw [← hu]
      simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    · intro hg
      have : (⟨ζGL hω3, hζMem⟩ : SU3 hp.one_le) ∈
          (Subgroup.center (GL (Fin 3) (GaloisField 2 (2 * p)))).comap (SU3 hp.one_le).subtype := by
        show ζGL hω3 ∈ Subgroup.center (GL (Fin 3) (GaloisField 2 (2 * p)))
        rw [GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨_, rfl⟩
      exact (Subgroup.zpowers_le.mpr this) hg
  refine ⟨ω, hω3, hω1, O, haMem, hbMem, ?_⟩
  rw [← hpair.E_eq_closure]
  exact hpair.card_map_E (proj hp.one_le) hker

theorem exists_conj_of_fixing_std (hp : p.Prime) (h5 : 5 ≤ p) {ω : GaloisField 2 (2 * p)}
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (O : GL (Fin 3) (GaloisField 2 (2 * p)))
    (ha : O * aGL hω * O⁻¹ ∈ SU3 hp.one_le) (hb : O * bGL * O⁻¹ ∈ SU3 hp.one_le)
    (g : MulAut (PSU3 2 p)) (hg : Nat.Coprime p (orderOf g))
    (hfix : ∀ x ∈ (Subgroup.closure {(⟨_, ha⟩ : SU3 hp.one_le), ⟨_, hb⟩}).map (proj hp.one_le),
      g x = x) :
    ∃ y ∈ (Subgroup.closure {(⟨_, ha⟩ : SU3 hp.one_le), ⟨_, hb⟩}).map (proj hp.one_le),
      g = MulAut.conj y := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  set a' : SU3 hp.one_le := ⟨O * aGL hω * O⁻¹, ha⟩ with ha'
  set b' : SU3 hp.one_le := ⟨O * bGL * O⁻¹, hb⟩ with hb'
  obtain ⟨σ, B, hσ, hrep⟩ := exists_rep hp g hg
  have hPa : proj hp.one_le a' ∈
      (Subgroup.closure {a', b'}).map (proj hp.one_le) :=
    Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp))
  have hPb : proj hp.one_le b' ∈
      (Subgroup.closure {a', b'}).map (proj hp.one_le) :=
    Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp))
  have hBa : ProjGenLinGroup.mk (B * glAut σ (O * aGL hω * O⁻¹) * B⁻¹) =
      ProjGenLinGroup.mk (O * aGL hω * O⁻¹) := by
    have := hrep a'
    rw [hfix _ hPa, coe_proj] at this
    exact this.symm
  have hBb : ProjGenLinGroup.mk (B * glAut σ (O * bGL * O⁻¹) * B⁻¹) =
      ProjGenLinGroup.mk (O * bGL * O⁻¹) := by
    have := hrep b'
    rw [hfix _ hPb, coe_proj] at this
    exact this.symm
  have hσω := fix_of_mk_eq hω hω1 O σ B hBa hBb
  have hσ1 : σ = 1 := by
    rcases ringEquiv_eq_refl_or_bar (unitaryFieldData_galoisField hp.one_le) hσ with h | h
    · exact h
    · exfalso
      rw [h ω] at hσω
      have h1 := bar_mul_self_eq_one (unitaryFieldData_galoisField hp.one_le) hodd hω
      rw [hσω] at h1
      exact hω1 (by
        calc ω = ω * (ω * ω) := by rw [h1, mul_one]
          _ = ω ^ 3 := by ring
          _ = 1 := hω)
  subst hσ1
  have hBa' : ProjGenLinGroup.mk (B * (O * aGL hω * O⁻¹) * B⁻¹) =
      ProjGenLinGroup.mk (O * aGL hω * O⁻¹) := by simpa using hBa
  have hBb' : ProjGenLinGroup.mk (B * (O * bGL * O⁻¹) * B⁻¹) =
      ProjGenLinGroup.mk (O * bGL * O⁻¹) := by simpa using hBb
  obtain ⟨e, he, μ, hBe⟩ := exists_mem_closure_of_mk_eq hω hω1 O B hBa' hBb'
  have hsub : ({O * aGL hω * O⁻¹, O * bGL * O⁻¹} : Set (GL (Fin 3) (GaloisField 2 (2 * p)))) ⊆
      (SU3 hp.one_le : Set (GL (Fin 3) (GaloisField 2 (2 * p)))) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have heS : e ∈ SU3 hp.one_le := (Subgroup.closure_le (SU3 hp.one_le)).mpr hsub he
  set e' : SU3 hp.one_le := ⟨e, heS⟩ with he'_def
  have hmap : (Subgroup.closure {a', b'}).map (SU3 hp.one_le).subtype =
      Subgroup.closure {O * aGL hω * O⁻¹, O * bGL * O⁻¹} := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have he' : e' ∈ Subgroup.closure {a', b'} := by
    have : e ∈ (Subgroup.closure {a', b'}).map (SU3 hp.one_le).subtype := hmap ▸ he
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp this
    have : s = e' := Subtype.ext hse
    rwa [← this]
  refine ⟨proj hp.one_le e', Subgroup.mem_map_of_mem _ he', ?_⟩
  ext z
  obtain ⟨w, rfl⟩ := proj_surjective hp.one_le z
  rw [hrep w, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_proj, coe_proj, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg ProjGenLinGroup.mk ?_
  have hs : GeneralLinearGroup.scalar (Fin 3) μ * (w : GL (Fin 3) (GaloisField 2 (2 * p))) *
      (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ = w := by
    rw [(commute_scalar_left μ w).eq, mul_inv_cancel_right]
  rw [map_one, MulAut.one_apply, hBe, _root_.mul_inv_rev]
  calc e * GeneralLinearGroup.scalar (Fin 3) μ * (w : GL (Fin 3) (GaloisField 2 (2 * p))) *
      ((GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ * e⁻¹)
      = e * (GeneralLinearGroup.scalar (Fin 3) μ * (w : GL (Fin 3) (GaloisField 2 (2 * p))) *
        (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹) * e⁻¹ := by group
    _ = _ := by rw [hs]

theorem exists_conj_of_fixing (hp : p.Prime) (h5 : 5 ≤ p) (P : Subgroup (PSU3 2 p))
    (hP : Nat.card P = 9) (g : MulAut (PSU3 2 p)) (hg : Nat.Coprime p (orderOf g))
    (hfix : ∀ x ∈ P, g x = x) : ∃ y ∈ P, g = MulAut.conj y := by
  obtain ⟨ω, hω, hω1, O, ha, hb, hcard⟩ := exists_std_frame hp h5
  obtain ⟨y, hy⟩ := exists_conj_of_card_nine hp h5 P _ hP hcard
  set g' : MulAut (PSU3 2 p) := (MulAut.conj y)⁻¹ * g * MulAut.conj y with hg'
  have hsemi : SemiconjBy (MulAut.conj y) g' g := by
    show MulAut.conj y * g' = g * MulAut.conj y
    rw [hg']
    group
  have hord : orderOf g' = orderOf g := hsemi.orderOf_eq
  have hfix' : ∀ x ∈ (Subgroup.closure {(⟨_, ha⟩ : SU3 hp.one_le), ⟨_, hb⟩}).map
      (proj hp.one_le), g' x = x := by
    intro x hx
    have hxP : MulAut.conj y x ∈ P := by
      rw [hy]
      exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hx
    have := hfix _ hxP
    rw [hg']
    simp only [MulAut.mul_apply, this, MulAut.inv_apply]
    simp [MulAut.conj_symm_apply, MulAut.conj_apply]
    group
  obtain ⟨z, hz, hgz⟩ := exists_conj_of_fixing_std hp h5 hω hω1 O ha hb g' (hord ▸ hg) hfix'
  refine ⟨y * z * y⁻¹, ?_, ?_⟩
  · rw [hy]
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
  · have : g = MulAut.conj y * g' * (MulAut.conj y)⁻¹ := by
      rw [hg']
      group
    rw [this, hgz, ← map_inv, ← map_mul, ← map_mul]

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryAut
