module

public import CFSG.Quasithin.H13.GoldschmidtU43DForm

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Swap

variable [Finite G] {z t w a : G} (s : Swap z t w) (ha : Good z t a)
include s ha

@[expose] noncomputable def Mcol (k : ↥(Subgroup.normalizer (Eg z t w a : Set G))) : Fin 4 → V4 :=
  fun i => Classical.choose (s.exists_crd ha
    ((Subgroup.mem_normalizer_iff.mp k.2 (gE z t w a i)).mp (by
      rw [← crd_idc (gE z t w a) i]
      exact crd_gE_mem (idc i))))

theorem Mcol_spec (k : ↥(Subgroup.normalizer (Eg z t w a : Set G))) (i : Fin 4) :
    (k : G) * gE z t w a i * (k : G)⁻¹ = crd (gE z t w a) (s.Mcol ha k i) :=
  Classical.choose_spec (s.exists_crd ha
    ((Subgroup.mem_normalizer_iff.mp k.2 (gE z t w a i)).mp (by
      rw [← crd_idc (gE z t w a) i]
      exact crd_gE_mem (idc i))))

theorem psi_conj (k : ↥(Subgroup.normalizer (Eg z t w a : Set G))) (c : V4) :
    (k : G) * crd (gE z t w a) c * (k : G)⁻¹ = crd (gE z t w a) (app (s.Mcol ha k) c) :=
  (s.comm4_gE ha).conj_crd (k : G) (s.Mcol ha k) (s.Mcol_spec ha k) c

theorem psi_inj {c c' : V4} (h : crd (gE z t w a) c = crd (gE z t w a) c') : c = c' :=
  (s.comm4_gE ha).crd_injective (fun _ hc => s.crd_gE_indep ha hc) h

@[expose] noncomputable def Mat (k : ↥(Subgroup.normalizer (Eg z t w a : Set G))) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => s.Mcol ha k j i

theorem mulVec_Mat (k : ↥(Subgroup.normalizer (Eg z t w a : Set G))) (c : V4) :
    (s.Mat ha k).mulVec c = app (s.Mcol ha k) c := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Mat, Matrix.of_apply, app,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem Mcol_mul (k k' : ↥(Subgroup.normalizer (Eg z t w a : Set G))) (j : Fin 4) :
    s.Mcol ha (k * k') j = app (s.Mcol ha k) (s.Mcol ha k' j) := by
  apply s.psi_inj ha
  rw [← s.Mcol_spec ha, ← s.psi_conj ha, ← s.Mcol_spec ha]
  simp only [Subgroup.coe_mul]
  group

theorem Mat_mul (k k' : ↥(Subgroup.normalizer (Eg z t w a : Set G))) :
    s.Mat ha (k * k') = s.Mat ha k * s.Mat ha k' := by
  ext i j
  simp only [Mat, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four, s.Mcol_mul ha k k' j, app,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem Mcol_one (j : Fin 4) :
    s.Mcol ha (1 : ↥(Subgroup.normalizer (Eg z t w a : Set G))) j = idc j := by
  apply s.psi_inj ha
  rw [← s.Mcol_spec ha, crd_idc]
  simp

theorem Mat_one : s.Mat ha (1 : ↥(Subgroup.normalizer (Eg z t w a : Set G))) = 1 := by
  ext i j
  simp only [Mat, Matrix.of_apply, s.Mcol_one ha j, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [idc]

@[expose] noncomputable def rho :
    ↥(Subgroup.normalizer (Eg z t w a : Set G)) →* GL (Fin 4) (ZMod 2) where
  toFun k := ⟨s.Mat ha k, s.Mat ha k⁻¹, by rw [← s.Mat_mul ha, mul_inv_cancel, s.Mat_one ha],
    by rw [← s.Mat_mul ha, inv_mul_cancel, s.Mat_one ha]⟩
  map_one' := Units.ext (s.Mat_one ha)
  map_mul' k k' := Units.ext (s.Mat_mul ha k k')

theorem coe_rho (k : ↥(Subgroup.normalizer (Eg z t w a : Set G))) :
    ((s.rho ha k : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = s.Mat ha k := rfl

theorem rho_eq_one_iff (k : ↥(Subgroup.normalizer (Eg z t w a : Set G))) :
    s.rho ha k = 1 ↔ (k : G) ∈ Eg z t w a := by
  constructor
  · intro h1
    have hM : s.Mat ha k = 1 := by
      have := congrArg (fun g : GL (Fin 4) (ZMod 2) => (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) h1
      simpa [coe_rho] using this
    have hid : ∀ c, app (s.Mcol ha k) c = c := fun c => by
      rw [← s.mulVec_Mat ha, hM, Matrix.one_mulVec]
    have hcent : (k : G) ∈ Subgroup.centralizer (Eg z t w a : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨c, rfl⟩ := s.exists_crd ha hy
      have h2 := s.psi_conj ha k c
      rw [hid c] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    rw [s.centralizer_E ha] at hcent
    exact hcent
  · intro hk
    have hcol : ∀ j, s.Mcol ha k j = idc j := by
      intro j
      apply s.psi_inj ha
      rw [← s.Mcol_spec ha, crd_idc]
      have hgj : gE z t w a j ∈ Eg z t w a := by
        rw [← crd_idc (gE z t w a) j]
        exact crd_gE_mem (idc j)
      have hc := (s.Eg_comm_sq ha hk hgj).1
      calc (k : G) * gE z t w a j * (k : G)⁻¹ = (gE z t w a j * k) * (k : G)⁻¹ := by rw [hc]
        _ = gE z t w a j := by group
    have hM : s.Mat ha k = 1 := by
      ext i j
      simp only [Mat, Matrix.of_apply, hcol j, Matrix.one_apply]
      fin_cases i <;> fin_cases j <;> simp [idc]
    exact Units.ext hM

theorem Fv_rho (k : ↥(Subgroup.normalizer (Eg z t w a : Set G))) (c d : V4) :
    Fv z t w a ((s.Mat ha k).mulVec c) ((s.Mat ha k).mulVec d) = Fv z t w a c d := by
  rw [s.mulVec_Mat ha, s.mulVec_Mat ha]
  exact s.Fv_conj_inv ha (s.Mcol ha k) (fun c => s.psi_conj ha k c) c d

end Swap

end CFSG.Quasithin.H13.U43
