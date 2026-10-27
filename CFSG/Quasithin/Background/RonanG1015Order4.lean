module

public import CFSG.Quasithin.Background.G12Rad

public section

namespace CFSG.Quasithin

namespace RonanG1015

open CFSG.Quasithin.G11

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

@[expose] noncomputable def tv (f : LinearMap.BilinForm (ZMod 2) U) (u : U) : GLV U :=
  radE f u 0 1

section Tv

variable {f : LinearMap.BilinForm (ZMod 2) U}

theorem tv_apply (hf : IsSymplectic f) (u z : U) : tv f u z = z + f z u • u := by
  rw [tv, radE_zero_apply hf, one_mul]

theorem tv_mem_spSub (hf : IsSymplectic f) (u : U) : tv f u ∈ spSub f :=
  radE_mem_spSub hf (by simp)

theorem tv_mul_self (hf : IsSymplectic f) (u : U) : tv f u * tv f u = 1 :=
  radE_mul_self hf (by simp)

theorem tv_comm (hf : IsSymplectic f) {u w : U} (huw : f u w = 0) :
    tv f u * tv f w = tv f w * tv f u := by
  have hwu : f w u = 0 := by rw [hf.symm']; exact huw
  refine LinearEquiv.ext fun z => ?_
  simp only [LinearEquiv.mul_apply, tv_apply hf, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, huw, hwu, mul_zero, add_zero]
  abel

end Tv


section Path

variable {f : LinearMap.BilinForm (ZMod 2) U} {a b c : U}

theorem path_apply (hf : IsSymplectic f) (hab : f a b = 1) (hbc : f b c = 1) (hac : f a c = 0)
    (z : U) :
    (tv f a * tv f b * tv f c) z =
      z + (f z a + f z b + f z c) • a + (f z b + f z c) • b + f z c • c := by
  have hba : f b a = 1 := by rw [hf.symm']; exact hab
  have hcb : f c b = 1 := by rw [hf.symm']; exact hbc
  have hca : f c a = 0 := by rw [hf.symm']; exact hac
  simp only [LinearEquiv.mul_apply, tv_apply hf, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hf.1, hab, hbc, hac, hba, hcb, hca, mul_zero, mul_one,
    add_zero, zero_add]
  generalize f z a = p
  generalize f z b = r
  generalize f z c = s
  module

theorem path_coord (hf : IsSymplectic f) (hab : f a b = 1) (hbc : f b c = 1) (hac : f a c = 0)
    (z : U) :
    f ((tv f a * tv f b * tv f c) z) a = f z a + f z b + f z c ∧
      f ((tv f a * tv f b * tv f c) z) b = f z a ∧
      f ((tv f a * tv f b * tv f c) z) c = f z b := by
  have hba : f b a = 1 := by rw [hf.symm']; exact hab
  have hcb : f c b = 1 := by rw [hf.symm']; exact hbc
  have hca : f c a = 0 := by rw [hf.symm']; exact hac
  rw [path_apply hf hab hbc hac z]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hf.1, hab,
    hbc, hac, hba, hcb, hca, mul_zero, mul_one, add_zero, zero_add]
  generalize f z a = p
  generalize f z b = r
  generalize f z c = s
  refine ⟨?_, ?_, ?_⟩ <;> revert p r s <;> decide

theorem path_sq_apply (hf : IsSymplectic f) (hab : f a b = 1) (hbc : f b c = 1) (hac : f a c = 0)
    (z : U) :
    (tv f a * tv f b * tv f c) ((tv f a * tv f b * tv f c) z) =
      z + (f z a + f z b) • a + (f z a + f z c) • b + (f z b + f z c) • c := by
  obtain ⟨h1, h2, h3⟩ := path_coord hf hab hbc hac z
  rw [path_apply hf hab hbc hac ((tv f a * tv f b * tv f c) z), h1, h2, h3,
    path_apply hf hab hbc hac z]
  generalize f z a = p
  generalize f z b = r
  generalize f z c = s
  have key : ∀ p r s : ZMod 2, (p + r + s) + ((p + r + s) + p + r) = p + r ∧
      (r + s) + (p + r) = p + s ∧ s + r = r + s := by decide
  obtain ⟨k1, k2, k3⟩ := key p r s
  calc _ = z + ((p + r + s) + ((p + r + s) + p + r)) • a + ((r + s) + (p + r)) • b +
        (s + r) • c := by module
    _ = _ := by rw [k1, k2, k3]

theorem path_sq_coord (hf : IsSymplectic f) (hab : f a b = 1) (hbc : f b c = 1) (hac : f a c = 0)
    (z : U) :
    f ((tv f a * tv f b * tv f c) ((tv f a * tv f b * tv f c) z)) a = f z c ∧
      f ((tv f a * tv f b * tv f c) ((tv f a * tv f b * tv f c) z)) b = f z a + f z b + f z c ∧
      f ((tv f a * tv f b * tv f c) ((tv f a * tv f b * tv f c) z)) c = f z a := by
  obtain ⟨h1, h2, h3⟩ := path_coord hf hab hbc hac z
  obtain ⟨g1, g2, g3⟩ := path_coord hf hab hbc hac ((tv f a * tv f b * tv f c) z)
  refine ⟨?_, ?_, ?_⟩
  · rw [g1, h1, h2, h3]
    generalize f z a = p
    generalize f z b = r
    generalize f z c = s
    revert p r s
    decide
  · rw [g2, h1]
  · rw [g3, h2]

theorem path_pow_four (hf : IsSymplectic f) (hab : f a b = 1) (hbc : f b c = 1) (hac : f a c = 0) :
    (tv f a * tv f b * tv f c) ^ 4 = 1 := by
  set G := tv f a * tv f b * tv f c with hG
  refine LinearEquiv.ext fun z => ?_
  have e : G ^ 4 = G * G * (G * G) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [e]
  show G (G (G (G z))) = z
  obtain ⟨c1, c2, c3⟩ := path_sq_coord hf hab hbc hac z
  rw [path_sq_apply hf hab hbc hac (G (G z)), c1, c2, c3, path_sq_apply hf hab hbc hac z]
  generalize f z a = p
  generalize f z b = r
  generalize f z c = s
  have key : ∀ p r s : ZMod 2, ((p + r) + (s + (p + r + s))) = 0 ∧
      ((p + s) + (s + p)) = 0 ∧ ((r + s) + ((p + r + s) + p)) = 0 := by decide
  obtain ⟨k1, k2, k3⟩ := key p r s
  calc _ = z + ((p + r) + (s + (p + r + s))) • a + ((p + s) + (s + p)) • b +
        ((r + s) + ((p + r + s) + p)) • c := by module
    _ = z := by rw [k1, k2, k3]; simp

theorem path_sq_ne_one (hf : IsSymplectic f) (hab : f a b = 1) (hbc : f b c = 1)
    (hac : f a c = 0) (hne : a ≠ c) : (tv f a * tv f b * tv f c) ^ 2 ≠ 1 := by
  intro h
  have h1 := LinearEquiv.congr_fun h a
  rw [pow_two, LinearEquiv.mul_apply, LinearEquiv.coe_one, id,
    path_sq_apply hf hab hbc hac a] at h1
  have haa : f a a = 0 := hf.1 a
  have h3 : a + a = 0 := g12_vadd_self a
  simp only [haa, hab, hac, zero_add, add_zero, one_smul, zero_smul] at h1
  apply hne
  calc a = (a + a) + c := by rw [h1]
    _ = c := by rw [h3, zero_add]

end Path

section Extra

variable {f : LinearMap.BilinForm (ZMod 2) U} {a b c e : U}

theorem commute_path_extra (hf : IsSymplectic f) (hae : f a e = 0) (hbe : f b e = 0)
    (hce : f c e = 0) : Commute (tv f a * tv f b * tv f c) (tv f e) :=
  Commute.mul_left (Commute.mul_left (tv_comm hf hae) (tv_comm hf hbe)) (tv_comm hf hce)

theorem path_extra_pow_four (hf : IsSymplectic f) (hab : f a b = 1) (hbc : f b c = 1)
    (hac : f a c = 0) (hae : f a e = 0) (hbe : f b e = 0) (hce : f c e = 0) :
    (tv f a * tv f b * tv f c * tv f e) ^ 4 = 1 := by
  rw [(commute_path_extra hf hae hbe hce).mul_pow, path_pow_four hf hab hbc hac, one_mul,
    show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, tv_mul_self hf, one_mul]

theorem path_extra_sq_ne_one (hf : IsSymplectic f) (hab : f a b = 1) (hbc : f b c = 1)
    (hac : f a c = 0) (hne : a ≠ c) (hae : f a e = 0) (hbe : f b e = 0) (hce : f c e = 0) :
    (tv f a * tv f b * tv f c * tv f e) ^ 2 ≠ 1 := by
  rw [(commute_path_extra hf hae hbe hce).mul_pow, pow_two (tv f e), tv_mul_self hf, mul_one]
  exact path_sq_ne_one hf hab hbc hac hne

end Extra

end RonanG1015

end CFSG.Quasithin
