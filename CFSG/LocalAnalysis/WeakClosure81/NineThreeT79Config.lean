module

public import Mathlib.Algebra.Group.Conj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

structure Nine3Config {Y : Type} [Group Y] (c a e a' v : Y) : Prop where
  conj_a : IsConj c a
  conj_e : IsConj c e
  conj_a' : IsConj c a'
  conj_v : IsConj c v
  sq_a : a * a = 1
  sq_e : e * e = 1
  sq_a' : a' * a' = 1
  sq_v : v * v = 1
  ne_v : v ≠ 1
  pow_ae : (a * e) ^ 3 = 1
  pow_ea' : (e * a') ^ 3 = 1
  comm_aa' : a * a' = a' * a
  ne_aa' : a * a' ≠ 1
  comm_va : v * a = a * v
  comm_ve : v * e = e * v
  comm_va' : v * a' = a' * v

theorem Nine3Config.map {Y Y' : Type} [Group Y] [Group Y'] (f : Y ≃* Y') {c a e a' v : Y}
    (h : Nine3Config c a e a' v) : Nine3Config (f c) (f a) (f e) (f a') (f v) where
  conj_a := f.toMonoidHom.map_isConj h.conj_a
  conj_e := f.toMonoidHom.map_isConj h.conj_e
  conj_a' := f.toMonoidHom.map_isConj h.conj_a'
  conj_v := f.toMonoidHom.map_isConj h.conj_v
  sq_a := by rw [← map_mul, h.sq_a, map_one]
  sq_e := by rw [← map_mul, h.sq_e, map_one]
  sq_a' := by rw [← map_mul, h.sq_a', map_one]
  sq_v := by rw [← map_mul, h.sq_v, map_one]
  ne_v := fun hv => h.ne_v (f.injective (by rw [hv, map_one]))
  pow_ae := by rw [← map_mul, ← map_pow, h.pow_ae, map_one]
  pow_ea' := by rw [← map_mul, ← map_pow, h.pow_ea', map_one]
  comm_aa' := by rw [← map_mul, ← map_mul, h.comm_aa']
  ne_aa' := fun hh => h.ne_aa' (f.injective (by rw [map_mul, hh, map_one]))
  comm_va := by rw [← map_mul, ← map_mul, h.comm_va]
  comm_ve := by rw [← map_mul, ← map_mul, h.comm_ve]
  comm_va' := by rw [← map_mul, ← map_mul, h.comm_va']

end CFSG.LocalAnalysis.WeakClosure81
