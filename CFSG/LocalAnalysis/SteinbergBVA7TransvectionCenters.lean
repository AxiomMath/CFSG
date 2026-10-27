module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SteinbergBQRankOneChainIrreducible
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

namespace BinaryTransvection

theorem add_self_eq_zero (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem zmodTwo_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a
  decide

theorem zmodTwo_eq_zero_of_ne_one {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  revert a
  decide

theorem exists_eq_one_of_ne_zero {f : Dual (ZMod 2) V} (hf : f ≠ 0) : ∃ x, f x = 1 := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.1 hf
  exact ⟨x, zmodTwo_eq_one_of_ne_zero hx⟩

theorem id_add_smulRight_mul {u : V} {f g : Dual (ZMod 2) V} (hf : f u = 0) :
    (LinearMap.id + f.smulRight u) * (LinearMap.id + g.smulRight u) =
      (LinearMap.id + (f + g).smulRight u : Module.End (ZMod 2) V) := by
  ext x
  have h1 : f (x + g x • u) = f x := by rw [map_add, map_smul, hf, smul_zero, add_zero]
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, h1, add_smul]
  abel

theorem id_add_smulRight_mul_same {x y : V} {h : Dual (ZMod 2) V} (hy : h y = 0) :
    (LinearMap.id + h.smulRight x) * (LinearMap.id + h.smulRight y) =
      (LinearMap.id + h.smulRight (x + y) : Module.End (ZMod 2) V) := by
  ext z
  have h1 : h (z + h z • y) = h z := by rw [map_add, map_smul, hy, smul_zero, add_zero]
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, h1, smul_add]
  abel

theorem conj_id_add_smulRight (a : LinearMap.GeneralLinearGroup (ZMod 2) V) (u : V)
    (f : Dual (ZMod 2) V) :
    (a : Module.End (ZMod 2) V) * (LinearMap.id + f.smulRight u) *
        ((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) =
      LinearMap.id + (f.comp ((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        Module.End (ZMod 2) V)).smulRight ((a : Module.End (ZMod 2) V) u) := by
  ext x
  have h1 : (a : Module.End (ZMod 2) V)
      (((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) x) = x := by
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, map_add, map_smul, h1, LinearMap.comp_apply]

theorem eq_of_id_add_smulRight_eq {u v : V} {f g : Dual (ZMod 2) V} (hu : u ≠ 0) (hf : f ≠ 0)
    (h : (LinearMap.id + f.smulRight u : Module.End (ZMod 2) V) = LinearMap.id + g.smulRight v) :
    u = v ∧ f = g := by
  have h' : f.smulRight u = g.smulRight v := add_left_cancel h
  obtain ⟨x, hx⟩ := exists_eq_one_of_ne_zero hf
  have hux : u = g x • v := by
    have := LinearMap.congr_fun h' x
    rwa [LinearMap.smulRight_apply, LinearMap.smulRight_apply, hx, one_smul] at this
  have hgx : g x = 1 := by
    by_contra hg
    rw [zmodTwo_eq_zero_of_ne_one hg, zero_smul] at hux
    exact hu hux
  rw [hgx, one_smul] at hux
  subst hux
  refine ⟨rfl, LinearMap.ext fun y => smul_left_injective (ZMod 2) hu ?_⟩
  have := LinearMap.congr_fun h' y
  rwa [LinearMap.smulRight_apply, LinearMap.smulRight_apply] at this

theorem finrank_range_smulRight [FiniteDimensional (ZMod 2) V] {u : V} {f : Dual (ZMod 2) V}
    (hu : u ≠ 0) (hf : f ≠ 0) : finrank (ZMod 2) (LinearMap.range (f.smulRight u)) = 1 := by
  have hrange : LinearMap.range (f.smulRight u) = Submodule.span (ZMod 2) {u} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨x, hx⟩ := exists_eq_one_of_ne_zero hf
      exact ⟨x, by rw [LinearMap.smulRight_apply, hx, one_smul]⟩
  rw [hrange, finrank_span_singleton hu]

end BinaryTransvection

open BinaryTransvection

@[expose] def IsBinaryTransvection (n : LinearMap.GeneralLinearGroup (ZMod 2) V) : Prop :=
  ∃ (u : V) (f : Dual (ZMod 2) V), u ≠ 0 ∧ f ≠ 0 ∧ f u = 0 ∧
    (n : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u

@[expose] def centerFunctionals (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) (u : V) :
    Submodule (ZMod 2) (Dual (ZMod 2) V) where
  carrier := {f | f u = 0 ∧ ∃ n ∈ N, (n : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u}
  add_mem' := by
    rintro f g ⟨hf, n, hn, hnf⟩ ⟨hg, m, hm, hmg⟩
    refine ⟨by rw [LinearMap.add_apply, hf, hg, add_zero], n * m, mul_mem hn hm, ?_⟩
    rw [Units.val_mul, hnf, hmg, id_add_smulRight_mul hf]
  zero_mem' := ⟨rfl, 1, one_mem _, by ext x; simp⟩
  smul_mem' := by
    rintro c f ⟨hf, n, hn, hnf⟩
    obtain rfl | rfl : c = 0 ∨ c = 1 := by revert c; decide
    · exact ⟨by simp, 1, one_mem _, by ext x; simp⟩
    · exact ⟨by simpa using hf, n, hn, by simpa using hnf⟩

@[expose] def transvectionCenters (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) :
    Set V :=
  {u | u ≠ 0 ∧ centerFunctionals N u ≠ ⊥}

namespace BinaryTransvection

variable {N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}

theorem mem_centerFunctionals {u : V} {f : Dual (ZMod 2) V} :
    f ∈ centerFunctionals N u ↔
      f u = 0 ∧ ∃ n ∈ N, (n : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u :=
  Iff.rfl

theorem mul_self_of_val_eq {n : LinearMap.GeneralLinearGroup (ZMod 2) V} {u : V}
    {f : Dual (ZMod 2) V} (hfu : f u = 0)
    (hn : (n : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u) : n * n = 1 := by
  apply Units.ext
  rw [Units.val_mul, hn, id_add_smulRight_mul hfu, add_self_eq_zero, LinearMap.zero_smulRight,
    add_zero, Units.val_one]
  rfl

theorem inv_eq_of_val_eq {n : LinearMap.GeneralLinearGroup (ZMod 2) V} {u : V}
    {f : Dual (ZMod 2) V} (hfu : f u = 0)
    (hn : (n : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u) : n⁻¹ = n :=
  inv_eq_of_mul_eq_one_right (mul_self_of_val_eq hfu hn)

theorem finrank_centerFunctionals_le [FiniteDimensional (ZMod 2) V]
    {a : LinearMap.GeneralLinearGroup (ZMod 2) V} (ha : a ∈ N) (u : V) :
    finrank (ZMod 2) (centerFunctionals N ((a : Module.End (ZMod 2) V) u)) ≤
      finrank (ZMod 2) (centerFunctionals N u) := by
  set A := (a : Module.End (ZMod 2) V)
  set A' := ((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V)
  have hA'A : ∀ x, A' (A x) = x := fun x => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hAA' : ∀ x, A (A' x) = x := fun x => by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have hmaps : ∀ k ∈ centerFunctionals N (A u), A.dualMap k ∈ centerFunctionals N u := by
    rintro k ⟨hk, n, hn, hnk⟩
    refine ⟨by rw [LinearMap.dualMap_apply]; exact hk, a⁻¹ * n * a, ?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem ha) hn) ha
    · have h1 := conj_id_add_smulRight a⁻¹ (A u) k
      rw [inv_inv] at h1
      rw [Units.val_mul, Units.val_mul, hnk, h1, hA'A]
      ext x
      simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        LinearMap.comp_apply, LinearMap.dualMap_apply]
      rfl
  have hinj : Function.Injective ((A.dualMap).restrict hmaps) := by
    intro k k' hkk'
    apply Subtype.ext
    ext x
    have := congrArg (fun φ : centerFunctionals N u => (φ : Dual (ZMod 2) V) (A' x)) hkk'
    simpa [LinearMap.dualMap_apply, hAA'] using this
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem finrank_centerFunctionals_eq [FiniteDimensional (ZMod 2) V]
    {a : LinearMap.GeneralLinearGroup (ZMod 2) V} (ha : a ∈ N) (u : V) :
    finrank (ZMod 2) (centerFunctionals N ((a : Module.End (ZMod 2) V) u)) =
      finrank (ZMod 2) (centerFunctionals N u) := by
  refine le_antisymm (finrank_centerFunctionals_le ha u) ?_
  have h := finrank_centerFunctionals_le (inv_mem ha) ((a : Module.End (ZMod 2) V) u)
  rwa [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply] at h

theorem mem_transvectionCenters {u : V} :
    u ∈ transvectionCenters N ↔ u ≠ 0 ∧ centerFunctionals N u ≠ ⊥ :=
  Iff.rfl

theorem exists_mem_apply_eq_of_incidence {x y : V} {f g : Dual (ZMod 2) V}
    (hf : f ∈ centerFunctionals N x) (hfy : f y = 1) (hg : g ∈ centerFunctionals N y)
    (hgx : g x = 1) : ∃ a ∈ N, (a : Module.End (ZMod 2) V) x = y := by
  obtain ⟨hfx, n, hn, hnf⟩ := mem_centerFunctionals.1 hf
  obtain ⟨-, m, hm, hmg⟩ := mem_centerFunctionals.1 hg
  refine ⟨n * m, mul_mem hn hm, ?_⟩
  have h1 : (LinearMap.id + g.smulRight y : Module.End (ZMod 2) V) x = x + y := by
    rw [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, hgx, one_smul]
  have h2 : (LinearMap.id + f.smulRight x : Module.End (ZMod 2) V) (x + y) = y := by
    rw [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_add, hfx, hfy,
      zero_add, one_smul, add_comm x y, add_assoc, add_self_eq_zero, add_zero]
  rw [Units.val_mul, Module.End.mul_apply, hnf, hmg, h1, h2]

theorem le_of_one_way {x y : V} {f : Dual (ZMod 2) V} (hf : f ∈ centerFunctionals N x)
    (hfy : f y = 1) (hyx : ∀ g ∈ centerFunctionals N y, g x = 0) :
    centerFunctionals N y ≤ centerFunctionals N x := by
  intro g hg
  have hgx := hyx g hg
  obtain ⟨hfx, n, hn, hnf⟩ := mem_centerFunctionals.1 hf
  obtain ⟨hgy, m, hm, hmg⟩ := mem_centerFunctionals.1 hg
  have hm' : ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) =
      LinearMap.id + g.smulRight y := by
    rw [inv_eq_of_val_eq hgy hmg, hmg]
  have hcomp : f.comp ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      Module.End (ZMod 2) V) = f + g := by
    rw [hm']
    ext z
    simp [hfy]
  have hmx : (m : Module.End (ZMod 2) V) x = x := by
    rw [hmg]
    simp [hgx]
  have hfg : f + g ∈ centerFunctionals N x := by
    refine mem_centerFunctionals.2 ⟨by rw [LinearMap.add_apply, hfx, hgx, add_zero],
      m * n * m⁻¹, mul_mem (mul_mem hm hn) (inv_mem hm), ?_⟩
    rw [Units.val_mul, Units.val_mul, hnf, conj_id_add_smulRight, hcomp, hmx]
  have := (centerFunctionals N x).sub_mem hfg hf
  rwa [add_sub_cancel_left] at this

theorem finrank_lt_of_one_way [FiniteDimensional (ZMod 2) V] {x y : V} {f : Dual (ZMod 2) V}
    (hf : f ∈ centerFunctionals N x) (hfy : f y = 1)
    (hyx : ∀ g ∈ centerFunctionals N y, g x = 0) :
    finrank (ZMod 2) (centerFunctionals N y) < finrank (ZMod 2) (centerFunctionals N x) := by
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (le_of_one_way hf hfy hyx) ?_)
  intro h
  have hf' : f ∈ centerFunctionals N y := by
    rw [h]
    exact hf
  have hfy' := (mem_centerFunctionals.1 hf').1
  rw [hfy] at hfy'
  exact one_ne_zero hfy'

theorem finrank_le_of_incidence [FiniteDimensional (ZMod 2) V] {x y : V} {f : Dual (ZMod 2) V}
    (hf : f ∈ centerFunctionals N x) (hfy : f y = 1) :
    finrank (ZMod 2) (centerFunctionals N y) ≤ finrank (ZMod 2) (centerFunctionals N x) := by
  by_cases h : ∃ g ∈ centerFunctionals N y, g x = 1
  · obtain ⟨g, hg, hgx⟩ := h
    obtain ⟨a, ha, hax⟩ := exists_mem_apply_eq_of_incidence hf hfy hg hgx
    rw [← hax, finrank_centerFunctionals_eq ha]
  · push Not at h
    exact (finrank_lt_of_one_way hf hfy fun g hg => zmodTwo_eq_zero_of_ne_one (h g hg)).le

theorem mem_of_incidence {x y : V} {g h : Dual (ZMod 2) V} (hg : g ∈ centerFunctionals N y)
    (hgx : g x = 1) (hh : h ∈ centerFunctionals N x) (hhy : h y = 0) :
    h ∈ centerFunctionals N y := by
  obtain ⟨hgy, m, hm, hmg⟩ := mem_centerFunctionals.1 hg
  obtain ⟨hhx, n, hn, hnh⟩ := mem_centerFunctionals.1 hh
  refine mem_centerFunctionals.2 ⟨hhy, m * n * m⁻¹ * n⁻¹,
    mul_mem (mul_mem (mul_mem hm hn) (inv_mem hm)) (inv_mem hn), ?_⟩
  have hm' : ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) =
      LinearMap.id + g.smulRight y := by
    rw [inv_eq_of_val_eq hgy hmg, hmg]
  have hn' : ((n⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) =
      LinearMap.id + h.smulRight x := by
    rw [inv_eq_of_val_eq hhx hnh, hnh]
  have hcomp : h.comp ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      Module.End (ZMod 2) V) = h := by
    rw [hm']
    ext z
    simp [hhy]
  have hmx : (m : Module.End (ZMod 2) V) x = x + y := by
    rw [hmg]
    simp [hgx]
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hnh, conj_id_add_smulRight, hcomp, hmx, hn',
    id_add_smulRight_mul_same hhx, add_comm x y, add_assoc, add_self_eq_zero, add_zero]

theorem finrank_inf_ker_eval [FiniteDimensional (ZMod 2) V] {u w : V} {f : Dual (ZMod 2) V}
    (hf : f ∈ centerFunctionals N u) (hfw : f w = 1) :
    finrank (ZMod 2) ↥(centerFunctionals N u ⊓ LinearMap.ker (Dual.eval (ZMod 2) V w)) =
      finrank (ZMod 2) (centerFunctionals N u) - 1 := by
  have hsurj : Function.Surjective (Dual.eval (ZMod 2) V w) := fun c =>
    ⟨c • f, by rw [map_smul, Dual.eval_apply, hfw, smul_eq_mul, mul_one]⟩
  have hK := LinearMap.finrank_range_add_finrank_ker (Dual.eval (ZMod 2) V w)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at hK
  set K := LinearMap.ker (Dual.eval (ZMod 2) V w)
  have hsup : centerFunctionals N u ⊔ K = ⊤ := by
    refine eq_top_iff.2 fun φ _ => ?_
    have hφ : φ - φ w • f ∈ K := by
      rw [LinearMap.mem_ker, Dual.eval_apply, LinearMap.sub_apply, LinearMap.smul_apply, hfw,
        smul_eq_mul, mul_one, sub_self]
    have := Submodule.add_mem_sup (Submodule.smul_mem _ (φ w) hf) hφ
    rwa [add_sub_cancel] at this
  have h := Submodule.finrank_sup_add_finrank_inf_eq (centerFunctionals N u) K
  rw [hsup, finrank_top] at h
  omega

end BinaryTransvection

open BinaryTransvection in
theorem binary_transvection_center_reciprocity [FiniteDimensional (ZMod 2) V]
    (hV : 2 ≤ finrank (ZMod 2) V) (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure {n | n ∈ N ∧ IsBinaryTransvection n}) :
    (∀ u : V, (centerFunctionals N u : Set (Dual (ZMod 2) V)) =
        {f | f u = 0 ∧ ∃ n ∈ N, (n : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u}) ∧
      Submodule.span (ZMod 2) (transvectionCenters N) = ⊤ ∧
      (∀ u ∈ transvectionCenters N, ∀ v ∈ transvectionCenters N,
        ∃ n ∈ N, (n : Module.End (ZMod 2) V) u = v) ∧
      (∀ u ∈ transvectionCenters N, ∀ v ∈ transvectionCenters N, u ≠ v →
        ((∃ f ∈ centerFunctionals N u, f v = 1) ↔ ∃ g ∈ centerFunctionals N v, g u = 1)) ∧
      ∃ r : ℕ, 0 < r ∧
        (∀ u ∈ transvectionCenters N, finrank (ZMod 2) (centerFunctionals N u) = r) ∧
        ∀ u ∈ transvectionCenters N, ∀ v ∈ transvectionCenters N,
          (∃ f ∈ centerFunctionals N u, f v = 1) →
            centerFunctionals N u ⊓ LinearMap.ker (Dual.eval (ZMod 2) V v) =
                centerFunctionals N v ⊓ LinearMap.ker (Dual.eval (ZMod 2) V u) ∧
              finrank (ZMod 2)
                ↥(centerFunctionals N u ⊓ LinearMap.ker (Dual.eval (ZMod 2) V v)) = r - 1 := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) := Finite.of_injective
    (fun u : LinearMap.GeneralLinearGroup (ZMod 2) V => (u : Module.End (ZMod 2) V))
    Units.val_injective
  set T : Set (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    {n | n ∈ N ∧ IsBinaryTransvection n} with hT
  have hTfin : T.Finite := Set.toFinite T
  set D := hTfin.toFinset with hD
  have hDT : (D : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) = T := hTfin.coe_toFinset
  have hmemD : ∀ t, t ∈ D ↔ t ∈ N ∧ IsBinaryTransvection t := fun t => hTfin.mem_toFinset
  have hdata : ∀ t : LinearMap.GeneralLinearGroup (ZMod 2) V, ∃ (u : V) (f : Dual (ZMod 2) V),
      IsBinaryTransvection t → u ≠ 0 ∧ f ≠ 0 ∧ f u = 0 ∧
        (t : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u := by
    intro t
    by_cases ht : IsBinaryTransvection t
    · obtain ⟨u, f, hu, hf, hfu, htuf⟩ := ht
      exact ⟨u, f, fun _ => ⟨hu, hf, hfu, htuf⟩⟩
    · exact ⟨0, 0, fun h => absurd h ht⟩
  choose v φ hP using hdata
  have hPD : ∀ t ∈ D, v t ≠ 0 ∧ φ t ≠ 0 ∧ φ t (v t) = 0 ∧
      (t : Module.End (ZMod 2) V) = LinearMap.id + (φ t).smulRight (v t) :=
    fun t ht => hP t ((hmemD t).1 ht).2
  have hDne : D.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hN : N = ⊥ := by
      rw [hgen, ← hDT, hne, Finset.coe_empty, Subgroup.closure_empty]
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    rcases hirr (Submodule.span (ZMod 2) {x}) (fun n hn u hu => by
        rw [hN, Subgroup.mem_bot] at hn
        rw [hn]
        exact hu) with h | h
    · exact hx (Submodule.span_singleton_eq_bot.1 h)
    · have := finrank_span_singleton (K := ZMod 2) hx
      rw [h, finrank_top] at this
      omega
  have hrank : ∀ t ∈ D,
      finrank (ZMod 2) (LinearMap.range ((t : V →ₗ[ZMod 2] V) - 1)) = 1 := by
    intro t ht
    obtain ⟨hvt, hφt, -, htv⟩ := hPD t ht
    rw [htv, show (1 : Module.End (ZMod 2) V) = LinearMap.id from rfl, add_sub_cancel_left]
    exact finrank_range_smulRight hvt hφt
  have hvφ : ∀ t ∈ D, ∀ x, ((t : V →ₗ[ZMod 2] V) - 1) x = φ t x • v t := by
    intro t ht x
    obtain ⟨-, -, -, htv⟩ := hPD t ht
    rw [htv, show (1 : Module.End (ZMod 2) V) = LinearMap.id from rfl, add_sub_cancel_left,
      LinearMap.smulRight_apply]
  have hirrD : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ Subgroup.closure (D : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)),
        ∀ u ∈ U, (n : V →ₗ[ZMod 2] V) u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hirr U fun n hn => hU n ?_
    rw [hDT, ← hgen]
    exact hn
  obtain ⟨hspanv, -, hchain⟩ :=
    (CFSG.QuasithinUnique.rank_one_generator_chain_irreducibility_criterion D hDne hrank v φ
      (fun t ht => (hPD t ht).1) (fun t ht => (hPD t ht).2.1) hvφ).1 hirrD
  have hcenter : ∀ t ∈ D, v t ∈ transvectionCenters N ∧ φ t ∈ centerFunctionals N (v t) := by
    intro t ht
    obtain ⟨hvt, hφt, hφv, htv⟩ := hPD t ht
    have hmem : φ t ∈ centerFunctionals N (v t) :=
      mem_centerFunctionals.2 ⟨hφv, t, ((hmemD t).1 ht).1, htv⟩
    refine ⟨mem_transvectionCenters.2 ⟨hvt, fun hbot => hφt ?_⟩, hmem⟩
    rw [hbot] at hmem
    exact (Submodule.mem_bot _).1 hmem
  have hΔD : ∀ u ∈ transvectionCenters N, ∀ f ∈ centerFunctionals N u, f ≠ 0 →
      ∃ t ∈ D, v t = u ∧ φ t = f := by
    intro u hu f hf hf0
    obtain ⟨hfu, n, hn, hnf⟩ := mem_centerFunctionals.1 hf
    have hnD : n ∈ D := (hmemD n).2 ⟨hn, u, f, (mem_transvectionCenters.1 hu).1, hf0, hfu, hnf⟩
    obtain ⟨h1, h2⟩ := eq_of_id_add_smulRight_eq (mem_transvectionCenters.1 hu).1 hf0
      (hnf.symm.trans (hPD n hnD).2.2.2)
    exact ⟨n, hnD, h1.symm, h2.symm⟩
  have hspanΔ : Submodule.span (ZMod 2) (transvectionCenters N) = ⊤ := by
    rw [eq_top_iff, ← hspanv]
    refine Submodule.span_mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact (hcenter t ht).1
  let E : V → V → Prop := fun x y => x ∈ transvectionCenters N ∧ y ∈ transvectionCenters N ∧
    ∃ f ∈ centerFunctionals N x, f y = 1
  have hconn : ∀ x ∈ transvectionCenters N, ∀ y ∈ transvectionCenters N,
      Relation.ReflTransGen E x y := by
    intro x hx y hy
    obtain ⟨f, hf, hf0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (mem_transvectionCenters.1 hx).2
    obtain ⟨g, hg, hg0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (mem_transvectionCenters.1 hy).2
    obtain ⟨s, hs, rfl, -⟩ := hΔD x hx f hf hf0
    obtain ⟨t, ht, rfl, -⟩ := hΔD y hy g hg hg0
    obtain ⟨k, c, hc0, hck, hcD, hcφ⟩ := hchain s hs t ht
    have key : ∀ i ≤ k, Relation.ReflTransGen E (v s) (v (c i)) := by
      intro i
      induction i with
      | zero => exact fun _ => hc0 ▸ Relation.ReflTransGen.refl
      | succ i ih =>
        intro hi
        have hci := hcD i (by omega)
        have hci' := hcD (i + 1) hi
        exact (ih (by omega)).tail ⟨(hcenter _ hci).1, (hcenter _ hci').1, φ (c i),
          (hcenter _ hci).2, zmodTwo_eq_one_of_ne_zero (hcφ i (by omega))⟩
    have := key k le_rfl
    rwa [hck] at this
  have hpath : ∀ a b, Relation.ReflTransGen E a b →
      finrank (ZMod 2) (centerFunctionals N b) ≤ finrank (ZMod 2) (centerFunctionals N a) := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | tail _ hbc ih =>
      obtain ⟨-, -, f, hf, hfc⟩ := hbc
      exact (finrank_le_of_incidence hf hfc).trans ih
  have hrecip : ∀ u ∈ transvectionCenters N, ∀ w ∈ transvectionCenters N,
      (∃ f ∈ centerFunctionals N u, f w = 1) → ∃ g ∈ centerFunctionals N w, g u = 1 := by
    rintro u hu w hw ⟨f, hf, hfw⟩
    by_contra h
    push Not at h
    have hlt := finrank_lt_of_one_way hf hfw fun g hg => zmodTwo_eq_zero_of_ne_one (h g hg)
    have hle := hpath w u (hconn w hw u hu)
    omega
  have htrans : ∀ u ∈ transvectionCenters N, ∀ w ∈ transvectionCenters N,
      ∃ n ∈ N, (n : Module.End (ZMod 2) V) u = w := by
    intro u hu w hw
    have hr := hconn u hu w hw
    clear hw
    induction hr with
    | refl => exact ⟨1, one_mem _, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨n, hn, hnu⟩ := ih
      obtain ⟨hb, hc, f, hf, hfc⟩ := hbc
      obtain ⟨g, hg, hgb⟩ := hrecip _ hb _ hc ⟨f, hf, hfc⟩
      obtain ⟨a, ha, hab⟩ := exists_mem_apply_eq_of_incidence hf hfc hg hgb
      exact ⟨a * n, mul_mem ha hn, by rw [Units.val_mul, Module.End.mul_apply, hnu, hab]⟩
  obtain ⟨t₀, ht₀⟩ := hDne
  have hu₀ := (hcenter t₀ ht₀).1
  have hdim : ∀ u ∈ transvectionCenters N,
      finrank (ZMod 2) (centerFunctionals N u) = finrank (ZMod 2) (centerFunctionals N (v t₀)) := by
    intro u hu
    obtain ⟨a, ha, hau⟩ := htrans (v t₀) hu₀ u hu
    rw [← hau, finrank_centerFunctionals_eq ha]
  refine ⟨fun u => rfl, hspanΔ, htrans, fun u hu w hw _ => ⟨hrecip u hu w hw, hrecip w hw u hu⟩,
    finrank (ZMod 2) (centerFunctionals N (v t₀)), ?_, hdim, ?_⟩
  · apply Nat.pos_of_ne_zero
    rw [Ne, Submodule.finrank_eq_zero]
    exact (mem_transvectionCenters.1 hu₀).2
  · rintro u hu w hw ⟨f, hf, hfw⟩
    obtain ⟨g, hg, hgu⟩ := hrecip u hu w hw ⟨f, hf, hfw⟩
    refine ⟨le_antisymm ?_ ?_, by rw [finrank_inf_ker_eval hf hfw, hdim u hu]⟩
    · intro h hh
      obtain ⟨hhu, hhw⟩ := Submodule.mem_inf.1 hh
      rw [LinearMap.mem_ker, Dual.eval_apply] at hhw
      refine Submodule.mem_inf.2 ⟨mem_of_incidence hg hgu hhu hhw, ?_⟩
      rw [LinearMap.mem_ker, Dual.eval_apply]
      exact (mem_centerFunctionals.1 hhu).1
    · intro h hh
      obtain ⟨hhw, hhu⟩ := Submodule.mem_inf.1 hh
      rw [LinearMap.mem_ker, Dual.eval_apply] at hhu
      refine Submodule.mem_inf.2 ⟨mem_of_incidence hf hfw hhw hhu, ?_⟩
      rw [LinearMap.mem_ker, Dual.eval_apply]
      exact (mem_centerFunctionals.1 hhw).1

end CFSG.LocalAnalysis.SteinbergBV
