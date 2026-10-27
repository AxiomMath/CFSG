module

public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinCent
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Basis
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions

public section

namespace CFSG.StandardType.FF81.RootFusionLin

open Matrix

variable (m : ℕ)

theorem index_uSub_cent_one :
    ((uSub 1 m).subgroupOf (Cent 1 m)).index = Nat.card (GL (Fin m) (ZMod 2)) := by
  have hGL1 : Nat.card (GL (Fin 1) (ZMod 2)) = 1 := by
    have h := Matrix.card_GL_field (𝔽 := ZMod 2) 1
    rw [ZMod.card] at h
    simpa using h
  have hcard : Nat.card ((uSub 1 m).subgroupOf (Cent 1 m)) = Nat.card (uSub 1 m) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (uSub_le_cent 1 m)).toEquiv
  have h1 := Subgroup.card_mul_index ((uSub 1 m).subgroupOf (Cent 1 m))
  rw [hcard, card_uSub, card_cent, hGL1] at h1
  have hpos : 0 < 2 ^ (1 * 1 + 2 * 1 * m) := by positivity
  exact Nat.eq_of_mul_eq_mul_left hpos (by simpa using h1)

theorem padicValNat_index_uSub_cent_one :
    padicValNat 2 ((uSub 1 m).subgroupOf (Cent 1 m)).index = m.choose 2 := by
  rw [index_uSub_cent_one, padicValNat_card_GL]

private noncomputable def extra_form (k : ℕ) :
    LinearMap.BilinForm (ZMod 2)
      (Matrix (Fin 1) (Fin k) (ZMod 2) × Matrix (Fin k) (Fin 1) (ZMod 2)) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => (x.1 * y.2) 0 0 + (y.1 * x.2) 0 0)
    (fun x y z => by
      simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply]
      abel)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_apply]
      ring)
    (fun x y z => by
      simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply]
      abel)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_apply]
      ring)

private theorem extra_form_comm (k : ℕ)
    (x y : Matrix (Fin 1) (Fin k) (ZMod 2) × Matrix (Fin k) (Fin 1) (ZMod 2)) :
    extra_form k x y = extra_form k y x := by
  unfold extra_form
  rw [LinearMap.mk₂_apply, LinearMap.mk₂_apply, add_comm]

private theorem extra_form_sep_left (k : ℕ) : (extra_form k).SeparatingLeft := by
  intro x hx
  have h1 : x.1 = 0 := by
    ext i j
    fin_cases i
    have h0 := hx ((0 : Matrix (Fin 1) (Fin k) (ZMod 2)),
      Matrix.single j (0 : Fin 1) (1 : ZMod 2))
    simp only [extra_form, LinearMap.mk₂_apply, Matrix.zero_mul, Matrix.zero_apply] at h0
    simpa using h0
  have h2 : x.2 = 0 := by
    ext i j
    fin_cases j
    have h0 := hx (Matrix.single (0 : Fin 1) i (1 : ZMod 2),
      (0 : Matrix (Fin k) (Fin 1) (ZMod 2)))
    simp only [extra_form, LinearMap.mk₂_apply, Matrix.mul_zero, Matrix.zero_apply] at h0
    simpa using h0
  exact Prod.ext h1 h2

private theorem extra_form_nondegenerate (k : ℕ) : (extra_form k).Nondegenerate :=
  ⟨extra_form_sep_left k, fun y hy => extra_form_sep_left k y fun x => by
    rw [extra_form_comm k y x]; exact hy x⟩

private theorem extra_iso_bound (k : ℕ)
    (W : AddSubgroup (Matrix (Fin 1) (Fin k) (ZMod 2) × Matrix (Fin k) (Fin 1) (ZMod 2)))
    (hiso : ∀ x ∈ W, ∀ y ∈ W, extra_form k x y = 0) :
    Nat.card W ≤ 2 ^ k := by
  let Ws : Submodule (ZMod 2)
      (Matrix (Fin 1) (Fin k) (ZMod 2) × Matrix (Fin k) (Fin 1) (ZMod 2)) :=
    { W with smul_mem' := fun c x hx => ZMod.smul_mem (K := W) hx c }
  have hcard : Nat.card Ws = Nat.card W := rfl
  have hle : Ws ≤ (extra_form k).orthogonal Ws := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hiso y hy x hx
  have hfin : Module.finrank (ZMod 2) Ws ≤ k := by
    have h1 := Submodule.finrank_mono hle
    have h2 := LinearMap.BilinForm.finrank_orthogonal (K := ZMod 2)
      (extra_form_nondegenerate k) Ws
    have hV : Module.finrank (ZMod 2)
        (Matrix (Fin 1) (Fin k) (ZMod 2) × Matrix (Fin k) (Fin 1) (ZMod 2)) = 2 * k := by
      rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_matrix]
      simp
      ring
    rw [h2, hV] at h1
    omega
  calc Nat.card W = Nat.card Ws := hcard.symm
    _ = 2 ^ Module.finrank (ZMod 2) Ws := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hfin

private def extra_a (g : uSub 1 m) : Matrix (Fin 1) (Fin m) (ZMod 2) :=
  Matrix.of fun i j =>
    ((g : GL (BlkIdx 1 m) (ZMod 2)) : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))
      (.inl i) (.inr (.inl j))

private def extra_b (g : uSub 1 m) : Matrix (Fin m) (Fin 1) (ZMod 2) :=
  Matrix.of fun i j =>
    ((g : GL (BlkIdx 1 m) (ZMod 2)) : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))
      (.inr (.inl i)) (.inr (.inr j))

private theorem extra_a_uGL (a : Matrix (Fin 1) (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin 1) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) :
    extra_a m (⟨uGL a b c,
      (mem_uSub_iff (r := 1) (m := m)).mpr ⟨a, b, c, rfl⟩⟩ : uSub 1 m) = a := by
  ext i j
  simp [extra_a, coe_uGL, uMat, blk]

private theorem extra_b_uGL (a : Matrix (Fin 1) (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin 1) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) :
    extra_b m (⟨uGL a b c,
      (mem_uSub_iff (r := 1) (m := m)).mpr ⟨a, b, c, rfl⟩⟩ : uSub 1 m) = b := by
  ext i j
  simp [extra_b, coe_uGL, uMat, blk]

private theorem extra_a_eq_of_coe_eq {g : uSub 1 m}
    {a : Matrix (Fin 1) (Fin m) (ZMod 2)} {b : Matrix (Fin m) (Fin 1) (ZMod 2)}
    {c : Matrix (Fin 1) (Fin 1) (ZMod 2)}
    (h : (g : GL (BlkIdx 1 m) (ZMod 2)) = uGL a b c) : extra_a m g = a := by
  have hg : g = ⟨uGL a b c, (mem_uSub_iff (r := 1) (m := m)).mpr ⟨a, b, c, rfl⟩⟩ :=
    Subtype.ext h
  rw [hg, extra_a_uGL]

private theorem extra_b_eq_of_coe_eq {g : uSub 1 m}
    {a : Matrix (Fin 1) (Fin m) (ZMod 2)} {b : Matrix (Fin m) (Fin 1) (ZMod 2)}
    {c : Matrix (Fin 1) (Fin 1) (ZMod 2)}
    (h : (g : GL (BlkIdx 1 m) (ZMod 2)) = uGL a b c) : extra_b m g = b := by
  have hg : g = ⟨uGL a b c, (mem_uSub_iff (r := 1) (m := m)).mpr ⟨a, b, c, rfl⟩⟩ :=
    Subtype.ext h
  rw [hg, extra_b_uGL]

private def extra_proj : Additive (uSub 1 m) →+
    (Matrix (Fin 1) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin 1) (ZMod 2)) where
  toFun g := (extra_a m (Additive.toMul g), extra_b m (Additive.toMul g))
  map_zero' := by
    show (extra_a m (Additive.toMul (0 : Additive (uSub 1 m))),
        extra_b m (Additive.toMul (0 : Additive (uSub 1 m)))) = (0, 0)
    rw [toMul_zero]
    refine Prod.ext ?_ ?_
    · exact extra_a_eq_of_coe_eq (m := m) (a := 0) (b := 0) (c := 0) (by rw [uGL_zero]; rfl)
    · exact extra_b_eq_of_coe_eq (m := m) (a := 0) (b := 0) (c := 0) (by rw [uGL_zero]; rfl)
  map_add' g h := by
    obtain ⟨a, b, c, hg⟩ := (mem_uSub_iff (r := 1) (m := m)).mp (Additive.toMul g).2
    obtain ⟨a', b', c', hh⟩ := (mem_uSub_iff (r := 1) (m := m)).mp (Additive.toMul h).2
    have hmul : ((Additive.toMul g * Additive.toMul h : uSub 1 m) :
        GL (BlkIdx 1 m) (ZMod 2)) = uGL (a + a') (b + b') (c + c' + a * b') := by
      rw [Subgroup.coe_mul, hg, hh, uGL_mul]
    show (extra_a m (Additive.toMul (g + h)), extra_b m (Additive.toMul (g + h))) =
      (extra_a m (Additive.toMul g), extra_b m (Additive.toMul g)) +
      (extra_a m (Additive.toMul h), extra_b m (Additive.toMul h))
    rw [toMul_add]
    have hA : extra_a m (Additive.toMul g * Additive.toMul h) =
        extra_a m (Additive.toMul g) + extra_a m (Additive.toMul h) := by
      rw [extra_a_eq_of_coe_eq (m := m) hmul, extra_a_eq_of_coe_eq (m := m) hg,
        extra_a_eq_of_coe_eq (m := m) hh]
    have hB : extra_b m (Additive.toMul g * Additive.toMul h) =
        extra_b m (Additive.toMul g) + extra_b m (Additive.toMul h) := by
      rw [extra_b_eq_of_coe_eq (m := m) hmul, extra_b_eq_of_coe_eq (m := m) hg,
        extra_b_eq_of_coe_eq (m := m) hh]
    exact Prod.ext hA hB

private theorem extra_mem_zSub_of_proj_eq_zero {g : Additive (uSub 1 m)}
    (hg : extra_proj m g = 0) :
    ((Additive.toMul g : uSub 1 m) : GL (BlkIdx 1 m) (ZMod 2)) ∈ zSub 1 m := by
  obtain ⟨a, b, c, hg'⟩ := (mem_uSub_iff (r := 1) (m := m)).mp (Additive.toMul g).2
  have hpair : (extra_a m (Additive.toMul g), extra_b m (Additive.toMul g)) = (0, 0) := by
    simpa [extra_proj] using hg
  have ha : a = 0 := (extra_a_eq_of_coe_eq (m := m) hg').symm.trans (congrArg Prod.fst hpair)
  have hb : b = 0 := (extra_b_eq_of_coe_eq (m := m) hg').symm.trans (congrArg Prod.snd hpair)
  refine (mem_zSub_iff (r := 1) (m := m)).mpr ⟨c, ?_⟩
  rw [hg', ha, hb]

private noncomputable def extra_zCoeff (x : zSub 1 m) : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  Classical.choose ((mem_zSub_iff (r := 1) (m := m)).mp x.2)

private theorem extra_card_zSub_le_two : Nat.card (zSub 1 m) ≤ 2 := by
  have hMat : Nat.card (Matrix (Fin 1) (Fin 1) (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hinj : Function.Injective (extra_zCoeff m) := by
    intro x y hxy
    apply Subtype.ext
    rw [Classical.choose_spec ((mem_zSub_iff (r := 1) (m := m)).mp x.2),
      Classical.choose_spec ((mem_zSub_iff (r := 1) (m := m)).mp y.2)]
    change uGL 0 0 (extra_zCoeff m x) = uGL 0 0 (extra_zCoeff m y)
    rw [hxy]
  calc Nat.card (zSub 1 m) ≤ Nat.card (Matrix (Fin 1) (Fin 1) (ZMod 2)) :=
        Nat.card_le_card_of_injective _ hinj
    _ = 2 := hMat

private theorem extra_form_eq_zero_of_commute {g h : uSub 1 m}
    (hgh : (g : GL (BlkIdx 1 m) (ZMod 2)) * (h : GL (BlkIdx 1 m) (ZMod 2)) =
      (h : GL (BlkIdx 1 m) (ZMod 2)) * (g : GL (BlkIdx 1 m) (ZMod 2))) :
    extra_form m (extra_a m g, extra_b m g) (extra_a m h, extra_b m h) = 0 := by
  obtain ⟨a, b, c, hg⟩ := (mem_uSub_iff (r := 1) (m := m)).mp g.2
  obtain ⟨a', b', c', hh⟩ := (mem_uSub_iff (r := 1) (m := m)).mp h.2
  have hcomm' : uGL a b c * uGL a' b' c' = uGL a' b' c' * uGL a b c := by
    rw [← hg, ← hh]; exact hgh
  have hzero : a * b' + a' * b = 0 := by
    have h := uGL_commutator 1 m a a' b b' c c'
    rw [hcomm'] at h
    have h1 : uGL a' b' c' * uGL a b c * (uGL a b c)⁻¹ * (uGL a' b' c')⁻¹ = 1 := by group
    rw [h1] at h
    have h2 : uGL (0 : Matrix (Fin 1) (Fin m) (ZMod 2))
        (0 : Matrix (Fin m) (Fin 1) (ZMod 2)) (a * b' + a' * b) = uGL 0 0 0 :=
      h.symm.trans uGL_zero.symm
    exact (uGL_injective h2).2.2
  rw [extra_a_eq_of_coe_eq (m := m) hg, extra_b_eq_of_coe_eq (m := m) hg,
    extra_a_eq_of_coe_eq (m := m) hh, extra_b_eq_of_coe_eq (m := m) hh]
  simp only [extra_form, LinearMap.mk₂_apply]
  rw [← Matrix.add_apply, hzero, Matrix.zero_apply]

theorem card_le_of_commute_of_le_uSub_one (E : Subgroup (GL (BlkIdx 1 m) (ZMod 2)))
    (hEU : E ≤ uSub 1 m) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card E ≤ 2 ^ (m + 1) := by
  let E' : Subgroup (uSub 1 m) := E.subgroupOf (uSub 1 m)
  let f : Additive E' →+
      (Matrix (Fin 1) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin 1) (ZMod 2)) :=
    (extra_proj m).comp E'.subtype.toAdditive
  have hEcard : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEU).toEquiv
  have hker : Nat.card f.ker ≤ 2 := by
    have h1 : Nat.card f.ker ≤ Nat.card (zSub 1 m) := by
      let Φ : f.ker → zSub 1 m := fun x =>
        ⟨(Additive.toMul (E'.subtype.toAdditive x.1) : uSub 1 m),
          extra_mem_zSub_of_proj_eq_zero (m := m) (g := E'.subtype.toAdditive x.1)
            (by
              show extra_proj m (E'.subtype.toAdditive x.1) = 0
              exact x.2)⟩
      have hinj : Function.Injective Φ := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : zSub 1 m => (z : GL (BlkIdx 1 m) (ZMod 2))) hxy
      exact Nat.card_le_card_of_injective Φ hinj
    exact h1.trans (extra_card_zSub_le_two m)
  have hrange : Nat.card f.range ≤ 2 ^ m := by
    refine extra_iso_bound m f.range ?_
    intro x hx y hy
    obtain ⟨ex, rfl⟩ := AddMonoidHom.mem_range.mp hx
    obtain ⟨ey, rfl⟩ := AddMonoidHom.mem_range.mp hy
    have h1 : f ex = (extra_a m (Additive.toMul (E'.subtype.toAdditive ex)),
        extra_b m (Additive.toMul (E'.subtype.toAdditive ex))) := rfl
    have h2 : f ey = (extra_a m (Additive.toMul (E'.subtype.toAdditive ey)),
        extra_b m (Additive.toMul (E'.subtype.toAdditive ey))) := rfl
    rw [h1, h2]
    exact extra_form_eq_zero_of_commute (m := m)
      (g := Additive.toMul (E'.subtype.toAdditive ex))
      (h := Additive.toMul (E'.subtype.toAdditive ey))
      (hcomm _ (Subgroup.mem_subgroupOf.mp (Additive.toMul ex).2) _
        (Subgroup.mem_subgroupOf.mp (Additive.toMul ey).2))
  have hmain := AddSubgroup.card_ker_mul_card_range f
  calc Nat.card E = Nat.card E' := hEcard.symm
    _ = Nat.card f.ker * Nat.card f.range := hmain.symm
    _ ≤ 2 * 2 ^ m := Nat.mul_le_mul hker hrange
    _ = 2 ^ (m + 1) := by rw [pow_succ, mul_comm]

end CFSG.StandardType.FF81.RootFusionLin

end
