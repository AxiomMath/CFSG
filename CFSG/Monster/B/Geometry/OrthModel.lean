module

public import CFSG.LieType.Chevalley.C2E6MinusSixForm

public section

namespace CFSG.Monster.B.Geometry

open Module CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap (X Q)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev OV : Type := Fin 8 → ZMod 2

@[expose] def oPolar (v w : OV) : ZMod 2 :=
  v 0 * w 3 + v 3 * w 0 + v 1 * w 4 + v 4 * w 1 + v 2 * w 5 + v 5 * w 2 + v 6 * w 7 + v 7 * w 6

@[expose] def oPolarBilin : LinearMap.BilinForm (ZMod 2) OV :=
  LinearMap.mk₂ (ZMod 2) oPolar
    (fun _ _ _ => by simp only [oPolar, Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [oPolar, Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [oPolar, Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [oPolar, Pi.smul_apply, smul_eq_mul]; ring)

@[expose] def oQ : QuadraticForm (ZMod 2) OV where
  toFun v := v 0 * v 3 + v 1 * v 4 + v 2 * v 5 + v 6 ^ 2 + v 6 * v 7 + v 7 ^ 2
  toFun_smul a v := by simp only [Pi.smul_apply, smul_eq_mul]; ring
  exists_companion' := ⟨oPolarBilin, fun x y => by
    have h2 : (2 : ZMod 2) = 0 := rfl
    simp only [oPolarBilin, LinearMap.mk₂_apply, oPolar, Pi.add_apply]
    linear_combination (x 6 * y 6 + x 7 * y 7) * h2⟩

theorem oQ_apply (v : OV) :
    oQ v = v 0 * v 3 + v 1 * v 4 + v 2 * v 5 + v 6 ^ 2 + v 6 * v 7 + v 7 ^ 2 := rfl

theorem polar_oQ (v w : OV) : QuadraticMap.polar oQ v w = oPolar v w := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [QuadraticMap.polar, oQ_apply, oPolar, Pi.add_apply]
  linear_combination (v 6 * w 6 + v 7 * w 7) * h2

theorem oQ_add (v w : OV) : oQ (v + w) = oQ v + oQ w + oPolar v w := by
  rw [← polar_oQ]
  exact QuadraticMap.map_add oQ v w

theorem oPolar_comm (v w : OV) : oPolar v w = oPolar w v := by
  simp only [oPolar]
  ring

theorem oPolar_self (v : OV) : oPolar v v = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [oPolar]
  linear_combination (v 0 * v 3 + v 1 * v 4 + v 2 * v 5 + v 6 * v 7) * h2

theorem oPolar_add_left (v v' w : OV) : oPolar (v + v') w = oPolar v w + oPolar v' w := by
  simp only [oPolar, Pi.add_apply]
  ring

theorem oPolar_add_right (v w w' : OV) : oPolar v (w + w') = oPolar v w + oPolar v w' := by
  simp only [oPolar, Pi.add_apply]
  ring

theorem oPolar_smul_left (c : ZMod 2) (v w : OV) : oPolar (c • v) w = c * oPolar v w := by
  simp only [oPolar, Pi.smul_apply, smul_eq_mul]
  ring

theorem oPolar_smul_right (c : ZMod 2) (v w : OV) : oPolar v (c • w) = c * oPolar v w := by
  simp only [oPolar, Pi.smul_apply, smul_eq_mul]
  ring

theorem oPolar_zero_left (w : OV) : oPolar 0 w = 0 := by simp [oPolar]

theorem oPolar_zero_right (v : OV) : oPolar v 0 = 0 := by simp [oPolar]

theorem oQ_smul (c : ZMod 2) (v : OV) : oQ (c • v) = c * c * oQ v := by
  rw [QuadraticMap.map_smul, smul_eq_mul]

theorem oPolar_nondeg (v : OV) (hv : ∀ w, oPolar v w = 0) : v = 0 := by
  have h0 := hv (Pi.single 3 1)
  have h1 := hv (Pi.single 4 1)
  have h2 := hv (Pi.single 5 1)
  have h3 := hv (Pi.single 0 1)
  have h4 := hv (Pi.single 1 1)
  have h5 := hv (Pi.single 2 1)
  have h6 := hv (Pi.single 7 1)
  have h7 := hv (Pi.single 6 1)
  simp only [oPolar, Pi.single_apply] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  funext i
  fin_cases i <;> assumption

@[expose] def IsTSo (U : Submodule (ZMod 2) OV) : Prop := ∀ v ∈ U, oQ v = 0

theorem oPolar_eq_zero_of_isTSo {U : Submodule (ZMod 2) OV} (hU : IsTSo U) {v w : OV}
    (hv : v ∈ U) (hw : w ∈ U) : oPolar v w = 0 := by
  have h := oQ_add v w
  rw [hU _ (U.add_mem hv hw), hU v hv, hU w hw, zero_add, zero_add] at h
  exact h.symm

theorem IsTSo.mono {U U' : Submodule (ZMod 2) OV} (hU : IsTSo U) (h : U' ≤ U) : IsTSo U' :=
  fun v hv => hU v (h hv)

theorem isTSo_sup_span {U : Submodule (ZMod 2) OV} (hU : IsTSo U) {v : OV} (hv : oQ v = 0)
    (hvU : ∀ u ∈ U, oPolar u v = 0) : IsTSo (U ⊔ (ZMod 2) ∙ v) := by
  intro w hw
  obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [oQ_add, hU u hu, oQ_smul, hv, oPolar_smul_right, hvU u hu]
  ring

@[expose] def oProjFun (v : OV) : X := ![v 1, v 2, v 4, v 5, v 6, v 7]

@[expose] def oProj : OV →ₗ[ZMod 2] X where
  toFun := oProjFun
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl

theorem oProj_apply (v : OV) : oProj v = ![v 1, v 2, v 4, v 5, v 6, v 7] := rfl

theorem oQ_eq_Q_oProj {v : OV} (hv : v 3 = 0) : oQ v = Q (oProj v) := by
  rw [oQ_apply, C2E6Overlap.Q_apply, oProj_apply, hv]
  simp

theorem oPolar_eq_polarQ_oProj {v w : OV} (hv : v 3 = 0) (hw : w 3 = 0) (hv0 : v 0 = 0 ∨ w 0 = 0)
    : oPolar v w = C2E6Overlap.polarQ (oProj v) (oProj w) := by
  rw [oPolar, C2E6Overlap.polarQ, oProj_apply, oProj_apply, hv, hw]
  rcases hv0 with h | h <;> simp [h]

theorem eq_smul_of_oProj_eq_zero {v : OV} (hv : v 3 = 0) (h : oProj v = 0) :
    v = v 0 • Pi.single 0 1 := by
  have h' : ∀ i, (![v 1, v 2, v 4, v 5, v 6, v 7] : X) i = 0 := fun i => by
    rw [← oProj_apply, h]
    rfl
  have e1 := h' 0
  have e2 := h' 1
  have e4 := h' 2
  have e5 := h' 3
  have e6 := h' 4
  have e7 := h' 5
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at e1 e2 e4 e5 e6 e7
  funext i
  fin_cases i <;> simp [hv, e1, e2, e4, e5, e6, e7]

theorem isTotallySingular_map_oProj {U : Submodule (ZMod 2) OV} (hU : IsTSo U)
    (hU3 : ∀ v ∈ U, v 3 = 0) : C2E6Overlap.IsTotallySingular (U.map oProj) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [← oQ_eq_Q_oProj (hU3 v hv)]
  exact hU v hv

theorem single_zero_ne_zero : (Pi.single 0 1 : OV) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

theorem finrank_le_finrank_map_oProj_add_one {U : Submodule (ZMod 2) OV}
    (hU3 : ∀ v ∈ U, v 3 = 0) :
    finrank (ZMod 2) U ≤ finrank (ZMod 2) (U.map oProj) + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (oProj.domRestrict U)
  rw [LinearMap.range_domRestrict] at h
  have hk : finrank (ZMod 2) (LinearMap.ker (oProj.domRestrict U)) ≤ 1 := by
    rw [← Submodule.finrank_map_subtype_eq]
    have hle : (LinearMap.ker (oProj.domRestrict U)).map U.subtype ≤
        (ZMod 2) ∙ (Pi.single 0 1 : OV) := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.domRestrict_apply] at hu
      rw [Submodule.subtype_apply, eq_smul_of_oProj_eq_zero (hU3 u u.2) hu]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    exact (Submodule.finrank_mono hle).trans (finrank_span_singleton single_zero_ne_zero).le
  omega

theorem finrank_le_finrank_map_oProj {U : Submodule (ZMod 2) OV} (hU3 : ∀ v ∈ U, v 3 = 0)
    (he : (Pi.single 0 1 : OV) ∉ U) :
    finrank (ZMod 2) U ≤ finrank (ZMod 2) (U.map oProj) := by
  have h := LinearMap.finrank_range_add_finrank_ker (oProj.domRestrict U)
  rw [LinearMap.range_domRestrict] at h
  have hk : LinearMap.ker (oProj.domRestrict U) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hu
    have h1 := eq_smul_of_oProj_eq_zero (hU3 u u.2) hu
    rcases C2E6Overlap.zmod_two_eq_zero_or_one ((u : OV) 0) with h0 | h0
    · rw [Submodule.mem_bot]
      exact Subtype.ext (by rw [h1, h0, zero_smul]; rfl)
    · exfalso
      rw [h0, one_smul] at h1
      exact he (h1 ▸ u.2)
  rw [hk, finrank_bot] at h
  omega

theorem finrank_le_three_of_isTSo {U : Submodule (ZMod 2) OV} (hU : IsTSo U) :
    finrank (ZMod 2) U ≤ 3 := by
  by_cases he : (Pi.single 0 1 : OV) ∈ U
  · have h3 : ∀ u ∈ U, u 3 = 0 := fun u hu => by
      have := oPolar_eq_zero_of_isTSo hU he hu
      simpa [oPolar, Pi.single_apply] using this
    have h1 := finrank_le_finrank_map_oProj_add_one h3
    have h2 := C2E6Overlap.finrank_le_two_of_isTotallySingular
      (isTotallySingular_map_oProj hU h3)
    omega
  · set φ : OV →ₗ[ZMod 2] ZMod 2 := LinearMap.proj 3
    have h3 : ∀ u ∈ U ⊓ LinearMap.ker φ, u 3 = 0 := fun u hu =>
      LinearMap.mem_ker.mp (Submodule.mem_inf.mp hu).2
    have hφ : finrank (ZMod 2) (LinearMap.ker φ) = 7 := by
      have h := LinearMap.finrank_range_add_finrank_ker φ
      have hr : LinearMap.range φ = ⊤ := by
        rw [eq_top_iff]
        intro c _
        exact ⟨Pi.single 3 c, by simp [φ]⟩
      rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
      omega
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker φ)
    have hle := Submodule.finrank_le (U ⊔ LinearMap.ker φ)
    rw [Module.finrank_fin_fun] at hle
    have h1 := finrank_le_finrank_map_oProj h3 (fun h => he (Submodule.mem_inf.mp h).1)
    have h2 := C2E6Overlap.finrank_le_two_of_isTotallySingular
      (isTotallySingular_map_oProj (hU.mono inf_le_left) h3)
    omega

end CFSG.Monster.B.Geometry
