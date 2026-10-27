module

public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.S2
public import CFSG.Quasithin.Recognition.SzVBEvenCrit

public section

namespace CFSG.Quasithin.Kleidman.VBOdd

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

@[expose] def actTriv (P Y W : Subgroup G) (hYP : Y ≤ P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) (hPW : P ≤ Subgroup.normalizer (W : Set G)) :
    Subgroup G where
  carrier := {g | g ∈ P ∧ ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ W}
  one_mem' := ⟨P.one_mem, fun y _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgY⟩ ⟨hh, hhY⟩
    refine ⟨P.mul_mem hg hh, fun y hy => ?_⟩
    have h1 : g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hPW hg) _).mp (hhY y hy)
    have e : g * h * y * (g * h)⁻¹ * y⁻¹ =
        g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹) := by group
    rw [e]
    exact W.mul_mem h1 (hgY y hy)
  inv_mem' := by
    rintro g ⟨hg, hgY⟩
    refine ⟨P.inv_mem hg, fun y hy => ?_⟩
    have hy' : g⁻¹ * y⁻¹ * g ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hPY (P.inv_mem hg)) y⁻¹).mp (Y.inv_mem hy)
      simpa using this
    have h1 := hgY _ hy'
    have h2 : y * (g * (g⁻¹ * y⁻¹ * g) * g⁻¹ * (g⁻¹ * y⁻¹ * g)⁻¹) * y⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hPW (hYP hy)) _).mp h1
    have e : g⁻¹ * y * g⁻¹⁻¹ * y⁻¹ =
        y * (g * (g⁻¹ * y⁻¹ * g) * g⁻¹ * (g⁻¹ * y⁻¹ * g)⁻¹) * y⁻¹ := by group
    rw [e]
    exact h2

omit [Finite G] in
theorem le_normalizer_actTriv {P Y W : Subgroup G} (hYP : Y ≤ P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) (hPW : P ≤ Subgroup.normalizer (W : Set G)) :
    P ≤ Subgroup.normalizer (actTriv P Y W hYP hPY hPW : Set G) := by
  have key : ∀ k ∈ P, ∀ g ∈ actTriv P Y W hYP hPY hPW,
      k * g * k⁻¹ ∈ actTriv P Y W hYP hPY hPW := by
    rintro k hk g ⟨hg, hgY⟩
    refine ⟨P.mul_mem (P.mul_mem hk hg) (P.inv_mem hk), fun y hy => ?_⟩
    have hy' : k⁻¹ * y * k ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hPY (P.inv_mem hk)) y).mp hy
      simpa using this
    have h1 : k * (g * (k⁻¹ * y * k) * g⁻¹ * (k⁻¹ * y * k)⁻¹) * k⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hPW hk) _).mp (hgY _ hy')
    have e : k * g * k⁻¹ * y * (k * g * k⁻¹)⁻¹ * y⁻¹ =
        k * (g * (k⁻¹ * y * k) * g⁻¹ * (k⁻¹ * y * k)⁻¹) * k⁻¹ := by group
    rw [e]
    exact h1
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key k hk g, fun h => ?_⟩
  have := key k⁻¹ (P.inv_mem hk) _ h
  simpa [mul_assoc] using this

namespace CritGeo

variable {p : ℕ → CosetGeom G₀ G₁ G₂} (H : CritGeo p V) (C : Ctx G₀ G₁ G₂ T V z)

include H C

theorem s6 : False := by
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hb := H.b7
  have hG := C.hyp.gen
  have hN := C.hyp.normalizes
  obtain ⟨hYab, hWY, hYG, hGY⟩ := H.y3_basic C
  have hW : Vv V (γ₁ G₀ G₁ G₂) = conjClosure V G₂ := Vv_γ₁ C.hyp.le₂ hN
  have hGW : G₂ ≤ Subgroup.normalizer (conjClosure V G₂ : Set G) := by
    have := stab_le_normalizer_Vv hN (γ₁ G₀ G₁ G₂)
    rwa [stab_γ₁ C.hyp.le₂, hW] at this
  have hα : vtype (p b) = true := H.vtype_odd hG le_rfl H.odd
  have hW'β : Vv V (p b) ≤ G₂ := by
    have := SzVB.Vv_le_stab_of_dist_le_B C.toGeoCtx hα (x := γ₁ G₀ G₁ G₂)
      (by rw [CosetGeom.dist_comm, ← H.p1, H.dist_eq (by omega) le_rfl]; omega)
    rwa [stab_γ₁ C.hyp.le₂] at this
  set C' := actTriv G₂ (ballV V 3 (γ₁ G₀ G₁ G₂)) (conjClosure V G₂) hYG hGY hGW with hC'
  have hC'le : C' ≤ G₂ := fun g hg => hg.1
  have hW'C : Vv V (p b) ≤ C' := by
    intro x hx
    refine ⟨hW'β hx, fun y hy => ?_⟩
    have h1 := H.s5 C y hy x hx
    have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have hC'Q : ¬ C' ≤ pCoreOf 2 G₂ := fun h => (H.s1 C).2 (hW'C.trans h)
  have hsup := C.simple C' hC'le (le_normalizer_actTriv hYG hGY hGW) hC'Q
  set Y := ballV V 2 (γ₀ G₀ G₁ G₂) with hYdef
  have hWY' : conjClosure V G₂ ≤ Y := by
    rw [← hW, Vv_B_le_iff vtype_γ₁]
    intro x hx
    refine Vv_le_ballV (vtype_eq_false_of_adj hx vtype_γ₁) ?_
    have h1 := dist_triangle hG (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) x
    rw [dist_eq_one_iff_adj.mpr (adj_γ₀_γ₁ (G₀ := G₀)), dist_eq_one_iff_adj.mpr hx] at h1
    omega
  have hYY3 : Y ≤ ballV V 3 (γ₁ G₀ G₁ G₂) := by
    refine ballV_le fun x hx hd => Vv_le_ballV hx ?_
    have h1 := dist_triangle hG (γ₁ G₀ G₁ G₂) (γ₀ G₀ G₁ G₂) x
    rw [dist_eq_one_iff_adj.mpr (adj_γ₀_γ₁ (G₀ := G₀)).symm] at h1
    omega
  have hG₁Y : G₁ ≤ Subgroup.normalizer (Y : Set G) := by
    have := stab_le_normalizer_ballV hN 2 (γ₀ G₀ G₁ G₂)
    rwa [stab_γ₀ C.hyp.le₁] at this
  have hC'Y : C' ≤ Subgroup.normalizer (Y : Set G) := by
    have key : ∀ g ∈ C', conjSub g Y ≤ Y := by
      intro g hg
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hg.2 y (hYY3 hy)
      show g * y * g⁻¹ ∈ Y
      have e : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact Y.mul_mem (hWY' h1) hy
    intro g hg
    exact mem_normalizer_of_conj_le (key g hg) (key g⁻¹ (C'.inv_mem hg))
  have hQY : pCoreOf 2 G₂ ≤ Subgroup.normalizer (Y : Set G) := by
    intro c hc
    have h1 : c ∈ ballStab 1 (γ₁ G₀ G₁ G₂) := by
      have := pCoreOf_stab_le_ballStab_one C.hyp.toAmalgamHyp (γ₁ G₀ G₁ G₂)
      rw [stab_γ₁ C.hyp.le₂] at this
      exact this hc
    have h2 : c ∈ stab (γ₀ G₀ G₁ G₂) := mem_ballStab.mp h1 _
      (by rw [dist_eq_one_iff_adj.mpr (adj_γ₀_γ₁ (G₀ := G₀)).symm])
    rw [stab_γ₀ C.hyp.le₁] at h2
    exact hG₁Y h2
  have hG₂Y : G₂ ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← hsup]
    exact sup_le hC'Y hQY
  have hG₀Y : G₀ ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hG]; exact sup_le hG₁Y hG₂Y
  have hYG₀ : Y ≤ G₀ := (hYY3.trans hYG).trans C.hyp.le₂
  have hYp : IsPGroup 2 Y := isPGroup_of_isElemAbelian (isElemAbelian_mono hYab hYY3)
  have hYO := le_pCoreOf_of_le_normalizer 2 hYG₀ hG₀Y hYp
  rw [C.hyp.o2_trivial] at hYO
  have hVY : V ≤ Y := by
    have := Vv_le_ballV (V := V) (n := 2) (u := γ₀ G₀ G₁ G₂) vtype_γ₀
      (by rw [CosetGeom.dist_self]; omega)
    rwa [Vv_γ₀ hN] at this
  exact SzVB.V_ne_bot C.toGeoCtx (le_bot_iff.mp (hVY.trans hYO))

end CritGeo

theorem Ctx.false_of_odd (C : Ctx G₀ G₁ G₂ T V z) (hb : 7 ≤ critDist G₀ G₁ G₂ V)
    (hodd : Odd (critDist G₀ G₁ G₂ V)) : False := by
  obtain ⟨p, hp, hp0, hp1, hcrit⟩ := SzVB.exists_crit_geodesic C.toGeoCtx
  exact (CritGeo.mk hb hodd hp hp0 hp1 hcrit).s6 C

end CFSG.Quasithin.Kleidman.VBOdd
