module

public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.S1
public import CFSG.Quasithin.Recognition.SzVBEvenLabel
public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Ball

public section

namespace CFSG.Quasithin.Kleidman.VBOdd

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

namespace CritGeo

variable {p : ℕ → CosetGeom G₀ G₁ G₂} (H : CritGeo p V) (C : Ctx G₀ G₁ G₂ T V z)

include H C

theorem y3_basic :
    IsElemAbelian 2 (ballV V 3 (γ₁ G₀ G₁ G₂)) ∧ conjClosure V G₂ ≤ ballV V 3 (γ₁ G₀ G₁ G₂) ∧
      ballV V 3 (γ₁ G₀ G₁ G₂) ≤ G₂ ∧
      G₂ ≤ Subgroup.normalizer (ballV V 3 (γ₁ G₀ G₁ G₂) : Set G) := by
  have hb := H.b7
  have hN := C.hyp.normalizes
  refine ⟨isElemAbelian_ballV C.hyp (SzVB.V_ne_bot C.toGeoCtx) (by omega) _, ?_, ?_, ?_⟩
  · rw [← Vv_γ₁ C.hyp.le₂ hN, Vv_B_le_iff vtype_γ₁]
    intro x hx
    exact Vv_le_ballV (vtype_eq_false_of_adj hx vtype_γ₁) (by rw [dist_eq_one_iff_adj.mpr hx]; norm_num)
  · refine ballV_le fun x hx hd => ?_
    have := SzVB.Vv_le_stab_of_dist_le C.toGeoCtx hx (y := γ₁ G₀ G₁ G₂)
      (by rw [CosetGeom.dist_comm]; omega)
    rwa [stab_γ₁ C.hyp.le₂] at this
  · have := stab_le_normalizer_ballV hN 3 (γ₁ G₀ G₁ G₂)
    rwa [stab_γ₁ C.hyp.le₂] at this

theorem s2 :
    ballV V 3 (γ₁ G₀ G₁ G₂) ≤
      Subgroup.centralizer (Vv V (p (critDist G₀ G₁ G₂ V - 1)) : Set G) := by
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hb := H.b7
  have hG := C.hyp.gen
  have hN := C.hyp.normalizes
  obtain ⟨hYab, hWY, -, -⟩ := H.y3_basic C
  have hσ : vtype (p (b - 3)) = false := H.vtype_even hG (by omega)
    (by obtain ⟨k, hk⟩ := H.odd; exact ⟨k - 1, by omega⟩)
  have hā : vtype (p (b - 1)) = false := H.vtype_even hG (by omega)
    (by obtain ⟨k, hk⟩ := H.odd; exact ⟨k, by omega⟩)
  have d1σ : dist (γ₁ G₀ G₁ G₂) (p (b - 3)) = b - 4 := by
    rw [← H.p1, H.dist_eq (by omega) (by omega)]; omega
  have hYQσ : ballV V 3 (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 (stab (p (b - 3))) := by
    refine ballV_le fun x hx hd => SzVB.Vv_le_pCoreOf_of_dist_lt C.toGeoCtx hx ?_
    have := dist_triangle hG x (γ₁ G₀ G₁ G₂) (p (b - 3))
    have hd' : dist x (γ₁ G₀ G₁ G₂) ≤ 3 := by rw [CosetGeom.dist_comm]; exact hd
    omega
  have hadj1 : (graph G₀ G₁ G₂).Adj (p (b - 3)) (p (b - 2)) := by
    have := H.adj (i := b - 3) (by omega)
    rwa [show b - 3 + 1 = b - 2 by omega] at this
  have hadj2 : (graph G₀ G₁ G₂).Adj (p (b - 1)) (p (b - 2)) := by
    have := H.adj (i := b - 2) (by omega)
    rw [show b - 2 + 1 = b - 1 by omega] at this
    exact this.symm
  have hadj3 : (graph G₀ G₁ G₂).Adj (p (b - 1)) (p b) := by
    have := H.adj (i := b - 1) (by omega)
    rwa [show b - 1 + 1 = b by omega] at this
  have hne : p b ≠ p (b - 2) := (H.geo.ne (by omega : b - 2 < b) le_rfl).symm
  have hsup := SzVB.Zv_sup_eq C.toGeoCtx hā hadj3 hadj2 hne
  rw [Subgroup.le_centralizer_iff, ← hsup]
  apply sup_le
  ·
    intro c hc y hy
    exact isElemAbelian_comm hYab hy (hWY ((H.s1 C).1 hc))
  ·
    have hZ : Zv z (p (b - 2)) ≤ Vv V (p (b - 3)) :=
      Zv_le_Vv_of_adj C.klein.z_mem hN (SzVB.G₂_le_normalizer_zpowers C.toGeoCtx) hadj1 hσ
    intro c hc y hy
    have := SzVB.pCoreOf_le_centralizer_Vv C.toGeoCtx hσ (hYQσ hy)
    exact (Subgroup.mem_centralizer_iff.mp this c (hZ hc)).symm

theorem s3 :
    ballV V 3 (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 (stab (p (critDist G₀ G₁ G₂ V - 2))) := by
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hb := H.b7
  have hG := C.hyp.gen
  have hN := C.hyp.normalizes
  obtain ⟨hYab, -, -, -⟩ := H.y3_basic C
  have hcent := H.s2 C
  have hd : vtype (p (b - 2)) = true := H.vtype_odd hG (by omega)
    (by obtain ⟨k, hk⟩ := H.odd; exact ⟨k - 1, by omega⟩)
  have hσ : vtype (p (b - 3)) = false := H.vtype_even hG (by omega)
    (by obtain ⟨k, hk⟩ := H.odd; exact ⟨k - 1, by omega⟩)
  have d1σ : dist (γ₁ G₀ G₁ G₂) (p (b - 3)) = b - 4 := by
    rw [← H.p1, H.dist_eq (by omega) (by omega)]; omega
  have d1d : dist (γ₁ G₀ G₁ G₂) (p (b - 2)) = b - 3 := by
    rw [← H.p1, H.dist_eq (by omega) (by omega)]; omega
  have hYQσ : ballV V 3 (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 (stab (p (b - 3))) := by
    refine ballV_le fun x hx hd => SzVB.Vv_le_pCoreOf_of_dist_lt C.toGeoCtx hx ?_
    have := dist_triangle hG x (γ₁ G₀ G₁ G₂) (p (b - 3))
    have hd' : dist x (γ₁ G₀ G₁ G₂) ≤ 3 := by rw [CosetGeom.dist_comm]; exact hd
    omega
  have hYd : ballV V 3 (γ₁ G₀ G₁ G₂) ≤ stab (p (b - 2)) := by
    refine ballV_le fun x hx hd => SzVB.Vv_le_stab_of_dist_le C.toGeoCtx hx ?_
    have := dist_triangle hG x (γ₁ G₀ G₁ G₂) (p (b - 2))
    have hd' : dist x (γ₁ G₀ G₁ G₂) ≤ 3 := by rw [CosetGeom.dist_comm]; exact hd
    omega
  have hσd : p (b - 3) ∈ nbrs (p (b - 2)) := by
    have := H.adj (i := b - 3) (by omega)
    rw [show b - 3 + 1 = b - 2 by omega] at this
    exact this.symm
  have hād : p (b - 1) ∈ nbrs (p (b - 2)) := by
    have := H.adj (i := b - 2) (by omega)
    rwa [show b - 2 + 1 = b - 1 by omega] at this
  have hneV : Vv V (p (b - 3)) ≠ Vv V (p (b - 1)) := by
    intro heq
    have hα'ā : p b ∈ nbrs (p (b - 1)) := by
      have := H.adj (i := b - 1) (by omega)
      rw [show b - 1 + 1 = b by omega] at this
      exact this
    have h1 := C.twin_at hd hσd hād heq hα'ā
    have h2 : dist (p (b - 3)) (p b) = 1 := dist_eq_one_iff_adj.mpr h1
    rw [H.dist_eq (by omega) le_rfl] at h2
    omega
  intro y hy
  have hy2 : y * y = 1 := by
    have := isElemAbelian_pow_eq_one hYab hy; rwa [pow_two] at this
  have hyσ : y ∈ Subgroup.normalizer (Vv V (p (b - 3)) : Set G) :=
    stab_le_normalizer_Vv hN _ ((pCoreOf_le 2 _) (hYQσ hy))
  have hyā : y ∈ Subgroup.normalizer (Vv V (p (b - 1)) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (hcent hy)
  exact C.two_fixed_at hd hσd hād hneV (hYd hy) hy2 hyσ hyā

theorem s4 :
    ballV V 3 (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 (stab (p (critDist G₀ G₁ G₂ V - 1))) := by
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hb := H.b7
  have hG := C.hyp.gen
  have hā : vtype (p (b - 1)) = false := H.vtype_even hG (by omega)
    (by obtain ⟨k, hk⟩ := H.odd; exact ⟨k, by omega⟩)
  have hād : dist (p (b - 2)) (p (b - 1)) ≤ 1 := by
    rw [H.dist_eq (by omega) (by omega)]; omega
  intro y hy
  have h1 : y ∈ stab (p (b - 1)) :=
    mem_ballStab.mp (pCoreOf_stab_le_ballStab_one C.hyp.toAmalgamHyp _ (H.s3 C hy)) _ hād
  exact C.inf_centralizer_le_at hā ⟨h1, H.s2 C hy⟩

theorem s5 : ∀ y ∈ ballV V 3 (γ₁ G₀ G₁ G₂), ∀ x ∈ Vv V (p (critDist G₀ G₁ G₂ V)),
    y * x * y⁻¹ * x⁻¹ ∈ conjClosure V G₂ := by
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hb := H.b7
  have hG := C.hyp.gen
  have hN := C.hyp.normalizes
  obtain ⟨hYab, hWY, hYG, hGY⟩ := H.y3_basic C
  have hα : vtype (p b) = true := H.vtype_odd hG le_rfl H.odd
  have hW : Vv V (γ₁ G₀ G₁ G₂) = conjClosure V G₂ := Vv_γ₁ C.hyp.le₂ hN
  have hWab : IsElemAbelian 2 (conjClosure V G₂) := by
    rw [← hW]; exact SzVB.isElemAbelian_Vv_of_vtype C.toGeoCtx vtype_γ₁ (by omega)
  have hZW := (H.s1 C).1
  have hW'β : Vv V (p b) ≤ G₂ := by
    have := SzVB.Vv_le_stab_of_dist_le_B C.toGeoCtx hα (x := γ₁ G₀ G₁ G₂)
      (by rw [CosetGeom.dist_comm, ← H.p1, H.dist_eq (by omega) le_rfl]; omega)
    rwa [stab_γ₁ C.hyp.le₂] at this
  have hW'NW : ∀ x ∈ Vv V (p b), ∀ a ∈ conjClosure V G₂, x * a * x⁻¹ ∈ conjClosure V G₂ := by
    intro x hx a ha
    have hxN : x ∈ Subgroup.normalizer (conjClosure V G₂ : Set G) := by
      have := stab_le_normalizer_Vv hN (γ₁ G₀ G₁ G₂)
        (show x ∈ stab (γ₁ G₀ G₁ G₂) by rw [stab_γ₁ C.hyp.le₂]; exact hW'β hx)
      rwa [hW] at this
    exact (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
  have hW'NY : ∀ x ∈ Vv V (p b), ∀ a ∈ ballV V 3 (γ₁ G₀ G₁ G₂),
      x * a * x⁻¹ ∈ ballV V 3 (γ₁ G₀ G₁ G₂) := fun x hx a ha =>
    (Subgroup.mem_normalizer_iff.mp (hGY (hW'β hx)) a).mp ha
  have hYα : ballV V 3 (γ₁ G₀ G₁ G₂) ≤ stab (p b) := by
    intro y hy
    have hāα : dist (p (b - 1)) (p b) ≤ 1 := by rw [H.dist_eq (by omega) le_rfl]; omega
    exact mem_ballStab.mp (pCoreOf_stab_le_ballStab_one C.hyp.toAmalgamHyp _ (H.s4 C hy)) _ hāα
  have hZ : ∀ h ∈ pCoreOf 2 (stab (p b)), ∀ x ∈ Vv V (p b),
      h * x * h⁻¹ * x⁻¹ ∈ conjClosure V G₂ := by
    intro h hh x hx
    have h1 : x * h * x⁻¹ * h⁻¹ ∈ Zv z (p b) := by
      apply SzVB.commutator_Vv_pCoreOf_le_Zv C.toGeoCtx hα
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hx hh
    have e : h * x * h⁻¹ * x⁻¹ = (x * h * x⁻¹ * h⁻¹)⁻¹ := by group
    rw [e]; exact hZW (inv_mem h1)
  have hVQ : ¬ V ≤ pCoreOf 2 (stab (p b)) := fun h =>
    H.crit (h.trans (pCoreOf_stab_le_ballStab_one C.hyp.toAmalgamHyp _))
  obtain ⟨w, hwV, hwQ⟩ := IsConcreteLE.not_le_iff_exists.mp hVQ
  have hwW : w ∈ conjClosure V G₂ := le_conjClosure V G₂ hwV
  have hwY : w ∈ ballV V 3 (γ₁ G₀ G₁ G₂) := hWY hwW
  have hw2 : w * w = 1 := by
    have := isElemAbelian_pow_eq_one hWab hwW; rwa [pow_two] at this
  intro y hy x hx
  have hy2 : y * y = 1 := by
    have := isElemAbelian_pow_eq_one hYab hy; rwa [pow_two] at this
  have hq : ∀ a ∈ Vv V (p b), w * (y * a * y⁻¹ * a⁻¹) * w⁻¹ = y * a * y⁻¹ * a⁻¹ := by
    intro a ha
    have hmem : y * a * y⁻¹ * a⁻¹ ∈ ballV V 3 (γ₁ G₀ G₁ G₂) := by
      have h1 := hW'NY a ha y⁻¹ (inv_mem hy)
      have e1 : y * a * y⁻¹ * a⁻¹ = y * (a * y⁻¹ * a⁻¹) := by group
      rw [e1]; exact mul_mem hy h1
    have hc := isElemAbelian_comm hYab hwY hmem
    calc w * (y * a * y⁻¹ * a⁻¹) * w⁻¹ = y * a * y⁻¹ * a⁻¹ * w * w⁻¹ := by rw [hc]
      _ = y * a * y⁻¹ * a⁻¹ := by group
  rcases C.quad_pair_at hα (hYα hy) (hYα hwY) hy2 hw2 (isElemAbelian_comm hYab hy hwY) hq with
    h | h | h
  · exact hZ y h x hx
  · exact absurd h hwQ
  ·
    have hhY : y * w ∈ ballV V 3 (γ₁ G₀ G₁ G₂) := mul_mem hy hwY
    have hwx : w * x * w⁻¹ * x⁻¹ ∈ conjClosure V G₂ := by
      have h1 := hW'NW x hx w⁻¹ (inv_mem hwW)
      have e1 : w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
      rw [e1]; exact mul_mem hwW h1
    have hcomm := isElemAbelian_comm hYab hhY (hWY hwx)
    have ey : y = y * w * w := by rw [mul_assoc, hw2, mul_one]
    have e1 : y * x * y⁻¹ * x⁻¹ = (w * x * w⁻¹ * x⁻¹) * ((y * w) * x * (y * w)⁻¹ * x⁻¹) := by
      calc y * x * y⁻¹ * x⁻¹ = (y * w * w) * x * (y * w * w)⁻¹ * x⁻¹ := by rw [← ey]
        _ = (y * w) * (w * x * w⁻¹ * x⁻¹) * (y * w)⁻¹ *
            ((y * w) * x * (y * w)⁻¹ * x⁻¹) := by group
        _ = (w * x * w⁻¹ * x⁻¹) * (y * w) * (y * w)⁻¹ *
            ((y * w) * x * (y * w)⁻¹ * x⁻¹) := by rw [hcomm]
        _ = (w * x * w⁻¹ * x⁻¹) * ((y * w) * x * (y * w)⁻¹ * x⁻¹) := by group
    rw [e1]
    exact mul_mem hwx (hZ (y * w) h x hx)

end CritGeo

end CFSG.Quasithin.Kleidman.VBOdd
