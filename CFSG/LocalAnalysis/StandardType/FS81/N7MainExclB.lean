module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainSyl
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainInvol

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

private theorem nmh_mul_conj_sq {g g' t : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hgg' : g * g' = 1) (hg'g : g' * g = 1) (ht2 : t * t = 1) :
    (g * t * g') * (g * t * g') = 1 := by
  calc (g * t * g') * (g * t * g') = g * t * (g' * g) * t * g' := by noncomm_ring
    _ = g * (t * t) * g' := by rw [hg'g]; noncomm_ring
    _ = g * g' := by rw [ht2, mul_one]
    _ = 1 := hgg'

private theorem nmh_eq_zero_of_nmSgn_mulVec {C : Finset (Fin 8)} {w : Coords 8}
    (h : nmSgn C *ᵥ w = w) {j : Fin 8} (hj : j ∈ C) : w j = 0 := by
  have hc := congrFun h j
  rw [nmSgn_mulVec] at hc
  change (if j ∈ C then -w j else w j) = w j at hc
  rw [if_pos hj] at hc
  exact nmh_eq_zero_of_neg_eq_self hc.symm

private theorem nmh_nmSgn_mulVec_of_eq_zero {B C : Finset (Fin 8)} {w : Coords 8}
    (hB : B ⊆ C) (hw : ∀ j ∈ C, w j = 0) : nmSgn B *ᵥ w = w := by
  funext j
  rw [nmSgn_mulVec]
  change (if j ∈ B then -w j else w j) = w j
  by_cases hj : j ∈ B
  · rw [if_pos hj, hw j (hB hj)]
    exact neg_zero
  · rw [if_neg hj]

private theorem nmh_mem_v_fix
    {g g' y t M : Matrix (Fin 8) (Fin 8) (ZMod 3)} {A₀ : Finset (Fin 8)}
    (hg'g : g' * g = 1) (hM : M = g * t * g') (ht : t = nmSgn A₀)
    (hy : ∀ u : Coords 8, M *ᵥ u = -u → y *ᵥ u = u)
    {i : Fin 8} (hi : i ∈ A₀) :
    (g' * y * g) *ᵥ Pi.single i 1 = Pi.single i 1 := by
  have hte : t *ᵥ Pi.single i 1 = -Pi.single i 1 := by
    rw [ht]
    exact nmSgn_mulVec_single_of_mem hi
  have hg'ge : g' *ᵥ (g *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, hg'g, Matrix.one_mulVec]
  have hMe : M *ᵥ (g *ᵥ Pi.single i 1) = -(g *ᵥ Pi.single i 1) := by
    rw [hM]
    calc (g * t * g') *ᵥ (g *ᵥ Pi.single i 1)
        = g *ᵥ (t *ᵥ (g' *ᵥ (g *ᵥ Pi.single i 1))) := by
          simp only [← Matrix.mulVec_mulVec]
      _ = g *ᵥ (t *ᵥ Pi.single i 1) := by rw [hg'ge]
      _ = g *ᵥ (-Pi.single i 1) := by rw [hte]
      _ = -(g *ᵥ Pi.single i 1) := Matrix.mulVec_neg _ _
  have hye : y *ᵥ (g *ᵥ Pi.single i 1) = g *ᵥ Pi.single i 1 := hy _ hMe
  calc (g' * y * g) *ᵥ Pi.single i 1
      = g' *ᵥ (y *ᵥ (g *ᵥ Pi.single i 1)) := by
        simp only [← Matrix.mulVec_mulVec]
    _ = g' *ᵥ (g *ᵥ Pi.single i 1) := by rw [hye]
    _ = Pi.single i 1 := hg'ge

private theorem nmh_conj_comm {X : Type} [Group X] {x w z v : X}
    (hv : v = x⁻¹ * w * x) (hw : w * (x * z * x⁻¹) = (x * z * x⁻¹) * w) :
    v * z = z * v := by
  subst hv
  have h := (Commute.conj (show Commute w (x * z * x⁻¹) from hw) x⁻¹).eq
  have hz : x⁻¹ * (x * z * x⁻¹) * x = z := by group
  simpa [hz] using h

private theorem nmh_comm_sgn_mem {gv : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    {A₀ B : Finset (Fin 8)}
    (hfix : ∀ i ∈ A₀, gv *ᵥ Pi.single i 1 = Pi.single i 1)
    {i : Fin 8} (hi : i ∈ A₀) :
    (gv * nmSgn B) *ᵥ Pi.single i 1 = (nmSgn B * gv) *ᵥ Pi.single i 1 := by
  by_cases hiB : i ∈ B
  · calc (gv * nmSgn B) *ᵥ Pi.single i 1
        = gv *ᵥ (nmSgn B *ᵥ Pi.single i 1) :=
          (Matrix.mulVec_mulVec (Pi.single i 1) gv (nmSgn B)).symm
      _ = gv *ᵥ (-Pi.single i 1) := by rw [nmSgn_mulVec_single_of_mem hiB]
      _ = -(gv *ᵥ Pi.single i 1) := Matrix.mulVec_neg (Pi.single i 1) gv
      _ = -Pi.single i 1 := by rw [hfix i hi]
      _ = nmSgn B *ᵥ Pi.single i 1 := (nmSgn_mulVec_single_of_mem hiB).symm
      _ = nmSgn B *ᵥ (gv *ᵥ Pi.single i 1) := by rw [hfix i hi]
      _ = (nmSgn B * gv) *ᵥ Pi.single i 1 :=
        Matrix.mulVec_mulVec (Pi.single i 1) (nmSgn B) gv
  · calc (gv * nmSgn B) *ᵥ Pi.single i 1
        = gv *ᵥ (nmSgn B *ᵥ Pi.single i 1) :=
          (Matrix.mulVec_mulVec (Pi.single i 1) gv (nmSgn B)).symm
      _ = gv *ᵥ Pi.single i 1 := by rw [nmSgn_mulVec_single_of_notMem hiB]
      _ = Pi.single i 1 := hfix i hi
      _ = nmSgn B *ᵥ Pi.single i 1 := (nmSgn_mulVec_single_of_notMem hiB).symm
      _ = nmSgn B *ᵥ (gv *ᵥ Pi.single i 1) := by rw [hfix i hi]
      _ = (nmSgn B * gv) *ᵥ Pi.single i 1 :=
        Matrix.mulVec_mulVec (Pi.single i 1) (nmSgn B) gv

private theorem nmh_comm_sgn_notMem {gv t : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    {A₀ B : Finset (Fin 8)} (ht : t = nmSgn A₀) (hB : B ⊆ A₀)
    (hvt : gv * t = t * gv) {i : Fin 8} (hi : i ∉ A₀) :
    (gv * nmSgn B) *ᵥ Pi.single i 1 = (nmSgn B * gv) *ᵥ Pi.single i 1 := by
  have hiB : i ∉ B := fun h => hi (hB h)
  have hte : t *ᵥ Pi.single i 1 = Pi.single i 1 := by
    rw [ht]
    exact nmSgn_mulVec_single_of_notMem hi
  have htu : t *ᵥ (gv *ᵥ Pi.single i 1) = gv *ᵥ Pi.single i 1 := by
    calc t *ᵥ (gv *ᵥ Pi.single i 1)
        = (t * gv) *ᵥ Pi.single i 1 := Matrix.mulVec_mulVec (Pi.single i 1) t gv
      _ = (gv * t) *ᵥ Pi.single i 1 := by rw [← hvt]
      _ = gv *ᵥ (t *ᵥ Pi.single i 1) :=
          (Matrix.mulVec_mulVec (Pi.single i 1) gv t).symm
      _ = gv *ᵥ Pi.single i 1 := by rw [hte]
  have hBfix : nmSgn B *ᵥ (gv *ᵥ Pi.single i 1) = gv *ᵥ Pi.single i 1 :=
    nmh_nmSgn_mulVec_of_eq_zero hB
      (fun j hj => nmh_eq_zero_of_nmSgn_mulVec (ht ▸ htu) hj)
  calc (gv * nmSgn B) *ᵥ Pi.single i 1
      = gv *ᵥ (nmSgn B *ᵥ Pi.single i 1) :=
        (Matrix.mulVec_mulVec (Pi.single i 1) gv (nmSgn B)).symm
    _ = gv *ᵥ Pi.single i 1 := by rw [nmSgn_mulVec_single_of_notMem hiB]
    _ = nmSgn B *ᵥ (gv *ᵥ Pi.single i 1) := hBfix.symm
    _ = (nmSgn B * gv) *ᵥ Pi.single i 1 :=
        Matrix.mulVec_mulVec (Pi.single i 1) (nmSgn B) gv

private theorem nmh_comm_sgn {gv t : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    {A₀ B : Finset (Fin 8)} (ht : t = nmSgn A₀) (hB : B ⊆ A₀)
    (hvt : gv * t = t * gv)
    (hfix : ∀ i ∈ A₀, gv *ᵥ Pi.single i 1 = Pi.single i 1) :
    gv * nmSgn B = nmSgn B * gv := by
  apply Matrix.ext_of_mulVec_single
  intro i
  by_cases hi : i ∈ A₀
  · exact nmh_comm_sgn_mem hfix hi
  · exact nmh_comm_sgn_notMem ht hB hvt hi

private theorem nmh_klein_data {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {t : Matrix (Fin 8) (Fin 8) (ZMod 3)} (ht : t ∈ nmE6) {x : X}
    (h1 : S.ρ x * t * S.ρ x⁻¹ ∈ evenAll0 7) (h2 : S.ρ x * t * S.ρ x⁻¹ ∉ nmE6) :
    ∃ (A₀ : Finset (Fin 8)) (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) (w : X),
      0 ∉ A₀ ∧ A₀.card = 6 ∧ t = nmSgn A₀ ∧ S.ρ w = y ∧ y * y = 1 ∧ y.det = -1 ∧
        y * (S.ρ x * t * S.ρ x⁻¹) = (S.ρ x * t * S.ρ x⁻¹) * y ∧
        ∀ u : Coords 8, (S.ρ x * t * S.ρ x⁻¹) *ᵥ u = -u → y *ᵥ u = u := by
  classical
  obtain ⟨A₀, hA0, hA6, ht_eq⟩ := ht
  have htmem : t ∈ nmE6 := ⟨A₀, hA0, hA6, ht_eq⟩
  set g : Matrix (Fin 8) (Fin 8) (ZMod 3) := S.ρ x with hg
  set g' : Matrix (Fin 8) (Fin 8) (ZMod 3) := S.ρ x⁻¹ with hg'
  set M' : Matrix (Fin 8) (Fin 8) (ZMod 3) := g * t * g' with hM'
  have h1M : M' ∈ evenAll0 7 := by simpa [hM', hg, hg'] using h1
  have h2M : M' ∉ nmE6 := by simpa [hM', hg, hg'] using h2
  have hgg' : g * g' = 1 := by rw [hg, hg', ← map_mul, mul_inv_cancel, map_one]
  have hg'g : g' * g = 1 := by rw [hg, hg', ← map_mul, inv_mul_cancel, map_one]
  have ht2 : t * t = 1 := by rw [ht_eq]; exact nmSgn_mul_self A₀
  have hM2 : M' * M' = 1 := by
    rw [hM']
    exact nmh_mul_conj_sq hgg' hg'g ht2
  have h9 : nmFixCount M' = 9 := by
    have hc := nmFixCount_conj (M := t) hgg' hg'g
    rw [← hM'] at hc
    rw [hc, nmFixCount_of_mem_nmE6 htmem]
  obtain ⟨y, hy, hy2, hyM, hydet, hyfix⟩ := nm_klein h1M hM2 h9 h2M
  obtain ⟨w, hw⟩ := S.surj_H1 y hy
  exact ⟨A₀, y, w, hA0, hA6, ht_eq, hw, hy2, hydet, hyM, hyfix⟩

private theorem nmh_build_v {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {t : Matrix (Fin 8) (Fin 8) (ZMod 3)} {A₀ : Finset (Fin 8)} {x w : X}
    {y : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hA6 : A₀.card = 6) (ht_eq : t = nmSgn A₀) (hw : S.ρ w = y)
    (hy2 : y * y = 1) (hydet : y.det = -1)
    (hyM : y * (S.ρ x * t * S.ρ x⁻¹) = (S.ρ x * t * S.ρ x⁻¹) * y)
    (hyfix : ∀ u : Coords 8, (S.ρ x * t * S.ρ x⁻¹) *ᵥ u = -u → y *ᵥ u = u) :
    ∃ v : X, v * v = 1 ∧ (S.ρ v).det = -1 ∧ S.ρ v * t = t * S.ρ v ∧
      ∀ i ∈ A₀, S.ρ v *ᵥ Pi.single i 1 = Pi.single i 1 := by
  classical
  have htF : t ∈ nmF := by
    rw [ht_eq]
    exact nmSgn_mem_nmF (by rw [hA6]; exact ⟨3, rfl⟩)
  obtain ⟨z, hz⟩ := S.exists_of_mem_nmF htF
  have hwcomm : w * (x * z * x⁻¹) = (x * z * x⁻¹) * w := by
    apply S.ρ_inj
    simp only [map_mul, hw, hz]
    exact hyM
  set v : X := x⁻¹ * w * x with hv
  have hρv : S.ρ v = S.ρ x⁻¹ * y * S.ρ x := by
    rw [hv]
    simp only [map_mul, hw]
  have hvz : v * z = z * v := nmh_conj_comm hv hwcomm
  have hvt : S.ρ v * t = t * S.ρ v := by
    have h := congrArg S.ρ hvz
    simpa [map_mul, hz, hρv] using h
  have hw2 : w * w = 1 := by
    apply S.ρ_inj
    rw [map_mul, map_one, hw]
    exact hy2
  have hgg' : S.ρ x * S.ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hg'g : S.ρ x⁻¹ * S.ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hv2 : v * v = 1 := by
    have h : v * v = x⁻¹ * (w * w) * x := by rw [hv]; group
    rw [h, hw2]
    group
  have hdetv : (S.ρ v).det = -1 := by
    rw [hρv, Matrix.det_mul_comm (S.ρ x⁻¹ * y) (S.ρ x), ← mul_assoc, hgg', one_mul]
    exact hydet
  have hvfix : ∀ i ∈ A₀, S.ρ v *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro i hi
    rw [hρv]
    exact nmh_mem_v_fix hg'g rfl ht_eq hyfix hi
  exact ⟨v, hv2, hdetv, hvt, hvfix⟩

theorem nm_exclB {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    (hY : ∀ x : X, (∀ a, a ∈ S.Fgrp ↔ x * a * x⁻¹ ∈ S.Fgrp) → S.ρ x ∈ evenAll0 7)
    {t : Matrix (Fin 8) (Fin 8) (ZMod 3)} (ht : t ∈ nmE6) {x : X}
    (h1 : S.ρ x * t * S.ρ x⁻¹ ∈ evenAll0 7) (h2 : S.ρ x * t * S.ρ x⁻¹ ∉ nmE6) : False := by
  obtain ⟨A₀, y, w, hA0, hA6, ht_eq, hw, hy2, hydet, hyM, hyfix⟩ := nmh_klein_data S ht h1 h2
  obtain ⟨v, hv2, hdetv, hvt, hvfix⟩ :=
    nmh_build_v S hA6 ht_eq hw hy2 hydet hyM hyfix
  have hc : ∀ x' : X, (∃ B : Finset (Fin 8), B ⊆ A₀ ∧ Even B.card ∧ S.ρ x' = nmSgn B) →
      v * x' = x' * v := by
    rintro x' ⟨B, hB, -, hxB⟩
    apply S.ρ_inj
    rw [map_mul, map_mul, hxB]
    exact nmh_comm_sgn ht_eq hB hvt hvfix
  have hdet1 := nm_det_one_of_centralizer S hY hA0 hA6 hv2 hc
  rw [hdetv] at hdet1
  exact absurd hdet1 (by decide)

end CFSG.StandardType.FrameRoute.FS81

end
