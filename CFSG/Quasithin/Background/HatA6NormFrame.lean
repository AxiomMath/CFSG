module

public import CFSG.Quasithin.Background.HatA6NormColl

public section

namespace CFSG.Quasithin.HatA6

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
open CFSG.Quasithin.H13.Orbit

@[expose] def ovalVec : Fin 6 → Fin 3 → FieldFour :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1], ![1, ω, ω₂], ![1, ω₂, ω]]

@[expose] def ovalStd : Set (Multiplicative (Fin 3 → FieldFour)) :=
  {c | ∃ k : FieldFour, k ≠ 0 ∧ ∃ i : Fin 6, Multiplicative.toAdd c = k • ovalVec i}

private theorem ovalVec_smul_sep (k k' : FieldFour) (i i' : Fin 6) (hk : k ≠ 0)
    (hk' : k' ≠ 0) (h : k • ovalVec i = k' • ovalVec i') : k = k' ∧ i = i' := by
  revert k k' i i'
  decide +kernel

theorem card_ovalStd : Nat.card ↥ovalStd = 18 := by
  have hbij : Function.Bijective (fun p : {k : FieldFour // k ≠ 0} × Fin 6 =>
      (⟨Multiplicative.ofAdd (p.1.1 • ovalVec p.2), p.1.1, p.1.2, p.2, rfl⟩ : ↥ovalStd)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
      have hval : k • ovalVec i = k' • ovalVec i' := by
        simpa using congrArg (fun x : ↥ovalStd =>
          Multiplicative.toAdd (x : Multiplicative (Fin 3 → FieldFour))) h
      obtain ⟨rfl, rfl⟩ := ovalVec_smul_sep k k' i i' hk hk' hval
      rfl
    · rintro ⟨c, k, hk, i, hi⟩
      refine ⟨⟨⟨k, hk⟩, i⟩, ?_⟩
      apply Subtype.ext
      change Multiplicative.ofAdd (k • ovalVec i) = c
      rw [← hi, ofAdd_toAdd]
  calc Nat.card ↥ovalStd = Nat.card ({k : FieldFour // k ≠ 0} × Fin 6) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card {k : FieldFour // k ≠ 0} * Nat.card (Fin 6) := by rw [Nat.card_prod]
    _ = 3 * 6 := by
        have h3 : Nat.card {k : FieldFour // k ≠ 0} = 3 := by
          rw [Nat.card_eq_fintype_card]
          decide
        rw [h3, Nat.card_fin]
    _ = 18 := by norm_num

private def offLines (d : Fin 3 → FieldFour) : Prop :=
  ∀ i j : Fin 6, i < 4 → j < 4 → i ≠ j → ∀ a b : FieldFour,
    d ≠ a • ovalVec i + b • ovalVec j

private instance (d : Fin 3 → FieldFour) : Decidable (offLines d) := by
  unfold offLines
  infer_instance

private def onOval45 (d : Fin 3 → FieldFour) : Prop :=
  ∃ k : FieldFour, k ≠ 0 ∧ (d = k • ovalVec 4 ∨ d = k • ovalVec 5)

private instance (d : Fin 3 → FieldFour) : Decidable (onOval45 d) := by
  unfold onOval45
  infer_instance

private theorem offLines_imp :
    ∀ d0 d1 d2 : FieldFour, offLines ![d0, d1, d2] → onOval45 ![d0, d1, d2] := by
  decide +kernel

theorem eq_ovalVec_of_not_mem_lines (d : Fin 3 → FieldFour)
    (hd : ∀ i j : Fin 6, i < 4 → j < 4 → i ≠ j → ∀ a b : FieldFour,
      d ≠ a • ovalVec i + b • ovalVec j) :
    ∃ k : FieldFour, k ≠ 0 ∧ (d = k • ovalVec 4 ∨ d = k • ovalVec 5) := by
  have hdvec : (![d 0, d 1, d 2] : Fin 3 → FieldFour) = d := by
    funext i
    fin_cases i <;> rfl
  have hd' : offLines ![d 0, d 1, d 2] := by
    rw [hdvec]
    exact hd
  have h := offLines_imp (d 0) (d 1) (d 2) hd'
  rwa [hdvec] at h

variable {W : Type} [CommGroup W] [Finite W] {K : Subgroup (MulAut W)} {z : ↥K} {f : W}

private theorem fsmul_mul_self {V : Type} [CommGroup V] {z : MulAut V}
    (hsq : ∀ v : V, v * v = 1) (c : FieldFour) (v : V) :
    fsmul z c v * fsmul z c v = 1 := by
  rw [← fsmul_add hsq, CharTwo.add_self_eq_zero, fsmul_zero]

private theorem fsmul_inv_fsmul {V : Type} [CommGroup V] {z : MulAut V}
    (hsq : ∀ v : V, v * v = 1) (hzz : ∀ v : V, z (z v) = v * z v)
    {c : FieldFour} (hc : c ≠ 0) (v : V) : fsmul z c⁻¹ (fsmul z c v) = v := by
  rw [← fsmul_mul hsq hzz, inv_mul_cancel₀ hc, fsmul_one]

private theorem fsmul_mem_orbit {V : Type} [CommGroup V] {z : MulAut V} {O : Set V}
    (hzz : ∀ v : V, z (z v) = v * z v) (hzO : ∀ w ∈ O, z w ∈ O)
    {c : FieldFour} (hc : c ≠ 0) {w : V} (hw : w ∈ O) : fsmul z c w ∈ O := by
  have hc' : c = 1 ∨ c = FieldFour.ω ∨ c = FieldFour.ω₂ := by
    revert c
    decide
  rcases hc' with rfl | rfl | rfl
  · rwa [fsmul_one]
  · rw [fsmul_ω]
    exact hzO w hw
  · rw [fsmul_ω₂ hzz]
    exact hzO _ (hzO w hw)

private theorem coordHom_injective_of_three {V : Type} [CommGroup V] {z : MulAut V}
    {hsq : ∀ v : V, v * v = 1} {hzz : ∀ v : V, z (z v) = v * z v} {O : Set V}
    (hz3 : z ^ 3 = 1) (hone : (1 : V) ∉ O) {p : Fin 3 → V}
    (h0 : p 0 ∈ O) (h1 : p 1 ∈ O) (h2 : p 2 ∈ O)
    (h01 : pt z (p 0) ≠ pt z (p 1)) (h02 : pt z (p 0) ≠ pt z (p 2))
    (h12 : pt z (p 1) ≠ pt z (p 2))
    (hNC : ∀ {u v w : V}, u ∈ O → v ∈ O → w ∈ O → pt z u ≠ pt z v → pt z u ≠ pt z w →
      pt z v ≠ pt z w → ∀ a b : FieldFour, u ≠ fsmul z a v * fsmul z b w) :
    Function.Injective (coordHom hsq z p) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have h : fsmul z (Multiplicative.toAdd c 0) (p 0) *
      fsmul z (Multiplicative.toAdd c 1) (p 1) *
      fsmul z (Multiplicative.toAdd c 2) (p 2) = 1 := by
    have h' := hc
    rw [coordHom_apply] at h'
    exact h'
  by_cases hc2 : Multiplicative.toAdd c 2 = 0
  · simp only [hc2, fsmul_zero, mul_one] at h
    by_cases hc1 : Multiplicative.toAdd c 1 = 0
    · simp only [hc1, fsmul_zero, mul_one] at h
      by_cases hc0 : Multiplicative.toAdd c 0 = 0
      · have hcz : Multiplicative.toAdd c = 0 := by
          funext i
          fin_cases i
          · simpa using hc0
          · simpa using hc1
          · simpa using hc2
        rw [← ofAdd_toAdd c, hcz, ofAdd_zero]
      · have hA : fsmul z (Multiplicative.toAdd c 0) (p 0) = 1 := by
          simpa using h
        have hp : p 0 = 1 := by
          calc p 0 = fsmul z (Multiplicative.toAdd c 0)⁻¹
                (fsmul z (Multiplicative.toAdd c 0) (p 0)) :=
                (fsmul_inv_fsmul hsq hzz hc0 (p 0)).symm
            _ = fsmul z (Multiplicative.toAdd c 0)⁻¹ 1 := by rw [hA]
            _ = 1 := fsmul_one_right z _
        exact absurd (hp ▸ h0) hone
    · have hAB : fsmul z (Multiplicative.toAdd c 0) (p 0) *
          fsmul z (Multiplicative.toAdd c 1) (p 1) = 1 := by
        simpa using h
      have hB : fsmul z (Multiplicative.toAdd c 1) (p 1) =
          fsmul z (Multiplicative.toAdd c 0) (p 0) :=
        (inv_eq_of_mul_eq_one_right (fsmul_mul_self hsq _ _)).symm.trans
          (inv_eq_of_mul_eq_one_left hAB)
      have hp : p 1 = fsmul z ((Multiplicative.toAdd c 1)⁻¹ *
          Multiplicative.toAdd c 0) (p 0) := by
        calc p 1 = fsmul z (Multiplicative.toAdd c 1)⁻¹
              (fsmul z (Multiplicative.toAdd c 1) (p 1)) :=
              (fsmul_inv_fsmul hsq hzz hc1 (p 1)).symm
          _ = fsmul z (Multiplicative.toAdd c 1)⁻¹
              (fsmul z (Multiplicative.toAdd c 0) (p 0)) := by rw [hB]
          _ = fsmul z ((Multiplicative.toAdd c 1)⁻¹ * Multiplicative.toAdd c 0) (p 0) :=
              (fsmul_mul hsq hzz _ _ _).symm
      by_cases hc10 : (Multiplicative.toAdd c 1)⁻¹ * Multiplicative.toAdd c 0 = 0
      · have hp1 : p 1 = 1 := by rw [hp, hc10, fsmul_zero]
        exact absurd (hp1 ▸ h1) hone
      · refine absurd ?_ h01.symm
        rw [hp]
        exact (pt_eq_pt_iff hz3).2 (fsmul_mem_pt hzz hc10 (p 0))
  · have hC : fsmul z (Multiplicative.toAdd c 2) (p 2) =
        fsmul z (Multiplicative.toAdd c 0) (p 0) *
          fsmul z (Multiplicative.toAdd c 1) (p 1) :=
      (inv_eq_of_mul_eq_one_right (fsmul_mul_self hsq _ _)).symm.trans
        (inv_eq_of_mul_eq_one_left h)
    have hp : p 2 = fsmul z ((Multiplicative.toAdd c 2)⁻¹ *
          Multiplicative.toAdd c 0) (p 0) *
        fsmul z ((Multiplicative.toAdd c 2)⁻¹ * Multiplicative.toAdd c 1) (p 1) := by
      calc p 2 = fsmul z (Multiplicative.toAdd c 2)⁻¹
            (fsmul z (Multiplicative.toAdd c 2) (p 2)) :=
            (fsmul_inv_fsmul hsq hzz hc2 (p 2)).symm
        _ = fsmul z (Multiplicative.toAdd c 2)⁻¹
            (fsmul z (Multiplicative.toAdd c 0) (p 0) *
              fsmul z (Multiplicative.toAdd c 1) (p 1)) := by rw [hC]
        _ = fsmul z (Multiplicative.toAdd c 2)⁻¹
              (fsmul z (Multiplicative.toAdd c 0) (p 0)) *
            fsmul z (Multiplicative.toAdd c 2)⁻¹
              (fsmul z (Multiplicative.toAdd c 1) (p 1)) :=
            fsmul_mul_right z _ _ _
        _ = fsmul z ((Multiplicative.toAdd c 2)⁻¹ * Multiplicative.toAdd c 0) (p 0) *
            fsmul z ((Multiplicative.toAdd c 2)⁻¹ * Multiplicative.toAdd c 1) (p 1) := by
            rw [fsmul_mul hsq hzz, fsmul_mul hsq hzz]
    exact absurd hp (hNC h2 h0 h1 h02.symm h12.symm h01
      ((Multiplicative.toAdd c 2)⁻¹ * Multiplicative.toAdd c 0)
      ((Multiplicative.toAdd c 2)⁻¹ * Multiplicative.toAdd c 1))

private theorem exists_smul_of_coord_mem_pt {V : Type} [CommGroup V] {z : MulAut V}
    {hsq : ∀ v : V, v * v = 1} {hzz : ∀ v : V, z (z v) = v * z v}
    {v : Fin 3 → V} (hb : Function.Injective (coordHom hsq z v))
    {e d : Fin 3 → FieldFour} {x : V} (hx : x = coordHom hsq z v d)
    (hmem : x ∈ pt z (coordHom hsq z v (Multiplicative.ofAdd e))) :
    ∃ k : FieldFour, k ≠ 0 ∧ Multiplicative.toAdd d = k • e := by
  have hωω : FieldFour.ω * FieldFour.ω = FieldFour.ω₂ := by
    rw [← pow_two, FieldFour.ω_sq]
  simp only [pt, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · refine ⟨1, one_ne_zero, ?_⟩
    have hde : d = Multiplicative.ofAdd e := hb (hx.symm.trans h)
    rw [hde, toAdd_ofAdd, one_smul]
  · refine ⟨FieldFour.ω, FieldFour.ω_ne_zero, ?_⟩
    have hz : z (coordHom hsq z v (Multiplicative.ofAdd e)) =
        coordHom hsq z v (Multiplicative.ofAdd (FieldFour.ω • e)) :=
      (coordHom_ω hsq hzz v (Multiplicative.ofAdd e)).symm
    have hde : d = Multiplicative.ofAdd (FieldFour.ω • e) :=
      hb (hx.symm.trans (h.trans hz))
    rw [hde, toAdd_ofAdd]
  · refine ⟨FieldFour.ω₂, FieldFour.ω₂_ne_zero, ?_⟩
    have hz1 : z (coordHom hsq z v (Multiplicative.ofAdd e)) =
        coordHom hsq z v (Multiplicative.ofAdd (FieldFour.ω • e)) :=
      (coordHom_ω hsq hzz v (Multiplicative.ofAdd e)).symm
    have hz2 : z (coordHom hsq z v (Multiplicative.ofAdd (FieldFour.ω • e))) =
        coordHom hsq z v (Multiplicative.ofAdd (FieldFour.ω • (FieldFour.ω • e))) := by
      simpa only [toAdd_ofAdd] using
        (coordHom_ω hsq hzz v (Multiplicative.ofAdd (FieldFour.ω • e))).symm
    have hzz' : z (z (coordHom hsq z v (Multiplicative.ofAdd e))) =
        coordHom hsq z v (Multiplicative.ofAdd (FieldFour.ω₂ • e)) := by
      rw [hz1, hz2, smul_smul, hωω]
    have hde : d = Multiplicative.ofAdd (FieldFour.ω₂ • e) :=
      hb (hx.symm.trans (h.trans hzz'))
    rw [hde, toAdd_ofAdd]

private theorem coordHom_smul_apply {V : Type} [CommGroup V] {z : MulAut V}
    {hsq : ∀ v : V, v * v = 1} (hzz : ∀ v : V, z (z v) = v * z v)
    (v : Fin 3 → V) (k : FieldFour) (e : Fin 3 → FieldFour) :
    coordHom hsq z v (Multiplicative.ofAdd (k • e)) =
      fsmul z k (coordHom hsq z v (Multiplicative.ofAdd e)) := by
  simpa only [toAdd_ofAdd] using
    coordHom_smul (hsq := hsq) (hzz := hzz) v k (Multiplicative.ofAdd e)

theorem Setup.exists_frame (S : Setup W K z f) :
    ∃ v : Fin 3 → W, Function.Bijective (coordHom S.sq (z : MulAut W) v) ∧
      orbitIn K f = coordHom S.sq (z : MulAut W) v '' ovalStd := by
  have hsq : ∀ w : W, w * w = 1 := S.sq
  have hzz : ∀ w : W, (z : MulAut W) ((z : MulAut W) w) = w * (z : MulAut W) w := S.zz
  let epts := Finite.equivFinOfCardEq S.card_points
  let h46 : 4 ≤ 6 := by omega
  let P : Fin 4 → ↥(points (z : MulAut W) (orbitIn K f)) := fun i => epts.symm (Fin.castLE h46 i)
  have hP : Function.Injective P := by
    intro i j hij
    exact Fin.castLE_injective h46 (epts.symm.injective hij)
  have hex : ∀ i : Fin 4, ∃ u : W, u ∈ orbitIn K f ∧
      pt (z : MulAut W) u = (P i : Set W) := fun i => (P i).2
  choose w hw hpt using hex
  have hwne : ∀ i j : Fin 4, i ≠ j →
      pt (z : MulAut W) (w i) ≠ pt (z : MulAut W) (w j) := by
    intro i j hij h
    have hsets : (P i : Set W) = (P j : Set W) := by
      rw [← hpt i, ← hpt j]
      exact h
    exact hij (hP (Subtype.ext hsets))
  have hinj3 : Function.Injective (coordHom hsq (z : MulAut W) ![w 0, w 1, w 2]) :=
    coordHom_injective_of_three (hsq := hsq) (hzz := hzz) S.pow_three S.one_not_mem_orbit
      (p := ![w 0, w 1, w 2]) (hw 0) (hw 1) (hw 2) (hwne 0 1 (by decide))
      (hwne 0 2 (by decide)) (hwne 1 2 (by decide)) S.not_collinear
  have hb3 : Function.Bijective (coordHom hsq (z : MulAut W) ![w 0, w 1, w 2]) :=
    (Nat.bijective_iff_injective_and_card _).2
      ⟨hinj3, by rw [card_coords, S.card]; norm_num⟩
  obtain ⟨c3, hc3⟩ := hb3.surjective (w 3)
  let a0 : FieldFour := Multiplicative.toAdd c3 0
  let a1 : FieldFour := Multiplicative.toAdd c3 1
  let a2 : FieldFour := Multiplicative.toAdd c3 2
  have hceq : fsmul (z : MulAut W) a0 (w 0) * fsmul (z : MulAut W) a1 (w 1) *
      fsmul (z : MulAut W) a2 (w 2) = w 3 := by
    have h' := hc3
    rw [coordHom_apply] at h'
    exact h'
  have ha0 : a0 ≠ 0 := by
    intro h
    simp only [h, fsmul_zero, one_mul] at hceq
    exact (S.not_collinear (hw 3) (hw 1) (hw 2) (hwne 3 1 (by decide))
      (hwne 3 2 (by decide)) (hwne 1 2 (by decide)) a1 a2) hceq.symm
  have ha1 : a1 ≠ 0 := by
    intro h
    simp only [h, fsmul_zero, mul_one] at hceq
    exact (S.not_collinear (hw 3) (hw 0) (hw 2) (hwne 3 0 (by decide))
      (hwne 3 2 (by decide)) (hwne 0 2 (by decide)) a0 a2) hceq.symm
  have ha2 : a2 ≠ 0 := by
    intro h
    simp only [h, fsmul_zero, mul_one] at hceq
    exact (S.not_collinear (hw 3) (hw 0) (hw 1) (hwne 3 0 (by decide))
      (hwne 3 1 (by decide)) (hwne 0 1 (by decide)) a0 a1) hceq.symm
  let v : Fin 3 → W :=
    ![fsmul (z : MulAut W) a0 (w 0), fsmul (z : MulAut W) a1 (w 1),
      fsmul (z : MulAut W) a2 (w 2)]
  let fv : Fin 4 → W := ![v 0, v 1, v 2, w 3]
  have hfvO : ∀ i : Fin 4, fv i ∈ orbitIn K f := by
    intro i
    fin_cases i
    · exact fsmul_mem_orbit (O := orbitIn K f) hzz (fun u hu => S.z_mem_orbit hu)
        ha0 (hw 0)
    · exact fsmul_mem_orbit (O := orbitIn K f) hzz (fun u hu => S.z_mem_orbit hu)
        ha1 (hw 1)
    · exact fsmul_mem_orbit (O := orbitIn K f) hzz (fun u hu => S.z_mem_orbit hu)
        ha2 (hw 2)
    · exact hw 3
  have hfvpt : ∀ i : Fin 4,
      pt (z : MulAut W) (fv i) = pt (z : MulAut W) (w i) := by
    intro i
    fin_cases i
    · exact (pt_eq_pt_iff S.pow_three).2 (fsmul_mem_pt hzz ha0 (w 0))
    · exact (pt_eq_pt_iff S.pow_three).2 (fsmul_mem_pt hzz ha1 (w 1))
    · exact (pt_eq_pt_iff S.pow_three).2 (fsmul_mem_pt hzz ha2 (w 2))
    · rfl
  have hfvne : ∀ i j : Fin 4, i ≠ j →
      pt (z : MulAut W) (fv i) ≠ pt (z : MulAut W) (fv j) := by
    intro i j hij h
    exact hwne i j hij (by rw [← hfvpt i, ← hfvpt j]; exact h)
  have hinjv : Function.Injective (coordHom hsq (z : MulAut W) v) :=
    coordHom_injective_of_three (hsq := hsq) (hzz := hzz) S.pow_three S.one_not_mem_orbit
      (p := v) (hfvO 0) (hfvO 1) (hfvO 2) (hfvne 0 1 (by decide))
      (hfvne 0 2 (by decide)) (hfvne 1 2 (by decide)) S.not_collinear
  have hbv : Function.Bijective (coordHom hsq (z : MulAut W) v) :=
    (Nat.bijective_iff_injective_and_card _).2
      ⟨hinjv, by rw [card_coords, S.card]; norm_num⟩
  let fc : Fin 4 → Fin 3 → FieldFour := ![ovalVec 0, ovalVec 1, ovalVec 2, ovalVec 3]
  have hfc6 : ∀ (i : Fin 6) (hi : i < 4), fc ⟨i, hi⟩ = ovalVec i := by
    intro i hi
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
  have hfc4 : ∀ i : Fin 4, fc i = ovalVec (Fin.castLE h46 i) := by
    intro i
    fin_cases i <;> rfl
  have hframe : ∀ i : Fin 4,
      coordHom hsq (z : MulAut W) v (Multiplicative.ofAdd (fc i)) = fv i := by
    intro i
    fin_cases i
    · simp [fc, fv, v, ovalVec, coordHom_apply, fsmul_one, fsmul_zero]
    · simp [fc, fv, v, ovalVec, coordHom_apply, fsmul_one, fsmul_zero]
    · simp [fc, fv, v, ovalVec, coordHom_apply, fsmul_one, fsmul_zero]
    · simp [fc, fv, v, ovalVec, coordHom_apply, fsmul_one, hceq]
  have hsub : orbitIn K f ⊆ coordHom hsq (z : MulAut W) v '' ovalStd := by
    intro x hx
    obtain ⟨d, rfl⟩ := hbv.surjective x
    suffices hd : d ∈ ovalStd from ⟨d, hd, rfl⟩
    have hframeCase : ∀ i : Fin 4,
        pt (z : MulAut W) (coordHom hsq (z : MulAut W) v d) = pt (z : MulAut W) (fv i) →
        ∃ k : FieldFour, k ≠ 0 ∧ Multiplicative.toAdd d = k • fc i := by
      intro i hxi
      have hmem : coordHom hsq (z : MulAut W) v d ∈ pt (z : MulAut W) (fv i) :=
        (pt_eq_pt_iff S.pow_three).1 hxi
      have hfve : fv i = coordHom hsq (z : MulAut W) v (Multiplicative.ofAdd (fc i)) :=
        (hframe i).symm
      rw [hfve] at hmem
      exact exists_smul_of_coord_mem_pt (hsq := hsq) (hzz := hzz) hbv.injective rfl hmem
    by_cases hx0 : pt (z : MulAut W) (coordHom hsq (z : MulAut W) v d) =
        pt (z : MulAut W) (fv 0)
    · obtain ⟨k, hk, hkd⟩ := hframeCase 0 hx0
      exact ⟨k, hk, Fin.castLE h46 0, by rwa [hfc4 0] at hkd⟩
    by_cases hx1 : pt (z : MulAut W) (coordHom hsq (z : MulAut W) v d) =
        pt (z : MulAut W) (fv 1)
    · obtain ⟨k, hk, hkd⟩ := hframeCase 1 hx1
      exact ⟨k, hk, Fin.castLE h46 1, by rwa [hfc4 1] at hkd⟩
    by_cases hx2 : pt (z : MulAut W) (coordHom hsq (z : MulAut W) v d) =
        pt (z : MulAut W) (fv 2)
    · obtain ⟨k, hk, hkd⟩ := hframeCase 2 hx2
      exact ⟨k, hk, Fin.castLE h46 2, by rwa [hfc4 2] at hkd⟩
    by_cases hx3 : pt (z : MulAut W) (coordHom hsq (z : MulAut W) v d) =
        pt (z : MulAut W) (fv 3)
    · obtain ⟨k, hk, hkd⟩ := hframeCase 3 hx3
      exact ⟨k, hk, Fin.castLE h46 3, by rwa [hfc4 3] at hkd⟩
    have hoff : offLines (Multiplicative.toAdd d) := by
      intro i j hi hj hij a b hEq
      have hi' : (⟨i, hi⟩ : Fin 4) ≠ ⟨j, hj⟩ := by
        intro h
        exact hij (Fin.ext (by simpa using congrArg Fin.val h))
      have hnei : pt (z : MulAut W) (coordHom hsq (z : MulAut W) v d) ≠
          pt (z : MulAut W) (fv ⟨i, hi⟩) := by
        fin_cases i
        · exact hx0
        · exact hx1
        · exact hx2
        · exact hx3
        · exact absurd hi (by decide)
        · exact absurd hi (by decide)
      have hnej : pt (z : MulAut W) (coordHom hsq (z : MulAut W) v d) ≠
          pt (z : MulAut W) (fv ⟨j, hj⟩) := by
        fin_cases j
        · exact hx0
        · exact hx1
        · exact hx2
        · exact hx3
        · exact absurd hj (by decide)
        · exact absurd hj (by decide)
      have hxeq : coordHom hsq (z : MulAut W) v d =
          fsmul (z : MulAut W) a (fv ⟨i, hi⟩) *
            fsmul (z : MulAut W) b (fv ⟨j, hj⟩) := by
        calc coordHom hsq (z : MulAut W) v d
            = coordHom hsq (z : MulAut W) v
                (Multiplicative.ofAdd (a • ovalVec i + b • ovalVec j)) := by
              rw [← ofAdd_toAdd d, hEq]
          _ = coordHom hsq (z : MulAut W) v
                (Multiplicative.ofAdd (a • ovalVec i) *
                  Multiplicative.ofAdd (b • ovalVec j)) := by rw [ofAdd_add]
          _ = coordHom hsq (z : MulAut W) v (Multiplicative.ofAdd (a • ovalVec i)) *
                coordHom hsq (z : MulAut W) v
                  (Multiplicative.ofAdd (b • ovalVec j)) := map_mul _ _ _
          _ = fsmul (z : MulAut W) a
                (coordHom hsq (z : MulAut W) v
                  (Multiplicative.ofAdd (ovalVec i))) *
              fsmul (z : MulAut W) b
                (coordHom hsq (z : MulAut W) v
                  (Multiplicative.ofAdd (ovalVec j))) := by
              rw [coordHom_smul_apply hzz, coordHom_smul_apply hzz]
          _ = fsmul (z : MulAut W) a (fv ⟨i, hi⟩) *
                fsmul (z : MulAut W) b (fv ⟨j, hj⟩) := by
              simp only [← hfc6 i hi, ← hfc6 j hj, hframe]
      exact (S.not_collinear hx (hfvO ⟨i, hi⟩) (hfvO ⟨j, hj⟩) hnei hnej
        (hfvne ⟨i, hi⟩ ⟨j, hj⟩ hi') a b) hxeq
    obtain ⟨k, hk, hk4 | hk5⟩ := eq_ovalVec_of_not_mem_lines (Multiplicative.toAdd d) hoff
    · exact ⟨k, hk, 4, hk4⟩
    · exact ⟨k, hk, 5, hk5⟩
  have hOcard : (orbitIn K f).ncard = 18 := by
    rw [← Nat.card_coe_set_eq]
    exact S.card_orbit
  have himgcard : (coordHom hsq (z : MulAut W) v '' ovalStd).ncard = 18 := by
    rw [← Nat.card_coe_set_eq, Nat.card_image_of_injective hbv.injective]
    exact card_ovalStd
  refine ⟨v, hbv, ?_⟩
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [himgcard, hOcard]

end CFSG.Quasithin.HatA6

end
