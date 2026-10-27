module

public import CFSG.Timmesfeld.Moufang.P3

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates
open CFSG.Sporadic.Bridge.J2 (seedGroup)
open CFSG.Timmesfeld.Moufang.J2 (nativeGens nativeGens_relators)

variable {G : Type*} [Group G] {D : Set G}

private theorem commute_conj (g : G) {a b : G} (h : Commute a b) :
    Commute (g * a * g⁻¹) (g * b * g⁻¹) := by
  unfold Commute SemiconjBy at *
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

private theorem mul_mul_self_cancel {d : G} (hd2 : d * d = 1) (y : G) : d * (d * y) = y := by
  rw [← mul_assoc, hd2, one_mul]

theorem not_commute_of_orderOf_eq_five (hD : IsRootInvolutionSet D) {d c : G} (hd : d ∈ D)
    (hc : c ∈ D) (h5 : orderOf (d * c) = 5) : ¬ Commute d c := fun hdc => by
  have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hd)
    (hD.mul_self_eq_one hc)).1 hdc)
  rw [h5] at this
  exact absurd this (by norm_num)

theorem odd_of_orderOf_eq_five {d c : G} (h5 : orderOf (d * c) = 5) : Odd (orderOf (d * c)) := by
  rw [h5]; decide

theorem false_of_commute_of_five (h : Hyp G D) (hNP : NoPolar D) {d c f : G} (hd : d ∈ D)
    (hc : c ∈ D) (h5 : orderOf (d * c) = 5) (hf : f ∈ D) (hdf : Commute d f)
    (hfc : Commute f c) : False := by
  have hD := h.root
  have hdc := not_commute_of_orderOf_eq_five hD hd hc h5
  have hne : d ≠ f := fun e => hdc (e ▸ hfc)
  exact not_commute_of_collinear hD hd hc hdc (odd_of_orderOf_eq_five h5) hf hdf
    (hNP d hd f hf hdf hne) hfc

theorem exists_order_three_point (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hQ : CommLambda D) (hL : LL5 D) {d c y : G} (hd : d ∈ D) (hc : c ∈ D)
    (h5 : orderOf (d * c) = 5) (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D) :
    ∃ x, (x = y ∨ x = d * y) ∧ orderOf (c * x) = 3 ∧ orderOf (c * (d * x)) = 5 := by
  have hD := h.root
  have hd2 := hD.mul_self_eq_one hd
  obtain ⟨n1, o1⟩ := opposite_of_collinear_of_five h hsing hQ hd hc h5 hy hdy hdyD
  have hddy : Commute d (d * y) := (Commute.refl d).mul_right hdy
  have hddyD : d * (d * y) ∈ D := by rw [mul_mul_self_cancel hd2]; exact hy
  obtain ⟨n2, o2⟩ := opposite_of_collinear_of_five h hsing hQ hd hc h5 hdyD hddy hddyD
  rcases hL d hd y hy c hc hdy hdyD (not_commute_of_orderOf_eq_five hD hd hc h5)
    (odd_of_orderOf_eq_five h5) n1 o1 n2 o2 with L | L | L
  · rw [h5] at L
    exact absurd L.1 (by norm_num)
  · exact ⟨y, Or.inl rfl, by rw [orderOf_mul_comm_eq]; exact L.2.1,
      by rw [orderOf_mul_comm_eq]; exact L.2.2⟩
  · exact ⟨d * y, Or.inr rfl, by rw [orderOf_mul_comm_eq]; exact L.2.2,
      by rw [mul_mul_self_cancel hd2, orderOf_mul_comm_eq]; exact L.2.1⟩

private theorem line_ne {d w x' a : G} (hd2 : d * d = 1) (hx : x' = w ∨ x' = d * w)
    (hw : w ≠ a ∧ w ≠ d * a) : x' ≠ a ∧ x' ≠ d * a := by
  rcases hx with rfl | rfl
  · exact hw
  · refine ⟨fun e => hw.2 ?_, fun e => hw.1 ?_⟩
    · rw [← e, mul_mul_self_cancel hd2]
    · rw [← mul_mul_self_cancel hd2 w, e, mul_mul_self_cancel hd2]

private theorem line_ne_symm {d a b : G} (hd2 : d * d = 1) (h : b ≠ a ∧ b ≠ d * a) :
    a ≠ b ∧ a ≠ d * b :=
  ⟨Ne.symm h.1, fun e => h.2 (by rw [e, mul_mul_self_cancel hd2])⟩

theorem exists_two_lines (h : Hyp G D) {d : G} (hd : d ∈ D) :
    ∃ y₁ ∈ D, ∃ y₂ ∈ D, Commute d y₁ ∧ d * y₁ ∈ D ∧ Commute d y₂ ∧ d * y₂ ∈ D ∧
      y₂ ≠ y₁ ∧ y₂ ≠ d * y₁ := by
  have hD := h.root
  obtain ⟨e, he, h4⟩ := exists_orderOf_mul_eq_four h hd
  obtain ⟨hz, hdz, hez, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  have hdzD : d * (d * e) ^ 2 ∈ D := mul_sq_mem_of_orderOf_eq_four h.isClass hD hd he h4
  have h4' : orderOf (e * d) = 4 := by rw [orderOf_mul_comm_eq]; exact h4
  have hezD' : e * (e * d) ^ 2 ∈ D := mul_sq_mem_of_orderOf_eq_four h.isClass hD he hd h4'
  have hx4 : (d * e) ^ 4 = 1 := h4 ▸ pow_orderOf_eq_one (d * e)
  have hinv : e * d = (d * e)⁻¹ := by rw [mul_inv_rev, hD.inv_eq hd, hD.inv_eq he]
  have hsq : (e * d) ^ 2 = (d * e) ^ 2 := by
    rw [hinv, inv_pow, inv_eq_iff_mul_eq_one, ← pow_add]
    exact hx4
  rw [hsq] at hezD'
  obtain ⟨g, hg⟩ := isConj_iff.mp (h.isConj hz hd)
  have hz1 := commute_conj g hdz.symm
  have hz2 := commute_conj g hez.symm
  rw [hg] at hz1 hz2
  refine ⟨g * d * g⁻¹, h.conj_mem g hd, g * e * g⁻¹, h.conj_mem g he, hz1, ?_, hz2, ?_, ?_, ?_⟩
  · have e1 : d * (g * d * g⁻¹) = g * ((d * e) ^ 2 * d) * g⁻¹ := by
      calc d * (g * d * g⁻¹) = g * (d * e) ^ 2 * g⁻¹ * (g * d * g⁻¹) := by rw [hg]
        _ = g * ((d * e) ^ 2 * d) * g⁻¹ := by group
    rw [e1]
    exact h.conj_mem g (by rw [← hdz.eq]; exact hdzD)
  · have e1 : d * (g * e * g⁻¹) = g * ((d * e) ^ 2 * e) * g⁻¹ := by
      calc d * (g * e * g⁻¹) = g * (d * e) ^ 2 * g⁻¹ * (g * e * g⁻¹) := by rw [hg]
        _ = g * ((d * e) ^ 2 * e) * g⁻¹ := by group
    rw [e1]
    exact h.conj_mem g (by rw [← hez.eq]; exact hezD')
  · intro he'
    have hed : e = d := by simpa using he'
    rw [hed, hD.mul_self_eq_one hd, orderOf_one] at h4
    exact absurd h4 (by norm_num)
  · intro he'
    have e1 : d * (g * d * g⁻¹) = g * ((d * e) ^ 2 * d) * g⁻¹ := by
      calc d * (g * d * g⁻¹) = g * (d * e) ^ 2 * g⁻¹ * (g * d * g⁻¹) := by rw [hg]
        _ = g * ((d * e) ^ 2 * d) * g⁻¹ := by group
    rw [e1] at he'
    have hed : e = (d * e) ^ 2 * d := by simpa using he'
    have hc : Commute d e := by rw [hed]; exact hdz.mul_right (Commute.refl d)
    have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hd)
      (hD.mul_self_eq_one he)).1 hc)
    rw [h4] at this
    exact absurd this (by norm_num)

theorem eq_line_of_five (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hQ : CommLambda D)
    (hL : LL5 D) (hNP : NoPolar D) {d c : G} (hd : d ∈ D) (hc : c ∈ D)
    (h5 : orderOf (d * c) = 5) {x : Fin 5 → G} (hx : ∀ i, x i ∈ D)
    (hxd : ∀ i, Commute d (x i)) (hxdD : ∀ i, d * x i ∈ D)
    (hu : x 0 * x 1 * x 2 * x 3 * x 4 * (x 0 * x 1 * x 2 * x 3 * x 4) = 1)
    (huc : Commute (x 0 * x 1 * x 2 * x 3 * x 4) c) {w : G} (hw : w ∈ D) (hwd : Commute d w)
    (hwdD : d * w ∈ D) : ∃ i, w = x i ∨ w = d * x i := by
  by_contra hno
  push Not at hno
  have hD := h.root
  have hd2 := hD.mul_self_eq_one hd
  obtain ⟨w', hw'eq, hw'3, hw'5⟩ := exists_order_three_point h hsing hQ hL hd hc h5 hw hwd hwdD
  have hw'D : w' ∈ D := by
    rcases hw'eq with rfl | rfl
    · exact hw
    · exact hwdD
  have hdw' : Commute d w' := by
    rcases hw'eq with rfl | rfl
    · exact hwd
    · exact (Commute.refl d).mul_right hwd
  have hdw'D : d * w' ∈ D := by
    rcases hw'eq with rfl | rfl
    · exact hwdD
    · rw [mul_mul_self_cancel hd2]; exact hw
  have hne : ∀ i, w' ≠ x i ∧ w' ≠ d * x i := fun i => line_ne hd2 hw'eq (hno i)
  have hw2 : w' * w' = 1 := hD.mul_self_eq_one hw'D
  have hconj : ∀ i, w' * x i * w' = x i * d := by
    intro i
    have hsp := (special_of_ne_line h hsing hQ hL hNP hd hc h5 (hx i) (hxd i) (hxdD i) hw'D hdw'
      hdw'D (hne i).1 (hne i).2).2
    rw [pow_two] at hsp
    have hxi2 := hD.mul_self_eq_one (hx i)
    calc w' * x i * w' = x i * (x i * w' * (x i * w')) := by
          rw [show x i * (x i * w' * (x i * w')) = (x i * x i) * w' * x i * w' by group, hxi2,
            one_mul]
      _ = x i * d := by rw [hsp]
  have key : ∀ a b : G, (w' * a * w') * (w' * b * w') = w' * (a * b) * w' := fun a b => by
    rw [show (w' * a * w') * (w' * b * w') = w' * a * (w' * w') * b * w' by group, hw2, mul_one]
    group
  have hp : ∀ (a : G) (i : Fin 5), a * d * (x i * d) = a * x i := fun a i => by
    rw [show a * d * (x i * d) = a * (d * x i) * d by group, (hxd i).eq,
      show a * (x i * d) * d = a * x i * (d * d) by group, hd2, mul_one]
  set u := x 0 * x 1 * x 2 * x 3 * x 4 with hu_def
  have hdu : Commute d u := by
    rw [hu_def]
    exact ((((hxd 0).mul_right (hxd 1)).mul_right (hxd 2)).mul_right (hxd 3)).mul_right (hxd 4)
  have hwu : w' * u * w' = u * d := by
    calc w' * u * w' = (w' * x 0 * w') * (w' * x 1 * w') * (w' * x 2 * w') * (w' * x 3 * w') *
          (w' * x 4 * w') := by
          rw [key, key, key, key]
      _ = x 0 * d * (x 1 * d) * (x 2 * d) * (x 3 * d) * (x 4 * d) := by simp only [hconj]
      _ = u * d := by
          rw [hp (x 0) 1, show x 0 * x 1 * (x 2 * d) = x 0 * x 1 * x 2 * d by group,
            hp (x 0 * x 1 * x 2) 3, hu_def]
          group
  have h1 : u * w' = w' * (u * d) := by
    calc u * w' = w' * (w' * u * w') := by
          rw [show w' * (w' * u * w') = (w' * w') * u * w' by group, hw2, one_mul]
      _ = w' * (u * d) := by rw [hwu]
  have h2 : u * w' * u = w' * d := by
    rw [h1, show w' * (u * d) * u = w' * (u * d * u) by group,
      show u * d * u = d * (u * u) by rw [← hdu.eq]; group, hu, mul_one]
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hcu : u * c * u = c := by rw [huc.eq, mul_assoc, hu, mul_one]
  have hconj' : u * (w' * c) * u⁻¹ = w' * d * c := by
    rw [hui]
    calc u * (w' * c) * u = (u * w' * u) * (u * c * u) := by
          rw [show (u * w' * u) * (u * c * u) = u * w' * (u * u) * c * u by group, hu, mul_one]
          group
      _ = w' * d * c := by rw [h2, hcu]
  have e1 := orderOf_conj_eq u (w' * c)
  rw [hconj', ← hdw'.eq, orderOf_mul_comm_eq, hw'5, orderOf_mul_comm_eq, hw'3] at e1
  exact absurd e1 (by norm_num)

theorem lineConfig_of_lines (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hQ : CommLambda D) (hL : LL5 D) (hNP : NoPolar D) {n : ℕ} {d c : G} {x : Fin n → G}
    (hd : d ∈ D) (hc : c ∈ D) (h5 : orderOf (d * c) = 5) (hx : ∀ i, x i ∈ D)
    (hxd : ∀ i, Commute d (x i)) (hxdD : ∀ i, d * x i ∈ D)
    (hne : ∀ i j, i ≠ j → x j ≠ x i ∧ x j ≠ d * x i) (hx3 : ∀ i, orderOf (c * x i) = 3)
    (hx5 : ∀ i, orderOf (c * (d * x i)) = 5) : LineConfig d c x where
  d_sq := h.root.mul_self_eq_one hd
  c_sq := h.root.mul_self_eq_one hc
  x_sq i := h.root.mul_self_eq_one (hx i)
  dc_pow := by rw [← h5]; exact pow_orderOf_eq_one _
  d_comm := hxd
  sq_eq i j hij := (special_of_ne_line h hsing hQ hL hNP hd hc h5 (hx i) (hxd i) (hxdD i) (hx j)
    (hxd j) (hxdD j) (hne i j hij).1 (hne i j hij).2).2
  cx_pow i := by rw [← hx3 i]; exact pow_orderOf_eq_one _
  cdx_pow i := by rw [← hx5 i]; exact pow_orderOf_eq_one _

theorem lineConfig_native :
    LineConfig (nativeGens 0) (nativeGens 1) (fun i : Fin 5 => nativeGens (i.addNat 2)) :=
  lineConfig_of_signedProd (ov := true) (fun w hw => by
    rw [lineGens_self]
    exact nativeGens_relators w hw)

theorem ovoid_native :
    nativeGens 2 * nativeGens 3 * nativeGens 4 * nativeGens 5 * nativeGens 6 = 1 := by
  have := nativeGens_relators ((List.finRange 5).map letterX)
    (List.mem_append_right _ (by simp))
  rw [show (List.finRange 5).map letterX =
    [letterX 0, letterX 1, letterX 2, letterX 3, letterX 4] by decide] at this
  rw [← lineGens_self nativeGens] at this
  simp only [signedProd_letterX, signedProd_nil, mul_one] at this
  simpa [mul_assoc] using this

theorem nativeGens_zero_ne_one : nativeGens 0 ≠ 1 := by
  intro h0
  have hJ := lineConfig_native
  have hc1 : nativeGens 1 = 1 := by
    have h5 := hJ.dc_pow
    rw [h0, one_mul] at h5
    have h2 := hJ.c_sq
    calc nativeGens 1 = nativeGens 1 ^ 5 * (nativeGens 1 * nativeGens 1)⁻¹ ^ 2 := by group
      _ = 1 := by rw [h5, h2, inv_one, one_pow, one_mul]
  have hx1 : ∀ i : Fin 5, nativeGens (i.addNat 2) = 1 := by
    intro i
    have h3 := hJ.cx_pow i
    rw [hc1, one_mul] at h3
    have h2 := hJ.x_sq i
    calc nativeGens (i.addNat 2) = nativeGens (i.addNat 2) ^ 3 *
          (nativeGens (i.addNat 2) * nativeGens (i.addNat 2))⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  have hall : ∀ j : Fin 7, nativeGens j = 1 := by
    rw [← lineGens_self nativeGens]
    intro j
    unfold lineGens
    split_ifs
    · exact h0
    · exact hc1
    · exact hx1 _
  have htriv : P3.toSeed = 1 := PresentedGroup.ext fun j =>
    ((P3.toSeed_of j).trans (hall _)).trans (MonoidHom.one_apply _).symm
  have hcard := CFSG.Sporadic.Bridge.J2.le_card_seedGroup
  have hsub : Subsingleton ↥seedGroup := ⟨fun a b => by
    obtain ⟨p, rfl⟩ := P3.toSeed_surjective a
    obtain ⟨q, rfl⟩ := P3.toSeed_surjective b
    rw [htriv, MonoidHom.one_apply, MonoidHom.one_apply]⟩
  rw [Nat.card_unique] at hcard
  exact absurd hcard (by norm_num)

theorem native_ne {i j : Fin 5} (hij : i ≠ j) :
    nativeGens (j.addNat 2) ≠ nativeGens (i.addNat 2) ∧
      nativeGens (j.addNat 2) ≠ nativeGens 0 * nativeGens (i.addNat 2) := by
  have hJ := lineConfig_native
  have hsq := hJ.sq_eq i j hij
  have hd1 := nativeGens_zero_ne_one
  constructor
  · intro e
    rw [e, hJ.x_sq i, one_pow] at hsq
    exact hd1 hsq.symm
  · intro e
    rw [e, show nativeGens (i.addNat 2) * (nativeGens 0 * nativeGens (i.addNat 2)) =
      nativeGens 0 * (nativeGens (i.addNat 2) * nativeGens (i.addNat 2)) by
        rw [← mul_assoc, ← (hJ.d_comm i).eq, mul_assoc], hJ.x_sq i, mul_one, pow_two,
      hJ.d_sq] at hsq
    exact hd1 hsq.symm

theorem native_ne_zero (i : Fin 5) : nativeGens (i.addNat 2) ≠ nativeGens 0 := by
  have hJ := lineConfig_native
  intro e
  have hij : i + 1 ≠ i := (by decide : ∀ k : Fin 5, k + 1 ≠ k) i
  have hsq := hJ.sq_eq (i + 1) i hij
  rw [e, (commute_iff_mul_sq_eq_one (hJ.x_sq _) hJ.d_sq).1 (hJ.d_comm (i + 1)).symm] at hsq
  exact nativeGens_zero_ne_one hsq.symm

noncomputable def threeLinesHom {d c : G} {x : Fin 3 → G} (hcfg : LineConfig d c x) :
    P3.Pres →* G :=
  wordsHom (lineRels 3 false) (lineGens d c x) (hcfg.signedProd_lineRels (by simp))

section Three

variable {d c : G} {x : Fin 3 → G} (hcfg : LineConfig d c x)
include hcfg

theorem threeLinesHom_zero : threeLinesHom hcfg (PresentedGroup.of 0) = d := by
  rw [threeLinesHom, wordsHom_of, lineGens_zero]

theorem threeLinesHom_one : threeLinesHom hcfg (PresentedGroup.of 1) = c := by
  rw [threeLinesHom, wordsHom_of, lineGens_one]

theorem threeLinesHom_addNat (i : Fin 3) :
    threeLinesHom hcfg (PresentedGroup.of (i.addNat 2)) = x i := by
  rw [threeLinesHom, wordsHom_of, lineGens_addNat]

end Three

theorem toSeed_addNat (i : Fin 3) :
    P3.toSeed (PresentedGroup.of (i.addNat 2)) =
      nativeGens ((Fin.castLE (by norm_num) i : Fin 5).addNat 2) := by
  rw [P3.toSeed_of]
  exact congrArg nativeGens (Fin.ext (by simp [P3.emb5]))

theorem exists_five_lines (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hQ : CommLambda D) (hL : LL5 D) (hNP : NoPolar D) {d c : G} (hd : d ∈ D) (hc : c ∈ D)
    (h5 : orderOf (d * c) = 5) {x : Fin 3 → G} (hx : ∀ i, x i ∈ D)
    (hxd : ∀ i, Commute d (x i)) (hxdD : ∀ i, d * x i ∈ D)
    (hne : ∀ i j, i ≠ j → x j ≠ x i ∧ x j ≠ d * x i) (hx3 : ∀ i, orderOf (c * x i) = 3)
    (hx5 : ∀ i, orderOf (c * (d * x i)) = 5) :
    ∃ (K : Subgroup G) (y : Fin 5 → G), d ∈ K ∧ c ∈ K ∧ (∀ i, y i ∈ K) ∧
      y 0 = x 0 ∧ y 1 = x 1 ∧ y 2 = x 2 ∧
      (∀ i, y i ∈ D) ∧ (∀ i, Commute d (y i)) ∧ (∀ i, d * y i ∈ D) ∧
      (∀ i j, i ≠ j → y j ≠ y i ∧ y j ≠ d * y i) ∧
      (∀ i, orderOf (c * y i) = 3) ∧ (∀ i, orderOf (c * (d * y i)) = 5) ∧
      (∀ g ∈ K, Commute (y 0 * y 1 * y 2 * y 3 * y 4) g) ∧
      y 0 * y 1 * y 2 * y 3 * y 4 * (y 0 * y 1 * y 2 * y 3 * y 4) = 1 := by
  have hD := h.root
  have hd2 := hD.mul_self_eq_one hd
  have hcfg := lineConfig_of_lines h hsing hQ hL hNP hd hc h5 hx hxd hxdD hne hx3 hx5
  set φ := threeLinesHom hcfg with hφ
  have hφ0 : φ (PresentedGroup.of 0) = d := threeLinesHom_zero hcfg
  have hφ1 : φ (PresentedGroup.of 1) = c := threeLinesHom_one hcfg
  have hφx : ∀ i : Fin 3, φ (PresentedGroup.of (i.addNat 2)) = x i := threeLinesHom_addNat hcfg
  have hdc : ¬ Commute (φ (PresentedGroup.of 0)) (φ (PresentedGroup.of 1)) := by
    rw [hφ0, hφ1]
    exact not_commute_of_orderOf_eq_five hD hd hc h5
  have hJ := lineConfig_native
  have hJ0 := nativeGens_zero_ne_one
  set p₃ := P3.conjPoint P3.conjX3 with hp₃
  set p₄ := P3.conjPoint P3.conjX4 with hp₄
  have ht₃ : P3.toSeed p₃ = nativeGens ((3 : Fin 5).addNat 2) := P3.toSeed_conjX3
  have ht₄ : P3.toSeed p₄ = nativeGens ((4 : Fin 5).addNat 2) := P3.toSeed_conjX4
  have ht0 : P3.toSeed (PresentedGroup.of 0) = nativeGens 0 := P3.toSeed_of 0
  have ht1 : P3.toSeed (PresentedGroup.of 1) = nativeGens 1 := P3.toSeed_of 1
  have htx : ∀ i : Fin 3, P3.toSeed (PresentedGroup.of (i.addNat 2)) =
      nativeGens ((Fin.castLE (by norm_num) i : Fin 5).addNat 2) := toSeed_addNat
  have hφp : ∀ w : List (Fin 5 × Bool), φ (P3.conjPoint w) ∈ D := fun w => by
    rw [P3.conjPoint_def, map_mul, map_mul, map_inv, hφ0]
    exact h.conj_mem _ hd
  have lift : ∀ (p : P3.Pres) (k : Fin 5), φ p ∈ D →
      P3.toSeed p = nativeGens (k.addNat 2) →
      Commute d (φ p) ∧ d * φ p ∈ D ∧ orderOf (c * φ p) = 3 ∧ orderOf (c * (d * φ p)) = 5 ∧
        φ p ≠ d := by
    intro p k hpD hpk
    have hne0 : φ p ≠ d := by
      intro e
      have := P3.toSeed_eq_of_eq φ hdc (e.trans hφ0.symm)
      rw [hpk, ht0] at this
      exact native_ne_zero k this
    have hq : P3.toSeed ((p * PresentedGroup.of 0) * (p * PresentedGroup.of 0)) = 1 := by
      rw [map_mul, map_mul, hpk, ht0, ← pow_two]
      exact (commute_iff_mul_sq_eq_one (hJ.x_sq k) hJ.d_sq).1 (hJ.d_comm k).symm
    have hz2 := P3.mul_self_eq_one_of_toSeed φ hq
    have hzc := P3.commute_of_toSeed φ hq
    rw [map_mul, map_mul, hφ0] at hz2 hzc
    have hcomm : Commute d (φ p) := by
      by_contra hnc
      have hnc' : ¬ Commute (φ p) d := fun e => hnc e.symm
      have h4 : orderOf (φ p * d) = 4 := by
        rw [commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hpD) hd2] at hnc'
        have : orderOf (φ p * d) = 2 ^ 2 := by
          refine orderOf_eq_prime_pow (p := 2) ?_ ?_
          · simpa using hnc'
          · rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two]
            exact hz2
        simpa using this
      have hzD := hD.sq_mem hpD hd h4
      rw [pow_two] at hzD
      have hdz : Commute d (φ p * d * (φ p * d)) := by
        have := hzc (PresentedGroup.of 0)
        rw [hφ0] at this
        exact this.symm
      have hzc' : Commute (φ p * d * (φ p * d)) c := by
        have := hzc (PresentedGroup.of 1)
        rwa [hφ1] at this
      exact false_of_commute_of_five h hNP hd hc h5 hzD hdz hzc'
    have hdpD : d * φ p ∈ D := hNP d hd _ hpD hcomm hne0.symm
    have hq3 : P3.toSeed ((PresentedGroup.of 1 * p) ^ 3) = 1 := by
      rw [map_pow, map_mul, ht1, hpk]
      exact hJ.cx_pow k
    have h6 : (c * φ p) ^ 6 = 1 := by
      have := P3.mul_self_eq_one_of_toSeed φ hq3
      rw [map_pow, map_mul, hφ1, ← pow_add] at this
      exact this
    obtain ⟨x', hx'eq, hx'3, hx'5⟩ :=
      exists_order_three_point h hsing hQ hL hd hc h5 hpD hcomm hdpD
    rcases hx'eq with rfl | rfl
    · exact ⟨hcomm, hdpD, hx'3, hx'5, hne0⟩
    · rw [mul_mul_self_cancel hd2] at hx'5
      have := orderOf_dvd_of_pow_eq_one h6
      rw [hx'5] at this
      exact absurd this (by norm_num)
  obtain ⟨hc₃, hcD₃, h3₃, h5₃, -⟩ := lift p₃ 3 (hφp _) ht₃
  obtain ⟨hc₄, hcD₄, h3₄, h5₄, -⟩ := lift p₄ 4 (hφp _) ht₄
  have sep : ∀ (p q : P3.Pres) (i j : Fin 5), i ≠ j →
      P3.toSeed p = nativeGens (i.addNat 2) → P3.toSeed q = nativeGens (j.addNat 2) →
      φ q ≠ φ p ∧ φ q ≠ d * φ p := by
    intro p q i j hij hp hq
    have hn := native_ne hij
    refine ⟨fun e => hn.1 ?_, fun e => hn.2 ?_⟩
    · rw [← hq, ← hp]
      exact P3.toSeed_eq_of_eq φ hdc e
    · rw [← hq, ← hp, ← ht0, ← map_mul]
      exact P3.toSeed_eq_of_eq φ hdc (by rw [map_mul, hφ0]; exact e)
  set y : Fin 5 → G := ![x 0, x 1, x 2, φ p₃, φ p₄] with hy
  have hyp : ∀ i : Fin 5, ∃ p : P3.Pres, φ p = y i ∧ P3.toSeed p = nativeGens (i.addNat 2) := by
    intro i
    fin_cases i
    · exact ⟨_, hφx 0, by rw [htx 0]; rfl⟩
    · exact ⟨_, hφx 1, by rw [htx 1]; rfl⟩
    · exact ⟨_, hφx 2, by rw [htx 2]; rfl⟩
    · exact ⟨p₃, rfl, ht₃⟩
    · exact ⟨p₄, rfl, ht₄⟩
  have hyD : ∀ i, y i ∈ D := by
    intro i; fin_cases i
    · exact hx 0
    · exact hx 1
    · exact hx 2
    · exact hφp _
    · exact hφp _
  refine ⟨φ.range, y, ⟨_, hφ0⟩, ⟨_, hφ1⟩, fun i => ?_, rfl, rfl, rfl, hyD, fun i => ?_,
    fun i => ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · obtain ⟨p, hp, -⟩ := hyp i
    exact ⟨p, hp⟩
  · fin_cases i
    · exact hxd 0
    · exact hxd 1
    · exact hxd 2
    · exact hc₃
    · exact hc₄
  · fin_cases i
    · exact hxdD 0
    · exact hxdD 1
    · exact hxdD 2
    · exact hcD₃
    · exact hcD₄
  · obtain ⟨p, hp, hpi⟩ := hyp i
    obtain ⟨q, hq, hqj⟩ := hyp j
    rw [← hp, ← hq]
    exact sep p q i j hij hpi hqj
  · fin_cases i
    · exact hx3 0
    · exact hx3 1
    · exact hx3 2
    · exact h3₃
    · exact h3₄
  · fin_cases i
    · exact hx5 0
    · exact hx5 1
    · exact hx5 2
    · exact h5₃
    · exact h5₄
  ·
    have hu : P3.toSeed (PresentedGroup.of ((0 : Fin 3).addNat 2) *
        PresentedGroup.of ((1 : Fin 3).addNat 2) * PresentedGroup.of ((2 : Fin 3).addNat 2) *
        p₃ * p₄) = 1 := by
      rw [map_mul, map_mul, map_mul, map_mul, htx 0, htx 1, htx 2, ht₃, ht₄]
      exact ovoid_native
    rintro g ⟨q, rfl⟩
    have := P3.commute_of_toSeed φ hu q
    rwa [map_mul, map_mul, map_mul, map_mul, hφx 0, hφx 1, hφx 2] at this
  · have hu : P3.toSeed (PresentedGroup.of ((0 : Fin 3).addNat 2) *
        PresentedGroup.of ((1 : Fin 3).addNat 2) * PresentedGroup.of ((2 : Fin 3).addNat 2) *
        p₃ * p₄) = 1 := by
      rw [map_mul, map_mul, map_mul, map_mul, htx 0, htx 1, htx 2, ht₃, ht₄]
      exact ovoid_native
    have := P3.mul_self_eq_one_of_toSeed φ hu
    rwa [map_mul, map_mul, map_mul, map_mul, hφx 0, hφx 1, hφx 2] at this

theorem lineCount_of (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hQ : CommLambda D)
    (hL : LL5 D) (hNP : NoPolar D) (hconn : Closure.CommConnected D) : LineCount D := by
  intro d hd c hc h5
  have hD := h.root
  have hd2 := hD.mul_self_eq_one hd
  have pt : ∀ {y x' : G}, y ∈ D → Commute d y → d * y ∈ D → (x' = y ∨ x' = d * y) →
      x' ∈ D ∧ Commute d x' ∧ d * x' ∈ D := by
    intro y x' hy hdy hdyD hx'
    rcases hx' with rfl | rfl
    · exact ⟨hy, hdy, hdyD⟩
    · exact ⟨hdyD, (Commute.refl d).mul_right hdy, by rw [mul_mul_self_cancel hd2]; exact hy⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, hdy₁, hdy₁D, hdy₂, hdy₂D, h21, h21'⟩ := exists_two_lines h hd
  obtain ⟨x₀, hx₀e, hx₀3, hx₀5⟩ := exists_order_three_point h hsing hQ hL hd hc h5 hy₁ hdy₁ hdy₁D
  obtain ⟨x₁, hx₁e, hx₁3, hx₁5⟩ := exists_order_three_point h hsing hQ hL hd hc h5 hy₂ hdy₂ hdy₂D
  obtain ⟨hx₀D, hdx₀, hdx₀D⟩ := pt hy₁ hdy₁ hdy₁D hx₀e
  obtain ⟨hx₁D, hdx₁, hdx₁D⟩ := pt hy₂ hdy₂ hdy₂D hx₁e
  have hne₁₀ : x₁ ≠ x₀ ∧ x₁ ≠ d * x₀ :=
    line_ne hd2 hx₁e (line_ne_symm hd2 (line_ne hd2 hx₀e (line_ne_symm hd2 ⟨h21, h21'⟩)))
  by_cases hall : ∀ w ∈ D, Commute d w → d * w ∈ D →
      (w = x₀ ∨ w = d * x₀) ∨ (w = x₁ ∨ w = d * x₁)
  · left
    refine ⟨![x₀, x₁], ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i => ?_,
      fun f hf hdf => ?_⟩⟩
    · fin_cases i
      · exact hx₀D
      · exact hx₁D
    · fin_cases i
      · exact hdx₀
      · exact hdx₁
    · fin_cases i
      · exact hdx₀D
      · exact hdx₁D
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hne₁₀
      · exact line_ne_symm hd2 hne₁₀
      · exact absurd rfl hij
    · fin_cases i
      · exact hx₀3
      · exact hx₁3
    · by_cases hfd : f = d
      · exact Or.inl hfd
      · right
        rcases hall f hf hdf (hNP d hd f hf hdf (Ne.symm hfd)) with h0 | h1
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
  · right
    push Not at hall
    obtain ⟨w, hw, hdw, hdwD, hw0, hw1⟩ := hall
    obtain ⟨x₂, hx₂e, hx₂3, hx₂5⟩ := exists_order_three_point h hsing hQ hL hd hc h5 hw hdw hdwD
    obtain ⟨hx₂D, hdx₂, hdx₂D⟩ := pt hw hdw hdwD hx₂e
    have hne₂₀ : x₂ ≠ x₀ ∧ x₂ ≠ d * x₀ := line_ne hd2 hx₂e hw0
    have hne₂₁ : x₂ ≠ x₁ ∧ x₂ ≠ d * x₁ := line_ne hd2 hx₂e hw1
    obtain ⟨K, y, hdK, hcK, hyK, -, -, -, hyD, hyd, hydD, hyne, hy3, -, huK, hu⟩ :=
      exists_five_lines h hsing hQ hL hNP hd hc h5 (x := ![x₀, x₁, x₂])
        (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> assumption)
        (fun i => by fin_cases i <;> assumption)
        (fun i j hij => by
          fin_cases i <;> fin_cases j
          · exact absurd rfl hij
          · exact hne₁₀
          · exact hne₂₀
          · exact line_ne_symm hd2 hne₁₀
          · exact absurd rfl hij
          · exact hne₂₁
          · exact line_ne_symm hd2 hne₂₀
          · exact line_ne_symm hd2 hne₂₁
          · exact absurd rfl hij)
        (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> assumption)
    have hlines : LinesAt D d c y := by
      refine ⟨hyD, hyd, hydD, hyne, hy3, fun f hf hdf => ?_⟩
      by_cases hfd : f = d
      · exact Or.inl hfd
      · exact Or.inr (eq_line_of_five h hsing hQ hL hNP hd hc h5 hyD hyd hydD hu (huK c hcK) hf
          hdf (hNP d hd f hf hdf (Ne.symm hfd)))
    have hcfg := lineConfig_of_linesAt h hsing hQ hL hNP hd hc h5 hlines
    have hdH : d ∈ Subgroup.closure (insert d (insert c (Set.range y))) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hcH : c ∈ Subgroup.closure (insert d (insert c (Set.range y))) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have hyH : ∀ i, y i ∈ Subgroup.closure (insert d (insert c (Set.range y))) := fun i =>
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
    have hconj := fun i => (hcfg.subgroup hdH hcH hyH).isConj i
    have htop := closure_eq_top_of_isConj h hconn hd hlines fun i =>
      ⟨exists_mem_of_isConj (hconj i).1, exists_mem_of_isConj (hconj i).2⟩
    have hK : K = ⊤ := by
      rw [eq_top_iff, ← htop, Subgroup.closure_le]
      rintro g (rfl | rfl | ⟨i, rfl⟩)
      · exact hdK
      · exact hcK
      · exact hyK i
    have hcen : y 0 * y 1 * y 2 * y 3 * y 4 ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (huK g (hK ▸ Subgroup.mem_top g)).eq.symm
    rw [h.center_eq_bot, Subgroup.mem_bot] at hcen
    exact ⟨y, hlines, hcen⟩

end CFSG.Timmesfeld.Moufang
