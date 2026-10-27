module

public import CFSG.Timmesfeld.Exceptional.DeepW1
public import Certificates.Certificate15950
public import CFSG.Timmesfeld.Exceptional.DeepJ2Split

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang CFSG.Certificates CFSG.Blueprint
open CFSG.Sporadic.Bridge.J2 (idL lwordL)
open CFSG.Timmesfeld.Moufang.J2 (genL nativeGens genL_wf unitGen_val unitGen_inv
  coe_signedProd_nativeGens signedProd_comp)

variable {G : Type*} [Group G] {D : Set G}

theorem reflect_family (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D) {z a y : G}
    (hz : z ∈ D) (ha : a ∈ D) (ha3 : a ∉ nbhd D z 3) (hy : y ∈ collinearSet D a)
    (hy3 : y ∈ nbhd D z 3) {n : ℕ} {s : Fin n → G} (hs : ∀ j, s j ∈ D)
    (hys : ∀ j, Commute y (s j)) (h4 : ∀ j, orderOf (s j * z) = 4)
    (hinj : Function.Injective s) :
    ∃ v : Fin (n + 1) → G, (∀ j, v j ∈ collinearSet D a) ∧ (∀ j, v j ∈ nbhd D z 3) ∧
      ∀ j l, j ≠ l → v l ≠ v j ∧ v l ≠ a * v j := by
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  obtain ⟨hyD, hay, hayD⟩ := hy
  have hTO := (totallyOpposite_iff_not_mem_nbhd_three hD hNL hz ha).2 ha3
  obtain ⟨-, hodd⟩ := hTO.opposite_self ha
  obtain ⟨e, he, hea, -⟩ := exists_reflection hD hconj ha hz hodd
  have hy2 : y ∉ nbhd D z 2 := fun h => ha3 (mem_nbhd_succ_of_commute ha h hay)
  have hv : ∀ j, e * (s j * z) ^ 2 * e ∈ collinearSet D a ∧ e * (s j * z) ^ 2 * e ∈ nbhd D z 3 ∧
      e * (s j * z) ^ 2 * e ≠ y ∧ e * (s j * z) ^ 2 * e ≠ a * y := fun j => by
    obtain ⟨h1, h2, -, h3, h4'⟩ := FarLine.reflect hclass hD hNL hNP hPl hP1 hz ha ha3 he hea
      hyD hay (hs j) (hys j) (h4 j) rfl rfl
    exact ⟨h1, h2, h3, h4'⟩
  have ha2 := hD.mul_self_eq_one ha
  have hflip : ∀ u w : G, u ≠ a * w → w ≠ a * u := fun u w h e => h (by
    rw [e, ← mul_assoc, ha2, one_mul])
  refine ⟨Fin.cons y fun j => e * (s j * z) ^ 2 * e, fun j => ?_, fun j => ?_, ?_⟩
  · cases j using Fin.cases with
    | zero => exact ⟨hyD, hay, hayD⟩
    | succ j => exact (hv j).1
  · cases j using Fin.cases with
    | zero => exact hy3
    | succ j => exact (hv j).2.1
  · intro j l hjl
    cases j using Fin.cases with
    | zero =>
      cases l using Fin.cases with
      | zero => exact absurd rfl hjl
      | succ l =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact ⟨(hv l).2.2.1, (hv l).2.2.2⟩
    | succ j =>
      cases l using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact ⟨Ne.symm (hv j).2.2.1, hflip _ _ (hv j).2.2.2⟩
      | succ l =>
        have hjl' : j ≠ l := fun h => hjl (by rw [h])
        simp only [Fin.cons_succ]
        refine ⟨fun h => hjl' (hinj ?_), FarLine.ne_mul_reflect hclass hD hNL hNP hPl hz he hea
          hyD hy2 (hs l) (hys l) (h4 l) (hs j) (hys j) (h4 j)⟩
        exact (FarLine.eq_of_reflect_eq hD hconj hNL hNP hPl hz hyD hy2 (hs l) (hys l) (h4 l)
          (hs j) (hys j) (h4 j) h).symm

theorem lwordL_wJ_0 : ∀ k : Fin 3, lwordL genL genL
    (((List.replicate 4 (wJ 0 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL :=
  Certificates.certificate15950.1

theorem lwordL_wJ_1 : ∀ k : Fin 3, lwordL genL genL
    (((List.replicate 4 (wJ 1 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL :=
  Certificates.certificate15950.2.1

theorem lwordL_wJ_2 : ∀ k : Fin 3, lwordL genL genL
    (((List.replicate 4 (wJ 2 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL :=
  Certificates.certificate15950.2.2.1

theorem lwordL_wJ_3 : ∀ k : Fin 3, lwordL genL genL
    (((List.replicate 4 (wJ 3 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL :=
  Certificates.certificate15950.2.2.2

theorem native_pow_four (i : Fin 4) (k : Fin 3) : signedProd nativeGens (wJ i k) ^ 4 = 1 := by
  rw [← signedProd_replicate]
  apply Subtype.ext
  rw [coe_signedProd_nativeGens, Subgroup.coe_one]
  refine CFSG.Sporadic.Bridge.J2.wordProd_eq_one_of_lwordL genL_wf genL_wf unitGen_val
    unitGen_inv ?_
  fin_cases i
  exacts [lwordL_wJ_0 k, lwordL_wJ_1 k, lwordL_wJ_2 k, lwordL_wJ_3 k]

theorem lineGens_castLE {α : Type*} (p c : α) (x : Fin 3 → α) (j : Fin 4) :
    lineGens p c x (Fin.castLE (by norm_num) j) = lineGens p c ![x 0, x 1] j := by
  fin_cases j <;> simp [lineGens]

theorem threeLinesHom_of {p c : G} {x : Fin 3 → G} (hcfg : LineConfig p c x) (j : Fin 5) :
    threeLinesHom hcfg (PresentedGroup.of j) = lineGens p c x j := by
  fin_cases j
  · exact (threeLinesHom_zero hcfg).trans (lineGens_zero p c x).symm
  · exact (threeLinesHom_one hcfg).trans (lineGens_one p c x).symm
  · exact (threeLinesHom_addNat hcfg 0).trans (lineGens_addNat p c x 0).symm
  · exact (threeLinesHom_addNat hcfg 1).trans (lineGens_addNat p c x 1).symm
  · exact (threeLinesHom_addNat hcfg 2).trans (lineGens_addNat p c x 2).symm

theorem threeLinesHom_castLE {p c : G} {x : Fin 3 → G} (hcfg : LineConfig p c x)
    (w : List (Fin 4 × Bool)) :
    threeLinesHom hcfg (signedProd PresentedGroup.of
      (w.map fun l => (Fin.castLE (by norm_num) l.1, l.2))) =
      signedProd (lineGens p c ![x 0, x 1]) w := by
  rw [map_signedProd]
  have hf : (fun j => threeLinesHom hcfg (PresentedGroup.of j)) = lineGens p c x :=
    funext (threeLinesHom_of hcfg)
  rw [hf, ← signedProd_comp]
  congr 1
  funext j
  exact lineGens_castLE p c x j

theorem toSeed_castLE (w : List (Fin 4 × Bool)) :
    P3.toSeed (signedProd PresentedGroup.of
      (w.map fun l => (Fin.castLE (by norm_num : 4 ≤ 5) l.1, l.2))) =
      signedProd nativeGens (w.map fun l => (Fin.castLE (by norm_num : 4 ≤ 7) l.1, l.2)) := by
  rw [map_signedProd]
  have hf : (fun j => P3.toSeed (PresentedGroup.of j)) = nativeGens ∘ P3.emb5 :=
    funext P3.toSeed_of
  rw [hf, signedProd_comp, List.map_map]
  rfl

theorem orderOf_eq_four_of_pow_eight (hD : IsRootInvolutionSet D) {t z : G} (ht : t ∈ D)
    (hz : z ∈ D) (h8 : (t * z) ^ 8 = 1) (hnc : ¬ Commute t z) : orderOf (t * z) = 4 := by
  rcases commute_or_orderOf_mul_eq_four_or_odd hD ht hz with hc | h4 | ⟨hodd, -⟩
  · exact absurd hc hnc
  · exact h4
  · exfalso
    have hd := orderOf_dvd_of_pow_eq_one h8
    have hle := Nat.le_of_dvd (by norm_num) hd
    have h1 : orderOf (t * z) = 1 := by
      interval_cases hn : orderOf (t * z) <;> simp_all <;> contradiction
    rw [orderOf_eq_one_iff] at h1
    have e : t = z := by
      rw [← inv_eq_of_mul_eq_one_right h1, hD.inv_eq ht]
    exact hnc (e ▸ Commute.refl t)

@[expose] def linePt (d x : G) (b : Bool) : G := cond b (d * x) x

theorem orderOf_linePt_zPt (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hNL : NoLevi D) (hNP : NoPolar D) (hP1 : ExcP1 D) {c p : G}
    (hp : p ∈ D) {x : Fin 3 → G} (hcfg3 : LineConfig p c x) (hcfg2 : LineConfig p c ![x 0, x 1])
    (hx2 : ∀ i, ![x 0, x 1] i ∈ collinearSet D p) (hyD : ∀ k, fivePoints hcfg3 k ∈ D)
    (hyp : ∀ k, Commute p (fivePoints hcfg3 k)) (hypD : ∀ k, p * fivePoints hcfg3 k ∈ D)
    (i : Fin 4) (k : Fin 3) :
    orderOf (linePt p (fivePoints hcfg3 (k.addNat 2)) (tD i) * zPt p c ![x 0, x 1] i) = 4 := by
  set φ := threeLinesHom hcfg3 with hφ
  obtain ⟨Y, hY, hYs⟩ := exists_preimage_fivePoints hcfg3 (k.addNat 2)
  set Z := signedProd (PresentedGroup.of (rels := wordRels (lineRels 3 false)))
    ((tZ i).map fun l => (Fin.castLE (by norm_num) l.1, l.2)) with hZ
  have hZφ : φ Z = zPt p c ![x 0, x 1] i := threeLinesHom_castLE hcfg3 (tZ i)
  have hZs := toSeed_castLE (tZ i)
  set T := cond (tD i) (PresentedGroup.of 0 * Y) Y with hT
  have hTφ : φ T = linePt p (fivePoints hcfg3 (k.addNat 2)) (tD i) := by
    rw [hT, linePt]
    cases tD i
    · exact hY
    · rw [Bool.cond_true, Bool.cond_true, map_mul, threeLinesHom_zero, hY]
  have hTs : P3.toSeed T * P3.toSeed Z = signedProd nativeGens (wJ i k) := by
    rw [hZs, wJ, signedProd_append, signedProd_append, hT]
    have hk : (k.addNat 2).addNat 2 = (⟨k.val + 4, by omega⟩ : Fin 7) := Fin.ext (by simp)
    cases tD i
    · simp [signedProd, hYs, hk]
    · simp [signedProd, hYs, hk, P3.toSeed_of, P3.emb5]
  have h4 : P3.toSeed ((T * Z) ^ 4) = 1 := by
    rw [map_pow, map_mul, hTs, native_pow_four]
  have h8 : (φ T * φ Z) ^ 8 = 1 := by
    have := P3.mul_self_eq_one_of_toSeed φ h4
    rw [map_pow, map_mul] at this
    rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add]
    exact this
  rw [hTφ, hZφ] at h8
  have hp2 := (zPt_facts hclass hD hNL hNP hP1 hcfg2 hp hx2 i).2.1
  have hz := zPt_mem (c := c) (x := ![x 0, x 1]) hclass hp i
  have htD : linePt p (fivePoints hcfg3 (k.addNat 2)) (tD i) ∈ D := by
    rw [linePt]
    cases tD i
    · exact hyD _
    · exact hypD _
  have hpt : Commute p (linePt p (fivePoints hcfg3 (k.addNat 2)) (tD i)) := by
    rw [linePt]
    cases tD i
    · exact hyp _
    · exact (Commute.refl p).mul_right (hyp _)
  refine orderOf_eq_four_of_pow_eight hD htD hz h8 fun hc => hp2 ?_
  exact mem_nbhd_succ_of_commute hp ((mem_nbhd_one_iff hz).2 ⟨htD, hc⟩) hpt

theorem mem_fiveLines_iff (h : Hyp G D) (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D)
    {c p : G} (hp : p ∈ D) (hc : c ∈ D) (h5 : orderOf (p * c) = 5) {y : Fin 5 → G}
    (hy : ∀ k, y k ∈ D) (hyp : ∀ k, Commute p (y k)) (hypD : ∀ k, p * y k ∈ D)
    (hy3 : ∀ k, orderOf (c * y k) = 3)
    (hu : y 0 * y 1 * y 2 * y 3 * y 4 * (y 0 * y 1 * y 2 * y 3 * y 4) = 1)
    (huc : Commute (y 0 * y 1 * y 2 * y 3 * y 4) c) {w : G} (hw : w ∈ collinearSet D p) :
    (∃ k, w = y k ∨ w = p * y k) ↔ (orderOf (c * w) = 3 ∨ orderOf (c * (p * w)) = 3) := by
  have hp2 := h.root.mul_self_eq_one hp
  have hpp : ∀ g : G, p * (p * g) = g := fun g => by rw [← mul_assoc, hp2, one_mul]
  constructor
  · rintro ⟨k, rfl | rfl⟩
    · exact Or.inl (hy3 k)
    · rw [hpp]
      exact Or.inr (hy3 k)
  · rintro (h3 | h3)
    · exact eq_line_of_five' h hNL hNP hPl hp hc h5 hy hyp hypD hu huc hw.1 hw.2.1 hw.2.2 h3
    · obtain ⟨k, hk⟩ := eq_line_of_five' h hNL hNP hPl hp hc h5 hy hyp hypD hu huc hw.2.2
        ((Commute.refl p).mul_right hw.2.1) (by rw [hpp]; exact hw.1) h3
      rcases hk with e | e
      · exact ⟨k, Or.inr (by rw [← hpp w, e])⟩
      · exact ⟨k, Or.inl (mul_left_cancel e)⟩

theorem injective_lineIdx :
    ∀ i : Fin 4, Function.Injective (![![1, 0, 1, 1] i, 2, 3, 4] : Fin 4 → Fin 5) := by
  decide

theorem false_of_threeNear (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hNL : NoLevi D)
    (hPl : ExcNoPlane D) {c p : G} (hc : c ∈ D) (hp : p ∈ D) (hp3 : p ∉ nbhd D c 3)
    (hT : ThreeNear D c p) (h3 : (collinearSet D p).ncard % 3 ≠ 1) : False := by
  have := h.finite
  have hclass := h.isClass
  have hD := h.root
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => h.conj_mem g hx
  have hNP := hNL.noPolar hclass hD hsing hPl
  have hP1 := p1_of_noPolar_noPlane h hNP hPl
  have hQ := commLambda_of_noPolar_noPlane hD hconj hNP hPl
  have hp2 := hD.mul_self_eq_one hp
  have hpp : ∀ g : G, p * (p * g) = g := fun g => by rw [← mul_assoc, hp2, one_mul]
  obtain ⟨x, hx, hx3, hne⟩ := hT
  have hp4 : p ∈ nbhd D c 4 := mem_nbhd_succ_of_commute hp (hx3 0) (hx 0).2.1
  have h5 := orderOf_eq_five_of_mem_nbhd_four hclass hD hNL hNP hPl hP1 hp hc hp4 hp3
  have hTO := (totallyOpposite_iff_not_mem_nbhd_three hD hNL hc hp).2 hp3
  have hord := fun i => orders_of_near h hNL hNP hPl hP1 hc hp hp4 hp3 (hx i) (hx3 i)
  have hcfg3 := lineConfig_of_lines' hD hconj hNL hNP hPl hp hc h5 (fun i => (hx i).1)
    (fun i => (hx i).2.1) (fun i => (hx i).2.2) hne (fun i => (hord i).1) (fun i => (hord i).2)
  obtain ⟨hK, hyD, hyp, hypD, hy3, -, huK, hu⟩ := fivePoints_spec h hNP hp hc h5 hTO hcfg3
    (fun i => (hx i).1) (fun i => (hx i).2.1) (fun i => (hx i).2.2) (fun i => (hord i).1)
    (fun i => (hord i).2)
  have hyne := fivePoints_ne hD hp hc h5 hcfg3
  set y := fivePoints hcfg3 with hy_def
  have huc : Commute (y 0 * y 1 * y 2 * y 3 * y 4) c := huK c ⟨_, threeLinesHom_one hcfg3⟩
  have hy0 : y 0 = x 0 := rfl
  have hy1 : y 1 = x 1 := rfl
  set x₂ : Fin 2 → G := ![x 0, x 1] with hx₂_def
  have hx₂ : ∀ i, x₂ i ∈ collinearSet D p := fun i => by fin_cases i; exacts [hx 0, hx 1]
  have hx₂3 : ∀ i, x₂ i ∈ nbhd D c 3 := fun i => by fin_cases i; exacts [hx3 0, hx3 1]
  have hcfg2 := lineConfig_of_two_near hclass hD hNL hNP hPl hP1 hc hp hp4 hp3 hx₂ hx₂3
    (hne 0 1 (by decide)).1 (hne 0 1 (by decide)).2
  obtain ⟨hzp, hzc, -, hz3⟩ := zEl_facts hcfg2
  set z := zEl p c x₂ with hz_def
  have hlines : ∀ k k' : Fin 5, ∀ b b' : Bool, k ≠ k' → linePt p (y k) b ≠ linePt p (y k') b' := by
    intro k k' b b' hkk' e
    obtain ⟨h1, h2⟩ := hyne k k' hkk'
    cases b <;> cases b' <;> simp only [linePt, Bool.cond_false, Bool.cond_true] at e
    · exact h1 e.symm
    · exact h2 (by rw [e, hpp])
    · exact h2 e.symm
    · exact h1 (mul_left_cancel e).symm
  have hne1 : ∀ k, y k ≠ p * y k := fun k e => hD.ne_one hp (by
    have := congrArg (· * (y k)⁻¹) e
    simpa using this.symm)
  set S : Set G := {r | r ∈ collinearSet D p ∧ ∀ k, r ≠ y k ∧ r ≠ p * y k} with hS_def
  have hmem : ∀ w ∈ collinearSet D p,
      (∃ k, w = y k ∨ w = p * y k) ↔ (orderOf (c * w) = 3 ∨ orderOf (c * (p * w)) = 3) :=
    fun w hw => mem_fiveLines_iff h hNL hNP hPl hp hc h5 hyD hyp hypD hy3 hu huc hw
  have hconjp : ∀ s : G, z * (p * s) * z⁻¹ = p * (z * s * z⁻¹) := fun s => by
    rw [show z * (p * s) * z⁻¹ = z * p * s * z⁻¹ by group, hzp.eq]; group
  have hconjc : ∀ s : G, z * (c * s) * z⁻¹ = c * (z * s * z⁻¹) := fun s => by
    rw [show z * (c * s) * z⁻¹ = z * c * s * z⁻¹ by group, hzc.eq]; group
  have hord_conj : ∀ g : G, orderOf (z * g * z⁻¹) = orderOf g := fun g => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hSz : ∀ s ∈ S, z * s * z⁻¹ ∈ S := by
    rintro s ⟨⟨hsD, hps, hpsD⟩, hsy⟩
    have hs' : z * s * z⁻¹ ∈ collinearSet D p := by
      refine ⟨conj_mem_of_isClass hclass z hsD, ?_, ?_⟩
      · have := (Commute.conj_iff z).2 hps
        rwa [show z * p * z⁻¹ = p by rw [hzp.eq, mul_inv_cancel_right]] at this
      · rw [← hconjp]
        exact conj_mem_of_isClass hclass z hpsD
    refine ⟨hs', fun k => ⟨fun e => ?_, fun e => ?_⟩⟩ <;>
    · have h1 := (hmem _ hs').1 ⟨k, by simp [e]⟩
      rw [← hconjc, hord_conj, ← hconjp, ← hconjc, hord_conj] at h1
      obtain ⟨k', hk'⟩ := (hmem s ⟨hsD, hps, hpsD⟩).2 h1
      rcases hk' with hk' | hk'
      · exact (hsy k').1 hk'
      · exact (hsy k').2 hk'
  have hcardS : S.ncard + 10 = (collinearSet D p).ncard := by
    set e : Fin 5 × Bool → G := fun kb => linePt p (y kb.1) kb.2 with he
    have he_inj : Function.Injective e := by
      rintro ⟨k, b⟩ ⟨k', b'⟩ hkb
      by_cases hk : k = k'
      · subst hk
        cases b <;> cases b' <;> simp only [he, linePt, Bool.cond_false, Bool.cond_true] at hkb
        · rfl
        · exact absurd hkb (hne1 k)
        · exact absurd hkb.symm (hne1 k)
        · rfl
      · exact absurd hkb (hlines k k' b b' hk)
    have hT : Set.range e ⊆ collinearSet D p := by
      rintro _ ⟨⟨k, b⟩, rfl⟩
      cases b
      · exact ⟨hyD k, hyp k, hypD k⟩
      · exact mul_mem_collinearSet hD hp ⟨hyD k, hyp k, hypD k⟩
    have hSe : S = collinearSet D p \ Set.range e := by
      ext r
      simp only [hS_def, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_range, Prod.exists, he,
        linePt, not_exists]
      constructor
      · rintro ⟨hr, hry⟩
        refine ⟨hr, fun k b => ?_⟩
        cases b
        · exact fun e => (hry k).1 e.symm
        · exact fun e => (hry k).2 e.symm
      · rintro ⟨hr, hry⟩
        exact ⟨hr, fun k => ⟨fun e => hry k false e.symm, fun e => hry k true e.symm⟩⟩
    have hcard : (Set.range e).ncard = 10 := by
      rw [Set.ncard_range_of_injective he_inj, Nat.card_eq_fintype_card]
      rfl
    rw [hSe, Set.ncard_sdiff hT, hcard]
    have := Set.ncard_le_ncard hT (Set.toFinite _)
    omega
  obtain ⟨q, ⟨hq, hqy⟩, hzq⟩ := exists_conj_fixed hz3 hSz (by omega)
  have hzq' : Commute z q := mul_inv_eq_iff_eq_mul.1 hzq
  have hq2 : q ∉ nbhd D c 2 := fun h2 => hp3 (mem_nbhd_succ_of_commute hp h2 hq.2.1)
  obtain ⟨-, hodd⟩ := (not_mem_nbhd_two_iff hD hNL hc hq.1).1 hq2
  have hqx₂ : ∀ i, q ≠ x₂ i ∧ q ≠ p * x₂ i := fun i => by
    fin_cases i
    · exact hqy 0
    · exact hqy 1
  have hY := sq_q_yPt (c := c) hclass hD hNL hNP hPl hp hx₂ hq hqx₂
  have hW := pow_three_q_wPt hclass hD hsing hQ hNL hNP hPl hP1 hcfg2 hp hx₂ hq hqx₂
  have hZ : ∀ i, (q * zPt p c x₂ i) ^ 5 = 1 := by
    intro i
    obtain ⟨hp3z, hp2z, hs4, ha3⟩ := zPt_facts hclass hD hNL hNP hP1 hcfg2 hp hx₂ i
    have hzD := zPt_mem (c := c) (x := x₂) hclass hp i
    have ha := yPt_mem (c := c) hD hp hx₂ (farZ i)
    have hpa : p ∈ collinearSet D (yPt p c x₂ (farZ i)) :=
      ⟨hp, ha.2.1.symm, by rw [← ha.2.1.eq]; exact ha.2.2⟩
    have hq3 : q ∉ nbhd D (zPt p c x₂ i) 3 := by
      intro hq3
      obtain ⟨s₂, hs₂D, hps₂, hs₂4, hs₂y⟩ : ∃ s₂, s₂ ∈ D ∧ Commute p s₂ ∧
          orderOf (s₂ * zPt p c x₂ i) = 4 ∧ ∀ k b, s₂ ≠ linePt p (y k) b := by
        rcases special_of_mem_nbhd_three hD hNL hNP hP1 hzD hp hp3z hp2z hq hq3 with h4 | h4
        · refine ⟨q, hq.1, hq.2.1, h4, fun k b => ?_⟩
          cases b
          · exact (hqy k).1
          · exact (hqy k).2
        · refine ⟨p * q, hq.2.2, (Commute.refl p).mul_right hq.2.1, h4, fun k b e => ?_⟩
          cases b <;> simp only [linePt, Bool.cond_false, Bool.cond_true] at e
          · exact (hqy k).2 (by rw [← e, hpp])
          · exact (hqy k).1 (mul_left_cancel e)
      set ℓ : Fin 4 → Fin 5 := ![![1, 0, 1, 1] i, 2, 3, 4] with hℓ
      set β : Fin 4 → Bool := ![![true, false, false, true] i, tD i, tD i, tD i] with hβ
      have hℓinj : Function.Injective ℓ := injective_lineIdx i
      have hnear : yPt p c x₂ (nearZ i) = linePt p (y (ℓ 0)) (β 0) := by
        obtain ⟨e0, e1, e2, e3⟩ := yPt_eq p c x₂
        fin_cases i
        · exact e2
        · exact e1
        · exact e3
        · exact e2
      set s : Fin 5 → G := Fin.snoc (fun j : Fin 4 => linePt p (y (ℓ j)) (β j)) s₂ with hs
      have hsl : ∀ j : Fin 4, s (Fin.castSucc j) = linePt p (y (ℓ j)) (β j) := fun j => by
        rw [hs, Fin.snoc_castSucc]
      have hsr : s (Fin.last 4) = s₂ := by rw [hs, Fin.snoc_last]
      have hlD : ∀ k b, linePt p (y k) b ∈ D := fun k b => by
        cases b
        · exact hyD k
        · exact hypD k
      have hlp : ∀ k b, Commute p (linePt p (y k) b) := fun k b => by
        cases b
        · exact hyp k
        · exact (Commute.refl p).mul_right (hyp k)
      have hsD : ∀ j, s j ∈ D := fun j => by
        cases j using Fin.lastCases with
        | last => rw [hsr]; exact hs₂D
        | cast j => rw [hsl]; exact hlD _ _
      have hps : ∀ j, Commute p (s j) := fun j => by
        cases j using Fin.lastCases with
        | last => rw [hsr]; exact hps₂
        | cast j => rw [hsl]; exact hlp _ _
      have hs4' : ∀ j, orderOf (s j * zPt p c x₂ i) = 4 := fun j => by
        cases j using Fin.lastCases with
        | last => rw [hsr]; exact hs₂4
        | cast j =>
          rw [hsl]
          fin_cases j
          · show orderOf (linePt p (y (ℓ 0)) (β 0) * zPt p c x₂ i) = 4
            rw [← hnear]
            exact hs4
          · exact orderOf_linePt_zPt hclass hD hNL hNP hP1 hp hcfg3 hcfg2 hx₂ hyD hyp hypD i 0
          · exact orderOf_linePt_zPt hclass hD hNL hNP hP1 hp hcfg3 hcfg2 hx₂ hyD hyp hypD i 1
          · exact orderOf_linePt_zPt hclass hD hNL hNP hP1 hp hcfg3 hcfg2 hx₂ hyD hyp hypD i 2
      have hsinj : Function.Injective s := by
        intro j l hjl
        cases j using Fin.lastCases with
        | last =>
          cases l using Fin.lastCases with
          | last => rfl
          | cast l => rw [hsr, hsl] at hjl; exact absurd hjl (hs₂y _ _)
        | cast j =>
          cases l using Fin.lastCases with
          | last => rw [hsr, hsl] at hjl; exact absurd hjl.symm (hs₂y _ _)
          | cast l =>
            rw [hsl, hsl] at hjl
            by_cases hjl' : j = l
            · rw [hjl']
            · exact absurd hjl (hlines _ _ _ _ fun e => hjl' (hℓinj e))
      obtain ⟨v, hv, hv3, hvne⟩ := reflect_family hclass hD hNL hNP hPl hP1 hzD ha.1 ha3 hpa
        hp3z hsD hps hs4' hsinj
      exact not_six_near h hNP hNL hPl hP1 hzD ha.1
        (mem_nbhd_succ_of_commute ha.1 hp3z ha.2.1.symm) ha3 hv hv3 hvne
    have hq4 : q ∈ nbhd D (zPt p c x₂ i) 4 := mem_nbhd_succ_of_commute hq.1 hp3z hq.2.1.symm
    rw [← orderOf_eq_five_of_mem_nbhd_four hclass hD hNL hNP hPl hP1 hq.1 hzD hq4 hq3]
    exact pow_orderOf_eq_one _
  exact hD.ne_one hq.1 (eq_one_of_relations hcfg2 hzq' (hD.mul_self_eq_one hq.1) hq.2.1 hY hW hZ
    hodd)

theorem excThreeNearInput : ExcThreeNearInput := by
  intro G _ D hH hsing hNL hPl h3 c hc p hp hp3 hT
  exact false_of_threeNear hH hsing hNL hPl hc hp hp3 hT (h3 p hp)

end CFSG.Timmesfeld.Moufang.Deep
