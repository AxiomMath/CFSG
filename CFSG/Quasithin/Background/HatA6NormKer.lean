module

public import CFSG.Quasithin.Background.HatA6NormFrame

public section

namespace CFSG.Quasithin.HatA6

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
open CFSG.Quasithin.H13.Orbit

@[expose] def frobVec :
    Multiplicative (Fin 3 → FieldFour) ≃* Multiplicative (Fin 3 → FieldFour) where
  toFun c := Multiplicative.ofAdd fun i => frob (Multiplicative.toAdd c i)
  invFun c := Multiplicative.ofAdd fun i => frob (Multiplicative.toAdd c i)
  left_inv c := by
    apply Multiplicative.ofAdd.injective
    funext i
    exact frob_frob _
  right_inv c := by
    apply Multiplicative.ofAdd.injective
    funext i
    exact frob_frob _
  map_mul' c d := by
    apply_fun Multiplicative.toAdd
    funext i
    change frob (Multiplicative.toAdd c i + Multiplicative.toAdd d i) =
      frob (Multiplicative.toAdd c i) + frob (Multiplicative.toAdd d i)
    exact map_add frob _ _

variable {W : Type} [CommGroup W]

@[expose] noncomputable def frobAt {hsq : ∀ w : W, w * w = 1} {z : MulAut W} {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom hsq z v)) : MulAut W :=
  ((coordEquiv hb).symm.trans frobVec).trans (coordEquiv hb)

variable [Finite W] {K : Subgroup (MulAut W)} {z : ↥K} {f : W}

private lemma frobVec_fsmul_ω (c : Multiplicative (Fin 3 → FieldFour)) :
    frobVec (Multiplicative.ofAdd (ω • Multiplicative.toAdd c)) =
      Multiplicative.ofAdd (ω₂ • Multiplicative.toAdd (frobVec c)) := by
  apply Multiplicative.ofAdd.injective
  funext i
  change frob (ω * Multiplicative.toAdd c i) = ω₂ * frob (Multiplicative.toAdd c i)
  rw [map_mul, frob_ω]

private lemma frobVec_ω_frob (c : Multiplicative (Fin 3 → FieldFour)) :
    frobVec (Multiplicative.ofAdd (ω • Multiplicative.toAdd (frobVec c))) =
      Multiplicative.ofAdd (ω₂ • Multiplicative.toAdd c) := by
  have h := frobVec_fsmul_ω (frobVec c)
  have h2 : frobVec (frobVec c) = c := by
    ext i <;> simp [frobVec, frob_frob]
  rw [h, h2]

omit [Finite W] in
private lemma frobAt_apply_coord {hsq : ∀ w : W, w * w = 1} {z : MulAut W} {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom hsq z v)) (c : Multiplicative (Fin 3 → FieldFour)) :
    frobAt hb (coordEquiv hb c) = coordEquiv hb (frobVec c) := by
  simp [frobAt]

omit [Finite W] in
private lemma frobAt_involutive {hsq : ∀ w : W, w * w = 1} {z : MulAut W} {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom hsq z v)) :
    frobAt hb * frobAt hb = 1 := by
  ext w
  set c := (coordEquiv hb).symm w with hc
  have hw : coordEquiv hb c = w := by simp [hc]
  rw [← hw]
  rw [MulAut.mul_apply, frobAt_apply_coord hb c, frobAt_apply_coord hb (frobVec c)]
  exact congrArg (coordEquiv hb) (by ext i <;> simp [frobVec, frob_frob])

private lemma frob_ovalVec_lt4 {i : Fin 6} (hi : i < 4) :
    (fun j => frob (ovalVec i j)) = ovalVec i := by
  fin_cases i <;> simp_all <;> decide

private lemma frob_ovalVec_4 :
    (fun j => frob (ovalVec 4 j)) = ovalVec 5 := by
  decide

private lemma frob_ovalVec_5 :
    (fun j => frob (ovalVec 5 j)) = ovalVec 4 := by
  decide

private def frobIndex (i : Fin 6) : Fin 6 :=
  if i = 4 then 5 else if i = 5 then 4 else i

private lemma frobVec_ovalVec (i : Fin 6) :
    (fun j => frob (ovalVec i j)) = ovalVec (frobIndex i) := by
  unfold frobIndex
  split_ifs with h1 h2
  · rw [h1]; exact frob_ovalVec_4
  · rw [h2]; exact frob_ovalVec_5
  · have hi6 : (i : ℕ) < 6 := i.isLt
    have hi : i < 4 := by omega
    exact frob_ovalVec_lt4 hi

private lemma frob_ne_zero {k : FieldFour} (hk : k ≠ 0) : frob k ≠ 0 := by
  intro h
  apply hk
  have hinj : Function.Injective frob := frob.injective
  exact hinj (by rw [h, map_zero])

private lemma frobVec_mem_ovalStd {c : Multiplicative (Fin 3 → FieldFour)} (hc : c ∈ ovalStd) :
    frobVec c ∈ ovalStd := by
  rcases hc with ⟨k, hk, i, hi⟩
  refine ⟨frob k, frob_ne_zero hk, ⟨frobIndex i, ?_⟩⟩
  funext j
  change frob (Multiplicative.toAdd c j) = frob k * ovalVec (frobIndex i) j
  rw [hi]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [map_mul]
  have h := congr_fun (frobVec_ovalVec i) j
  rw [h]

private lemma frobVec_image_ovalStd : ⇑frobVec '' ovalStd = ovalStd := by
  ext c
  constructor
  · rintro ⟨d, hd, h_eq⟩
    rw [← h_eq]
    exact frobVec_mem_ovalStd hd
  · intro hc
    refine ⟨frobVec c, frobVec_mem_ovalStd hc, ?_⟩
    ext i <;> simp [frobVec, frob_frob]

omit [Finite W] in
private lemma frobAt_image_coord {hsq : ∀ w : W, w * w = 1} {z : MulAut W} {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom hsq z v)) (A : Set (Multiplicative (Fin 3 → FieldFour))) :
    ⇑(frobAt hb) '' (coordEquiv hb '' A) = coordEquiv hb '' (⇑frobVec '' A) := by
  ext w
  constructor
  · rintro ⟨u, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨frobVec c, ⟨c, hc, rfl⟩, ?_⟩
    exact (frobAt_apply_coord hb c).symm
  · rintro ⟨d, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨coordEquiv hb c, ⟨c, hc, rfl⟩, ?_⟩
    exact frobAt_apply_coord hb c

omit [Finite W] in
private lemma coordEquiv_ovalVec_0 {hsq : ∀ w : W, w * w = 1} {z : MulAut W}
    {v : Fin 3 → W} (hb : Function.Bijective (coordHom hsq z v)) :
    coordEquiv hb (Multiplicative.ofAdd (ovalVec 0)) = v 0 := by
  rw [coordEquiv_apply, coordHom_apply]
  simp [ovalVec, fsmul_one, fsmul_zero]

omit [Finite W] in
private lemma coordEquiv_ovalVec_1 {hsq : ∀ w : W, w * w = 1} {z : MulAut W}
    {v : Fin 3 → W} (hb : Function.Bijective (coordHom hsq z v)) :
    coordEquiv hb (Multiplicative.ofAdd (ovalVec 1)) = v 1 := by
  rw [coordEquiv_apply, coordHom_apply]
  simp [ovalVec, fsmul_one, fsmul_zero]

omit [Finite W] in
private lemma coordEquiv_ovalVec_2 {hsq : ∀ w : W, w * w = 1} {z : MulAut W}
    {v : Fin 3 → W} (hb : Function.Bijective (coordHom hsq z v)) :
    coordEquiv hb (Multiplicative.ofAdd (ovalVec 2)) = v 2 := by
  rw [coordEquiv_apply, coordHom_apply]
  simp [ovalVec, fsmul_one, fsmul_zero]

omit [Finite W] in
private lemma coordEquiv_ovalVec_3 {hsq : ∀ w : W, w * w = 1} {z : MulAut W}
    {v : Fin 3 → W} (hb : Function.Bijective (coordHom hsq z v)) :
    coordEquiv hb (Multiplicative.ofAdd (ovalVec 3)) = v 0 * v 1 * v 2 := by
  rw [coordEquiv_apply, coordHom_apply]
  simp [ovalVec, fsmul_one]

omit [Finite W] in
private lemma mem_pt_iff {z : MulAut W} (hzz : ∀ w, z (z w) = w * z w) {x w : W} :
    x ∈ pt z w ↔ x = w ∨ x = fsmul z ω w ∨ x = fsmul z ω₂ w := by
  simp only [pt, Set.mem_insert_iff, Set.mem_singleton_iff, fsmul_ω]
  rw [fsmul_ω₂ hzz]

omit [Finite W] in
private lemma s_fix_mem_pt {hsq : ∀ w : W, w * w = 1} {z : MulAut W} {v : Fin 3 → W}
    {i : Fin 6} {s : MulAut W}
    (hfix : ⇑s '' pt z (coordHom hsq z v (Multiplicative.ofAdd (ovalVec i))) =
      pt z (coordHom hsq z v (Multiplicative.ofAdd (ovalVec i)))) :
    s (coordHom hsq z v (Multiplicative.ofAdd (ovalVec i))) ∈
      pt z (coordHom hsq z v (Multiplicative.ofAdd (ovalVec i))) := by
  have hmem : coordHom hsq z v (Multiplicative.ofAdd (ovalVec i)) ∈
      pt z (coordHom hsq z v (Multiplicative.ofAdd (ovalVec i))) := by
    simp [pt]
  have := Set.mem_image_of_mem s hmem
  rwa [hfix] at this

private lemma ofAdd_ovalVec_mem_ovalStd (i : Fin 6) :
    Multiplicative.ofAdd (ovalVec i) ∈ ovalStd :=
  ⟨1, one_ne_zero, i, by rw [toAdd_ofAdd, one_smul]⟩

private lemma coordEquiv_ovalVec_mem_orbit (S : Setup W K z f) {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom S.sq (z : MulAut W) v))
    (hO : orbitIn K f = coordHom S.sq (z : MulAut W) v '' ovalStd) (i : Fin 6) :
    coordEquiv hb (Multiplicative.ofAdd (ovalVec i)) ∈ orbitIn K f := by
  rw [hO]
  exact ⟨Multiplicative.ofAdd (ovalVec i), ofAdd_ovalVec_mem_ovalStd i, rfl⟩

private lemma pt_ovalVec_mem_points (S : Setup W K z f) {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom S.sq (z : MulAut W) v))
    (hO : orbitIn K f = coordHom S.sq (z : MulAut W) v '' ovalStd) (i : Fin 6) :
    pt (z : MulAut W) (coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec i))) ∈
      points (z : MulAut W) (orbitIn K f) :=
  ⟨_, coordEquiv_ovalVec_mem_orbit S hb hO i, rfl⟩

private lemma ovalVec_ne_smul :
    ∀ (i j : Fin 6) (c : FieldFour), i ≠ j → c ≠ 0 → ovalVec i ≠ c • ovalVec j := by
  decide +kernel

private lemma pt_ovalVec_ne (S : Setup W K z f) {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom S.sq (z : MulAut W) v)) {i j : Fin 6} (hij : i ≠ j) :
    pt (z : MulAut W) (coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec i))) ≠
      pt (z : MulAut W) (coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec j))) := by
  have hzz := S.zz
  intro h
  have hmem : coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec i)) ∈
      pt (z : MulAut W) (coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec j))) :=
    (pt_eq_pt_iff S.pow_three).1 h
  rw [mem_pt_iff hzz] at hmem
  have hzj : (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec j))) =
      coordEquiv hb (Multiplicative.ofAdd (FieldFour.ω • ovalVec j)) := by
    rw [← fsmul_ω (z := (z : MulAut W)), coordEquiv_smul hb hzz]
  have hzj2 : (z : MulAut W) ((z : MulAut W)
      (coordEquiv hb (Multiplicative.ofAdd (ovalVec j)))) =
      coordEquiv hb (Multiplicative.ofAdd (FieldFour.ω₂ • ovalVec j)) := by
    rw [coordEquiv_smul hb hzz]
    exact (fsmul_ω₂ hzz
      (coordEquiv hb (Multiplicative.ofAdd (ovalVec j)))).symm
  rcases hmem with h1 | h1 | h1
  · have hvec : ovalVec i = ovalVec j :=
      Multiplicative.ofAdd.injective ((coordEquiv hb).injective h1)
    exact ovalVec_ne_smul i j 1 hij (by decide) (by simpa using hvec)
  · have h1' : coordEquiv hb (Multiplicative.ofAdd (ovalVec i)) =
        coordEquiv hb (Multiplicative.ofAdd (FieldFour.ω • ovalVec j)) := by
      rw [← hzj]
      exact h1.trans (fsmul_ω (z := (z : MulAut W)) _)
    have hvec : ovalVec i = FieldFour.ω • ovalVec j :=
      Multiplicative.ofAdd.injective ((coordEquiv hb).injective h1')
    exact ovalVec_ne_smul i j FieldFour.ω hij (by decide) hvec
  · have h1' : coordEquiv hb (Multiplicative.ofAdd (ovalVec i)) =
        coordEquiv hb (Multiplicative.ofAdd (FieldFour.ω₂ • ovalVec j)) := by
      rw [← hzj2]
      exact h1.trans (fsmul_ω₂ hzz _)
    have hvec : ovalVec i = FieldFour.ω₂ • ovalVec j :=
      Multiplicative.ofAdd.injective ((coordEquiv hb).injective h1')
    exact ovalVec_ne_smul i j FieldFour.ω₂ hij (by decide) hvec

omit [Finite W] in
private lemma image_pt_eq_self_of_pointPerm_eq_one {z : MulAut W} {O : Set W}
    (h3 : z ^ 3 = 1) (s : ↥(semiStab z O))
    (hs : pointPerm h3 s = 1) {w : W} (hw : w ∈ O) : ⇑(s : MulAut W) '' pt z w = pt z w := by
  rw [image_pt h3 (mem_semiStab_iff.1 s.2).1 w,
    (pt_eq_pt_iff h3).2 ((pointPerm_eq_one_iff h3 s).1 hs w hw)]

private lemma frobAt_ovalVec_lt4 (S : Setup W K z f) {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom S.sq (z : MulAut W) v)) {i : Fin 6} (hi : i < 4) :
    frobAt hb (coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec i))) =
      coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec i)) := by
  change frobAt hb (coordEquiv hb (Multiplicative.ofAdd (ovalVec i))) =
    coordEquiv hb (Multiplicative.ofAdd (ovalVec i))
  rw [frobAt_apply_coord hb]
  congr 1
  change Multiplicative.ofAdd (fun j => frob (ovalVec i j)) =
    Multiplicative.ofAdd (ovalVec i)
  rw [frob_ovalVec_lt4 hi]

private lemma frobAt_ovalVec_4 (S : Setup W K z f) {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom S.sq (z : MulAut W) v)) :
    frobAt hb (coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec 4))) =
      coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec 5)) := by
  change frobAt hb (coordEquiv hb (Multiplicative.ofAdd (ovalVec 4))) =
    coordEquiv hb (Multiplicative.ofAdd (ovalVec 5))
  rw [frobAt_apply_coord hb]
  congr 1
  change Multiplicative.ofAdd (fun j => frob (ovalVec 4 j)) =
    Multiplicative.ofAdd (ovalVec 5)
  rw [frob_ovalVec_4]

theorem Setup.frobAt_conj (S : Setup W K z f) {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom S.sq (z : MulAut W) v)) :
    frobAt hb * (z : MulAut W) * (frobAt hb)⁻¹ = (z : MulAut W)⁻¹ := by
  have hzz := S.zz
  have hinv : (frobAt hb)⁻¹ = frobAt hb :=
    inv_eq_of_mul_eq_one_left (frobAt_involutive hb)
  have hzsq : (z : MulAut W) * (z : MulAut W) = (z : MulAut W)⁻¹ := by
    have h3 : (z : MulAut W) ^ 3 = 1 := S.pow_three
    have h : (z : MulAut W) * (z : MulAut W) * (z : MulAut W) = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using h3
    exact eq_inv_of_mul_eq_one_left h
  ext w
  set c := (coordEquiv hb).symm w with hc
  have hw : coordEquiv hb c = w := by simp [hc]
  rw [← hw]
  rw [hinv]
  simp only [MulAut.mul_apply]
  rw [frobAt_apply_coord hb c]
  have hz1 : (z : MulAut W) (coordEquiv hb (frobVec c)) =
      coordEquiv hb (Multiplicative.ofAdd (ω • Multiplicative.toAdd (frobVec c))) := by
    rw [← fsmul_ω]
    change fsmul (z : MulAut W) FieldFour.ω
      (coordEquiv hb (Multiplicative.ofAdd (Multiplicative.toAdd (frobVec c)))) =
      coordEquiv hb (Multiplicative.ofAdd (ω • Multiplicative.toAdd (frobVec c)))
    rw [← coordEquiv_smul hb hzz FieldFour.ω (Multiplicative.toAdd (frobVec c))]
  rw [hz1]
  rw [frobAt_apply_coord hb]
  rw [frobVec_ω_frob]
  rw [← hzsq]
  rw [MulAut.mul_apply]
  rw [coordEquiv_smul hb hzz]
  have hω₂ : FieldFour.ω₂ = FieldFour.ω * FieldFour.ω := by decide
  rw [hω₂, fsmul_mul S.sq hzz, fsmul_ω, fsmul_ω]
  rfl

theorem Setup.frobAt_mem_semiStab (S : Setup W K z f) {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom S.sq (z : MulAut W) v))
    (hO : orbitIn K f = coordHom S.sq (z : MulAut W) v '' ovalStd) :
    frobAt hb ∈ semiStab (z : MulAut W) (orbitIn K f) := by
  rw [mem_semiStab_iff]
  constructor
  · right
    exact Setup.frobAt_conj S hb
  · rw [hO]
    change ⇑(frobAt hb) '' (coordEquiv hb '' ovalStd) = coordEquiv hb '' ovalStd
    rw [frobAt_image_coord hb ovalStd, frobVec_image_ovalStd]

theorem Setup.mem_zpowers_of_fix_frame (S : Setup W K z f) {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom S.sq (z : MulAut W) v)) {s : MulAut W}
    (hs : s * (z : MulAut W) = (z : MulAut W) * s)
    (hfix : ∀ i : Fin 6, i < 4 →
      ⇑s '' pt (z : MulAut W) (coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec i))) =
        pt (z : MulAut W) (coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec i)))) :
    s ∈ Subgroup.zpowers (z : MulAut W) := by
  have hzz := S.zz
  have hx : ∀ w : W, s ((z : MulAut W) w) = (z : MulAut W) (s w) := by
    intro w
    have := congrArg (fun f : MulAut W => f w) hs
    simpa [MulAut.mul_apply] using this
  have hP0 : coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec 0)) = v 0 :=
    coordEquiv_ovalVec_0 (hsq := S.sq) hb
  have hP1 : coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec 1)) = v 1 :=
    coordEquiv_ovalVec_1 (hsq := S.sq) hb
  have hP2 : coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec 2)) = v 2 :=
    coordEquiv_ovalVec_2 (hsq := S.sq) hb
  have hP3 : coordHom S.sq (z : MulAut W) v (Multiplicative.ofAdd (ovalVec 3)) =
      v 0 * v 1 * v 2 :=
    coordEquiv_ovalVec_3 (hsq := S.sq) hb
  obtain ⟨a0, ha0, hs0⟩ :=
    exists_fsmul_of_mem_pt hzz
      (s_fix_mem_pt (hsq := S.sq) (hfix 0 (by decide)))
  obtain ⟨a1, ha1, hs1⟩ :=
    exists_fsmul_of_mem_pt hzz
      (s_fix_mem_pt (hsq := S.sq) (hfix 1 (by decide)))
  obtain ⟨a2, ha2, hs2⟩ :=
    exists_fsmul_of_mem_pt hzz
      (s_fix_mem_pt (hsq := S.sq) (hfix 2 (by decide)))
  obtain ⟨d, hd, hs3⟩ :=
    exists_fsmul_of_mem_pt hzz
      (s_fix_mem_pt (hsq := S.sq) (hfix 3 (by decide)))
  rw [hP0] at hs0
  rw [hP1] at hs1
  rw [hP2] at hs2
  rw [hP3] at hs3
  have h_eq : Multiplicative.ofAdd ![a0, a1, a2] =
      Multiplicative.ofAdd ![d, d, d] := by
    apply (coordEquiv hb).injective
    rw [coordEquiv_apply, coordEquiv_apply, coordHom_apply, coordHom_apply]
    simp
    have h1 : s (v 0 * v 1 * v 2) =
        fsmul (z : MulAut W) a0 (v 0) * fsmul (z : MulAut W) a1 (v 1) *
          fsmul (z : MulAut W) a2 (v 2) := by
      rw [map_mul, map_mul, hs0, hs1, hs2]
    have h2 : s (v 0 * v 1 * v 2) =
        fsmul (z : MulAut W) d (v 0) * fsmul (z : MulAut W) d (v 1) *
          fsmul (z : MulAut W) d (v 2) := by
      rw [hs3, fsmul_mul_right, fsmul_mul_right]
    rw [← h1, h2]
  have hfun : ![a0, a1, a2] = ![d, d, d] := Multiplicative.ofAdd.injective h_eq
  have ha0d : a0 = d := by simpa using congrFun hfun 0
  have ha1d : a1 = d := by simpa using congrFun hfun 1
  have ha2d : a2 = d := by simpa using congrFun hfun 2
  rw [ha0d] at hs0
  rw [ha1d] at hs1
  rw [ha2d] at hs2
  have hs_eq : ⇑s = fsmul (z : MulAut W) d := by
    funext w
    obtain ⟨c, rfl⟩ := (coordEquiv hb).surjective w
    rw [coordEquiv_apply, coordHom_apply]
    set c0 := Multiplicative.toAdd c 0
    set c1 := Multiplicative.toAdd c 1
    set c2 := Multiplicative.toAdd c 2
    calc
      s (fsmul (z : MulAut W) c0 (v 0) * fsmul (z : MulAut W) c1 (v 1) *
          fsmul (z : MulAut W) c2 (v 2))
          = s (fsmul (z : MulAut W) c0 (v 0)) * s (fsmul (z : MulAut W) c1 (v 1)) *
              s (fsmul (z : MulAut W) c2 (v 2)) := by
              rw [map_mul, map_mul]
      _ = fsmul (z : MulAut W) c0 (s (v 0)) * fsmul (z : MulAut W) c1 (s (v 1)) *
            fsmul (z : MulAut W) c2 (s (v 2)) := by
              rw [map_fsmul hx, map_fsmul hx, map_fsmul hx]
      _ = fsmul (z : MulAut W) c0 (fsmul (z : MulAut W) d (v 0)) *
            fsmul (z : MulAut W) c1 (fsmul (z : MulAut W) d (v 1)) *
              fsmul (z : MulAut W) c2 (fsmul (z : MulAut W) d (v 2)) := by
              rw [hs0, hs1, hs2]
      _ = fsmul (z : MulAut W) (c0 * d) (v 0) * fsmul (z : MulAut W) (c1 * d) (v 1) *
            fsmul (z : MulAut W) (c2 * d) (v 2) := by
              rw [← fsmul_mul S.sq hzz, ← fsmul_mul S.sq hzz, ← fsmul_mul S.sq hzz]
      _ = fsmul (z : MulAut W) (d * c0) (v 0) * fsmul (z : MulAut W) (d * c1) (v 1) *
            fsmul (z : MulAut W) (d * c2) (v 2) := by
              rw [mul_comm c0 d, mul_comm c1 d, mul_comm c2 d]
      _ = fsmul (z : MulAut W) d (fsmul (z : MulAut W) c0 (v 0)) *
            fsmul (z : MulAut W) d (fsmul (z : MulAut W) c1 (v 1)) *
              fsmul (z : MulAut W) d (fsmul (z : MulAut W) c2 (v 2)) := by
              rw [fsmul_mul S.sq hzz, fsmul_mul S.sq hzz, fsmul_mul S.sq hzz]
      _ = fsmul (z : MulAut W) d (fsmul (z : MulAut W) c0 (v 0) *
            fsmul (z : MulAut W) c1 (v 1) * fsmul (z : MulAut W) c2 (v 2)) := by
              rw [fsmul_mul_right, fsmul_mul_right]
  rcases hd with rfl | rfl | rfl
  · have h1 : s = 1 := by
      ext w
      have := congrFun hs_eq w
      simpa [fsmul_one] using this
    rw [h1]
    exact Subgroup.one_mem _
  · have h1 : s = (z : MulAut W) := by
      ext w
      have := congrFun hs_eq w
      simpa [fsmul_ω] using this
    rw [h1]
    exact Subgroup.mem_zpowers _
  · have h1 : s = (z : MulAut W) * (z : MulAut W) := by
      ext w
      have := congrFun hs_eq w
      rw [fsmul_ω₂ hzz] at this
      rw [MulAut.mul_apply]
      exact this
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

theorem Setup.mem_zpowers_of_pointPerm_eq_one (S : Setup W K z f) {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom S.sq (z : MulAut W) v))
    (hO : orbitIn K f = coordHom S.sq (z : MulAut W) v '' ovalStd)
    (s : ↥(semiStab (z : MulAut W) (orbitIn K f))) (hs : pointPerm S.pow_three s = 1) :
    (s : MulAut W) ∈ Subgroup.zpowers (z : MulAut W) := by
  have hw (i : Fin 6) : coordEquiv hb (Multiplicative.ofAdd (ovalVec i)) ∈ orbitIn K f :=
    coordEquiv_ovalVec_mem_orbit S hb hO i
  have hfix (i : Fin 6) : ⇑(s : MulAut W) '' pt (z : MulAut W)
      (coordEquiv hb (Multiplicative.ofAdd (ovalVec i))) =
      pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec i))) :=
    image_pt_eq_self_of_pointPerm_eq_one S.pow_three s hs (hw i)
  rcases (mem_semiStab_iff.mp s.2).1 with hconj | hconj
  · have hcomm : (s : MulAut W) * (z : MulAut W) = (z : MulAut W) * (s : MulAut W) := by
      have h := congrArg (fun x => x * (s : MulAut W)) hconj
      simpa [mul_assoc] using h
    exact Setup.mem_zpowers_of_fix_frame S hb hcomm (fun i _ => hfix i)
  · let t : MulAut W := (s : MulAut W) * frobAt hb
    have ht_conj : t * (z : MulAut W) * t⁻¹ = (z : MulAut W) := by
      have h1 : t * (z : MulAut W) * t⁻¹ =
          (s : MulAut W) * (frobAt hb * (z : MulAut W) * (frobAt hb)⁻¹) *
            (s : MulAut W)⁻¹ := by
        change ((s : MulAut W) * frobAt hb) * (z : MulAut W) *
          ((s : MulAut W) * frobAt hb)⁻¹ = _
        group
      rw [h1, Setup.frobAt_conj S hb]
      have h2 : (s : MulAut W) * (z : MulAut W)⁻¹ * (s : MulAut W)⁻¹ =
          ((s : MulAut W) * (z : MulAut W) * (s : MulAut W)⁻¹)⁻¹ := by group
      rw [h2, hconj]
      group
    have ht_comm : t * (z : MulAut W) = (z : MulAut W) * t := by
      have h := congrArg (fun x => x * t) ht_conj
      simpa [mul_assoc] using h
    have ht_fix : ∀ i : Fin 6, i < 4 →
        ⇑t '' pt (z : MulAut W) (coordHom S.sq (z : MulAut W) v
          (Multiplicative.ofAdd (ovalVec i))) =
        pt (z : MulAut W) (coordHom S.sq (z : MulAut W) v
          (Multiplicative.ofAdd (ovalVec i))) := by
      intro i hi
      have hfi : ⇑(frobAt hb) '' pt (z : MulAut W) (coordEquiv hb
          (Multiplicative.ofAdd (ovalVec i))) =
          pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec i))) := by
        rw [image_pt S.pow_three (mem_semiStab_iff.1 (Setup.frobAt_mem_semiStab S hb hO)).1]
        change pt (z : MulAut W) (frobAt hb (coordHom S.sq (z : MulAut W) v
          (Multiplicative.ofAdd (ovalVec i)))) =
          pt (z : MulAut W) (coordHom S.sq (z : MulAut W) v
            (Multiplicative.ofAdd (ovalVec i)))
        rw [frobAt_ovalVec_lt4 S hb hi]
      change ⇑t '' pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec i))) =
        pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec i)))
      change ⇑((s : MulAut W) * frobAt hb) '' pt (z : MulAut W)
          (coordEquiv hb (Multiplicative.ofAdd (ovalVec i))) =
        pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec i)))
      rw [MulAut.coe_mul, Set.image_comp, hfi, hfix i]
    have ht_zp : t ∈ Subgroup.zpowers (z : MulAut W) :=
      Setup.mem_zpowers_of_fix_frame S hb ht_comm ht_fix
    have ht_semi : t ∈ semiStab (z : MulAut W) (orbitIn K f) := by
      have h1 : t = (s : MulAut W) * frobAt hb := rfl
      rw [h1]
      exact (semiStab (z : MulAut W) (orbitIn K f)).mul_mem s.2
        (Setup.frobAt_mem_semiStab S hb hO)
    have ht_perm : pointPerm S.pow_three ⟨t, ht_semi⟩ = 1 := by
      refine MonoidHom.mem_ker.1 (zpowers_le_ker_pointPerm S.pow_three ?_)
      rw [Subgroup.mem_subgroupOf]
      exact ht_zp
    have hfr4 : ⇑(frobAt hb) '' pt (z : MulAut W) (coordEquiv hb
        (Multiplicative.ofAdd (ovalVec 4))) =
        pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec 5))) := by
      rw [image_pt S.pow_three (mem_semiStab_iff.1 (Setup.frobAt_mem_semiStab S hb hO)).1]
      change pt (z : MulAut W) (frobAt hb (coordHom S.sq (z : MulAut W) v
        (Multiplicative.ofAdd (ovalVec 4)))) =
        pt (z : MulAut W) (coordHom S.sq (z : MulAut W) v
          (Multiplicative.ofAdd (ovalVec 5)))
      rw [frobAt_ovalVec_4 S hb]
    have hP5 : ⇑t '' pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec 5))) =
        pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec 5))) :=
      image_pt_eq_self_of_pointPerm_eq_one S.pow_three ⟨t, ht_semi⟩ ht_perm (hw 5)
    have hs_eq : (s : MulAut W) = t * frobAt hb := by
      change (s : MulAut W) = ((s : MulAut W) * frobAt hb) * frobAt hb
      rw [mul_assoc, frobAt_involutive hb, mul_one]
    have h45 : pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec 4))) =
        pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec 5))) := by
      calc pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec 4)))
          = ⇑(s : MulAut W) '' pt (z : MulAut W)
              (coordEquiv hb (Multiplicative.ofAdd (ovalVec 4))) := (hfix 4).symm
        _ = ⇑(t * frobAt hb) '' pt (z : MulAut W)
              (coordEquiv hb (Multiplicative.ofAdd (ovalVec 4))) := by rw [← hs_eq]
        _ = ⇑t '' (⇑(frobAt hb) '' pt (z : MulAut W)
              (coordEquiv hb (Multiplicative.ofAdd (ovalVec 4)))) := by
              rw [MulAut.coe_mul, Set.image_comp]
        _ = ⇑t '' pt (z : MulAut W)
              (coordEquiv hb (Multiplicative.ofAdd (ovalVec 5))) := by rw [hfr4]
        _ = pt (z : MulAut W) (coordEquiv hb (Multiplicative.ofAdd (ovalVec 5))) := hP5
    exfalso
    exact pt_ovalVec_ne S hb (by decide : (4 : Fin 6) ≠ 5) h45

theorem Setup.card_semiStab_inf_centralizer_le (S : Setup W K z f) {v : Fin 3 → W}
    (hb : Function.Bijective (coordHom S.sq (z : MulAut W) v))
    (hO : orbitIn K f = coordHom S.sq (z : MulAut W) v '' ovalStd) :
    Nat.card ↥(semiStab (z : MulAut W) (orbitIn K f) ⊓
      Subgroup.centralizer ({(z : MulAut W)} : Set (MulAut W))) ≤ 1080 := by
  classical
  let zW : MulAut W := (z : MulAut W)
  let O : Set W := orbitIn K f
  let G : Subgroup (MulAut W) :=
    semiStab zW O ⊓ Subgroup.centralizer ({zW} : Set (MulAut W))
  let ψ : ↥G →* Equiv.Perm ↥(points zW O) :=
    (pointPerm S.pow_three).comp (Subgroup.inclusion inf_le_left)
  change Nat.card ↥G ≤ 1080
  have : Nontrivial W := by
    rw [← Finite.one_lt_card_iff_nontrivial, S.card]
    norm_num
  have hz_ne : zW ≠ 1 := by
    have hz : (z : MulAut W) ≠ 1 := by
      obtain ⟨w, hw⟩ := exists_ne (1 : W)
      intro h
      exact hw (S.fpf w (by rw [h]; rfl))
    simpa only [zW] using hz
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf zW = 3 := orderOf_eq_prime S.pow_three hz_ne
  have hker_le : ∀ x : ↥ψ.ker, (x : MulAut W) ∈ Subgroup.zpowers zW := by
    intro x
    have hx : pointPerm S.pow_three (Subgroup.inclusion inf_le_left (x : ↥G)) = 1 := by
      have h := MonoidHom.mem_ker.1 x.2
      simpa only [ψ, MonoidHom.comp_apply] using h
    exact Setup.mem_zpowers_of_pointPerm_eq_one S hb hO _ hx
  let toZ : ↥ψ.ker → Subgroup.zpowers zW := fun x => ⟨(x : MulAut W), hker_le x⟩
  have htoZ : Function.Injective toZ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : Subgroup.zpowers zW => (t : MulAut W)) hxy
  have hker_card : Nat.card ↥ψ.ker ≤ 3 := by
    have h := Nat.card_le_card_of_injective toZ htoZ
    rwa [Nat.card_zpowers, hord] at h
  have hP_mem (i : Fin 6) : pt zW (coordHom S.sq zW v (Multiplicative.ofAdd (ovalVec i))) ∈
      points zW O := by
    simpa only [zW, O] using pt_ovalVec_mem_points S hb hO i
  have hP_ne {i j : Fin 6} (hij : i ≠ j) :
      pt zW (coordHom S.sq zW v (Multiplicative.ofAdd (ovalVec i))) ≠
        pt zW (coordHom S.sq zW v (Multiplicative.ofAdd (ovalVec j))) := by
    simpa only [zW] using pt_ovalVec_ne S hb hij
  let P (i : Fin 6) : Set W :=
    pt zW (coordHom S.sq zW v (Multiplicative.ofAdd (ovalVec i)))
  let a : ↥(points zW O) := ⟨P 4, hP_mem 4⟩
  let b : ↥(points zW O) := ⟨P 5, hP_mem 5⟩
  let σ : Equiv.Perm ↥(points zW O) := Equiv.swap a b
  have hab : a ≠ b := by
    intro h
    exact hP_ne (by decide : (4 : Fin 6) ≠ 5) (congrArg Subtype.val h)
  have hσa : σ a = b := Equiv.swap_apply_left a b
  have hσx {x : ↥(points zW O)} (hxa : x ≠ a) (hxb : x ≠ b) : σ x = x :=
    Equiv.swap_apply_of_ne_of_ne hxa hxb
  have hσ_ne : σ ≠ 1 := by
    intro h
    have h1 : b = a := by
      have h := congrArg (fun f : Equiv.Perm ↥(points zW O) => f a) h
      simpa [hσa] using h
    exact hab h1.symm
  have hrange_ne : ψ.range ≠ ⊤ := by
    intro htop
    have hσmem : σ ∈ ψ.range := by
      rw [htop]
      exact Subgroup.mem_top σ
    obtain ⟨g, hg⟩ := hσmem
    have hgG : (g : MulAut W) ∈ semiStab zW O ⊓
        Subgroup.centralizer ({zW} : Set (MulAut W)) := g.2
    have hfix (i : Fin 6) (hi : i < 4) : ⇑(g : MulAut W) '' P i = P i := by
      have hxi : (⟨P i, hP_mem i⟩ : ↥(points zW O)) ≠ a := by
        intro h
        exact hP_ne (ne_of_lt hi) (congrArg Subtype.val h)
      have hxb : (⟨P i, hP_mem i⟩ : ↥(points zW O)) ≠ b := by
        intro h
        exact hP_ne (ne_of_lt (lt_trans hi (by decide : (4 : Fin 6) < 5)))
          (congrArg Subtype.val h)
      have hψi : ψ g (⟨P i, hP_mem i⟩ : ↥(points zW O)) = ⟨P i, hP_mem i⟩ := by
        rw [hg]
        exact hσx hxi hxb
      have h1 : ⇑((Subgroup.inclusion inf_le_left (g : ↥G) : ↥(semiStab zW O)) :
          MulAut W) '' P i = P i := by
        have h := congrArg (fun Q : ↥(points zW O) => (Q : Set W)) hψi
        simpa only [ψ, MonoidHom.comp_apply, coe_pointPerm_apply] using h
      simpa only [Subgroup.coe_inclusion] using h1
    have hg_comm : (g : MulAut W) * zW = zW * (g : MulAut W) := by
      have hcent : (g : MulAut W) ∈ Subgroup.centralizer ({zW} : Set (MulAut W)) :=
        (Subgroup.mem_inf.mp hgG).2
      exact ((Subgroup.mem_centralizer_iff.mp hcent) zW (Set.mem_singleton zW)).symm
    have hg_zp : (g : MulAut W) ∈ Subgroup.zpowers zW :=
      Setup.mem_zpowers_of_fix_frame S hb hg_comm hfix
    have hg_semi : (g : MulAut W) ∈ semiStab zW O := (Subgroup.mem_inf.mp hgG).1
    have hg_perm : pointPerm S.pow_three ⟨(g : MulAut W), hg_semi⟩ = 1 := by
      refine MonoidHom.mem_ker.1 (zpowers_le_ker_pointPerm S.pow_three ?_)
      rw [Subgroup.mem_subgroupOf]
      exact hg_zp
    have hψg : ψ g = 1 := by
      change pointPerm S.pow_three (Subgroup.inclusion inf_le_left (g : ↥G)) = 1
      exact hg_perm
    have hσ_one : σ = 1 := by rw [← hg, hψg]
    exact hσ_ne hσ_one
  have hperm_card : Nat.card (Equiv.Perm ↥(points zW O)) = 720 := by
    have h6 : Nat.card ↥(points zW O) = 6 := by simpa only [zW, O] using S.card_points
    rw [Nat.card_perm, h6]
    norm_num
  have hrange_lt : Nat.card ↥ψ.range < 720 := by
    have hle : Nat.card ↥ψ.range ≤ Nat.card (Equiv.Perm ↥(points zW O)) :=
      Subgroup.card_le_card_group (H := ψ.range)
    rcases lt_or_eq_of_le hle with h | h
    · rwa [hperm_card] at h
    · exact absurd (Subgroup.eq_top_of_card_eq (H := ψ.range) h) hrange_ne
  have hrange_le : Nat.card ↥ψ.range ≤ 360 := by
    have hdvd : Nat.card ↥ψ.range ∣ 720 := by
      have h := Subgroup.card_subgroup_dvd_card ψ.range
      rwa [hperm_card] at h
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      rw [Nat.two_le_iff]
      constructor
      · rintro rfl
        simp at hk
      · intro h1
        rw [h1, mul_one] at hk
        omega
    have h2 : Nat.card ↥ψ.range * 2 ≤ 720 := by
      rw [hk]
      exact Nat.mul_le_mul_left _ hk2
    omega
  have hcard := Subgroup.card_ker_mul_card_range ψ
  calc Nat.card ↥G = Nat.card ψ.ker * Nat.card ψ.range := hcard.symm
    _ ≤ 3 * 360 := Nat.mul_le_mul hker_card hrange_le
    _ = 1080 := by norm_num

end CFSG.Quasithin.HatA6

end
