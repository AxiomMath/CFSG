module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private def s16t3_F : Fin 7 → Fin 7 → Fin 7 :=
  ![![0, 3, 4, 1, 2, 6, 5], ![3, 1, 5, 0, 6, 2, 4], ![4, 5, 2, 6, 0, 1, 3],
    ![1, 0, 6, 3, 5, 4, 2], ![2, 6, 0, 5, 4, 3, 1], ![6, 2, 1, 4, 3, 5, 0],
    ![5, 4, 3, 2, 1, 0, 6]]

private def s16t3_vec : Fin 7 → (Fin 3 → ZMod 2) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

private def s16t3_vecSub : Fin 7 → {v : Fin 3 → ZMod 2 // v ≠ 0} :=
  fun i => ⟨s16t3_vec i, by fin_cases i <;> decide⟩

private theorem s16t3_third_inj {S : Type} (third : S → S → S)
    (h3 : ∀ x y, x ≠ y → third x (third x y) = y)
    {a p q : S} (hp : p ≠ a) (hq : q ≠ a) (hpq : third a p = third a q) : p = q := by
  rw [← h3 a p hp.symm, hpq, h3 a q hq.symm]

private theorem s16t3_third_eq_of_cover {S : Type} [Fintype S] [DecidableEq S]
    (third : S → S → S) (h1 : ∀ x y, x ≠ y → third x y ≠ x ∧ third x y ≠ y)
    (h3 : ∀ x y, x ≠ y → third x (third x y) = y)
    {a b b' c c' x y : S}
    (hcover : (Finset.univ : Finset S) = {a, b, b', c, c', x, y})
    (hb : third a b' = b) (hc : third a c' = c)
    (hb'a : b' ≠ a) (hc'a : c' ≠ a) (hxa : x ≠ a)
    (hxb : x ≠ b) (hxb' : x ≠ b') (hxc : x ≠ c) (hxc' : x ≠ c')
    (hxy : x ≠ y) : third a x = y := by
  have hba : b ≠ a := by
    have := (h1 a b' hb'a.symm).1
    rwa [hb] at this
  have hca : c ≠ a := by
    have := (h1 a c' hc'a.symm).1
    rwa [hc] at this
  have hb'' : third a b = b' := by
    have := h3 a b' hb'a.symm
    rwa [hb] at this
  have hc'' : third a c = c' := by
    have := h3 a c' hc'a.symm
    rwa [hc] at this
  have hxa' : third a x ≠ a := (h1 a x hxa.symm).1
  have hxx' : third a x ≠ x := (h1 a x hxa.symm).2
  have hmem : third a x ∈ ({a, b, b', c, c', x, y} : Finset S) := by
    rw [← hcover]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h
  · exact absurd h hxa'
  · exact absurd (s16t3_third_inj third h3 hb'a hxa (hb.trans h.symm)).symm hxb'
  · exact absurd (s16t3_third_inj third h3 hba hxa (hb''.trans h.symm)).symm hxb
  · exact absurd (s16t3_third_inj third h3 hc'a hxa (hc.trans h.symm)).symm hxc'
  · exact absurd (s16t3_third_inj third h3 hca hxa (hc''.trans h.symm)).symm hxc
  · exact absurd h hxx'
  · exact h

theorem s16t3_sts7_coordinates {S : Type} [Fintype S] [DecidableEq S] (hS : Fintype.card S = 7)
    (third : S → S → S) (h1 : ∀ x y, x ≠ y → third x y ≠ x ∧ third x y ≠ y)
    (h2 : ∀ x y, third x y = third y x) (h3 : ∀ x y, x ≠ y → third x (third x y) = y) :
    ∃ e : S ≃ {v : Fin 3 → ZMod 2 // v ≠ 0},
      ∀ x y, x ≠ y → ((e (third x y) : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) =
        (e x : Fin 3 → ZMod 2) + (e y : Fin 3 → ZMod 2) := by
  classical
  have hinj : ∀ a p q : S, p ≠ a → q ≠ a → third a p = third a q → p = q :=
    fun a p q hp hq hpq => s16t3_third_inj third h3 hp hq hpq
  have h2lt : 1 < Fintype.card S := by rw [hS]; norm_num
  obtain ⟨x0, x1, hx01⟩ := Fintype.exists_pair_of_one_lt_card h2lt
  let z01 : S := third x0 x1
  have hz01x0 : z01 ≠ x0 := (h1 x0 x1 hx01).1
  have hz01x1 : z01 ≠ x1 := (h1 x0 x1 hx01).2
  have hcard3 : ({x0, x1, z01} : Finset S).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨x0, x1, z01, hx01, hz01x0.symm, hz01x1.symm, rfl⟩
  have hne3 : ({x0, x1, z01} : Finset S) ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, hS] at hcard3
    norm_num at hcard3
  have hprop3 : ({x0, x1, z01} : Finset S) ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne3⟩
  obtain ⟨x2, -, hx2T3⟩ := Finset.exists_of_ssubset hprop3
  have hx2x0 : x2 ≠ x0 := fun h => hx2T3 (by simp [h])
  have hx2x1 : x2 ≠ x1 := fun h => hx2T3 (by simp [h])
  have hx2z01 : x2 ≠ z01 := fun h => hx2T3 (by simp [h])
  have hx02 : x0 ≠ x2 := hx2x0.symm
  have hx12 : x1 ≠ x2 := hx2x1.symm
  let z02 : S := third x0 x2
  let z12 : S := third x1 x2
  have hz02x0 : z02 ≠ x0 := (h1 x0 x2 hx02).1
  have hz02x2 : z02 ≠ x2 := (h1 x0 x2 hx02).2
  have hz12x1 : z12 ≠ x1 := (h1 x1 x2 hx12).1
  have hz12x2 : z12 ≠ x2 := (h1 x1 x2 hx12).2
  have d_x0x1 : x0 ≠ x1 := hx01
  have d_x0x2 : x0 ≠ x2 := hx02
  have d_x0z01 : x0 ≠ z01 := hz01x0.symm
  have d_x0z02 : x0 ≠ z02 := hz02x0.symm
  have d_x1x2 : x1 ≠ x2 := hx12
  have d_x1z01 : x1 ≠ z01 := hz01x1.symm
  have d_x2z01 : x2 ≠ z01 := hx2z01
  have d_x2z02 : x2 ≠ z02 := hz02x2.symm
  have d_x2z12 : x2 ≠ z12 := hz12x2.symm
  have h3x0x1 : third x0 z01 = x1 := h3 x0 x1 hx01
  have h3x0x2 : third x0 z02 = x2 := h3 x0 x2 hx02
  have h3x1x2 : third x1 z12 = x2 := h3 x1 x2 hx12
  have hz02x1 : z02 ≠ x1 := by
    intro h
    have heq : third x0 x2 = third x0 z01 := h.trans h3x0x1.symm
    exact d_x2z01 (hinj x0 x2 z01 hx02.symm hz01x0 heq)
  have d_x1z02 : x1 ≠ z02 := hz02x1.symm
  have hz01z02 : z01 ≠ z02 := by
    intro h
    exact hx12 (hinj x0 x2 x1 hx02.symm hx01.symm h.symm).symm
  have hz01z12 : z01 ≠ z12 := by
    intro h
    have heq : third x1 x0 = third x1 x2 := (h2 x0 x1).symm.trans h
    exact hx02 (hinj x1 x0 x2 hx01 hx12.symm heq)
  have d_x1z12 : x1 ≠ z12 := hz12x1.symm
  have hz02z12 : z02 ≠ z12 := by
    intro h
    have heq : third x2 x0 = third x2 x1 :=
      ((h2 x0 x2).symm).trans (h.trans ((h2 x1 x2).symm).symm)
    exact hx01 (hinj x2 x0 x1 hx02 hx12 heq)
  have d_x0z12 : x0 ≠ z12 := by
    intro h
    have h3x1z01 : third x1 z01 = x0 := by
      have := h3 x1 x0 hx01.symm
      rwa [← h2 x0 x1] at this
    have heq : third x1 x2 = third x1 z01 := by
      change z12 = third x1 z01
      rw [h.symm, h3x1z01]
    exact d_x2z01 (hinj x1 x2 z01 hx12.symm hz01x1 heq)
  have h3x1x0 : third x1 z01 = x0 := by
    have := h3 x1 x0 hx01.symm
    rwa [← h2 x0 x1] at this
  have h3x2x0 : third x2 z02 = x0 := by
    have := h3 x2 x0 hx02.symm
    rwa [← h2 x0 x2] at this
  have h3x2x1 : third x2 z12 = x1 := by
    have := h3 x2 x1 hx12.symm
    rwa [← h2 x1 x2] at this
  let T6 : Finset S := {x0, x1, x2, z01, z02, z12}
  have hT6card : T6.card = 6 := by
    simp [T6, d_x0x1, d_x0x2, d_x0z01, d_x0z02, d_x0z12, d_x1x2, d_x1z01, d_x1z02,
      d_x1z12, d_x2z01, d_x2z02, d_x2z12, hz01z02, hz01z12, hz02z12]
  have hT6ne : T6 ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, hS] at hT6card
    norm_num at hT6card
  have hprop6 : T6 ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T6, hT6ne⟩
  obtain ⟨y0, -, hy0T6⟩ := Finset.exists_of_ssubset hprop6
  have hy0x0 : y0 ≠ x0 := fun h => hy0T6 (by simp [T6, h])
  have hy0x1 : y0 ≠ x1 := fun h => hy0T6 (by simp [T6, h])
  have hy0x2 : y0 ≠ x2 := fun h => hy0T6 (by simp [T6, h])
  have hy0z01 : y0 ≠ z01 := fun h => hy0T6 (by simp [T6, h])
  have hy0z02 : y0 ≠ z02 := fun h => hy0T6 (by simp [T6, h])
  have hy0z12 : y0 ≠ z12 := fun h => hy0T6 (by simp [T6, h])
  have h7card : ({x0, x1, x2, z01, z02, z12, y0} : Finset S).card = 7 := by
    simp [d_x0x1, d_x0x2, d_x0z01, d_x0z02, d_x0z12, hy0x0.symm,
      d_x1x2, d_x1z01, d_x1z02, d_x1z12, hy0x1.symm,
      d_x2z01, d_x2z02, d_x2z12, hy0x2.symm,
      hz01z02, hz01z12, hy0z01.symm, hz02z12, hy0z02.symm, hy0z12.symm]
  have hcover7 : (Finset.univ : Finset S) = ({x0, x1, x2, z01, z02, z12, y0} : Finset S) :=
    (Finset.eq_univ_of_card ({x0, x1, x2, z01, z02, z12, y0} : Finset S)
      (by rw [h7card, hS])).symm
  have hcov1 : (Finset.univ : Finset S) = ({x0, x1, z01, x2, z02, z12, y0} : Finset S) := by
    rw [hcover7]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  have hcov2 : (Finset.univ : Finset S) = ({x1, x0, z01, x2, z12, z02, y0} : Finset S) := by
    rw [hcover7]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  have hcov3 : (Finset.univ : Finset S) = ({x2, x0, z02, x1, z12, z01, y0} : Finset S) := by
    rw [hcover7]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  have hcov4 : (Finset.univ : Finset S) = ({z12, x0, y0, x1, x2, z01, z02} : Finset S) := by
    rw [hcover7]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  have hcov5 : (Finset.univ : Finset S) = ({z02, x0, x2, x1, y0, z12, z01} : Finset S) := by
    rw [hcover7]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  have D1 : third x0 z12 = y0 :=
    s16t3_third_eq_of_cover third h1 h3 hcov1 h3x0x1 h3x0x2
      d_x0z01.symm d_x0z02.symm d_x0z12.symm d_x1z12.symm hz01z12.symm
      d_x2z12.symm hz02z12.symm hy0z12.symm
  have D2 : third x1 z02 = y0 :=
    s16t3_third_eq_of_cover third h1 h3 hcov2 h3x1x0 h3x1x2
      d_x1z01.symm d_x1z12.symm d_x1z02.symm d_x0z02.symm hz01z02.symm
      d_x2z02.symm hz02z12 hy0z02.symm
  have D3 : third x2 z01 = y0 :=
    s16t3_third_eq_of_cover third h1 h3 hcov3 h3x2x0 h3x2x1
      d_x2z02.symm d_x2z12.symm d_x2z01.symm d_x0z01.symm hz01z02
      d_x1z01.symm hz01z12 hy0z01.symm
  have hz12y0 : third z12 y0 = x0 := by
    have h1z12x0 : third z12 x0 = y0 := (h2 x0 z12).symm.trans D1
    have := h3 z12 x0 d_x0z12.symm
    rwa [h1z12x0] at this
  have hz12x2 : third z12 x2 = x1 := (h2 z12 x2).trans h3x2x1
  have D4 : third z12 z01 = z02 :=
    s16t3_third_eq_of_cover third h1 h3 hcov4 hz12y0 hz12x2
      hy0z12 d_x2z12 hz01z12 d_x0z01.symm hy0z01.symm
      d_x1z01.symm d_x2z01.symm hz01z02
  have hz02x2 : third z02 x2 = x0 := (h2 z02 x2).trans h3x2x0
  have hz02y0 : third z02 y0 = x1 := by
    have hz02x1 : third z02 x1 = y0 := (h2 x1 z02).symm.trans D2
    have := h3 z02 x1 d_x1z02.symm
    rwa [hz02x1] at this
  have D5 : third z02 z12 = z01 :=
    s16t3_third_eq_of_cover third h1 h3 hcov5 hz02x2 hz02y0
      d_x2z02 hy0z02 hz02z12.symm d_x0z12.symm d_x2z12.symm
      d_x1z12.symm hy0z12.symm hz01z12.symm
  have th01 : third x0 x1 = z01 := rfl
  have th02 : third x0 x2 = z02 := rfl
  have th03 : third x0 z01 = x1 := h3x0x1
  have th04 : third x0 z02 = x2 := h3x0x2
  have th05 : third x0 z12 = y0 := D1
  have th06 : third x0 y0 = z12 := by
    have := h3 x0 z12 d_x0z12
    rwa [D1] at this
  have th12 : third x1 x2 = z12 := rfl
  have th13 : third x1 z01 = x0 := h3x1x0
  have th14 : third x1 z02 = y0 := D2
  have th15 : third x1 z12 = x2 := h3x1x2
  have th16 : third x1 y0 = z02 := by
    have := h3 x1 z02 d_x1z02
    rwa [D2] at this
  have th23 : third x2 z01 = y0 := D3
  have th24 : third x2 z02 = x0 := h3x2x0
  have th25 : third x2 z12 = x1 := h3x2x1
  have th26 : third x2 y0 = z01 := by
    have := h3 x2 z01 d_x2z01
    rwa [D3] at this
  have th35 : third z01 z12 = z02 := (h2 z12 z01).symm.trans D4
  have th34 : third z01 z02 = z12 := by
    have := h3 z01 z12 hz01z12
    rwa [th35] at this
  have th36 : third z01 y0 = x2 := by
    have hz01x2 : third z01 x2 = y0 := (h2 x2 z01).symm.trans D3
    have := h3 z01 x2 d_x2z01.symm
    rwa [hz01x2] at this
  have th45 : third z02 z12 = z01 := D5
  have th46 : third z02 y0 = x1 := by
    have hz02x1 : third z02 x1 = y0 := (h2 x1 z02).symm.trans D2
    have := h3 z02 x1 d_x1z02.symm
    rwa [hz02x1] at this
  have th56 : third z12 y0 = x0 := hz12y0
  have th10 : third x1 x0 = z01 := (h2 x0 x1).symm.trans th01
  have th20 : third x2 x0 = z02 := (h2 x0 x2).symm.trans th02
  have th30 : third z01 x0 = x1 := (h2 x0 z01).symm.trans th03
  have th40 : third z02 x0 = x2 := (h2 x0 z02).symm.trans th04
  have th50 : third z12 x0 = y0 := (h2 x0 z12).symm.trans th05
  have th60 : third y0 x0 = z12 := (h2 x0 y0).symm.trans th06
  have th21 : third x2 x1 = z12 := (h2 x1 x2).symm.trans th12
  have th31 : third z01 x1 = x0 := (h2 x1 z01).symm.trans th13
  have th41 : third z02 x1 = y0 := (h2 x1 z02).symm.trans th14
  have th51 : third z12 x1 = x2 := (h2 x1 z12).symm.trans th15
  have th61 : third y0 x1 = z02 := (h2 x1 y0).symm.trans th16
  have th32 : third z01 x2 = y0 := (h2 x2 z01).symm.trans th23
  have th42 : third z02 x2 = x0 := (h2 x2 z02).symm.trans th24
  have th52 : third z12 x2 = x1 := (h2 x2 z12).symm.trans th25
  have th62 : third y0 x2 = z01 := (h2 x2 y0).symm.trans th26
  have th43 : third z02 z01 = z12 := (h2 z01 z02).symm.trans th34
  have th53 : third z12 z01 = z02 := (h2 z01 z12).symm.trans th35
  have th63 : third y0 z01 = x2 := (h2 z01 y0).symm.trans th36
  have th54 : third z12 z02 = z01 := (h2 z02 z12).symm.trans th45
  have th64 : third y0 z02 = x1 := (h2 z02 y0).symm.trans th46
  have th65 : third y0 z12 = x0 := (h2 z12 y0).symm.trans th56
  clear h1 h2 h3
  let pts : Fin 7 → S := ![x0, x1, x2, z01, z02, z12, y0]
  have hF : ∀ i j : Fin 7, i ≠ j → third (pts i) (pts j) = pts (s16t3_F i j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [pts, s16t3_F] <;>
      first
        | exact absurd rfl hij
        | exact hij.elim
        | assumption
  clear th01 th02 th03 th04 th05 th06 th12 th13 th14 th15 th16 th23 th24 th25 th26
    th35 th34 th36 th45 th46 th56 th10 th20 th30 th40 th50 th60 th21 th31 th41 th51
    th61 th32 th42 th52 th62 th43 th53 th63 th54 th64 th65
  have hpts_inj : Function.Injective pts := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [pts] at hij ⊢ <;>
      first
        | rfl
        | exact absurd hij d_x0x1
        | exact absurd hij.symm d_x0x1
        | exact absurd hij d_x0x2
        | exact absurd hij.symm d_x0x2
        | exact absurd hij d_x0z01
        | exact absurd hij.symm d_x0z01
        | exact absurd hij d_x0z02
        | exact absurd hij.symm d_x0z02
        | exact absurd hij d_x0z12
        | exact absurd hij.symm d_x0z12
        | exact absurd hij hy0x0.symm
        | exact absurd hij.symm hy0x0.symm
        | exact absurd hij d_x1x2
        | exact absurd hij.symm d_x1x2
        | exact absurd hij d_x1z01
        | exact absurd hij.symm d_x1z01
        | exact absurd hij d_x1z02
        | exact absurd hij.symm d_x1z02
        | exact absurd hij d_x1z12
        | exact absurd hij.symm d_x1z12
        | exact absurd hij hy0x1.symm
        | exact absurd hij.symm hy0x1.symm
        | exact absurd hij d_x2z01
        | exact absurd hij.symm d_x2z01
        | exact absurd hij d_x2z02
        | exact absurd hij.symm d_x2z02
        | exact absurd hij d_x2z12
        | exact absurd hij.symm d_x2z12
        | exact absurd hij hy0x2.symm
        | exact absurd hij.symm hy0x2.symm
        | exact absurd hij hz01z02
        | exact absurd hij.symm hz01z02
        | exact absurd hij hz01z12
        | exact absurd hij.symm hz01z12
        | exact absurd hij hy0z01.symm
        | exact absurd hij.symm hy0z01.symm
        | exact absurd hij hz02z12
        | exact absurd hij.symm hz02z12
        | exact absurd hij hy0z02.symm
        | exact absurd hij.symm hy0z02.symm
        | exact absurd hij hy0z12.symm
        | exact absurd hij.symm hy0z12.symm
  have hpts_bij : Function.Bijective pts := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hpts_inj, by simp [hS]⟩
  have hvec_inj : Function.Injective s16t3_vecSub := by
    intro i j hij
    exact (by decide : ∀ i j : Fin 7, s16t3_vec i = s16t3_vec j → i = j) i j
      (congrArg Subtype.val hij)
  have hvec_bij : Function.Bijective s16t3_vecSub := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hvec_inj, by decide⟩
  let ptsEquiv : Fin 7 ≃ S := Equiv.ofBijective pts hpts_bij
  let vecEquiv : Fin 7 ≃ {v : Fin 3 → ZMod 2 // v ≠ 0} :=
    Equiv.ofBijective s16t3_vecSub hvec_bij
  let e : S ≃ {v : Fin 3 → ZMod 2 // v ≠ 0} := ptsEquiv.symm.trans vecEquiv
  have e_pts : ∀ i : Fin 7,
      ((e (pts i) : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) = s16t3_vec i := by
    intro i
    have h : e (pts i) = vecEquiv i := by simp [e, ptsEquiv, vecEquiv]
    rw [h]
    rfl
  have hvec : ∀ i j : Fin 7, i ≠ j →
      s16t3_vec (s16t3_F i j) = s16t3_vec i + s16t3_vec j := by decide
  refine ⟨e, ?_⟩
  intro x y hxy
  obtain ⟨i, rfl⟩ := ptsEquiv.surjective x
  obtain ⟨j, rfl⟩ := ptsEquiv.surjective y
  have hij : i ≠ j := by
    intro h
    exact hxy (by rw [h])
  calc
    ((e (third (pts i) (pts j)) : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2)
        = ((e (pts (s16t3_F i j)) : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) := by
          rw [hF i j hij]
    _ = s16t3_vec (s16t3_F i j) := e_pts _
    _ = s16t3_vec i + s16t3_vec j := hvec i j hij
    _ = ((e (pts i) : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2)
          + ((e (pts j) : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) := by
          rw [e_pts, e_pts]

theorem s16t3_gl3_of_perm (π : {v : Fin 3 → ZMod 2 // v ≠ 0} ≃ {v : Fin 3 → ZMod 2 // v ≠ 0})
    (hπ : ∀ x y : {v : Fin 3 → ZMod 2 // v ≠ 0}, x ≠ y →
      ∀ hxy : (x : Fin 3 → ZMod 2) + (y : Fin 3 → ZMod 2) ≠ 0,
        ((π ⟨(x : Fin 3 → ZMod 2) + (y : Fin 3 → ZMod 2), hxy⟩ : {v : Fin 3 → ZMod 2 // v ≠ 0}) :
            Fin 3 → ZMod 2) = (π x : Fin 3 → ZMod 2) + (π y : Fin 3 → ZMod 2)) :
    ∃ M : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2),
      ∀ x : {v : Fin 3 → ZMod 2 // v ≠ 0},
        ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (x : Fin 3 → ZMod 2)) =
          (π x : Fin 3 → ZMod 2) := by
  let f : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) :=
    fun v => if h : v = 0 then 0 else (π ⟨v, h⟩ : Fin 3 → ZMod 2)
  have hf0 : f 0 = 0 := by simp [f]
  have hf : ∀ v (h : v ≠ 0), f v = (π ⟨v, h⟩ : Fin 3 → ZMod 2) := fun v h => dif_neg h
  have haddself : ∀ v : Fin 3 → ZMod 2, v + v = 0 := by
    intro v
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  have hadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    by_cases hx : x = 0
    · subst hx; simp [hf0]
    by_cases hy : y = 0
    · subst hy; simp [hf0]
    by_cases hxy : x = y
    · subst hxy
      rw [haddself x, hf0, hf x hx]
      exact (haddself (π ⟨x, hx⟩ : Fin 3 → ZMod 2)).symm
    · have hne : x + y ≠ 0 := by
        intro h0
        have hyx : y = x := by
          calc y = 0 + y := (zero_add y).symm
            _ = (x + x) + y := by rw [haddself x]
            _ = x + (x + y) := by rw [add_assoc]
            _ = x + 0 := by rw [h0]
            _ = x := add_zero x
        exact hxy hyx.symm
      rw [hf (x + y) hne, hf x hx, hf y hy]
      exact hπ ⟨x, hx⟩ ⟨y, hy⟩ (fun h => hxy (congrArg Subtype.val h)) hne
  let fHom : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    { toFun := f, map_zero' := hf0, map_add' := hadd }
  have hfHom : ∀ v, fHom v = f v := fun v => rfl
  let lin : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) := fHom.toZModLinearMap 2
  have hlin : ∀ v, lin v = f v := fun v => rfl
  have hlin_inj : Function.Injective lin := by
    intro x y hxy
    rw [hlin, hlin] at hxy
    by_cases hx : x = 0
    · subst hx
      rw [hf0] at hxy
      by_cases hy : y = 0
      · exact hy.symm
      · rw [hf y hy] at hxy
        exact absurd hxy.symm (π ⟨y, hy⟩).2
    · by_cases hy : y = 0
      · subst hy
        rw [hf0] at hxy
        rw [hf x hx] at hxy
        exact absurd hxy (π ⟨x, hx⟩).2
      · have h1 : (π ⟨x, hx⟩ : Fin 3 → ZMod 2) = π ⟨y, hy⟩ := by
          rw [hf x hx, hf y hy] at hxy
          exact hxy
        exact congrArg Subtype.val (π.injective (Subtype.ext h1))
  have hlin_bij : Function.Bijective lin :=
    ⟨hlin_inj, Finite.surjective_of_injective hlin_inj⟩
  have hunit : IsUnit lin := (Module.End.isUnit_iff lin).mpr hlin_bij
  let A : Matrix (Fin 3) (Fin 3) (ZMod 2) := LinearMap.toMatrix' lin
  have hAunit : IsUnit A := LinearMap.isUnit_toMatrix'_iff.mpr hunit
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  let M : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    Matrix.GeneralLinearGroup.mk'' A hAdet
  refine ⟨M, fun x => ?_⟩
  calc
    (M : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (x : Fin 3 → ZMod 2)
        = A.mulVec (x : Fin 3 → ZMod 2) := rfl
    _ = lin (x : Fin 3 → ZMod 2) := LinearMap.toMatrix'_mulVec lin (x : Fin 3 → ZMod 2)
    _ = f (x : Fin 3 → ZMod 2) := hlin (x : Fin 3 → ZMod 2)
    _ = (π x : Fin 3 → ZMod 2) := hf x x.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
