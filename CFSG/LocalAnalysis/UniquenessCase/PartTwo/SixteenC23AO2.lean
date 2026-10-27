module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AO2A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AStep

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem c23a_false_of_inCalO2 {M V W W' V₀ : Subgroup G} {n : ℕ} {g : G} (hn : n ≤ 2)
    (hP : C23APair M V W W')
    (hP' : C23APair (conjSubgroup M g) (conjSubgroup V g) (conjSubgroup W g)
      (conjSubgroup W' g))
    (h : InCalO2 n M V₀ V g) : False := by
  unfold InCalO2 InCalO OFirst ODual TwoFirst TwoDual at h
  obtain ⟨⟨⟨hVgM, hmUg, _⟩, ⟨hVMg, hmB, _⟩⟩, ⟨I, hI, hIb⟩, ⟨I', hI', hI'a⟩, _⟩ := h
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let C' : Subgroup G := U ⊓ centralizer (conjSubgroup V g : Set G)
  have hmU : E3.mQuot V U ≤ n := by
    have hm : E3.mQuot V U = E3.mQuot V (conjSubgroup M g) :=
      c23a_o2_mQuot_inf_left V (conjSubgroup M g)
    rw [hm]; exact hmUg
  have hmI : E3.mQuot V I ≤ n := by
    have hIV : I ≤ V := hI.1.trans inf_le_left
    have hm : E3.mQuot V I = n := by
      have h' := mQuot_eq_of_mem_gammaSet (V := V) (A := I) (M := V ⊓ conjSubgroup M g)
        (i := n) hI (g := 1) (by rw [conjSubgroup_one]; exact hIV)
      simpa [conjSubgroup_one] using h'
    exact hm.le
  obtain ⟨b, hb_mem, hb_notC⟩ := SetLike.not_le_iff_exists.1 hIb
  obtain ⟨⟨hbVg, hbM⟩, hbCI⟩ := Subgroup.mem_inf.1 hb_mem
  have hb2 : b ^ 2 = 1 := hP'.elem.2 b hbVg
  have hbV : ¬ V ≤ centralizer ({b} : Set G) := c23a_o2_not_le_centralizer_singleton hb_notC
  have hIb' : ∀ i ∈ I, b * i = i * b :=
    fun i hi => (Subgroup.mem_centralizer_iff.1 hbCI i hi).symm
  have hcomm : ∀ u ∈ U, u * b * u⁻¹ * b⁻¹ ∈ V ⊓ conjSubgroup V g :=
    fun u hu => c23a_o2_comm_mem_inf hP hP' hu (Subgroup.mem_inf.2 ⟨hbVg, hbM⟩)
  have hD : (V ⊓ conjSubgroup V g) ⊓ W = ⊥ ∧
      (V ⊓ conjSubgroup V g) ⊓ W' = ⊥ :=
    c23a_inf_blocks_eq_bot hP hVgM (X := V ⊓ conjSubgroup V g)
      (fun x hx a ha => hP'.elem.comm ha hx.2)
  obtain ⟨X, Y, hXY, hYcomm, -, -, -, hYU⟩ :=
    c23a_step12 (M := M) (V := V) (W := W) (W' := W') (U := U)
      (D₀ := V ⊓ conjSubgroup V g) (I := I) (b := b) hn hP inf_le_left hI.1
      hbM hb2 hbV hIb' hmI hmU hcomm hD
  obtain ⟨a, ha_mem, ha_notC⟩ := SetLike.not_le_iff_exists.1 hI'a
  obtain ⟨haU, haCI'⟩ := Subgroup.mem_inf.1 ha_mem
  have haV : a ∈ V := (Subgroup.mem_inf.1 haU).1
  have haM : a ∈ conjSubgroup M g := (Subgroup.mem_inf.1 haU).2
  have ha2 : a ^ 2 = 1 := hP.elem.2 a haV
  have haVg : ¬ conjSubgroup V g ≤ centralizer ({a} : Set G) :=
    c23a_o2_not_le_centralizer_singleton ha_notC
  have hI'a_comm : ∀ i ∈ I', a * i = i * a :=
    fun i hi => (Subgroup.mem_centralizer_iff.1 haCI' i hi).symm
  have hmI' : E3.mQuot (conjSubgroup V g) I' ≤ n := by
    have hI'Vg : I' ≤ conjSubgroup V g := hI'.1.trans inf_le_left
    have hm : E3.mQuot (conjSubgroup V g) I' = n := by
      have h' := mQuot_eq_of_mem_gammaSet (V := conjSubgroup V g) (A := I')
        (M := conjSubgroup V g ⊓ M) (i := n) hI' (g := 1)
        (by rw [conjSubgroup_one]; exact hI'Vg)
      simpa [conjSubgroup_one] using h'
    exact hm.le
  have hmB' : E3.mQuot (conjSubgroup V g) B ≤ n := by
    have hm : E3.mQuot (conjSubgroup V g) B = E3.mQuot (conjSubgroup V g) M :=
      c23a_o2_mQuot_inf_left (conjSubgroup V g) M
    rw [hm]; exact hmB
  have hcomm' : ∀ u ∈ B, u * a * u⁻¹ * a⁻¹ ∈ conjSubgroup V g ⊓ V := by
    intro u hu
    have h := c23a_o2_comm_mem_inf hP hP' haU hu
    have hinv : (a * u * a⁻¹ * u⁻¹)⁻¹ ∈ V ⊓ conjSubgroup V g :=
      (V ⊓ conjSubgroup V g).inv_mem h
    have heq : u * a * u⁻¹ * a⁻¹ = (a * u * a⁻¹ * u⁻¹)⁻¹ := by group
    rw [heq, inf_comm]
    exact hinv
  have hD' : (conjSubgroup V g ⊓ V) ⊓ conjSubgroup W g = ⊥ ∧
      (conjSubgroup V g ⊓ V) ⊓ conjSubgroup W' g = ⊥ :=
    c23a_inf_blocks_eq_bot hP' hVMg (X := conjSubgroup V g ⊓ V)
      (fun x hx a' ha' => hP.elem.comm ha' hx.2)
  obtain ⟨X', Y', hX'Y', hY'a, -, -, -, hY'B⟩ :=
    c23a_step12 (M := conjSubgroup M g) (V := conjSubgroup V g)
      (W := conjSubgroup W g) (W' := conjSubgroup W' g) (U := B)
      (D₀ := conjSubgroup V g ⊓ V) (I := I') (b := a) hn hP' inf_le_left hI'.1
      haM ha2 haVg hI'a_comm hmI' hmB' hcomm' hD'
  have hstep3 : ∀ u ∈ U,
      u ∈ normalizer (conjSubgroup W g : Set G) ∧
      u ∈ normalizer (conjSubgroup W' g : Set G) ∧
      (∀ y ∈ Y', u * y = y * u) := by
    intro u hu
    have huMg : u ∈ conjSubgroup M g := (Subgroup.mem_inf.1 hu).2
    rcases hP'.perm u huMg with hfix | hswap
    · refine ⟨(conjSubgroup_eq_iff_mem_normalizer).1 hfix.1,
        (conjSubgroup_eq_iff_mem_normalizer).1 hfix.2, ?_⟩
      have hYfix : conjSubgroup Y' u = Y' := by
        rcases hX'Y' with ⟨hX, hY⟩ | ⟨hX, hY⟩
        · rw [hY]; exact hfix.2
        · rw [hY]; exact hfix.1
      intro y hy
      have hmemD : u * y * u⁻¹ * y⁻¹ ∈ V ⊓ conjSubgroup V g :=
        c23a_o2_comm_mem_inf hP hP' hu (hY'B hy)
      have hmemY : u * y * u⁻¹ * y⁻¹ ∈ Y' := by
        have h1 : u * y * u⁻¹ ∈ Y' :=
          mem_conjSubgroup_iff.1 (by rw [hYfix]; exact hy)
        exact Y'.mul_mem h1 (Y'.inv_mem hy)
      have hDY : (V ⊓ conjSubgroup V g) ⊓ Y' = ⊥ := by
        have hinn : V ⊓ conjSubgroup V g = conjSubgroup V g ⊓ V := inf_comm V (conjSubgroup V g)
        rcases hX'Y' with ⟨-, hY⟩ | ⟨-, hY⟩
        · rw [hY, hinn]; exact hD'.2
        · rw [hY, hinn]; exact hD'.1
      have hmem : u * y * u⁻¹ * y⁻¹ ∈ (V ⊓ conjSubgroup V g) ⊓ Y' :=
        Subgroup.mem_inf.2 ⟨hmemD, hmemY⟩
      rw [hDY, Subgroup.mem_bot] at hmem
      have h1 : u * y * u⁻¹ = y := by
        have h2 : (u * y * u⁻¹ * y⁻¹) * y = 1 * y := by rw [hmem]
        simpa [mul_assoc] using h2
      have h3 : (u * y * u⁻¹) * u = y * u := by rw [h1]
      simpa [mul_assoc] using h3
    · exfalso
      have huax : u * a * u⁻¹ = a := by
        have h := hP.elem.comm (Subgroup.mem_inf.1 hu).1 haV
        rw [h]; group
      exact ha_notC (c23a_o2_mem_centralizer_of_swap (V := conjSubgroup V g)
        (W := conjSubgroup W g) (W' := conjSubgroup W' g) (X' := X') (Y' := Y')
        (a := a) (u := u) (fun x hx y hy => hP'.elem.comm hx hy) hP'.sup huax hX'Y'
          hswap hY'a)
  have hUelem : IsElemAbelian 2 U := hP.elem.mono inf_le_left
  have hnormW : ∀ e ∈ U, e ∈ normalizer (conjSubgroup W g : Set G) :=
    fun e he => (hstep3 e he).1
  have hnormW' : ∀ e ∈ U, e ∈ normalizer (conjSubgroup W' g : Set G) :=
    fun e he => (hstep3 e he).2.1
  have hcentY' : ∀ e ∈ U, ∀ y ∈ Y', e * y = y * e :=
    fun e he => (hstep3 e he).2.2
  have hle2 : E3.mQuot U (centralizer (conjSubgroup V g : Set G)) ≤ 2 := by
    rcases hX'Y' with ⟨hX, hY⟩ | ⟨hX, hY⟩
    · have hc : ∀ e ∈ U, ∀ y ∈ conjSubgroup W' g, e * y = y * e :=
        fun e he y hy => hcentY' e he y (hY.symm ▸ hy)
      exact hP'.rankLe U inf_le_right hUelem hnormW hc
    · have hc : ∀ e ∈ U, ∀ y ∈ conjSubgroup W g, e * y = y * e :=
        fun e he y hy => hcentY' e he y (hY.symm ▸ hy)
      exact hP'.rankLe' U inf_le_right hUelem hnormW' hc
  have hYeq : Y = W ∨ Y = W' := by
    rcases hXY with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hrkY : 3 ≤ rk ↥Y := by
    rcases hYeq with h | h
    · rw [h]; simpa only [mSub] using hP.three
    · rw [h]; simpa only [mSub] using hP.three'
  have hC'leV : C' ≤ V := (inf_le_left : C' ≤ U).trans (inf_le_left : U ≤ V)
  have hC'leC : C' ≤ centralizer (conjSubgroup V g : Set G) := inf_le_right
  have hXbot : (V ⊓ centralizer (conjSubgroup V g : Set G)) ⊓ W = ⊥ ∧
      (V ⊓ centralizer (conjSubgroup V g : Set G)) ⊓ W' = ⊥ :=
    c23a_inf_blocks_eq_bot hP hVgM (X := V ⊓ centralizer (conjSubgroup V g : Set G))
      (fun x hx a ha => Subgroup.mem_centralizer_iff.1 hx.2 a ha)
  have hYinfC' : Y ⊓ C' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzY, hzC⟩ := Subgroup.mem_inf.1 hz
    have hzX : z ∈ V ⊓ centralizer (conjSubgroup V g : Set G) :=
      Subgroup.mem_inf.2 ⟨hC'leV hzC, hC'leC hzC⟩
    have hXYbot : (V ⊓ centralizer (conjSubgroup V g : Set G)) ⊓ Y = ⊥ := by
      rcases hYeq with h | h
      · rw [h]; exact hXbot.1
      · rw [h]; exact hXbot.2
    have hzYX : z ∈ (V ⊓ centralizer (conjSubgroup V g : Set G)) ⊓ Y :=
      Subgroup.mem_inf.2 ⟨hzX, hzY⟩
    rw [hXYbot] at hzYX
    exact Subgroup.mem_bot.1 hzYX
  have hcommYC' : ∀ y ∈ Y, ∀ c ∈ C', y * c = c * y := by
    intro y hy c hc
    exact hP.elem.comm (Subgroup.mem_inf.1 (hYU hy)).1 (hC'leV hc)
  have hrksup : rk ↥(Y ⊔ C') = rk ↥Y + rk ↥C' :=
    c23a_o2_rk_sup_of_comm hcommYC' hYinfC'
  have hleU : Y ⊔ C' ≤ U := sup_le hYU inf_le_left
  have hrkle : rk ↥(Y ⊔ C') ≤ rk ↥U := rk_mono hleU
  have hrkC : 3 ≤ rk ↥U - rk ↥C' := by omega
  have hQuot : E3.mQuot U C' = rk ↥U - rk ↥C' :=
    c23a_o2_mQuot_eq_rk_sub (V := U) (U := C') inf_le_left
  have hQuot' : E3.mQuot U (centralizer (conjSubgroup V g : Set G)) = E3.mQuot U C' :=
    (c23a_o2_mQuot_inf_left U (centralizer (conjSubgroup V g : Set G))).symm
  have hge3 : 3 ≤ E3.mQuot U (centralizer (conjSubgroup V g : Set G)) := by
    rw [hQuot', hQuot]
    exact hrkC
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
