module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Fischer.Classification.Orthogonal2.Reflect
public import CFSG.Open.GLADefs
import CFSG.LocalAnalysis.StandardType.ZS.DThreeChain
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.Fischer.Classification.Defs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Fischer.Classification.Orth2
open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap

private def plusForm8 (c : Fin 8 → ZMod 2) : ZMod 2 :=
  c 0 * c 4 + c 1 * c 5 + c 2 * c 6 + c 3 * c 7

private def plusPolar8 (c c' : Fin 8 → ZMod 2) : ZMod 2 :=
  c 0 * c' 4 + c' 0 * c 4 + c 1 * c' 5 + c' 1 * c 5 +
    c 2 * c' 6 + c' 2 * c 6 + c 3 * c' 7 + c' 3 * c 7

private def eightCoord (c : Fin 8 → ZMod 2) : Fin 4 ⊕ Fin 4 → ZMod 2 :=
  fun i => c (finSumFinEquiv i)

private def eightOfCoord (c : Fin 4 ⊕ Fin 4 → ZMod 2) : Fin 8 → ZMod 2 :=
  fun j => c (finSumFinEquiv.symm j)

private theorem eightCoord_ofCoord (c : Fin 4 ⊕ Fin 4 → ZMod 2) :
    eightCoord (eightOfCoord c) = c := by
  funext i
  simp [eightCoord, eightOfCoord]

private theorem GLAQPlus_eq_plusForm8 (c : Fin 8 → ZMod 2) :
    CFSG.Open.GLAQPlus (ZMod 2) 4 (eightCoord c) = plusForm8 c := by
  change CFSG.Assembly.LargeEvenQPlus (ZMod 2) 4 (eightCoord c) = plusForm8 c
  rw [CFSG.Assembly.largeEvenQPlus_def]
  simp only [eightCoord, plusForm8, Fin.sum_univ_four,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  rfl

private def codeVec8 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) (k : ℕ) : V :=
  e.symm (eightCoord (bitVec 8 k))

private noncomputable abbrev reflO8 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (v : V) :
    TauCeti.QuadraticMap.orthogonalGroup Q :=
  ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩

private noncomputable abbrev tau8 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (k : ℕ) : TauCeti.QuadraticMap.orthogonalGroup Q :=
  reflO8 Q (codeVec8 e k)

private theorem Q_eightCoord {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (e v)) (c : Fin 8 → ZMod 2) :
    Q (e.symm (eightCoord c)) = plusForm8 c := by
  rw [hb, LinearEquiv.apply_symm_apply]
  exact GLAQPlus_eq_plusForm8 c

private theorem Q_codeVec8 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (e v)) (k : ℕ) :
    Q (codeVec8 e k) = plusForm8 (bitVec 8 k) := by
  rw [codeVec8]
  exact Q_eightCoord e hb (bitVec 8 k)

private theorem polar_eightCoord {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (e v)) (c c' : Fin 8 → ZMod 2) :
    polar Q (e.symm (eightCoord c)) (e.symm (eightCoord c')) = plusPolar8 c c' := by
  have hv : e.symm (eightCoord c) + e.symm (eightCoord c') =
      e.symm (eightCoord (c + c')) := by
    rw [← map_add]
    rfl
  rw [polar, hv, Q_eightCoord e hb (c + c'), Q_eightCoord e hb c,
    Q_eightCoord e hb c']
  simp only [plusForm8, plusPolar8, Pi.add_apply]
  ring_nf

private theorem polar_codeVec8 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (e v)) (a c : ℕ) :
    polar Q (codeVec8 e a) (codeVec8 e c) = plusPolar8 (bitVec 8 a) (bitVec 8 c) := by
  rw [codeVec8, codeVec8]
  exact polar_eightCoord e hb (bitVec 8 a) (bitVec 8 c)

private theorem codeVec8_xor {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) (a c : ℕ) :
    codeVec8 e (a ^^^ c) = codeVec8 e a + codeVec8 e c := by
  have h : eightCoord (bitVec 8 (a ^^^ c)) =
      eightCoord (bitVec 8 a) + eightCoord (bitVec 8 c) := by
    funext i
    simp only [eightCoord, Pi.add_apply]
    rw [bitVec_xor]
    rfl
  rw [codeVec8, codeVec8, codeVec8, h, map_add]

private theorem plusPolar8_self (c : Fin 8 → ZMod 2) : plusPolar8 c c = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [plusPolar8]
  linear_combination (c 0 * c 4 + c 1 * c 5 + c 2 * c 6 + c 3 * c 7) * h2

private theorem plusPolar8_comm (c c' : Fin 8 → ZMod 2) : plusPolar8 c c' = plusPolar8 c' c := by
  simp only [plusPolar8]
  ring_nf

private theorem eightCoord_eq_zero : eightCoord (0 : Fin 8 → ZMod 2) = 0 := rfl

private theorem eq_zero_of_plusPolar8_eq_zero {c : Fin 8 → ZMod 2}
    (h : ∀ c', plusPolar8 c c' = 0) : c = 0 := by
  have h0 : c 0 = 0 := by
    simpa [plusPolar8, Pi.single_apply] using h (Pi.single 4 1)
  have h1 : c 1 = 0 := by
    simpa [plusPolar8, Pi.single_apply] using h (Pi.single 5 1)
  have h2 : c 2 = 0 := by
    simpa [plusPolar8, Pi.single_apply] using h (Pi.single 6 1)
  have h3 : c 3 = 0 := by
    simpa [plusPolar8, Pi.single_apply] using h (Pi.single 7 1)
  have h4 : c 4 = 0 := by
    simpa [plusPolar8, Pi.single_apply] using h (Pi.single 0 1)
  have h5 : c 5 = 0 := by
    simpa [plusPolar8, Pi.single_apply] using h (Pi.single 1 1)
  have h6 : c 6 = 0 := by
    simpa [plusPolar8, Pi.single_apply] using h (Pi.single 2 1)
  have h7 : c 7 = 0 := by
    simpa [plusPolar8, Pi.single_apply] using h (Pi.single 3 1)
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]

private theorem polarBilin_nondegenerate_of_eightCoord {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (e v)) :
    (polarBilin Q).Nondegenerate := by
  have hleft : ∀ c : Fin 8 → ZMod 2, (∀ c', plusPolar8 c c' = 0) → c = 0 :=
    fun c => eq_zero_of_plusPolar8_eq_zero
  constructor
  · intro x hx
    have hx' : ∀ c', plusPolar8 (eightOfCoord (e x)) c' = 0 := by
      intro c'
      have h1 : polar Q x (e.symm (eightCoord c')) = 0 := by
        simpa using hx (e.symm (eightCoord c'))
      calc plusPolar8 (eightOfCoord (e x)) c'
          = polar Q (e.symm (eightCoord (eightOfCoord (e x))))
              (e.symm (eightCoord c')) := (polar_eightCoord e hb _ _).symm
        _ = polar Q x (e.symm (eightCoord c')) := by
              rw [eightCoord_ofCoord, LinearEquiv.symm_apply_apply]
        _ = 0 := h1
    have hc : eightOfCoord (e x) = 0 := hleft _ hx'
    have hx0 : x = 0 := by
      rw [← e.symm_apply_apply x, ← eightCoord_ofCoord (e x), hc, eightCoord_eq_zero,
        map_zero]
    exact hx0
  · intro y hy
    have hy' : ∀ c', plusPolar8 (eightOfCoord (e y)) c' = 0 := by
      intro c'
      have h1 : polar Q (e.symm (eightCoord c')) y = 0 := by
        simpa using hy (e.symm (eightCoord c'))
      calc plusPolar8 (eightOfCoord (e y)) c'
          = polar Q (e.symm (eightCoord (eightOfCoord (e y))))
              (e.symm (eightCoord c')) := (polar_eightCoord e hb _ _).symm
        _ = polar Q y (e.symm (eightCoord c')) := by
              rw [eightCoord_ofCoord, LinearEquiv.symm_apply_apply]
        _ = polar Q (e.symm (eightCoord c')) y := polar_comm _ _ _
        _ = 0 := h1
    have hc : eightOfCoord (e y) = 0 := hleft _ hy'
    have hy0 : y = 0 := by
      rw [← e.symm_apply_apply y, ← eightCoord_ofCoord (e y), hc, eightCoord_eq_zero,
        map_zero]
    exact hy0

private theorem orderOf_tau8_mul_tau8 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (e v)) (a c : ℕ)
    (ha : plusForm8 (bitVec 8 a) = 1) (hc : plusForm8 (bitVec 8 c) = 1)
    (hac : plusPolar8 (bitVec 8 a) (bitVec 8 c) = 1) :
    orderOf (tau8 Q e a * tau8 Q e c) = 3 := by
  have hua : Q (codeVec8 e a) = 1 := by rw [Q_codeVec8 e hb]; exact ha
  have huc : Q (codeVec8 e c) = 1 := by rw [Q_codeVec8 e hb]; exact hc
  have hp : polar Q (codeVec8 e a) (codeVec8 e c) = 1 := by
    rw [polar_codeVec8 e hb]; exact hac
  have hp' : polar Q (codeVec8 e c) (codeVec8 e a) = 1 := by
    rw [polar_comm]; exact hp
  have hbr1 : reflO8 Q (codeVec8 e a) * reflO8 Q (codeVec8 e c) *
      reflO8 Q (codeVec8 e a) = reflO8 Q (codeVec8 e a + codeVec8 e c) :=
    Subtype.ext (reflect_mul_reflect_mul_reflect (V := V) (Q := Q) hua hp)
  have hbr2 : reflO8 Q (codeVec8 e c) * reflO8 Q (codeVec8 e a) *
      reflO8 Q (codeVec8 e c) = reflO8 Q (codeVec8 e c + codeVec8 e a) :=
    Subtype.ext (reflect_mul_reflect_mul_reflect (V := V) (Q := Q) huc hp')
  have h3 : (tau8 Q e a * tau8 Q e c) ^ 3 = 1 := by
    change (reflO8 Q (codeVec8 e a) * reflO8 Q (codeVec8 e c)) ^ 3 = 1
    have h : (reflO8 Q (codeVec8 e a) * reflO8 Q (codeVec8 e c)) ^ 3 =
        (reflO8 Q (codeVec8 e a) * reflO8 Q (codeVec8 e c) *
          reflO8 Q (codeVec8 e a)) *
          (reflO8 Q (codeVec8 e c) * reflO8 Q (codeVec8 e a) *
            reflO8 Q (codeVec8 e c)) := by
      rw [pow_succ, pow_succ, pow_one]
      simp only [mul_assoc]
    rw [h, hbr1, hbr2, add_comm]
    apply Subtype.ext
    change reflect Q (codeVec8 e c + codeVec8 e a) *
      reflect Q (codeVec8 e c + codeVec8 e a) = 1
    exact reflect_mul_self Q _
  have hne : tau8 Q e a * tau8 Q e c ≠ 1 := by
    intro h1
    have h2 : (tau8 Q e a * tau8 Q e c : V ≃ₗ[ZMod 2] V)
        (codeVec8 e a) = codeVec8 e c := by
      change reflect Q (codeVec8 e a) (reflect Q (codeVec8 e c) (codeVec8 e a)) =
        codeVec8 e c
      rw [reflect_apply_of_map_eq_one huc, hp, one_smul,
        reflect_apply_of_map_eq_one hua, polar_add_left, polar_codeVec8 e hb a a,
        plusPolar8_self, polar_codeVec8 e hb c a, plusPolar8_comm, hac, zero_add, one_smul]
      rw [add_assoc, add_comm (codeVec8 e c) (codeVec8 e a), ← add_assoc,
        ZModModule.add_self, zero_add]
    have hwu : codeVec8 e c = codeVec8 e a := by
      rw [← h2]
      exact congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
        (g : V ≃ₗ[ZMod 2] V) (codeVec8 e a)) h1
    rw [hwu, polar_codeVec8 e hb a a, plusPolar8_self] at hp
    exact zero_ne_one hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 hne

private def e₈Codes : Fin 8 → ℕ :=
  ![136, 200, 196, 38, 216, 17, 248, 34]

private theorem plusForm8_e₈Codes : ∀ i : Fin 8, plusForm8 (bitVec 8 (e₈Codes i)) = 1 := by
  decide

private theorem Q_e₈Codes {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (e v)) (i : Fin 8) :
    Q (codeVec8 e (e₈Codes i)) = 1 := by
  rw [Q_codeVec8 e hb]
  exact plusForm8_e₈Codes i

private theorem e₈Codes_distinct :
    ∀ i j : Fin 8, eightCoord (bitVec 8 (e₈Codes i)) =
      eightCoord (bitVec 8 (e₈Codes j)) → i = j := by
  decide

private theorem e₈Codes_polar_edge :
    ∀ i j : Fin 8, CoxeterMatrix.E₈ i j = 3 →
      plusPolar8 (bitVec 8 (e₈Codes i)) (bitVec 8 (e₈Codes j)) = 1 := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val'] <;>
    decide

private theorem e₈Codes_polar_off :
    ∀ i j : Fin 8, i ≠ j → CoxeterMatrix.E₈ i j = 2 →
      plusPolar8 (bitVec 8 (e₈Codes i)) (bitVec 8 (e₈Codes j)) = 0 := by
  intro i j hne h
  fin_cases i <;> fin_cases j <;>
    simp_all [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val'] <;>
    decide

private def e₈Known : List ℕ := [136, 200, 196, 38, 216, 17, 248, 34]

private def e₈Next (a c : ℕ) : ℕ := a ^^^ c

private def e₈Ok (a c : ℕ) : Bool :=
  decide (plusForm8 (bitVec 8 a) = 1 ∧ plusForm8 (bitVec 8 c) = 1 ∧
    plusPolar8 (bitVec 8 a) (bitVec 8 c) = 1)

private def e₈Steps : List (ℕ × ℕ) := [
  (17, 216), (34, 248), (38, 196), (136, 196), (200, 38), (216, 38),
  (248, 17), (17, 218), (38, 76), (76, 238), (136, 162), (196, 254),
  (200, 58), (201, 38), (216, 106), (218, 201), (226, 19), (233, 58),
  (238, 19), (248, 201), (254, 42), (17, 58), (19, 38), (34, 53),
  (42, 19), (49, 42), (58, 162), (76, 23), (106, 19), (136, 27),
  (162, 19), (178, 17), (196, 27), (200, 43), (201, 152), (203, 81),
  (211, 162), (212, 17), (216, 81), (218, 81), (226, 137), (233, 81),
  (238, 81), (239, 27), (241, 139), (242, 23), (248, 81), (253, 43),
  (254, 57), (19, 113), (23, 42), (27, 53), (34, 61), (38, 81),
  (42, 121), (43, 119), (49, 92), (53, 81), (57, 92), (58, 100),
  (76, 81), (81, 23), (91, 31), (106, 92), (107, 23), (113, 29),
  (121, 54), (122, 46), (136, 29), (137, 23), (139, 23), (147, 29),
  (152, 23), (154, 23), (162, 23), (163, 31), (169, 31), (177, 23),
  (178, 31), (184, 31), (191, 19), (196, 83), (197, 79), (199, 124),
  (200, 68), (201, 140), (203, 140), (211, 138), (212, 69), (214, 152),
  (216, 142), (218, 151), (223, 119), (226, 197), (227, 145), (229, 145),
  (233, 138), (238, 145), (68, 81), (69, 92), (70, 101), (71, 121),
  (76, 99), (77, 127), (78, 136), (79, 158), (81, 140), (83, 168),
  (84, 158), (86, 178), (89, 177), (91, 172)]

private theorem e₈_chainOK :
    chainOK e₈Next e₈Ok e₈Known e₈Steps = true := by
  decide +kernel

private theorem e₈_cover :
    ∀ k < 2 ^ 8, plusForm8 (bitVec 8 k) = 1 →
      k ∈ chainLabels e₈Next e₈Known e₈Steps := by
  decide +kernel

private theorem exists_code_eq : ∀ k ∈ e₈Known, ∃ i : Fin 8, e₈Codes i = k := by
  decide +kernel

private theorem tau8_add_mem {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (e v))
    (H : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) (a c : ℕ)
    (ha : tau8 Q e a ∈ H) (hc : tau8 Q e c ∈ H)
    (hok : e₈Ok a c = true) :
    tau8 Q e (e₈Next a c) ∈ H := by
  simp only [e₈Ok, decide_eq_true_eq] at hok
  obtain ⟨haq, hcq, hac⟩ := hok
  have hu : Q (codeVec8 e a) = 1 := by rw [Q_codeVec8 e hb]; exact haq
  have hw : Q (codeVec8 e c) = 1 := by rw [Q_codeVec8 e hb]; exact hcq
  have hp : polar Q (codeVec8 e a) (codeVec8 e c) = 1 := by
    rw [polar_codeVec8 e hb]; exact hac
  have hbr : tau8 Q e a * tau8 Q e c * tau8 Q e a =
      tau8 Q e (e₈Next a c) := by
    change reflO8 Q (codeVec8 e a) * reflO8 Q (codeVec8 e c) *
      reflO8 Q (codeVec8 e a) = reflO8 Q (codeVec8 e (a ^^^ c))
    rw [codeVec8_xor]
    exact Subtype.ext (reflect_mul_reflect_mul_reflect hu hp)
  rw [← hbr]
  exact mul_mem (mul_mem ha hc) ha

private theorem reflClass_le_closure_e₈ {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (e v)) :
    reflClass Q ⊆
      (Subgroup.closure (Set.range fun i : Fin 8 => tau8 Q e (e₈Codes i)) :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  classical
  set H := Subgroup.closure (Set.range fun i : Fin 8 => tau8 Q e (e₈Codes i)) with hH
  have hstep : ∀ a c, tau8 Q e a ∈ H → tau8 Q e c ∈ H →
      e₈Ok a c = true → tau8 Q e (e₈Next a c) ∈ H :=
    fun a c => tau8_add_mem e hb H a c
  have hinit : ∀ k ∈ e₈Known, tau8 Q e k ∈ H := by
    intro k hk
    obtain ⟨i, rfl⟩ := exists_code_eq k hk
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hlabel := mem_of_chainOK H (fun k => tau8 Q e k) e₈Next e₈Ok hstep
    e₈Steps e₈Known hinit e₈_chainOK
  intro g hg
  obtain ⟨v, hv, hgv⟩ := mem_reflClass.mp hg
  set u : Fin 8 → ZMod 2 := eightOfCoord (e v) with hu
  obtain ⟨k, hk, hku⟩ := exists_lt_bitVec_eq u
  have hkvec : eightCoord (bitVec 8 k) = e v := by
    rw [hku, hu, eightCoord_ofCoord]
  have hvk : v = codeVec8 e k := by
    rw [codeVec8, hkvec, LinearEquiv.symm_apply_apply]
  have hq : plusForm8 (bitVec 8 k) = 1 := by
    rw [← Q_codeVec8 e hb k, ← hvk]
    exact hv
  have hmem : tau8 Q e k ∈ H := hlabel k (e₈_cover k hk hq)
  have hgτ : g = tau8 Q e k := by
    refine Subtype.ext ?_
    rw [hgv, hvk]
  rw [hgτ]
  exact hmem

private theorem exists_coxeterConfig_E₈_of_equiv {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V}
    (e : V ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (e v))
    (htop : Subgroup.closure (reflClass Q) = ⊤) :
    ∃ d : Fin 8 → TauCeti.QuadraticMap.orthogonalGroup Q,
      CoxeterConfig (reflClass Q) CoxeterMatrix.E₈ d ∧
        Subgroup.closure (Set.range d) = ⊤ := by
  classical
  have hnd := polarBilin_nondegenerate_of_eightCoord e hb
  refine ⟨fun i => tau8 Q e (e₈Codes i), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨codeVec8 e (e₈Codes i), Q_e₈Codes e hb i, rfl⟩
    · intro i j hij
      refine e₈Codes_distinct i j ?_
      have hvec : codeVec8 e (e₈Codes i) = codeVec8 e (e₈Codes j) :=
        eq_of_reflect_eq hnd (Q_e₈Codes e hb i) (congrArg Subtype.val hij)
          (Q_e₈Codes e hb j)
      have hcoord := congrArg e hvec
      simpa [codeVec8] using hcoord
    · intro i j h
      exact orderOf_tau8_mul_tau8 e hb _ _ (plusForm8_e₈Codes i) (plusForm8_e₈Codes j)
        (e₈Codes_polar_edge i j h)
    · intro i j hne h
      refine Subtype.ext ((reflect_mul_comm_iff (Q_e₈Codes e hb i)
        (Q_e₈Codes e hb j)).mpr ?_)
      rw [polar_codeVec8 e hb]
      exact e₈Codes_polar_off i j hne h
  · rw [eq_top_iff, ← htop, Subgroup.closure_le]
    exact reflClass_le_closure_e₈ e hb

theorem exists_coxeterConfig_E₈_reflClass_plus
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 4) → ZMod 2)}
    (b : Module.Basis (Fin 4 ⊕ Fin 4) (ZMod 2) (Fin (2 * 4) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 4 (b.equivFun v))
    (htop : Subgroup.closure (reflClass Q) = ⊤) :
    ∃ d : Fin 8 → TauCeti.QuadraticMap.orthogonalGroup Q,
      CoxeterConfig (reflClass Q) CoxeterMatrix.E₈ d ∧
        Subgroup.closure (Set.range d) = ⊤ :=
  exists_coxeterConfig_E₈_of_equiv b.equivFun hb htop

end CFSG.StandardType.ZS
