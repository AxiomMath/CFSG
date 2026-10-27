module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Fischer.Classification.Orthogonal2.Reflect
public import CFSG.Open.GLADefs
import CFSG.LocalAnalysis.StandardType.ZS.DThreeChain
import CFSG.Fischer.Classification.Orthogonal2.Pair
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.Fischer.Classification.Defs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
import CFSG.RankThree.GroupTheory.ClassTwoThree
import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Fischer.Classification.Orth2 QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.Fischer.Classification.Recognition.SymO

private def plusIdx : Fin 3 ⊕ Fin 3 → Fin 6
  | Sum.inl i => ⟨i.val, by omega⟩
  | Sum.inr i => ⟨3 + i.val, by omega⟩

private def plusIdxInv (j : Fin 6) : Fin 3 ⊕ Fin 3 :=
  if h : j.val < 3 then Sum.inl ⟨j.val, h⟩ else Sum.inr ⟨j.val - 3, by omega⟩

private def plusCoord (k : ℕ) : Fin 3 ⊕ Fin 3 → ZMod 2 :=
  fun i => bitVec 6 k (plusIdx i)

private theorem plusIdx_left : ∀ i : Fin 3 ⊕ Fin 3, plusIdxInv (plusIdx i) = i :=
  by decide

private def plusForm6 (c : Fin 3 ⊕ Fin 3 → ZMod 2) : ZMod 2 :=
  c (Sum.inl 0) * c (Sum.inr 0) + c (Sum.inl 1) * c (Sum.inr 1) + c (Sum.inl 2) * c (Sum.inr 2)

private def a₇Codes : Fin 7 → ℕ := ![36, 50, 44, 9, 60, 18, 52]

private def a₇Steps : List (ℕ × ℕ) :=
  [(36, 50), (9, 44), (9, 60), (44, 50), (44, 53), (44, 22), (50, 37), (50, 25), (18, 43),
   (18, 52), (18, 53), (18, 25), (18, 60), (52, 11), (52, 39), (52, 46), (52, 57), (9, 58),
   (11, 22), (13, 36), (18, 29)]

private def a₇Ok (a b : ℕ) : Bool :=
  decide (plusForm6 (plusCoord a) = 1 ∧ plusForm6 (plusCoord b) = 1 ∧
    polar plusForm6 (plusCoord a) (plusCoord b) = 1)

private theorem plusForm6_eq_GLAQPlus (c : Fin 3 ⊕ Fin 3 → ZMod 2) :
    CFSG.Open.GLAQPlus (ZMod 2) 3 c = plusForm6 c := by
  simp only [CFSG.Assembly.largeEvenQPlus_def, Fin.sum_univ_three, plusForm6]

private theorem plusCoord_xor (a b : ℕ) :
    plusCoord (a ^^^ b) = plusCoord a + plusCoord b := by
  funext i
  simp only [plusCoord, bitVec_xor, Pi.add_apply]

private theorem zo4_Q_of_coord {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ι : Type} {e : V ≃ₗ[ZMod 2] (ι → ZMod 2)} {Q : QuadraticForm (ZMod 2) V}
    {q q' : (ι → ZMod 2) → ZMod 2} (hqq' : ∀ c, q c = q' c) (hQ : ∀ v, Q v = q (e v)) (v : V) :
    Q v = q' (e v) := by
  rw [hQ v]
  exact hqq' (e v)

private theorem zo4_polar_eq_of_coord {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ι : Type} {e : V ≃ₗ[ZMod 2] (ι → ZMod 2)} {Q : QuadraticForm (ZMod 2) V}
    {q : (ι → ZMod 2) → ZMod 2} (hQ : ∀ v, Q v = q (e v)) (c c' : ι → ZMod 2) :
    polar Q (e.symm c) (e.symm c') = polar q c c' := by
  have h1 : e.symm c + e.symm c' = e.symm (c + c') := by
    rw [← map_add]
  have hp : polar Q (e.symm c) (e.symm c') =
      Q (e.symm c + e.symm c') - Q (e.symm c) - Q (e.symm c') := rfl
  rw [hp, h1]
  simp only [hQ, LinearEquiv.apply_symm_apply]
  rfl

private theorem plusPolar6_nondeg (c : Fin 3 ⊕ Fin 3 → ZMod 2) (hc : c ≠ 0) :
    ∃ c', polar plusForm6 c c' = 1 := by
  revert c
  decide

private theorem plusForm6_a₇Codes : ∀ i : Fin 7, plusForm6 (plusCoord (a₇Codes i)) = 1 :=
  by decide

private theorem plusPolar6_a₇Codes : ∀ p : Fin 7 × Fin 7,
    polar plusForm6 (plusCoord (a₇Codes p.1))
      (plusCoord (a₇Codes p.2)) = if CoxeterMatrix.A 7 p.1 p.2 = 3 then 1 else 0 :=
  by decide

private theorem a₇Codes_distinct : ∀ p : Fin 7 × Fin 7,
    plusCoord (a₇Codes p.1) = plusCoord (a₇Codes p.2) → p.1 = p.2 :=
  by decide

private theorem plusCoord_surj (c : Fin 3 ⊕ Fin 3 → ZMod 2) :
    ∃ k : Fin 64, plusCoord k = c := by
  obtain ⟨k, hk, hbit⟩ := exists_lt_bitVec_eq (fun j : Fin 6 => c (plusIdxInv j))
  refine ⟨⟨k, by simpa using hk⟩, ?_⟩
  funext i
  simp only [plusCoord, hbit, plusIdx_left]

private theorem a₇_chainOK :
    chainOK (fun a b => a ^^^ b) a₇Ok (List.ofFn a₇Codes) a₇Steps =
      true := by
  decide

private theorem a₇_cover : ∀ k : Fin 64, plusForm6 (plusCoord k) = 1 →
    ((k : ℕ) ∈ chainLabels (fun a b => a ^^^ b) (List.ofFn a₇Codes) a₇Steps) :=
  by decide

private def minusIdx : (Fin 2 ⊕ Fin 2) ⊕ Fin 2 → Fin 6
  | Sum.inl (Sum.inl i) => ⟨i.val, by omega⟩
  | Sum.inl (Sum.inr i) => ⟨2 + i.val, by omega⟩
  | Sum.inr j => ⟨4 + j.val, by omega⟩

private def minusIdxInv (j : Fin 6) : (Fin 2 ⊕ Fin 2) ⊕ Fin 2 :=
  if h : j.val < 2 then Sum.inl (Sum.inl ⟨j.val, h⟩)
  else if h' : j.val < 4 then Sum.inl (Sum.inr ⟨j.val - 2, by omega⟩)
  else Sum.inr ⟨j.val - 4, by omega⟩

private def minusCoord (k : ℕ) : (Fin 2 ⊕ Fin 2) ⊕ Fin 2 → ZMod 2 :=
  fun i => bitVec 6 k (minusIdx i)

private theorem minusIdx_left :
    ∀ i : (Fin 2 ⊕ Fin 2) ⊕ Fin 2, minusIdxInv (minusIdx i) = i := by
  decide

private def minusForm6 (c : (Fin 2 ⊕ Fin 2) ⊕ Fin 2 → ZMod 2) : ZMod 2 :=
  c (Sum.inl (Sum.inl 0)) * c (Sum.inl (Sum.inr 0)) +
    c (Sum.inl (Sum.inl 1)) * c (Sum.inl (Sum.inr 1)) +
    c (Sum.inr 0) ^ 2 + c (Sum.inr 0) * c (Sum.inr 1) + c (Sum.inr 1) ^ 2

private def e₆Codes : Fin 6 → ℕ := ![32, 40, 18, 34, 44, 5]

private def e₆Steps : List (ℕ × ℕ) :=
  [(32, 18), (34, 40), (34, 44), (34, 18), (34, 50), (5, 44), (5, 14), (40, 11), (40, 14),
   (40, 48), (40, 16), (44, 48), (44, 16), (44, 24), (44, 56), (18, 11), (18, 35), (5, 20),
   (5, 60), (10, 25), (10, 28), (10, 57), (10, 60), (11, 20), (11, 52), (16, 49), (16, 52),
   (16, 63), (18, 31), (20, 19)]

private def e₆Ok (a b : ℕ) : Bool :=
  decide (minusForm6 (minusCoord a) = 1 ∧ minusForm6 (minusCoord b) = 1 ∧
    polar minusForm6 (minusCoord a) (minusCoord b) = 1)

private theorem minusForm6_eq_GLAQMinus (c : (Fin 2 ⊕ Fin 2) ⊕ Fin 2 → ZMod 2) :
    CFSG.Open.GLAQMinus 2 (1 : ZMod 2) 1 c = minusForm6 c := by
  simp only [CFSG.Open.GLAQMinus, CFSG.Assembly.LargeEvenQMinus, Fin.sum_univ_two, one_mul,
    minusForm6]

private theorem minusCoord_xor (a b : ℕ) :
    minusCoord (a ^^^ b) = minusCoord a + minusCoord b := by
  funext i
  simp only [minusCoord, bitVec_xor, Pi.add_apply]

private theorem minusForm6_e₆Codes :
    ∀ i : Fin 6, minusForm6 (minusCoord (e₆Codes i)) = 1 := by decide

private theorem minusPolar6_e₆Codes : ∀ p : Fin 6 × Fin 6,
    polar minusForm6 (minusCoord (e₆Codes p.1))
      (minusCoord (e₆Codes p.2)) = if CoxeterMatrix.E₆ p.1 p.2 = 3 then 1 else 0 :=
  by decide

private theorem e₆Codes_distinct : ∀ p : Fin 6 × Fin 6,
    minusCoord (e₆Codes p.1) = minusCoord (e₆Codes p.2) → p.1 = p.2 :=
  by decide

private theorem minusCoord_surj (c : (Fin 2 ⊕ Fin 2) ⊕ Fin 2 → ZMod 2) :
    ∃ k : Fin 64, minusCoord k = c := by
  obtain ⟨k, hk, hbit⟩ := exists_lt_bitVec_eq (fun j : Fin 6 => c (minusIdxInv j))
  refine ⟨⟨k, by simpa using hk⟩, ?_⟩
  funext i
  simp only [minusCoord, hbit, minusIdx_left]

private theorem minusPolar6_nondeg (c : (Fin 2 ⊕ Fin 2) ⊕ Fin 2 → ZMod 2) (hc : c ≠ 0) :
    ∃ c', polar minusForm6 c c' = 1 := by
  obtain ⟨k, hk⟩ := minusCoord_surj c
  rw [← hk] at hc ⊢
  exact (by decide : ∀ k : Fin 64, minusCoord k ≠ 0 →
    ∃ c', polar minusForm6 (minusCoord k) c' = 1) k hc

private theorem e₆_chainOK :
    chainOK (fun a b => a ^^^ b) e₆Ok (List.ofFn e₆Codes) e₆Steps =
      true := by
  decide

private theorem e₆_cover : ∀ k : Fin 64, minusForm6 (minusCoord k) = 1 →
    ((k : ℕ) ∈ chainLabels (fun a b => a ^^^ b) (List.ofFn e₆Codes) e₆Steps) :=
  by decide

private theorem orderOf_reflO_mul_reflO {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hnd : (polarBilin Q).Nondegenerate) {u w : V}
    (hu : Q u = 1) (hw : Q w = 1) (huw : polar Q u w = 1) :
    orderOf (reflO Q u * reflO Q w) = 3 := by
  have hwu : polar Q w u = 1 := by rw [polar_comm]; exact huw
  have h3 : (reflO Q u * reflO Q w) ^ 3 = 1 := by
    have hbr1 : reflO Q u * reflO Q w * reflO Q u = reflO Q (u + w) :=
      Subtype.ext (reflect_mul_reflect_mul_reflect hu huw)
    have hbr2 : reflO Q w * reflO Q u * reflO Q w = reflO Q (w + u) :=
      Subtype.ext (reflect_mul_reflect_mul_reflect hw hwu)
    have h : (reflO Q u * reflO Q w) ^ 3 =
        (reflO Q u * reflO Q w * reflO Q u) * (reflO Q w * reflO Q u * reflO Q w) := by
      rw [pow_succ, pow_succ, pow_one]
      simp only [mul_assoc]
    rw [h, hbr1, hbr2, add_comm]
    exact Subtype.ext (reflect_mul_self Q (w + u))
  refine orderOf_eq_prime h3 ?_
  intro h1
  have h2 : reflO Q u = reflO Q w := by
    have hw2 : reflO Q w * reflO Q w = 1 := Subtype.ext (reflect_mul_self Q w)
    have hh := congrArg (· * reflO Q w) h1
    simpa only [mul_assoc, hw2, mul_one, one_mul] using hh
  have huw' : u = w := eq_of_reflect_eq hnd hu (congrArg Subtype.val h2) hw
  rw [huw', polar_self_zmod_two] at huw
  exact zero_ne_one huw

private theorem polarBilin_nondegenerate_of_coord {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ι : Type} {e : V ≃ₗ[ZMod 2] (ι → ZMod 2)} {Q : QuadraticForm (ZMod 2) V}
    {q : (ι → ZMod 2) → ZMod 2} (hB : ∀ c c', polar Q (e.symm c) (e.symm c') = polar q c c')
    (hq : ∀ c : ι → ZMod 2, c ≠ 0 → ∃ c', polar q c c' = 1) :
    (polarBilin Q).Nondegenerate := by
  have key : ∀ x : V, (∀ y : V, polar Q x y = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have he : e x ≠ 0 := by
      intro he0
      exact hx0 (by rw [← e.symm_apply_apply x, he0, map_zero])
    obtain ⟨c', hc'⟩ := hq (e x) he
    have h1 : polar Q x (e.symm c') = 1 := by
      rw [← e.symm_apply_apply x, hB]
      exact hc'
    exact one_ne_zero (h1.symm.trans (hx _))
  refine ⟨fun x hx => key x fun y => ?_, fun y hy => key y fun x => ?_⟩
  · exact (polarBilin_apply_apply Q x y).symm.trans (hx y)
  · rw [polar_comm Q y x]
    exact (polarBilin_apply_apply Q x y).symm.trans (hy x)

private theorem coxeterConfig_reflO_of_codes {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ι : Type} {e : V ≃ₗ[ZMod 2] (ι → ZMod 2)} {Q : QuadraticForm (ZMod 2) V}
    {q : (ι → ZMod 2) → ZMod 2} (hnd : (polarBilin Q).Nondegenerate)
    {m : ℕ} {M : CoxeterMatrix (Fin m)} {codes : Fin m → ℕ} {co : ℕ → ι → ZMod 2}
    (hQe : ∀ k, Q (e.symm (co k)) = q (co k))
    (hBe : ∀ a b, polar Q (e.symm (co a)) (e.symm (co b)) = polar q (co a) (co b))
    (hQcodes : ∀ i, q (co (codes i)) = 1)
    (hTable : ∀ i j, polar q (co (codes i)) (co (codes j)) = if M i j = 3 then 1 else 0)
    (hdistinct : ∀ i j, co (codes i) = co (codes j) → i = j) :
    CoxeterConfig (reflClass Q) M (fun i => reflO Q (e.symm (co (codes i)))) := by
  have hQc : ∀ i : Fin m, Q (e.symm (co (codes i))) = 1 := by
    intro i
    rw [hQe, hQcodes]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨e.symm (co (codes i)), hQc i, rfl⟩
  · intro i j hij
    have hval : reflect Q (e.symm (co (codes i))) = reflect Q (e.symm (co (codes j))) :=
      congrArg Subtype.val hij
    have hvec := eq_of_reflect_eq hnd (hQc i) hval (hQc j)
    refine hdistinct i j ?_
    have h2 := congrArg e hvec
    simpa only [LinearEquiv.apply_symm_apply] using h2
  · intro i j hij
    have hp : polar Q (e.symm (co (codes i))) (e.symm (co (codes j))) = 1 := by
      rw [hBe, hTable i j]
      simp [hij]
    exact orderOf_reflO_mul_reflO hnd (hQc i) (hQc j) hp
  · intro i j hne hM
    have hp : polar Q (e.symm (co (codes i))) (e.symm (co (codes j))) = 0 := by
      rw [hBe, hTable i j]
      simp [hM]
    exact Subtype.ext ((reflect_mul_comm_iff (hQc i) (hQc j)).mpr hp)

private theorem closure_eq_top_of_codes {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ι : Type} {e : V ≃ₗ[ZMod 2] (ι → ZMod 2)} {Q : QuadraticForm (ZMod 2) V}
    {q : (ι → ZMod 2) → ZMod 2} {m N : ℕ} {codes : Fin m → ℕ} {steps : List (ℕ × ℕ)}
    {co : ℕ → ι → ZMod 2} (hQe : ∀ k, Q (e.symm (co k)) = q (co k))
    (hBe : ∀ a b, polar Q (e.symm (co a)) (e.symm (co b)) = polar q (co a) (co b))
    (hcoadd : ∀ a b, e.symm (co (a ^^^ b)) = e.symm (co a) + e.symm (co b))
    (hsurj : ∀ c : ι → ZMod 2, ∃ k : Fin N, co k = c)
    (hchain : chainOK (fun a b => a ^^^ b)
        (fun a b => decide (q (co a) = 1 ∧ q (co b) = 1 ∧ polar q (co a) (co b) = 1))
        (List.ofFn codes) steps = true)
    (hcover : ∀ k : Fin N, q (co k) = 1 →
        (k : ℕ) ∈ chainLabels (fun a b => a ^^^ b) (List.ofFn codes) steps)
    (htop : Subgroup.closure (reflClass Q) = ⊤) :
    Subgroup.closure (Set.range (fun i => reflO Q (e.symm (co (codes i))))) = ⊤ := by
  let τ : ℕ → TauCeti.QuadraticMap.orthogonalGroup Q := fun k => reflO Q (e.symm (co k))
  let d : Fin m → TauCeti.QuadraticMap.orthogonalGroup Q := fun i => τ (codes i)
  change Subgroup.closure (Set.range d) = ⊤
  have hstep : ∀ a b, τ a ∈ Subgroup.closure (Set.range d) →
      τ b ∈ Subgroup.closure (Set.range d) →
      (decide (q (co a) = 1 ∧ q (co b) = 1 ∧ polar q (co a) (co b) = 1) = true) →
      τ (a ^^^ b) ∈ Subgroup.closure (Set.range d) := by
    intro a b ha hb hab
    rw [decide_eq_true_eq] at hab
    obtain ⟨hqa, hqb, hqab⟩ := hab
    have hua : Q (e.symm (co a)) = 1 := by rw [hQe]; exact hqa
    have hub : Q (e.symm (co b)) = 1 := by rw [hQe]; exact hqb
    have huab : polar Q (e.symm (co a)) (e.symm (co b)) = 1 := by rw [hBe]; exact hqab
    have hbraid : τ a * τ b * τ a = τ (a ^^^ b) := by
      have h : τ a * τ b * τ a = reflO Q (e.symm (co a) + e.symm (co b)) :=
        Subtype.ext (reflect_mul_reflect_mul_reflect (Q := Q) hua huab)
      rw [← hcoadd] at h
      exact h
    have hmem : τ a * τ b * τ a ∈ Subgroup.closure (Set.range d) :=
      mul_mem (mul_mem ha hb) ha
    rwa [hbraid] at hmem
  have hknown : ∀ k ∈ List.ofFn codes, τ k ∈ Subgroup.closure (Set.range d) := by
    intro k hk
    rw [List.mem_ofFn', Set.mem_range] at hk
    obtain ⟨i, rfl⟩ := hk
    exact Subgroup.subset_closure (Set.mem_range_self i)
  apply top_unique
  rw [← htop, Subgroup.closure_le]
  rintro g ⟨v, hv, hgv⟩
  obtain ⟨k, hk⟩ := hsurj (e v)
  have hvk : e.symm (co (k : ℕ)) = v := by rw [hk, LinearEquiv.symm_apply_apply]
  have hqk : q (co (k : ℕ)) = 1 := by rw [← hQe (k : ℕ), hvk, hv]
  have hmem := mem_of_chainOK (Subgroup.closure (Set.range d)) τ (fun a b => a ^^^ b)
    (fun a b => decide (q (co a) = 1 ∧ q (co b) = 1 ∧ polar q (co a) (co b) = 1))
    hstep steps (List.ofFn codes) hknown hchain (k : ℕ) (hcover k hqk)
  have hτ : τ (k : ℕ) = reflO Q v := by simp only [τ, hvk]
  rw [hτ] at hmem
  have hg : g = reflO Q v := Subtype.ext hgv
  rwa [hg]

private theorem exists_coxeterConfig_of_codes {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ι : Type} {e : V ≃ₗ[ZMod 2] (ι → ZMod 2)} {Q : QuadraticForm (ZMod 2) V}
    {q : (ι → ZMod 2) → ZMod 2} (hQ : ∀ v, Q v = q (e v))
    (hB : ∀ c c', polar Q (e.symm c) (e.symm c') = polar q c c')
    (hq : ∀ c : ι → ZMod 2, c ≠ 0 → ∃ c', polar q c c' = 1)
    {m N : ℕ} {M : CoxeterMatrix (Fin m)} {codes : Fin m → ℕ} {steps : List (ℕ × ℕ)}
    {co : ℕ → ι → ZMod 2} (hcoadd : ∀ a b, co (a ^^^ b) = co a + co b)
    (hsurj : ∀ c : ι → ZMod 2, ∃ k : Fin N, co k = c)
    (hQcodes : ∀ i, q (co (codes i)) = 1)
    (hTable : ∀ i j, polar q (co (codes i)) (co (codes j)) = if M i j = 3 then 1 else 0)
    (hdistinct : ∀ i j, co (codes i) = co (codes j) → i = j)
    (hchain : chainOK (fun a b => a ^^^ b)
        (fun a b => decide (q (co a) = 1 ∧ q (co b) = 1 ∧ polar q (co a) (co b) = 1))
        (List.ofFn codes) steps = true)
    (hcover : ∀ k : Fin N, q (co k) = 1 →
        (k : ℕ) ∈ chainLabels (fun a b => a ^^^ b) (List.ofFn codes) steps)
    (htop : Subgroup.closure (reflClass Q) = ⊤) :
    ∃ d : Fin m → TauCeti.QuadraticMap.orthogonalGroup Q,
      CoxeterConfig (reflClass Q) M d ∧ Subgroup.closure (Set.range d) = ⊤ := by
  have hQe : ∀ k : ℕ, Q (e.symm (co k)) = q (co k) := by
    intro k
    rw [hQ, LinearEquiv.apply_symm_apply]
  have hBe : ∀ a b, polar Q (e.symm (co a)) (e.symm (co b)) = polar q (co a) (co b) :=
    fun a b => hB (co a) (co b)
  have hcoadd' : ∀ a b, e.symm (co (a ^^^ b)) = e.symm (co a) + e.symm (co b) := by
    intro a b
    rw [hcoadd, map_add]
  exact ⟨fun i => reflO Q (e.symm (co (codes i))),
    coxeterConfig_reflO_of_codes (polarBilin_nondegenerate_of_coord hB hq) hQe hBe hQcodes hTable
      hdistinct,
    closure_eq_top_of_codes hQe hBe hcoadd' hsurj hchain hcover htop⟩

theorem exists_coxeterConfig_A₇_reflClass_plus
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2)}
    (b : Module.Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Fin (2 * 3) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 3 (b.equivFun v))
    (htop : Subgroup.closure (reflClass Q) = ⊤) :
    ∃ d : Fin 7 → TauCeti.QuadraticMap.orthogonalGroup Q,
      CoxeterConfig (reflClass Q) (CoxeterMatrix.A 7) d ∧
        Subgroup.closure (Set.range d) = ⊤ := by
  have hQ : ∀ v, Q v = plusForm6 (b.equivFun v) :=
    fun v => zo4_Q_of_coord plusForm6_eq_GLAQPlus hb v
  refine exists_coxeterConfig_of_codes (e := b.equivFun) (q := plusForm6) hQ ?_ plusPolar6_nondeg
    plusCoord_xor plusCoord_surj plusForm6_a₇Codes ?_ ?_ a₇_chainOK a₇_cover htop
  · intro c c'
    exact zo4_polar_eq_of_coord hQ c c'
  · intro i j
    exact plusPolar6_a₇Codes (i, j)
  · intro i j
    exact a₇Codes_distinct (i, j)

theorem exists_coxeterConfig_E₆_reflClass_minus
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2)}
    (b : Module.Basis (CFSG.Open.GLAMinusIdx 2) (ZMod 2) (Fin (2 * 3) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQMinus 2 (1 : ZMod 2) 1 (b.equivFun v))
    (htop : Subgroup.closure (reflClass Q) = ⊤) :
    ∃ d : Fin 6 → TauCeti.QuadraticMap.orthogonalGroup Q,
      CoxeterConfig (reflClass Q) CoxeterMatrix.E₆ d ∧
        Subgroup.closure (Set.range d) = ⊤ := by
  have hQ : ∀ v, Q v = minusForm6 (b.equivFun v) :=
    fun v => zo4_Q_of_coord minusForm6_eq_GLAQMinus hb v
  refine exists_coxeterConfig_of_codes (e := b.equivFun) (q := minusForm6) hQ ?_ minusPolar6_nondeg
    minusCoord_xor minusCoord_surj minusForm6_e₆Codes ?_ ?_ e₆_chainOK e₆_cover htop
  · intro c c'
    exact zo4_polar_eq_of_coord hQ c c'
  · intro i j
    exact minusPolar6_e₆Codes (i, j)
  · intro i j
    exact e₆Codes_distinct (i, j)

private def zo4_minus4Idx : CFSG.Open.GLAMinusIdx 1 → Fin 4
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr j => ⟨j.val + 2, by omega⟩

private def zo4_minus4IdxInv (j : Fin 4) : CFSG.Open.GLAMinusIdx 1 :=
  if h : j.val < 1 then Sum.inl (Sum.inl ⟨j.val, h⟩)
  else if h' : j.val < 2 then Sum.inl (Sum.inr ⟨j.val - 1, by omega⟩)
  else Sum.inr ⟨j.val - 2, by omega⟩

private def zo4_minus4Coord (k : ℕ) : CFSG.Open.GLAMinusIdx 1 → ZMod 2 :=
  fun i => bitVec 4 k (zo4_minus4Idx i)

private theorem zo4_minus4Idx_left :
    ∀ i : CFSG.Open.GLAMinusIdx 1, zo4_minus4IdxInv (zo4_minus4Idx i) = i := by
  decide

private def zo4_minus4Form (c : CFSG.Open.GLAMinusIdx 1 → ZMod 2) : ZMod 2 :=
  c (Sum.inl (Sum.inl 0)) * c (Sum.inl (Sum.inr 0)) +
    c (Sum.inr 0) ^ 2 + c (Sum.inr 0) * c (Sum.inr 1) + c (Sum.inr 1) ^ 2

private theorem zo4_minus4Form_eq_GLAQMinus (c : CFSG.Open.GLAMinusIdx 1 → ZMod 2) :
    CFSG.Open.GLAQMinus 1 (1 : ZMod 2) 1 c = zo4_minus4Form c := by
  simp only [CFSG.Open.GLAQMinus, CFSG.Assembly.LargeEvenQMinus, Fin.sum_univ_one, one_mul,
    zo4_minus4Form]

private def zo4_a₄Codes : Fin 4 → ℕ := ![3, 5, 8, 4]

private def zo4_a₄Steps : List (ℕ × ℕ) := [(3, 5), (5, 8), (8, 4), (8, 6), (4, 13), (4, 14)]

private def zo4_a₄Ok (a b : ℕ) : Bool :=
  decide (zo4_minus4Form (zo4_minus4Coord a) = 1 ∧ zo4_minus4Form (zo4_minus4Coord b) = 1 ∧
    polar zo4_minus4Form (zo4_minus4Coord a) (zo4_minus4Coord b) = 1)

private theorem zo4_minus4Form_a₄Codes :
    ∀ i : Fin 4, zo4_minus4Form (zo4_minus4Coord (zo4_a₄Codes i)) = 1 := by decide

private theorem zo4_minus4Polar_a₄Codes : ∀ p : Fin 4 × Fin 4,
    polar zo4_minus4Form (zo4_minus4Coord (zo4_a₄Codes p.1))
      (zo4_minus4Coord (zo4_a₄Codes p.2)) =
      if CoxeterMatrix.A 4 p.1 p.2 = 3 then 1 else 0 :=
  by decide

private theorem zo4_a₄Codes_distinct : ∀ p : Fin 4 × Fin 4,
    zo4_minus4Coord (zo4_a₄Codes p.1) = zo4_minus4Coord (zo4_a₄Codes p.2) → p.1 = p.2 :=
  by decide

private theorem zo4_minus4Coord_surj (c : CFSG.Open.GLAMinusIdx 1 → ZMod 2) :
    ∃ k : Fin 16, zo4_minus4Coord k = c := by
  obtain ⟨k, hk, hbit⟩ := exists_lt_bitVec_eq (fun j : Fin 4 => c (zo4_minus4IdxInv j))
  refine ⟨⟨k, by simpa using hk⟩, ?_⟩
  funext i
  simp only [zo4_minus4Coord, hbit, zo4_minus4Idx_left]

private theorem zo4_minus4Polar_nondeg (c : CFSG.Open.GLAMinusIdx 1 → ZMod 2) (hc : c ≠ 0) :
    ∃ c', polar zo4_minus4Form c c' = 1 := by
  obtain ⟨k, hk⟩ := zo4_minus4Coord_surj c
  rw [← hk] at hc ⊢
  exact (by decide : ∀ k : Fin 16, zo4_minus4Coord k ≠ 0 →
    ∃ c', polar zo4_minus4Form (zo4_minus4Coord k) c' = 1) k hc

private theorem zo4_minus4Coord_xor (a b : ℕ) :
    zo4_minus4Coord (a ^^^ b) = zo4_minus4Coord a + zo4_minus4Coord b := by
  funext i
  simp only [zo4_minus4Coord, bitVec_xor, Pi.add_apply]

private theorem zo4_a₄_chainOK :
    chainOK (fun a b => a ^^^ b) zo4_a₄Ok (List.ofFn zo4_a₄Codes) zo4_a₄Steps = true := by
  decide

private theorem zo4_a₄_cover : ∀ k : Fin 16, zo4_minus4Form (zo4_minus4Coord k) = 1 →
    ((k : ℕ) ∈ chainLabels (fun a b => a ^^^ b) (List.ofFn zo4_a₄Codes) zo4_a₄Steps) :=
  by decide

theorem exists_coxeterConfig_A₄_reflClass_minus
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (b : Module.Basis (CFSG.Open.GLAMinusIdx 1) (ZMod 2) (Fin (2 * 2) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQMinus 1 (1 : ZMod 2) 1 (b.equivFun v))
    (htop : Subgroup.closure (reflClass Q) = ⊤) :
    ∃ d : Fin 4 → TauCeti.QuadraticMap.orthogonalGroup Q,
      CoxeterConfig (reflClass Q) (CoxeterMatrix.A 4) d ∧
        Subgroup.closure (Set.range d) = ⊤ := by
  have hQ : ∀ v, Q v = zo4_minus4Form (b.equivFun v) :=
    fun v => zo4_Q_of_coord zo4_minus4Form_eq_GLAQMinus hb v
  refine exists_coxeterConfig_of_codes (e := b.equivFun) (q := zo4_minus4Form) hQ ?_
    zo4_minus4Polar_nondeg zo4_minus4Coord_xor zo4_minus4Coord_surj
    zo4_minus4Form_a₄Codes ?_ ?_ zo4_a₄_chainOK zo4_a₄_cover htop
  · intro c c'
    exact zo4_polar_eq_of_coord hQ c c'
  · intro i j
    exact zo4_minus4Polar_a₄Codes (i, j)
  · intro i j
    exact zo4_a₄Codes_distinct (i, j)

theorem exists_totallySingular_plane_of_GLAQPlus_two
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (b : Module.Basis (Fin 2 ⊕ Fin 2) (ZMod 2) (Fin (2 * 2) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) 2 (b.equivFun v)) :
    ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0 := by
  let v : Fin 2 → (Fin (2 * 2) → ZMod 2) := fun i => b (Sum.inl i)
  have hli : LinearIndependent (ZMod 2) v :=
    b.linearIndependent.comp Sum.inl Sum.inl_injective
  have hrange : Set.range v =
      ({b (Sum.inl 0), b (Sum.inl 1)} : Set (Fin (2 * 2) → ZMod 2)) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [v]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [v]⟩
      · exact ⟨1, by simp [v]⟩
  refine ⟨Submodule.span (ZMod 2) (Set.range v), ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · intro w hw
    have hw' : w ∈ Submodule.span (ZMod 2) ({b (Sum.inl 0), b (Sum.inl 1)} : Set _) := by
      rw [← hrange]
      exact hw
    rw [Submodule.mem_span_pair] at hw'
    obtain ⟨a, c, hst⟩ := hw'
    have hzero : ∀ j : Fin 2, (b.equivFun w) (Sum.inr j) = 0 := by
      intro j
      fin_cases j <;> (rw [← hst]; simp)
    simp only [hb w, CFSG.Assembly.largeEvenQPlus_def, Fin.sum_univ_two, hzero 0, hzero 1,
      mul_zero, add_zero]

end CFSG.StandardType.ZS
