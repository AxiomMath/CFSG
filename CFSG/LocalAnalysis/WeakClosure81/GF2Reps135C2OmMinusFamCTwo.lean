module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy
public import CFSG.LieType.Universal.Spin.Twisted.Short
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFClass
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFNW
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFVanish
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeylEx
import CFSG.LieType.Universal.Spin.Twisted.ShortAction
import CFSG.LieType.Universal.Spin.Twisted.Generation
import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.RankThree.OrthogonalInvolutions

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private def w135c2_omfMC2_sign (n : ℕ) : Fin (n - 1) → ℤ :=
  fun a => if n ≤ a.val + 3 then -1 else 1

private theorem w135c2_omfMC2_sign_isSign (n : ℕ) : SpIsSign (w135c2_omfMC2_sign n) := by
  intro a
  unfold w135c2_omfMC2_sign
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem w135c2_omfMC2_sign_card (n : ℕ) (hn : 4 ≤ n) :
    (Finset.univ.filter fun a : Fin (n - 1) => w135c2_omfMC2_sign n a = -1).card = 2 := by
  rw [Finset.card_eq_two]
  refine ⟨⟨n - 3, by omega⟩, ⟨n - 2, by omega⟩, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  · ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    unfold w135c2_omfMC2_sign
    constructor
    · intro h
      by_cases h' : n ≤ a.val + 3
      · have := a.isLt
        have hd : a.val = n - 3 ∨ a.val = n - 2 := by omega
        rcases hd with hd | hd
        · left; exact Fin.ext hd
        · right; exact Fin.ext hd
      · exfalso
        simp [h'] at h
    · rintro (rfl | rfl)
      · rw [if_pos (show n ≤ (n : ℕ) - 3 + 3 by omega)]
      · rw [if_pos (show n ≤ (n : ℕ) - 2 + 3 by omega)]

private theorem w135c2_omfMC2_card_sum {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    (Finset.univ.filter fun x : Fin m ⊕ Fin m => p (Sum.elim id id x)).card =
      2 * (Finset.univ.filter p).card := by
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
  rw [two_mul]
  congr 1

private theorem w135c2_omfMC2_support_card (n : ℕ) (hn : 4 ≤ n) :
    (spMonoPerm (1 : Equiv.Perm (Fin (n - 1))) (w135c2_omfMC2_sign n)).support.card = 4 := by
  have hmoved : (spMonoPerm (1 : Equiv.Perm (Fin (n - 1))) (w135c2_omfMC2_sign n)).support =
      Finset.univ.filter fun x : Fin (n - 1) ⊕ Fin (n - 1) =>
        w135c2_omfMC2_sign n (Sum.elim id id x) ≠ 1 := by
    ext x
    rw [Equiv.Perm.mem_support]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases x with a | a
    · rw [spMonoPerm_inl]
      by_cases h : w135c2_omfMC2_sign n a = 1
      · simp [h]
      · simp [h]
    · rw [spMonoPerm_inr]
      by_cases h : w135c2_omfMC2_sign n a = 1
      · simp [h]
      · simp [h]
  rw [hmoved]
  rw [w135c2_omfMC2_card_sum (p := fun a => w135c2_omfMC2_sign n a ≠ 1)]
  have hcompl : (Finset.univ.filter fun a : Fin (n - 1) =>
      ¬ (w135c2_omfMC2_sign n a = 1)).card =
      (Finset.univ.filter fun a : Fin (n - 1) => w135c2_omfMC2_sign n a = -1).card := by
    refine congrArg Finset.card (Finset.filter_congr fun a _ => ?_)
    rcases w135c2_omfMC2_sign_isSign n a with h | h <;> simp [h]
  rw [hcompl, w135c2_omfMC2_sign_card n hn]

private theorem w135c2_omfMC2_sign_prod (n : ℕ) (hn : 4 ≤ n) :
    ∏ a, w135c2_omfMC2_sign n a = 1 := by
  have hs := w135c2_omfMC2_sign_isSign n
  have h1 : ∏ a, w135c2_omfMC2_sign n a =
      ∏ a : Fin (n - 1), (if w135c2_omfMC2_sign n a = -1 then (-1 : ℤ) else 1) := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rcases hs a with h | h <;> simp [h]
  rw [h1, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    w135c2_omfMC2_sign_card n hn]
  norm_num

private theorem w135c2_omfMC2_spMonoPerm_mul_self (n : ℕ) :
    spMonoPerm (1 : Equiv.Perm (Fin (n - 1))) (w135c2_omfMC2_sign n) *
      spMonoPerm 1 (w135c2_omfMC2_sign n) = 1 := by
  have hs := w135c2_omfMC2_sign_isSign n
  have h1 := spMonoPerm_mul (π₁ := (1 : Equiv.Perm (Fin (n - 1)))) (π₂ := 1) hs hs
  rw [← h1, mul_one]
  have h2 : (fun c : Fin (n - 1) =>
      w135c2_omfMC2_sign n c * w135c2_omfMC2_sign n ((1 : Equiv.Perm (Fin (n - 1))) c)) = 1 := by
    funext c
    simp only [Equiv.Perm.one_apply, Pi.one_apply]
    exact hs.mul_self c
  rw [h2, spMonoPerm_one]

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMC2_linearIndependent {n : ℕ} (i : Fin (n - 1)) :
    LinearIndependent K ![(eVec n i : Vm n K), (planeVec n planeOne : Vm n K)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  constructor
  · have h := congrFun hst (Sum.inl i)
    have h1 : (eVec n i : Vm n K) (Sum.inl i) = (1 : K) := by simp [eVec]
    have h2 : (planeVec n planeOne : Vm n K) (Sum.inl i) = (0 : K) := by simp [planeVec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [h1, h2, mul_zero, add_zero, mul_one] at h
    exact h
  · have h := congrFun hst (Sum.inr (Sum.inr (0 : Fin 2)))
    have h1 : (eVec n i : Vm n K) (Sum.inr (Sum.inr (0 : Fin 2))) = (0 : K) := by
      simp [eVec]
    have h2 : (planeVec n planeOne : Vm n K) (Sum.inr (Sum.inr (0 : Fin 2))) = (1 : K) := by
      simp [planeVec, planeOne]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [h1, h2, mul_zero, zero_add, mul_one] at h
    exact h

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMC2_spinAction_shortPosHom_eq_eichler {n : ℕ}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) :
    spinAction (quadMinus n K b c) (shortPosHom n hirrQ i (Multiplicative.ofAdd planeOne)) =
      CFSG.ClassicalGroups.Orthogonal.eichler (quadMinus n K b c) (eVec n i)
        (planeVec n planeOne) := by
  rw [← twShortRoot_true n hirrQ i, spinAction_twShortRoot_eq_eichler, minusVec_true]

omit [Finite K] in
private theorem w135c2_omfMC2_shortPosHom_mul_self {n : ℕ}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) (p : Fin 2 → K) :
    shortPosHom n hirrQ i (Multiplicative.ofAdd p) *
      shortPosHom n hirrQ i (Multiplicative.ofAdd p) = 1 := by
  have hp : Multiplicative.ofAdd p * Multiplicative.ofAdd p = 1 := by
    rw [← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero]
  rw [← map_mul, hp, map_one]

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMC2_shortPosHom_ne_one {n : ℕ}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) :
    shortPosHom n hirrQ i (Multiplicative.ofAdd (planeOne : Fin 2 → K)) ≠ 1 := by
  intro h
  have h1 : Multiplicative.ofAdd (planeOne : Fin 2 → K) = 1 :=
    shortPosHom_injective n hirrQ i (by rw [h, map_one])
  exact planeOne_ne_zero ((ofAdd_eq_one).mp h1)

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMC2_eichler_fVec {n : ℕ} (i : Fin (n - 1)) :
    CFSG.ClassicalGroups.Orthogonal.eichler (quadMinus n K b c) (eVec n i) (planeVec n planeOne)
        (fVec n i) = fVec n i + planeVec n planeOne - eVec n i := by
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply (quadMinus_eVec n b c i)
    (polar_eVec_planeVec n b c i planeOne)]
  simp [polar_fVec_eVec, polar_fVec_planeVec, quadMinus_planeVec', planeNorm_planeOne]

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMC2_eichler_Q_ne_zero {n : ℕ} (i : Fin (n - 1)) :
    quadMinus n K b c
      (CFSG.ClassicalGroups.Orthogonal.eichler (quadMinus n K b c) (eVec n i)
        (planeVec n planeOne) (fVec n i) - fVec n i) ≠ 0 := by
  rw [w135c2_omfMC2_eichler_fVec i]
  have hx : ((fVec n i : Vm n K) + planeVec n planeOne - eVec n i) - fVec n i =
      planeVec n planeOne - eVec n i := by
    ext j
    simp only [Pi.sub_apply, Pi.add_apply]
    abel
  rw [hx]
  have hQ : quadMinus n K b c (planeVec n planeOne - eVec n i) = 1 := by
    rw [sub_eq_add_neg, QuadraticMap.map_add (quadMinus n K b c), QuadraticMap.map_neg,
      quadMinus_planeVec', quadMinus_eVec, QuadraticMap.polar_neg_right, polar_planeVec_eVec,
      planeNorm_planeOne]
    ring
  rw [hQ]; norm_num

theorem suzukiLetter_nW_negLastTwo {n : ℕ} (hn : 4 ≤ n) (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group}
    (hxr : omqnfRealizes (n - 1) x 1 (fun a => if n ≤ a.val + 3 then -1 else 1)) :
    orderOf (spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirrQ).nW x)) = 2 ∧
      suzukiLetter (quadMinus n K b c)
          (spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirrQ).nW x)) = .c ∧
      Module.finrank K (commSpace
          (spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirrQ).nW x))) = 2 := by
  have hs : SpIsSign (w135c2_omfMC2_sign n) := w135c2_omfMC2_sign_isSign n
  have hxr' : omqnfRealizes (n - 1) x 1 (w135c2_omfMC2_sign n) := hxr
  have hacts := omqnf_spinAction_nW hn hirrQ hxr' hs
  set T := spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirrQ).nW x) with hT
  have hσ := w135c2_omfMC2_spMonoPerm_mul_self n
  have hTT : T * T = 1 := hacts.mul_self_eq_one hσ
  have ha0 : w135c2_omfMC2_sign n ⟨n - 3, by omega⟩ = -1 := by
    unfold w135c2_omfMC2_sign
    rw [if_pos (by omega : n ≤ (n : ℕ) - 3 + 3)]
  have hrk : Module.finrank K (commSpace T) = 2 := by
    rw [omqnf_finrank_commSpace hirrQ hacts hσ, w135c2_omfMC2_support_card n hn,
      w135c2_omfMC2_sign_prod n hn]
    norm_num
  have hT1 : T ≠ 1 := by
    intro h
    obtain ⟨x0, hx0, hQ⟩ := omqnf_nonvanish_of_flip (n := n) (a := ⟨n - 3, by omega⟩) ha0 hacts
    have hbot : commSpace (1 : Vm n K ≃ₗ[K] Vm n K) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
      simp
    rw [h, hbot, Submodule.mem_bot] at hx0
    exact hQ (by rw [hx0, QuadraticMap.map_zero])
  have hletter : suzukiLetter (quadMinus n K b c) T = .c := by
    obtain ⟨x0, hx0, hQ⟩ := omqnf_nonvanish_of_flip (n := n) (a := ⟨n - 3, by omega⟩) ha0 hacts
    exact suzukiLetter_eq_c_iff.mpr ⟨by rw [hrk]; decide, x0, hx0, hQ⟩
  exact ⟨orderOf_eq_prime (by rw [pow_two]; exact hTT) hT1, hletter, hrk⟩

theorem suzukiLetter_shortPosHom_planeOne {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    orderOf (spinAction (quadMinus n K b c)
        (shortPosHom n hirrQ ⟨n - 2, by omega⟩ (Multiplicative.ofAdd planeOne))) = 2 ∧
      suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c)
        (shortPosHom n hirrQ ⟨n - 2, by omega⟩ (Multiplicative.ofAdd planeOne))) = .c ∧
      Module.finrank K (commSpace (spinAction (quadMinus n K b c)
        (shortPosHom n hirrQ ⟨n - 2, by omega⟩ (Multiplicative.ofAdd planeOne)))) = 2 := by
  let i : Fin (n - 1) := ⟨n - 2, by omega⟩
  set T := spinAction (quadMinus n K b c)
    (shortPosHom n hirrQ i (Multiplicative.ofAdd planeOne)) with hT
  have hTT : T * T = 1 := by
    rw [← map_mul, w135c2_omfMC2_shortPosHom_mul_self hirrQ i planeOne, map_one]
  have hT1 : T ≠ 1 := by
    rw [hT]
    intro h
    exact w135c2_omfMC2_shortPosHom_ne_one hirrQ i
      (CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ (by rw [h, map_one]))
  have hT2 : orderOf T = 2 := orderOf_eq_prime (by rw [pow_two]; exact hTT) hT1
  have hQnd := nondegenerate_polarBilin_quadMinus_of_finite n K hirrQ
  have hli := w135c2_omfMC2_linearIndependent (K := K) i
  have hcomm : commSpace T = Submodule.span K {eVec n i, planeVec n planeOne} := by
    rw [hT, w135c2_omfMC2_spinAction_shortPosHom_eq_eichler hirrQ i]
    exact le_antisymm
      (CFSG.ClassicalGroups.Orthogonal.commSpace_eichler_le_span (eVec n i) (planeVec n planeOne))
      (CFSG.ClassicalGroups.Orthogonal.span_le_commSpace_eichler (Q := quadMinus n K b c) hQnd
        (quadMinus_eVec n b c i) (polar_eVec_planeVec n b c i planeOne) hli)
  have hrk : Module.finrank K (commSpace T) = 2 := by
    rw [hcomm]
    have h := finrank_span_eq_card hli
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Fintype.card_fin] at h
    exact h
  have hQne : quadMinus n K b c (T (fVec n i) - fVec n i) ≠ 0 := by
    rw [hT, w135c2_omfMC2_spinAction_shortPosHom_eq_eichler hirrQ i]
    exact w135c2_omfMC2_eichler_Q_ne_zero i
  exact ⟨hT2, suzukiLetter_eq_c_iff.mpr ⟨by rw [hrk]; decide,
    ⟨T (fVec n i) - fVec n i, sub_mem_commSpace T _, hQne⟩⟩, hrk⟩

theorem exists_conj_shortPosHom_planeOne_eq_nW {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (g : spinGroup (quadMinus n K b c))
      (x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group),
      omqnfRealizes (n - 1) x 1 (fun a => if n ≤ a.val + 3 then -1 else 1) ∧
      g * shortPosHom n hirrQ ⟨n - 2, by omega⟩ (Multiplicative.ofAdd planeOne) * g⁻¹ =
        (SmallO8mCurtis.curtisDatum n hn hirrQ).nW x := by
  let i : Fin (n - 1) := ⟨n - 2, by omega⟩
  set y := shortPosHom n hirrQ i (Multiplicative.ofAdd planeOne) with hy
  have hs : SpIsSign (w135c2_omfMC2_sign n) := w135c2_omfMC2_sign_isSign n
  obtain ⟨x, hx⟩ := exists_omqnfRealizes_of_signedPerm (m := n - 1) 1 hs
  have hx' : omqnfRealizes (n - 1) x 1 (fun a => if n ≤ a.val + 3 then -1 else 1) := hx
  set T := spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirrQ).nW x) with hT
  have h1 := suzukiLetter_nW_negLastTwo hn hirrQ hx'
  have h2 := suzukiLetter_shortPosHom_planeOne hn hirrQ
  have hyy : y * y = 1 := w135c2_omfMC2_shortPosHom_mul_self hirrQ i planeOne
  have hy1 : y ≠ 1 := w135c2_omfMC2_shortPosHom_ne_one hirrQ i
  have hTO : T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    exact map_spinAction (quadMinus n K b c) _ v
  obtain ⟨g, hg⟩ := omqnf_exists_conj_of_spinAction_eq hn hirrQ hyy hy1 hTO h1.1
    (h1.2.1.trans h2.2.1.symm) (h1.2.2.trans h2.2.2.symm)
    (fun h => by rw [h2.2.1] at h; exact absurd h.1 (by decide))
    (z := (SmallO8mCurtis.curtisDatum n hn hirrQ).nW x) rfl
  exact ⟨g, x, hx, hg⟩

end CFSG.LocalAnalysis.WeakClosure81
