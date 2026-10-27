module

public import CFSG.LocalAnalysis.StandardType.GGE6NegativeLift
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralCyclic
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralClauses
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralEmbed
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourToral
public import CFSG.LocalAnalysis.StandardType.GGTwE6HyperplaneTypes
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial
public import Mathlib.Tactic.IntervalCases

public noncomputable section

namespace CFSG.StandardType.E6NegativeCyclic

open Subgroup CFSG.StandardType.E6NonToralThree CFSG.StandardType.TableBExc.Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.TwE6HyperplaneTypes

private instance : NeZero Tag.E6.rank := ⟨by decide⟩

theorem conj_eq_cE6_of_word_cases
    (v : Fin 3 → ZMod 3) (j : ZMod 3)
    (h : ∀ i : Fin Tag.E6.rank,
      CFSG.StandardType.TableBExc.wordAct .E6
        (CFSG.StandardType.TwE6HyperplaneTypes.conjWordE6 v j ++
          CFSG.StandardType.TwE6HyperplaneTypes.modelWordE6 v j) (Pi.single i 1) =
      CFSG.StandardType.TableBExc.wordAct .E6
        (wordE6C ++ CFSG.StandardType.TwE6HyperplaneTypes.conjWordE6 v j) (Pi.single i 1)) :
    (coxeterSystem .E6).wordProd (CFSG.StandardType.TwE6HyperplaneTypes.conjWordE6 v j) *
      (coxeterSystem .E6).wordProd (CFSG.StandardType.TwE6HyperplaneTypes.modelWordE6 v j) =
      cE6 * (coxeterSystem .E6).wordProd
        (CFSG.StandardType.TwE6HyperplaneTypes.conjWordE6 v j) := by
  apply CFSG.LieType.Chevalley.ext_single
  intro i
  change _ = ((coxeterSystem .E6).wordProd wordE6C * _) • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)
  rw [← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append]
  simpa only [CFSG.StandardType.TableBExc.wordProd_smul] using h i

theorem model_weyl_cases (y : CFSG.StandardType.TableBExc.Three.Model piE7 piE7_pow_three)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hyg : ∀ i, modelHomE6 y ≠ gE6 i)
    (hygi : ∀ i, modelHomE6 y ≠ (gE6 i)⁻¹) :
    (∃ v : Multiplicative (Fin 3 → ZMod 3), (∀ i, v.toAdd i ≠ 0) ∧
      modelHomE6 y = modelHomE6 (SemidirectProduct.inl v)) ∨
    ∃ u : WeylGroup .E6, u * modelHomE6 y = cE6 * u := by
  let v := y.left.toAdd
  let j := y.right.toAdd
  have hvec : (⟨Multiplicative.ofAdd v, Multiplicative.ofAdd j⟩ :
      CFSG.StandardType.TableBExc.Three.Model piE7 piE7_pow_three) = y := by
    cases y with
    | mk l r => cases l; cases r; rfl
  have hword := CFSG.StandardType.TwE6HyperplaneTypes.modelHomE6_eq_wordProd y
  have hcond : j = 0 ∨ v 0 + v 1 + v 2 = 0 := by
    by_contra hn
    obtain ⟨i,hi⟩ := CFSG.StandardType.TwE6HyperplaneTypes.modelElt_cube_ne v j hn
    have hc : (coxeterSystem .E6).wordProd
        (List.replicate 3 (CFSG.StandardType.TwE6HyperplaneTypes.modelWordE6 v j)).flatten = 1 := by
      rw [CFSG.StandardType.TableBExc.wordProd_replicate]
      change ((coxeterSystem .E6).wordProd
        (CFSG.StandardType.TwE6HyperplaneTypes.modelWordE6 y.left.toAdd y.right.toAdd)) ^ 3 = 1
      rw [← hword, ← map_pow, hy3, map_one]
    apply hi
    rw [← CFSG.StandardType.TableBExc.wordProd_smul, hc, one_smul]
  have hne : ¬ (v = 0 ∧ j = 0) := by
    rintro ⟨hv,hj⟩
    apply hy1
    rw [← hvec,hv,hj]
    rfl
  have hex : ∀ i : Fin 3, ¬ (j = 0 ∧ (v = Pi.single i 1 ∨ v = Pi.single i 2)) := by
    intro i
    rintro ⟨hj,hv⟩
    rcases hv with hv | hv
    · apply hyg i
      rw [← hvec,hj,hv]
      exact E6NonToralThree.modelHomE6_inl_single_one i
    · apply hygi i
      rw [← hvec,hj,hv]
      exact E6NonToralThree.modelHomE6_inl_single_two i
  rcases CFSG.StandardType.TwE6HyperplaneTypes.modelElt_cases v j hcond hne hex with hfp | hc
  · refine Or.inl ⟨Multiplicative.ofAdd v,hfp.2,?_⟩
    rw [← hvec,hfp.1]
    rfl
  · refine Or.inr ⟨(coxeterSystem .E6).wordProd
      (CFSG.StandardType.TwE6HyperplaneTypes.conjWordE6 v j),?_⟩
    rw [hword]
    exact conj_eq_cE6_of_word_cases v j hc

theorem no_gE6_of_mem_zpowers_cE6 {w : WeylGroup .E6}
    (hw : w ∈ Subgroup.zpowers cE6) (i : Fin 3) : w ≠ gE6 i := by
  let x : Fin Tag.E6.rank → ℤ := Pi.single 3 1
  have hfix : cE6 • x = x := by
    rw [CFSG.StandardType.TwE6HyperplaneTypes.cE6_smul]
    decide +kernel
  have hmove : gE6 i • x ≠ x := by
    rw [gE6,CFSG.StandardType.TableBExc.wordProd_smul]
    fin_cases i <;> decide +kernel
  have hs : cE6 ∈ MulAction.stabilizer (WeylGroup .E6) x := hfix
  have hwfix : w • x = x :=
    MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hs) hw)
  intro h
  exact hmove (h ▸ hwfix)

theorem zpowers_cE6_le_model : Subgroup.zpowers cE6 ≤ modelHomE6.range := by
  apply Subgroup.zpowers_le.mpr
  refine ⟨⟨Multiplicative.ofAdd 0, Multiplicative.ofAdd 1⟩,?_⟩
  rw [CFSG.StandardType.TwE6HyperplaneTypes.modelHomE6_eq_wordProd]
  rfl


private def cShift : Fin Tag.E6.rank → ℤ := ![-2,-1,-2,-2,-1,0]

private theorem shift_cE6 : e6Shift cE6 = cShift := by
  apply e6Shift_eq_of_three_smul
  rw [cE6_smul]
  decide +kernel

private theorem shift_cE6_dot : dotZ3 (e6Shift cE6) (basisC 0) = 1 := by
  rw [shift_cE6]
  decide +kernel

private theorem shift_cE6_sq_dot : dotZ3 (e6Shift (cE6 ^ 2)) (basisC 0) = 2 := by
  rw [pow_two, e6Shift_mul, shift_cE6, cE6_smul]
  decide +kernel

theorem eq_one_of_mem_zpowers_cE6_of_shift_eq_one
    {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {w : WeylGroup .E6} (hw : w ∈ Subgroup.zpowers cE6)
    (hsh : rootChar (zetaVec ζ hζ (basisC 0)) (e6Shift w) = 1) : w = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hd : dotZ3 (e6Shift (cE6 ^ m)) (basisC 0) = 0 := by
    rw [CFSG.StandardType.NoOffE8Five.rootChar_zetaVec] at hsh
    have h1 : Multiplicative.ofAdd (∑ j,
        ((e6Shift (cE6 ^ m) j : ℤ) : ZMod 3) * basisC 0 j) = 1 :=
      (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ) (by rw [hsh, map_one])
    simpa [dotZ3] using congrArg Multiplicative.toAdd h1
  have hp := zpow_eq_zpow_emod' m cE6_pow_three
  rw [hp] at hd
  have hlo : 0 ≤ m % 3 := Int.emod_nonneg m (by decide)
  have hhi : m % 3 < 3 := Int.emod_lt_of_pos m (by decide)
  generalize hr : m % 3 = r at *
  interval_cases r
  · rw [hp, zpow_zero]
  · simp only [zpow_one, shift_cE6_dot] at hd
    exact False.elim ((by decide : (1 : ZMod 3) ≠ 0) hd)
  · simp only [zpow_ofNat, shift_cE6_sq_dot] at hd
    exact False.elim ((by decide : (2 : ZMod 3) ≠ 0) hd)

private def beta : Fin 6 → ZMod 3 := ![-1, -1, -1, -1, 0, 0]

private def y1 : Fin 6 → ZMod 9 := ![0, 0, 0, 1, 3, 0]

private def y2 : Fin 6 → ZMod 9 := ![0, 0, 0, 2, 0, 0]

private def kerVec (a1 a2 : ZMod 3) : Fin 6 → ZMod 3 :=
  combC ![a1 - a2, a1, a2]

private def preY (a1 a2 : ZMod 3) : Fin 6 → ZMod 9 :=
  fun j => (a1.val : ZMod 9) * y1 j + (a2.val : ZMod 9) * y2 j

private theorem beta_kerVec :
    ∀ a1 a2 : ZMod 3, (∑ i, beta i * kerVec a1 a2 i) = 0 := by
  decide +kernel

private def lift3 (z : ZMod 3) : ZMod 9 := (z.val : ZMod 9)

private theorem norm_preimage_combC_adWord :
    ∀ (a1 a2 : ZMod 3) (j : Fin Tag.E6.rank),
      (preY a1 a2 j + adWord .E6 9 wordE6C (preY a1 a2) j +
        adWord .E6 9 wordE6C (adWord .E6 9 wordE6C (preY a1 a2)) j) =
      3 * lift3 (kerVec a1 a2 j) := by
  decide +kernel

private theorem norm_preimage_combC_adAct :
    ∀ (a1 a2 : ZMod 3) (j : Fin Tag.E6.rank),
      (preY a1 a2 j +
        adAct .E6 9 CFSG.StandardType.TableBExc.E6Three.cE6 (preY a1 a2) j +
        adAct .E6 9 CFSG.StandardType.TableBExc.E6Three.cE6
          (adAct .E6 9 CFSG.StandardType.TableBExc.E6Three.cE6 (preY a1 a2)) j) =
      3 * lift3 (kerVec a1 a2 j) := by
  have hA : ∀ z : Fin Tag.E6.rank → ZMod 9,
      adAct .E6 9 CFSG.StandardType.TableBExc.E6Three.cE6 z =
        adWord .E6 9 wordE6C z := by
    intro z
    change adAct .E6 9 ((coxeterSystem .E6).wordProd wordE6C) z =
      adWord .E6 9 wordE6C z
    exact (adWord_eq_adAct (τ := .E6) (p := 9) (ω := wordE6C) (x := z)).symm
  intro a1 a2 j
  rw [hA (preY a1 a2), hA (adWord .E6 9 wordE6C (preY a1 a2))]
  exact norm_preimage_combC_adWord a1 a2 j


private theorem beta_combC_eq_zero_iff :
    ∀ a : Fin 3 → ZMod 3,
      (∑ i, beta i * combC a i = 0) ↔ a 0 = a 1 - a 2 := by
  decide +kernel

private theorem exists_norm_preimage_of_fixed_beta
    (x : Fin Tag.E6.rank → ZMod 3)
    (hfix : adAct .E6 3 CFSG.StandardType.TableBExc.E6Three.cE6 x = x)
    (hbeta : ∑ i, beta i * x i = 0) :
    ∃ y : Fin Tag.E6.rank → ZMod 9,
      ∀ j : Fin Tag.E6.rank,
        y j +
          adAct .E6 9 CFSG.StandardType.TableBExc.E6Three.cE6 y j +
          adAct .E6 9 CFSG.StandardType.TableBExc.E6Three.cE6
            (adAct .E6 9 CFSG.StandardType.TableBExc.E6Three.cE6 y) j =
        3 * lift3 (x j) := by
  have hA3 : ∀ z : Fin Tag.E6.rank → ZMod 3,
      adAct .E6 3 CFSG.StandardType.TableBExc.E6Three.cE6 z =
        adWord .E6 3 wordE6C z := by
    intro z
    change adAct .E6 3 ((coxeterSystem .E6).wordProd wordE6C) z =
      adWord .E6 3 wordE6C z
    exact (adWord_eq_adAct (τ := .E6) (p := 3) (ω := wordE6C) (x := z)).symm
  have hfixW : adWord .E6 3 wordE6C x = x := by
    rw [← hA3 x]
    exact hfix
  obtain ⟨a, rfl⟩ := exists_combC_of_adWord x hfixW
  have ha0 : a 0 = a 1 - a 2 := (beta_combC_eq_zero_iff a).mp hbeta
  refine ⟨preY (a 1) (a 2), ?_⟩
  have hcomb : combC a = kerVec (a 1) (a 2) := by
    have ha : a = ![a 1 - a 2, a 1, a 2] := by
      funext i
      fin_cases i <;> simp [ha0]
    rw [ha]
    rfl
  intro j
  rw [hcomb]
  exact norm_preimage_combC_adAct (a 1) (a 2) j

private theorem triple_lift_val (z : ZMod 3) :
    ((3 : ZMod 9) * (z.val : ZMod 9)).val = 3 * z.val := by
  revert z
  decide +kernel

private theorem zetaVec_triple_lift {L : Type} [Field L] (η : Lˣ) (hη9 : η ^ 9 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) :
    zetaVec η hη9 (fun i => (3 : ZMod 9) * (x i).val) =
      zetaVec (η ^ 3) (by rw [← pow_mul]; exact hη9) x := by
  funext i
  rw [zetaVec_apply, zetaVec_apply, triple_lift_val, pow_mul]

private theorem exists_torus_norm_of_fixed_beta
    {L : Type} [Field L] [IsAlgClosed L] (n : ModGL .E6 L) (hnM : n ∈ monomialSubgroup .E6 L)
    (hnw : weylQuotientHom .E6 L ⟨n, hnM⟩ = cE6)
    (η : Lˣ) (hη9 : η ^ 9 = 1) (x : Fin Tag.E6.rank → ZMod 3)
    (hfix : adAct .E6 3 cE6 x = x) (hbeta : ∑ i, beta i * x i = 0) :
    ∃ s ∈ torusGroup .E6 L,
      s * (n * s * n⁻¹) * (n ^ 2 * s * (n ^ 2)⁻¹) =
        rootDiagUnit .E6 (zetaVec (η ^ 3) (by rw [← pow_mul]; exact hη9) x) := by
  obtain ⟨y, hy⟩ := exists_norm_preimage_of_fixed_beta x hfix hbeta
  let s := rootDiagUnit .E6 (zetaVec η hη9 y)
  have hconj (v : Fin Tag.E6.rank → ZMod 9) :
      n * rootDiagUnit .E6 (zetaVec η hη9 v) * n⁻¹ =
        rootDiagUnit .E6 (zetaVec η hη9 (adAct .E6 9 cE6 v)) := by
    rw [monomial_conj_rootDiagUnit_weylTuple hnM
      (mapsRootLines_weylQuotientHom ⟨n,hnM⟩), weylTuple_zetaVec, hnw]
  have hconj2 : n ^ 2 * s * (n ^ 2)⁻¹ = n * (n * s * n⁻¹) * n⁻¹ := by
    rw [pow_two]
    group
  have hsum : y + adAct .E6 9 cE6 y + adAct .E6 9 cE6 (adAct .E6 9 cE6 y) =
      fun j => (3 : ZMod 9) * (x j).val := by
    funext j
    exact hy j
  refine ⟨s, rootDiagUnit_mem_torusGroup _, ?_⟩
  change s * (n * s * n⁻¹) * (n ^ 2 * s * (n ^ 2)⁻¹) = _
  rw [hconj2]
  dsimp only [s]
  rw [hconj, hconj, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    ← CFSG.StandardType.ExcFrames.zetaVec_add, ← CFSG.StandardType.ExcFrames.zetaVec_add,
    hsum, zetaVec_triple_lift]

private theorem shift_combC_eq_zero_iff :
    ∀ a : Fin 3 → ZMod 3, dotZ3 cShift (combC a) = 0 ↔ a 0 = a 1 - a 2 := by
  decide +kernel

private theorem beta_zero_of_fixed_shift_zero
    (x : Fin Tag.E6.rank → ZMod 3) (hfix : adAct .E6 3 cE6 x = x)
    (hsh : dotZ3 (e6Shift cE6) x = 0) : ∑ i, beta i * x i = 0 := by
  have hw : adWord .E6 3 wordE6C x = x := by
    rw [adWord_eq_adAct]
    change adAct .E6 3 cE6 x = x
    exact hfix
  obtain ⟨a, ha⟩ := exists_combC_of_adWord x hw
  rw [ha, shift_cE6] at hsh
  rw [ha]
  exact (beta_combC_eq_zero_iff a).mpr ((shift_combC_eq_zero_iff a).mp hsh)

theorem exists_torus_norm_of_fixed_shift_zero
    {L : Type} [Field L] [IsAlgClosed L] (n : ModGL .E6 L)
    (hnM : n ∈ monomialSubgroup .E6 L)
    (hnw : weylQuotientHom .E6 L ⟨n, hnM⟩ = cE6)
    (η : Lˣ) (hη9 : η ^ 9 = 1) (x : Fin Tag.E6.rank → ZMod 3)
    (hfix : adAct .E6 3 cE6 x = x) (hsh : dotZ3 (e6Shift cE6) x = 0) :
    ∃ s ∈ torusGroup .E6 L,
      s * (n * s * n⁻¹) * (n ^ 2 * s * (n ^ 2)⁻¹) =
        rootDiagUnit .E6 (zetaVec (η ^ 3) (by rw [← pow_mul]; exact hη9) x) :=
  exists_torus_norm_of_fixed_beta n hnM hnw η hη9 x hfix
    (beta_zero_of_fixed_shift_zero x hfix hsh)

private theorem combC_first_basis : combC ![1,0,0] = basisC 0 := by
  decide +kernel

theorem negative_mem_connected_of_weyl_cE6
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ x (hx : x ∈ E), weylQuotientHom .E6 L ⟨x,hEM hx⟩ ∈ modelHomE6.range)
    (hAg : ∀ x (hx : x ∈ E) i, weylQuotientHom .E6 L ⟨x,hEM hx⟩ ≠ gE6 i)
    (hA : (E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L) =
      Subgroup.zpowers cE6)
    (φ : MulAut E) (hφ : GGIsReflection 3 φ)
    {g : ModGL .E6 L} (hg : g ∈ adjointGroup .E6 L)
    (hact : ∀ x : E, g * (x : ModGL .E6 L) * g⁻¹ = φ x)
    {e : E} (he : φ e = e⁻¹) :
    (e : ModGL .E6 L) ∈ CFSG.LieType.AlgebraicGroups.closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let : Algebra (ZMod 2) L := ZMod.algebra L 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Algebra.IsAlgebraic (ZMod 2) L :=
    CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (k := K)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; decide
  have hEA (w : WeylGroup .E6) : w ∈ Subgroup.zpowers cE6 ↔
      ∃ x, ∃ hx : x ∈ E, weylQuotientHom .E6 L ⟨x,hEM hx⟩ = w := by
    rw [← hA]
    constructor
    · rintro ⟨x,hx,hw⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mp hx, hw⟩
    · rintro ⟨x,hx,rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨x,hEM hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨n, hnE, hnρ⟩ := (hEA cE6).mp (Subgroup.mem_zpowers cE6)
  have hnM := hEM hnE
  have hnW : MapsRootLines n cE6 := by
    have h := mapsRootLines_weylQuotientHom ⟨n,hnM⟩
    rwa [hnρ] at h
  have h3L : (3 : L) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime L Nat.prime_three (by decide)
  obtain ⟨ζ, hζo⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (k := L) (n := 3) h3L
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  let aux := rootDiagUnit .E6 (zetaVec ζ hζ (basisC 0))
  have hauxT : aux ∈ torusGroup .E6 L := rootDiagUnit_mem_torusGroup _
  have hcfix : adAct .E6 3 cE6 (basisC 0) = basisC 0 := by
    have hbase : combC ![1,0,0] = basisC 0 := combC_first_basis
    have h := adWord_combC ![1,0,0]
    rw [hbase, adWord_eq_adAct] at h
    exact h
  have hnaux : n * aux * n⁻¹ = aux := by
    dsimp only [aux]
    rw [monomial_conj_rootDiagUnit_weylTuple hnM hnW, weylTuple_zetaVec, hcfix]
  have hnauxC : Commute n aux := (mul_inv_eq_iff_eq_mul).mp hnaux
  have hauxC (x : ModGL .E6 L) (hx : x ∈ E) : Commute aux x := by
    obtain ⟨t,ht,m,hx⟩ := E6NonToralThree.exists_torusRep_of_weyl_zpowers
      hEM hEA hnE hnρ rfl hx
    have hta : Commute t aux := (triangular_borel_structure.{0,0} .E6 L).1 t ht aux hauxT
    rw [hx]
    exact (hta.mul_left (hnauxC.zpow_left m)).symm
  have haux3 : aux ^ 3 = 1 := by
    have hz3 : (zetaVec ζ hζ (basisC 0)) ^ 3 = 1 := by
      funext i
      simp only [Pi.pow_apply, Pi.one_apply, zetaVec_apply]
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow]
    dsimp only [aux]
    rw [rootDiagUnit_pow, hz3, rootDiagUnit_one]
  have hauxE : aux ∈ E := E6NonToralThree.mem_of_torus_of_commute
    hL hEM hE hcard hET hAS hAg hauxT (fun x hx => (hauxC x hx).eq) haux3
  have decomp (x : ModGL .E6 L) (hx : x ∈ monomialSubgroup .E6 L) :
      ∃ b : Fin Tag.E6.rank → Lˣ, x = rootDiagUnit .E6 b *
        canonicalRep (coxeterSystem .E6) L (weylQuotientHom .E6 L ⟨x,hx⟩) := by
    obtain ⟨w,t,ht,heq⟩ := monomialSubgroup_le_torusWeylCosets hx
    have hw : w = weylQuotientHom .E6 L ⟨x,hx⟩ :=
      (mapsRootLines_mul_canonicalRep ht w).unique (heq ▸ mapsRootLines_weylQuotientHom ⟨x,hx⟩)
    obtain ⟨b,hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    refine ⟨b, ?_⟩
    calc x = t * canonicalRep (coxeterSystem .E6) L w := heq
      _ = rootDiagUnit .E6 b * canonicalRep (coxeterSystem .E6) L w := by rw [hb]
      _ = rootDiagUnit .E6 b * canonicalRep (coxeterSystem .E6) L
        (weylQuotientHom .E6 L ⟨x,hx⟩) := by rw [hw]
  obtain ⟨F,hF,hFfin,κ,ι,_,hEΦ,_,hComm⟩ :=
    exists_finite_e6Sc_lift_centralizing_of_negative_reflection K (algebraMap K L)
      (by decide : (3 : ℕ) ≠ 2) hEG hE φ hφ hg hact he
  let : Field F := hF
  let : Finite F := hFfin
  let Φ := e6ScToBar F ι
  obtain ⟨ue,hue⟩ := hEΦ e.property
  obtain ⟨ua,hua⟩ := hEΦ hauxE
  obtain ⟨un,hun⟩ := hEΦ hnE
  let w := weylQuotientHom .E6 L ⟨(e : ModGL .E6 L),hEM e.property⟩
  obtain ⟨be,heq⟩ := decomp e (hEM e.property)
  change (e : ModGL .E6 L) = rootDiagUnit .E6 be * canonicalRep (coxeterSystem .E6) L w at heq
  have heaux : (e : ModGL .E6 L) * aux * (e : ModGL .E6 L)⁻¹ = aux := by
    rw [(hauxC e e.property).eq.symm, mul_inv_cancel_right]
  have hbaux : Commute (rootDiagUnit .E6 be) aux :=
    (triangular_borel_structure.{0,0} .E6 L).1 _ (rootDiagUnit_mem_torusGroup _) _ hauxT
  have hwaux : canonicalRep (coxeterSystem .E6) L w * aux *
      (canonicalRep (coxeterSystem .E6) L w)⁻¹ = aux := by
    apply (MulAut.conj (rootDiagUnit .E6 be)).injective
    change rootDiagUnit .E6 be *
      (canonicalRep (coxeterSystem .E6) L w * aux *
        (canonicalRep (coxeterSystem .E6) L w)⁻¹) * (rootDiagUnit .E6 be)⁻¹ =
      rootDiagUnit .E6 be * aux * (rootDiagUnit .E6 be)⁻¹
    calc rootDiagUnit .E6 be *
        (canonicalRep (coxeterSystem .E6) L w * aux *
          (canonicalRep (coxeterSystem .E6) L w)⁻¹) * (rootDiagUnit .E6 be)⁻¹ =
          (e : ModGL .E6 L) * aux * (e : ModGL .E6 L)⁻¹ := by rw [heq]; group
      _ = aux := heaux
      _ = rootDiagUnit .E6 be * aux * (rootDiagUnit .E6 be)⁻¹ := by
        rw [hbaux.eq, mul_inv_cancel_right]
  have hwstab : w ∈ rootCharStabilizer (zetaVec ζ hζ (basisC 0)) := by
    apply (conj_canonicalRep_eq_iff _ w).mp
    change aux * canonicalRep (coxeterSystem .E6) L w * aux⁻¹ =
      canonicalRep (coxeterSystem .E6) L w
    have hh := (mul_inv_eq_iff_eq_mul).mp hwaux
    rw [← hh, mul_inv_cancel_right]
  have hshiftw : rootChar (zetaVec ζ hζ (basisC 0)) (e6Shift w) = 1 :=
    rootChar_e6Shift_of_isotropic (K := K) ι (hComm ue ua hue (by rw [hua]; exact hauxE)).symm
      (Subgroup.one_mem _) (Subgroup.one_mem _)
      (by simp only [one_mul, mul_one, inv_one, hua]; rfl)
      (by simp only [mul_one, one_mul])
      (by simpa only [one_mul, mul_one, inv_one, hue] using heq) hwstab
  have hw1 : w = 1 := eq_one_of_mem_zpowers_cE6_of_shift_eq_one hζ hζo
    ((hEA w).mpr ⟨e,e.property,rfl⟩) hshiftw
  have heT : (e : ModGL .E6 L) ∈ torusGroup .E6 L := by
    have hker : (⟨(e : ModGL .E6 L),hEM e.property⟩ : monomialSubgroup .E6 L) ∈
        (weylQuotientHom .E6 L).ker := hw1
    rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2,
      Subgroup.mem_subgroupOf] at hker
    exact hker
  obtain ⟨a,ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup heT
  have ha3 : a ^ 3 = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (K := L)
    rw [← rootDiagUnit_pow, ← ha, rootDiagUnit_one]
    exact hE.2 e e.property
  obtain ⟨v,hv0⟩ := exists_zetaVec_eq hζo hζ ha3
  have hv : (e : ModGL .E6 L) = rootDiagUnit .E6 (zetaVec ζ hζ v) :=
    ha.trans (congrArg (rootDiagUnit .E6) hv0).symm
  have hne : n * (e : ModGL .E6 L) * n⁻¹ = e := by
    rw [CFSG.StandardType.TableB.IsElemAbelian.comm hE hnE e.property, mul_inv_cancel_right]
  have hdiag : rootDiagUnit .E6 (zetaVec ζ hζ (adAct .E6 3 cE6 v)) =
      rootDiagUnit .E6 (zetaVec ζ hζ v) := by
    rw [hv, monomial_conj_rootDiagUnit_weylTuple hnM hnW, weylTuple_zetaVec] at hne
    exact hne
  have hvfix : adAct .E6 3 cE6 v = v := zetaVec_injective hζo hζ
    (CFSG.LieType.Chevalley.rootDiagUnit_injective hdiag)
  obtain ⟨bn,hnq⟩ := decomp n hnM
  rw [hnρ] at hnq
  have hwc : cE6 ∈ rootCharStabilizer (zetaVec ζ hζ v) := by
    apply (conj_canonicalRep_eq_iff _ cE6).mp
    have hh : canonicalRep (coxeterSystem .E6) L cE6 * rootDiagUnit .E6 (zetaVec ζ hζ v) *
        (canonicalRep (coxeterSystem .E6) L cE6)⁻¹ = rootDiagUnit .E6 (zetaVec ζ hζ v) :=
      (canonicalRep_conj_rootDiagUnit cE6 _).trans (by rw [weylTuple_zetaVec]; exact hdiag)
    rw [← (mul_inv_eq_iff_eq_mul).mp hh, mul_inv_cancel_right]
  have hχ : rootChar (zetaVec ζ hζ v) (e6Shift cE6) = 1 :=
    rootChar_e6Shift_of_isotropic (K := K) ι (hComm ue un hue (by rw [hun]; exact hnE))
      (Subgroup.one_mem _) (Subgroup.one_mem _)
      (by simpa only [one_mul, mul_one, inv_one, hue] using hv)
      (by simp only [mul_one, one_mul])
      (by simpa only [one_mul, mul_one, inv_one, hun] using hnq) hwc
  have hvsh : dotZ3 (e6Shift cE6) v = 0 := by
    rw [NoOffE8Five.rootChar_zetaVec] at hχ
    have h : Multiplicative.ofAdd (∑ j, ((e6Shift cE6 j : ℤ) : ZMod 3) * v j) = 1 :=
      (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ) (by rw [hχ, map_one])
    simpa [dotZ3] using congrArg Multiplicative.toAdd h
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (ζ : L) (by decide : 0 < 3)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by decide)] at hz
    exact ζ.ne_zero hz.symm
  let η := Units.mk0 z hz0
  have hηζ : η ^ 3 = ζ := Units.ext (by simpa [η] using hz)
  have hη9 : η ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hηζ, hζ]
  obtain ⟨s,hsT,hsN⟩ := exists_torus_norm_of_fixed_shift_zero n hnM hnρ η hη9 v hvfix hvsh
  have hnormE : s * (n * s * n⁻¹) * (n ^ 2 * s * (n ^ 2)⁻¹) = (e : ModGL .E6 L) := by
    have htup : zetaVec (η ^ 3) (by rw [← pow_mul]; exact hη9) v = zetaVec ζ hζ v := by
      funext i
      rw [zetaVec_apply, zetaVec_apply, hηζ]
    exact hsN.trans ((congrArg (rootDiagUnit .E6) htup).trans hv.symm)
  have hTcomm (x y : torusGroup .E6 L) : x * y = y * x :=
    Subtype.ext ((triangular_borel_structure.{0,0} .E6 L).1 x x.property y y.property)
  have hc := E6NonToralThree.normFun_mem_closedIdentityComponent
    hEM hE hEA hnE hnρ rfl hTcomm (⟨s,hsT⟩ : torusGroup .E6 L)
  have heval : ((E6NonToralThree.normFun
      (E6NonToralThree.normPhi n hnM) ⟨s,hsT⟩ : torusGroup .E6 L) : ModGL .E6 L) =
      s * (n * s * n⁻¹) * (n ^ 2 * s * (n ^ 2)⁻¹) := by
    simp only [E6NonToralThree.normFun, Subgroup.coe_mul, E6NonToralThree.normPhi_apply]
    group
  rw [heval, hnormE] at hc
  exact hc

theorem negative_mem_connected_of_conj_weyl_cE6
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (φ : MulAut E) (hφ : GGIsReflection 3 φ)
    {g : ModGL .E6 L} (hg : g ∈ adjointGroup .E6 L)
    (hact : ∀ x : E, g * (x : ModGL .E6 L) * g⁻¹ = φ x)
    {e : E} (he : φ e = e⁻¹)
    (a : ModGL .E6 L) (ha : a ∈ adjointGroup .E6 L)
    (hEM : E.map (MulAut.conj a).toMonoidHom ≤ monomialSubgroup .E6 L)
    (hET : ¬ E.map (MulAut.conj a).toMonoidHom ≤ torusGroup .E6 L)
    (hAS : ∀ x (hx : x ∈ E.map (MulAut.conj a).toMonoidHom),
      weylQuotientHom .E6 L ⟨x,hEM hx⟩ ∈ modelHomE6.range)
    (hAg : ∀ x (hx : x ∈ E.map (MulAut.conj a).toMonoidHom) i,
      weylQuotientHom .E6 L ⟨x,hEM hx⟩ ≠ gE6 i)
    (hA : ((E.map (MulAut.conj a).toMonoidHom).subgroupOf (monomialSubgroup .E6 L)).map
      (weylQuotientHom .E6 L) = Subgroup.zpowers cE6) :
    (e : ModGL .E6 L) ∈ CFSG.LieType.AlgebraicGroups.closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let f := (MulAut.conj a).toMonoidHom
  let E0 := E.map f
  let γ : E ≃* E0 := Subgroup.equivMapOfInjective E f (MulAut.conj a).injective
  have : Finite E0 := Finite.of_equiv E γ.toEquiv
  have hEG0 : E0 ≤ adjointGroup .E6 L := by
    rintro x ⟨y,hy,rfl⟩
    exact (adjointGroup .E6 L).mul_mem
      ((adjointGroup .E6 L).mul_mem ha (hEG hy)) ((adjointGroup .E6 L).inv_mem ha)
  have hE0 : CFSG.Open.IsElemAbelian 3 E0 := hE.map f
  have hcard0 : Nat.card E0 = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
    exact hcard
  let φ0 := MulAut.congr γ φ
  have hφ0 : GGIsReflection 3 φ0 := (F4AutRefl.ggIsReflection_congr_iff γ φ).mpr hφ
  let g0 := a * g * a⁻¹
  have hg0 : g0 ∈ adjointGroup .E6 L := (adjointGroup .E6 L).mul_mem
    ((adjointGroup .E6 L).mul_mem ha hg) ((adjointGroup .E6 L).inv_mem ha)
  have hact0 (x : E0) : g0 * (x : ModGL .E6 L) * g0⁻¹ = φ0 x := by
    obtain ⟨y,rfl⟩ := γ.surjective x
    have hφγ : φ0 (γ y) = γ (φ y) := by
      change γ (φ (γ.symm (γ y))) = γ (φ y)
      rw [γ.symm_apply_apply]
    rw [hφγ]
    change g0 * (a * (y : ModGL .E6 L) * a⁻¹) * g0⁻¹ =
      a * (φ y : ModGL .E6 L) * a⁻¹
    calc g0 * (a * (y : ModGL .E6 L) * a⁻¹) * g0⁻¹ =
        a * (g * (y : ModGL .E6 L) * g⁻¹) * a⁻¹ := by dsimp only [g0]; group
      _ = a * (φ y : ModGL .E6 L) * a⁻¹ := by rw [hact]
  have he0 : φ0 (γ e) = (γ e)⁻¹ := by
    change γ (φ (γ.symm (γ e))) = (γ e)⁻¹
    rw [γ.symm_apply_apply, he, map_inv]
  have hc := negative_mem_connected_of_weyl_cE6 K hEG0 hEM hE0 hcard0 hET hAS hAg hA
    φ0 hφ0 hg0 hact0 he0
  change f (e : ModGL .E6 L) ∈ CFSG.LieType.AlgebraicGroups.closedIdentityComponent
    (adjointGroup .E6 L ⊓ Subgroup.centralizer (E.map f : Set (ModGL .E6 L))) at hc
  rw [← CFSG.LieType.AlgebraicGroups.map_adjoint_centralizer_conj E ha,
    CFSG.LieType.AlgebraicGroups.closedIdentityComponent_map_conj] at hc
  obtain ⟨x,hx,heq⟩ := Subgroup.mem_map.mp hc
  have hx' : x = (e : ModGL .E6 L) := (MulAut.conj a).injective heq
  exact hx' ▸ hx

theorem centralizer_eq_self_of_weyl_fpf
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEG : E ≤ adjointGroup .E6 L)
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ x (hx : x ∈ E), weylQuotientHom .E6 L ⟨x,hEM hx⟩ ∈ modelHomE6.range)
    (hAg : ∀ x (hx : x ∈ E) i, weylQuotientHom .E6 L ⟨x,hEM hx⟩ ≠ gE6 i)
    {n : ModGL .E6 L} (hnE : n ∈ E)
    {v : Multiplicative (Fin 3 → ZMod 3)} (hv : ∀ i, v.toAdd i ≠ 0)
    (hnv : weylQuotientHom .E6 L ⟨n,hEM hnE⟩ = modelHomE6 (SemidirectProduct.inl v)) :
    adjointGroup .E6 L ⊓ centralizer (E : Set (ModGL .E6 L)) = E := by
  apply le_antisymm
  · intro c hc
    exact E6NonToralThree.mem_of_centralizer_of_weyl_fpf hL hEM hE hcard hET hAS hAg
      hnE hv hnv hc.1 (fun x hx => (Subgroup.mem_centralizer_iff.mp hc.2 x hx).symm)
  · intro e he
    refine ⟨hEG he, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    exact CFSG.StandardType.TableB.IsElemAbelian.comm hE hx he

theorem exists_conj_weyl_eq_zpowers_cE6
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) {a : WeylGroup .E6}
    (hEA : ∀ w, w ∈ Subgroup.zpowers a ↔
      ∃ x, ∃ hx : x ∈ E, weylQuotientHom .E6 L ⟨x,hEM hx⟩ = w)
    {n : ModGL .E6 L} (hnE : n ∈ E)
    (hnw : weylQuotientHom .E6 L ⟨n,hEM hnE⟩ = a)
    (u : WeylGroup .E6) (hua : u * a = cE6 * u) :
    ∃ m ∈ adjointGroup .E6 L,
      ∃ hM : E.map (MulAut.conj m).toMonoidHom ≤ monomialSubgroup .E6 L,
        ((E.map (MulAut.conj m).toMonoidHom).subgroupOf (monomialSubgroup .E6 L)).map
          (weylQuotientHom .E6 L) = Subgroup.zpowers cE6 := by
  classical
  let m := canonicalRep (coxeterSystem .E6) L u
  let f := (MulAut.conj m).toMonoidHom
  let E0 := E.map f
  have hm : m ∈ monomialSubgroup .E6 L := canonicalRep_mem_monomialSubgroup L u
  have hMG : m ∈ adjointGroup .E6 L :=
    canonicalRep_mem_adjointGroup (cs := coxeterSystem .E6) L u
  have hM : E0 ≤ monomialSubgroup .E6 L := by
    rintro x ⟨y,hy,rfl⟩
    exact mul_mem (mul_mem hm (hEM hy)) (inv_mem hm)
  have hπ (x : ModGL .E6 L) (hx : x ∈ E) :
      weylQuotientHom .E6 L ⟨f x,hM (Subgroup.mem_map_of_mem f hx)⟩ =
        u * weylQuotientHom .E6 L ⟨x,hEM hx⟩ * u⁻¹ := by
    change weylQuotientHom .E6 L
      ((⟨m,hm⟩ : monomialSubgroup .E6 L) * ⟨x,hEM hx⟩ * (⟨m,hm⟩ : monomialSubgroup .E6 L)⁻¹) = _
    rw [map_mul,map_mul,map_inv,weylQuotientHom_eq (mapsRootLines_canonicalRep u)]
  have huac : u * a * u⁻¹ = cE6 := by rw [hua,mul_inv_cancel_right]
  refine ⟨m,hMG,hM,?_⟩
  apply le_antisymm
  · rintro w ⟨x,hx,rfl⟩
    obtain ⟨y,hy,heq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    have hxval : x = ⟨f y,hM (Subgroup.mem_map_of_mem f hy)⟩ := Subtype.ext heq.symm
    rw [hxval,hπ y hy]
    obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp ((hEA _).mpr ⟨y,hy,rfl⟩)
    rw [← hk]
    have hp : u * a ^ k * u⁻¹ = (u * a * u⁻¹) ^ k :=
      map_zpow (MulAut.conj u).toMonoidHom a k
    rw [hp,huac]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k,rfl⟩
  · apply Subgroup.zpowers_le.mpr
    let nc : monomialSubgroup .E6 L := ⟨f n,hM (Subgroup.mem_map_of_mem f hnE)⟩
    have hnsub : nc ∈ E0.subgroupOf (monomialSubgroup .E6 L) :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem f hnE)
    have hnc := Subgroup.mem_map_of_mem (weylQuotientHom .E6 L) hnsub
    have hnπ : weylQuotientHom .E6 L ⟨f n,hM (Subgroup.mem_map_of_mem f hnE)⟩ = cE6 := by
      rw [hπ n hnE,hnw,huac]
    rw [← hnπ]
    exact hnc

theorem exists_conj_cE6_or_centralizer_eq_self_of_regular
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEG : E ≤ adjointGroup .E6 L)
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ x (hx : x ∈ E), weylQuotientHom .E6 L ⟨x,hEM hx⟩ ∈ modelHomE6.range)
    (hAg : ∀ x (hx : x ∈ E) i, weylQuotientHom .E6 L ⟨x,hEM hx⟩ ≠ gE6 i) :
    (∃ m ∈ adjointGroup .E6 L,
      ∃ hM : E.map (MulAut.conj m).toMonoidHom ≤ monomialSubgroup .E6 L,
        (∀ x (hx : x ∈ E.map (MulAut.conj m).toMonoidHom),
          weylQuotientHom .E6 L ⟨x,hM hx⟩ ∈ modelHomE6.range) ∧
        (∀ x (hx : x ∈ E.map (MulAut.conj m).toMonoidHom) i,
          weylQuotientHom .E6 L ⟨x,hM hx⟩ ≠ gE6 i) ∧
        ((E.map (MulAut.conj m).toMonoidHom).subgroupOf (monomialSubgroup .E6 L)).map
          (weylQuotientHom .E6 L) = Subgroup.zpowers cE6) ∨
    adjointGroup .E6 L ⊓ centralizer (E : Set (ModGL .E6 L)) = E := by
  classical
  rcases weylImage_card_cases hEM hcard hET with hA3 | hA9
  · obtain ⟨A,hA3,hEA,hAS',hAE,hA1,hAgi,n,hnE,a,hnw,hAeq,ha3,ha1,hag,hagi⟩ :=
      exists_weylGenerator hEM hE hET hAS hAg hA3
    obtain ⟨y,hy⟩ := hAS' ((hEA a).mpr ⟨n,hnE,hnw⟩)
    have hy3 : y ^ 3 = 1 := modelHomE6_injective (by rw [map_pow,hy,ha3,map_one])
    have hy1 : y ≠ 1 := by intro hh; apply ha1; rw [← hy,hh,map_one]
    rcases model_weyl_cases y hy3 hy1 (fun i => by rw [hy]; exact hag i)
      (fun i => by rw [hy]; exact hagi i) with hfp | hc
    · obtain ⟨v,hv,hvπ⟩ := hfp
      have hnπ : weylQuotientHom .E6 L ⟨n,hEM hnE⟩ =
          modelHomE6 (SemidirectProduct.inl v) := hnw.trans (hy.symm.trans hvπ)
      exact Or.inr (centralizer_eq_self_of_weyl_fpf hL hEG hEM hE hcard hET hAS hAg hnE hv hnπ)
    · obtain ⟨u,hu⟩ := hc
      rw [hy] at hu
      have hEA' : ∀ w, w ∈ Subgroup.zpowers a ↔
          ∃ x, ∃ hx : x ∈ E, weylQuotientHom .E6 L ⟨x,hEM hx⟩ = w := by
        rw [← hAeq]; exact hEA
      obtain ⟨m,hm,hM,hAc⟩ := exists_conj_weyl_eq_zpowers_cE6 hEM hEA' hnE hnw u hu
      refine Or.inl ⟨m,hm,hM,?_,?_,hAc⟩
      · intro x hx
        apply zpowers_cE6_le_model
        rw [← hAc]
        exact Subgroup.mem_map.mpr ⟨⟨x,hM hx⟩,Subgroup.mem_subgroupOf.mpr hx,rfl⟩
      · intro x hx i
        apply no_gE6_of_mem_zpowers_cE6 (i := i)
        rw [← hAc]
        exact Subgroup.mem_map.mpr ⟨⟨x,hM hx⟩,Subgroup.mem_subgroupOf.mpr hx,rfl⟩
  · refine Or.inr (le_antisymm ?_ ?_)
    · intro c hc
      exact mem_of_centralizer_of_nine hL hEM hE hcard hET hAS hAg hA9 hc.1
        (fun x hx => (Subgroup.mem_centralizer_iff.mp hc.2 x hx).symm)
    · intro e he
      refine ⟨hEG he,Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro x hx
      exact CFSG.StandardType.TableB.IsElemAbelian.comm hE hx he

theorem exists_conj_cE6_or_centralizer_eq_self
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hNT : ¬ CFSG.StandardType.SCFourCover.E6AdToral E) :
    (∃ a ∈ adjointGroup .E6 L,
      ∃ hM : E.map (MulAut.conj a).toMonoidHom ≤ monomialSubgroup .E6 L,
        (∀ x (hx : x ∈ E.map (MulAut.conj a).toMonoidHom),
          weylQuotientHom .E6 L ⟨x,hM hx⟩ ∈ modelHomE6.range) ∧
        (∀ x (hx : x ∈ E.map (MulAut.conj a).toMonoidHom) i,
          weylQuotientHom .E6 L ⟨x,hM hx⟩ ≠ gE6 i) ∧
        ((E.map (MulAut.conj a).toMonoidHom).subgroupOf (monomialSubgroup .E6 L)).map
          (weylQuotientHom .E6 L) = Subgroup.zpowers cE6) ∨
    adjointGroup .E6 L ⊓ centralizer (E : Set (ModGL .E6 L)) = E := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L :=
    CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (k := K)
  obtain ⟨g,hg,hEM,hreg⟩ := exists_conj_regular (ℓ := 2) (by decide) halg hEG (Set.toFinite (E : Set (ModGL .E6 L))) hE
  let f := (MulAut.conj g).toMonoidHom
  let E0 := E.map f
  have hEG0 : E0 ≤ adjointGroup .E6 L := by
    rintro x ⟨y,hy,rfl⟩
    exact mul_mem (mul_mem hg (hEG hy)) (inv_mem hg)
  have hE0 : IsElemAbelian 3 E0 := hE.map f
  have hcard0 : Nat.card E0 = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have hET0 : ¬ E0 ≤ torusGroup .E6 L := by
    intro ht
    apply hNT
    refine ⟨g,hg,?_⟩
    intro x hx
    exact ht (Subgroup.mem_map_of_mem f hx)
  have hL : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; decide
  rcases exists_conj_cE6_or_centralizer_eq_self_of_regular hL hEG0 hEM hE0 hcard0 hET0
      (fun x hx => (hreg x hx).1) (fun x hx => (hreg x hx).2) with hc | hself
  · obtain ⟨m,hm,hM,hS,hgI,hA⟩ := hc
    have hmap : E0.map (MulAut.conj m).toMonoidHom = E.map (MulAut.conj (m * g)).toMonoidHom := by
      dsimp only [E0,f]
      rw [Subgroup.map_map]
      congr 1
    refine Or.inl ⟨m * g,mul_mem hm hg,?_⟩
    rw [← hmap]
    exact ⟨hM,hS,hgI,hA⟩
  · have hm : (adjointGroup .E6 L ⊓ centralizer (E : Set (ModGL .E6 L))).map f = E.map f := by
      rw [CFSG.LieType.AlgebraicGroups.map_adjoint_centralizer_conj E hg,hself]
    exact Or.inr (Subgroup.map_injective (MulAut.conj g).injective hm)

end CFSG.StandardType.E6NegativeCyclic
