module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourZero
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6Orb

public section

namespace CFSG.StandardType.SpFour

open Module Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCSpIsotypic
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.TwoThree CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6 (solvable_of_card_two_three gu_card_two_three
  not_solvable_of_quasisimple)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem primaryFactor_cases_sp (hK : Nat.card K = 2) {x : StatedSp m K} (hx : x ^ 3 = 1)
    {h : K[X]}
    (hh : h ∈ primaryFactors (spEnd x)) : h = X - 1 ∨ h = SpFin.h3 K := by
  obtain ⟨hirr, hmon, hdvd⟩ := mem_primaryFactors.1 hh
  have hann : aeval (spEnd x) (X ^ 3 - 1 : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
    exact spEnd_pow hx
  have hmin : minpoly K (spEnd x) ∣ X ^ 3 - 1 := minpoly.dvd _ _ hann
  have hdiv : h ∣ (X - 1) * SpFin.h3 K := by
    have : ((X - 1) * SpFin.h3 K : K[X]) = X ^ 3 - 1 := by
      unfold SpFin.h3
      ring
    rw [this]
    exact hdvd.trans hmin
  rcases hirr.prime.dvd_or_dvd hdiv with h1 | h2
  · left
    exact eq_of_monic_of_associated hmon monic_X_sub_one
      (hirr.associated_of_dvd irreducible_X_sub_one h1)
  · right
    exact eq_of_monic_of_associated hmon SpFin.h3_monic
      (hirr.associated_of_dvd (SpFin.h3_irreducible hK) h2)

theorem not_isQuasisimple_commutator_of_solvable {G : Type*} [Group G] {A : Subgroup G}
    (hA : Group.IsSolvable ↥A) : ¬ CFSG.IsQuasisimple ↥⁅A, A⁆ := by
  intro hQ
  have hle : ⁅A, A⁆ ≤ A := Subgroup.commutator_le_self _
  haveI : Group.IsSolvable ↥⁅A, A⁆ :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact not_solvable_of_quasisimple hQ this

theorem fixedFactor_solvable_of_two (hK : Nat.card K = 2) {x : StatedSp m K}
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x))
    (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)) (hd : spFixedDim x = 2) :
    Group.IsSolvable ↥(spSupported x {X - 1}) := by
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm m K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin m ⊕ Fin m → K)
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hB blocks.fixed_nondegenerate
  have hs1 : s = 1 := by
    have h1 : spFixedDim x = finrank K (primaryComponent (spEnd x) (X - 1)) := rfl
    omega
  subst hs1
  have hc : Nat.card (spSupported x {X - 1}) = Nat.card (StatedSp 1 K) :=
    Nat.card_congr (φ.trans e).toEquiv
  rw [SymplecticFlag.card_statedSp, hK] at hc
  exact solvable_of_card_two_three (a := 1) (b := 1) (by rw [hc]; norm_num)

theorem selfDual_solvable_of_le (hK : Nat.card K = 2) {x : StatedSp m K}
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x))
    (hmem : SpFin.h3 K ∈ primaryFactors (spEnd x))
    (hn : primaryMultiplicity (spEnd x) (SpFin.h3 K) ≤ 3)
    (hpos : 1 ≤ primaryMultiplicity (spEnd x) (SpFin.h3 K)) :
    Group.IsSolvable ↥(spSupported x {SpFin.h3 K}) := by
  haveI : Fact (Irreducible (SpFin.h3 K)) := ⟨SpFin.h3_irreducible hK⟩
  obtain ⟨d, hd2, -, -, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
    (blocks.selfDual ⟨SpFin.h3 K, hmem⟩ SpFin.h3_ne_X_sub_one SpFin.h3_reciprocal).exists_half
  have hd1 : d = 1 := by
    have h1 : (SpFin.h3 K).natDegree = 2 * d := hd2
    rw [SpFin.h3_natDegree] at h1
    omega
  subst hd1
  have hcardφ : Nat.card (spSupported x {SpFin.h3 K}) = Nat.card (sesqUnitaryGroup Hf) :=
    Nat.card_congr φ.toEquiv
  have hc := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
    (n := primaryMultiplicity (spEnd x) (SpFin.h3 K)) rfl hpos).1
  obtain ⟨a, b, hab⟩ := gu_card_two_three (G := ↥(sesqUnitaryGroup Hf)) hn hpos rfl hc
  exact solvable_of_card_two_three (a := a) (b := b) (by rw [hcardφ, hab])

theorem not_isComponentOf_of_two (hK : Nat.card K = 2) {x : StatedSp 4 K} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (blocks : SpPrimaryBlocks 2 1 3 x (proj 4 K x)) (hd : spFixedDim x = 2)
    {Q : Subgroup (StatedSp 4 K)}
    (hQ : CFSG.Assembly.IsComponentOf Q (Subgroup.centralizer ({x} : Set _))) : False := by
  classical
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    norm_num at h
  have hsq := (altPrimaryData_spLin hpK hx3).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hfixconj : fixSubgroup (MulAut.conj ((MonoidHom.id (StatedSp 4 K)) x)) =
      Subgroup.centralizer ({x} : Set (StatedSp 4 K)) := by
    ext g
    rw [mem_fixSubgroup, MonoidHom.id_apply, MulAut.conj_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc g * x = (x * g * x⁻¹) * x := by rw [h]
        _ = x * g := by group
    · intro h
      calc x * g * x⁻¹ = (g * x) * x⁻¹ := by rw [h]
        _ = g := by group
  have hQo : CFSG.Open.IsComponentOf Q
      (fixSubgroup (MulAut.conj ((MonoidHom.id (StatedSp 4 K)) x))) := by
    rw [hfixconj]
    exact isComponentOf_iff_open.mp hQ
  obtain ⟨O, hOq, -⟩ := LieComp.components_conj_of_orbit_family (MonoidHom.id (StatedSp 4 K))
    Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le) x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
    hjoin (fun O => LieSemisimple.quasisimple_or_solvable_spSupported (by norm_num)
      (by norm_num : 2 ≤ 2 ^ 1) hsq blocks O) Q hQo
  have hx3' : spLin 4 K x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hsum : finrank K (LinearMap.ker (spEnd x - 1)) +
      finrank K (LinearMap.range (spEnd x - 1)) = 2 * 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl (SpFin.isCompl_fix_rng hx3')
    rw [SpFin.finrank_spSpace 4] at h
    exact h
  have hfix : finrank K (LinearMap.ker (spEnd x - 1)) = spFixedDim x := by
    rw [← blocks.fixed_eq]
    rfl
  obtain ⟨h, hh, hO⟩ := O.2
  have hhm : h ∈ primaryFactors (spEnd x) := hh
  have hO2 : ({h, KCOrthogonal.reciprocalPolynomial h} : Set K[X]) = (O : Set K[X]) := hO
  have hsolv : Group.IsSolvable ↥(spSupported x (O : Set K[X])) := by
    rcases primaryFactor_cases_sp hK hx3 hhm with rfl | rfl
    · have hO' : (O : Set K[X]) = {X - 1} := by
        rw [← hO2, KCOrthogonal.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
      rw [hO']
      exact fixedFactor_solvable_of_two hK blocks hhm hd
    · have hO' : (O : Set K[X]) = {SpFin.h3 K} := by
        rw [← hO2, SpFin.h3_reciprocal, Set.pair_eq_singleton]
      rw [hO']
      haveI : Fact (Irreducible (SpFin.h3 K)) := ⟨SpFin.h3_irreducible hK⟩
      have h1 := finrank_primaryComponent (spEnd x) (SpFin.h3 K)
      rw [SpFin.h3_natDegree] at h1
      have h1' : finrank K (primaryComponent (spEnd x) (SpFin.h3 K)) =
          finrank K (LinearMap.range (spEnd x - 1)) := by
        rw [SpFin.primaryComponent_h3 hK hx3]
      have h2 : primaryMultiplicity (spEnd x) (SpFin.h3 K) =
          finrank (AdjoinRoot (SpFin.h3 K)) (primaryComponent (spEnd x) (SpFin.h3 K)) := rfl
      exact selfDual_solvable_of_le hK blocks hhm (by omega) (by omega)
  exact not_isQuasisimple_commutator_of_solvable hsolv hOq

end CFSG.StandardType.SpFour
