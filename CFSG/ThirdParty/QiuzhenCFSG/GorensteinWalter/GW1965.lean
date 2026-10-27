module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FourPointAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddIndexSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.S4SubgroupClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalCenterlessDihedral
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore -- centralizer_le_of_normal_dihedral (the V4 lemma) for the Prop-9 centralizer proofs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalNormalOddIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeNormalExtension
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenNormalExtension
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGroupExtension
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.GroupTheory.Subgroup.Center

namespace CFSG
end CFSG
open CFSG

/-!
# Gorenstein--Walter (1965): statements needed for Proposition 9 and Lemmas 2.1/2.2

Statements (with `sorry` bodies; no proofs in this file) translated from
Daniel Gorenstein and John H. Walter, *The characterization of finite groups
with dihedral Sylow 2-subgroups*, J. Algebra 2 (1965): Part I pp. 85--151 and
Part II pp. 218--270.  Scope: Part II pp. 218--220 (Proposition 9, its proof
and the following remark), Part I pp. 90--91 (Lemmas 2.1 and 2.2), and Part I
pp. 119--124 (Section 3: Lemmas 3.2(ix) and 3.3(vi), the facts the proof of
Proposition 9 cites).  The transcription is `refs/gorenstein-walter.tex`.

Fidelity-review verdicts (`node_graph/review-gw-fidelity.md`) adopted here:

* Prop 9's citation "Lemmas 3.2 (ix) and 3.3 (vi)" is used — the txt layer is
  definitive and the transcription's "3.2 (i)" is a probable misread (review
  item C1).  The D-group conclusion for the `PSL(2,q)` case is covered by
  3.3(vi) and for the `A₇` case by 3.2(ix).
* The paper's `C'(Z)` notation is used for the normalizer/centralizer
  containment statements (the transcription drops the prime in the remark and
  at p. 220; review Block 1 SHOULD-FIX row): `cPrime Z` below is a set, not
  always a subgroup — the paper notes `C'(Z)` is a subgroup exactly when
  `N(Z) = C'(Z)`.
* The four image-only (NEEDS-USER) items are out of scope here and remain
  open: the p. 220 middle paragraph, the placement of `ε₀` in (2.39), the
  `|C(T₁)|` reading on p. 118, and Lemma 3.1(xi).  Lemma 3.1(iii) (the
  flagged "are S₂-subgroups" reading) is likewise not needed for this scope;
  the review's corrected reading ("`H` contains an S₂-subgroup of `S'`") is
  recorded in `review-gw-fidelity.md`.

Mapping notes:

* The paper's "minimal counterexample to Theorem 1" (Part II, §5: a finite
  group of least order containing a dihedral `S₂`-subgroup and not satisfying
  the conclusion of Theorem 1) is expressed by the repository's
  `IsMinimalCounterexample` (`GorensteinWalter.Classification`), whose
  induction hypothesis is the Bender-style cyclic-or-dihedral form; the cyclic
  part is exactly the Burnside transfer step of Prop 9.  No statement below
  strengthens the paper's conditions silently.
* The paper's "`D`-group" (Part I, p. 118) requires (i) dihedral Sylow
  `2`-subgroups and (ii) `G/O(G)` isomorphic to `A₇` or to a subgroup of
  `PΓL(2,q)` containing `PSL(2,q)`, `q` odd.  The repository's `IsDGroup`
  additionally allows the `2`-group quotient case (Bender's normal-`2`-complement
  clause); where the paper's own condition is needed (so that e.g. a dihedral
  `2`-group is not a "`D`-group"), the new predicate `IsDGroupQuotient` below
  carries the paper's clause (ii) alone.  `PΓL(2,q)` and `PΓL₀(2,q)` are not
  in the repository vocabulary; their occurrences are expressed through the
  `PSL(2,q)`/`PGL(2,q)` normal-subgroup clause, and the paper's "but not
  `PGL(2,q)`" refinement of the remark after Prop 9 is not expressible.
* Theorem 1 (Part I) concludes "`G` is a `D`-group or `G/O(G)` is isomorphic
  to a Sylow `2`-subgroup of `G`"; it does **not** assert `G/O(G) ≅ PSL(2,q)`
  (that is Theorem 2, for simple groups).
* The paper's `Aut(H)` is written `MulAut H` (the repository's group
  automorphism type); `NormalPComplement` is `Glauberman.NormalPComplement`.
* Lemmas 2.3 and 2.4 (Part I, p. 91) appear in the transcription but are not
  needed for `minimalCounterexample_isSimple` and are not translated here.

Modified for CFSG: the two statements of the remark after Proposition 9 are removed. Their
proofs were `sorry` upstream and nothing here uses them.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## Notation introduced for the translation -/

/-- Every Sylow `2`-subgroup is cyclic.  Used for the Burnside transfer step
of Proposition 9 ("the only other possibility is that an `S₂`-subgroup of `H`
is cyclic"). -/
@[expose] public def HasCyclicSylowTwo (G : Type u) [Group G] : Prop :=
  ∀ S : Sylow 2 G, IsCyclic S


/-! ## Proposition 9 (Part II, pp. 218--220): proper subgroups -/

/-- Proposition 9 proof (p. 219): "the subgroups of a dihedral `2`-group are
either cyclic or dihedral `2`-groups." -/
public theorem gw_prop9_subgroups_dihedral_twoGroup_cyclic_or_dihedral
    {m : ℕ} (hm : 1 ≤ m) (H : Subgroup (DihedralGroup (2 ^ m))) :
    IsCyclic H ∨ ∃ k : ℕ, 1 ≤ k ∧ Nonempty (H ≃* DihedralGroup (2 ^ k)) := by
  exact subgroups_dihedral_twoGroup_cyclic_or_dihedral hm H

/-- Proposition 9 proof (p. 219): "Burnside's transfer theorem implies that
`H` has a normal `2`-complement" — a finite group with cyclic Sylow
`2`-subgroups has a normal `2`-complement. -/
public theorem gw_prop9_burnside_cyclicSylowTwo_normalTwoComplement
    {G : Type u} [Group G] [Finite G]
    (hSylow : HasCyclicSylowTwo G) :
    Glauberman.NormalPComplement 2 G := by
  by_cases h2 : 2 ∣ Nat.card G
  · let S : Sylow 2 G := Classical.choice Sylow.nonempty
    have hmin : (Nat.card G).minFac = 2 :=
      (Nat.minFac_eq_two_iff (Nat.card G)).2 h2
    have hNC : Subgroup.normalizer (S : Set G) ≤
        Subgroup.centralizer (S : Set G) :=
      (hSylow S).normalizer_le_centralizer hmin
    have hScenter : (S : Subgroup G) ≤
        centerIn (G := G) (Subgroup.normalizer (S : Subgroup G)) := by
      intro s hs
      refine ⟨Subgroup.le_normalizer hs, ?_⟩
      change s ∈ Subgroup.centralizer (Subgroup.normalizer (S : Set G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (Subgroup.mem_centralizer_iff.mp (hNC hg) s hs).symm
    have hcomp : HasNormalPComplement 2 G :=
      hasNormalPComplement_of_sylow_le_center_normalizer (G := G) 2 S hScenter
    exact normalPComplement_of_hasNormalPComplement hcomp
  · have hodd : Odd (Nat.card G) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact h2
    have hcomp : HasNormalPComplement 2 G := by
      refine ⟨⊤, inferInstance, ?_, ?_⟩
      · simpa using hodd.coprime_two_left
      · intro x
        refine ⟨0, ?_⟩
        have hsub : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
          QuotientGroup.subsingleton_quotient_top
        simpa using (@Subsingleton.elim _ hsub x 1)
    exact normalPComplement_of_hasNormalPComplement hcomp

/-- Proposition 9, second assertion (p. 219): every proper subgroup `H` of a
minimal counterexample is a `D`-group or possesses a normal `2`-complement.
The paper's "minimal counterexample to Theorem 1" is expressed by
`IsMinimalCounterexample` (see the module header for the mapping). -/
public theorem gw_prop9_properSubgroups_dGroup_or_normalTwoComplement
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hH : H ≠ ⊤) :
    IsDGroup H ∨ Glauberman.NormalPComplement 2 (↥H) := by
  exact Or.inl (properSubgroups_areDGroups hmin H hH)

/-! ## Proposition 9: `O(G) = 1` and the minimal-normal-subgroup analysis -/

/-- Proposition 9 proof (p. 219): "Hence `O(𝔊) = 1`." -/
public theorem gw_prop9_oddCore_trivial
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) :
    pPrimeCore 2 G = ⊥ := by
  exact pPrimeCore_two_eq_bot_of_minimalCounterexample hmin

/-! ## Minimal-normal quotient transport

The next classification theorem needs to pass the `IsDGroupQuotient` clause
through the trivial odd core of a minimal normal subgroup.  This transport is
independent of the hard ``normal odd-index linear subgroup is all of `H`''
classification step, so expose it as a reusable helper. -/

/-- Transport the quotient alternatives in `IsDGroupQuotient` across the
trivial `O₂'(H)` quotient of a minimal normal subgroup.  The helper deliberately
retains the normal odd-index linear subgroup in the linear branch; identifying
that subgroup with `H` is the separate Gorenstein--Walter classification step. -/
public theorem gw_prop9_minimalNormal_dGroup_quotient_reduction
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal) (_hHne : H ≠ ⊥)
    (_hHmin : ∀ M : Subgroup G, M.Normal → M ≤ H → M = ⊥ ∨ M = H)
    (hHD : IsDGroupQuotient H) :
    pPrimeCore 2 (↥H) = ⊥ ∧
      (Nonempty ((↥H) ≃* alternatingGroup (Fin 7)) ∨
        ∃ L : Subgroup (↥H),
          L.Normal ∧ Odd L.index ∧
            (IsIsoToPSL2OddExists L ∨ IsIsoToPGL2OddExists L)) := by
  have hOH : pPrimeCore 2 (↥H) = ⊥ :=
    pPrimeCore_two_eq_bot_of_normal_subgroup_of_minimalCounterexample
      hmin H hHnormal
  let qE : (↥H ⧸ pPrimeCore 2 H) ≃* (↥H) :=
    (QuotientGroup.quotientMulEquivOfEq (G := ↥H) hOH).trans
      (QuotientGroup.quotientBot (G := ↥H))
  refine ⟨hOH, ?_⟩
  rcases hHD with hA7 | ⟨L, hLnormal, hLindex, hLmodel⟩
  · left
    exact ⟨qE.symm.trans hA7.some⟩
  · right
    let L' : Subgroup (↥H) := L.map qE.toMonoidHom
    have hL'normal : L'.Normal := by
      simpa [L'] using (hLnormal.map qE.toMonoidHom qE.surjective)
    have hL'index : Odd L'.index := by
      change Odd (L.map qE.toMonoidHom).index
      rw [Subgroup.index_map]
      have hker : qE.toMonoidHom.ker = ⊥ :=
        MonoidHom.ker_eq_bot qE.toMonoidHom qE.injective
      have hrange : qE.toMonoidHom.range = ⊤ :=
        MonoidHom.range_eq_top.mpr qE.surjective
      rw [hker, hrange, Subgroup.index_top, mul_one, sup_bot_eq]
      exact hLindex
    have eL : L ≃* L' := by
      simpa [L'] using
        (Subgroup.equivMapOfInjective L qE.toMonoidHom qE.injective)
    have hLmodel' :
        IsIsoToPSL2OddExists L' ∨ IsIsoToPGL2OddExists L' := by
      rcases hLmodel with hLpsl | hLpgl
      · left
        rcases hLpsl with ⟨K, instK, finK, hK⟩
        let : Field K := instK
        let : Finite K := finK
        refine ⟨K, instK, finK, ?_⟩
        exact ⟨hK.1, ⟨eL.symm.trans hK.2.some⟩⟩
      · right
        rcases hLpgl with ⟨K, instK, finK, hK⟩
        let : Field K := instK
        let : Finite K := finK
        refine ⟨K, instK, finK, ?_⟩
        exact ⟨hK.1, ⟨eL.symm.trans hK.2.some⟩⟩
    exact ⟨L', hL'normal, hL'index, hLmodel'⟩

/-- Proposition 9 proof (p. 219): "If `H` is a `D`-group, the minimality of
`H` implies that `H` is isomorphic to `PSL(2,q)`, `q` odd, or to `A₇`."  The
paper's "`D`-group" is the dihedral-Sylow plus quotient condition, written
`HasDihedralSylowTwo (↥H)` and `IsDGroupQuotient H` (the repository's
`IsDGroup` would be wrong here: its `2`-group quotient case includes e.g.
`V₄`, for which the conclusion fails). -/
public theorem gw_prop9_minimalNormal_dGroup_iso_PSL2_or_A7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal) (hHne : H ≠ ⊥)
    (hHmin : ∀ M : Subgroup G, M.Normal → M ≤ H → M = ⊥ ∨ M = H)
    (hHd : HasDihedralSylowTwo (↥H)) (hHD : IsDGroupQuotient H) :
    IsIsoToPSL2OddExists H ∨ Nonempty (H ≃* alternatingGroup (Fin 7)) := by
  rcases gw_prop9_minimalNormal_dGroup_quotient_reduction
      hmin H hHnormal hHne hHmin hHD with
    ⟨_hcore, hA7 | ⟨L, hLnormal, hLindex, hLmodel⟩⟩
  · exact Or.inr hA7
  have hLtop : L = ⊤ :=
    normal_odd_index_eq_top_of_minimalNormal_dihedral
      H hHnormal hHmin hHd L hLnormal hLindex
  rw [hLtop] at hLmodel
  rcases hLmodel with hLpsl | hLpgl
  · left
    rcases hLpsl with ⟨K, instK, finK, hK⟩
    let : Field K := instK
    let : Finite K := finK
    refine ⟨K, instK, finK, ?_⟩
    refine ⟨hK.1, ?_⟩
    exact ⟨Subgroup.topEquiv.symm.trans hK.2.some⟩
  · rcases hLpgl with ⟨K, instK, finK, hK⟩
    let : Field K := instK
    let : Finite K := finK
    let eH : (↥H) ≃* PGL2 K := Subgroup.topEquiv.symm.trans hK.2.some
    have hcomm : commutator (↥H) ≠ ⊥ ∧ commutator (↥H) ≠ ⊤ :=
      commutator_ne_bot_ne_top_of_mulEquiv_pgl2_odd K hK.1 eH
    let C : Subgroup (↥H) := commutator (↥H)
    let : C.Characteristic := by
      dsimp [C]
      infer_instance
    let : H.Normal := hHnormal
    have hCnormal : (C.map H.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hCle : C.map H.subtype ≤ H := Subgroup.map_subtype_le C
    rcases hHmin (C.map H.subtype) hCnormal hCle with hCbot | hCtop
    · exfalso
      apply hcomm.1
      simpa [C] using
        (Subgroup.map_eq_bot_iff_of_injective C H.subtype_injective).mp hCbot
    · exfalso
      apply hcomm.2
      have htopmap : (⊤ : Subgroup (↥H)).map H.subtype = H := by
        rw [← MonoidHom.range_eq_map, H.range_subtype]
      have hCeqTop : C = ⊤ :=
        Subgroup.map_subtype_inj.mp (hCtop.trans htopmap.symm)
      simpa [C] using hCeqTop

/-- **[10]-wave addition, pending review.** Proposition 9 supplies, in the
`PSL(2,q)`, `q` odd branch of `gw_prop9_minimalNormal_dGroup_iso_PSL2_or_A7`,
the dihedral-Sylow hypothesis `hHd` of
`gw_prop9_centralizer_odd_of_trivial_center_dihedralSylow`: a subgroup
`H ≅ PSL₂(K)` with `|K|` an odd prime power has dihedral Sylow
`2`-subgroups. -/
public theorem gw_prop9_PSL2_odd_hasDihedralSylowTwo
    (K : Type u) [Field K] [Finite K]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hH : IsIsoToPSL2Odd K H) :
    HasDihedralSylowTwo (↥H) := by
  exact hasDihedralSylowTwo_of_mulEquiv hH.2.some
    (psl2_odd_hasDihedralSylowTwo_model K hH.1)

/-- The `PGL(2,q)` analogue of
`gw_prop9_PSL2_odd_hasDihedralSylowTwo`: an odd-prime-power projective
general linear model has dihedral Sylow `2`-subgroups. -/
public theorem gw_prop9_PGL2_odd_hasDihedralSylowTwo
    (K : Type u) [Field K] [Finite K]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hH : IsIsoToPGL2Odd K H) :
    HasDihedralSylowTwo (↥H) := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  exact hasDihedralSylowTwo_of_mulEquiv hH.2.some
    (pgl2_odd_hasDihedralSylowTwo_model K hH.1)

/-- **[10]-wave addition, pending review.** Proposition 9 supplies, in the
`PSL(2,q)`, `q` odd branch of `gw_prop9_minimalNormal_dGroup_iso_PSL2_or_A7`,
the trivial-center hypothesis `hZ` of
`gw_prop9_centralizer_odd_of_trivial_center_dihedralSylow`: a subgroup
`H ≅ PSL₂(K)` with `|K|` an odd prime power has trivial center. -/
public theorem gw_prop9_PSL2_odd_center_eq_bot
    (K : Type u) [Field K] [Finite K]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hH : IsIsoToPSL2Odd K H) :
    Subgroup.center (↥H) = ⊥ := by
  exact center_eq_bot_of_mulEquiv hH.2.some (psl2_center_eq_bot K)

/-- **[10]-wave addition, pending review.** The full `hHd` supply for
`gw_prop9_centralizer_odd_of_trivial_center_dihedralSylow`: a minimal normal
subgroup `H` of the minimal counterexample with `H/O(H)` a `D`-group quotient
has dihedral Sylow `2`-subgroups.  Since `O(H) = 1`, the `A₇` branch transports
directly to `H`.  In the linear branch, the model subgroup has odd index in
`H/O(H)`, so its `PSL(2,q)` or `PGL(2,q)` dihedral Sylow subgroup is already
Sylow in the quotient and then transports back to `H`. -/
public theorem hasDihedralSylowTwo_of_minimalNormal_dGroupQuotient
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal) (_hHne : H ≠ ⊥)
    (_hHmin : ∀ M : Subgroup G, M.Normal → M ≤ H → M = ⊥ ∨ M = H)
    (hHD : IsDGroupQuotient H) :
    HasDihedralSylowTwo (↥H) := by
  have hOH : pPrimeCore 2 (↥H) = ⊥ :=
    pPrimeCore_two_eq_bot_of_normal_subgroup_of_minimalCounterexample
      hmin H hHnormal
  let qE : (H ⧸ pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq (G := ↥H) hOH).trans
      (QuotientGroup.quotientBot (G := ↥H))
  rcases hHD with hA7 | ⟨L, hLnormal, hLindex, hLmodel⟩
  · have eHA : H ≃* alternatingGroup (Fin 7) :=
      qE.symm.trans hA7.some
    exact hasDihedralSylowTwo_of_mulEquiv eHA
      hasDihedralSylowTwo_alternatingGroupSeven
  · have hLd : HasDihedralSylowTwo L := by
      rcases hLmodel with hPSL | hPGL
      · rcases hPSL with ⟨K, instK, finK, hK⟩
        let : Field K := instK
        let : Finite K := finK
        exact gw_prop9_PSL2_odd_hasDihedralSylowTwo K L hK
      · rcases hPGL with ⟨K, instK, finK, hK⟩
        let : Field K := instK
        let : Finite K := finK
        exact gw_prop9_PGL2_odd_hasDihedralSylowTwo K L hK
    have hQd : HasDihedralSylowTwo (H ⧸ pPrimeCore 2 H) :=
      hasDihedralSylowTwo_of_odd_index L hLindex hLd
    exact hasDihedralSylowTwo_of_mulEquiv qE.symm hQd

/-- **[10]-wave addition, pending review.** The full `hZ` supply for
`gw_prop9_centralizer_odd_of_trivial_center_dihedralSylow` (the
`center_eq_bot_of_A7_quotient` analogue at the `D`-group-quotient level): a
minimal normal subgroup `H` of the minimal counterexample with `H/O(H)` a
`D`-group quotient has trivial center.  The route wires the
`PSL(2,q)`/`A₇` classification
(`gw_prop9_minimalNormal_dGroup_iso_PSL2_or_A7`) with the trivial-center
clauses of both branches: `gw_prop9_PSL2_odd_center_eq_bot` and
`center_eq_bot_of_A7_quotient`. -/
public theorem center_eq_bot_of_minimalNormal_dGroupQuotient
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal) (hHne : H ≠ ⊥)
    (hHmin : ∀ M : Subgroup G, M.Normal → M ≤ H → M = ⊥ ∨ M = H)
    (hHD : IsDGroupQuotient H) :
    Subgroup.center (↥H) = ⊥ := by
  have hHd : HasDihedralSylowTwo (↥H) :=
    hasDihedralSylowTwo_of_minimalNormal_dGroupQuotient
      hmin H hHnormal hHne hHmin hHD
  rcases gw_prop9_minimalNormal_dGroup_iso_PSL2_or_A7
      hmin H hHnormal hHne hHmin hHd hHD with hPSL | hA7
  · rcases hPSL with ⟨K, instK, finK, hK⟩
    let : Field K := instK
    let : Finite K := finK
    exact gw_prop9_PSL2_odd_center_eq_bot K H hK
  · have hOH : pPrimeCore 2 (↥H) = ⊥ :=
      pPrimeCore_two_eq_bot_of_normal_subgroup_of_minimalCounterexample
        hmin H hHnormal
    have eQ : Nonempty ((H ⧸ pPrimeCore 2 H) ≃* alternatingGroup (Fin 7)) := by
      refine ⟨((QuotientGroup.quotientMulEquivOfEq (G := ↥H) hOH).trans
        (QuotientGroup.quotientBot (G := ↥H))).trans hA7.some⟩
    exact center_eq_bot_of_A7_quotient hmin H hHnormal eQ

/-- Proposition 9 proof (p. 219): "Since `Z(H) = 1` and the `S₂`-subgroup of
`H` is dihedral, `C(H)` is odd."  The paper's context is `H` a *minimal
normal* subgroup of the minimal counterexample `G` — the bare statement is
false without it (refuted by `G = A₅ × C₂`, `H = A₅`: `Z(H) = 1`, Sylow 2 of
`H` is `V₄` dihedral, but `|C_G(H)| = 2`).  The truth-critical hypotheses
are the minimality of `H` and `G`'s own dihedral Sylow 2: with
`D := H ∩ S ⊴ S` for a Sylow `S` of `G`, the centralizer part satisfies
`C_S(D) ⊆ D` (the `V₄`-Sylow case is the delicate one to formalize), and
`|C_G(H)|` has odd order. -/
public theorem gw_prop9_centralizer_odd_of_trivial_center_dihedralSylow
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (hHmin : ∀ M : Subgroup G, M.Normal → M ≤ H → M = ⊥ ∨ M = H)
    (hHne : H ≠ ⊥)
    (hZ : Subgroup.center (↥H) = ⊥) (hSylow : HasDihedralSylowTwo (↥H)) :
    Nat.Coprime 2 (Nat.card (↥(Subgroup.centralizer (H : Set G)))) := by
  exact centralizer_card_coprime_two_of_normal_centerless_dihedral
    hmin.1 H hHnormal hZ hSylow

/-- Proposition 9 proof (p. 219): "Since `C(H) ⊴ 𝔊`, we must have
`C(H) = 1`" — a normal centralizer of odd order is trivial because `O(G) = 1`
(`gw_prop9_oddCore_trivial`). -/
public theorem gw_prop9_centralizer_of_normal_odd_order_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (hCodd : Nat.Coprime 2 (Nat.card (↥(Subgroup.centralizer (H : Set G))))) :
    Subgroup.centralizer (H : Set G) = ⊥ := by
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let : H.Normal := hHnormal
  have hCnormal : C.Normal := by
    simpa [C] using (Subgroup.normal_centralizer (H := H))
  have hO : pPrimeCore 2 G = ⊥ :=
    pPrimeCore_two_eq_bot_of_minimalCounterexample hmin
  have hCle : C ≤ pPrimeCore 2 G := by
    exact le_sSup ⟨hCnormal, by simpa [C] using hCodd⟩
  have hCbot : C = ⊥ := by
    rw [hO] at hCle
    exact le_bot_iff.mp hCle
  simpa [C] using hCbot

/-- Proposition 9 proof (p. 219), dihedral case: "`C(H)` possesses a normal
`2`-complement, which is normal in `G`."  The paper's sentence covers every
normal dihedral `2`-subgroup `H` of the minimal counterexample (for `|H| = 4`
the claim rests on the `O(G) = 1` context, not on Burnside's theorem; see the
next statement for the triviality of the complement). -/
public theorem gw_prop9_centralizer_dihedral_normalTwoComplement
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (hHdihedral : ∃ m : ℕ, 1 ≤ m ∧ Nonempty (H ≃* DihedralGroup (2 ^ m))) :
    Glauberman.NormalPComplement 2 (↥(Subgroup.centralizer (H : Set G))) := by
  rcases hHdihedral with ⟨m, hm, ⟨eH⟩⟩
  have hHpg : IsPGroup 2 H := by
    have hdpg : IsPGroup 2 (DihedralGroup (2 ^ m)) := by
      apply IsPGroup.of_card (n := m + 1)
      rw [DihedralGroup.nat_card]
      rw [pow_succ]
      ring
    exact hdpg.of_equiv eH.symm
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let P : Sylow 2 (↥C) := Classical.choice Sylow.nonempty
  let Pmap : Subgroup G := (P : Subgroup C).map C.subtype
  have hPmap : IsPGroup 2 Pmap := by
    simpa [Pmap] using
      IsPGroup.map (p := 2) (H := (P : Subgroup C)) P.isPGroup' C.subtype
  have hPmapC : Pmap ≤ C := by
    simpa [Pmap] using Subgroup.map_subtype_le (P : Subgroup C)
  have hHnormP : H ≤ Subgroup.normalizer (Pmap : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh p hp
    have hpC : p ∈ C := hPmapC hp
    have hcomm : h * p = p * h :=
      (Subgroup.mem_centralizer_iff.mp hpC) h hh
    rw [hcomm]
    simpa using hp
  have hsup : IsPGroup 2 (H ⊔ Pmap : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hHpg hPmap hHnormP
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hsup
  have hHleS : H ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hPmapS : Pmap ≤ (S : Subgroup G) := le_sup_right.trans hS
  let D : Subgroup S := H.subgroupOf (S : Subgroup G)
  have hDnormal : D.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hHleS).2
    intro h k hh hk
    exact hHnormal.conj_mem h hh (k : G)
  have hDnc : ¬ IsCyclic D := by
    intro hcyc
    have hcycH : IsCyclic H :=
      (Subgroup.subgroupOfEquivOfLe hHleS).isCyclic.mp hcyc
    have hcycDih : IsCyclic (DihedralGroup (2 ^ m)) := eH.isCyclic.mp hcycH
    apply (DihedralGroup.not_isCyclic (by
      have : 2 ^ m ≠ 1 := by
        intro hpow
        have : m = 0 := by
          simpa using (Nat.pow_eq_one.mp hpow).resolve_left (by norm_num)
        omega
      exact this)) hcycDih
  rcases hmin.1 S with ⟨k, hk, ⟨eS⟩⟩
  have hleD : Subgroup.centralizer (D : Set S) ≤ D :=
    centralizer_le_of_normal_dihedral_of_mulEquiv hk eS D hDnormal hDnc
  have hPcent : Pmap.subgroupOf (S : Subgroup G) ≤
      Subgroup.centralizer (D : Set S) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hpmap : (p : G) ∈ Pmap := hp
    have hpC : (p : G) ∈ C := hPmapC hpmap
    have hdH : (d : G) ∈ H := hd
    have hcomm : (d : G) * (p : G) = (p : G) * (d : G) :=
      (Subgroup.mem_centralizer_iff.mp hpC) (d : G) hdH
    apply Subtype.ext
    exact hcomm
  have hPsubD : Pmap.subgroupOf (S : Subgroup G) ≤ D := hPcent.trans hleD
  have hPsubH : Pmap ≤ H := by
    intro x hx
    let xs : S := ⟨x, hPmapS hx⟩
    have hxs : xs ∈ D :=
      hPsubD (show xs ∈ Pmap.subgroupOf (S : Subgroup G) from hx)
    exact hxs
  have hPcenter : (P : Subgroup C) ≤
      centerIn (G := C) (Subgroup.normalizer (P : Subgroup C)) := by
    intro p hp
    refine ⟨Subgroup.le_normalizer hp, ?_⟩
    change p ∈ Subgroup.centralizer (Subgroup.normalizer ((P : Subgroup C) : Set C) : Set C)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hpG : (p : G) ∈ H := by
      apply hPsubH
      exact Subgroup.mem_map_of_mem C.subtype hp
    have hqC : (q : G) ∈ C := q.property
    have hcomm : (p : G) * (q : G) = (q : G) * (p : G) :=
      (Subgroup.mem_centralizer_iff.mp hqC) (p : G) hpG
    apply Subtype.ext
    exact hcomm.symm
  have hcomp : HasNormalPComplement 2 (↥C) :=
    hasNormalPComplement_of_sylow_le_center_normalizer (G := ↥C) 2 P hPcenter
  exact normalPComplement_of_hasNormalPComplement hcomp

/-- Proposition 9 proof (p. 219), dihedral case: "and hence `O(C(H)) = 1`".
Stated for every normal `H`: the odd core of `C_G(H)` is characteristic in
`C_G(H) ⊴ G`, hence normal and odd in `G`, hence contained in `O(G) = 1`. -/
public theorem gw_prop9_centralizer_oddCore_trivial
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal) :
    oddCoreOf (Subgroup.centralizer (H : Set G)) = ⊥ := by
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  have hCnormal : C.Normal := by
    exact Subgroup.normal_centralizer (H := H)
  have hbot : pPrimeCore 2 (↥C) = ⊥ :=
    pPrimeCore_two_eq_bot_of_normal_subgroup_of_minimalCounterexample hmin C hCnormal
  unfold oddCoreOf
  simpa [C, hbot]

/-- Proposition 9 proof (p. 219), dihedral case: "Then it follows that each
element of `𝔊 − 𝔍` induces an outer automorphism of `𝔍`" — for a normal
dihedral `2`-subgroup `H`, no element outside `H` acts on `H` by an inner
automorphism. -/
public theorem gw_prop9_dihedral_normal_subgroup_outer_automorphism
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (hHdihedral : ∃ m : ℕ, 1 ≤ m ∧ Nonempty (H ≃* DihedralGroup (2 ^ m)))
    (g : G) (hg : g ∉ H) :
    ¬ ∃ n : ↥H, ∀ x : ↥H, g * x * g⁻¹ = n * x * n⁻¹ := by
  rcases hHdihedral with ⟨m, hm, ⟨eH⟩⟩
  have hHpg : IsPGroup 2 H := by
    have hdpg : IsPGroup 2 (DihedralGroup (2 ^ m)) := by
      apply IsPGroup.of_card (n := m + 1)
      rw [DihedralGroup.nat_card, pow_succ]
      ring
    exact hdpg.of_equiv eH.symm
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  have hNPC : Glauberman.NormalPComplement 2 (↥C) :=
    gw_prop9_centralizer_dihedral_normalTwoComplement hmin H hHnormal
      ⟨m, hm, ⟨eH⟩⟩
  have hCO : oddCoreOf C = ⊥ := by
    simpa [C] using gw_prop9_centralizer_oddCore_trivial hmin H hHnormal
  have hCcore : pPrimeCore 2 (↥C) = ⊥ := by
    unfold oddCoreOf at hCO
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pPrimeCore 2 (↥C)) C.subtype_injective).mp hCO
  have hCtwo : IsPGroup 2 (↥C) :=
    isPGroup_of_normalPComplement_of_pPrimeCore_eq_bot hNPC hCcore
  let Cmap : Subgroup G := C
  have hCmap : IsPGroup 2 Cmap := by
    simpa [Cmap] using hCtwo
  have hCmapC : Cmap ≤ C := by
    simpa [Cmap]
  have hHnormC : H ≤ Subgroup.normalizer (Cmap : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh c hc
    have hcC : c ∈ C := hCmapC hc
    have hcomm : h * c = c * h :=
      (Subgroup.mem_centralizer_iff.mp hcC) h hh
    rw [hcomm]
    simpa using hc
  have hsup : IsPGroup 2 (H ⊔ Cmap : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hHpg hCmap hHnormC
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hsup
  have hHleS : H ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hCmapS : Cmap ≤ (S : Subgroup G) := le_sup_right.trans hS
  let D : Subgroup S := H.subgroupOf (S : Subgroup G)
  have hDnormal : D.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hHleS).2
    intro h k hh hk
    exact hHnormal.conj_mem h hh (k : G)
  have hDnc : ¬ IsCyclic D := by
    intro hcyc
    have hcycH : IsCyclic H :=
      (Subgroup.subgroupOfEquivOfLe hHleS).isCyclic.mp hcyc
    have hcycDih : IsCyclic (DihedralGroup (2 ^ m)) := eH.isCyclic.mp hcycH
    apply (DihedralGroup.not_isCyclic (by
      have : 2 ^ m ≠ 1 := by
        intro hpow
        have : m = 0 := by
          simpa using (Nat.pow_eq_one.mp hpow).resolve_left (by norm_num)
        omega
      exact this)) hcycDih
  rcases hmin.1 S with ⟨k, hk, ⟨eS⟩⟩
  have hleD : Subgroup.centralizer (D : Set S) ≤ D :=
    centralizer_le_of_normal_dihedral_of_mulEquiv hk eS D hDnormal hDnc
  intro hinter
  rcases hinter with ⟨n, hn⟩
  let c : G := (n : G)⁻¹ * g
  have hcC : c ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hconj := hn ⟨x, hx⟩
    change g * x * g⁻¹ = (n : G) * x * (n : G)⁻¹ at hconj
    change x * c = c * x
    dsimp [c]
    calc
      x * ((n : G)⁻¹ * g) = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * g := by group
      _ = (n : G)⁻¹ * (g * x * g⁻¹) * g := by rw [hconj]
      _ = ((n : G)⁻¹ * g) * x := by group
  have hcmap : c ∈ Cmap := by simpa [Cmap] using hcC
  have hcS : c ∈ (S : Subgroup G) := hCmapS hcmap
  have hcDcent : (⟨c, hcS⟩ : S) ∈ Subgroup.centralizer (D : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdH : (d : G) ∈ H := hd
    have hcomm : (d : G) * c = c * (d : G) :=
      (Subgroup.mem_centralizer_iff.mp hcC) (d : G) hdH
    apply Subtype.ext
    exact hcomm
  have hcD : (⟨c, hcS⟩ : S) ∈ D := hleD hcDcent
  have hcH : c ∈ H := hcD
  have hgH : g ∈ H := by
    have hnH : (n : G) ∈ H := n.property
    have hc_eq : g = (n : G) * c := by
      dsimp [c]
      group
    rw [hc_eq]
    exact H.mul_mem hnH hcH
  exact hg hgH

/-- Proposition 9 proof (p. 219): "If `|H| > 4`, `Aut(H)` is a `2`-group" —
for a dihedral `2`-group of order `2^(m+1)` with `m ≥ 2` (order at least
`8`), written `MulAut` for the paper's `Aut`. -/
public theorem gw_prop9_aut_dihedral_is_twoGroup {m : ℕ} (hm : 2 ≤ m) :
    IsPGroup 2 (MulAut (DihedralGroup (2 ^ m))) := by
  exact dihedral_mulAut_is_twoGroup hm

/-- Proposition 9 proof (p. 219): "If `|H| = 4`, `Aut(H)` is isomorphic to
the symmetric group `S₃`" — the automorphism group (written `MulAut`) of a
four-group. -/
public theorem gw_prop9_aut_kleinFour_is_S3 {Z : Type u} [Group Z] [Finite Z]
    (hZ : IsKleinFour Z) :
    Nonempty (MulAut Z ≃* Equiv.Perm (Fin 3)) := by
  let T : Type u := {x : Z // x ≠ (1 : Z)}
  have hTcard : Nat.card T = 3 := by
    dsimp [T]
    have hcard : Nat.card Z = 4 := hZ.card_four
    have hcardT : Nat.card (SubMulAction.ofStabilizer Z (1 : Z)) + 1 = Nat.card Z :=
      SubMulAction.nat_card_ofStabilizer_add_one_eq Z (1 : Z)
    change Nat.card {x : Z // x ∉ ({1} : Set Z)} + 1 = Nat.card Z at hcardT
    have hcardT' : Nat.card {x : Z // x ≠ (1 : Z)} + 1 = Nat.card Z := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hcardT
    have hsub := Nat.eq_sub_of_add_eq hcardT'
    simpa [hcard] using hsub
  let autToPerm : MulAut Z →* Equiv.Perm T :=
    { toFun := fun f =>
        ((MulAut.toPerm Z) f).subtypePerm (fun x => by
          change f x ≠ (1 : Z) ↔ x ≠ (1 : Z)
          rw [f.map_ne_one_iff])
      map_one' := by
        ext x
        rfl
      map_mul' := by
        intro f g
        ext x
        rfl }
  have hAutToPermInj : Function.Injective autToPerm := by
    intro f g hfg
    apply MulEquiv.ext
    intro z
    by_cases hz : z = 1
    · simp [hz, f.map_one, g.map_one]
    · let zT : T := ⟨z, hz⟩
      have hval := DFunLike.congr_fun hfg zT
      exact congrArg Subtype.val hval
  have hAutToPermSurj : Function.Surjective autToPerm := by
    intro q
    let p : Z → Prop := fun z => z ≠ (1 : Z)
    let : DecidablePred p := Classical.decPred p
    let c : Type u := {z : Z // ¬p z}
    let e0 : {z : Z // p z} ⊕ c ≃ Z := Equiv.sumCompl p
    let e : Z ≃ Z := e0.symm.trans ((Equiv.sumCongr q (Equiv.refl c)).trans e0)
    have he1 : e 1 = (1 : Z) := by
      dsimp [e]
      rw [Equiv.sumCompl_symm_apply_of_neg (p := p) (a := (1 : Z)) (by simp [p])]
      rfl
    let : IsKleinFour Z := hZ
    let a : MulAut Z := hZ.mulEquiv e he1
    refine ⟨a, ?_⟩
    ext x
    change e (x : Z) = (q x : Z)
    dsimp [e]
    rw [Equiv.sumCompl_symm_apply_pos x]
    rfl
  have hAutToPermBij : Function.Bijective autToPerm :=
    ⟨hAutToPermInj, hAutToPermSurj⟩
  have eAutT : MulAut Z ≃* Equiv.Perm T :=
    MulEquiv.ofBijective autToPerm hAutToPermBij
  let eTFin : T ≃ Fin 3 := Finite.equivFinOfCardEq hTcard
  exact ⟨eAutT.trans eTFin.permCongrHom⟩

-- `gw_prop9_fourGroup_normal_subgroup_embeds_S4` moved OUT of this wrapper
-- on 2026-08-15 (unused; wrapper declaration conflicts with the cleanup
-- module that imports `MinimalCounterexample`): it is declared and proved
-- in `GorensteinWalter/GW1965FourGroupEmbedsS4.lean`, which is NOT imported
-- here (landing cycle).  See tasks/gw-gw1965-cleanup.md.

/-- Proposition 9 proof (p. 219), four-group case: "Hence either `𝔊` is a
`2`-group or `𝔊` is isomorphic to `PSL(2,3)` or `PGL(2,3)`, and Theorem 1
holds for `𝔊`" — the subgroups of `S₄` with dihedral Sylow `2`-subgroups. -/
public theorem gw_prop9_subgroup_S4_twoGroup_or_PSL23_or_PGL23
    {G : Type u} [Group G] [Finite G]
    (hGd : HasDihedralSylowTwo G)
    (hemb : ∃ φ : G →* Equiv.Perm (Fin 4), Function.Injective φ) :
    IsPGroup 2 G ∨
      Nonempty (G ≃* PSL2 (ZMod 3)) ∨ Nonempty (G ≃* PGL2 (ZMod 3)) := by
  rcases hemb with ⟨φ, hφ⟩
  let K : Subgroup (Equiv.Perm (Fin 4)) := φ.range
  let e : G ≃* K :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨fun a b hab => hφ (congrArg Subtype.val hab), φ.rangeRestrict_surjective⟩
  have hKd : HasDihedralSylowTwo (↥K) :=
    hasDihedralSylowTwo_of_mulEquiv e.symm hGd
  rcases subgroup_S4_dihedral_classification hKd with hP | hAlt | hTop
  · exact Or.inl (hP.of_equiv e.symm)
  · right; left
    rw [hAlt] at e
    exact ⟨e.trans psl2_three_equiv_alternatingGroup.symm⟩
  · right; right
    rw [hTop] at e
    exact ⟨(e.trans Subgroup.topEquiv).trans pgl2_three_equiv_perm.symm⟩

/-- Proposition 9 proof (p. 219), cyclic case: "if `𝔍` is cyclic, the
minimality of `𝔍` implies that `|𝔍| = 2`" — a minimal normal cyclic subgroup
of the minimal counterexample has order `2` (an odd prime order would put it
inside `O(G) = 1`). -/
public theorem gw_prop9_minimalNormal_cyclic_card_two
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal) (hHne : H ≠ ⊥)
    (hHmin : ∀ M : Subgroup G, M.Normal → M ≤ H → M = ⊥ ∨ M = H)
    (hHcyc : IsCyclic H) :
    Nat.card (↥H) = 2 := by
  classical
  have hcard_ne_one : Nat.card (↥H) ≠ 1 := by
    intro hcard
    apply hHne
    exact Subgroup.eq_bot_of_card_eq H hcard
  obtain ⟨p, hpPrime, hpDiv⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let : CommGroup H := hHcyc.commGroup
  let K : Subgroup H := (powMonoidHom p : H →* H).ker
  have hKchar : K.Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    apply MonoidHom.mem_ker.mpr
    have hyPow : y ^ p = (1 : H) := by
      exact MonoidHom.mem_ker.mp
        (show y ∈ (powMonoidHom p : H →* H).ker from hy)
    change (φ y) ^ p = (1 : H)
    rw [← map_pow, hyPow, map_one]
  have hKcard : Nat.card K = p := by
    have hformula := IsCyclic.card_powMonoidHom_ker H p
    have hgcd : (Nat.card H).gcd p = p := Nat.gcd_eq_right hpDiv
    simpa [K, hgcd] using hformula
  let : H.Normal := hHnormal
  let : K.Characteristic := hKchar
  have hKnormal : (K.map H.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hKcases := hHmin (K.map H.subtype) hKnormal (Subgroup.map_subtype_le K)
  have hcardH_eq_p : Nat.card (↥H) = p := by
    rcases hKcases with hKbot | hKtop
    · have hKleker : K ≤ H.subtype.ker := (Subgroup.map_eq_bot_iff K).mp hKbot
      have hker : H.subtype.ker = ⊥ :=
        MonoidHom.ker_eq_bot H.subtype Subtype.coe_injective
      rw [hker] at hKleker
      have hKeqbot : K = ⊥ := le_bot_iff.mp hKleker
      have hcard_bot : Nat.card K = 1 := by
        simpa [hKeqbot] using
          (Subgroup.card_bot : Nat.card (⊥ : Subgroup H) = 1)
      rw [hKcard] at hcard_bot
      exfalso
      have hpgt : 1 < p := hpPrime.one_lt
      omega
    · let eK : K ≃* K.map H.subtype :=
        Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
      calc
        Nat.card (↥H) = Nat.card (↥(K.map H.subtype)) := by rw [hKtop]
        _ = Nat.card (↥K) := (Nat.card_congr eK.toEquiv).symm
        _ = p := hKcard
  have hpnotodd : ¬ Odd p := by
    intro hpodd
    have hcop : Nat.Coprime 2 (Nat.card (↥H)) := by
      rw [hcardH_eq_p]
      exact Odd.coprime_two_left hpodd
    have hO : pPrimeCore 2 G = ⊥ :=
      pPrimeCore_two_eq_bot_of_minimalCounterexample hmin
    have hHle : H ≤ pPrimeCore 2 G := le_sSup ⟨hHnormal, hcop⟩
    rw [hO] at hHle
    exact hHne (le_bot_iff.mp hHle)
  have hp2 : p = 2 := by
    rcases hpPrime.eq_two_or_odd' with hp2 | hpodd
    · exact hp2
    · exact False.elim (hpnotodd hpodd)
  simpa [hcardH_eq_p, hp2]

/-- Proposition 9 proof (p. 219), cyclic case: "whence `𝔍 = C(𝔍)`" — the
paper's equality is a slip; the true statement is that a normal subgroup of
order `2` is central, i.e. `C_G(H) = G`. -/
public theorem gw_prop9_order_two_normal_subgroup_central
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hHnormal : H.Normal) (hH2 : Nat.card (↥H) = 2) :
    H ≤ Subgroup.center G := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hx1 : x = 1
  · simp [hx1]
  · have hconj : g * x * g⁻¹ ∈ H := hHnormal.conj_mem x hx g
    have hx' : (⟨x, hx⟩ : H) ≠ (1 : H) := by
      intro h
      apply hx1
      exact Subtype.ext_iff.mp h
    have hconj' : (⟨g * x * g⁻¹, hconj⟩ : H) ≠ (1 : H) := by
      intro h
      apply hx1
      have hval' : g * x * g⁻¹ = (1 : G) := by
        simpa using congrArg (fun z : H => (z : G)) h
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [hval']
        _ = 1 := by simp
    have hu := (Nat.card_eq_two_iff' (1 : H)).mp hH2
    have heq : (⟨g * x * g⁻¹, hconj⟩ : H) = ⟨x, hx⟩ :=
      hu.unique hconj' hx'
    have hval' : g * x * g⁻¹ = x := by
      simpa using congrArg (fun z : H => (z : G)) heq
    calc
      g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hval']

/-! ## Lemma 2.2 (Part I, pp. 90--91) -/

/-- Lemma 2.2 (Part I, p. 91): "If `𝔊` is a group with a dihedral `S₂`-subgroup
`𝔖` and if `T₁` is an involution in `Z(𝔖)`, then `C(T₁)` possesses a normal
`2`-complement."  The membership `T₁ ∈ Z(𝔖)` is written in the ambient group
as `t ∈ (Subgroup.center (↥S)).map S.subtype`. -/
public theorem gw_lemma_2_2
    {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G)
    (S : Sylow 2 G)
    (t : G) (ht : t ∈ (Subgroup.center (↥S)).map (S : Subgroup G).subtype)
    (ht2 : IsInvolution t) :
    Glauberman.NormalPComplement 2 (↥(Subgroup.centralizer ({t} : Set G))) := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
  have htC : t ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
  let tC : C := ⟨t, htC⟩
  have htCne : tC ≠ 1 := by
    intro h
    apply ht2.1
    exact congrArg Subtype.val h
  have htCcentral : tC ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hx := x.property
    rw [Subgroup.mem_centralizer_iff] at hx
    exact (hx t (Set.mem_singleton t)).symm
  have hSC : (S : Subgroup G) ≤ C := by
    obtain ⟨z, hzcenter, hzt⟩ := Subgroup.mem_map.mp ht
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    have hzcomm := Subgroup.mem_center_iff.mp hzcenter ⟨s, hs⟩
    have hzcomm' := congrArg Subtype.val hzcomm
    change t * s = s * t
    rw [← hzt]
    exact hzcomm'.symm
  let SC : Sylow 2 C := S.subtype hSC
  have hCdihedral : HasDihedralSylowTwo C := by
    obtain ⟨m, hm, ⟨eS⟩⟩ := hdihedral S
    intro Q
    refine ⟨m, hm, ⟨(Sylow.equiv SC Q).symm |>.trans ?_⟩⟩
    exact (Subgroup.subgroupOfEquivOfLe hSC).trans eS
  have htCorder : orderOf tC = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact ht2.2
    · exact htCne
  let T : Subgroup C := Subgroup.zpowers tC
  have hTp : IsPGroup 2 T := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, htCorder]
    norm_num
  have hTcentral : T ≤ Subgroup.center C := by
    exact (Subgroup.zpowers_le).mpr htCcentral
  let : T.Normal := ⟨by
    intro x hx g
    have hxcentral : x ∈ Subgroup.center C := hTcentral hx
    have hcomm : g * x = x * g :=
      Subgroup.mem_center_iff.mp hxcentral g
    rw [hcomm]
    simpa using hx⟩
  have ht_all_sylow (Q : Sylow 2 C) : tC ∈ Q := by
    exact hTp.le_sylow_of_normal Q (Subgroup.mem_zpowers tC)
  have hEq (Q : Sylow 2 C) (Z : Subgroup C)
      (hZQ : Z ≤ (Q : Subgroup C)) (hZ : IsKleinFour Z) :
      cPrime Z = (Subgroup.normalizer (Z : Set C) : Set C) := by
    obtain ⟨m, hm, ⟨eQ⟩⟩ := hCdihedral Q
    let ZQ : Subgroup Q := Z.subgroupOf Q
    let eZQ : ZQ ≃* Z := Subgroup.subgroupOfEquivOfLe hZQ
    have hZQ4 : IsKleinFour ZQ := {
      card_four := (Nat.card_congr eZQ.toEquiv).trans hZ.card_four
      exponent_two :=
        (Monoid.exponent_eq_of_mulEquiv eZQ).trans hZ.exponent_two
    }
    let tQ : Q := ⟨tC, ht_all_sylow Q⟩
    have htQcentral : tQ ∈ Subgroup.center Q := by
      apply Subgroup.mem_center_iff.mpr
      intro x
      apply Subtype.ext
      simpa [tQ] using
        (Subgroup.mem_center_iff.mp htCcentral (x : C))
    have htZQ : tQ ∈ ZQ :=
      center_mem_kleinFour_of_dihedral_mulEquiv hm eQ ZQ hZQ4 htQcentral
    have htZ : tC ∈ Z := htZQ
    exact cPrime_eq_normalizer_of_kleinFour_fixed_center
      Z hZ htZ htCne htCcentral
  rcases gw_lemma_2_1 hCdihedral with hfirst | hsecond | hthird
  · obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := C)
    obtain ⟨m, hm, ⟨eQ⟩⟩ := hCdihedral Q
    obtain ⟨Z, hZQ, hZ⟩ :=
      exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
        (Q : Subgroup C) hm eQ
    have hstrict : NormalizerContainsCPrime Z :=
      hfirst.2.2 Q Z hZQ hZ
    rw [NormalizerContainsCPrime, hEq Q Z hZQ hZ] at hstrict
    exact (lt_irrefl _ hstrict).elim
  · rcases hsecond.2.2 with
      ⟨Q, _hQcard, Z₀, Z₁, hZ₀Q, hZ₁Q, hZ₀, hZ₁,
        _hnconj, _hcover, hstrict⟩
    rcases hstrict with ⟨hstrict₀, _⟩ | ⟨hstrict₁, _⟩
    · rw [NormalizerContainsCPrime, hEq Q Z₀ hZ₀Q hZ₀] at hstrict₀
      exact (lt_irrefl _ hstrict₀).elim
    · rw [NormalizerContainsCPrime, hEq Q Z₁ hZ₁Q hZ₁] at hstrict₁
      exact (lt_irrefl _ hstrict₁).elim
  · exact hthird.2

/-- Proposition 9 proof (p. 219), cyclic case: "But now Lemma 2.2 implies
that [`𝔊`] possesses a normal `2`-complement, and again Theorem 1 holds for
`𝔊`" — with `|H| = 2` the involution of `H` lies in `Z(S)` (Lemma 2.2's
hypothesis), and Lemma 2.2 applied to `G` gives the normal `2`-complement of
`G` (the paper's "`H` possesses" is a slip for "`𝔊` possesses"). -/
public theorem gw_prop9_cyclic_minimalNormal_normalTwoComplement
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal) (hHne : H ≠ ⊥)
    (hHmin : ∀ M : Subgroup G, M.Normal → M ≤ H → M = ⊥ ∨ M = H)
    (hHcyc : IsCyclic H) :
    Glauberman.NormalPComplement 2 G := by
  classical
  have hH2 : Nat.card (↥H) = 2 :=
    gw_prop9_minimalNormal_cyclic_card_two hmin H hHnormal hHne hHmin hHcyc
  have hHcenter : H ≤ Subgroup.center G :=
    gw_prop9_order_two_normal_subgroup_central H hHnormal hH2
  obtain ⟨x, hxne, hxuniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hH2
  let t : G := x
  have htne : t ≠ (1 : G) := by
    intro ht
    apply hxne
    exact Subtype.ext ht
  have hx2 : x ^ 2 = (1 : H) := by
    have hxpow := (pow_card_eq_one' (x := x))
    simpa [hH2] using hxpow
  have ht2 : IsInvolution t := by
    refine ⟨htne, ?_⟩
    simpa [t] using congrArg (fun z : H => (z : G)) hx2
  have htc : t ∈ Subgroup.center G := hHcenter x.property
  have hT : IsPGroup 2 (Subgroup.zpowers t) := by
    have hcard_dvd : Nat.card (Subgroup.zpowers t) ∣ 2 := by
      simpa [Nat.card_zpowers] using (orderOf_dvd_of_pow_eq_one ht2.2)
    have hcard_dvd' : Nat.card (Subgroup.zpowers t) ∣ 2 ^ 1 := by
      simpa using hcard_dvd
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hcard_dvd' with ⟨n, hn, hcard⟩
    simpa using IsPGroup.of_card hcard
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hT
  have htS : t ∈ (S : Subgroup G) := hS (Subgroup.mem_zpowers t)
  have htmap : t ∈ (Subgroup.center (↥S)).map (S : Subgroup G).subtype := by
    let s : S := ⟨t, htS⟩
    have hs : s ∈ Subgroup.center (↥S) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp htc) (y : G)
    exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
  have hNPC_C := gw_lemma_2_2 hmin.1 S t htmap ht2
  have hCtop : Subgroup.centralizer ({t} : Set G) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr htc)
  rw [hCtop] at hNPC_C
  have hOpTop : Op_p'p 2 (↥(⊤ : Subgroup G)) = ⊤ :=
    Glauberman.normalPComplement_eq_top hNPC_C
  have hcompOp : HasNormalPComplement 2
      (↥(Op_p'p 2 (↥(⊤ : Subgroup G)))) :=
    hasNormalPComplement_Op_p'p (p := 2) (G := (↥(⊤ : Subgroup G)))
  rw [hOpTop] at hcompOp
  have hcompTop : HasNormalPComplement 2 (↥(⊤ : Subgroup G)) :=
    hasNormalPComplement_of_equiv 2
      (Subgroup.topEquiv (G := (↥(⊤ : Subgroup G)))) hcompOp
  have hcompG : HasNormalPComplement 2 G :=
    hasNormalPComplement_of_equiv 2 (Subgroup.topEquiv (G := G)) hcompTop
  exact normalPComplement_of_hasNormalPComplement hcompG

/-- **[10]-wave addition, pending review.** Proposition 9, cyclic case
(p. 220): "and again Theorem 1 holds for `𝔊`" — a minimal counterexample with
a normal `2`-complement satisfies Theorem 1: the normal complement is odd,
so `G/O₂'(G)` is a `2`-group (via `Op_p'p_eq_pCore_of_pPrimeCore_eq_bot` and
`pCore_isPGroup`), and the dihedral Sylow `2` gives the `D`-group quotient
clause.  (The bridge cannot be proved in `MinimalCounterexample.lean`: the
`module`-private `Glauberman.NormalPComplement` body is not exposed, so the
importing module cannot unfold it.) -/
public theorem gw_prop9_normalTwoComplement_isDGroup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (hNPC : Glauberman.NormalPComplement 2 G) :
    IsDGroup G := by
  have hSylow : HasCyclicOrDihedralSylowTwo G := by
    intro S
    rcases hmin.1 S with ⟨m, hm, e⟩
    exact Or.inr ⟨m, hm, e⟩
  have hO : pPrimeCore 2 G = ⊥ :=
    pPrimeCore_two_eq_bot_of_minimalCounterexample hmin
  have hG2 : IsPGroup 2 G :=
    isPGroup_of_normalPComplement_of_pPrimeCore_eq_bot hNPC hO
  exact IsDGroup.quotientIsTwoGroup hSylow
    (IsPGroup.to_quotient hG2 (pPrimeCore 2 G))

/-! ## Section 3 facts cited by Proposition 9 (Part I, pp. 119--124) -/

/-- Lemma 3.2(ix) (Part I, p. 123): "`A₇` has no outer automorphisms of odd
order" — every automorphism of `A₇` of odd order is an inner automorphism
(written `MulAut` for the paper's `Aut`).  Cited by the proof of Proposition
9 with the reading "(ix)" (txt layer; the transcription's "3.2 (i)" is a
probable misread, review item C1). -/
public theorem gw_lemma_3_2_ix_a7_no_outer_automorphisms_odd_order :
    ∀ φ : MulAut (alternatingGroup (Fin 7)),
      Odd (orderOf φ) → ∃ g : alternatingGroup (Fin 7), φ = MulAut.conj g := by
  intro φ hφodd
  let c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7))
  have hc : Function.Bijective c :=
    GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      7 (by norm_num) (by norm_num)
  obtain ⟨σ, hσ⟩ := hc.2 φ
  have hσodd : Odd (orderOf σ) := by
    rw [← orderOf_injective c hc.1 σ, hσ]
    exact hφodd
  have hsign : Equiv.Perm.sign σ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · exact hs
    · exfalso
      have hpow : (Equiv.Perm.sign σ) ^ orderOf σ = 1 := by
        calc
          (Equiv.Perm.sign σ) ^ orderOf σ =
              Equiv.Perm.sign (σ ^ orderOf σ) :=
            (map_pow Equiv.Perm.sign σ (orderOf σ)).symm
          _ = Equiv.Perm.sign 1 := by rw [pow_orderOf_eq_one]
          _ = 1 := map_one Equiv.Perm.sign
      rw [hs] at hpow
      have heven : Even (orderOf σ) :=
        (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by norm_num)).mp hpow
      exact (Nat.not_even_iff_odd.mpr hσodd) heven
  let g : alternatingGroup (Fin 7) :=
    ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  refine ⟨g, ?_⟩
  rw [← MulAut.conjNormal_val (h := g)]
  exact hσ.symm

/-- Lemma 3.3(vi) (Part I, p. 124): "If `𝔖` or `𝔖'` is isomorphic to a normal
subgroup of a group `𝔍` having dihedral `S₂`-subgroups and satisfying
`O(𝔍) = 1`, then `𝔍` is isomorphic to a subgroup of `𝔖*`", with
`𝔖 = PSL(2,q)`, `𝔖' = PGL(2,q)`, `𝔖* = PΓL₀(2,q)`, `q` odd.  A subgroup of
`PΓL₀(2,q)` containing `PSL(2,q)` is exactly the paper's `D`-group condition;
`PΓL₀(2,q)` itself is not in the repository vocabulary, so the conclusion is
`IsDGroup R` (whose `2`-group quotient alternative is vacuous under
`pPrimeCore 2 R = ⊥`). -/
public theorem gw_lemma_3_3_vi_linear_normal_subgroup_centralizer_eq_bot
    {R : Type u} [Group R] [Finite R]
    (hSylow : HasDihedralSylowTwo R)
    (hO : pPrimeCore 2 R = ⊥)
    (N : Subgroup R) (hNnormal : N.Normal)
    (hN : IsIsoToPSL2OddExists (G := R) N ∨ IsIsoToPGL2OddExists (G := R) N) :
    Subgroup.centralizer (N : Set R) = ⊥ := by
  rcases hN with hPSL | hPGL
  · rcases hPSL with ⟨K, instK, finK, hK⟩
    let : Field K := instK
    let : Finite K := finK
    exact centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
      hSylow hO N hNnormal
        (gw_prop9_PSL2_odd_center_eq_bot K N hK)
        (gw_prop9_PSL2_odd_hasDihedralSylowTwo K N hK)
  · rcases hPGL with ⟨K, instK, finK, hK⟩
    let : Field K := instK
    let : Finite K := finK
    have hZ : Subgroup.center (↥N) = ⊥ :=
      center_eq_bot_of_mulEquiv hK.2.some (pgl2_center_eq_bot K)
    exact centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
      hSylow hO N hNnormal hZ
        (gw_prop9_PGL2_odd_hasDihedralSylowTwo K N hK)

/-- The conjugation action in Lemma 3.3(vi) is faithful: the preceding
centralizer theorem identifies its kernel with the trivial subgroup. -/
public theorem gw_lemma_3_3_vi_linear_normal_subgroup_mulAut_embedding
    {R : Type u} [Group R] [Finite R]
    (hSylow : HasDihedralSylowTwo R)
    (hO : pPrimeCore 2 R = ⊥)
    (N : Subgroup R) (hNnormal : N.Normal)
    (hN : IsIsoToPSL2OddExists (G := R) N ∨ IsIsoToPGL2OddExists (G := R) N) :
    ∃ φ : R →* MulAut N, Function.Injective φ := by
  have hC : Subgroup.centralizer (N : Set R) = ⊥ :=
    gw_lemma_3_3_vi_linear_normal_subgroup_centralizer_eq_bot
      hSylow hO N hNnormal hN
  let : N.Normal := hNnormal
  rcases quotient_centralizer_mulAut_embedding N with ⟨φ, hφ⟩
  let qE : (R ⧸ Subgroup.centralizer (N : Set R)) ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq (G := R) hC).trans
      (QuotientGroup.quotientBot (G := R))
  let ψ : R →* MulAut N := φ.comp qE.symm.toMonoidHom
  exact ⟨ψ, hφ.comp qE.symm.injective⟩

/-- In the large-field `PGL₂` branch of Lemma 3.3(vi), the characteristic
derived subgroup supplies a normal `PSL₂` core in the ambient group. -/
public theorem gw_lemma_3_3_vi_pgl_normal_subgroup_reduces_to_psl_of_card_gt_three
    {R : Type u} [Group R] [Finite R]
    (N : Subgroup R) (hNnormal : N.Normal)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PGL2 K) :
    ∃ L : Subgroup R,
      L.Normal ∧ L ≤ N ∧ IsIsoToPSL2OddExists (G := R) L := by
  rcases exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three
      N hNnormal K hK hcard e with ⟨L, hLnormal, hLle, hLmodel⟩
  exact ⟨L, hLnormal, hLle, K, inferInstance, inferInstance, hK, hLmodel⟩

/-- The `|K| = 3` PSL₂ branch of Lemma 3.3(vi): normalize the coefficient
field to `ZMod 3`, identify `PSL₂(3)` with `A₄`, and use
`Aut(A₄) ≃ S₄`. -/
public theorem gw_lemma_3_3_vi_psl_normal_subgroup_card_eq_three_dGroup
    {R : Type u} [Group R] [Finite R]
    (hSylow : HasDihedralSylowTwo R)
    (hO : pPrimeCore 2 R = ⊥)
    (N : Subgroup R) (hNnormal : N.Normal)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : Nat.card K = 3)
    (e : N ≃* PSL2 K) :
    IsDGroup R := by
  let : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  let eK : ZMod 3 ≃+* K :=
    ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  let eN3 : N ≃* PSL2 (ZMod 3) := e.trans (psl2RingEquiv eK).symm
  have hNmodel : IsIsoToPSL2OddExists (G := R) N :=
    ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  have hC : Subgroup.centralizer (N : Set R) = ⊥ :=
    gw_lemma_3_3_vi_linear_normal_subgroup_centralizer_eq_bot
      hSylow hO N hNnormal (Or.inl hNmodel)
  exact psl2_three_normal_extension_isDGroup
    hO hSylow N hNnormal eN3 hC

/-- The `|K| = 3` PGL₂ branch of Lemma 3.3(vi): its characteristic
derived subgroup is a normal `PSL₂(3)` subgroup, so the preceding normal
extension theorem applies. -/
public theorem gw_lemma_3_3_vi_pgl_normal_subgroup_card_eq_three_dGroup
    {R : Type u} [Group R] [Finite R]
    (hSylow : HasDihedralSylowTwo R)
    (hO : pPrimeCore 2 R = ⊥)
    (N : Subgroup R) (hNnormal : N.Normal)
    (K : Type u) [Field K] [Finite K]
    (hcard : Nat.card K = 3)
    (e : N ≃* PGL2 K) :
    IsDGroup R := by
  let : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  let eK : ZMod 3 ≃+* K :=
    ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  let eN3 : N ≃* PGL2 (ZMod 3) := e.trans (pgl2RingEquiv eK).symm
  rcases exists_normal_psl2_three_core_of_normal_mulEquiv_pgl2_three
      N hNnormal eN3 with ⟨L, hLnormal, _hLle, hLmodel⟩
  have hKodd : IsOddPrimePower (Nat.card K) := by
    exact ⟨3, 1, Nat.prime_three, by decide, by omega, by simpa [hcard]⟩
  let eLK : L ≃* PSL2 K := hLmodel.some.trans (psl2RingEquiv eK)
  have hLpredicate : IsIsoToPSL2OddExists (G := R) L :=
    ⟨K, inferInstance, inferInstance, hKodd, ⟨eLK⟩⟩
  have hC : Subgroup.centralizer (L : Set R) = ⊥ :=
    gw_lemma_3_3_vi_linear_normal_subgroup_centralizer_eq_bot
      hSylow hO L hLnormal (Or.inl hLpredicate)
  exact psl2_three_normal_extension_isDGroup
    hO hSylow L hLnormal hLmodel.some hC

public theorem gw_lemma_3_3_vi_normal_subgroup_iso_PSL2_or_PGL2_dGroup
    {R : Type u} [Group R] [Finite R]
    (hSylow : HasDihedralSylowTwo R)
    (hO : pPrimeCore 2 R = ⊥)
    (N : Subgroup R) (hNnormal : N.Normal)
    (hN : IsIsoToPSL2OddExists (G := R) N ∨ IsIsoToPGL2OddExists (G := R) N) :
    IsDGroup R := by
  have large_psl_core :
      ∀ (M : Subgroup R) (hMnormal : M.Normal)
        (K : Type u) [Field K] [Finite K],
        IsOddPrimePower (Nat.card K) → 3 < Nat.card K →
          (M ≃* PSL2 K) → IsDGroup R := by
    intro M hMnormal K instK finK hK hcard e
    let : M.Normal := hMnormal
    rcases hK with ⟨p, f, hp, hpOdd, hf, hKcard⟩
    let : Fact p.Prime := ⟨hp⟩
    have hK : IsOddPrimePower (Nat.card K) :=
      ⟨p, f, hp, hpOdd, hf, hKcard⟩
    have hMmodel : IsIsoToPSL2OddExists (G := R) M :=
      ⟨K, instK, finK, hK, ⟨e⟩⟩
    have hC : Subgroup.centralizer (M : Set R) = ⊥ :=
      gw_lemma_3_3_vi_linear_normal_subgroup_centralizer_eq_bot
        hSylow hO M hMnormal (Or.inl hMmodel)
    have hsurj : Function.Surjective
        (pGammaL2ToMulAutPSL2 K hK hcard) :=
      pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard
    let f : R →* PGammaL2 K :=
      normalPSL2ToPGammaL2 M K hK hcard e hsurj
    have hf : Function.Injective f := by
      dsimp [f]
      exact normalPSL2ToPGammaL2_injective
        M K hK hcard e hC hsurj
    let eR : R ≃* f.range :=
      MulEquiv.ofBijective f.rangeRestrict
        ⟨fun a b hab => hf (congrArg Subtype.val hab),
          f.rangeRestrict_surjective⟩
    let : Finite f.range := Finite.of_surjective eR eR.surjective
    have hRange : HasDihedralSylowTwo f.range :=
      hasDihedralSylowTwo_of_mulEquiv eR.symm hSylow
    have hPSLRange : pGammaL2PSLRange K ≤ f.range := by
      dsimp [f]
      exact normalPSL2ToPGammaL2_range_contains_psl
        M K hK hcard e hsurj
    have hodd : Odd (Nat.card
        (pGammaL2FieldProjection K
          (normalPSL2ToPGammaL2 M K hK hcard e hsurj).range).range) := by
      simpa [f] using
        pGammaL2_field_projection_range_odd_of_dihedral
          K hK hcard f.range hPSLRange hRange
    exact normalPSL2Extension_isDGroup
      hSylow hO M K hK hcard e hC hsurj hodd
  rcases hN with hPSL | hPGL
  · rcases hPSL with ⟨K, instK, finK, hK⟩
    let : Field K := instK
    let : Finite K := finK
    by_cases hcard : Nat.card K = 3
    · exact gw_lemma_3_3_vi_psl_normal_subgroup_card_eq_three_dGroup
        hSylow hO N hNnormal K hK.1 hcard hK.2.some
    · have hodd : Odd (Nat.card K) := by
        rcases hK.1 with ⟨p, n, hp, hpodd, hn, hq⟩
        rw [hq]
        exact hpodd.pow
      have hge : 3 ≤ Nat.card K := by
        have hone : 1 < Nat.card K := Finite.one_lt_card
        rcases hodd with ⟨k, hk⟩
        omega
      have hgt : 3 < Nat.card K := by omega
      exact large_psl_core N hNnormal K hK.1 hgt hK.2.some
  · rcases hPGL with ⟨K, instK, finK, hK⟩
    let : Field K := instK
    let : Finite K := finK
    by_cases hcard : Nat.card K = 3
    · exact gw_lemma_3_3_vi_pgl_normal_subgroup_card_eq_three_dGroup
        hSylow hO N hNnormal K hcard hK.2.some
    · have hodd : Odd (Nat.card K) := by
        rcases hK.1 with ⟨p, n, hp, hpodd, hn, hq⟩
        rw [hq]
        exact hpodd.pow
      have hge : 3 ≤ Nat.card K := by
        have hone : 1 < Nat.card K := Finite.one_lt_card
        rcases hodd with ⟨k, hk⟩
        omega
      have hgt : 3 < Nat.card K := by omega
      rcases exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three
          N hNnormal K hK.1 hgt hK.2.some with
        ⟨L, hLnormal, _hLle, hLmodel⟩
      exact large_psl_core L hLnormal K hK.1 hgt hLmodel.some

/-- Proposition 9 proof (p. 219): "But then it follows from Lemmas 3.2 (ix)
and 3.3 (vi) that `𝔊` is a `D`-group" — a minimal normal subgroup isomorphic
to `PSL(2,q)`, `q` odd, or to `A₇`, with trivial centralizer, forces the
minimal counterexample to be a `D`-group.  The `A₇` branch uses the complete
automorphism theorem `Aut(A₇) ≃ S₇` and excludes the `S₇` extension from its
Sylow `2`-structure; the linear branch is the cited Lemma 3.3(vi). -/
public theorem gw_prop9_dGroup_conclusion_from_minimalNormal
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (hH : IsIsoToPSL2OddExists H ∨ Nonempty (H ≃* alternatingGroup (Fin 7)))
    (hCH : Subgroup.centralizer (H : Set G) = ⊥) :
    IsDGroup G := by
  rcases hH with hPSL | hA7
  · rcases hPSL with ⟨K, instK, finK, hK⟩
    let : Field K := instK
    let : Finite K := finK
    exact gw_lemma_3_3_vi_normal_subgroup_iso_PSL2_or_PGL2_dGroup
      hmin.1 (pPrimeCore_two_eq_bot_of_minimalCounterexample hmin)
      H hHnormal (Or.inl ⟨K, instK, finK, hK⟩)
  · rcases hA7 with ⟨eH⟩
    have htop : H = ⊤ :=
      aSeven_normal_extension_eq_top_of_dihedralSylow
        hmin.1 H hHnormal eH hCH
    let eHG : H ≃* G :=
      (MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv (G := G))
    exact isDGroup_of_mulEquiv_aSeven ⟨eHG.symm.trans eH⟩

end CFSG.GorensteinWalter
