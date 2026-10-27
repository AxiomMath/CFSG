module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerFittingActionCommon
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerFittingActionA7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerFittingActionLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerInnerActionOfLinearModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2ComponentLeNormalizerLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectImageNormalOddIndex
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The PSL₂ Fact 1.10(ii) normalizer centralization: dispatch

The source step

> since `N_F(X)` induces inner automorphisms on `E(N_G(X))` by 1.10(ii), it
> follows that `E(N_G(X)) ⊆ C_G(N_F(X))`

is assembled from the D-group model cases of the classification of
`N := N_G(X)`:

* the two-group quotient case is impossible (the perfect image of the
  selected component in a solvable two-group quotient vanishes);
* the A₇-quotient case is proved in
  `SecondCasePSL2NormalizerFittingActionA7`;
* the PSL₂/PGL₂ quotient cases are proved in
  `SecondCasePSL2NormalizerFittingActionLinear` modulo the Fact 1.10(ii)
  inner-action hypothesis `secondCase_psl2_normalizer_innerAction` (the
  semilinear field-projection transport).

The exported theorem `secondCase_psl2_normalizer_fitting_action` yields
exactly the centralization statement consumed by the normalizer-layer
equality core (`secondCase_psl2_fact_1_10_ii_centralization`).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The two-group quotient case of the classification of `N = N_G(X)` is
impossible: the image of the perfect selected component in the solvable
two-group quotient `N/O₂'(N)` is trivial, so the component lies in the odd
core, contradicting its perfectness. -/
public theorem secondCase_psl2_normalizer_fitting_action_two_quotient_impossible
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (F X : Subgroup G)
    (hFleFU : F ≤ c.FU) (hFleM : F ≤ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hXne : X ≠ ⊥) (hXleF : X ≤ F)
    (hQ : IsPGroup 2 (Subgroup.normalizer (X : Set G) ⧸
      pPrimeCore 2 (Subgroup.normalizer (X : Set G)))) :
    False := by
  classical
  let E : Subgroup G := d.E
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let O : Subgroup N := pPrimeCore 2 N
  let : O.Normal := by dsimp [O]; infer_instance
  let q : N →* N ⧸ O := QuotientGroup.mk' O
  have hXcentE : X ≤ Subgroup.centralizer (E : Set G) := hXleF.trans hFcentE
  have hEcentX : E ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hXcentE hx) z hz).symm
  have hEleN : E ≤ N :=
    hEcentX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  let E0 : Subgroup N := E.subgroupOf N
  have hEperf : Group.IsPerfect E := (Group.isPerfect_def).2 d.E_component.2.2.2.1
  have hEne : E ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot E).mp d.E_component.2.2.1
  have hE0perf : Group.IsPerfect E0 := by
    let : Group.IsPerfect E := hEperf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hEleN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hEleN).symm.surjective
  have hE0ne : E0 ≠ ⊥ := by
    intro hbot
    apply hEne
    have hmap : E0.map N.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEleN
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := N))
  have hOsolv : Group.IsSolvable O := odd_order_theorem O hOodd
  have hEbarData := @perfect_image_le_normal_odd_index_of_solvable_kernel
    N _ _ E0 hE0perf hE0ne O (inferInstance : O.Normal) hOsolv
      (⊤ : Subgroup (N ⧸ O)) (by infer_instance) (by simp)
  let Ebar : Subgroup (N ⧸ O) := E0.map q
  have hEbarne : Ebar ≠ ⊥ := by simpa [Ebar, q] using hEbarData.1
  have hEbarperf : Group.IsPerfect Ebar := by simpa [Ebar, q] using hEbarData.2.1
  have hQsolvable : Group.IsSolvable (N ⧸ O) := isSolvable_of_isPGroup hQ
  have hEbarSolvable : Group.IsSolvable Ebar := by
    let : Group.IsSolvable (N ⧸ O) := hQsolvable
    infer_instance
  by_contra hEbarne'
  let : Nontrivial Ebar := (Subgroup.nontrivial_iff_ne_bot Ebar).2 hEbarne
  exact Group.IsPerfect.not_isSolvable Ebar hEbarSolvable

/-- The Fact 1.10(ii) normalizer centralization for the PSL₂ branch: the
layer of `N_G(X)` centralizes `N_F(X)` for every nontrivial `X ≤ F`, given
the Fact 1.10(ii) inner action of `F(U) ∩ N_G(X)` on the layer.  This is
exactly the statement consumed by the normalizer-layer equality core. -/
public theorem secondCase_psl2_normalizer_fitting_action
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (F X : Subgroup G)
    (s : d.E)
    (hF_eq : F = centralizerIn (c.FU ⊓ w.M) (s : G))
    (hrefl : c.IsReflection (s : G))
    (hFleFU : F ≤ c.FU) (hFleM : F ≤ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hXne : X ≠ ⊥) (hXleF : X ≤ F) :
    secondCase_psl2_fact_1_10_ii_centralization c w d F X hFleFU hFleM hFcentE hXne hXleF := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  have hNproper : N ≠ ⊤ := by
    intro hNtop
    have hXnormal : X.Normal :=
      (Subgroup.normalizer_eq_top_iff (H := X)).mp hNtop
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ (minimalCounterexample_isSimple hmin)
        X hXnormal with hXbot | hXtop
    · exact hXne hXbot
    · apply w.M_maximal.ne_top
      apply top_unique
      intro g _hg
      have hgX : g ∈ X := by rw [hXtop]; trivial
      exact hFleM (hXleF hgX)
  have hDN : IsDGroup N := properSubgroups_areDGroups hmin N hNproper
  rcases hDN with
      ⟨_hSylowN, hQ⟩ | ⟨_hSylowN, eA7⟩ |
        ⟨_hSylowN, K', hK', Lq, hLqnormal, hLqindex, hLqmodel⟩
  · exact False.elim (secondCase_psl2_normalizer_fitting_action_two_quotient_impossible
      hmin c w d K hK e F X hFleFU hFleM hFcentE hXne hXleF hQ)
  · exact secondCase_psl2_normalizer_fitting_action_of_a7_quotient
      hmin c w d K hK e F X s hF_eq hrefl hFleFU hFleM hFcentE hXne hXleF eA7
  · exact secondCase_psl2_normalizer_fitting_action_of_linear_quotient
      hmin c w d K hK e F X s hF_eq hrefl hFleFU hFleM hFcentE hXne hXleF
      K' hK' Lq hLqnormal hLqindex hLqmodel
      (secondCase_psl2_normalizer_innerAction_of_linear_model
        hmin c w d K hK e F X hFleFU hFleM hFcentE hXne hXleF
        _hSylowN K' hK' Lq hLqnormal hLqindex hLqmodel)

end CFSG.GorensteinWalter
