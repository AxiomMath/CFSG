module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2InnerReflection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2InvolutionCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2QuotientTorusCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2WeakFittingFieldProjection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The PSL₂ equation-(4) endpoint

This module exports the equation-(4) package for the PSL₂ branch of
Section 4, mirroring `SecondCaseA7FittingNormal` in the A₇ branch.  The
source sentence (`refs/bender-dihedral-sylow.tex`, L651--655) is

> Centralizing `S ∩ E` and inducing inner automorphisms on `E` by 1.10(ii),
> `F` centralizes `E`, hence is normal in `E(H ∩ M) = M`.

Concretely, with `E := d.E`, `M := w.M`, and `F` the equation-(3) fixed
part `B ∩ F(U) = C_{F(U)∩M}(s)`:

* `secondCase_psl2_fitting_innerAction` — the exact Fact 1.10(ii)
  inner-action endpoint: every odd element `f ∈ F` induces an inner
  automorphism on `E / Z(E)` (the semilinear field-projection transport,
  isolated as in the normalizer-layer analogue
  `secondCase_psl2_normalizer_innerAction`).
* `secondCase_psl2_innerAction_of_image_in_pslRange` — the transport: the
  inner action follows from the image of `F` under the semilinear action
  `ad.f` lying in the canonical `PSL₂(K)` layer (whose elements act by
  inner automorphisms).  This is fully proved from
  `SecondCasePSL2ActionData.action_eq`.
* `secondCase_psl2_fitting_centralizes_component` — equation (4), first
  half: `F ≤ C_G(d.E)`, obtained by applying
  `secondCase_psl2_odd_subgroup_centralizes_component_of_inner_reflection`
  (the reflected torus kills the inner representative, and perfectness
  lifts triviality from the quotient to `E`).
* `secondCase_psl2_fitting_equation4` — equation (4), full package:
  `F ◁ M`, via `secondCase_fitting_normal_in_M_of_centralizes_component`
  and the factorization `M = E·C_M(t)`.

The remaining semilinear core — deriving
`secondCase_psl2_fitting_innerAction` from the action data alone — is the
application of `pGammaL2_weak_normal_nilpotent_odd_fieldProjection_trivial`
to the transported Fitting image; the precise route and the exact missing
transport sublemmas are recorded in the final section of this file.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-! ## The Fact 1.10(ii) inner-action endpoint -/

/-- The exact Fact 1.10(ii) endpoint for the equation-(4) route: every
element of the odd fixed part `F` induces an inner automorphism on the
component quotient `E / Z(E)`.  Conjugation by `f` on `E` gives the
quotient automorphism `quotientCenterAutomorphism E α`; the endpoint
requires it to be conjugation by an element of `PSL₂(K)` in the model.
This is the semilinear field-projection transport, isolated (as a
definition, like `secondCase_psl2_normalizer_innerAction`) so that the
equation-(4) consumer does not depend on the field arithmetic. -/
@[expose] public def secondCase_psl2_fitting_innerAction
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K)
    (F : Subgroup G) (hFleM : F ≤ w.M) : Prop :=
  ∀ f : G, (hf : f ∈ F) →
    ∃ α : d.E ≃* d.E,
      (∀ x : d.E, α x =
        ⟨f * (x : G) * f⁻¹, d.E_normal.2 f (hFleM hf) (x : G) x.2⟩) ∧
      ∃ a : PSL2 K,
        MulAut.congr ad.modelEquiv.some (quotientCenterAutomorphism d.E α) =
          MulAut.conj a

/-! ## Conjugation automorphisms of the component -/

private def conjOn {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) : E →* E :=
  { toFun := fun x => ⟨f * (x : G) * f⁻¹, hE.2 f hf (x : G) x.2⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change f * ((x : G) * (y : G)) * f⁻¹ =
        (f * (x : G) * f⁻¹) * (f * (y : G) * f⁻¹)
      group }

private def conjOnInv {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) : E →* E :=
  conjOn E M f⁻¹ (M.inv_mem hf) hE

private theorem conjOn_left {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) (x : E) :
    conjOnInv E M f hf hE (conjOn E M f hf hE x) = x := by
  apply Subtype.ext
  simp [conjOnInv, conjOn]
  group

private theorem conjOn_right {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) (x : E) :
    conjOn E M f hf hE (conjOnInv E M f hf hE x) = x := by
  apply Subtype.ext
  simp [conjOnInv, conjOn]
  group

private def conjOnEquiv {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) : E ≃* E :=
  MulEquiv.ofBijective (conjOn E M f hf hE) ⟨
    (Function.LeftInverse.injective (conjOn_left E M f hf hE)),
    (fun y => ⟨conjOnInv E M f hf hE y, conjOn_right E M f hf hE y⟩)⟩

/-! ## Transport: the image in the PSL₂ layer acts by inner automorphisms -/

/-- The semilinear transport: once the image of `F` under the action
`ad.f` lies in the canonical `PSL₂(K)` layer of `PΓL₂(K)`, the induced
quotient automorphism of every `f ∈ F` is inner, i.e.
`secondCase_psl2_fitting_innerAction` holds.  The pointwise conjugation
compatibility `SecondCasePSL2ActionData.action_eq` identifies the quotient
action of `ad.f m` with conjugation by `m` on `E / Z(E)`, and the
`PSL₂(K)`-layer elements act on `PSL₂(K)` by ordinary conjugation
(`pGammaL2ToMulAutPSL2_inl` + `pgl2InnerAutPSL2_toPGL`). -/
public theorem secondCase_psl2_innerAction_of_image_in_pslRange
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K)
    (F : Subgroup G) (hFleM : F ≤ w.M)
    (himage : ∀ f : G, (hf : f ∈ F) →
      ad.f ⟨f, hFleM hf⟩ ∈ pGammaL2PSLRange K) :
    secondCase_psl2_fitting_innerAction d K ad F hFleM := by
  classical
  intro f hf
  let α : d.E ≃* d.E := conjOnEquiv d.E w.M f (hFleM hf) d.E_normal
  have hα : ∀ x : d.E, α x =
      ⟨f * (x : G) * f⁻¹, d.E_normal.2 f (hFleM hf) (x : G) x.2⟩ := by
    intro x
    rfl
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  have h2 : MulAut.congr ad.modelEquiv.some (quotientCenterAutomorphism d.E α) =
      pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree
        (ad.f ⟨f, hFleM hf⟩) := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ : ∃ x : d.E, ad.modelEquiv.some (q x) = z := by
      obtain ⟨y, hy⟩ :=
        (QuotientGroup.mk'_surjective (Subgroup.center d.E))
          (ad.modelEquiv.some.symm z)
      refine ⟨y, ?_⟩
      calc
        ad.modelEquiv.some (q y) =
            ad.modelEquiv.some (ad.modelEquiv.some.symm z) := congrArg ad.modelEquiv.some hy
        _ = z := by simp
    change ad.modelEquiv.some
        ((quotientCenterAutomorphism d.E α)
          (ad.modelEquiv.some.symm (ad.modelEquiv.some (q x)))) =
      pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree
        (ad.f ⟨f, hFleM hf⟩) (ad.modelEquiv.some (q x))
    rw [ad.modelEquiv.some.symm_apply_apply]
    rw [quotientCenterAutomorphism_apply_mk]
    rw [hα]
    rw [ad.action_eq ⟨f, hFleM hf⟩ x]
  rcases (mem_pGammaL2PSLRange_iff K (ad.f ⟨f, hFleM hf⟩)).mp (himage f hf) with ⟨a, ha⟩
  have h1 : pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree
      (SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K) a)) =
      MulAut.conj a := by
    rw [pGammaL2ToMulAutPSL2_inl]
    exact pgl2InnerAutPSL2_toPGL K ad.primePower ad.fieldCardGtThree a
  refine ⟨α, hα, ⟨a, ?_⟩⟩
  rw [← ha] at h2
  exact h2.trans h1

/-! ## Odd elements of the field-projection kernel lie in the PSL₂ layer -/

/-- An odd-order element of the field-projection kernel of a subgroup of
`PΓL₂(K)` lies in the canonical `PSL₂(K)` layer: the kernel consists of
projective-linear elements, and the `PGL₂(K)` layer modulo the `PSL₂(K)`
layer has order two.  This upgrades the weak-field-projection conclusion
(`N ≤ pGammaL2LinearKernel K A`) to the inner-action hypothesis
(`N ≤ pGammaL2PSLRange K`) for odd `N`. -/
public theorem pGammaL2_linearKernel_odd_order_mem_pslRange
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (A : Subgroup (PGammaL2 K))
    {x : PGammaL2 K} (hxA : x ∈ A)
    (hker : (⟨x, hxA⟩ : A) ∈ pGammaL2LinearKernel K A)
    (hodd : Odd (orderOf x)) :
    x ∈ pGammaL2PSLRange K := by
  classical
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
  let R : Subgroup (PGL2 K) := toPGL.range
  have hright : SemidirectProduct.rightHom x = 1 := by
    have h := (mem_pGammaL2LinearKernel_iff K A ⟨x, hxA⟩).mp hker
    simpa [pGammaL2FieldProjection] using h
  have hxPGL : x ∈ pGammaL2PGLRange K := by
    rw [pGammaL2PGLRange]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact hright
  let xH : pGammaL2PGLRange K := ⟨x, hxPGL⟩
  let z : PGL2 K := (pGammaL2PGLRangeEquiv K).symm xH
  have hxeq : x = SemidirectProduct.inl z := by
    have hz : (pGammaL2PGLRangeEquiv K) z = xH :=
      (pGammaL2PGLRangeEquiv K).apply_symm_apply xH
    have hc : (xH : PGammaL2 K) = SemidirectProduct.inl z := by
      have hc0 := congrArg Subtype.val hz.symm
      simpa [pGammaL2PGLRangeEquiv_coe] using hc0
    simpa using hc
  have hord : orderOf z = orderOf x := by
    have h3 : orderOf xH = orderOf z := by
      rw [← (pGammaL2PGLRangeEquiv K).apply_symm_apply xH]
      exact (pGammaL2PGLRangeEquiv K).orderOf_eq z
    have h4 : orderOf x = orderOf xH := by
      change orderOf ((pGammaL2PGLRange K).subtype xH) = orderOf xH
      exact orderOf_injective (pGammaL2PGLRange K).subtype
        (pGammaL2PGLRange K).subtype_injective xH
    rw [h4, h3]
  have hzodd : Odd (orderOf z) := by
    simpa [hord] using hodd
  have hRindex : R.index = 2 := pgl2_psl2Range_index_eq_two K hK
  have : R.Normal := Subgroup.normal_of_index_eq_two hRindex
  let q : PGL2 K →* PGL2 K ⧸ R := QuotientGroup.mk' R
  have hdvd2 : orderOf (q z) ∣ 2 := by
    have hcard : Nat.card (PGL2 K ⧸ R) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hRindex
    have hdvd : orderOf (q z) ∣ Nat.card (PGL2 K ⧸ R) :=
      orderOf_dvd_natCard (q z)
    simpa [hcard] using hdvd
  have hoddq : Odd (orderOf (q z)) :=
    Odd.of_dvd_nat hzodd (orderOf_map_dvd q z)
  have hq1 : q z = 1 := by
    rcases hoddq with ⟨k, hk⟩
    rw [hk] at hdvd2
    have hle : 2 * k + 1 ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd2
    have hk0 : k = 0 := by omega
    have hord1 : orderOf (q z) = 1 := by
      rw [hk, hk0]
      norm_num
    exact (orderOf_eq_one_iff (x := q z)).1 hord1
  have hzR : z ∈ R := (QuotientGroup.eq_one_iff (N := R) z).mp hq1
  rcases MonoidHom.mem_range.mp hzR with ⟨a, ha⟩
  rw [← ha] at hxeq
  rw [hxeq]
  exact (mem_pGammaL2PSLRange_iff K (SemidirectProduct.inl (toPGL a))).mpr ⟨a, rfl⟩

/-! ## Equation (4), first half: `F` centralizes the component -/

/-- The PSL₂ equation-(4) component-centralization endpoint: the
equation-(3) fixed part `F` centralizes the selected component `d.E`.

The argument is the inner-reflection route of
`secondCase_psl2_odd_subgroup_centralizes_component_of_inner_reflection`:
`F` is odd (it lies in the odd core `U`), centralizes the distinguished
involution `t` (it lies in `U ≤ H = C_G(t)`) and the reflected-torus
involution `s` (equation (3)); the torus data `T`/`hTinv`/`hTcontain` and
the inner-action endpoint `hinner` then force `F` to centralize `d.E`.

The distinguished involution is the central rotation of the dihedral Sylow
subgroup: `hrefl` supplies `s ∈ S \ S0`, from which `s` is an involution,
`t ≠ s` (as `t ∈ S0`), and `t` commutes with `s` (as `t` is central in
`S`, `centralizerSetup_S_le_H`). -/
public theorem secondCase_psl2_fitting_centralizes_component
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (F : Subgroup G)
    (hFleFU : F ≤ fittingSubgroupOf c.U) (hFleM : F ≤ w.M)
    (s : d.E) (hrefl : c.IsReflection (s : G))
    (hFcentS : F ≤ Subgroup.centralizer ({(s : G)} : Set G))
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hTinv : ∀ x : d.E ⧸ Subgroup.center d.E, x ∈ T →
      QuotientGroup.mk' (Subgroup.center d.E) s * x *
        (QuotientGroup.mk' (Subgroup.center d.E) s)⁻¹ = x⁻¹)
    (hTcontain : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({(QuotientGroup.mk' (Subgroup.center d.E)
            ⟨c.t, d.t_mem_E⟩)} : Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K)
    (hinner : secondCase_psl2_fitting_innerAction d K ad F hFleM) :
    F ≤ Subgroup.centralizer (d.E : Set G) := by
  classical
  let tE : d.E := ⟨c.t, d.t_mem_E⟩
  have hFodd : Odd (Nat.card F) := by
    have hUodd : Odd (Nat.card c.U) := by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H
    exact Odd.of_dvd_nat hUodd
      (Subgroup.card_dvd_of_le (hFleFU.trans (fittingSubgroupOf_le c.U)))
  have hsIG : IsInvolution (s : G) :=
    centralizerSetup_reflection_isInvolution c hrefl
  have hts : tE ≠ s := by
    intro h
    apply hrefl.2
    have hval : c.t = (s : G) := congrArg Subtype.val h
    rw [← hval]
    exact c.t_mem_S0
  have htsComm : Commute (tE : d.E) (s : d.E) := by
    apply Subtype.ext
    change c.t * (s : G) = (s : G) * c.t
    have hsS : (s : G) ∈ (c.S : Subgroup G) := hrefl.1
    have hsH : (s : G) ∈ c.H := centralizerSetup_S_le_H c hsS
    have hsC : (s : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact hsH
    exact (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have hFcentT : F ≤ Subgroup.centralizer ({c.t} : Set G) := by
    intro f hf
    have hfU : f ∈ c.U := hFleFU.trans (fittingSubgroupOf_le c.U) hf
    have hfH : f ∈ c.H := (Subgroup.map_subtype_le (pPrimeCore 2 c.H)) hfU
    rw [c.H_eq_centralizer] at hfH
    exact hfH
  exact secondCase_psl2_odd_subgroup_centralizes_component_of_inner_reflection
    d.E w.M F d.E_component d.E_normal hFleM hFodd
    tE s c.t_involution hsIG hts htsComm d.center_odd
    (by simpa [tE] using hFcentT) hFcentS T hTinv hTcontain
    K ad.primePower ad.modelEquiv hinner

/-! ## Equation (4), second half: `F ◁ M` -/

/-- The PSL₂ equation-(4) package, mirroring
`secondCase_a7_fitting_equation4`: the equation-(3) fixed part `F` is
central in the selected component and normal in the maximal subgroup.

Given the component centralization `F ≤ C_G(d.E)` (the previous theorem),
`F ≤ C_M(t)` is normalized by the local involution centralizer
`C_G(t) ∩ M` (because `F(U)` is characteristic in `U ◁ H`), and the
factorization `M = E·C_M(t)` (`secondCase_M_eq_component_sup_centralizer`)
makes `F` normal in `M` via
`secondCase_fitting_normal_in_M_of_centralizes_component`. -/
public theorem secondCase_psl2_fitting_equation4
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (F : Subgroup G)
    (hFleFU : F ≤ fittingSubgroupOf c.U) (hFleM : F ≤ w.M)
    (s : d.E) (hrefl : c.IsReflection (s : G))
    (hFcentS : F ≤ Subgroup.centralizer ({(s : G)} : Set G))
    (hF_eq : F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G))
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hTinv : ∀ x : d.E ⧸ Subgroup.center d.E, x ∈ T →
      QuotientGroup.mk' (Subgroup.center d.E) s * x *
        (QuotientGroup.mk' (Subgroup.center d.E) s)⁻¹ = x⁻¹)
    (hTcontain : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({(QuotientGroup.mk' (Subgroup.center d.E)
            ⟨c.t, d.t_mem_E⟩)} : Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K)
    (hinner : secondCase_psl2_fitting_innerAction d K ad F hFleM) :
    IsNormalIn F w.M := by
  have hFcentE := secondCase_psl2_fitting_centralizes_component
    c w d F hFleFU hFleM s hrefl hFcentS T hTinv hTcontain K ad hinner
  have hU_normalH : IsNormalIn c.U c.H := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
    · intro h hh x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
      have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈
          pPrimeCore 2 c.H :=
        (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
          p hp (⟨h, hh⟩ : c.H)
      exact Subgroup.mem_map.mpr
        ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩
  have hFUnormalH : IsNormalIn (fittingSubgroupOf c.U) c.H := by
    change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.H
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := fittingSubgroup (↥c.U)) (hKchar := by infer_instance)
      (hHnormal := hU_normalH)
  have hUleH : c.U ≤ c.H := by
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hFleC : F ≤ Subgroup.centralizer ({c.t} : Set G) ⊓ w.M := by
    intro f hf
    have hfH : f ∈ c.H := hUleH
      (fittingSubgroupOf_le c.U (hFleFU hf))
    rw [c.H_eq_centralizer] at hfH
    exact ⟨hfH, hFleM hf⟩
  have hFnormalC : IsNormalIn F
      (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M) := by
    refine ⟨hFleC, ?_⟩
    intro z hz f hf
    have hzH : z ∈ c.H := by
      rw [c.H_eq_centralizer]
      exact hz.1
    have hzM : z ∈ w.M := hz.2
    have hfFU : f ∈ fittingSubgroupOf c.U := hFleFU hf
    have hfM : f ∈ w.M := hFleM hf
    have hconjFU : z * f * z⁻¹ ∈ fittingSubgroupOf c.U :=
      hFUnormalH.2 z hzH f hfFU
    have hconjM : z * f * z⁻¹ ∈ w.M :=
      w.M.mul_mem (w.M.mul_mem hzM hfM) (w.M.inv_mem hzM)
    have hconjY : z * f * z⁻¹ ∈ fittingSubgroupOf c.U ⊓ w.M :=
      ⟨hconjFU, hconjM⟩
    have hconjCentE : z * f * z⁻¹ ∈
        Subgroup.centralizer (d.E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : z⁻¹ * e * z ∈ d.E :=
        by simpa using d.E_normal.2 z⁻¹ (w.M.inv_mem hzM) e he
      have hfe : f * (z⁻¹ * e * z) = (z⁻¹ * e * z) * f :=
        (Subgroup.mem_centralizer_iff.mp (hFcentE hf))
          (z⁻¹ * e * z) he' |>.symm
      calc
        e * (z * f * z⁻¹) = z * ((z⁻¹ * e * z) * f) * z⁻¹ := by group
        _ = z * (f * (z⁻¹ * e * z)) * z⁻¹ := by rw [hfe]
        _ = (z * f * z⁻¹) * e := by group
    have hconjS : z * f * z⁻¹ ∈
        Subgroup.centralizer ({(s : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hconjCentE) (s : G) s.2).symm
    rw [hF_eq]
    exact Subgroup.mem_inf.mpr ⟨hconjY, hconjS⟩
  exact secondCase_fitting_normal_in_M_of_centralizes_component
    c w d F hFleC hFnormalC hFcentE

/-! ## The semilinear field-projection core: precise route

The only remaining step between the action data and the equation-(4)
endpoint is producing `secondCase_psl2_fitting_innerAction` from
`SecondCasePSL2ActionData` alone.  The route, following the task file
(`tasks/gw-section4.md`, R15) and the generic core
`pGammaL2_weak_normal_nilpotent_odd_fieldProjection_trivial`, is:

1. **The squeezed involution centralizer.**  Put `C := C_G(c.t) ⊓ w.M`,
   `A := C.map ad.f`, `τ := ad.f ⟨c.t, d.E_component.1 d.t_mem_E⟩`.
   `secondCase_psl2_hAcont` supplies `τ ∈ pGammaL2PSLRange K`,
   `A ≤ C(τ)` and `C(τ) ⊓ pGammaL2PSLRange K ≤ A`.  `τ` is an involution:
   it is the image of the involution `t` under `ad.f`, and `t ∉ ker f`
   (the odd kernel meets the quasisimple `E` in the odd center
   `Z(E)`, while `t` is an involution).

2. **The odd nilpotent Fitting image.**  `Y := fittingSubgroupOf c.U ⊓ w.M`
   is normal in `C` (the Fitting subgroup of `U = O₂′(H)` is characteristic
   in the normal subgroup `U` of `H`, and `C ≤ H`), nilpotent (it lies in
   the nilpotent `F(U)`), and odd (it lies in `U`).  Hence
   `N := Y.map ad.f` is a normal nilpotent odd subgroup of `A`.

3. **The weak field projection.**  Apply
   `pGammaL2_weak_normal_nilpotent_odd_fieldProjection_trivial K hK hcard
   A τ ... N ...` to conclude `N ≤ pGammaL2LinearKernel K A`, then
   `pGammaL2_linearKernel_odd_order_mem_pslRange` (proved above) upgrades
   this to `N ≤ pGammaL2PSLRange K` because `N` is odd.  Since
   `F ≤ Y` (from `hF_eq` and `hFleFU`), this gives the `himage` hypothesis
   of `secondCase_psl2_innerAction_of_image_in_pslRange`.

   The weak lemma's remaining hypotheses are the torus package:

   * `U` — the PSL rotation torus through `τ`, transported from the
     quotient torus `T` of `SecondCasePSL2QuotientTorusCard` by
     `ad.modelEquiv.some` followed by `SemidirectProduct.inl ∘ toPGL`:
     `U := (T.map ad.modelEquiv.some.toMonoidHom).map
       (SemidirectProduct.inl.comp (Matrix.ProjectiveSpecialLinearGroup.toPGL
         (n := Fin 2) (R := K)))`.  Then `|U| = |T|` is `(q ± 1)/2`
     (`SecondCasePSL2QuotientTorusCard.T_card`), `U` is cyclic, `τ ∈ U`
     (`T_contains_t`), hence `U ≤ C(τ) ⊓ pslRange` (`hUleC`), and
     `|C(τ)| = 2|U|` (`SecondCasePSL2QuotientTorusCard.T_centralizer_card`
     transported through `ad.modelEquiv.some` and `inl`, as in
     `secondCase_psl2_centralizer_index`).
   * `U0` — the normal `p`-complement of `U` in `A` (the `p′` part of the
     cyclic `U`), with `|U0| = (|U|).divMaxPow p`
     (`normalPComplement_card_eq_divMaxPow`), `hU0cop`,
     `hU0quot : IsPGroup p (↥U ⧸ U0.subgroupOf U)`.
   * `p`, `σ`, `P` — a prime divisor `p` of the order of a nontrivial field
     projection of an element of `N` (the case `N ⊄ linearKernel`), `σ` of
     order `p` in `Aut(K)`, and the `p`-Sylow `P` of `F(A)` containing the
     `p`-part of that element; `r := |Fix σ|` with `|K| = r^p`,
     `3 ≤ r` (`finiteField_primeOrder_fixedSubfield_data`).
   * `hU0fixed` — the split/nonsplit fixed-field divisibility transport:
     for the `σ`-element `a₀ ∈ P` fixing `U0` pointwise,
     `|U0| ∣ (r ∓ 1)/2` in the split case via
     `pGammaL2_splitTorus_semilinearConjugate_fixedSubfield` (the `B ≤ Kˣ`
     preimage of `U0` in the standard split torus, conjugated to `U` by a
     projective element), and in the nonsplit case via the nonsplit
     analogue assembled from `pGammaL2_pureField_innerNonsplitTorus_fixedSubfield`.

   The two genuinely missing transport sublemmas are:
   (T1) the derivation of `p`, `σ`, and the `σ`-element `a₀ ∈ P` (the
        `p`-Sylow of `F(A)`) from a nontrivial field projection of `N`;
   (T2) `U ◁ A` from the uniqueness of the order-`|U|` cyclic subgroup in
        the dihedral centralizer `C(τ)` of order `2|U|` (the
        `torus_centralizer_card_of_reflected` structure transported through
        `ad.modelEquiv.some`).
   Together with the fixed-field transport (the `hU0fixed` clause above,
   split half already landed as
   `pGammaL2_splitTorus_semilinearConjugate_fixedSubfield`), these close
   the equation-(4) producer; nothing downstream of
   `secondCase_psl2_fitting_innerAction` is missing.
-/

end CFSG.GorensteinWalter
