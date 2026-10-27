module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Residual
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Local
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary713
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem2

namespace CFSG
end CFSG
open CFSG

/-!
# Induction infrastructure for Proposition 8.2(a)

This module currently contains the source-facing cardinality and residual
transport lemmas used by the strong induction.  The final induction theorem
is kept below these small facts so that the selected-point normalizer step can
be audited independently.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open External
open scoped Pointwise

universe u

/-- Enlarging a subgroup can only shrink its fixed-point set. -/
public theorem proposition82_fixedPoints_card_le_of_le
    {X : Type u} [Group X] [Finite X]
    {M A B : Subgroup X} (hAB : A ≤ B) :
    Nat.card (theorem4bFixedPoints M B) ≤
      Nat.card (theorem4bFixedPoints M A) := by
  let f : theorem4bFixedPoints M B → theorem4bFixedPoints M A :=
    fun omega =>
      ⟨omega.1, fun a ha => omega.2 a (hAB ha)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : theorem4bFixedPoints M A => (z : conjugateCosetSpace M)) hxy
  exact Nat.card_le_card_of_injective f hf

/-- The selected base coset is fixed by every subgroup of `M`. -/
public theorem proposition82_base_fixed_of_le
    {X : Type u} [Group X] [Finite X] {M A : Subgroup X}
    (hAM : A ≤ M) :
    (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) A :=
  theorem4b_baseCoset_mem_fixedPoints hAM

/-- A subgroup of a two-point stabilizer has odd order. -/
public theorem proposition82_odd_card_of_le_twoPointStabilizer
    {X : Type u} [Group X] [Finite X]
    {M A : Subgroup X} {beta gamma : conjugateCosetSpace M}
    (hM : IsStronglyEmbedded M)
    (hneq : beta ≠ gamma)
    (hA : A ≤ MulAction.stabilizer X beta ⊓
      MulAction.stabilizer X gamma) :
    Odd (Nat.card A) := by
  apply odd_of_card_dvd (twoPointStabilizer_card_odd
    (hunique := fun {u} hu {a b} ha hb =>
      (hM.involution_fixed_coset_unique hu).unique ha hb) hneq)
  exact Subgroup.card_dvd_of_le hA

private theorem proposition82_natCard_rightConjugate
    {X : Type u} [Group X] (Y : Subgroup X) (g : X) :
    Nat.card (rightConjugate Y g) = Nat.card Y := by
  rw [rightConjugate, Subgroup.conjBy]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective Y
      (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.toEquiv

/-- A smaller-cardinality base-point induction hypothesis transports to every
fixed point of the smaller subgroup. -/
private theorem proposition82aConclusion_of_base_lt
    {X : Type u} [Group X] [Finite X] {M : Subgroup X} {n : ℕ}
    (hbase : ∀ (A : Subgroup X), Nat.card A < n → A ≤ M →
      3 ≤ Nat.card (theorem4bFixedPoints M A) →
        ∃ u : X, u ∈ M ∧ IsInvolution u ∧
          A ≤ Subgroup.centralizer ({u} : Set X))
    {Y : Subgroup X} (hYlt : Nat.card Y < n) :
    Proposition82aConclusion M Y := by
  intro omega homega hfixed
  rcases QuotientGroup.mk_surjective omega with ⟨g, rfl⟩
  let Yg : Subgroup X := rightConjugate Y g
  have hYStab : Y ≤ MulAction.stabilizer X
      (QuotientGroup.mk g : conjugateCosetSpace M) := by
    intro y hyY
    exact MulAction.mem_stabilizer_iff.mpr (homega y hyY)
  have hYStab' : Y ≤ rightConjugate M g⁻¹ := by
    simpa [conjugateCoset_stabilizer] using hYStab
  have hYgM : Yg ≤ M := by
    intro x hx
    dsimp [Yg] at hx
    rcases hx with ⟨y, hyY, rfl⟩
    simpa [rightConjugateElem] using
      (rightConjugateElem_mem_of_mem_rightConjugate (hYStab' hyY))
  have hcardEq :
      Nat.card (theorem4bFixedPoints M Yg) =
        Nat.card (theorem4bFixedPoints M Y) :=
    Nat.card_congr (theorem4bFixedPoints_rightConjugateEquiv M Y g)
  have hfixedYg : 3 ≤ Nat.card (theorem4bFixedPoints M Yg) := by
    rw [hcardEq]
    exact hfixed
  have hYglt : Nat.card Yg < n := by
    rw [proposition82_natCard_rightConjugate]
    exact hYlt
  obtain ⟨u, huM, hu, hcentral⟩ :=
    hbase Yg hYglt hYgM hfixedYg
  let ug : X := rightConjugateElem u g⁻¹
  refine ⟨ug, ?_, isInvolution_rightConjugateElem hu, ?_⟩
  · rw [conjugateCoset_stabilizer]
    exact rightConjugateElem_mem_rightConjugate huM
  · intro y hyY
    have hyConj : rightConjugateElem y g ∈ Yg :=
      rightConjugateElem_mem_rightConjugate hyY
    have hcomm : rightConjugateElem y g * u =
        u * rightConjugateElem y g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcentral hyConj)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm' := congrArg (fun z : X => g * z * g⁻¹) hcomm
    simpa [ug, rightConjugateElem, mul_assoc] using hcomm'

private theorem proposition82_odd_card_of_three_fixed_of_le
    {X : Type u} [Group X] [Finite X] {M Y : Subgroup X}
    (hM : IsStronglyEmbedded M) (hYM : Y ≤ M)
    (hfixed : 3 ≤ Nat.card (theorem4bFixedPoints M Y)) :
    Odd (Nat.card Y) := by
  have hnontrivial : Nontrivial (theorem4bFixedPoints M Y) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial (theorem4bFixedPoints M Y) := hnontrivial
  let base : theorem4bFixedPoints M Y :=
    ⟨QuotientGroup.mk 1, theorem4b_baseCoset_mem_fixedPoints hYM⟩
  obtain ⟨beta, hbeta⟩ := exists_ne base
  have hne : (base : conjugateCosetSpace M) ≠
      (beta : conjugateCosetSpace M) := by
    intro h
    apply hbeta
    apply Subtype.ext
    exact h.symm
  apply proposition82_odd_card_of_le_twoPointStabilizer hM hne
  intro y hyY
  exact ⟨MulAction.mem_stabilizer_iff.mpr (base.property y hyY),
    MulAction.mem_stabilizer_iff.mpr (beta.property y hyY)⟩

/-- The residual and Sylow factors selected in a subgroup of odd order can be
embedded back into the ambient group without changing their cardinalities. -/
public structure Proposition82AmbientResidualData
    {X : Type u} [Group X] [Finite X]
    (Y : Subgroup X) where
  p : ℕ
  p_prime : p.Prime
  p_odd : Odd p
  W : Subgroup X
  R : Subgroup X
  W_le_Y : W ≤ Y
  R_le_Y : R ≤ Y
  W_ne_Y : W ≠ Y
  W_card_lt : Nat.card W < Nat.card Y
  R_isPGroup : IsPGroup p R
  R_normalizes_W : R ≤ Subgroup.normalizer (W : Set X)
  sup_eq_Y : W ⊔ R = Y

/-- Map the selected residual/Sylow data from `Y` into the ambient group. -/
public theorem proposition82AmbientResidualData_of_subgroup
    {X : Type u} [Group X] [Finite X]
    {Y : Subgroup X}
    (hYodd : Odd (Nat.card Y)) (hYsolv : Group.IsSolvable Y)
    (hYne : Y ≠ ⊥) :
    Nonempty (Proposition82AmbientResidualData Y) := by
  letI : Group.IsSolvable Y := hYsolv
  letI : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot (H := Y)).2 hYne
  obtain ⟨d⟩ := proposition82ResidualData_nonempty_of_odd
    (Y := Y) hYodd
  let W0 : Subgroup Y := hktPResidual d.p Y
  let R0 : Subgroup Y := (d.R : Subgroup Y)
  let W : Subgroup X := W0.map Y.subtype
  let R : Subgroup X := R0.map Y.subtype
  have hWle : W ≤ Y := by
    simpa [W] using Subgroup.map_le_range Y.subtype W0
  have hRle : R ≤ Y := by
    simpa [R] using Subgroup.map_le_range Y.subtype R0
  have hWne : W ≠ Y := by
    intro h
    have htopmap : (⊤ : Subgroup Y).map Y.subtype = Y := by
      simpa [MonoidHom.range_eq_map] using
        (Subgroup.range_subtype (H := Y))
    have hW0top : W0 = ⊤ := by
      apply Subgroup.map_injective Y.subtype_injective
      exact (show W0.map Y.subtype = (⊤ : Subgroup Y).map Y.subtype by
        simpa [W, htopmap] using h)
    exact d.residual_ne_top (by simpa [W0] using hW0top)
  have hWcard : Nat.card W < Nat.card Y :=
    natCard_lt_of_subgroup_lt (lt_of_le_of_ne hWle hWne)
  letI : W0.Normal := by
    simpa [W0] using (hktPResidual_normal (Q := Y) (q := d.p))
  have hRpg : IsPGroup d.p R := by
    exact d.R.isPGroup'.map Y.subtype
  have hRnorm : R ≤ Subgroup.normalizer (W : Set X) := by
    intro r hr
    rcases Subgroup.mem_map.mp hr with ⟨r0, hr0, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rcases Subgroup.mem_map.mp hw with ⟨w0, hw0, rfl⟩
      have hconj : (r0 : Y) * (w0 : Y) * (r0 : Y)⁻¹ ∈ W0 :=
        (inferInstance : W0.Normal).conj_mem (w0 : Y) hw0 (r0 : Y)
      exact Subgroup.mem_map.mpr ⟨r0 * w0 * r0⁻¹, hconj, rfl⟩
    · intro hw
      rcases Subgroup.mem_map.mp hw with ⟨w0, hw0, hwEq⟩
      have hback : (r0 : Y)⁻¹ * (w0 : Y) * ((r0 : Y)⁻¹)⁻¹ ∈ W0 :=
        (inferInstance : W0.Normal).conj_mem (w0 : Y) hw0 (r0 : Y)⁻¹
      apply Subgroup.mem_map.mpr
      refine ⟨r0⁻¹ * w0 * (r0⁻¹)⁻¹, hback, ?_⟩
      have hwEq' := congrArg (fun x : X => (r0 : X)⁻¹ * x * (r0 : X)) hwEq
      simpa [mul_assoc] using hwEq'
  have hsup : W ⊔ R = Y := by
    calc
      W ⊔ R = (W0 ⊔ R0).map Y.subtype := by
        simp [W, R, Subgroup.map_sup]
      _ = (⊤ : Subgroup Y).map Y.subtype := by
        rw [show W0 ⊔ R0 = ⊤ by
          simpa [W0, R0] using d.residual_sup_sylow]
      _ = Y := by
        simpa [MonoidHom.range_eq_map] using
          (Subgroup.range_subtype (H := Y))
  exact ⟨{
    p := d.p
    p_prime := d.p_prime
    p_odd := d.p_odd
    W := W
    R := R
    W_le_Y := hWle
    R_le_Y := hRle
    W_ne_Y := hWne
    W_card_lt := hWcard
    R_isPGroup := hRpg
    R_normalizes_W := hRnorm
    sup_eq_Y := hsup
  }⟩

/-- The inductive residual subgroup supplies the source orbit and the strong
embedding of its point stabilizer. -/
public theorem proposition82_residual_orbit_data
    {X : Type u} [Group X] [Finite X] {M W R : Subgroup X}
    (hWM : W ≤ M)
    (hRnorm : R ≤ Subgroup.normalizer (W : Set X))
    (h82b : Proposition82bConclusion M W)
    (hfixedW : 3 ≤ Nat.card (theorem4bFixedPoints M W)) :
    ∃ F : Subgroup X,
      F = Subgroup.centralizer (W : Set X) ⊔ R ∧
      IsTransitiveOn F
        (fixedPointsOfSubgroup X (conjugateCosetSpace M) W) ∧
      (∀ omega : conjugateCosetSpace M,
        omega ∈ fixedPointsOfSubgroup X
          (conjugateCosetSpace M) W →
        InOrbit F (QuotientGroup.mk 1) omega) ∧
      (∀ omega : conjugateCosetSpace M,
        InOrbit F (QuotientGroup.mk 1) omega →
        omega ∈ fixedPointsOfSubgroup X
          (conjugateCosetSpace M) W) ∧
      (∀ omega : conjugateCosetSpace M,
        omega ∈ fixedPointsOfSubgroup X
          (conjugateCosetSpace M) W →
        IsStronglyEmbedded (pointStabilizerIn F omega)) := by
  let C : Subgroup X := Subgroup.centralizer (W : Set X)
  let F : Subgroup X := C ⊔ R
  have hCnorm : C ≤ Subgroup.normalizer (W : Set X) := by
    simpa [C] using centralizer_le_normalizer W
  have hFnorm : F ≤ Subgroup.normalizer (W : Set X) := by
    exact sup_le hCnorm hRnorm
  have hcore : involutionCoreIn C ≤ F := by
    exact (involutionCoreIn_le C).trans le_sup_left
  obtain ⟨htrans, hstrong⟩ := h82b F hcore hFnorm hfixedW
  have hbase : (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) W :=
    theorem4b_baseCoset_mem_fixedPoints hWM
  have horbitForward : ∀ omega : conjugateCosetSpace M,
      omega ∈ fixedPointsOfSubgroup X
        (conjugateCosetSpace M) W → InOrbit F
          (QuotientGroup.mk 1) omega := by
    intro omega homega
    obtain ⟨f, hf⟩ := htrans hbase homega
    exact ⟨f, hf⟩
  have horbitBackward : ∀ omega : conjugateCosetSpace M,
      InOrbit F (QuotientGroup.mk 1) omega →
      omega ∈ fixedPointsOfSubgroup X
        (conjugateCosetSpace M) W := by
    intro omega horbit
    rcases horbit with ⟨f, hf⟩
    rw [← hf]
    exact fixedPoints_smul_of_mem_normalizer (hFnorm f.property) hbase
  exact ⟨F, rfl, htrans, horbitForward, horbitBackward,
    fun omega homega => hstrong omega homega⟩

/-- Unpack the involution supplied by strong embedding of a point stabilizer
inside a subgroup of the ambient action. -/
public theorem proposition82_exists_involution_of_pointStabilizerStrong
    {X : Type u} [Group X] [Finite X] {M F : Subgroup X}
    {omega : conjugateCosetSpace M}
    (hstrong : IsStronglyEmbedded (pointStabilizerIn F omega)) :
    ∃ u : X, u ∈ F ⊓ MulAction.stabilizer X omega ∧ IsInvolution u := by
  obtain ⟨u0, hu0, hu0Inv⟩ := hstrong.exists_involution
  let u : X := u0
  have huF : u ∈ F := u0.property
  have huStab : u ∈ MulAction.stabilizer X omega := hu0
  have huInv : IsInvolution u :=
    IsInvolution.map_of_injective hu0Inv F.subtype Subtype.val_injective
  exact ⟨u, ⟨huF, huStab⟩, huInv⟩

/-- Assemble the proper-subgroup branch of the source local normalizer step.
The solvable and Borel alternatives are discharged by the local Proposition
8.2 lemmas. -/
public theorem proposition82_proper_local_normalizer
    {X : Type u} [Group X] [Finite X] {M W F P : Subgroup X}
    (hM : IsStronglyEmbedded M) (hXsimple : IsSimpleGroup X)
    (h4b : Theorem4bAtBase M)
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    (hWnebot : W ≠ ⊥) (hWM : W ≤ M)
    (hFleN : F ≤ Subgroup.normalizer (W : Set X))
    (hFtrans : IsTransitiveOn F
      (fixedPointsOfSubgroup X (conjugateCosetSpace M) W))
    (hP : P ≤ F ⊓ M)
    (hPthree : 3 ≤ Nat.card
      {omega : conjugateCosetSpace M //
        InOrbit F (QuotientGroup.mk 1 : conjugateCosetSpace M) omega ∧
          omega ∈ fixedPointsOfSubgroup X
            (conjugateCosetSpace M) P})
    (hstrong : IsStronglyEmbedded
      (pointStabilizerIn F
        (QuotientGroup.mk 1 : conjugateCosetSpace M))) :
    ∃ u : X, u ∈ F ⊓ M ∧ IsInvolution u ∧
      u ∈ Subgroup.normalizer (P : Set X) := by
  have hbaseW : (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) W :=
    theorem4b_baseCoset_mem_fixedPoints hWM
  have hFnotle : ¬ F ≤ M := by
    intro hFM
    have hfixedW : 3 ≤ Nat.card (theorem4bFixedPoints M W) := by
      let f : {omega : conjugateCosetSpace M //
          InOrbit F (QuotientGroup.mk 1 : conjugateCosetSpace M) omega ∧
            omega ∈ fixedPointsOfSubgroup X
              (conjugateCosetSpace M) P} →
          theorem4bFixedPoints M W :=
        fun omega => ⟨omega.1, by
          rcases omega.2.1 with ⟨g, hg⟩
          rw [← hg]
          exact fixedPoints_smul_of_mem_normalizer
            (hFleN g.property)
            hbaseW⟩
      have hf : Function.Injective f := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : theorem4bFixedPoints M W =>
          (z : conjugateCosetSpace M)) hxy
      exact hPthree.trans (Nat.card_le_card_of_injective f hf)
    have hnontrivial : Nontrivial (theorem4bFixedPoints M W) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    letI : Nontrivial (theorem4bFixedPoints M W) := hnontrivial
    let baseW : theorem4bFixedPoints M W :=
      ⟨QuotientGroup.mk 1, hbaseW⟩
    obtain ⟨betaW, hbetaW⟩ := exists_ne baseW
    obtain ⟨f, hf⟩ := hFtrans hbaseW betaW.property
    have hfbase : (f : X) •
        (QuotientGroup.mk 1 : conjugateCosetSpace M) =
          QuotientGroup.mk 1 := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [show MulAction.stabilizer X
          (QuotientGroup.mk 1 : conjugateCosetSpace M) = M by simp]
      exact hFM f.property
    apply hbetaW
    apply Subtype.ext
    exact hf.symm.trans hfbase
  have hNproper : Subgroup.normalizer (W : Set X) ≠ ⊤ :=
    hM.normalizer_ne_top_of_isSimpleGroup_of_ne_bot_of_le
      hXsimple hWnebot hWM
  have hFproper : F ≠ ⊤ := by
    intro hFtop
    apply hNproper
    apply top_unique
    intro x _hx
    apply hFleN
    rw [hFtop]
    exact Subgroup.mem_top x
  obtain ⟨u0, hu0FM, hu0⟩ :=
    proposition82_exists_involution_of_pointStabilizerStrong hstrong
  have hu0FM' : u0 ∈ F ⊓ M := by
    refine ⟨hu0FM.1, ?_⟩
    simpa using hu0FM.2
  have h713 : Corollary713BorelConclusion M F :=
    corollary713_borel_of_source_endpoints M F hM h4b hFnotle hFproper
      hinduction hu0FM' hu0
  obtain ⟨u, huFM, hu, huNorm⟩ :=
    exists_local_normalizer_involution_of_corollary713_borel
      M F P hM hu0FM' hu0 h713 hP hPthree
  exact ⟨u, huFM, hu, huNorm⟩

private theorem proposition82_base_step
    {X : Type u} [Group X] [Finite X] {M Y : Subgroup X}
    (hM : IsStronglyEmbedded M) (hXsimple : IsSimpleGroup X)
    (h4b : Theorem4bAtBase M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    (hsmaller : ∀ (W : Subgroup X), Nat.card W < Nat.card Y →
      Proposition82aConclusion M W)
    (hYM : Y ≤ M)
    (hfixed : 3 ≤ Nat.card (theorem4bFixedPoints M Y)) :
    ∃ u : X, u ∈ M ∧ IsInvolution u ∧
      Y ≤ Subgroup.centralizer ({u} : Set X) := by
  classical
  by_cases hYbot : Y = ⊥
  · obtain ⟨u, huM, hu⟩ := hM.exists_involution
    refine ⟨u, huM, hu, ?_⟩
    rw [hYbot]
    exact bot_le
  have hYne : Y ≠ ⊥ := hYbot
  have hYodd : Odd (Nat.card Y) :=
    proposition82_odd_card_of_three_fixed_of_le hM hYM hfixed
  have hYsolv : Group.IsSolvable Y := odd_order_theorem Y hYodd
  obtain ⟨d⟩ := proposition82AmbientResidualData_of_subgroup
    hYodd hYsolv hYne
  letI : Fact d.p.Prime := ⟨d.p_prime⟩
  have hWM : d.W ≤ M := d.W_le_Y.trans hYM
  have hfixedW : 3 ≤ Nat.card (theorem4bFixedPoints M d.W) := by
    exact hfixed.trans (proposition82_fixedPoints_card_le_of_le d.W_le_Y)
  by_cases hWbot : d.W = ⊥
  · have hYR : Y = d.R := by
      calc
        Y = d.W ⊔ d.R := d.sup_eq_Y.symm
        _ = d.R := by simp [hWbot]
    have hRbase : d.R ≤ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
      simpa [baseCoset_stabilizer] using d.R_le_Y.trans hYM
    let Good : Subgroup X → Prop := fun Q =>
      IsPGroup d.p Q ∧ d.R ≤ Q ∧
        Q ≤ MulAction.stabilizer X
          (QuotientGroup.mk 1 : conjugateCosetSpace M) ∧
        3 ≤ Nat.card (theorem4bFixedPoints M Q)
    have hRgood : Good d.R := by
      refine ⟨d.R_isPGroup, le_rfl, hRbase, ?_⟩
      simpa [hYR] using hfixed
    obtain ⟨P, hRP, hPmax⟩ := Finite.exists_le_maximal hRgood
    have hPp : IsPGroup d.p P := hPmax.1.1
    have hPbase : P ≤ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M) :=
      hPmax.1.2.2.1
    have hPthree : 3 ≤ Nat.card (theorem4bFixedPoints M P) :=
      hPmax.1.2.2.2
    have hmaxThree : ∀ Q : Subgroup X,
        IsPGroup d.p Q →
        Q ≤ MulAction.stabilizer X
          (QuotientGroup.mk 1 : conjugateCosetSpace M) →
        3 ≤ Nat.card (theorem4bFixedPoints M Q) →
        P ≤ Q → Q = P := by
      intro Q hQp hQbase hQthree hPQ
      exact (hPmax.eq_of_le
        ⟨hQp, hPmax.1.2.1.trans hPQ, hQbase, hQthree⟩ hPQ).symm
    have hlocal : ∃ u : X,
        u ∈ MulAction.stabilizer X
            (QuotientGroup.mk 1 : conjugateCosetSpace M) ∧
          IsInvolution u ∧ u ∈ Subgroup.normalizer (P : Set X) := by
      by_cases htwo : ∃ Q : Subgroup X,
          IsPGroup d.p Q ∧
            Nat.card (theorem4bFixedPoints M Q) = 2
      · exact exists_local_normalizer_involution_of_maximal_containing
          hM d.p_prime d.p_odd ((hT2 d.p d.p_prime).1 htwo)
          hPmax
      · exact exists_local_normalizer_involution_of_theorem2_no_exact_two
          hT2 d.p_prime htwo
          (P := P) (QuotientGroup.mk 1 : conjugateCosetSpace M) hPp hPbase
          hPthree hmaxThree
    obtain ⟨u, huBase, hu, huNorm⟩ := hlocal
    have huM : u ∈ M := by
      simpa [baseCoset_stabilizer] using huBase
    have hPodd : Odd (Nat.card P) := by
      obtain ⟨k, hk⟩ := hPp.exists_card_eq
      rw [hk]
      exact d.p_odd.pow
    have hPcentral : P ≤ Subgroup.centralizer ({u} : Set X) :=
      h4b.centralizes_of_three_le_fixedPoints_card
        hu huM hPodd (by simpa [baseCoset_stabilizer] using hPbase)
          huNorm hPthree
    refine ⟨u, huM, hu, ?_⟩
    rw [hYR]
    exact hRP.trans hPcentral
  have h82aW : Proposition82aConclusion M d.W :=
    hsmaller d.W d.W_card_lt
  have h82bW : Proposition82bConclusion M d.W :=
    hM.proposition_8_2_b h82aW
  obtain ⟨F, hF, hFtrans, hOrbitForward, _hOrbitBackward, hstrong⟩ :=
    proposition82_residual_orbit_data hWM d.R_normalizes_W h82bW hfixedW
  have hCnorm : Subgroup.centralizer (d.W : Set X) ≤
      Subgroup.normalizer (d.W : Set X) :=
    centralizer_le_normalizer d.W
  have hFleN : F ≤ Subgroup.normalizer (d.W : Set X) := by
    rw [hF]
    exact sup_le hCnorm d.R_normalizes_W
  have hRFM : d.R ≤ F ⊓ M := by
    intro r hr
    refine ⟨?_, d.R_le_Y.trans hYM hr⟩
    rw [hF]
    exact (le_sup_right : d.R ≤
      Subgroup.centralizer (d.W : Set X) ⊔ d.R) hr
  have hbaseW : (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) d.W :=
    theorem4b_baseCoset_mem_fixedPoints hWM
  have hstrongBase : IsStronglyEmbedded
      (pointStabilizerIn F
        (QuotientGroup.mk 1 : conjugateCosetSpace M)) :=
    hstrong (QuotientGroup.mk 1) hbaseW
  let FixedOrbitR := {omega : conjugateCosetSpace M //
    InOrbit F (QuotientGroup.mk 1 : conjugateCosetSpace M) omega ∧
      omega ∈ fixedPointsOfSubgroup X
        (conjugateCosetSpace M) d.R}
  let f : theorem4bFixedPoints M Y → FixedOrbitR := fun omega =>
    ⟨omega.1, hOrbitForward omega.1
        (fun w hw => omega.2 w (d.W_le_Y hw)),
      fun r hr => omega.2 r (d.R_le_Y hr)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : FixedOrbitR => (z : conjugateCosetSpace M)) hab
  have hRthree : 3 ≤ Nat.card FixedOrbitR := by
    exact hfixed.trans (Nat.card_le_card_of_injective f hf)
  obtain ⟨u, huFM, hu, huNorm⟩ :=
    proposition82_proper_local_normalizer hM hXsimple h4b hinduction
      (by simpa using hWbot) hWM hFleN hFtrans hRFM hRthree hstrongBase
  have hRglobalThree : 3 ≤ Nat.card (theorem4bFixedPoints M d.R) := by
    let g : FixedOrbitR → theorem4bFixedPoints M d.R := fun omega =>
      ⟨omega.1, omega.2.2⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : theorem4bFixedPoints M d.R =>
        (z : conjugateCosetSpace M)) hab
    exact hRthree.trans (Nat.card_le_card_of_injective g hg)
  have hRodd : Odd (Nat.card d.R) := by
    obtain ⟨k, hk⟩ := d.R_isPGroup.exists_card_eq
    rw [hk]
    exact d.p_odd.pow
  have hRcentral : d.R ≤ Subgroup.centralizer ({u} : Set X) :=
    h4b.centralizes_of_three_le_fixedPoints_card
      hu huFM.2 hRodd (d.R_le_Y.trans hYM) huNorm hRglobalThree
  have hRnormC : d.R ≤ Subgroup.normalizer
      (Subgroup.centralizer (d.W : Set X) : Set X) :=
    d.R_normalizes_W.trans (normalizer_le_normalizer_centralizer d.W)
  have huC : u ∈ Subgroup.centralizer (d.W : Set X) := by
    apply sq_eq_one_mem_left_of_sup_isPGroup
      d.p_prime d.p_odd (Subgroup.centralizer (d.W : Set X)) d.R
      d.R_isPGroup hRnormC
    · rw [← hF]
      exact huFM.1
    · exact hu.sq_eq_one
  refine ⟨u, huFM.2, hu, ?_⟩
  rw [← d.sup_eq_Y]
  exact sup_le
    (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp huC w hw))
    hRcentral

/-- Strong induction for the base-point form of Proposition 8.2(a), once the
earlier Theorem 4(b) and proper-subgroup source endpoints are available. -/
public theorem IsStronglyEmbedded.proposition82aAtBase_of_theorem4b
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hXsimple : IsSimpleGroup X)
    (h4b : Theorem4bAtBase M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N) :
    Proposition82aAtBase M := by
  let P : ℕ → Prop := fun n =>
    ∀ (Y : Subgroup X), Nat.card Y = n → Y ≤ M →
      3 ≤ Nat.card (theorem4bFixedPoints M Y) →
      ∃ u : X, u ∈ M ∧ IsInvolution u ∧
        Y ≤ Subgroup.centralizer ({u} : Set X)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Y hcard hYM hfixed
        apply proposition82_base_step hM hXsimple h4b hT2 hinduction
        · intro W hWlt
          apply proposition82aConclusion_of_base_lt (n := n)
            (fun A hAlt hAM hAfixed =>
              ih (Nat.card A) hAlt A rfl hAM hAfixed)
          simpa [hcard] using hWlt
        · exact hYM
        · exact hfixed
  apply Proposition82aAtBase.of_forall
  intro Y hYM hfixed
  exact hP (Nat.card Y) Y rfl hYM hfixed

/-- Source-endpoint wrapper for the Proposition 8.2(a) induction. -/
public theorem IsStronglyEmbedded.proposition82aAtBase_of_source_endpoints
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hXsimple : IsSimpleGroup X)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N) :
    Proposition82aAtBase M := by
  let hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X) :=
    hM.theorem4bProposition63Theorem2
  let h4b : Theorem4bAtBase M :=
    hM.theorem4bAtBase_of_section7 hXsimple hrank hT2 hinduction
  exact hM.proposition82aAtBase_of_theorem4b
    hXsimple h4b hT2 hinduction

end CFSG.BenderSuzuki
