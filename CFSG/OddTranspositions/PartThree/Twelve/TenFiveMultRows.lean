module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultModels
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultHopf
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultDimFive
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultDimFiveSpin
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultDimFivePair
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultCover
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultSpinLift
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultSixMinus
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
public import CFSG.LieType.Steinberg.CentralExt.POmegaMinusMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LieType.Universal.SpinOmega.Kernel

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open CFSG.LieType.Universal.Spin CliffordAlgebra

theorem centralKernelTwoGroup_of_hopfMultiplier {X : Type} [Group X] (hX : commutator X = ⊤)
    {m : ℕ} (hM : Nat.card (griessHopfMultiplier X) ∣ 2 ^ m) : CentralKernelTwoGroup X := by
  intro Γ _ _ φ hφ hcen hcomm
  have hΓ : commutator Γ = ⊤ := by
    rw [eq_top_iff]
    intro γ _
    have h1 : φ γ ∈ (commutator Γ).map φ := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hφ, ← commutator_def, hX]
      exact Subgroup.mem_top _
    obtain ⟨γ', hγ', hγγ'⟩ := h1
    have hk : γ'⁻¹ * γ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hγγ', inv_mul_cancel]
    have e1 : γ = γ' * (γ'⁻¹ * γ) := by group
    rw [e1]
    exact Subgroup.mul_mem _ hγ' (hcomm hk)
  have : Group.IsPerfect Γ := ⟨hΓ⟩
  have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective φ hφ hcen
  have hdvd := Subgroup.card_dvd_of_surjective
    (f := CFSG.RankThree.PerfectCover.hopfMultiplierToKer φ hφ hcen) hsurj
  have hcard : Nat.card (griessHopfMultiplier X) =
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) :=
    Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv
  exact IsPGroup.of_card_dvd_pow (hdvd.trans (hcard ▸ hM))

@[expose] def ModelSpinData {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q₀ : (ι → ZMod 5) → ZMod 5) : Prop :=
  ∃ (U : Type) (_ : Group U) (_ : Finite U) (σ : U →* StatedProj (StatedOmega Q₀))
      (ω : U →* ↥(StatedOmega Q₀)) (z₀ : U),
    commutator U = ⊤ ∧ Function.Surjective σ ∧ σ.ker ≤ Subgroup.center U ∧
    (∀ (E : Type) [Group E] [Finite E] (p : E →* U), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : U →* E, ∀ g, p (s g) = g) ∧
    Nat.card σ.ker ≤ 4 ∧
    Function.Surjective ω ∧ ω.ker = Subgroup.zpowers z₀ ∧ z₀ ≠ 1 ∧ z₀ * z₀ = 1 ∧
    (∀ u, σ u = (QuotientGroup.mk (ω u) : StatedProj (StatedOmega Q₀))) ∧
    (∀ g₀ : ↥(StatedOmega Q₀), IsModelReflectionPair Q₀ (g₀ : GL ι (ZMod 5)) →
      ∃ u : U, ω u = g₀ ∧ u * u = z₀)

theorem modelInvolutionCover_of_spinData {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q₀ : (ι → ZMod 5) → ZMod 5} (h : ModelSpinData Q₀) : ModelInvolutionCover Q₀ := by
  classical
  obtain ⟨U, hUgrp, hUfin, σ, ω, z₀, hUperf, hσsurj, hσker_center, hUclosed, hcardZ,
    hωsurj, hωker, hz₀ne, hz₀sq, hσmk, hcliff⟩ := h
  letI : Group U := hUgrp
  letI : Finite U := hUfin
  intro Γ Γgrp Γfin ρ hρsurj hΓperf hρker_center hcardρ g₀ hrefpair hlift
  letI : Group Γ := Γgrp
  letI : Finite Γ := Γfin
  obtain ⟨x, hx, hxsq⟩ := hlift
  exact modelInvolutionCover_abstract (U := U) (X := StatedProj (StatedOmega Q₀))
    (Ω := ↥(StatedOmega Q₀)) (Γ := Γ) σ ω
    (QuotientGroup.mk' ((StatedScalars ι (ZMod 5)).subgroupOf (StatedOmega Q₀))) z₀
    hUperf hσsurj hωsurj hσmk hσker_center hUclosed hcardZ hωker hz₀ne hz₀sq
    ρ hρsurj hΓperf hρker_center hcardρ g₀ x hx hxsq (hcliff g₀ hrefpair)

set_option backward.isDefEq.respectTransparency false in
theorem modelSpinData_of_spinGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 5) (ι → ZMod 5)} {Q₀ : (ι → ZMod 5) → ZMod 5}
    (hQne : Q ≠ 0) (hR : (spinMatrix Q).range = StatedOmega Q₀)
    (hperf : Group.IsPerfect (spinGroup Q))
    (hkerle : (spinToStatedProj Q hR).ker ≤ Subgroup.center (spinGroup Q))
    (hcard : Nat.card (spinToStatedProj Q hR).ker ≤ 4)
    (hclosed : ∀ (E : Type) [Group E] [Finite E] (p : E →* spinGroup Q),
      Function.Surjective p → p.ker ≤ Subgroup.center E →
      ∃ s : spinGroup Q →* E, ∀ g, p (s g) = g)
    (hkerSet : ((spinMatrix Q).ker : Set (spinGroup Q)) =
      {1, CliffordAlgebra.spinGroup.negOne Q hQne})
    (hne : CliffordAlgebra.spinGroup.negOne Q hQne ≠ 1)
    (hcliff : ∀ g₀ : ↥(StatedOmega Q₀), IsModelReflectionPair Q₀ (g₀ : GL ι (ZMod 5)) →
      ∃ u : spinGroup Q,
        (spinMatrix Q).codRestrict (StatedOmega Q₀) (spinMatrix_mem_of_range_eq Q hR) u = g₀ ∧
        u * u = CliffordAlgebra.spinGroup.negOne Q hQne) : ModelSpinData Q₀ := by
  set z₀ : spinGroup Q := CliffordAlgebra.spinGroup.negOne Q hQne with hz₀
  set ω : spinGroup Q →* ↥(StatedOmega Q₀) :=
    (spinMatrix Q).codRestrict (StatedOmega Q₀) (spinMatrix_mem_of_range_eq Q hR) with hω
  set σ : spinGroup Q →* StatedProj (StatedOmega Q₀) := spinToStatedProj Q hR with hσ
  haveI : Finite (spinGroup Q) := CFSG.LieType.Steinberg.finite_spinGroup_of_ker Q hkerSet
  have hωker : ω.ker = (spinMatrix Q).ker := by
    rw [hω]
    exact MonoidHom.ker_codRestrict _ _ _
  refine ⟨spinGroup Q, inferInstance, inferInstance, σ, ω, z₀, hperf.commutator_eq_top,
    spinToStatedProj_surjective Q hR, hkerle, hclosed, hcard, ?_, ?_, hne,
    CliffordAlgebra.spinGroup.negOne_mul_self Q hQne, ?_, hcliff⟩
  · intro A
    obtain ⟨x, hx⟩ : (A : GL ι (ZMod 5)) ∈ (spinMatrix Q).range := by
      rw [hR]; exact A.2
    rw [hω]
    exact ⟨x, Subtype.ext hx⟩
  · apply le_antisymm
    · intro x hx
      rw [hωker] at hx
      have hx' : x ∈ ((spinMatrix Q).ker : Set (spinGroup Q)) := hx
      rw [hkerSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      rw [hωker]
      show z₀ ∈ ((spinMatrix Q).ker : Set (spinGroup Q))
      rw [hkerSet]
      simp
  · intro u
    rw [hσ, hω]
    exact spinToStatedProj_apply Q hR u

set_option backward.isDefEq.respectTransparency false in
theorem exists_spinGroup_lift_reflect_mul_reflect {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {a b : V} (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hab : QuadraticMap.polar Q a b = 0) (hsq : IsSquare (Q a * Q b)) :
    ∃ x : spinGroup Q, CFSG.LieType.Universal.Spin.spinAction Q x =
        CFSG.ClassicalGroups.Orthogonal.reflect Q a * CFSG.ClassicalGroups.Orthogonal.reflect Q b ∧
      (x : CliffordAlgebra Q) * x = -1 := by
  obtain ⟨μ, hμ⟩ := hsq
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ
    exact (mul_ne_zero ha hb) hμ
  set u : V := μ⁻¹ • a with hu
  have hnorm : Q u * Q b = 1 := by
    have huQ : Q u = (μ⁻¹ * μ⁻¹) * Q a := by
      rw [hu, QuadraticMap.map_smul, smul_eq_mul]
    calc Q u * Q b = (μ⁻¹ * μ⁻¹) * (Q a * Q b) := by rw [huQ]; ring
      _ = (μ⁻¹ * μ⁻¹) * (μ * μ) := by rw [← hμ]
      _ = 1 := by field_simp
  have hpol : QuadraticMap.polar Q u b = 0 := by
    rw [hu, QuadraticMap.polar_smul_left, hab, smul_zero]
  refine ⟨CFSG.ComponentClassification.GSThmB.Cent516.pairElt u b hnorm, ?_, ?_⟩
  · rw [CFSG.ComponentClassification.GSThmB.Cent516.spinAction_pairElt hnorm]
    congr 1
    rw [hu]
    exact reflect_smul_of_ne_zero Q ha (inv_ne_zero hμ0)
  · rw [← Submonoid.coe_mul]
    exact CFSG.ComponentClassification.GSThmB.Cent516.coe_pairElt_mul_self hnorm hpol

set_option backward.isDefEq.respectTransparency false in
theorem exists_lift_isModelReflectionPair {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 5) (ι → ZMod 5)} {Q₀ : (ι → ZMod 5) → ZMod 5} (hcoe : ⇑Q = Q₀)
    (hQne : Q ≠ 0) (hR : (spinMatrix Q).range = StatedOmega Q₀) (g₀ : ↥(StatedOmega Q₀))
    (hg : IsModelReflectionPair Q₀ (g₀ : GL ι (ZMod 5))) :
    ∃ u : spinGroup Q,
      (spinMatrix Q).codRestrict (StatedOmega Q₀) (spinMatrix_mem_of_range_eq Q hR) u = g₀ ∧
      u * u = spinGroup.negOne Q hQne := by
  obtain ⟨a, b, ha, hb, hsq, horth, hmat⟩ := hg
  have haQ : Q a ≠ 0 := by rw [hcoe]; exact ha
  have hbQ : Q b ≠ 0 := by rw [hcoe]; exact hb
  have hsqQ : IsSquare (Q a * Q b) := by rw [hcoe]; exact hsq
  have hpolar : QuadraticMap.polar Q a b = 0 := by
    rw [QuadraticMap.polar, hcoe, horth]
    abel
  obtain ⟨x, hx, hxx⟩ := exists_spinGroup_lift_reflect_mul_reflect haQ hbQ hpolar hsqQ
  refine ⟨x, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    change (spinMatrix Q x : Matrix ι ι (ZMod 5)) =
      ((g₀ : GL ι (ZMod 5)) : Matrix ι ι (ZMod 5))
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, spinMatrix_mulVec, hmat v, hx,
      LinearEquiv.mul_apply]
    rw [modelReflect_eq hcoe haQ (modelReflect Q₀ b v), modelReflect_eq hcoe hbQ v,
      CFSG.ClassicalGroups.Orthogonal.reflect_apply (Q := Q) (v := a) haQ,
      CFSG.ClassicalGroups.Orthogonal.reflect_apply (Q := Q) (v := b) hbQ]
  · exact (eq_negOne_iff Q hQne (x * x)).mpr (by rw [Submonoid.coe_mul]; exact hxx)

section SixMinusTransport

open CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalGroups.Orthogonal
  CFSG.Adapters.RankTwoModelTransports

theorem map_reflect_to_modelReflect {K : Type*} {ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (φ : K ≃+* ZMod 5) {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → ZMod 5) → ZMod 5}
    (hQ : ∀ v, Q₀ (φ ∘ v) = φ (Q v)) (a w : ι → K) :
    φ ∘ CFSG.ClassicalGroups.Orthogonal.reflect Q a w =
      modelReflect (ι := ι) Q₀ (φ ∘ a) (φ ∘ w) := by
  by_cases ha : Q a = 0
  · have hQa : Q₀ (φ ∘ a) = 0 := by rw [hQ, ha, map_zero]
    funext i
    simp [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero ha, modelReflect, hQa]
  · rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply ha]
    funext i
    simp only [Function.comp_apply, modelReflect, QuadraticMap.polar, Pi.sub_apply, Pi.smul_apply]
    conv_rhs => rw [show (φ ∘ w + φ ∘ a) = (φ ∘ (w + a)) by funext j; simp]
    rw [hQ (w + a), hQ w, hQ a]
    rw [map_sub (f := φ)]
    congr 1
    simp only [smul_eq_mul]
    rw [map_mul (f := φ), map_div₀ (f := φ), map_sub (f := φ), map_sub (f := φ)]
    rw [add_comm a w]
    have hD : φ (Q a) ≠ 0 := by
      rw [← map_zero φ]
      exact fun h => ha (φ.injective h)
    field_simp [hD]
    ring

theorem exists_spin_lift_of_modelReflectionPair
    (φ : GaloisField 5 1 ≃+* ZMod 5) {b c : ZMod 5} {b' c' : GaloisField 5 1}
    (hb : φ b' = b) (hc : φ c' = c)
    (hirr : ∀ s : GaloisField 5 1, s ^ 2 + b' * s + c' ≠ 0)
    {g₀ : ↥(StatedOmega (StatedQuadMinus 3 (ZMod 5) b c))}
    (hg : IsModelReflectionPair (StatedQuadMinus 3 (ZMod 5) b c) (g₀ : GL _ _)) :
    ∃ x : spinGroup (quadMinus 3 (GaloisField 5 1) b' c'),
      glCongr φ (spinMatrix (quadMinus 3 (GaloisField 5 1) b' c') x) = (g₀ : GL _ _) ∧
      x * x = CliffordAlgebra.spinGroup.negOne _ (nondegenerate_quadMinus_of_finite 3 _ hirr).ne_zero := by
  classical
  obtain ⟨avec, bvec, ha0, hb0, hsq, horth, hgmat⟩ := hg
  let a1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → GaloisField 5 1 := φ.symm ∘ avec
  let b1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → GaloisField 5 1 := φ.symm ∘ bvec
  have haeq : avec = φ ∘ a1 := by funext i; simp [a1]
  have hbeq : bvec = φ ∘ b1 := by funext i; simp [b1]
  have hQ : ∀ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → GaloisField 5 1,
      StatedQuadMinus 3 (ZMod 5) b c (φ ∘ v) =
        φ (quadMinus 3 (GaloisField 5 1) b' c' v) := by
    intro v
    rw [show quadMinus 3 (GaloisField 5 1) b' c' v =
      StatedQuadMinus 3 (GaloisField 5 1) b' c' v from
      congrFun (coe_quadMinus 3 (GaloisField 5 1) b' c') v]
    exact CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ hb hc v
  have hQa1 : quadMinus 3 (GaloisField 5 1) b' c' a1 ≠ 0 := by
    intro h
    apply ha0
    rw [haeq, hQ a1, h, map_zero]
  have hQb1 : quadMinus 3 (GaloisField 5 1) b' c' b1 ≠ 0 := by
    intro h
    apply hb0
    rw [hbeq, hQ b1, h, map_zero]
  have hsumφ : StatedQuadMinus 3 (ZMod 5) b c (φ ∘ (a1 + b1)) =
      StatedQuadMinus 3 (ZMod 5) b c (φ ∘ a1) +
        StatedQuadMinus 3 (ZMod 5) b c (φ ∘ b1) := by
    have hfun : φ ∘ (a1 + b1) = avec + bvec := by
      funext i
      simp [a1, b1, map_add, Pi.add_apply]
    rw [hfun, horth, haeq, hQ a1, hbeq, hQ b1]
  have hsum1 : quadMinus 3 (GaloisField 5 1) b' c' (a1 + b1) =
      quadMinus 3 (GaloisField 5 1) b' c' a1 +
        quadMinus 3 (GaloisField 5 1) b' c' b1 := by
    apply φ.injective
    rw [map_add (f := φ), (hQ (a1 + b1)).symm, (hQ a1).symm, (hQ b1).symm]
    exact hsumφ
  have hpolar : QuadraticMap.polar (quadMinus 3 (GaloisField 5 1) b' c') a1 b1 = 0 := by
    show quadMinus 3 (GaloisField 5 1) b' c' (a1 + b1) -
      quadMinus 3 (GaloisField 5 1) b' c' a1 -
        quadMinus 3 (GaloisField 5 1) b' c' b1 = 0
    rw [hsum1]
    abel
  have hsq1 : IsSquare (quadMinus 3 (GaloisField 5 1) b' c' a1 *
      quadMinus 3 (GaloisField 5 1) b' c' b1) := by
    obtain ⟨r, hr⟩ := hsq
    refine ⟨φ.symm r, ?_⟩
    apply φ.injective
    calc φ (quadMinus 3 (GaloisField 5 1) b' c' a1 *
          quadMinus 3 (GaloisField 5 1) b' c' b1)
        = φ (quadMinus 3 (GaloisField 5 1) b' c' a1) *
            φ (quadMinus 3 (GaloisField 5 1) b' c' b1) := map_mul φ _ _
      _ = StatedQuadMinus 3 (ZMod 5) b c avec * StatedQuadMinus 3 (ZMod 5) b c bvec := by
          rw [← hQ a1, ← hQ b1, haeq, hbeq]
      _ = r * r := hr
      _ = φ (φ.symm r * φ.symm r) := by simp
  obtain ⟨x, hxact, hxcliff⟩ := exists_spinGroup_lift_reflect_mul_reflect
    hQa1 hQb1 hpolar hsq1
  refine ⟨x, ?_, ?_⟩
  · apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [show v = φ ∘ (φ.symm ∘ v) from by funext i; simp]
    rw [CFSG.ClassicalInvolution.Upgrade.glCongr_mulVec, spinMatrix_mulVec, hxact]
    change φ ∘ ((CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 3 (GaloisField 5 1) b' c') a1)
        ((CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 3 (GaloisField 5 1) b' c') b1)
          (φ.symm ∘ v))) = (g₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (ZMod 5)) *ᵥ
            (φ ∘ (φ.symm ∘ v))
    rw [map_reflect_to_modelReflect φ hQ a1
      ((CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 3 (GaloisField 5 1) b' c') b1)
        (φ.symm ∘ v))]
    rw [map_reflect_to_modelReflect φ hQ b1 (φ.symm ∘ v)]
    rw [show φ ∘ a1 = avec from haeq.symm, show φ ∘ b1 = bvec from hbeq.symm]
    rw [show (φ ∘ φ.symm ∘ v) = v from by funext i; simp]
    exact (hgmat v).symm
  · have hQne : quadMinus 3 (GaloisField 5 1) b' c' ≠ 0 :=
      (nondegenerate_quadMinus_of_finite 3 (GaloisField 5 1) hirr).ne_zero
    exact (eq_negOne_iff (Q := quadMinus 3 (GaloisField 5 1) b' c') hQne (x * x)).2 (by simpa using hxcliff)

theorem modelSpinData_quadMinus_three_zmod5
    (φ : GaloisField 5 1 ≃+* ZMod 5) {b c : ZMod 5} {b' c' : GaloisField 5 1}
    (hb : φ b' = b) (hc : φ c' = c)
    (hirr : ∀ s : GaloisField 5 1, s ^ 2 + b' * s + c' ≠ 0) :
    ModelSpinData (StatedQuadMinus 3 (ZMod 5) b c) := by
  classical
  let F := GaloisField 5 1
  let Q1 := quadMinus 3 F b' c'
  let Q0 : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 5) → ZMod 5 :=
    StatedQuadMinus 3 (ZMod 5) b c
  let Ω1 := StatedOmega (StatedQuadMinus 3 F b' c')
  let Ω0 := StatedOmega Q0
  have hcardF : Nat.card F = 5 := by
    rw [show F = GaloisField 5 1 from rfl, GaloisField.card 5 1 (by norm_num)]
    norm_num
  have hodd : Odd (Nat.card F) := by rw [hcardF]; norm_num
  have h4 : 4 ≤ Nat.card F := by rw [hcardF]; norm_num
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hQne : Q1 ≠ 0 := (nondegenerate_quadMinus_of_finite 3 F hirr).ne_zero
  have hQ : ∀ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      Q0 (φ ∘ v) = φ (Q1 v) := by
    intro v
    rw [show Q1 v = StatedQuadMinus 3 F b' c' v from
      congrFun (coe_quadMinus 3 F b' c') v]
    exact CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ hb hc v
  have hQstat : ∀ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      Q0 (φ ∘ v) = φ (StatedQuadMinus 3 F b' c' v) := by
    intro v
    exact (hQ v).trans (by
      rw [show Q1 v = StatedQuadMinus 3 F b' c' v from
        congrFun (coe_quadMinus 3 F b' c') v])
  have hR : (spinMatrix Q1).range = Ω1 :=
    range_spinMatrix_quadMinus_three_odd hodd h4 hirr
  have hσ := spinToStatedProj_quadMinus_three_odd hodd (by omega) h4 hirr
  have hH : Ω1.map (glCongr φ).toMonoidHom = Ω0 :=
    CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ hQstat
  let ψΩ : Ω1 ≃* Ω0 :=
    (Ω1.equivMapOfInjective (glCongr φ).toMonoidHom (glCongr φ).injective).trans
      (MulEquiv.subgroupCongr hH)
  let Ψ : StatedProj Ω1 ≃* StatedProj Ω0 :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr (glCongr φ) hH
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  let ω1 : spinGroup Q1 →* Ω1 :=
    (spinMatrix Q1).codRestrict Ω1 (fun x => hR ▸ ⟨x, rfl⟩)
  let ω : spinGroup Q1 →* Ω0 := ψΩ.toMonoidHom.comp ω1
  let σ1 : spinGroup Q1 →* StatedProj Ω1 := spinToStatedProj Q1 hR
  let σ : spinGroup Q1 →* StatedProj Ω0 := Ψ.toMonoidHom.comp σ1
  let z0 : spinGroup Q1 := CliffordAlgebra.spinGroup.negOne Q1 hQne
  refine ⟨spinGroup Q1, inferInstance,
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker Q1
      (coe_ker_spinMatrix_quadMinus (n := 3) hirr),
    σ, ω, z0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : Group.IsPerfect (spinGroup Q1) :=
      CFSG.ComponentClassification.HarrisLit.T1.P54.Klein.isPerfect_spinGroup_quadMinus_three
        hodd h4 hirr
    exact Group.IsPerfect.commutator_eq_top
  · change Function.Surjective (Ψ.toMonoidHom.comp σ1)
    exact Ψ.surjective.comp hσ.1
  · change (Ψ.toMonoidHom.comp σ1).ker ≤ Subgroup.center (spinGroup Q1)
    rw [MonoidHom.ker_comp_of_injective σ1 Ψ.toMonoidHom Ψ.injective, hσ.2]
  · intro E _ _ p hp hk
    exact spin_five_exists_section_of_central hirr p hp hk
  · change Nat.card (Ψ.toMonoidHom.comp σ1).ker ≤ 4
    rw [MonoidHom.ker_comp_of_injective σ1 Ψ.toMonoidHom Ψ.injective,
      ker_spinToStatedProj (Q := Q1) (Q₀ := StatedQuadMinus 3 F b' c') hR]
    exact CFSG.LieType.Steinberg.card_comap_statedScalars_le_four
      (Q := Q1) (Q₀ := StatedQuadMinus 3 F b' c') (coe_quadMinus 3 F b' c')
      ⟨planeVec 3 (planeOne : Fin 2 → F), by
        rw [quadMinus_planeVec' (w := (planeOne : Fin 2 → F))]
        exact planeNorm_planeOne_ne_zero⟩
      hR (coe_ker_spinMatrix_quadMinus (n := 3) hirr)
  · rintro ⟨A, hA⟩
    obtain ⟨B, hB⟩ := ψΩ.surjective ⟨A, hA⟩
    have hBmem : (B : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) ∈ (spinMatrix Q1).range :=
      hR.symm ▸ B.2
    obtain ⟨x, hx⟩ := hBmem
    refine ⟨x, ?_⟩
    change ψΩ (ω1 x) = ⟨A, hA⟩
    rw [← hB]
    exact congrArg ψΩ (Subtype.ext hx)
  · apply le_antisymm
    · intro x hx
      have hx1 : x ∈ ω1.ker := by
        rw [MonoidHom.mem_ker] at hx ⊢
        apply ψΩ.injective
        simpa [ω] using hx
      rw [MonoidHom.ker_codRestrict] at hx1
      change x ∈ (spinMatrix (quadMinus 3 (GaloisField 5 1) b' c')).ker at hx1
      rw [mem_ker_spinMatrix_quadMinus_iff (n := 3) hirr] at hx1
      rcases hx1 with rfl | hxneg
      · exact Subgroup.one_mem _
      · have hxz : x = z0 :=
          (eq_negOne_iff (Q := quadMinus 3 (GaloisField 5 1) b' c') hQne x).2 hxneg
        rw [hxz]
        exact Subgroup.mem_zpowers _
    · refine Subgroup.zpowers_le.mpr ?_
      rw [MonoidHom.mem_ker]
      change ψΩ (ω1 z0) = 1
      have hz0ker : z0 ∈ ω1.ker := by
        rw [MonoidHom.ker_codRestrict]
        change z0 ∈ (spinMatrix (quadMinus 3 (GaloisField 5 1) b' c')).ker
        rw [mem_ker_spinMatrix_quadMinus_iff (n := 3) hirr]
        exact Or.inr (CliffordAlgebra.spinGroup.coe_negOne Q1 hQne)
      rw [MonoidHom.mem_ker] at hz0ker
      rw [hz0ker, map_one]
  · haveI : Invertible (2 : F) := invertibleOfNonzero h2
    exact CliffordAlgebra.spinGroup.negOne_ne_one (Q := Q1) hQne
  · exact CliffordAlgebra.spinGroup.negOne_mul_self (Q := Q1) hQne
  · intro u
    change Ψ (σ1 u) = QuotientGroup.mk (ψΩ (ω1 u))
    have hσ1u : σ1 u = QuotientGroup.mk (ω1 u) := by
      rw [spinToStatedProj_apply (Q := Q1) (Q₀ := StatedQuadMinus 3 F b' c') hR u]
      exact congrArg QuotientGroup.mk (Subtype.ext rfl)
    have hΨ_mk : ∀ x : Ω1, Ψ (QuotientGroup.mk x) = QuotientGroup.mk (ψΩ x) := by
      intro x
      rfl
    rw [hσ1u, hΨ_mk]
  · intro g0 hg
    obtain ⟨x, hxmat, hxsq⟩ := exists_spin_lift_of_modelReflectionPair φ hb hc hirr hg
    refine ⟨x, ?_, ?_⟩
    · change (ψΩ (ω1 x) : Ω0) = g0
      apply Subtype.ext
      change glCongr φ (spinMatrix Q1 x) = (g0 : GL _ _)
      exact hxmat
    · simpa [z0] using hxsq

end SixMinusTransport

theorem modelReflect_eq_reflect (a v : Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 5)
    (ha : StatedQuadOdd 2 (ZMod 5) a ≠ 0) :
    modelReflect (StatedQuadOdd 2 (ZMod 5)) a v =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) a v := by
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply
    (Q := quadOdd 2 (ZMod 5)) (by rwa [CFSG.LieType.Universal.Spin.coe_quadOdd])]
  simp only [modelReflect]
  congr 1
  rw [QuadraticMap.polar, div_eq_mul_inv, add_comm v a,
    CFSG.LieType.Universal.Spin.coe_quadOdd]
  ring

theorem modelReflectionPair_sq {g₀ : ↥(StatedOmega (StatedQuadOdd 2 (ZMod 5)))}
    (hg₀ : IsModelReflectionPair (StatedQuadOdd 2 (ZMod 5))
      (g₀ : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5))) : g₀ * g₀ = 1 := by
  obtain ⟨a, b, ha, hb, hsq, hab, hg⟩ := hg₀
  have hpol : QuadraticMap.polar (quadOdd 2 (ZMod 5)) a b = 0 := by
    simp only [QuadraticMap.polar, CFSG.LieType.Universal.Spin.coe_quadOdd]
    rw [hab]
    ring
  have hfac : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)
      (g₀ : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)) =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) a *
        CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hg v,
      modelReflect_eq_reflect b v hb, modelReflect_eq_reflect a
        (CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b v) ha]
  have hcomm : CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) a *
      CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b *
        CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) a :=
    CFSG.GH74.Filter.reflect_comm hpol
  have hcomm_fun : ∀ w, CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) a
      (CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b w) =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b
        (CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) a w) := by
    intro w
    simpa only [LinearEquiv.mul_apply] using congrArg (fun f => f w) hcomm
  have hprod : (CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) a *
      CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b) *
      (CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) a *
        CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b) = 1 := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      ← hcomm_fun (CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b v),
      ← LinearEquiv.mul_apply, CFSG.ClassicalGroups.Orthogonal.reflect_mul_self]
    change CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b
      (CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b v) = v
    rw [← LinearEquiv.mul_apply, CFSG.ClassicalGroups.Orthogonal.reflect_mul_self]
    rfl
  apply Subtype.ext
  change (g₀ : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)) *
      (g₀ : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)) = 1
  apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)).injective
  rw [map_mul, hfac, map_one]
  exact hprod

theorem modelReflectionPair_ne_one {g₀ : ↥(StatedOmega (StatedQuadOdd 2 (ZMod 5)))}
    (hg₀ : IsModelReflectionPair (StatedQuadOdd 2 (ZMod 5))
      (g₀ : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5))) : g₀ ≠ 1 := by
  obtain ⟨a, b, ha, hb, hsq, hab, hg⟩ := hg₀
  have hpol : QuadraticMap.polar (quadOdd 2 (ZMod 5)) a b = 0 := by
    simp only [QuadraticMap.polar, CFSG.LieType.Universal.Spin.coe_quadOdd]
    rw [hab]
    ring
  intro hg1
  have h1 : b = CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) a
      (CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b b) := by
    have h := hg b
    rw [hg1] at h
    have h' : b = modelReflect (StatedQuadOdd 2 (ZMod 5)) a
        (modelReflect (StatedQuadOdd 2 (ZMod 5)) b b) := by simpa using h
    refine h'.trans ?_
    rw [modelReflect_eq_reflect b b hb, modelReflect_eq_reflect a
      (CFSG.ClassicalGroups.Orthogonal.reflect (quadOdd 2 (ZMod 5)) b b) ha]
  rw [CFSG.GH74.Filter.reflect_apply_self (Q := quadOdd 2 (ZMod 5))
      (by rwa [CFSG.LieType.Universal.Spin.coe_quadOdd]), map_neg,
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero hpol] at h1
  have hb0 : b = 0 := by
    have h2 : b + b = 0 := (eq_neg_iff_add_eq_zero).mp h1
    have h3 : (2 : ZMod 5) • b = 0 := by rw [two_smul]; exact h2
    exact (smul_eq_zero.mp h3).resolve_left (by decide)
  exact hb (by rw [hb0]; norm_num [StatedQuadOdd])

theorem reflectionPair_invariant_holds {g₀ : ↥(StatedOmega (StatedQuadOdd 2 (ZMod 5)))}
    (hg₀ : IsModelReflectionPair (StatedQuadOdd 2 (ZMod 5))
      (g₀ : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5))) :
    ReflPairInvariant
      (QuotientGroup.mk g₀ : StatedProj (StatedOmega (StatedQuadOdd 2 (ZMod 5)))) := by
  obtain ⟨a, b, ha, hb, hsq, hab, hg⟩ := hg₀
  have ha' : Q5 a ≠ 0 := by
    simpa only [CFSG.LieType.Universal.Spin.coe_quadOdd] using ha
  have hb' : Q5 b ≠ 0 := by
    simpa only [CFSG.LieType.Universal.Spin.coe_quadOdd] using hb
  have hsq' : IsSquare (Q5 a * Q5 b) := by
    simpa only [CFSG.LieType.Universal.Spin.coe_quadOdd] using hsq
  have hpol : QuadraticMap.polar Q5 a b = 0 := by
    simp only [QuadraticMap.polar, CFSG.LieType.Universal.Spin.coe_quadOdd]
    rw [hab]
    ring
  have hfac : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)
      (g₀ : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) (ZMod 5)) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q5 b := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hg v,
      modelReflect_eq_reflect b v hb, modelReflect_eq_reflect a
        (CFSG.ClassicalGroups.Orthogonal.reflect Q5 b v) ha]
  let x : ↥(CFSG.RankThree.Classical2.orthDerived Q5) := statedOmegaEquivOrthDerived g₀
  have hx : (x : V5 ≃ₗ[ZMod 5] V5) = CFSG.ClassicalGroups.Orthogonal.reflect Q5 a *
      CFSG.ClassicalGroups.Orthogonal.reflect Q5 b := by
    rw [statedOmegaEquivOrthDerived_apply]
    exact hfac
  have hPx : ReflPairInvariant x := reflPairInvariant_intrinsic ha' hb' hpol hsq' hx
  have hPg : ReflPairInvariant g₀ :=
    (reflPairInvariant_map statedOmegaEquivOrthDerived g₀).mp hPx
  have hmk : QuotientGroup.mk g₀ = statedOmegaTwoProjEquiv.symm g₀ := by
    have := congrArg statedOmegaTwoProjEquiv.symm (statedOmegaTwoProjEquiv_mk g₀)
    simpa using this
  rw [hmk]
  exact (reflPairInvariant_map statedOmegaTwoProjEquiv.symm g₀).mpr hPg

theorem modelSpinData_quadOdd_two : ModelSpinData (StatedQuadOdd 2 (ZMod 5)) := by
  refine ⟨↥(StatedSp 2 (ZMod 5)), inferInstance, inferInstance, spTwoSigma, spTwoOmega,
    spTwoNegOne, ?_, spTwoSigma_surjective, spTwoSigma_ker_le_center, ?_,
    spTwoSigma_ker_card_le_four, spTwoOmega_surjective, spTwoOmega_ker, spTwoNegOne_ne_one,
    spTwoNegOne_mul_self, spTwoSigma_eq_mk_spTwoOmega, ?_⟩
  · exact (CFSG.LieType.Steinberg.CentralExt.SpClosed.isPerfect_statedSp 2 (ZMod 5)
      (by norm_num)).commutator_eq_top
  · intro E _ _ p hp hcen
    exact CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_central
      (n := 2) (F := ZMod 5) (by norm_num) (by rw [Nat.card_zmod]) hp hcen
  · intro g₀ hg₀
    obtain ⟨u, rfl⟩ := spTwoOmega_surjective g₀
    refine ⟨u, rfl, ?_⟩
    by_contra hne
    have hsq : u * u = 1 := by
      have hmem : u * u ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars
          2 (ZMod 5) := by
        have h1 : u * u ∈ spTwoOmega.ker := by
          rw [MonoidHom.mem_ker, map_mul, modelReflectionPair_sq hg₀]
        rwa [spTwoOmega_ker_eq_spScalars] at h1
      rcases CFSG.ClassicalInvolution.Asc77.C5O.M.mem_spScalars_iff.mp hmem with h | h
      · exact h
      · exact absurd h hne
    have he : statedProjQuadOddTwoEquiv (QuotientGroup.mk (spTwoOmega u)) = spTwoProj u := by
      rw [← spTwoSigma_eq_mk_spTwoOmega u]
      simp only [spTwoSigma, MonoidHom.comp_apply]
      exact MulEquiv.apply_symm_apply statedProjQuadOddTwoEquiv (spTwoProj u)
    have hproj_ne_one : spTwoProj u ≠ 1 := by
      intro h1
      have hmk1 : (QuotientGroup.mk (spTwoOmega u) :
          StatedProj (StatedOmega (StatedQuadOdd 2 (ZMod 5)))) = 1 := by
        apply statedProjQuadOddTwoEquiv.injective
        rw [he, h1, map_one]
      rw [QuotientGroup.eq_one_iff] at hmk1
      rw [statedScalarsOmegaTwo_subgroupOf_eq_bot, Subgroup.mem_bot] at hmk1
      exact modelReflectionPair_ne_one hg₀ hmk1
    have hu1 : u ≠ 1 := fun h => hproj_ne_one (by rw [h, map_one])
    have hum : u ≠ spTwoNegOne := fun h => hproj_ne_one (by rw [h]; exact spTwoProj_spTwoNegOne)
    have hP : ReflPairInvariant (spTwoProj u) := by
      rw [← he]
      exact (reflPairInvariant_map statedProjQuadOddTwoEquiv (QuotientGroup.mk (spTwoOmega u))).mpr
        (reflectionPair_invariant_holds hg₀)
    exact involution_invariant_fails u hsq hu1 hum hP

set_option backward.isDefEq.respectTransparency false in
theorem modelSpinData_quadOdd {n : ℕ} (hn : 2 ≤ n) :
    ModelSpinData (StatedQuadOdd n (ZMod 5)) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · have hn2 : n = 2 := by omega
    rw [hn2]
    exact modelSpinData_quadOdd_two
  · have h2 : (2 : ZMod 5) ≠ 0 := by decide
    have h5 : 5 ≤ Nat.card (ZMod 5) := by
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have hv : ∃ v : Fin n ⊕ Fin n ⊕ Unit → ZMod 5, quadOdd n (ZMod 5) v ≠ 0 :=
      exists_map_ne_zero_of_hypPair _ (CFSG.ClassicalGroups.Orthogonal.oddPair (ZMod 5)
        (⟨0, by omega⟩ : Fin n))
    refine modelSpinData_of_spinGroup (Q := quadOdd n (ZMod 5))
      (Q₀ := StatedQuadOdd n (ZMod 5)) (nondegenerate_quadOdd n (ZMod 5)).ne_zero
      (range_spinMatrix_quadOdd h2 h) (isPerfect_spinGroup_quadOdd h2 h) ?_ ?_ ?_ ?_ ?_ ?_
    · exact ker_spinToStatedProj_le_center _ _ hv
    · rw [CFSG.LieType.Steinberg.CentralExt.SpinOddClosed.card_ker_spinToStatedProj_quadOdd h2 h]
      norm_num
    · intro E _ _ p hp hcen
      exact CFSG.LieType.Steinberg.CentralExt.SpinOddClosed.spinOdd_exists_section_of_central
        h2 h h5 hp hcen
    · exact coe_ker_spinMatrix_quadOdd h2
    · let _ : Invertible (2 : ZMod 5) := invertibleOfNonzero h2
      exact spinGroup.negOne_ne_one _ _
    · intro g₀ hg
      exact exists_lift_isModelReflectionPair (coe_quadOdd n (ZMod 5))
        (nondegenerate_quadOdd n (ZMod 5)).ne_zero (range_spinMatrix_quadOdd h2 h) g₀ hg

set_option backward.isDefEq.respectTransparency false in
theorem modelSpinData_quadPlus {n : ℕ} (hn : 3 ≤ n) :
    ModelSpinData (StatedQuadPlus n (ZMod 5)) := by
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have h4 : 4 ≤ Nat.card (ZMod 5) := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  haveI : NeZero n := ⟨by omega⟩
  have hv : ∃ v : Fin n ⊕ Fin n → ZMod 5, quadPlus n (ZMod 5) v ≠ 0 :=
    exists_map_ne_zero_of_hypPair _ (CFSG.ClassicalGroups.Orthogonal.plusPair (ZMod 5)
      (⟨0, by omega⟩ : Fin n))
  refine modelSpinData_of_spinGroup (Q := quadPlus n (ZMod 5))
    (Q₀ := StatedQuadPlus n (ZMod 5)) (nondegenerate_quadPlus n (ZMod 5)).ne_zero
    (range_spinMatrix_quadPlus hn) (isPerfect_spinGroup_quadPlus hn) ?_ ?_ ?_ ?_ ?_ ?_
  · exact ker_spinToStatedProj_le_center _ _ hv
  · rw [ker_spinToStatedProj]
    exact CFSG.LieType.Steinberg.card_comap_statedScalars_le_four (Q := quadPlus n (ZMod 5))
      (coe_quadPlus n (ZMod 5)) hv (range_spinMatrix_quadPlus hn)
      (coe_ker_spinMatrix_quadPlus (K := ZMod 5))
  · intro E _ _ p hp hcen
    exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_exists_section_of_central
      hn h4 hp hcen
  · exact coe_ker_spinMatrix_quadPlus (K := ZMod 5)
  · let _ : Invertible (2 : ZMod 5) := invertibleOfNonzero h2
    exact spinGroup.negOne_ne_one _ _
  · intro g₀ hg
    exact exists_lift_isModelReflectionPair (coe_quadPlus n (ZMod 5))
      (nondegenerate_quadPlus n (ZMod 5)).ne_zero (range_spinMatrix_quadPlus hn) g₀ hg

@[expose] def FiveMinusInputs : Prop :=
  ∀ (n : ℕ) (b c : ZMod 5), 4 ≤ n → (∀ s : ZMod 5, s ^ 2 + b * s + c ≠ 0) →
    CentralKernelTwoGroup (StatedProj (StatedOmega (StatedQuadMinus n (ZMod 5) b c))) ∧
      ModelSpinData (StatedQuadMinus n (ZMod 5) b c)

theorem fiveMinusInputs_of_certificates :
    FiveMinusInputs := by
  intro n b c hn hirr
  have hK : Nat.card (ZMod 5) = 5 ^ 1 := by simp
  have hK4 : 4 ≤ Nat.card (ZMod 5) := by simp
  constructor
  ·
    obtain ⟨hcomm, hM⟩ :=
      CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.pomegaMinus_hopfMultiplier
        (K := ZMod 5) (b := b) (c := c) (p := 5) (f := 1) hn hirr hK hK4
    obtain ⟨e⟩ := hM
    refine centralKernelTwoGroup_of_hopfMultiplier hcomm (m := 2) ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact Nat.gcd_dvd_left 4 _
  ·
    have h2 : (2 : ZMod 5) ≠ 0 := by decide
    have h4 : 4 ≤ Nat.card (ZMod 5) := by
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have hv : ∃ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ZMod 5,
        quadMinus n (ZMod 5) b c v ≠ 0 :=
      exists_map_ne_zero_of_hypPair _
        (CFSG.ClassicalGroups.Orthogonal.minusPair (ZMod 5) b c (⟨0, by omega⟩ : Fin (n - 1)))
    refine modelSpinData_of_spinGroup (Q := quadMinus n (ZMod 5) b c)
      (Q₀ := StatedQuadMinus n (ZMod 5) b c)
      (nondegenerate_quadMinus_of_finite (n := n) (K := ZMod 5) hirr).ne_zero
      (range_spinMatrix_quadMinus hn hirr) (isPerfect_spinGroup_quadMinus hn hirr) ?_ ?_ ?_ ?_ ?_ ?_
    · exact ker_spinToStatedProj_le_center _ _ hv
    · rw [ker_spinToStatedProj]
      exact CFSG.LieType.Steinberg.card_comap_statedScalars_le_four (Q := quadMinus n (ZMod 5) b c)
        (coe_quadMinus n (ZMod 5) b c) hv (range_spinMatrix_quadMinus hn hirr)
        (coe_ker_spinMatrix_quadMinus (K := ZMod 5) hirr)
    · intro E _ _ p hp hcen
      exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_central
        hirr hn h4 hp hcen
    · exact coe_ker_spinMatrix_quadMinus (K := ZMod 5) hirr
    · let _ : Invertible (2 : ZMod 5) := invertibleOfNonzero h2
      exact spinGroup.negOne_ne_one _ _
    · intro g₀ hg
      exact exists_lift_isModelReflectionPair (coe_quadMinus n (ZMod 5) b c)
        (nondegenerate_quadMinus_of_finite (n := n) (K := ZMod 5) hirr).ne_zero
        (range_spinMatrix_quadMinus hn hirr) g₀ hg

@[expose] def FiveMinusSixInputs : Prop :=
  ∀ (b c : ZMod 5), (∀ s : ZMod 5, s ^ 2 + b * s + c ≠ 0) →
    CentralKernelTwoGroup (StatedProj (StatedOmega (StatedQuadMinus 3 (ZMod 5) b c))) ∧
      ModelSpinData (StatedQuadMinus 3 (ZMod 5) b c)

section CentralKernel

open CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalGroups.Orthogonal
  CFSG.Adapters.RankTwoModelTransports

theorem centralKernelTwoGroup_statedProj_quadMinus_three (b c : ZMod 5)
    (hirr : ∀ s : ZMod 5, s ^ 2 + b * s + c ≠ 0) :
    CentralKernelTwoGroup (StatedProj (StatedOmega (StatedQuadMinus 3 (ZMod 5) b c))) := by
  classical
  let φ : GaloisField 5 1 ≃+* ZMod 5 := (GaloisField.equivZmodP 5).toRingEquiv
  let F := GaloisField 5 1
  let b' : F := φ.symm b
  let c' : F := φ.symm c
  have hb : φ b' = b := by simp [b']
  have hc : φ c' = c := by simp [c']
  have hirr' : ∀ s : F, s ^ 2 + b' * s + c' ≠ 0 :=
    CFSG.ClassicalInvolution.Upgrade.irreducible_map φ.symm hirr
  let Q1 := quadMinus 3 F b' c'
  let Ω1 := StatedOmega (StatedQuadMinus 3 F b' c')
  let Ω0 := StatedOmega (StatedQuadMinus 3 (ZMod 5) b c)
  have hcardF : Nat.card F = 5 := by
    rw [show F = GaloisField 5 1 from rfl, GaloisField.card 5 1 (by norm_num)]
    norm_num
  have hodd : Odd (Nat.card F) := by rw [hcardF]; norm_num
  have h4 : 4 ≤ Nat.card F := by rw [hcardF]; norm_num
  have hR : (spinMatrix Q1).range = Ω1 :=
    range_spinMatrix_quadMinus_three_odd hodd h4 hirr'
  have hQ : ∀ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      StatedQuadMinus 3 (ZMod 5) b c (φ ∘ v) = φ (Q1 v) := by
    intro v
    rw [show Q1 v = StatedQuadMinus 3 F b' c' v from
      congrFun (coe_quadMinus 3 F b' c') v]
    exact CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ hb hc v
  have hQstat : ∀ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      StatedQuadMinus 3 (ZMod 5) b c (φ ∘ v) = φ (StatedQuadMinus 3 F b' c' v) := by
    intro v
    exact (hQ v).trans (by
      rw [show Q1 v = StatedQuadMinus 3 F b' c' v from
        congrFun (coe_quadMinus 3 F b' c') v])
  have hH : Ω1.map (CFSG.Adapters.RankTwoModelTransports.glCongr φ).toMonoidHom = Ω0 :=
    CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ hQstat
  let eField : StatedProj Ω1 ≃* StatedProj Ω0 :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr (CFSG.Adapters.RankTwoModelTransports.glCongr φ) hH
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  have hZ : Subgroup.center Ω1 =
      (StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).subgroupOf Ω1 :=
    center_statedOmega_quadMinus_three_eq_scalars (K := F) (b := b') (c := c')
      (by rw [hcardF]; norm_num) hirr'
  let eSpin : spinGroup Q1 ⧸ Subgroup.center (spinGroup Q1) ≃* StatedProj Ω1 :=
    spinQuotientCenterEquiv (Q := Q1) (Q₀ := StatedQuadMinus 3 F b' c') hR hZ
      ⟨planeVec 3 (planeOne : Fin 2 → F), by
        rw [quadMinus_planeVec' (w := (planeOne : Fin 2 → F))]
        exact planeNorm_planeOne_ne_zero⟩
  let K2 := GaloisField 5 (2 * 1)
  let SU4 := StatedSU 4 (5 ^ 1) K2
  have hK2 : Nat.card K2 = (5 ^ 1) ^ 2 := by
    change Nat.card (GaloisField 5 (2 * 1)) = (5 ^ 1) ^ 2
    rw [CFSG.LieType.Universal.card_galoisField_two_mul 5 1 (by norm_num)]
  have hZSU : Subgroup.center SU4 =
      (StatedScalars (Fin 4) K2).subgroupOf SU4 :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K2)
      (p := 5) (f := 1) hK2 (n := 4) (by norm_num) (by norm_num)).2
  obtain ⟨eSU, -⟩ := CFSG.ClassicalInvolution.WeakCT.SU4.su4SpinMinus_exists
    (p := 5) (f := 1) (by norm_num) (by norm_num) hirr'
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix (F := K2) (p := 5) (f := 1) hK2 4
  let cE : CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution K2 5 1) 4 ≃*
      CFSG.ClassicalInvolution.Phan.Su K2 5 1 4 := CFSG.LieType.Universal.Unitary.conjEquiv P hP
  let eCenter : spinGroup Q1 ⧸ Subgroup.center (spinGroup Q1) ≃*
      CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution K2 5 1) 4 ⧸
        Subgroup.center (CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution K2 5 1) 4) :=
    QuotientGroup.congr _ _ (eSU.trans cE.symm)
      (Subgroup.map_center_eq (eSU.trans cE.symm))
  let eSUq : CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution K2 5 1) 4 ⧸
        Subgroup.center (CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution K2 5 1) 4) ≃* StatedProj SU4 :=
    CFSG.LieType.Universal.Unitary.centerQuotientEquivStatedProj (F := K2) (p := 5) (f := 1)
      (n := 4) hK2 hZSU
  let eTotal : StatedProj Ω0 ≃* StatedProj SU4 :=
    eField.symm.trans (eSpin.symm.trans (eCenter.trans eSUq))
  have hpsu := CFSG.LieType.Steinberg.CentralExt.SUClosed.psu_hopfMultiplier
    (F := K2) (p := 5) (f := 1) hK2 (n := 4)
    (by norm_num : Even 4) (by norm_num : 4 ≤ 4) (by norm_num : 4 ≤ 5 ^ 1)
  obtain ⟨eM⟩ := hpsu.2
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj SU4)) ∣ 2 ^ 1 := by
    rw [Nat.card_congr eM.toEquiv]
    norm_num
  have hSU : CentralKernelTwoGroup (StatedProj SU4) :=
    centralKernelTwoGroup_of_hopfMultiplier hpsu.1 hM
  exact centralKernelTwoGroup_of_mulEquiv eTotal hSU

end CentralKernel
theorem fiveMinusSixInputs_of_certificates : FiveMinusSixInputs := by
  intro b c hirr
  let φ : GaloisField 5 1 ≃+* ZMod 5 := (GaloisField.equivZmodP 5).toRingEquiv
  have hirr' : ∀ s : GaloisField 5 1, s ^ 2 + φ.symm b * s + φ.symm c ≠ 0 :=
    CFSG.ClassicalInvolution.Upgrade.irreducible_map φ.symm hirr
  refine ⟨centralKernelTwoGroup_statedProj_quadMinus_three b c hirr, ?_⟩
  exact modelSpinData_quadMinus_three_zmod5 φ (by simp) (by simp) hirr'

end CFSG.OddTranspositions.PartThree
