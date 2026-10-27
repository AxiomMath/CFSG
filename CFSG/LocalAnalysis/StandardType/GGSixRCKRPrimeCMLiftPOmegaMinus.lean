module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMRestrict
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoOrth
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Aut
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.ClassicalGroups.Orthogonal.OddOrder
public import CFSG.GroupTheory.Commutator.SupNormalizer
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplitSp
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.ClassicalPosition
open Matrix

private lemma rck_lift_choose_POmegaMinus {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadMinus n F bq cq) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadMinus n F bq cq)))
    {s : spinGroup (Spin.quadMinus n F bq cq)} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {b : X}
    (hbID : GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ b) (hbe : Commute b e) :
    ∃ s_b : spinGroup (Spin.quadMinus n F bq cq),
      (∀ u, b⁻¹ * ψ u * b = ψ (s_b * u * s_b⁻¹)) ∧
        Commute (Spin.spinMatrix (Spin.quadMinus n F bq cq) s_b)
          (Spin.spinMatrix (Spin.quadMinus n F bq cq) s) := by
  obtain ⟨s_b, hs_b⟩ := exists_conj_eq_POmegaMinus n hirr hn ψ hker hbID
  have hcommSub : Commute s_b s :=
    conj_eq_commute_POmegaMinus n hirr hn ψ hker hbe hs_b hs
  exact ⟨s_b, hs_b, hcommSub.map _⟩

private lemma rck_spin_restrict_POmegaMinus {n : ℕ} {F : Type} [Field F] [Finite F]
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0)
    {s : spinGroup (Spin.quadMinus n F bq cq)}
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F (Units.val '' {Spin.spinMatrix (Spin.quadMinus n F bq cq) s})) ε)
    {s_b : spinGroup (Spin.quadMinus n F bq cq)}
    (hcomm : Commute (Spin.spinMatrix (Spin.quadMinus n F bq cq) s_b)
      (Spin.spinMatrix (Spin.quadMinus n F bq cq) s)) :
    ∃ s₁ : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
      s₁ ∈ Subgroup.centralizer
          ({Spin.spinMatrix (Spin.quadMinus n F bq cq) s} :
            Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) ⊓ glFixing (1 - ε) ∧
        (∀ v, Spin.quadMinus n F bq cq
          ((s₁ : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ v) =
          Spin.quadMinus n F bq cq v) ∧
        orderOf s₁ ∣ orderOf (Spin.spinMatrix (Spin.quadMinus n F bq cq) s_b) ∧
        (∀ g ∈ Subgroup.centralizer
            ({Spin.spinMatrix (Spin.quadMinus n F bq cq) s} :
              Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) ⊓ glFixing (1 - ε),
          Spin.spinMatrix (Spin.quadMinus n F bq cq) s_b * g *
              (Spin.spinMatrix (Spin.quadMinus n F bq cq) s_b)⁻¹ =
            s₁ * g * s₁⁻¹) := by
  have hS : ∀ a ∈ ({Spin.spinMatrix (Spin.quadMinus n F bq cq) s} :
      Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)),
      ∀ b' ∈ ({Spin.spinMatrix (Spin.quadMinus n F bq cq) s} :
        Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)), Commute a b' := by
    intro a ha b' hb'
    rw [Set.mem_singleton_iff] at ha hb'
    rw [ha, hb']
  have hs' : ∀ t ∈ ({Spin.spinMatrix (Spin.quadMinus n F bq cq) s} :
      Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)),
      Commute (Spin.spinMatrix (Spin.quadMinus n F bq cq) s_b) t := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hcomm
  obtain ⟨hs_bε, s₁, hs₁def, hs₁mem, hs₁ord, hs₁conj⟩ :=
    rckGLBlock_restrict (S := ({Spin.spinMatrix (Spin.quadMinus n F bq cq) s} :
      Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F))) hS hε.1 hε.2.1 _ hs'
  have hG : IsUnit (LinearMap.toMatrix₂' F
      (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))).det :=
    CFSG.StandardType.ClassicalPosition.Geo.isUnit_det_toMatrix₂'_polarBilin _
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite n F hirr)
  have hpol : ∀ u v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F,
      QuadraticMap.polarBilin (Spin.quadMinus n F bq cq) u v =
        dotProduct u ((LinearMap.toMatrix₂' F
          (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))).mulVec v) := by
    intro u v
    have h := Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix'
      (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))) u v
    rw [Matrix.toBilin'_toMatrix'] at h
    exact h
  have hQ : ∀ u v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F,
      Spin.quadMinus n F bq cq (u + v) =
        Spin.quadMinus n F bq cq u + Spin.quadMinus n F bq cq v +
          dotProduct u ((LinearMap.toMatrix₂' F
            (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))).mulVec v) := by
    intro u v
    rw [QuadraticMap.map_add (⇑(Spin.quadMinus n F bq cq)) u v,
      ← QuadraticMap.polarBilin_apply_apply (Spin.quadMinus n F bq cq) u v, hpol u v]
  have hquad : ∀ v, Spin.quadMinus n F bq cq
      ((s₁ : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ v) =
      Spin.quadMinus n F bq cq v :=
    rckGLBlock_restrict_quad hG hε.2.2.2.1 hε.2.1 hQ
      (fun v => Spin.spinMatrix_mem (Spin.quadMinus n F bq cq) s_b v) hs_bε hs₁def
  exact ⟨s₁, hs₁mem, hquad, hs₁ord, hs₁conj⟩

private lemma rck_spin_restrict_omega_POmegaMinus {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    {s : spinGroup (Spin.quadMinus n F bq cq)}
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F (Units.val '' {Spin.spinMatrix (Spin.quadMinus n F bq cq) s})) ε)
    {s_b : spinGroup (Spin.quadMinus n F bq cq)} {p : ℕ} (hp : Odd p) (hspow : s_b ^ p = 1)
    (hcomm : Commute (Spin.spinMatrix (Spin.quadMinus n F bq cq) s_b)
      (Spin.spinMatrix (Spin.quadMinus n F bq cq) s)) :
    ∃ s₁ : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
      s₁ ∈ Subgroup.centralizer
          ({Spin.spinMatrix (Spin.quadMinus n F bq cq) s} :
            Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) ⊓ glFixing (1 - ε) ∧
        s₁ ∈ CFSG.Open.StatedOmega ⇑(Spin.quadMinus n F bq cq) ∧
        (∀ g ∈ Subgroup.centralizer
            ({Spin.spinMatrix (Spin.quadMinus n F bq cq) s} :
              Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) ⊓ glFixing (1 - ε),
          Spin.spinMatrix (Spin.quadMinus n F bq cq) s_b * g *
              (Spin.spinMatrix (Spin.quadMinus n F bq cq) s_b)⁻¹ =
            s₁ * g * s₁⁻¹) := by
  obtain ⟨s₁, hs₁mem, hquad, hs₁ord, hs₁conj⟩ :=
    rck_spin_restrict_POmegaMinus hirr hε hcomm
  have hdvd : orderOf s₁ ∣ p :=
    hs₁ord.trans (orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hspow, map_one]))
  have hs₁p : s₁ ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  obtain ⟨hQnd, hT⟩ :=
    CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := F) (n := n) (b := bq) (c := cq) hn hirr
  have homega : s₁ ∈ CFSG.Open.StatedOmega ⇑(Spin.quadMinus n F bq cq) := by
    refine CFSG.ClassicalGroups.Orthogonal.mem_of_odd_pow_of_sq_mem
      (N := CFSG.Open.StatedOmega ⇑(Spin.quadMinus n F bq cq))
      (fun x hx => ?_) hp hs₁p
    rw [hx]
    exact CFSG.ComponentClassification.RankTwoClassical.sq_mem_statedOmega
      (Spin.quadMinus n F bq cq) hQnd hT hquad
  exact ⟨s₁, hs₁mem, homega, hs₁conj⟩

private lemma rck_lift_block_POmegaMinus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadMinus n F bq cq) →* X}
    {s : spinGroup (Spin.quadMinus n F bq cq)} {b : X}
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F (Units.val '' {Spin.spinMatrix (Spin.quadMinus n F bq cq) s})) ε)
    {J' : Subgroup (spinGroup (Spin.quadMinus n F bq cq))}
    (hJ'G : J' ≤ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
      {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε)
    {s_b : spinGroup (Spin.quadMinus n F bq cq)}
    (hs_b : ∀ u, b⁻¹ * ψ u * b = ψ (s_b * u * s_b⁻¹))
    {p : ℕ} (hp : Odd p) (hspow : s_b ^ p = 1)
    (hcomm : Commute (Spin.spinMatrix (Spin.quadMinus n F bq cq) s_b)
      (Spin.spinMatrix (Spin.quadMinus n F bq cq) s)) :
    ∃ s₁' : spinGroup (Spin.quadMinus n F bq cq),
      s₁' ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
        {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε ∧
        (∀ y ∈ J', b⁻¹ * ψ y * b = ψ (s₁' * y * s₁'⁻¹)) := by
  obtain ⟨s₁, hs₁mem, hs₁omega, hs₁conj⟩ :=
    rck_spin_restrict_omega_POmegaMinus hirr hn hε hp hspow hcomm
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadMinus n F bq cq)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero F 2))
  have hmem : s₁ ∈ (Spin.spinMatrix (Spin.quadMinus n F bq cq)).range := by
    rw [CFSG.StandardType.AutOm.range_spinMatrix_minus hn hirr]
    exact hs₁omega
  obtain ⟨s₁', hs₁'⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨s₁', ?_, ?_⟩
  · rw [glBlockCentralizer, Subgroup.mem_comap, hs₁']
    exact hs₁mem
  · intro y hy
    have hyblock : Spin.spinMatrix (Spin.quadMinus n F bq cq) y ∈
        Subgroup.centralizer ({Spin.spinMatrix (Spin.quadMinus n F bq cq) s} :
          Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp (hJ'G hy)
    have hyEq := hs₁conj _ hyblock
    rw [hs_b y]
    refine congrArg ψ (hinj ?_)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hs₁']
    exact hyEq

private lemma rck_lift_map_eq_POmegaMinus {n : ℕ} {F : Type} [Field F] {bq cq : F}
    {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadMinus n F bq cq) →* X}
    {J' : Subgroup (spinGroup (Spin.quadMinus n F bq cq))} {b : X}
    (hbK : b ∈ Subgroup.normalizer ((J'.map ψ : Subgroup X) : Set X))
    {s₁' : spinGroup (Spin.quadMinus n F bq cq)}
    (hact : ∀ y ∈ J', b⁻¹ * ψ y * b = ψ (s₁' * y * s₁'⁻¹)) :
    (J'.map (MulAut.conj s₁').toMonoidHom).map ψ = J'.map ψ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [Subgroup.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hact y hy]
    exact (Subgroup.mem_normalizer_iff''.mp hbK (ψ y)).mp
      (Subgroup.mem_map_of_mem ψ hy)
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyK : b * ψ y * b⁻¹ ∈ J'.map ψ :=
      (Subgroup.mem_normalizer_iff.mp hbK (ψ y)).mp (Subgroup.mem_map_of_mem ψ hy)
    rw [Subgroup.mem_map] at hyK
    obtain ⟨y', hy', hy'eq⟩ := hyK
    refine ⟨s₁' * y' * s₁'⁻¹, ?_, ?_⟩
    · change s₁' * y' * s₁'⁻¹ ∈
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s₁')) J'
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
        Subgroup.mem_map_of_mem (MulAut.conj s₁').toMonoidHom hy'
    · rw [show ψ (s₁' * y' * s₁'⁻¹) = b⁻¹ * ψ y' * b from (hact y' hy').symm,
        hy'eq]
      group

theorem rckLiftToBlock_POmegaMinus {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {X : Type} [Group X]
    {ψ : ↥(spinGroup (Spin.quadMinus n F bq cq)) →* X}
    (hker : ψ.ker ≤ Subgroup.center ↥(spinGroup (Spin.quadMinus n F bq cq)))
    {s : ↥(spinGroup (Spin.quadMinus n F bq cq))} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F (Units.val '' {Spin.spinMatrix (Spin.quadMinus n F bq cq) s})) ε)
    {J' : Subgroup ↥(spinGroup (Spin.quadMinus n F bq cq))}
    (hJ'G : J' ≤ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
      {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε)
    (hperf : ⁅J', J'⁆ = J') {p : ℕ} (hp : Odd p) {b : X} (hbp : b ^ p = 1)
    (hbN : b ∈ Subgroup.normalizer (ψ.range : Set X))
    (hbID : GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ b) (hbe : Commute b e)
    (hbK : b ∈ Subgroup.normalizer ((J'.map ψ : Subgroup X) : Set X)) :
    ∃ s₁ ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
        {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε,
      s₁ ∈ Subgroup.normalizer (J' : Set ↥(spinGroup (Spin.quadMinus n F bq cq))) ∧
        ∀ y ∈ J', b⁻¹ * ψ y * b = ψ (s₁ * y * s₁⁻¹) := by
  obtain ⟨s_b, hs_b, hcomm⟩ := rck_lift_choose_POmegaMinus hirr hn hker hs hbID hbe
  have hspow : s_b ^ p = 1 :=
    spin_pow_eq_one_of_conj_POmegaMinus hirr hn ψ hker hbp hs_b
  obtain ⟨s₁', hblock, hact⟩ :=
    rck_lift_block_POmegaMinus hirr hn hε hJ'G hs_b hp hspow hcomm
  have hmap : (J'.map (MulAut.conj s₁').toMonoidHom).map ψ = J'.map ψ :=
    rck_lift_map_eq_POmegaMinus hbK hact
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadMinus n F bq cq)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero F 2))
  haveI : Finite (spinGroup (Spin.quadMinus n F bq cq)) :=
    Finite.of_injective _ hinj
  have hZnorm : ψ.ker ≤
      Subgroup.normalizer (J' : Set (spinGroup (Spin.quadMinus n F bq cq))) := by
    intro z hz
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    have hzy : z * y = y * z := (Subgroup.mem_center_iff.mp (hker hz) y).symm
    rw [show z * y * z⁻¹ = y from by rw [hzy]; group]
  have hcent : ψ.ker ≤
      Subgroup.centralizer (J' : Set (spinGroup (Spin.quadMinus n F bq cq))) := by
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun y _ => ?_
    exact Subgroup.mem_center_iff.mp (hker hz) y
  have hcentSup : ψ.ker ≤ Subgroup.centralizer
      ((J' ⊔ ψ.ker : Subgroup (spinGroup (Spin.quadMinus n F bq cq))) :
        Set (spinGroup (Spin.quadMinus n F bq cq))) := by
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun y _ => ?_
    exact Subgroup.mem_center_iff.mp (hker hz) y
  have hle : J'.map (MulAut.conj s₁').toMonoidHom ≤ J' := by
    have hsub : J'.map (MulAut.conj s₁').toMonoidHom ≤ J' ⊔ ψ.ker := by
      intro x hx
      have hx' : ψ x ∈ J'.map ψ := by
        rw [← hmap]
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      obtain ⟨j, hj, hψj⟩ := Subgroup.mem_map.mp hx'
      have hmem : j⁻¹ * x ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hψj]
        group
      rw [show x = j * (j⁻¹ * x) from by group]
      exact (J' ⊔ ψ.ker).mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hmem)
    have hperf' : ⁅J'.map (MulAut.conj s₁').toMonoidHom,
        J'.map (MulAut.conj s₁').toMonoidHom⁆ = J'.map (MulAut.conj s₁').toMonoidHom := by
      rw [← Subgroup.map_commutator (f := (MulAut.conj s₁').toMonoidHom), hperf]
    refine hperf'.ge.trans ?_
    calc ⁅J'.map (MulAut.conj s₁').toMonoidHom, J'.map (MulAut.conj s₁').toMonoidHom⁆
        ≤ ⁅J' ⊔ ψ.ker, J' ⊔ ψ.ker⁆ := Subgroup.commutator_mono hsub hsub
      _ = J' := by
          rw [CFSG.commutator_sup_eq_commutator_left hZnorm hcentSup, Subgroup.commutator_comm,
            CFSG.commutator_sup_eq_commutator_left hZnorm hcent, hperf]
  have hEq : J'.map (MulAut.conj s₁').toMonoidHom = J' := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj s₁').injective]
  exact ⟨s₁', hblock, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq, hact⟩

end CFSG.StandardType.RCKRP
