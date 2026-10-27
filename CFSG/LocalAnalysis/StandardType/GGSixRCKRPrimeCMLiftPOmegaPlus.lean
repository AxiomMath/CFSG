module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMRestrict
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepAPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoOrth
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Aut
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

private lemma rck_lift_choose {n f : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField 2 f))))
    {s : spinGroup (Spin.quadPlus n (GaloisField 2 f))} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {b : X}
    (hbID : GGPsiInnerDiag (Spin.plusDatum n (GaloisField 2 f) hn) ψ b) (hbe : Commute b e) :
    ∃ s_b : spinGroup (Spin.quadPlus n (GaloisField 2 f)),
      (∀ u, b⁻¹ * ψ u * b = ψ (s_b * u * s_b⁻¹)) ∧
        Commute (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s_b)
          (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s) := by
  obtain ⟨s_b, hs_b⟩ := exists_conj_eq_POmegaPlus n (GaloisField 2 f) hn ψ hker hbID
  have hcommSub : Commute s_b s :=
    conj_eq_commute_POmegaPlus n (GaloisField 2 f) hn ψ hker hbe hs_b hs
  exact ⟨s_b, hs_b, hcommSub.map _⟩

private lemma rck_spin_restrict {n f : ℕ}
    {s : spinGroup (Spin.quadPlus n (GaloisField 2 f))}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s})) ε)
    {s_b : spinGroup (Spin.quadPlus n (GaloisField 2 f))}
    (hcomm : Commute (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s_b)
      (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s)) :
    ∃ s₁ : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      s₁ ∈ Subgroup.centralizer
          ({Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} :
            Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) ⊓ glFixing (1 - ε) ∧
        (∀ v, Spin.quadPlus n (GaloisField 2 f)
          ((s₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ v) =
          Spin.quadPlus n (GaloisField 2 f) v) ∧
        orderOf s₁ ∣ orderOf (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s_b) ∧
        (∀ g ∈ Subgroup.centralizer
            ({Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} :
              Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) ⊓ glFixing (1 - ε),
          Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s_b * g *
              (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s_b)⁻¹ =
            s₁ * g * s₁⁻¹) := by
  have hS : ∀ a ∈ ({Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} :
      Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      ∀ b' ∈ ({Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} :
        Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))), Commute a b' := by
    intro a ha b' hb'
    rw [Set.mem_singleton_iff] at ha hb'
    rw [ha, hb']
  have hs' : ∀ t ∈ ({Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} :
      Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      Commute (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s_b) t := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hcomm
  obtain ⟨hs_bε, s₁, hs₁def, hs₁mem, hs₁ord, hs₁conj⟩ :=
    rckGLBlock_restrict (S := ({Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} :
      Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))) hS hε.1 hε.2.1 _ hs'
  have hG : IsUnit (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)))).det :=
    CFSG.StandardType.ClassicalPosition.Geo.isUnit_det_toMatrix₂'_polarBilin _
      (Spin.nondegenerate_polarBilin_quadPlus n (GaloisField 2 f))
  have hpol : ∀ u v : Fin n ⊕ Fin n → GaloisField 2 f,
      QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)) u v =
        dotProduct u ((LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)))).mulVec v) := by
    intro u v
    have h := Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix'
      (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)))) u v
    rw [Matrix.toBilin'_toMatrix'] at h
    exact h
  have hQ : ∀ u v : Fin n ⊕ Fin n → GaloisField 2 f,
      Spin.quadPlus n (GaloisField 2 f) (u + v) =
        Spin.quadPlus n (GaloisField 2 f) u + Spin.quadPlus n (GaloisField 2 f) v +
          dotProduct u ((LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)))).mulVec v) := by
    intro u v
    rw [QuadraticMap.map_add (⇑(Spin.quadPlus n (GaloisField 2 f))) u v,
      ← QuadraticMap.polarBilin_apply_apply (Spin.quadPlus n (GaloisField 2 f)) u v, hpol u v]
  have hquad : ∀ v, Spin.quadPlus n (GaloisField 2 f)
      ((s₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ v) =
      Spin.quadPlus n (GaloisField 2 f) v :=
    rckGLBlock_restrict_quad hG hε.2.2.2.1 hε.2.1 hQ
      (fun v => Spin.spinMatrix_mem (Spin.quadPlus n (GaloisField 2 f)) s_b v) hs_bε hs₁def
  exact ⟨s₁, hs₁mem, hquad, hs₁ord, hs₁conj⟩

private lemma rck_spin_restrict_omega {n f : ℕ} (hn : 3 ≤ n)
    {s : spinGroup (Spin.quadPlus n (GaloisField 2 f))}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s})) ε)
    {s_b : spinGroup (Spin.quadPlus n (GaloisField 2 f))} {p : ℕ} (hp : Odd p)
    (hspow : s_b ^ p = 1)
    (hcomm : Commute (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s_b)
      (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s)) :
    ∃ s₁ : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      s₁ ∈ Subgroup.centralizer
          ({Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} :
            Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) ⊓ glFixing (1 - ε) ∧
        s₁ ∈ CFSG.Open.StatedOmega ⇑(Spin.quadPlus n (GaloisField 2 f)) ∧
        (∀ g ∈ Subgroup.centralizer
            ({Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} :
              Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) ⊓ glFixing (1 - ε),
          Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s_b * g *
              (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s_b)⁻¹ =
            s₁ * g * s₁⁻¹) := by
  obtain ⟨s₁, hs₁mem, hquad, hs₁ord, hs₁conj⟩ := rck_spin_restrict hε hcomm
  have hdvd : orderOf s₁ ∣ p :=
    hs₁ord.trans (orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hspow, map_one]))
  have hs₁p : s₁ ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  have h2k : ((p + 1) / 2) * 2 = p + 1 := by
    have h := Nat.two_mul_div_two_of_even hp.one_add
    rw [Nat.mul_comm, Nat.add_comm 1 p] at h
    exact h
  have hB2 : (s₁ ^ ((p + 1) / 2)) ^ 2 = s₁ := by
    rw [← pow_mul, h2k, pow_succ, hs₁p, one_mul]
  have hpowiso : ∀ k : ℕ, ∀ v, Spin.quadPlus n (GaloisField 2 f)
      (((s₁ ^ k : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ v) =
      Spin.quadPlus n (GaloisField 2 f) v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec]
        exact (ih ((s₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ v)).trans
          (hquad v)
  have homega : s₁ ∈ CFSG.Open.StatedOmega ⇑(Spin.quadPlus n (GaloisField 2 f)) := by
    have h := CFSG.ComponentClassification.RankTwoClassical.sq_mem_statedOmega
      (Spin.quadPlus n (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus n (GaloisField 2 f))
      (CFSG.ComponentClassification.RankTwoClassical.exists_totallySingular_quadPlus hn
        (GaloisField 2 f))
      (M := s₁ ^ ((p + 1) / 2)) (hpowiso _)
    rwa [hB2] at h
  exact ⟨s₁, hs₁mem, homega, hs₁conj⟩

private lemma rck_lift_block {n f : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    {s : spinGroup (Spin.quadPlus n (GaloisField 2 f))} {b : X}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s})) ε)
    {J' : Subgroup (spinGroup (Spin.quadPlus n (GaloisField 2 f)))}
    (hJ'G : J' ≤ glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
      {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε)
    {s_b : spinGroup (Spin.quadPlus n (GaloisField 2 f))}
    (hs_b : ∀ u, b⁻¹ * ψ u * b = ψ (s_b * u * s_b⁻¹))
    {p : ℕ} (hp : Odd p) (hspow : s_b ^ p = 1)
    (hcomm : Commute (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s_b)
      (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s)) :
    ∃ s₁' : spinGroup (Spin.quadPlus n (GaloisField 2 f)),
      s₁' ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
        {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε ∧
        (∀ y ∈ J', b⁻¹ * ψ y * b = ψ (s₁' * y * s₁'⁻¹)) := by
  obtain ⟨s₁, hs₁mem, hs₁omega, hs₁conj⟩ := rck_spin_restrict_omega hn hε hp hspow hcomm
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero (GaloisField 2 f) 2))
  have hmem : s₁ ∈ (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))).range := by
    rw [Spin.range_spinMatrix_quadPlus hn, ← Spin.coe_quadPlus]
    exact hs₁omega
  obtain ⟨s₁', hs₁'⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨s₁', ?_, ?_⟩
  · rw [glBlockCentralizer, Subgroup.mem_comap, hs₁']
    exact hs₁mem
  · intro y hy
    have hyblock : Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) y ∈
        Subgroup.centralizer ({Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} :
          Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp (hJ'G hy)
    have hyEq := hs₁conj _ hyblock
    rw [hs_b y]
    refine congrArg ψ (hinj ?_)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hs₁']
    exact hyEq

private lemma rck_lift_map_eq {n f : ℕ} {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    {J' : Subgroup (spinGroup (Spin.quadPlus n (GaloisField 2 f)))} {b : X}
    (hbK : b ∈ Subgroup.normalizer ((J'.map ψ : Subgroup X) : Set X))
    {s₁' : spinGroup (Spin.quadPlus n (GaloisField 2 f))}
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

theorem rckLiftToBlock_POmegaPlus {n f : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField 2 f))))
    {s : spinGroup (Spin.quadPlus n (GaloisField 2 f))} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s})) ε)
    {J' : Subgroup (spinGroup (Spin.quadPlus n (GaloisField 2 f)))}
    (hJ'G : J' ≤ glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
      {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε)
    (hperf : ⁅J', J'⁆ = J') {p : ℕ} (hp : Odd p) {b : X} (hbp : b ^ p = 1)
    (hbN : b ∈ Subgroup.normalizer (ψ.range : Set X))
    (hbID : GGPsiInnerDiag (Spin.plusDatum n (GaloisField 2 f) hn) ψ b) (hbe : Commute b e)
    (hbK : b ∈ Subgroup.normalizer ((J'.map ψ : Subgroup X) : Set X)) :
    ∃ s₁ ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
        {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε,
      s₁ ∈ Subgroup.normalizer (J' : Set (spinGroup (Spin.quadPlus n (GaloisField 2 f)))) ∧
        ∀ y ∈ J', b⁻¹ * ψ y * b = ψ (s₁ * y * s₁⁻¹) := by
  obtain ⟨s_b, hs_b, hcomm⟩ := rck_lift_choose hn hker hs hbID hbe
  have hspow : s_b ^ p = 1 := spin_pow_eq_one_of_conj_POmegaPlus hn ψ hker hbp hs_b
  obtain ⟨s₁', hblock, hact⟩ := rck_lift_block hn hε hJ'G hs_b hp hspow hcomm
  have hmap : (J'.map (MulAut.conj s₁').toMonoidHom).map ψ = J'.map ψ :=
    rck_lift_map_eq hbK hact
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero (GaloisField 2 f) 2))
  haveI : Finite (spinGroup (Spin.quadPlus n (GaloisField 2 f))) :=
    Finite.of_injective _ hinj
  have hZnorm : ψ.ker ≤
      Subgroup.normalizer (J' : Set (spinGroup (Spin.quadPlus n (GaloisField 2 f)))) := by
    intro z hz
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    have hzy : z * y = y * z := (Subgroup.mem_center_iff.mp (hker hz) y).symm
    rw [show z * y * z⁻¹ = y from by rw [hzy]; group]
  have hcent : ψ.ker ≤
      Subgroup.centralizer (J' : Set (spinGroup (Spin.quadPlus n (GaloisField 2 f)))) := by
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun y _ => ?_
    exact Subgroup.mem_center_iff.mp (hker hz) y
  have hcentSup : ψ.ker ≤ Subgroup.centralizer
      ((J' ⊔ ψ.ker : Subgroup (spinGroup (Spin.quadPlus n (GaloisField 2 f)))) :
        Set (spinGroup (Spin.quadPlus n (GaloisField 2 f)))) := by
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
