module

public import CFSG.ClassicalGroups.QuadraticInvolutionCentralizer
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISpBlock

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal CFSG.ClassicalGroups.QuadraticCentralizer

theorem spin_pCore_centralizer_of_fix_kernel
    {F N : Type} [Field F] [Finite F] [CharP F 2] [Fintype N] [DecidableEq N]
    (Q : QuadraticForm F (N → F)) (hnd : Q.polarBilin.Nondegenerate)
    (hinj : Function.Injective (Spin.spinMatrix Q))
    (hΩ : (Spin.spinAction Q).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd)
    (r : spinGroup Q) (hr : r ^ 2 = 1)
    (hAlt : ∀ x, Q.polarBilin x (Spin.spinAction Q r x - x) = 0)
    (V : Subgroup (spinGroup Q))
    (hFix : ∀ v ∈ V, ∀ x, Spin.spinAction Q r x = x → Spin.spinAction Q v x = x) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({r} : Set (spinGroup Q))) ≤
      Subgroup.centralizer (V : Set (spinGroup Q)) := by
  let f := Spin.spinToOrthogonalGroup Q
  have hf : Function.Injective f := by
    intro x y hxy
    have hAct : Spin.spinAction Q x = Spin.spinAction Q y := by
      apply LinearEquiv.ext
      intro v
      rw [← Spin.coe_spinToOrthogonalGroup_apply Q x v,
        ← Spin.coe_spinToOrthogonalGroup_apply Q y v]
      exact congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q => g.1 v) hxy
    apply hinj
    apply Units.ext
    rw [Spin.coe_spinMatrix, Spin.coe_spinMatrix, hAct]
  have hRange : f.range = (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    ext g
    rw [Subgroup.mem_subgroupOf, ← hΩ]
    change (∃ x, f x = g) ↔ ∃ x, Spin.spinAction Q x = g.1
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      apply LinearEquiv.ext
      intro v
      exact (Spin.coe_spinToOrthogonalGroup_apply Q x v).symm
    · rintro ⟨x, hx⟩
      refine ⟨x, Subtype.ext ?_⟩
      apply LinearEquiv.ext
      intro v
      rw [Spin.coe_spinToOrthogonalGroup_apply, hx]
  have hNormal : f.range.Normal := by
    rw [hRange, ← CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker Q hnd]
    infer_instance
  have hNondeg : ∀ w : N → F, w ≠ 0 → ∃ a, Q.polarBilin w a ≠ 0 := by
    intro w hw
    by_contra hc
    push Not at hc
    exact hw (hnd.1 w hc)
  refine pCoreOf_centralizer_le_centralizer_of_injective_of_fix_kernel
    Q hNondeg f hf hNormal r hr ?_ V ?_
  · simpa only [f, Spin.coe_spinToOrthogonalGroup_apply] using hAlt
  · simpa only [f, Spin.coe_spinToOrthogonalGroup_apply] using hFix

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.StandardType
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits CFSG.StandardType.RCKK1IIISU
open CFSG.StandardType.ClassicalPosition

theorem k2At_of_unitary_linear_embedding_orthogonal
    {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 1) (N → GaloisField 2 1))
    (hnd : Q.polarBilin.Nondegenerate) (hinj : Function.Injective (Spin.spinMatrix Q))
    (hΩ : (Spin.spinAction Q).range = CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd)
    {m : ℕ} (hm : 4 ≤ m) [Algebra (GaloisField 2 1) SUF]
    (ι : SUG m →* spinGroup Q)
    (E : (Fin m → SUF) →ₗ[GaloisField 2 1] (N → GaloisField 2 1))
    (hE : Function.Injective E) (C : Submodule (GaloisField 2 1) (N → GaloisField 2 1))
    (hAct : ∀ g x, Spin.spinAction Q (ι g) (E x) = E (natRep (SU SUσ m) g x))
    (hFix : ∀ g w, w ∈ C → Spin.spinAction Q (ι g) w = w)
    (hSplit : ∀ z, ∃ x, ∃ w ∈ C, z = E x + w)
    (hAlt : ∀ g, g ^ 2 = 1 → ∀ z, Q.polarBilin z (Spin.spinAction Q (ι g) z - z) = 0)
    {V : Subgroup (SUG m)} {r : SUG m}
    (hFour : FourAt (⊤ : Subgroup (SUG m)) V r)
    (hCore : CoreCommAt (⊤ : Subgroup (SUG m)) V r)
    (hRank : (mat SUσ m r - 1).rank = 2) :
    K2At (⊤ : Subgroup (spinGroup Q)) (V.map ι) (ι r) := by
  have hr : r ^ 2 = 1 := hFour.2.2.1.2 r hFour.1
  have hSourceFix := rckSU_fixes_fixed_space_of_rank_two hm hFour hCore hRank
  have hr' : (ι r) ^ 2 = 1 := by rw [← map_pow, hr, map_one]
  have hK2 := spin_pCore_centralizer_of_fix_kernel Q hnd hinj hΩ (ι r) hr'
    (hAlt r hr) (V.map ι) ?_
  · simpa only [K2At, top_inf_eq] using hK2.trans (Subgroup.centralizer_le_normalizer _)
  intro v hv z hRz
  obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
  obtain ⟨x, w, hw, hz⟩ := hSplit z
  have hRx : natRep (SU SUσ m) r x = x := by
    apply hE
    rw [hz, map_add, hAct, hFix r w hw] at hRz
    exact add_right_cancel hRz
  rw [hz, map_add, hAct, hFix v₀ w hw, hSourceFix v₀ hv₀ x hRx]

section BlockCertificates


theorem k2At_of_shortAt_unitary_orthogonal_embedding
    {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 1) (N → GaloisField 2 1))
    (hnd : Q.polarBilin.Nondegenerate) (hinj : Function.Injective (Spin.spinMatrix Q))
    (hΩ : (Spin.spinAction Q).range = CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd)
    {m : ℕ} (hm : 4 ≤ m) [Algebra (GaloisField 2 1) SUF]
    (ι : SUG m →* spinGroup Q) (hι : Function.Injective ι)
    {J : Subgroup (spinGroup Q)} (hRange : ι.range = J)
    (E : (Fin m → SUF) →ₗ[GaloisField 2 1] (N → GaloisField 2 1))
    (hE : Function.Injective E) (C : Submodule (GaloisField 2 1) (N → GaloisField 2 1))
    (hAct : ∀ g x, Spin.spinAction Q (ι g) (E x) = E (natRep (SU SUσ m) g x))
    (hFix : ∀ g w, w ∈ C → Spin.spinAction Q (ι g) w = w)
    (hSplit : ∀ z, ∃ x, ∃ w ∈ C, z = E x + w)
    (hAlt : ∀ g, g ^ 2 = 1 → ∀ z, Q.polarBilin z (Spin.spinAction Q (ι g) z - z) = 0)
    {V : Subgroup (spinGroup Q)} {r : spinGroup Q}
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At (⊤ : Subgroup (spinGroup Q)) V r := by
  let : Finite (spinGroup Q) := Finite.of_injective (Spin.spinMatrix Q) hinj
  let ιJ : SUG m →* J := ι.codRestrict J (by
    intro g
    rw [← hRange]
    exact ⟨g, rfl⟩)
  have hιJ : Function.Bijective ιJ := by
    constructor
    · intro x y hxy
      exact hι (congrArg Subtype.val hxy)
    · intro j
      have hj : (j : spinGroup Q) ∈ ι.range := hRange.symm ▸ j.2
      obtain ⟨g, hg⟩ := hj
      exact ⟨g, Subtype.ext hg⟩
  let η : J ≃* SUG m := (MulEquiv.ofBijective ιJ hιJ).symm
  have hComp (j : J) : ι (η j) = (j : spinGroup Q) :=
    congrArg Subtype.val (η.symm_apply_apply j)
  have hrJ : r ∈ J := hFour.2.1 hFour.1
  have hFour' := fourAt_map_mulEquiv η hrJ hFour
  have hCore' := coreCommAt_map_mulEquiv η hrJ hCore
  obtain ⟨rJ, hr, hPos⟩ := hShort
  have hr1 : rJ ≠ 1 := by
    intro h
    apply hFour.2.2.2.2.1
    rw [← hr, h]
    rfl
  have hr2 : rJ ^ 2 = 1 := by
    apply Subtype.ext
    change (rJ : spinGroup Q) ^ 2 = 1
    rw [hr]
    exact hFour.2.2.1.2 r hFour.1
  have hRank := rckSURank_of_shortAt_model hm η hr1 hr2 hPos
  have hSub : (⟨r, hrJ⟩ : J) = rJ := Subtype.ext hr.symm
  have hRank' : (mat SUσ m (η ⟨r, hrJ⟩) - 1).rank = 2 := by
    simpa only [hSub] using hRank
  have hK2 := k2At_of_unitary_linear_embedding_orthogonal Q hnd hinj hΩ hm
    ι E hE C hAct hFix hSplit hAlt hFour' hCore' hRank'
  have hV : ((V.subgroupOf J).map η.toMonoidHom).map ι = V := by
    rw [Subgroup.map_map]
    have hHom : ι.comp η.toMonoidHom = J.subtype := MonoidHom.ext hComp
    rw [hHom, Subgroup.map_subgroupOf_eq_of_le hFour.2.1]
  have hR : ι (η ⟨r, hrJ⟩) = r := hComp ⟨r, hrJ⟩
  rwa [hV, hR] at hK2

theorem k2At_of_shortAt_selfDualTwo_plus_block
    (k : ℕ) (S : Set (Matrix.GeneralLinearGroup (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 1)) (LinearMap.toMatrix₂' (GaloisField 2 1)
      (Spin.quadPlus (k + 3) (GaloisField 2 1)).polarBilin) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 4)
    {J V : Subgroup (spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 1)))}
    {r : spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 1))}
    (hJ : CFSG.Assembly.IsComponentOf J ⁅glBlockCentralizer
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))) S e,
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))) S e⁆)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At (⊤ : Subgroup (spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 1)))) V r := by
  obtain ⟨m, A, ι, E, C, hm, hι, hRange, hE, hAct, hFix, hSplit, hAlt⟩ :=
    exists_linearBlockModel_selfDualTwo_POmegaPlus_at_two k S hSU hS hodd
      he hadj hdeg₁ hdeg₂ hJ
  let : Algebra (GaloisField 2 1) SUF := A
  have hnd := Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 1)
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Spin.ker_spinMatrix_quadPlus_eq_bot (K := GaloisField 2 1) (n := k + 3)
      (CharP.cast_eq_zero (GaloisField 2 1) 2)
  exact k2At_of_shortAt_unitary_orthogonal_embedding _ hnd hinj
    (range_spinAction_quadPlus_eq_omegaGroup k 1) hm ι hι hRange E hE C hAct hFix hSplit hAlt
    hFour hCore hShort

theorem k2At_of_shortAt_selfDualTwo_minus_block
    (n : ℕ) (hn : 4 ≤ n)
    (S : Set (Matrix.GeneralLinearGroup (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 1)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 1)) (LinearMap.toMatrix₂' (GaloisField 2 1)
      (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2).polarBilin)
      e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 4)
    {J V : Subgroup (spinGroup (Spin.quadMinus n (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2))}
    {r : spinGroup (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)}
    (hJ : CFSG.Assembly.IsComponentOf J ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n
      (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) S e,
      glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 1)
        (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) S e⁆)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At (⊤ : Subgroup (spinGroup (Spin.quadMinus n (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2))) V r := by
  obtain ⟨m, A, ι, E, C, hm, hι, hRange, hE, hAct, hFix, hSplit, hAlt⟩ :=
    exists_linearBlockModel_selfDualTwo_POmegaMinus_at_two n hn S hSU hS hodd
      he hadj hdeg₁ hdeg₂ hJ
  let : Algebra (GaloisField 2 1) SUF := A
  have hnd := Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 1)
    (minusCoeffs_irr 2 1)
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 1) CharTwo.two_eq_zero
  exact k2At_of_shortAt_unitary_orthogonal_embedding _ hnd hinj
    (range_spinAction_quadMinus_eq_omegaGroup n 1 hn) hm ι hι hRange E hE C hAct hFix hSplit hAlt
    hFour hCore hShort

@[expose] def FixedOrthBlockAt {X : Type} [Group X] (K J : Subgroup X) : Prop :=
  (∃ (k : ℕ) (η : K ≃* spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 1)))
      (S : Set (Matrix.GeneralLinearGroup (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1)))
      (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1)),
    (∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))).range) ∧
    (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧ (∀ s ∈ S, Odd (orderOf s)) ∧
    IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e ∧
    formAdj (RingHom.id (GaloisField 2 1)) (LinearMap.toMatrix₂' (GaloisField 2 1)
      (Spin.quadPlus (k + 3) (GaloisField 2 1)).polarBilin) e = e ∧
    2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e ∧
    blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 4 ∧
    CFSG.Assembly.IsComponentOf ((J.subgroupOf K).map η.toMonoidHom) ⁅glBlockCentralizer
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))) S e,
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1))) S e⁆) ∨
  (∃ (n : ℕ) (_ : 4 ≤ n)
      (η : K ≃* spinGroup (Spin.quadMinus n (GaloisField 2 1)
        (minusCoeffs 2 1).1 (minusCoeffs 2 1).2))
      (S : Set (Matrix.GeneralLinearGroup (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 1)))
      (e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (GaloisField 2 1)),
    (∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)).range) ∧
    (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧ (∀ s ∈ S, Odd (orderOf s)) ∧
    IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e ∧
    formAdj (RingHom.id (GaloisField 2 1)) (LinearMap.toMatrix₂' (GaloisField 2 1)
      (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2).polarBilin)
      e = e ∧
    2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e ∧
    blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 4 ∧
    CFSG.Assembly.IsComponentOf ((J.subgroupOf K).map η.toMonoidHom) ⁅glBlockCentralizer (Spin.spinMatrix
      (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) S e,
      glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 1)
        (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) S e⁆)

theorem k2At_of_fixedOrthBlockAt
    {X : Type} [Group X] [Finite X] {K J V : Subgroup X} {r : X}
    (hBlock : FixedOrthBlockAt K J) (hJK : J ≤ K)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r := by
  have hrK : r ∈ K := hJK (hFour.2.1 hFour.1)
  rcases hBlock with hPlus | hMinus
  · obtain ⟨k, η, S, e, hSU, hS, hodd, he, hadj, hdeg₁, hdeg₂, hJ⟩ := hPlus
    have hFour' := fourAt_subgroup_map_mulEquiv η hJK hrK hFour
    have hCore' := coreCommAt_subgroup_map_mulEquiv η hJK hrK hCore
    have hShort' := shortAt_map_mulEquiv η hJK hShort
    have hK2 := k2At_of_shortAt_selfDualTwo_plus_block k S hSU hS hodd
      he hadj hdeg₁ hdeg₂ hJ hFour' hCore' hShort'
    apply k2At_of_mulEquiv η hrK (hFour.2.1.trans hJK)
    simpa only [K2At, top_inf_eq] using hK2
  · obtain ⟨n, hn, η, S, e, hSU, hS, hodd, he, hadj, hdeg₁, hdeg₂, hJ⟩ := hMinus
    have hFour' := fourAt_subgroup_map_mulEquiv η hJK hrK hFour
    have hCore' := coreCommAt_subgroup_map_mulEquiv η hJK hrK hCore
    have hShort' := shortAt_map_mulEquiv η hJK hShort
    have hK2 := k2At_of_shortAt_selfDualTwo_minus_block n hn S hSU hS hodd
      he hadj hdeg₁ hdeg₂ hJ hFour' hCore' hShort'
    apply k2At_of_mulEquiv η hrK (hFour.2.1.trans hJK)
    simpa only [K2At, top_inf_eq] using hK2

end BlockCertificates

end CFSG.StandardType.RCKC1
