module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.LocalAnalysis.StandardType.GGK1DKind
public import CFSG.LocalAnalysis.StandardType.GGK1DWitt
public import CFSG.LocalAnalysis.StandardType.GGK1DPos
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalDiag
public import CFSG.LocalAnalysis.StandardType.GGK1CBlFF
public import CFSG.LocalAnalysis.StandardType.GGK1CBlIdx
public import CFSG.LocalAnalysis.StandardType.GGK1CBlCl
public import CFSG.LocalAnalysis.StandardType.GGK1CBlSu
public import CFSG.LocalAnalysis.StandardType.GGK1CBlSolv
public import CFSG.CGT.M24R.WrapCtx
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
public import CFSG.CGT.T75P.Inputs
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Sec5One
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial Matrix
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial isometryCentralizer
  IsOrbitRepresentatives)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv)
open CFSG.RankThree.Classical (IsReciprocalTransversal)

private lemma ggK1Df_lin_apply {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) (v : ι → K) : ggK1DLin x v = (x : Matrix ι ι K) *ᵥ v := by
  rw [ggK1DLin, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    Matrix.GeneralLinearGroup.coe_toLin, Matrix.coe_mulVecLin]

private lemma ggK1Df_lin_mul {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (a b : GL ι K) : ggK1DLin (a * b) = ggK1DLin a * ggK1DLin b := by
  ext v
  rw [LinearEquiv.mul_apply, ggK1Df_lin_apply, ggK1Df_lin_apply, ggK1Df_lin_apply,
    Units.val_mul, Matrix.mulVec_mulVec]

private lemma ggK1Df_lin_pow {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) (n : ℕ) : ggK1DLin (x ^ n) = (ggK1DLin x) ^ n := by
  induction n with
  | zero => ext v; rw [pow_zero, pow_zero, ggK1Df_lin_apply]; simp
  | succ n ih => rw [pow_succ, pow_succ, ggK1Df_lin_mul, ih]

private lemma ggK1Df_cast_ne_zero {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) : (p : K) ≠ 0 := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  intro hp0
  have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp hp0
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd).symm

theorem ggK1Df_omegaLift_plus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} (hx : x ^ p = 1) :
    OddOrderIsometry (CFSG.StandardType.TableBOrth.qPlusForm K r) p
      (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) := by
  have hxp : (x : GL (Fin r ⊕ Fin r) K) ^ p = 1 := by
    simpa using congrArg (fun y : ↥(LargeEvenOmega (LargeEvenQPlus K r)) =>
      (y : GL (Fin r ⊕ Fin r) K)) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Df_lin_apply, TableBOrth.coe_qPlusForm]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  · rw [← ggK1Df_lin_pow, hxp]
    ext v; rw [ggK1Df_lin_apply]; simp
  · exact ggK1Df_cast_ne_zero hp hp2 hK
  · intro v hv
    exact (TableBOrth.nondegenerate_qPlusForm (K := K) r).1 v (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w)

theorem ggK1Df_omegaLift_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} (hx : x ^ p = 1) :
    OddOrderIsometry (CFSG.StandardType.TableBOrth.qMinusForm K (r - 1) b c) p
      (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) := by
  have hxp : (x : GL (LargeEvenMinusIdx (r - 1)) K) ^ p = 1 := by
    simpa using congrArg (fun y : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) =>
      (y : GL (LargeEvenMinusIdx (r - 1)) K)) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Df_lin_apply, TableBOrth.coe_qMinusForm]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  · rw [← ggK1Df_lin_pow, hxp]
    ext v; rw [ggK1Df_lin_apply]; simp
  · exact ggK1Df_cast_ne_zero hp hp2 hK
  · intro v hv
    exact (TableBOrth.nondegenerate_qMinusForm (K := K) (r - 1) hirr).1 v (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w)

noncomputable def ggK1Df_mapSub {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} (hscal : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥)
    (S : Subgroup ((ι → K) ≃ₗ[K] (ι → K))) : Subgroup (LargeEvenProj (LargeEvenOmega Q)) :=
  ((S.map (toLinEquiv ι K).symm.toMonoidHom).subgroupOf (LargeEvenOmega Q)).map
    (TableBOrth.projMkEquiv hscal).toMonoidHom

noncomputable def ggK1Df_derivedEquiv {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} (hQ : Q = ⇑Qf)
    (hscal : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥) :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup Qf, TauCeti.QuadraticMap.orthogonalGroup Qf⁆ ≃*
      LargeEvenProj (LargeEvenOmega Q) :=
  let D : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) :=
    ⁅TauCeti.QuadraticMap.orthogonalGroup Qf, TauCeti.QuadraticMap.orthogonalGroup Qf⁆
  (MulEquiv.subgroupMap (toLinEquiv ι K).symm D).trans
    ((MulEquiv.subgroupCongr (by
        rw [← Subgroup.comap_equiv_eq_map_symm (toLinEquiv ι K) D]
        exact (CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ.symm).symm)).trans
      (TableBOrth.projMkEquiv hscal))

private lemma ggK1Df_map_commute {D R : Type*} [Group D] [Group R] (φ : D ≃* R)
    {κ : Type*} {S : κ → Subgroup D}
    (hS : ∀ q q', q ≠ q' → ∀ a ∈ S q, ∀ b ∈ S q', Commute a b) :
    ∀ q q', q ≠ q' → ∀ a ∈ (S q).map φ.toMonoidHom, ∀ b ∈ (S q').map φ.toMonoidHom,
      Commute a b := by
  intro q q' hqq' a ha b hb
  obtain ⟨a', ha', hea⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb', heb⟩ := Subgroup.mem_map.mp hb
  rw [← hea, ← heb]
  exact (hS q q' hqq' a' ha' b' hb').map φ.toMonoidHom

private lemma ggK1Df_map_iSup {D R : Type*} [Group D] [Group R] (φ : D ≃* R)
    {κ : Type*} (S : κ → Subgroup D) :
    ⨆ q, (S q).map φ.toMonoidHom = (⨆ q, S q).map φ.toMonoidHom :=
  (Subgroup.map_iSup φ.toMonoidHom S).symm

private lemma ggK1Df_map_iSupIndep {D R : Type*} [Group D] [Group R] (φ : D ≃* R)
    {κ : Type*} {S : κ → Subgroup D} (hS : iSupIndep S) :
    iSupIndep (fun q => (S q).map φ.toMonoidHom) :=
  iSupIndep.map_orderIso (MulEquiv.mapSubgroup φ) hS

private lemma ggK1Df_map_centralizer {D R : Type*} [Group D] [Group R] (φ : D ≃* R)
    (d : D) : (Subgroup.centralizer ({d} : Set D)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ d} : Set R) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := Subgroup.mem_map.mp hx
    rw [← heq]
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    change φ.toMonoidHom y * φ.toMonoidHom d = φ.toMonoidHom d * φ.toMonoidHom y
    simpa only [map_mul] using congrArg φ.toMonoidHom hy
  · intro hx
    refine Subgroup.mem_map.mpr ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have := congrArg φ.symm hx
    simpa using this

private lemma ggK1Df_map_tame {D R : Type*} [Group D] [Group R] (φ : D ≃* R)
    {S : Subgroup D}
    (h : CFSG.IsQuasisimple ↥⁅S, S⁆ ∨ Group.IsSolvable ↥S) :
    CFSG.IsQuasisimple ↥⁅S.map φ.toMonoidHom, S.map φ.toMonoidHom⁆ ∨
      Group.IsSolvable ↥(S.map φ.toMonoidHom) := by
  rcases h with hq | hs
  · left
    rw [← Subgroup.map_commutator S S φ.toMonoidHom]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap φ ⁅S, S⁆) hq
  · right
    haveI : Group.IsSolvable ↥S := hs
    exact Group.isSolvable_of_surjective
      (f := (MulEquiv.subgroupMap φ S).toMonoidHom) (MulEquiv.subgroupMap φ S).surjective

private lemma ggK1Df_toLinEquiv_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) : toLinEquiv ι K x = ggK1DLin x := by
  ext v
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, ggK1Df_lin_apply]

private lemma ggK1Df_iSup_subgroupOf {G : Type*} [Group G] {κ : Type*} {H : Subgroup G}
    (S : κ → Subgroup G) (hS : ∀ q, S q ≤ H) :
    ⨆ q, (S q).subgroupOf H = (⨆ q, S q).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_iSup, Subgroup.map_subgroupOf_eq_of_le (iSup_le hS)]
  apply le_antisymm
  · apply iSup_le; intro q
    rw [Subgroup.map_subgroupOf_eq_of_le (hS q)]
    exact le_iSup (fun q => S q) q
  · apply iSup_le; intro q
    rw [← Subgroup.map_subgroupOf_eq_of_le (hS q)]
    exact le_iSup (fun q => ((S q).subgroupOf H).map H.subtype) q

private lemma ggK1Df_subgroupOf_centralizer {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {Qf : QuadraticForm K (ι → K)}
    {D : Subgroup ((ι → K) ≃ₗ[K] (ι → K))}
    (hDle : D ≤ TauCeti.QuadraticMap.orthogonalGroup Qf)
    {xL : (ι → K) ≃ₗ[K] (ι → K)} (hxD : xL ∈ D) :
    (isometryCentralizer Qf xL ⊓ D).subgroupOf D =
      Subgroup.centralizer ({⟨xL, hxD⟩} : Set ↥D) := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    CFSG.RankThree.PartOne.KCOrthogonal.mem_isometryCentralizer,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨_, hcomm⟩, _⟩
    exact Subtype.ext (LinearEquiv.ext (fun v => hcomm v))
  · intro hcomm
    refine ⟨⟨?_, ?_⟩, g.2⟩
    · intro v
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hDle g.2) v
    · intro v
      have h := congrArg (fun e : ↥D => ((e : (ι → K) ≃ₗ[K] (ι → K)) v)) hcomm
      simpa using h

private lemma ggK1Df_iSupIndep_subgroupOf {G : Type*} [Group G] {κ : Type*} {H : Subgroup G}
    (S : κ → Subgroup G) (hS : ∀ q, S q ≤ H) (hind : iSupIndep S) :
    iSupIndep (fun q => (S q).subgroupOf H) := by
  intro i
  rw [disjoint_iff]
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_bot, Subgroup.map_inf _ _ H.subtype H.subtype_injective]
  have h1 : ((S i).subgroupOf H).map H.subtype = S i := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hS i)]
  have h2 : ∀ j, (⨆ (_ : j ≠ i), (S j).subgroupOf H).map H.subtype =
      ⨆ (_ : j ≠ i), S j := by
    intro j
    rw [Subgroup.map_iSup]
    exact iSup_congr (fun _ => by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hS j)])
  rw [Subgroup.map_iSup, h1]
  simp only [h2]
  have := hind i
  rwa [disjoint_iff] at this

private lemma ggK1Df_commutator_subgroupOf {G : Type*} [Group G] {H S : Subgroup G}
    (hS : S ≤ H) :
    ⁅S.subgroupOf H, S.subgroupOf H⁆ = (⁅S, S⁆).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hS,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hS hS)]

private theorem ggK1Df_transport {p nf : ℕ} {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} (hQ : Q = ⇑Qf)
    (hscal : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥)
    {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K))) :
    ∃ A : (Σ i : P.ι, Fin (P.blk i).length) → Subgroup (LargeEvenProj (LargeEvenOmega Q)),
      (∀ q q', q ≠ q' → ∀ a ∈ A q, ∀ b ∈ A q', Commute a b) ∧
      (⨆ q, A q) = Subgroup.centralizer
        ({LargeEvenProjMk (LargeEvenOmega Q) x} : Set (LargeEvenProj (LargeEvenOmega Q))) ∧
      iSupIndep A ∧
      (∀ q, CFSG.IsQuasisimple ↥⁅A q, A q⁆ ∨ Group.IsSolvable ↥(A q)) ∧
      (∀ q, Nonempty (↥(A q) ≃* ↥(P.sub q.1 q.2))) := by
  classical
  let D : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) :=
    ⁅TauCeti.QuadraticMap.orthogonalGroup Qf, TauCeti.QuadraticMap.orthogonalGroup Qf⁆
  let φ : ↥D ≃* LargeEvenProj (LargeEvenOmega Q) := ggK1Df_derivedEquiv hQ hscal
  have hDle : D ≤ TauCeti.QuadraticMap.orthogonalGroup Qf :=
    Subgroup.commutator_le_self _
  have hxD : ggK1DLin (x : GL ι K) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Qf, TauCeti.QuadraticMap.orthogonalGroup Qf⁆ := by
    have hxmem : (x : GL ι K) ∈ CFSG.Open.StatedOmega Q := x.2
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ.symm] at hxmem
    rw [Subgroup.mem_comap] at hxmem
    change (toLinEquiv ι K (x : GL ι K)) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Qf, TauCeti.QuadraticMap.orthogonalGroup Qf⁆
      at hxmem
    rw [ggK1Df_toLinEquiv_eq] at hxmem
    exact hxmem
  have hxφ : φ ⟨ggK1DLin (x : GL ι K), hxD⟩ = LargeEvenProjMk (LargeEvenOmega Q) x := by
    show ggK1Df_derivedEquiv hQ hscal ⟨ggK1DLin (x : GL ι K), hxD⟩ = _
    rw [ggK1Df_derivedEquiv]
    simp only [MulEquiv.trans_apply, MulEquiv.coe_subgroupMap_apply,
      MulEquiv.subgroupCongr_apply, TableBOrth.projMkEquiv_apply]
    congr 1
    exact Subtype.ext (by
      show (toLinEquiv ι K).symm (ggK1DLin (x : GL ι K)) = (x : GL ι K)
      rw [← ggK1Df_toLinEquiv_eq, MulEquiv.symm_apply_apply])
  have hsubD : ∀ q : Σ i, Fin (P.blk i).length, P.sub q.1 q.2 ≤ D := by
    intro q
    have hle : (⨆ q : Σ i, Fin (P.blk i).length, P.sub q.1 q.2) ≤ D := by
      rw [P.hjoin]
      exact inf_le_right
    exact (le_iSup (fun q : Σ i, Fin (P.blk i).length => P.sub q.1 q.2) q).trans hle
  let S : (Σ i, Fin (P.blk i).length) → Subgroup ↥D :=
    fun q => (P.sub q.1 q.2).subgroupOf D
  have hcommS : ∀ q q', q ≠ q' → ∀ a ∈ S q, ∀ b ∈ S q', Commute a b := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hne a ha b hb
    have ha' : (a : (ι → K) ≃ₗ[K] (ι → K)) ∈ P.sub i j := by
      simpa only [S, Subgroup.mem_subgroupOf] using ha
    have hb' : (b : (ι → K) ≃ₗ[K] (ι → K)) ∈ P.sub i' j' := by
      simpa only [S, Subgroup.mem_subgroupOf] using hb
    have hab : Commute (a : (ι → K) ≃ₗ[K] (ι → K))
        (b : (ι → K) ≃ₗ[K] (ι → K)) := by
      by_cases hi : i = i'
      · subst hi
        exact P.hcomm_sub i j j' (fun h => hne (by simp [h])) (a : _) ha' (b : _) hb'
      · exact P.hcomm i i' hi (a : _) (P.hsub_le i j ha') (b : _) (P.hsub_le i' j' hb')
    rw [commute_iff_eq]
    exact Subtype.ext (by rw [commute_iff_eq] at hab; exact hab)
  have hindepS : iSupIndep S :=
    ggK1Df_iSupIndep_subgroupOf (fun q : Σ i, Fin (P.blk i).length => P.sub q.1 q.2) hsubD
      P.hindep
  have htameS : ∀ q, CFSG.IsQuasisimple ↥⁅S q, S q⁆ ∨ Group.IsSolvable ↥(S q) := by
    intro q
    rcases P.htame q with hq | hs
    · left
      have hiso : ↥⁅S q, S q⁆ ≃* ↥⁅P.sub q.1 q.2, P.sub q.1 q.2⁆ := by
        change ↥⁅(P.sub q.1 q.2).subgroupOf D, (P.sub q.1 q.2).subgroupOf D⁆ ≃* _
        rw [ggK1Df_commutator_subgroupOf (hsubD q)]
        exact Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_of_le (hsubD q) (hsubD q))
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv hiso.symm hq
    · right
      haveI : Group.IsSolvable ↥(P.sub q.1 q.2) := hs
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe (hsubD q)).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (hsubD q)).symm.surjective
  refine ⟨fun q => (S q).map φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact ggK1Df_map_commute φ hcommS
  · rw [ggK1Df_map_iSup]
    have hjoinS : (⨆ q, S q) =
        (isometryCentralizer Qf (ggK1DLin (x : GL ι K)) ⊓ D).subgroupOf D := by
      dsimp only [S]
      rw [ggK1Df_iSup_subgroupOf (fun q : Σ i, Fin (P.blk i).length => P.sub q.1 q.2) hsubD,
        P.hjoin]
    rw [hjoinS, ggK1Df_subgroupOf_centralizer hDle hxD,
      ggK1Df_map_centralizer φ ⟨ggK1DLin (x : GL ι K), hxD⟩, hxφ]
  · apply ggK1Df_map_iSupIndep
    exact hindepS
  · intro q
    exact ggK1Df_map_tame φ (S := S q) (htameS q)
  · intro q
    exact ⟨(MulEquiv.subgroupMap φ (S q)).symm.trans
      (Subgroup.subgroupOfEquivOfLe (hsubD q))⟩

private lemma ggK1Df_tail_plumbing {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (y : Module.End K V) (m : List ℕ) (tailSet : Finset K[X])
    (kfun : K[X] → ggK1DCo_Kind) (f : ℕ → ggK1DCo_Kind)
    (hmult : Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
      tailSet.val.map (primaryMultiplicity y))
    (hk : ∀ t : ↥tailSet, kfun t.1 = f (primaryMultiplicity y t.1)) :
    (Finset.univ : Finset ↥tailSet).val.map (fun t => kfun t.1) =
      (m.tail.filter (fun j => decide (j ≠ 0))).map f := by
  rw [ggK1CBl_univ_map_subtype_val tailSet kfun]
  trans tailSet.val.map (f ∘ primaryMultiplicity y)
  · exact Multiset.map_congr rfl
      (fun t ht => by simpa [Function.comp_apply] using hk ⟨t, Finset.mem_val.mp ht⟩)
  · rw [← Multiset.map_map, ← hmult, Multiset.map_coe]

private theorem ggK1Df_dvd_cyclotomic {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {c : K[X]}
    (hc : Irreducible c) (hcm : c.Monic) (hcd : c ∣ X ^ p - 1) (hc1 : c ≠ X - 1) :
    c ∣ cyclotomic p K := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← cyclotomic_prime_mul_X_sub_one K p] at hcd
  rcases hc.prime.dvd_or_dvd hcd with h1 | h1
  · exact h1
  · exfalso
    have heq : c = X - 1 :=
      (eq_of_monic_of_associated hcm (monic_X_sub_C 1)
        (hc.associated_of_dvd (irreducible_X_sub_C 1) h1)).trans (by rw [C_1])
    exact hc1 heq

private theorem ggK1Df_ordQ_eq_one {K : Type} [Field K] [Finite K] {p nf : ℕ} (hp : p.Prime)
    (h1 : p ∣ 2 ^ nf - 1) (hK : Nat.card K = 2 ^ nf) : OrdPNS.ordQ K p = 1 := by
  have hle : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
  have hcast : ((Nat.card K : ℕ) : ZMod p) = 1 := by
    rw [hK]
    have hz : ((2 ^ nf - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h1
    rw [Nat.cast_sub hle, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz
  rw [OrdPNS.ordQ_def, hcast, orderOf_one]

private theorem ggK1Df_natDegree_eq_one {K : Type} [Field K] [Finite K] {p nf : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) (h1 : p ∣ 2 ^ nf - 1) (hK : Nat.card K = 2 ^ nf) {h : K[X]}
    (hirr : Irreducible h) (hgd : h ∣ cyclotomic p K) : h.natDegree = 1 := by
  rw [OrdPNS.natDegree_eq_ordQ hp hpK hirr hgd, ggK1Df_ordQ_eq_one hp h1 hK]

private theorem ggK1Df_not_selfDual_of_degree_one {K : Type} [Field K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {h : K[X]} [Fact (Irreducible h)] (hmon : h.Monic) (hdeg : h.natDegree = 1)
    (hord : orderOf (AdjoinRoot.root h) = p) : reciprocalPolynomial h ≠ h := by
  intro hself
  set rho := AdjoinRoot.root h with hrho
  have hrhop : rho ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one rho
  have hrho0 : rho ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hrhop
    exact zero_ne_one hrhop
  have hrhoinv : rho ^ (p - 1) = rho⁻¹ := by
    have hmul : rho ^ (p - 1) * rho = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hrhop]
    exact eq_inv_of_mul_eq_one_left hmul
  have hrhoroot : aeval rho h = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hstar : aeval rho⁻¹ (reciprocalPolynomial h) = 0 := by
    have hrhoinv0 : rho⁻¹ ≠ 0 := inv_ne_zero hrho0
    have := CFSG.RankThree.PartOne.KCOrthogonal.aeval_reciprocalPolynomial_of_unit
      (Units.mk0 (rho⁻¹) hrhoinv0) h
    rw [Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv] at this
    rw [this, hrhoroot, mul_zero, smul_zero]
  have hrhoinvh : aeval rho⁻¹ h = 0 := by
    have := hstar
    rwa [hself] at this
  have hc1 : h.coeff 1 = 1 := by
    have hlead : h.coeff h.natDegree = 1 := hmon.leadingCoeff
    rwa [hdeg] at hlead
  have hXc : h = X + C (h.coeff 0) := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)]
    rw [hc1, C_1, one_mul]
  have hdecomp : aeval rho h = rho + algebraMap K (AdjoinRoot h) (h.coeff 0) := by
    calc aeval rho h = aeval rho (X + C (h.coeff 0)) :=
          congrArg (fun p : K[X] => aeval rho p) hXc
      _ = rho + algebraMap K (AdjoinRoot h) (h.coeff 0) := by simp
  have hdecomp' : aeval rho⁻¹ h = rho⁻¹ + algebraMap K (AdjoinRoot h) (h.coeff 0) := by
    calc aeval rho⁻¹ h = aeval rho⁻¹ (X + C (h.coeff 0)) :=
          congrArg (fun p : K[X] => aeval rho⁻¹ p) hXc
      _ = rho⁻¹ + algebraMap K (AdjoinRoot h) (h.coeff 0) := by simp
  have hval : rho = - algebraMap K (AdjoinRoot h) (h.coeff 0) := by
    have h1 : rho + algebraMap K (AdjoinRoot h) (h.coeff 0) = 0 := by
      rw [← hdecomp]; exact hrhoroot
    exact eq_neg_of_add_eq_zero_left h1
  have hvalinv : rho⁻¹ = - algebraMap K (AdjoinRoot h) (h.coeff 0) := by
    have h1 : rho⁻¹ + algebraMap K (AdjoinRoot h) (h.coeff 0) = 0 := by
      rw [← hdecomp']; exact hrhoinvh
    exact eq_neg_of_add_eq_zero_left h1
  have hrhoeq : rho = rho⁻¹ := hval.trans hvalinv.symm
  have hsq : rho ^ 2 = 1 := by
    have hmul : rho * rho⁻¹ = 1 := mul_inv_cancel₀ hrho0
    rw [← hrhoeq] at hmul
    simpa [sq] using hmul
  have hpdvd : p ∣ 2 := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hsq
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd)

private lemma ggK1Df_iSupIndep_elim {κ κ' : Type*} {R : Type*} [Group R]
    (AP : κ → Subgroup R) (Φ : κ' → Option κ)
    (hinj : ∀ q q' a, Φ q = some a → Φ q' = some a → q = q')
    (hind : iSupIndep AP) :
    iSupIndep (fun q => (Φ q).elim ⊥ AP) := by
  intro i
  change Disjoint ((Φ i).elim ⊥ AP) (⨆ j, ⨆ (_ : j ≠ i), (Φ j).elim ⊥ AP)
  cases hi : Φ i with
  | none =>
    simp only [Option.elim_none]
    exact disjoint_bot_left
  | some a =>
    simp only [Option.elim_some]
    refine Disjoint.mono_right ?_ (hind a)
    refine iSup_le (fun j => ?_)
    refine iSup_le (fun hj => ?_)
    by_cases hjn : Φ j = none
    · rw [hjn]; simp only [Option.elim_none]; exact bot_le
    · obtain ⟨a', ha'⟩ := Option.ne_none_iff_exists'.mp hjn
      rw [ha']
      simp only [Option.elim_some]
      refine le_iSup_of_le a' (le_iSup_of_le (fun h => hj ?_) le_rfl)
      exact hinj j i a' ha' (hi.trans (congrArg some h).symm)

private lemma ggK1Df_iSup_elim {κ κ' : Type*} {R : Type*} [Group R]
    (AP : κ → Subgroup R) (Φ : κ' → Option κ)
    (hcover : ∀ a, ∃ q, Φ q = some a) :
    ⨆ q, (Φ q).elim ⊥ AP = ⨆ a, AP a := by
  apply le_antisymm
  · apply iSup_le; intro q
    cases hq : Φ q with
    | none => simp only [Option.elim_none]; exact bot_le
    | some a => simp only [Option.elim_some]; exact le_iSup AP a
  · apply iSup_le; intro a
    obtain ⟨q, hq⟩ := hcover a
    rw [show AP a = (Φ q).elim ⊥ AP from by rw [hq]; simp only [Option.elim_some]]
    exact le_iSup (fun q => (Φ q).elim ⊥ AP) q

private lemma ggK1Df_commute_elim {κ κ' : Type*} {R : Type*} [Group R]
    (AP : κ → Subgroup R) (Φ : κ' → Option κ)
    (hinj : ∀ q q' a, Φ q = some a → Φ q' = some a → q = q')
    (hcomm : ∀ a a', a ≠ a' → ∀ x ∈ AP a, ∀ y ∈ AP a', Commute x y) :
    ∀ q q', q ≠ q' → ∀ x ∈ (Φ q).elim ⊥ AP, ∀ y ∈ (Φ q').elim ⊥ AP, Commute x y := by
  intro q q' hne x hx y hy
  cases hq : Φ q with
  | none =>
    rw [hq] at hx
    change x ∈ (⊥ : Subgroup R) at hx
    rw [Subgroup.mem_bot] at hx
    subst hx
    exact Commute.one_left y
  | some a =>
    rw [hq] at hx
    change x ∈ AP a at hx
    cases hq' : Φ q' with
    | none =>
      rw [hq'] at hy
      change y ∈ (⊥ : Subgroup R) at hy
      rw [Subgroup.mem_bot] at hy
      subst hy
      exact Commute.one_right x
    | some a' =>
      rw [hq'] at hy
      change y ∈ AP a' at hy
      exact hcomm a a' (fun h => hne (hinj q q' a hq (hq'.trans (congrArg some h.symm)))) x hx y hy

private lemma ggK1Df_tame_elim {κ κ' : Type*} {R : Type*} [Group R]
    (AP : κ → Subgroup R) (Φ : κ' → Option κ)
    (htame : ∀ a, CFSG.IsQuasisimple ↥⁅AP a, AP a⁆ ∨ Group.IsSolvable ↥(AP a)) :
    ∀ q, CFSG.IsQuasisimple ↥⁅(Φ q).elim ⊥ AP, (Φ q).elim ⊥ AP⁆ ∨
      Group.IsSolvable ↥((Φ q).elim ⊥ AP) := by
  intro q
  cases hq : Φ q with
  | none =>
    right
    change Group.IsSolvable ↥(⊥ : Subgroup R)
    infer_instance
  | some a =>
    exact htame a

private lemma ggK1Df_kindOrbits_sl {nf m : ℕ} (hm : 2 ≤ m) :
    ggK1DCo_kindOrbits nf (ggK1DCo_Kind.sl m) = [ggMultBlockA (m - 1) nf 1] := by
  rcases m with _ | _ | k
  · omega
  · omega
  · simp [ggK1DCo_kindOrbits, ggMultBlockA]

private lemma ggK1Df_kindOrbits_su {nf m : ℕ} (hm : 2 ≤ m) :
    ggK1DCo_kindOrbits nf (ggK1DCo_Kind.su m) = [ggMultBlockA (m - 1) nf 2] := by
  rcases m with _ | _ | k
  · omega
  · omega
  · simp [ggK1DCo_kindOrbits, ggMultBlockA]

private lemma ggK1Df_kindOrbits_su_length {nf m : ℕ} :
    (ggK1DCo_kindOrbits nf (ggK1DCo_Kind.su m)).length = 1 := by
  rcases m with _ | _ | k <;> simp [ggK1DCo_kindOrbits]

private lemma ggK1Df_ccKindOrbit_sl {nf m : ℕ} (hm : 2 ≤ m) :
    ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sl m) = ggMultBlockA (m - 1) nf 1 := by
  rcases m with _ | _ | k
  · omega
  · omega
  · rfl

private lemma ggK1Df_ccKindOrbit_su {nf m : ℕ} (hm : 2 ≤ m) :
    ggK1CCo_kindOrbit nf (ggK1CCo_Kind.su m) = ggMultBlockA (m - 1) nf 2 := by
  rcases m with _ | _ | k
  · omega
  · omega
  · rfl

private lemma ggK1Df_sl_orbitModel {nf : ℕ} {K : Type} [Field K] (hnf : 1 ≤ nf)
    {m : ℕ} (hm : 2 ≤ m) {H : Type} [Group H] :
    ggK1CBl_Model nf K (ggK1CCo_Kind.sl m) H ↔
      ggK1DCo_OrbitModel nf K (ggMultBlockA (m - 1) nf 1) H := by
  have hba : ggMultBlockA (m - 1) nf 1 =
      (⟨⟨.A, m - 1, nf⟩, decide (¬ (m - 1 = 1 ∧ nf = 1))⟩ : GGKacOrbit) := by
    simp [ggMultBlockA]
  have hcond : ¬ (m - 1 = 1 ∧ nf = 2 * nf) := by
    rintro ⟨-, h⟩; omega
  rw [hba]
  simp only [ggK1CBl_Model, ggK1DCo_OrbitModel]
  rw [if_neg hcond, show m - 1 + 1 = m from by omega]

private lemma ggK1Df_su_orbitModel {nf : ℕ} {K : Type} [Field K] (hnf : 1 ≤ nf)
    {m : ℕ} (hm : 3 ≤ m) {H : Type} [Group H] :
    ggK1CBl_Model nf K (ggK1CCo_Kind.su m) H ↔
      ggK1DCo_OrbitModel nf K (ggMultBlockA (m - 1) nf 2) H := by
  have hba : ggMultBlockA (m - 1) nf 2 =
      (⟨⟨.twA, m - 1, nf⟩, decide (¬ (m - 1 = 2 ∧ nf = 1))⟩ : GGKacOrbit) := by
    simp only [ggMultBlockA, if_neg (by omega : ¬ (2 : ℕ) = 1)]
    rw [if_pos (by omega : 2 ≤ m - 1)]
  rw [hba]
  simp only [ggK1CBl_Model, ggK1DCo_OrbitModel]
  rw [show m - 1 + 1 = m from by omega]

private lemma ggK1Df_iSup_subsingleton {α ι : Type*} [CompleteLattice α] [Subsingleton ι]
    (f : ι → α) (i : ι) : (⨆ j, f j) = f i :=
  le_antisymm (iSup_le (fun j => by rw [Subsingleton.elim j i])) (le_iSup f i)

private noncomputable def ggK1Df_glRingEquiv {m : ℕ} {E K : Type} [Field E] [Field K]
    (e : E ≃+* K) : Matrix.GeneralLinearGroup (Fin m) E ≃*
      Matrix.GeneralLinearGroup (Fin m) K :=
  MulEquiv.ofBijective (Matrix.GeneralLinearGroup.map e.toRingHom)
    ⟨Matrix.GeneralLinearGroup.map_injective e.injective, by
      intro y
      refine ⟨Matrix.GeneralLinearGroup.map e.symm.toRingHom y, ?_⟩
      have hcomp : e.toRingHom.comp e.symm.toRingHom = RingHom.id K :=
        RingHom.ext (fun x => by simp)
      calc Matrix.GeneralLinearGroup.map e.toRingHom
            (Matrix.GeneralLinearGroup.map e.symm.toRingHom y)
          = Matrix.GeneralLinearGroup.map (e.toRingHom.comp e.symm.toRingHom) y := by
            rw [Matrix.GeneralLinearGroup.map_comp]; rfl
        _ = Matrix.GeneralLinearGroup.map (RingHom.id K) y := by rw [hcomp]
        _ = y := by rw [Matrix.GeneralLinearGroup.map_id]; rfl⟩

private theorem ggK1Df_sl_dict {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (h1 : p ∣ 2 ^ nf - 1)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (hxO : OddOrderIsometry Qf p (ggK1DLin (x : GL ι K)))
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (m : ℕ) (hkind : P.kind i = .sl m) (hm2 : 2 ≤ m)
    (j : Fin (P.blk i).length) :
    (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ ↔ ((P.blk i).get j).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ →
        ggK1DCo_OrbitModel nf K ((P.blk i).get j) ↥⁅P.sub i j, P.sub i j⁆) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hblk : P.blk i = [ggMultBlockA (m - 1) nf 1] := by
    rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_sl hm2]
  obtain ⟨E, hEfield, hEfin, h, hh, hne, hcard, _hmult, ⟨he⟩⟩ := P.paired_model i m hkind
  letI : Field E := hEfield
  letI : Fintype E := hEfin
  have hpf : h ∈ primaryFactors (ggK1DLin (x : GL ι K)).toLinearMap := hh
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hpf
  have hmon : h.Monic := monic_of_mem_primaryFactors hpf
  have hne1 : h ≠ X - 1 := by
    rintro rfl
    exact hne (by rw [CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one])
  have hdvd1 : h ∣ X ^ p - 1 := hxO.dvd_X_pow_sub_one hpf
  have hdvd2 : h ∣ cyclotomic p K := ggK1Df_dvd_cyclotomic hp hirr hmon hdvd1 hne1
  have hdeg : h.natDegree = 1 :=
    ggK1Df_natDegree_eq_one hp (ggK1Df_cast_ne_zero hp hp2 hK) h1 hK hirr hdvd2
  have hEcard : Fintype.card E = Fintype.card K := by
    rw [hcard, hdeg, pow_one, Fintype.card_eq_nat_card]
  have eEK : E ≃+* K := FiniteField.ringEquivOfCardEq hEcard
  have hAi : P.A i ≃* Matrix.GeneralLinearGroup (Fin m) K :=
    he.trans (ggK1Df_glRingEquiv (m := m) eEK)
  have hclass := ggK1CBl_classical_sl (K := K) hK hnf (by omega : 1 ≤ m) hAi
  have hsub : P.sub i j = P.A i := by
    have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
    haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
    rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
  have hget : (P.blk i).get j = ggMultBlockA (m - 1) nf 1 := by
    rw [List.get_of_eq hblk]
    simp
  rw [hsub, hget]
  refine ⟨?_, ?_⟩
  · rw [hclass.2.1, ggK1Df_ccKindOrbit_sl hm2]
  · intro hq
    rw [← ggK1Df_sl_orbitModel hnf hm2]
    exact hclass.2.2 hq

private theorem ggK1Df_su_dict {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (m : ℕ) (hkind : P.kind i = .su m) (hm3 : 3 ≤ m)
    (j : Fin (P.blk i).length) :
    (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ ↔ ((P.blk i).get j).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ →
        ggK1DCo_OrbitModel nf K ((P.blk i).get j) ↥⁅P.sub i j, P.sub i j⁆) := by
  have hblk : P.blk i = [ggMultBlockA (m - 1) nf 2] := by
    rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_su (by omega)]
  obtain ⟨E, hEfield, hEfin, hE, W, hWadd, hWmod, hWfin, Hf, hsym, hsep, hdim, ⟨he⟩⟩ :=
    P.selfDual_model i m hkind
  letI : Field E := hEfield
  letI : Fintype E := hEfin
  letI : AddCommGroup W := hWadd
  letI : Module E W := hWmod
  letI : FiniteDimensional E W := hWfin
  obtain ⟨b, hb⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.exists_orthonormal_basis
    hE hsym hsep
  let b' : Module.Basis (Fin m) E W := b.reindex (finCongr hdim)
  have hb' : ∀ i j, Hf (b' i) (b' j) = if i = j then 1 else 0 := by
    intro i j
    dsimp only [b']
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    simp
  have hclass := ggK1CBl_classical_su (K := K) hK hnf (by omega : 1 ≤ m) hE hsym hsep b' hb' he
  have hsub : P.sub i j = P.A i := by
    have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
    haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
    rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
  have hget : (P.blk i).get j = ggMultBlockA (m - 1) nf 2 := by
    rw [List.get_of_eq hblk]
    simp
  rw [hsub, hget]
  refine ⟨?_, ?_⟩
  · rw [hclass.2.1, ggK1Df_ccKindOrbit_su (by omega)]
  · intro hq
    rw [← ggK1Df_su_orbitModel hnf hm3]
    exact hclass.2.2 hq

private lemma ggK1Df_kindOrbits_om {nf m : ℕ} (hm : 2 ≤ m) (eps : Bool) :
    ggK1DCo_kindOrbits nf (ggK1DCo_Kind.om eps m) = ggMultV0 m eps nf := by
  simp only [ggK1DCo_kindOrbits, if_neg (by omega : ¬ m ≤ 1)]

private lemma ggK1Df_ggMultV0_large {m nf : ℕ} (hm : 4 ≤ m) (eps : Bool) :
    ggMultV0 m eps nf = if eps then [(⟨⟨.D, m, nf⟩, true⟩ : GGKacOrbit)]
      else [⟨⟨.twD, m, nf⟩, true⟩] := by
  simp only [ggMultV0, if_neg (by omega : ¬ m ≤ 1), if_neg (by omega : ¬ m = 2),
    if_neg (by omega : ¬ m = 3)]

private lemma ggK1Df_ggMultV0_three {nf : ℕ} (eps : Bool) :
    ggMultV0 3 eps nf = if eps then [(⟨⟨.A, 3, nf⟩, true⟩ : GGKacOrbit)]
      else [⟨⟨.twA, 3, nf⟩, true⟩] := by
  cases eps <;> simp [ggMultV0]

private lemma ggK1Df_ggMultV0_two {nf : ℕ} (eps : Bool) :
    ggMultV0 2 eps nf = if eps then
        [(⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit),
          ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩]
      else [(⟨⟨.A, 1, 2 * nf⟩, true⟩ : GGKacOrbit)] := by
  cases eps <;> simp [ggMultV0]

private lemma ggK1Df_commutator_eq_of_isQuasisimple {G : Type*} [Group G] {S : Subgroup G}
    (h : CFSG.IsQuasisimple ↥S) : (⁅S, S⁆ : Subgroup G) = S :=
  Subgroup.isPerfect_iff.mp h.1

private lemma ggK1Df_isQuasisimple_commutator {G : Type*} [Group G] {S : Subgroup G}
    (h : CFSG.IsQuasisimple ↥S) : CFSG.IsQuasisimple ↥⁅S, S⁆ :=
  (ggK1Df_commutator_eq_of_isQuasisimple h).symm ▸ h

private lemma ggK1Df_solvable_not_quasi {G : Type*} [Group G] {S : Subgroup G}
    (h : Group.IsSolvable ↥S) : ¬ CFSG.IsQuasisimple ↥⁅S, S⁆ := by
  haveI := h
  intro hq
  have hle : ⁅S, S⁆ ≤ S := Subgroup.commutator_le_self S
  haveI : Group.IsSolvable ↥⁅S, S⁆ :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  haveI : Group.IsPerfect ↥⁅S, S⁆ := hq.1
  haveI : Nontrivial ↥⁅S, S⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact Group.IsPerfect.not_isSolvable ↥⁅S, S⁆ inferInstance

private lemma ggK1Df_not_quasi_bot {G : Type*} [Group G] :
    ¬ CFSG.IsQuasisimple ↥(⊥ : Subgroup G) := by
  intro hq
  obtain ⟨a, b, hab⟩ := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact hab (Subsingleton.elim a b)

private theorem ggK1Df_quasi_dict {nf : ℕ} {K : Type} [Field K] {G : Type} [Group G]
    {S : Subgroup G} {o : GGKacOrbit}
    (hqs : o.qs = true) (hq : CFSG.IsQuasisimple ↥S)
    (hm : ggK1DCo_OrbitModel nf K o ↥S) :
    (CFSG.IsQuasisimple ↥⁅S, S⁆ ↔ o.qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅S, S⁆ → ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆) := by
  have heq := ggK1Df_commutator_eq_of_isQuasisimple hq
  refine ⟨?_, ?_⟩
  · rw [heq]; exact ⟨fun _ => hqs, fun _ => hq⟩
  · intro _; rw [heq]; exact hm

private theorem ggK1Df_om_large_dict {p nf : ℕ} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (eps : Bool) (m : ℕ) (hkind : P.kind i = .om eps m) (hm4 : 4 ≤ m)
    (j : Fin (P.blk i).length) :
    (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ ↔ ((P.blk i).get j).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ →
        ggK1DCo_OrbitModel nf K ((P.blk i).get j) ↥⁅P.sub i j, P.sub i j⁆) := by
  cases eps
  · have hblk : P.blk i = [(⟨⟨.twD, m, nf⟩, true⟩ : GGKacOrbit)] := by
      rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega), ggK1Df_ggMultV0_large hm4]
      simp
    have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
    have hsub : P.sub i j = P.A i := by
      haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
      rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
    have hget : (P.blk i).get j = (⟨⟨.twD, m, nf⟩, true⟩ : GGKacOrbit) := by
      have hj : (j : ℕ) = 0 := by omega
      rw [List.get_of_eq hblk]
      simp [hj]
    rcases P.fixed_model i false m hkind with ⟨-, -, hmodel, -, -, -⟩
    obtain ⟨b, c, hirr, ⟨he⟩⟩ := by simpa using hmodel (by omega)
    have hqΩ := CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadMinus
      (n := m) (K := K) (by omega) hirr
    have hqA : CFSG.IsQuasisimple ↥(P.A i) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv he.symm hqΩ
    rw [hsub, hget]
    exact ggK1Df_quasi_dict (o := ⟨⟨.twD, m, nf⟩, true⟩) rfl hqA ⟨b, c, hirr, ⟨he⟩⟩
  · have hblk : P.blk i = [(⟨⟨.D, m, nf⟩, true⟩ : GGKacOrbit)] := by
      rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega), ggK1Df_ggMultV0_large hm4]
      simp
    have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
    have hsub : P.sub i j = P.A i := by
      haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
      rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
    have hget : (P.blk i).get j = (⟨⟨.D, m, nf⟩, true⟩ : GGKacOrbit) := by
      have hj : (j : ℕ) = 0 := by omega
      rw [List.get_of_eq hblk]
      simp [hj]
    rcases P.fixed_model i true m hkind with ⟨-, -, hmodel, -, -, -⟩
    obtain ⟨he⟩ := by simpa using hmodel (by omega)
    have hqΩ := CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus
      (n := m) (K := K) (by omega)
    have hqA : CFSG.IsQuasisimple ↥(P.A i) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv he.symm hqΩ
    rw [hsub, hget]
    exact ggK1Df_quasi_dict (o := ⟨⟨.D, m, nf⟩, true⟩) rfl hqA ⟨he⟩

private theorem ggK1Df_om_two_dict_plus {p nf : ℕ} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (hK : Nat.card K = 2 ^ nf) (hnf : 1 ≤ nf)
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (hkind : P.kind i = .om true 2)
    (j : Fin (P.blk i).length) :
    (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ ↔ ((P.blk i).get j).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ →
        ggK1DCo_OrbitModel nf K ((P.blk i).get j) ↥⁅P.sub i j, P.sub i j⁆) := by
  have hblk : P.blk i = [(⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit),
      ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩] := by
    rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega) true, ggK1Df_ggMultV0_two]
    simp
  obtain ⟨he⟩ := (P.fixed_model i true 2 hkind).2.2.2.1 rfl rfl j
  have hget : (P.blk i).get j = (⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit) := by
    have hmem : (P.blk i).get j ∈
        [(⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit),
         (⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit)] := by
      rw [← hblk]
      exact List.get_mem _ _
    simpa using hmem
  have hm : ggK1DCo_OrbitModel nf K
      (⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit) ↥(P.sub i j) := by
    simp only [ggK1DCo_OrbitModel]
    rw [if_neg (by omega : ¬ (True ∧ nf = 2 * nf))]
    exact ⟨he⟩
  rw [hget]
  by_cases hnf1 : nf = 1
  · subst hnf1
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hsolvSL : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
      haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
          (Or.inl hK2)
      exact Group.isSolvable_of_isSolvable_injective
        (f := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective
    haveI : Group.IsSolvable ↥(P.sub i j) :=
      Group.isSolvable_of_surjective (f := he.symm.toMonoidHom) he.symm.surjective
    have hnotq : ¬ CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ :=
      ggK1Df_solvable_not_quasi (S := P.sub i j) inferInstance
    have hqs : (decide (¬ (1 = 1)) : Bool) = false := rfl
    refine ⟨?_, ?_⟩
    · rw [hqs]
      exact ⟨fun h => absurd h hnotq, fun h => (Bool.false_eq_true.mp h).elim⟩
    · intro h; exact absurd h hnotq
  · have hnf2 : 2 ≤ nf := by omega
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ nf := Nat.pow_le_pow_right (by norm_num) hnf2
    have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) :=
      CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (m := 2) le_rfl h4
    have hq : CFSG.IsQuasisimple ↥(P.sub i j) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv he.symm hqSL
    have hqs : (⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit).qs = true := by
      simp [hnf1]
    exact ggK1Df_quasi_dict (o := (⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit)) hqs hq hm

private theorem ggK1Df_om_two_dict_minus {p nf : ℕ} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (hK : Nat.card K = 2 ^ nf) (hnf : 1 ≤ nf)
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (hkind : P.kind i = .om false 2)
    (j : Fin (P.blk i).length) :
    (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ ↔ ((P.blk i).get j).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ →
        ggK1DCo_OrbitModel nf K ((P.blk i).get j) ↥⁅P.sub i j, P.sub i j⁆) := by
  have hblk : P.blk i = [(⟨⟨.A, 1, 2 * nf⟩, true⟩ : GGKacOrbit)] := by
    rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega) false, ggK1Df_ggMultV0_two]
    simp
  have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
  have hsub : P.sub i j = P.A i := by
    haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
    rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
  have hget : (P.blk i).get j = (⟨⟨.A, 1, 2 * nf⟩, true⟩ : GGKacOrbit) := by
    have hj : (j : ℕ) = 0 := by omega
    rw [List.get_of_eq hblk]
    simp [hj]
  obtain ⟨E, hEfield, hEfin, hEcard, ⟨he⟩⟩ :=
    (P.fixed_model i false 2 hkind).2.2.2.2.1 rfl rfl
  letI : Field E := hEfield
  letI : Fintype E := hEfin
  have h2K : 2 ≤ Nat.card K := by
    rw [hK]
    simpa using Nat.pow_le_pow_right (show (0 : ℕ) < 2 by norm_num) hnf
  have hE4 : 4 ≤ Nat.card E := by
    rw [Nat.card_eq_fintype_card, hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (Nat.card K) ^ 2 := Nat.pow_le_pow_left h2K 2
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) E) :=
    CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (m := 2) le_rfl hE4
  have hqA : CFSG.IsQuasisimple ↥(P.A i) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv he.symm hqSL
  have hm : ggK1DCo_OrbitModel nf K (⟨⟨.A, 1, 2 * nf⟩, true⟩ : GGKacOrbit) ↥(P.A i) := by
    simp only [ggK1DCo_OrbitModel]
    exact ⟨E, hEfield, hEfin, hEcard, ⟨he⟩⟩
  rw [hsub, hget]
  exact ggK1Df_quasi_dict (o := (⟨⟨.A, 1, 2 * nf⟩, true⟩ : GGKacOrbit)) rfl hqA hm

private lemma ggK1Df_gl_one_commutative {E : Type} [Field E] :
    IsMulCommutative (Matrix.GeneralLinearGroup (Fin 1) E) := by
  rw [isMulCommutative_iff]
  intro a b
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one]
  exact mul_comm _ _

private lemma ggK1Df_gl_zero_commutative {E : Type} [Field E] :
    IsMulCommutative (Matrix.GeneralLinearGroup (Fin 0) E) :=
  isMulCommutative_iff.mpr (fun a b => Units.ext (by ext i j; exact isEmptyElim i))

private lemma ggK1Df_gl_small_commutative {E : Type} [Field E] {m : ℕ} (hm : m ≤ 1) :
    IsMulCommutative (Matrix.GeneralLinearGroup (Fin m) E) := by
  rcases m with _ | _ | k
  · exact ggK1Df_gl_zero_commutative
  · exact ggK1Df_gl_one_commutative
  · omega

private theorem ggK1Df_om_dummy_dict {p nf : ℕ} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (eps : Bool) (m : ℕ) (hkind : P.kind i = .om eps m) (hm : m ≤ 1)
    (j : Fin (P.blk i).length) :
    ((P.blk i).get j).qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ := by
  have hblk : P.blk i = [ggK1DCo_dummyOrbit nf] := by
    rw [P.blk_eq i, hkind, ggK1DCo_kindOrbits, if_pos hm]
  have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
  have hsub : P.sub i j = P.A i := by
    haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
    rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
  have hget : (P.blk i).get j = ggK1DCo_dummyOrbit nf := by
    have hmem : (P.blk i).get j ∈ [ggK1DCo_dummyOrbit nf] := by
      rw [← hblk]; exact List.get_mem _ _
    simpa using hmem
  have habel := (P.fixed_model i eps m hkind).2.2.2.2.2 hm
  haveI : IsMulCommutative ↥(P.sub i j) := by
    rw [hsub]
    exact isMulCommutative_iff.mpr (fun a b => Subtype.ext (habel a.1 a.2 b.1 b.2).eq)
  have hbot : ⁅P.sub i j, P.sub i j⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr inferInstance
  refine ⟨?_, ?_⟩
  · rw [hget]; rfl
  · rw [hbot]; exact ggK1Df_not_quasi_bot

private theorem ggK1Df_sl_dummy_dict {p nf : ℕ} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (m : ℕ) (hkind : P.kind i = .sl m) (hm : m ≤ 1)
    (j : Fin (P.blk i).length) :
    ((P.blk i).get j).qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ := by
  have hblk : P.blk i = [ggK1DCo_dummyOrbit nf] := by
    rw [P.blk_eq i, hkind, ggK1DCo_kindOrbits, if_pos hm]
  have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
  have hsub : P.sub i j = P.A i := by
    haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
    rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
  have hget : (P.blk i).get j = ggK1DCo_dummyOrbit nf := by
    have hmem : (P.blk i).get j ∈ [ggK1DCo_dummyOrbit nf] := by
      rw [← hblk]; exact List.get_mem _ _
    simpa using hmem
  obtain ⟨E, hEfield, _hEfin, _h, _hh, _hne, _hcard, _hmult, ⟨he⟩⟩ := P.paired_model i m hkind
  letI : Field E := hEfield
  haveI : IsMulCommutative (Matrix.GeneralLinearGroup (Fin m) E) :=
    ggK1Df_gl_small_commutative hm
  haveI : IsMulCommutative ↥(P.A i) :=
    isMulCommutative_iff.mpr
      (fun a b => he.injective (by rw [map_mul, map_mul]; exact mul_comm' (he a) (he b)))
  haveI : IsMulCommutative ↥(P.sub i j) := by rw [hsub]; infer_instance
  have hbot : ⁅P.sub i j, P.sub i j⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr inferInstance
  refine ⟨?_, ?_⟩
  · rw [hget]; rfl
  · rw [hbot]; exact ggK1Df_not_quasi_bot

private theorem ggK1Df_su_dummy_dict {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (m : ℕ) (hkind : P.kind i = .su m) (hm : m ≤ 1)
    (j : Fin (P.blk i).length) :
    ((P.blk i).get j).qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ := by
  have hblk : P.blk i = [ggK1DCo_dummyOrbit nf] := by
    rw [P.blk_eq i, hkind, ggK1DCo_kindOrbits, if_pos hm]
  have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
  have hsub : P.sub i j = P.A i := by
    haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
    rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
  have hget : (P.blk i).get j = ggK1DCo_dummyOrbit nf := by
    have hmem : (P.blk i).get j ∈ [ggK1DCo_dummyOrbit nf] := by
      rw [← hblk]; exact List.get_mem _ _
    simpa using hmem
  rcases m with _ | _ | k
  ·
    obtain ⟨E, hEfield, hEfin, hE, W, hWadd, hWmod, hWfin, Hf, hsym, hsep, hdim, ⟨he⟩⟩ :=
      P.selfDual_model i 0 hkind
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    letI : AddCommGroup W := hWadd
    letI : Module E W := hWmod
    letI : FiniteDimensional E W := hWfin
    haveI : Subsingleton W := Module.finrank_zero_iff.mp hdim
    haveI : Subsingleton ↥(CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    haveI : Subsingleton ↥(P.A i) :=
      ⟨fun a b => he.injective (Subsingleton.elim (he a) (he b))⟩
    have hnotq : ¬ CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ := by
      rw [hsub]
      exact ggK1Df_solvable_not_quasi (S := P.A i) inferInstance
    exact ⟨by rw [hget]; rfl, hnotq⟩
  ·
    obtain ⟨E, hEfield, hEfin, hE, W, hWadd, hWmod, hWfin, Hf, hsym, hsep, hdim, ⟨he⟩⟩ :=
      P.selfDual_model i 1 hkind
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    letI : AddCommGroup W := hWadd
    letI : Module E W := hWmod
    letI : FiniteDimensional E W := hWfin
    obtain ⟨b, hb⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.exists_orthonormal_basis hE hsym hsep
    let b' : Module.Basis (Fin 1) E W := b.reindex (finCongr hdim)
    have hb' : ∀ i j, Hf (b' i) (b' j) = if i = j then 1 else 0 := by
      intro i j
      dsimp only [b']
      rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
      simp
    have hclass := ggK1CBl_classical_su (K := K) hK hnf (le_refl 1) hE hsym hsep b' hb' he
    have hnotq : ¬ CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ := by
      rw [hsub]
      rcases hclass.1 with hq | hs
      · exact absurd (hclass.2.1.mp hq) (by
          rw [show (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.su 1)).qs = false from rfl]
          exact Bool.false_ne_true)
      · exact ggK1Df_solvable_not_quasi hs
    exact ⟨by rw [hget]; rfl, hnotq⟩
  · omega

private theorem ggK1Df_su_two_dict {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (m : ℕ) (hkind : P.kind i = .su m) (hm2 : m = 2)
    (j : Fin (P.blk i).length) :
    (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ ↔ ((P.blk i).get j).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ →
        ggK1DCo_OrbitModel nf K ((P.blk i).get j) ↥⁅P.sub i j, P.sub i j⁆) := by
  haveI : Fintype K := Fintype.ofFinite K
  subst hm2
  have hblk : P.blk i = [ggMultBlockA 1 nf 2] := by
    rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_su (le_refl 2)]
  have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
  have hsub : P.sub i j = P.A i := by
    haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
    rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
  have hget : (P.blk i).get j = ggMultBlockA 1 nf 2 := by
    have hmem : (P.blk i).get j ∈ [ggMultBlockA 1 nf 2] := by
      rw [← hblk]; exact List.get_mem _ _
    simpa using hmem
  obtain ⟨E, hEfield, hEfin, hE, W, hWadd, hWmod, hWfin, Hf, hsym, hsep, hdim, ⟨he⟩⟩ :=
    P.selfDual_model i 2 hkind
  letI : Field E := hEfield
  letI : Fintype E := hEfin
  letI : AddCommGroup W := hWadd
  letI : Module E W := hWmod
  letI : FiniteDimensional E W := hWfin
  obtain ⟨b, hb⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.exists_orthonormal_basis hE hsym hsep
  let b' : Module.Basis (Fin 2) E W := b.reindex (finCongr hdim)
  have hb' : ∀ i j, Hf (b' i) (b' j) = if i = j then 1 else 0 := by
    intro i j
    dsimp only [b']
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    simp
  have hclass := ggK1CBl_classical_su (K := K) hK hnf (by omega : 1 ≤ 2) hE hsym hsep b' hb' he
  have hqs_eq : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.su 2)).qs =
      (ggMultBlockA 1 nf 2).qs := by
    rw [ggK1Df_ccKindOrbit_su (le_refl 2)]
  rw [hsub, hget]
  refine ⟨?_, ?_⟩
  · rw [hclass.2.1, hqs_eq]
  · intro hq
    obtain ⟨E', hE'field, hE'fin, hE'card, ⟨eSU⟩⟩ := hclass.2.2 hq
    rw [hK] at eSU
    letI : Field E' := hE'field
    letI : Fintype E' := hE'fin
    have hcardE' : Nat.card E' = (2 ^ nf) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hE'card, hK]
    have hcardE'' : Nat.card E' = 2 ^ (2 * nf) := by
      rw [hcardE', ← pow_mul, mul_comm]
    haveI : CharP E' 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hcardE''
    letI : Fintype ↥(CFSG.LieType.Steinberg.fixedSubfield E' 2 nf) := Fintype.ofFinite _
    have hcardfix : Nat.card (CFSG.LieType.Steinberg.fixedSubfield E' 2 nf) = 2 ^ nf :=
      CFSG.LieType.Steinberg.card_fixedSubfield hcardE'
    have hcardfix' : Fintype.card ↥(CFSG.LieType.Steinberg.fixedSubfield E' 2 nf) =
        Fintype.card K := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardfix, hK]
    have eK : CFSG.LieType.Steinberg.fixedSubfield E' 2 nf ≃+* K :=
      FiniteField.ringEquivOfCardEq hcardfix'
    obtain ⟨e2⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := E') (r := 2) (f := nf) hcardE'
    have eSL : Matrix.SpecialLinearGroup (Fin 2)
          (CFSG.LieType.Steinberg.fixedSubfield E' 2 nf) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K :=
      CFSG.ClassicalModels.specialLinearFieldEquiv eK (Fin 2)
    have hba : ggMultBlockA 1 nf 2 = (⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit) := by
      simp [ggMultBlockA]
    rw [hba]
    simp only [ggK1DCo_OrbitModel]
    rw [if_neg (by omega : ¬ (True ∧ nf = 2 * nf))]
    exact ⟨(eSU.trans e2.symm).trans eSL⟩

private theorem ggK1Df_orbitModel_congr {nf : ℕ} {K : Type} [Field K] {o : GGKacOrbit}
    {H H' : Type} [Group H] [Group H'] (e : H ≃* H') :
    ggK1DCo_OrbitModel nf K o H → ggK1DCo_OrbitModel nf K o H' := by
  obtain ⟨⟨tag, r, n⟩, qs⟩ := o
  intro h
  cases tag <;> simp only [ggK1DCo_OrbitModel] at h ⊢
  case A =>
    by_cases hc : r = 1 ∧ n = 2 * nf
    · rw [if_pos hc] at h ⊢
      obtain ⟨E, hEfield, hEfin, hEcard, ⟨eH⟩⟩ := h
      exact ⟨E, hEfield, hEfin, hEcard, ⟨e.symm.trans eH⟩⟩
    · rw [if_neg hc] at h ⊢
      obtain ⟨eH⟩ := h
      exact ⟨e.symm.trans eH⟩
  case twA =>
    obtain ⟨E, hEfield, hEfin, hEcard, ⟨eH⟩⟩ := h
    exact ⟨E, hEfield, hEfin, hEcard, ⟨e.symm.trans eH⟩⟩
  case D =>
    obtain ⟨eH⟩ := h
    exact ⟨e.symm.trans eH⟩
  case twD =>
    obtain ⟨b, c, hirr, ⟨eH⟩⟩ := h
    exact ⟨b, c, hirr, ⟨e.symm.trans eH⟩⟩
  all_goals exact h.elim

private noncomputable def ggK1Df_commutatorEquiv {G R : Type} [Group G] [Group R]
    {S : Subgroup G} {T : Subgroup R} (φ : ↥S ≃* ↥T) : ↥⁅S, S⁆ ≃* ↥⁅T, T⁆ :=
  (Subgroup.equivMapOfInjective (commutator ↥S) S.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator S)) |>.symm |>.trans
  ((MulEquiv.commutatorCongr φ).trans
    ((Subgroup.equivMapOfInjective (commutator ↥T) T.subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator T))))

private theorem ggK1Df_dict_transport {G R : Type} [Group G] [Group R]
    {S : Subgroup G} {T : Subgroup R} (φ : ↥S ≃* ↥T) {p nf : ℕ} {K : Type} [Field K]
    {o : GGKacOrbit}
    (h : (o.qs = true ∧ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧ ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆) ∨
      (o.qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧
        (o ≠ ggK1DCo_dummyOrbit nf → ∃ t ∈ S, t ^ p = 1 ∧ ∃ a ∈ S, a * t ≠ t * a))) :
    (o.qs = true ∧ CFSG.IsQuasisimple ↥⁅T, T⁆ ∧ ggK1DCo_OrbitModel nf K o ↥⁅T, T⁆) ∨
      (o.qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅T, T⁆ ∧
        (o ≠ ggK1DCo_dummyOrbit nf → ∃ t ∈ T, t ^ p = 1 ∧ ∃ a ∈ T, a * t ≠ t * a)) := by
  rcases h with ⟨hqs, hq, hm⟩ | ⟨hqs, hnq, hwit⟩
  · left
    refine ⟨hqs, ?_, ?_⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (ggK1Df_commutatorEquiv φ) hq
    · exact ggK1Df_orbitModel_congr (ggK1Df_commutatorEquiv φ) hm
  · right
    refine ⟨hqs, ?_, ?_⟩
    · intro hq
      exact hnq (CFSG.LocalCores.isQuasisimple_of_mulEquiv (ggK1Df_commutatorEquiv φ).symm hq)
    · intro ho
      obtain ⟨t, ht, ht1, a, ha, hne⟩ := hwit ho
      refine ⟨(φ ⟨t, ht⟩ : R), (φ ⟨t, ht⟩).2, ?_, (φ ⟨a, ha⟩ : R), (φ ⟨a, ha⟩).2, ?_⟩
      · have hS : (⟨t, ht⟩ : ↥S) ^ p = 1 := Subtype.ext ht1
        have h1 : (φ ⟨t, ht⟩ : ↥T) ^ p = 1 := by rw [← map_pow, hS, map_one]
        simpa using congrArg (fun x : ↥T => (x : R)) h1
      · intro hc
        apply hne
        have hc' : φ ⟨a, ha⟩ * φ ⟨t, ht⟩ = φ ⟨t, ht⟩ * φ ⟨a, ha⟩ := Subtype.ext hc
        have := congrArg φ.symm hc'
        simpa [map_mul] using this

private theorem ggK1Df_witness_subgroup {G H : Type} [Group G] [Group H] {A : Subgroup G}
    (φ : ↥A ≃* H) {p : ℕ} (h : ∃ t a : H, t ^ p = 1 ∧ a * t ≠ t * a) :
    ∃ t ∈ A, t ^ p = 1 ∧ ∃ a ∈ A, a * t ≠ t * a := by
  obtain ⟨t, a, ht, hne⟩ := h
  refine ⟨(φ.symm t : G), (φ.symm t).2, ?_, (φ.symm a : G), (φ.symm a).2, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow φ.symm t p, ht, map_one, Subgroup.coe_one]
  · intro hc
    apply hne
    have hc' : (φ.symm a) * (φ.symm t) = (φ.symm t) * (φ.symm a) :=
      Subtype.ext (by simpa [Subgroup.coe_mul] using hc)
    have := congrArg φ hc'
    simpa [map_mul] using this

private theorem ggK1Df_sl2_witness {K : Type} [Field K] :
    ∃ t a : Matrix.SpecialLinearGroup (Fin 2) K, t ^ 3 = 1 ∧ a * t ≠ t * a := by
  let tm : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1]
  let am : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1]
  have htdet : tm.det = 1 := by rw [Matrix.det_fin_two]; simp [tm]
  have hadet : am.det = 1 := by rw [Matrix.det_fin_two]; simp [am]
  let t : Matrix.SpecialLinearGroup (Fin 2) K := ⟨tm, htdet⟩
  let a : Matrix.SpecialLinearGroup (Fin 2) K := ⟨am, hadet⟩
  have htcoe : (t : Matrix (Fin 2) (Fin 2) K) = tm := rfl
  have hacoe : (a : Matrix (Fin 2) (Fin 2) K) = am := rfl
  refine ⟨t, a, ?_, ?_⟩
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, htcoe]
    fin_cases i <;> fin_cases j <;>
      simp [tm, Matrix.mul_apply, Fin.sum_univ_two, pow_succ, Matrix.one_apply]
  · intro hcon
    have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
      (x : Matrix (Fin 2) (Fin 2) K) 0 1) hcon
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      hacoe, htcoe] at h
    simp [am, tm, Matrix.mul_apply, Fin.sum_univ_two] at h

private theorem ggK1Df_dict_of_iff_model {p nf : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {S : Subgroup G} {o : GGKacOrbit}
    (hiff : CFSG.IsQuasisimple ↥⁅S, S⁆ ↔ o.qs = true)
    (hmodel : CFSG.IsQuasisimple ↥⁅S, S⁆ → ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆)
    (hwit : o.qs = false → o ≠ ggK1DCo_dummyOrbit nf →
      ∃ t ∈ S, t ^ p = 1 ∧ ∃ a ∈ S, a * t ≠ t * a) :
    (o.qs = true ∧ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧ ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆) ∨
      (o.qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧
        (o ≠ ggK1DCo_dummyOrbit nf → ∃ t ∈ S, t ^ p = 1 ∧ ∃ a ∈ S, a * t ≠ t * a)) := by
  by_cases hq : CFSG.IsQuasisimple ↥⁅S, S⁆
  · exact Or.inl ⟨hiff.mp hq, hq, hmodel hq⟩
  · have hqs : o.qs = false := by
      cases ho : o.qs with
      | false => rfl
      | true => exact absurd (hiff.mpr ho) hq
    exact Or.inr ⟨hqs, hq, hwit hqs⟩

private lemma ggK1Df_get_dummy {nf : ℕ} {l : List GGKacOrbit}
    (hblk : l = [ggK1DCo_dummyOrbit nf]) (j : Fin l.length) :
    l.get j = ggK1DCo_dummyOrbit nf := by
  have hmem : l.get j ∈ [ggK1DCo_dummyOrbit nf] := by rw [← hblk]; exact List.get_mem _ _
  simpa using hmem

private noncomputable def ggK1Df_glMapEquiv {ι K K' : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Field K'] (e : K ≃+* K') : GL ι K ≃* GL ι K' :=
  MulEquiv.ofBijective (Matrix.GeneralLinearGroup.map e.toRingHom)
    ⟨Matrix.GeneralLinearGroup.map_injective e.injective, by
      intro y
      refine ⟨Matrix.GeneralLinearGroup.map e.symm.toRingHom y, ?_⟩
      have hcomp : e.toRingHom.comp e.symm.toRingHom = RingHom.id K' :=
        RingHom.ext (fun x => by simp)
      calc Matrix.GeneralLinearGroup.map e.toRingHom
            (Matrix.GeneralLinearGroup.map e.symm.toRingHom y)
          = Matrix.GeneralLinearGroup.map (e.toRingHom.comp e.symm.toRingHom) y := by
            rw [Matrix.GeneralLinearGroup.map_comp]; rfl
        _ = Matrix.GeneralLinearGroup.map (RingHom.id K') y := by rw [hcomp]
        _ = y := by rw [Matrix.GeneralLinearGroup.map_id]; rfl⟩

private theorem ggK1Df_glMapEquiv_apply {ι K K' : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Field K'] (e : K ≃+* K') (g : GL ι K) (i j : ι) :
    ((ggK1Df_glMapEquiv e g : GL ι K') : Matrix ι ι K') i j =
      e ((g : Matrix ι ι K) i j) := by
  rw [ggK1Df_glMapEquiv]
  exact Matrix.GeneralLinearGroup.map_apply e.toRingHom i j g

private theorem ggK1Df_glMapEquiv_coe {ι K K' : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Field K'] (e : K ≃+* K') (g : GL ι K) :
    ((ggK1Df_glMapEquiv e g : GL ι K') : Matrix ι ι K') =
      (g : Matrix ι ι K).map e := by
  ext i j
  rw [ggK1Df_glMapEquiv_apply, Matrix.map_apply]

private theorem ggK1Df_glMapEquiv_symm_coe {ι K K' : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Field K'] (e : K ≃+* K') (g : GL ι K') :
    (((ggK1Df_glMapEquiv e).symm g : GL ι K) : Matrix ι ι K) =
      (g : Matrix ι ι K').map e.symm := by
  have h2 := ggK1Df_glMapEquiv_coe e ((ggK1Df_glMapEquiv e).symm g)
  rw [MulEquiv.apply_symm_apply] at h2
  rw [h2]
  ext i j
  simp [Matrix.map_apply]

private noncomputable def ggK1Df_vecMap {ι K K' : Type} [Field K] [Field K']
    (e : K ≃+* K') (v : ι → K) : ι → K' :=
  fun i => e (v i)

private theorem ggK1Df_mulVec_map {ι K K' : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Field K'] (e : K ≃+* K') (M : Matrix ι ι K) (v : ι → K) :
    (M.map e).mulVec (ggK1Df_vecMap e v) = ggK1Df_vecMap e (M.mulVec v) := by
  funext i
  simp only [ggK1Df_vecMap, mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

private theorem ggK1Df_statedQuadPlus_map {K K' : Type} [Field K] [Field K']
    (e : K ≃+* K') (v : Fin 3 ⊕ Fin 3 → K) :
    StatedQuadPlus 3 K' (ggK1Df_vecMap e v) = e (StatedQuadPlus 3 K v) := by
  simp only [StatedQuadPlus, MatrixModel.plusQuadCore, ggK1Df_vecMap, map_sum, map_mul]

private theorem ggK1Df_isometryCore_map {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') :
    (MatrixModel.isometryCore (StatedQuadPlus 3 K)).map
        (ggK1Df_glMapEquiv (ι := Fin 3 ⊕ Fin 3) e).toMonoidHom =
      MatrixModel.isometryCore (StatedQuadPlus 3 K') := by
  rw [MatrixModel.isometryCore, MonoidHom.map_closure]
  congr 1
  ext A
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨B, hB, rfl⟩
    intro w
    let v : Fin 3 ⊕ Fin 3 → K := fun i => e.symm (w i)
    have hw : ggK1Df_vecMap e v = w := by funext i; simp [ggK1Df_vecMap, v]
    have hcoe : (ggK1Df_glMapEquiv (ι := Fin 3 ⊕ Fin 3) e).toMonoidHom B =
        ggK1Df_glMapEquiv (ι := Fin 3 ⊕ Fin 3) e B := rfl
    have hmv : (ggK1Df_glMapEquiv (ι := Fin 3 ⊕ Fin 3) e B :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K').mulVec w =
        ggK1Df_vecMap e ((B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K).mulVec v) := by
      rw [← hw, ggK1Df_glMapEquiv_coe]
      exact ggK1Df_mulVec_map e (B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) v
    rw [hcoe, hmv, ggK1Df_statedQuadPlus_map, hB v, ← ggK1Df_statedQuadPlus_map e v, hw]
  · intro hA
    refine ⟨(ggK1Df_glMapEquiv (ι := Fin 3 ⊕ Fin 3) e).symm A, ?_, by simp⟩
    intro v
    apply e.injective
    have hmv : ggK1Df_vecMap e (((ggK1Df_glMapEquiv (ι := Fin 3 ⊕ Fin 3) e).symm A :
            Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K).mulVec v) =
        (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K').mulVec (ggK1Df_vecMap e v) := by
      funext i
      simp only [ggK1Df_vecMap, mulVec, dotProduct, ggK1Df_glMapEquiv_symm_coe,
        Matrix.map_apply, map_sum, map_mul, map_inv₀]
      apply Finset.sum_congr rfl
      intro j _
      simp
    rw [← ggK1Df_statedQuadPlus_map e (((ggK1Df_glMapEquiv (ι := Fin 3 ⊕ Fin 3) e).symm A :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K).mulVec v), hmv]
    simpa [ggK1Df_statedQuadPlus_map e v] using hA (ggK1Df_vecMap e v)

private theorem ggK1Df_statedOmega_plus_three_mapEquiv {K K' : Type} [Field K] [Field K']
    (e : K ≃+* K') :
    Nonempty (↥(StatedOmega (StatedQuadPlus 3 K)) ≃* ↥(StatedOmega (StatedQuadPlus 3 K'))) := by
  have hcore := ggK1Df_isometryCore_map e
  have hOmega : (StatedOmega (StatedQuadPlus 3 K)).map
      (ggK1Df_glMapEquiv (ι := Fin 3 ⊕ Fin 3) e).toMonoidHom =
      StatedOmega (StatedQuadPlus 3 K') := by
    change (⁅MatrixModel.isometryCore (StatedQuadPlus 3 K),
      MatrixModel.isometryCore (StatedQuadPlus 3 K)⁆).map _ =
      ⁅MatrixModel.isometryCore (StatedQuadPlus 3 K'),
        MatrixModel.isometryCore (StatedQuadPlus 3 K')⁆
    rw [Subgroup.map_commutator, hcore]
  exact ⟨(MulEquiv.subgroupMap (ggK1Df_glMapEquiv (ι := Fin 3 ⊕ Fin 3) e)
    (StatedOmega (StatedQuadPlus 3 K))).trans (MulEquiv.subgroupCongr hOmega)⟩

private theorem ggK1Df_om_three_dict {p nf : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (eps : Bool) (m : ℕ) (hkind : P.kind i = .om eps m) (hm : m = 3)
    (j : Fin (P.blk i).length) :
    (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ ↔ ((P.blk i).get j).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅P.sub i j, P.sub i j⁆ →
        ggK1DCo_OrbitModel nf K ((P.blk i).get j) ↥⁅P.sub i j, P.sub i j⁆) := by
  subst hm
  cases eps
  · have hblk : P.blk i = [(⟨⟨.twA, 3, nf⟩, true⟩ : GGKacOrbit)] := by
      rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega), ggK1Df_ggMultV0_three]
      simp
    have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
    have hsub : P.sub i j = P.A i := by
      haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
      rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
    have hget : (P.blk i).get j = (⟨⟨.twA, 3, nf⟩, true⟩ : GGKacOrbit) := by
      have hj : (j : ℕ) = 0 := by omega
      rw [List.get_of_eq hblk]; simp [hj]
    rcases P.fixed_model i false 3 hkind with ⟨-, -, hmodel, -, -, -⟩
    obtain ⟨b, c, hirr, ⟨he⟩⟩ := by simpa using hmodel (le_refl 3)
    obtain ⟨E, hEfield, hE, ⟨eSU⟩⟩ :=
      CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
        (K := K) hK hirr
    letI : Field E := hEfield
    haveI : Finite E := hE.finite
    letI : Fintype E := Fintype.ofFinite E
    have hEcard : Nat.card E = (2 ^ nf) ^ 2 := hE.card_eq_sq
    have hqSU : CFSG.IsQuasisimple ↥(StatedSU 4 (2 ^ nf) E) :=
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hEcard (by norm_num)
        (by norm_num : ((4 : ℕ), 2 ^ nf) ≠ (3, 2))).1
    have hqA : CFSG.IsQuasisimple ↥(P.A i) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (he.trans eSU).symm hqSU
    rw [hsub, hget]
    refine ggK1Df_quasi_dict (o := ⟨⟨.twA, 3, nf⟩, true⟩) rfl hqA ?_
    refine ⟨E, hEfield, inferInstance, ?_, ?_⟩
    · rw [← Nat.card_eq_fintype_card, hEcard, hK]
    · exact ⟨by rw [hK]; exact he.trans eSU⟩
  · have hblk : P.blk i = [(⟨⟨.A, 3, nf⟩, true⟩ : GGKacOrbit)] := by
      rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega), ggK1Df_ggMultV0_three]
      simp
    have hlen : (P.blk i).length = 1 := by rw [hblk]; rfl
    have hsub : P.sub i j = P.A i := by
      haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
      rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
    have hget : (P.blk i).get j = (⟨⟨.A, 3, nf⟩, true⟩ : GGKacOrbit) := by
      have hj : (j : ℕ) = 0 := by omega
      rw [List.get_of_eq hblk]; simp [hj]
    rcases P.fixed_model i true 3 hkind with ⟨-, -, hmodel, -, -, -⟩
    obtain ⟨he⟩ := by simpa using hmodel (le_refl 3)
    have hqΩ : CFSG.IsQuasisimple ↥(StatedOmega (StatedQuadPlus 3 K)) :=
      CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus (n := 3) (K := K) (le_refl 3)
    have hqA : CFSG.IsQuasisimple ↥(P.A i) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv he.symm hqΩ
    rw [hsub, hget]
    by_cases h4 : 4 ≤ Nat.card K
    · obtain ⟨eSL⟩ :=
        CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadPlus_three_equiv
          (K := K) h4
      refine ggK1Df_quasi_dict (o := ⟨⟨.A, 3, nf⟩, true⟩) rfl hqA ?_
      exact ⟨he.trans eSL⟩
    · have h2 : Nat.card K = 2 := by
        have hlt : 2 ^ nf < 2 ^ 2 := by
          have h : Nat.card K < 4 := by omega
          rw [hK] at h
          norm_num
          exact h
        have hnf1 : nf < 2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
        have hnf1' : nf = 1 := by omega
        rw [hK, hnf1']; norm_num
      haveI : Fintype K := Fintype.ofFinite K
      have e : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h2]; norm_num)
      obtain ⟨eOmega⟩ := ggK1Df_statedOmega_plus_three_mapEquiv e
      open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration in
      have eAlt := statedOmega_quadPlus_three_mulEquiv_alt8
      have eSL2 := CFSG.CGT.M24R.sl4GF2EquivAlt8
      have eF2 : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 1) ≃*
          Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
        CFSG.ClassicalModels.specialLinearFieldEquiv
          (GaloisField.equivZmodP (p := 2)).toRingEquiv (Fin 4)
      have eSLK : Matrix.SpecialLinearGroup (Fin 4) K ≃*
          Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
        CFSG.ClassicalModels.specialLinearFieldEquiv e (Fin 4)
      refine ggK1Df_quasi_dict (o := ⟨⟨.A, 3, nf⟩, true⟩) rfl hqA ?_
      exact ⟨he.trans eOmega |>.trans eAlt |>.trans eSL2.symm |>.trans eF2 |>.trans eSLK.symm⟩

private lemma ggK1Df_get_singleton {l : List GGKacOrbit} {o : GGKacOrbit}
    (hblk : l = [o]) (j : Fin l.length) : l.get j = o := by
  have hmem : l.get j ∈ [o] := by rw [← hblk]; exact List.get_mem _ _
  simpa using hmem

private theorem ggK1Df_su_kindWitness {p nf : ℕ} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (m : ℕ) (hkind : P.kind i = .su m) (hm : 1 ≤ m) :
    ggK1CBl_KindWitness nf K (ggK1CCo_Kind.su m) (P.A i) := by
  obtain ⟨E, hEfield, hEfin, hE, W, hWadd, hWmod, hWfin, Hf, hsym, hsep, hdim, ⟨he⟩⟩ :=
    P.selfDual_model i m hkind
  letI : Field E := hEfield
  letI : Fintype E := hEfin
  letI : AddCommGroup W := hWadd
  letI : Module E W := hWmod
  letI : FiniteDimensional E W := hWfin
  obtain ⟨b, hb⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.exists_orthonormal_basis hE hsym hsep
  let b' : Module.Basis (Fin m) E W := b.reindex (finCongr hdim)
  have hb' : ∀ i j, Hf (b' i) (b' j) = if i = j then 1 else 0 := by
    intro i j
    dsimp only [b']
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    simp
  exact ⟨hm, E, hEfield, hEfin, hE, W, hWadd, hWmod, hWfin, Hf, hsym, hsep, ⟨b', hb'⟩, ⟨he⟩⟩

private theorem ggK1Df_su_witness {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (m : ℕ) (hkind : P.kind i = .su m) (hm : 1 ≤ m)
    (j : Fin (P.blk i).length)
    (hqs : ((P.blk i).get j).qs = false)
    (ho : (P.blk i).get j ≠ ggK1DCo_dummyOrbit nf) :
    ∃ t ∈ P.sub i j, t ^ p = 1 ∧ ∃ a ∈ P.sub i j, a * t ≠ t * a := by
  have hlen : (P.blk i).length = 1 := by
    rw [P.blk_eq i, hkind]
    exact ggK1Df_kindOrbits_su_length
  have hsub : P.sub i j = P.A i := by
    haveI : Subsingleton (Fin (P.blk i).length) := ⟨fun a b => Fin.ext (by omega)⟩
    rw [← P.sub_join i, ggK1Df_iSup_subsingleton]
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm1 : m ≤ 1 := by omega
    have hblk : P.blk i = [ggK1DCo_dummyOrbit nf] := by
      rw [P.blk_eq i, hkind, ggK1DCo_kindOrbits, if_pos hm1]
    exact ho (ggK1Df_get_dummy hblk j)
  have hblk : P.blk i = [ggMultBlockA (m - 1) nf 2] := by
    rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_su hm2]
  have hget : (P.blk i).get j = ggMultBlockA (m - 1) nf 2 :=
    ggK1Df_get_singleton hblk j
  have hqs' : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.su m)).qs = false := by
    rw [ggK1Df_ccKindOrbit_su hm2, ← hget]
    exact hqs
  have hh : (ggK1CCo_Kind.su m).hasOrbit = true := by
    rcases m with _ | _ | k
    · omega
    · omega
    · rfl
  rw [hsub]
  exact ggK1CBl_solvable_witness hnf hK hp hp2 hdvd
    (ggK1Df_su_kindWitness P i m hkind hm) hh hqs'

private theorem ggK1Df_dict_su {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (m : ℕ) (hkind : P.kind i = .su m)
    (j : Fin (P.blk i).length) :
    let o := (P.blk i).get j
    let S := P.sub i j
    (o.qs = true ∧ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧ ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆) ∨
      (o.qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧
        (o ≠ ggK1DCo_dummyOrbit nf → ∃ t ∈ S, t ^ p = 1 ∧ ∃ a ∈ S, a * t ≠ t * a)) := by
  rcases lt_or_ge m 2 with hm2 | hm2
  · obtain ⟨hqs, hnotq⟩ := ggK1Df_su_dummy_dict hnf hK P i m hkind (by omega) j
    refine Or.inr ⟨hqs, hnotq, ?_⟩
    intro ho
    have hblk : P.blk i = [ggK1DCo_dummyOrbit nf] := by
      rw [P.blk_eq i, hkind, ggK1DCo_kindOrbits, if_pos (by omega)]
    exact absurd (ggK1Df_get_dummy hblk j) ho
  · rcases eq_or_lt_of_le hm2 with hm2' | hm3
    · subst hm2'
      obtain ⟨hiff, hmodel⟩ := ggK1Df_su_two_dict hnf hK P i 2 hkind rfl j
      exact ggK1Df_dict_of_iff_model hiff hmodel
        (ggK1Df_su_witness hp hp2 hnf hK hdvd P i 2 hkind (by omega : 1 ≤ 2) j)
    · obtain ⟨hiff, hmodel⟩ := ggK1Df_su_dict hp hp2 hnf hK P i m hkind hm3 j
      exact ggK1Df_dict_of_iff_model hiff hmodel
        (ggK1Df_su_witness hp hp2 hnf hK hdvd P i m hkind (by omega) j)

private theorem ggK1Df_dict_sl {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (h1 : p ∣ 2 ^ nf - 1)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (hxO : OddOrderIsometry Qf p (ggK1DLin (x : GL ι K)))
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (m : ℕ) (hkind : P.kind i = .sl m)
    (j : Fin (P.blk i).length) :
    let o := (P.blk i).get j
    let S := P.sub i j
    (o.qs = true ∧ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧ ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆) ∨
      (o.qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧
        (o ≠ ggK1DCo_dummyOrbit nf → ∃ t ∈ S, t ^ p = 1 ∧ ∃ a ∈ S, a * t ≠ t * a)) := by
  rcases lt_or_ge m 2 with hm2 | hm2
  · obtain ⟨hqs, hnotq⟩ := ggK1Df_sl_dummy_dict P i m hkind (by omega) j
    refine Or.inr ⟨hqs, hnotq, ?_⟩
    intro ho
    have hblk : P.blk i = [ggK1DCo_dummyOrbit nf] := by
      rw [P.blk_eq i, hkind, ggK1DCo_kindOrbits, if_pos (by omega)]
    exact absurd (ggK1Df_get_dummy hblk j) ho
  · obtain ⟨hiff, hmodel⟩ := ggK1Df_sl_dict hp hp2 hnf hK h1 hxO P i m hkind hm2 j
    refine ggK1Df_dict_of_iff_model hiff hmodel ?_
    intro hqs ho
    exfalso
    have hblk : P.blk i = [ggMultBlockA (m - 1) nf 1] := by
      rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_sl hm2]
    have hget : (P.blk i).get j = ggMultBlockA (m - 1) nf 1 :=
      ggK1Df_get_singleton hblk j
    have hnf1 : nf ≠ 1 := by
      intro h
      subst h
      exact hp.not_dvd_one (by simpa using h1)
    have htrue : (ggMultBlockA (m - 1) nf 1).qs = true := by
      simp [ggMultBlockA, hnf1]
    rw [hget, htrue] at hqs
    exact Bool.noConfusion hqs

private theorem ggK1Df_dict_om {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (eps : Bool) (m : ℕ) (hkind : P.kind i = .om eps m)
    (j : Fin (P.blk i).length) :
    let o := (P.blk i).get j
    let S := P.sub i j
    (o.qs = true ∧ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧ ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆) ∨
      (o.qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧
        (o ≠ ggK1DCo_dummyOrbit nf → ∃ t ∈ S, t ^ p = 1 ∧ ∃ a ∈ S, a * t ≠ t * a)) := by
  rcases lt_or_ge m 2 with hm2 | hm2
  · obtain ⟨hqs, hnotq⟩ := ggK1Df_om_dummy_dict P i eps m hkind (by omega) j
    refine Or.inr ⟨hqs, hnotq, ?_⟩
    intro ho
    have hblk : P.blk i = [ggK1DCo_dummyOrbit nf] := by
      rw [P.blk_eq i, hkind, ggK1DCo_kindOrbits, if_pos (by omega)]
    exact absurd (ggK1Df_get_dummy hblk j) ho
  · rcases eq_or_lt_of_le hm2 with hm2' | hm3
    · subst hm2'
      cases eps
      · obtain ⟨hiff, hmodel⟩ := ggK1Df_om_two_dict_minus hK hnf P i hkind j
        refine ggK1Df_dict_of_iff_model hiff hmodel ?_
        intro hqs _
        have hblk : P.blk i = [(⟨⟨.A, 1, 2 * nf⟩, true⟩ : GGKacOrbit)] := by
          rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega), ggK1Df_ggMultV0_two]
          simp
        have hget : (P.blk i).get j = (⟨⟨.A, 1, 2 * nf⟩, true⟩ : GGKacOrbit) :=
          ggK1Df_get_singleton hblk j
        rw [hget] at hqs
        exact Bool.noConfusion hqs
      · obtain ⟨hiff, hmodel⟩ := ggK1Df_om_two_dict_plus hK hnf P i hkind j
        refine ggK1Df_dict_of_iff_model hiff hmodel ?_
        intro hqs ho
        have hblk : P.blk i = [(⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit),
            ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩] := by
          rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega), ggK1Df_ggMultV0_two]
          simp
        have hget : (P.blk i).get j =
            (⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit) := by
          have hmem : (P.blk i).get j ∈
              [(⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit),
               (⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit)] := by
            rw [← hblk]; exact List.get_mem _ _
          simpa using hmem
        have hnf1 : nf = 1 := by
          rw [hget] at hqs
          by_contra h
          simp [h] at hqs
        have hp3 : p = 3 := by
          rcases hdvd with h | h
          · have : p = 1 := Nat.dvd_one.mp (by simpa [hnf1] using h)
            exact absurd this hp.ne_one
          · have : p ∣ 3 := by simpa [hnf1] using h
            exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp this
        obtain ⟨he⟩ := (P.fixed_model i true 2 hkind).2.2.2.1 rfl rfl j
        subst hp3
        exact ggK1Df_witness_subgroup he (ggK1Df_sl2_witness (K := K))
    · rcases eq_or_lt_of_le (show 3 ≤ m from hm3) with hm3' | hm4
      · subst hm3'
        haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
        obtain ⟨hiff, hmodel⟩ := ggK1Df_om_three_dict (hnf := hnf) (hK := hK) P i eps 3 hkind rfl j
        refine ggK1Df_dict_of_iff_model hiff hmodel ?_
        intro hqs _
        cases eps
        · have hblk : P.blk i = [(⟨⟨.twA, 3, nf⟩, true⟩ : GGKacOrbit)] := by
            rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega), ggK1Df_ggMultV0_three]
            simp
          have hget : (P.blk i).get j = (⟨⟨.twA, 3, nf⟩, true⟩ : GGKacOrbit) :=
            ggK1Df_get_singleton hblk j
          rw [hget] at hqs; exact Bool.noConfusion hqs
        · have hblk : P.blk i = [(⟨⟨.A, 3, nf⟩, true⟩ : GGKacOrbit)] := by
            rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega), ggK1Df_ggMultV0_three]
            simp
          have hget : (P.blk i).get j = (⟨⟨.A, 3, nf⟩, true⟩ : GGKacOrbit) :=
            ggK1Df_get_singleton hblk j
          rw [hget] at hqs; exact Bool.noConfusion hqs
      · obtain ⟨hiff, hmodel⟩ := ggK1Df_om_large_dict P i eps m hkind (by omega) j
        refine ggK1Df_dict_of_iff_model hiff hmodel ?_
        intro hqs _
        cases eps
        · have hblk : P.blk i = [(⟨⟨.twD, m, nf⟩, true⟩ : GGKacOrbit)] := by
            rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega),
              ggK1Df_ggMultV0_large (by omega)]
            simp
          have hget : (P.blk i).get j = (⟨⟨.twD, m, nf⟩, true⟩ : GGKacOrbit) :=
            ggK1Df_get_singleton hblk j
          rw [hget] at hqs; exact Bool.noConfusion hqs
        · have hblk : P.blk i = [(⟨⟨.D, m, nf⟩, true⟩ : GGKacOrbit)] := by
            rw [P.blk_eq i, hkind, ggK1Df_kindOrbits_om (by omega),
              ggK1Df_ggMultV0_large (by omega)]
            simp
          have hget : (P.blk i).get j = (⟨⟨.D, m, nf⟩, true⟩ : GGKacOrbit) :=
            ggK1Df_get_singleton hblk j
          rw [hget] at hqs; exact Bool.noConfusion hqs

private theorem ggK1Df_factor_dict {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (h1 : p ∣ 2 ^ nf - 1)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} {x : ↥(LargeEvenOmega Q)}
    (hxO : OddOrderIsometry Qf p (ggK1DLin (x : GL ι K)))
    (P : OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))
    (i : P.ι) (j : Fin (P.blk i).length) :
    let o := (P.blk i).get j
    let S := P.sub i j
    (o.qs = true ∧ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧ ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆) ∨
      (o.qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧
        (o ≠ ggK1DCo_dummyOrbit nf → ∃ t ∈ S, t ^ p = 1 ∧ ∃ a ∈ S, a * t ≠ t * a)) := by
  cases hk : P.kind i with
  | om eps m => exact ggK1Df_dict_om hp hp2 hnf hK hdvd P i eps m hk j
  | sl m => exact ggK1Df_dict_sl hp hp2 hnf hK h1 hxO P i m hk j
  | su m => exact ggK1Df_dict_su hp hp2 hnf hK hdvd P i m hk j

private lemma ggK1Df_hasOrbit_of_qs {nf : ℕ} {k : ggK1DCo_Kind} {o : GGKacOrbit}
    (ho : o ∈ ggK1DCo_kindOrbits nf k) (hqs : o.qs = true) :
    ggK1DCo_Kind.hasOrbit k = true := by
  cases k with
  | om eps m =>
      by_cases hm : m ≤ 1
      · rw [ggK1DCo_kindOrbits, if_pos hm, List.mem_singleton] at ho
        rw [ho] at hqs
        simp [ggK1DCo_dummyOrbit] at hqs
      · rw [ggK1DCo_Kind.hasOrbit, decide_eq_true_eq]; omega
  | sl m =>
      by_cases hm : m ≤ 1
      · rw [ggK1DCo_kindOrbits, if_pos hm, List.mem_singleton] at ho
        rw [ho] at hqs
        simp [ggK1DCo_dummyOrbit] at hqs
      · rw [ggK1DCo_Kind.hasOrbit, decide_eq_true_eq]; omega
  | su m =>
      by_cases hm : m ≤ 1
      · rw [ggK1DCo_kindOrbits, if_pos hm, List.mem_singleton] at ho
        rw [ho] at hqs
        simp [ggK1DCo_dummyOrbit] at hqs
      · rw [ggK1DCo_Kind.hasOrbit, decide_eq_true_eq]; omega

private lemma ggK1Df_dummy_not_mem_kindOrbits {nf : ℕ} {k : ggK1DCo_Kind}
    (hhas : ggK1DCo_Kind.hasOrbit k = true) :
    ggK1DCo_dummyOrbit nf ∉ ggK1DCo_kindOrbits nf k := by
  cases k with
  | om eps m =>
      rw [ggK1DCo_Kind.hasOrbit, decide_eq_true_eq] at hhas
      rw [ggK1DCo_kindOrbits, if_neg (by omega : ¬ m ≤ 1)]
      rcases m with _ | _ | _ | _ | k <;> cases eps <;>
        simp [ggMultV0, ggK1DCo_dummyOrbit]
  | sl m =>
      rw [ggK1DCo_Kind.hasOrbit, decide_eq_true_eq] at hhas
      rw [ggK1DCo_kindOrbits, if_neg (by omega : ¬ m ≤ 1)]
      rcases m with _ | _ | k <;> simp [ggMultBlockA, ggK1DCo_dummyOrbit]
  | su m =>
      rw [ggK1DCo_Kind.hasOrbit, decide_eq_true_eq] at hhas
      rw [ggK1DCo_kindOrbits, if_neg (by omega : ¬ m ≤ 1)]
      rcases m with _ | _ | k <;>
        simp only [ggMultBlockA, ggK1DCo_dummyOrbit]
      all_goals split_ifs <;> simp_all

private lemma ggK1Df_mem_datum {p nf d : ℕ} {tw : Bool} {m : List ℕ} {k : ggK1DCo_Kind}
    {o : GGKacOrbit} (hk : k ∈ ggK1DCo_expectedKindList p nf d tw m)
    (ho : o ∈ ggK1DCo_kindOrbits nf k) (hqs : o.qs = true) :
    o ∈ (ggMultDatumD p nf d tw m).orbits := by
  have hhas := ggK1Df_hasOrbit_of_qs ho hqs
  have hmem : o ∈ ggK1DCo_expectedOrbits p nf d tw m := by
    rw [ggK1DCo_expectedOrbits, List.mem_flatten]
    refine ⟨ggK1DCo_kindOrbits nf k, ?_, ho⟩
    rw [List.mem_map]
    exact ⟨k, List.mem_filter.mpr ⟨hk, hhas⟩, rfl⟩
  rwa [ggK1DCo_kindOrbit_multiset] at hmem

private lemma ggK1Df_exists_kind_of_mem_expectedOrbits {p nf d : ℕ} {tw : Bool} {m : List ℕ}
    {o : GGKacOrbit} (ho : o ∈ ggK1DCo_expectedOrbits p nf d tw m) :
    ∃ k ∈ ggK1DCo_expectedKindList p nf d tw m,
      ggK1DCo_Kind.hasOrbit k = true ∧ o ∈ ggK1DCo_kindOrbits nf k := by
  rw [ggK1DCo_expectedOrbits, List.mem_flatten] at ho
  obtain ⟨l, hl, hol⟩ := ho
  rw [List.mem_map] at hl
  obtain ⟨k, hk, rfl⟩ := hl
  exact ⟨k, (List.mem_filter.mp hk).1, (List.mem_filter.mp hk).2, hol⟩

private lemma ggK1Df_exists_pos {p nf d : ℕ} {tw : Bool} {m : List ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι] {kind : ι → ggK1DCo_Kind} {o : GGKacOrbit}
    (hmult : (Finset.univ : Finset ι).val.map kind = ggK1DCo_expectedKinds p nf d tw m)
    (ho : o ∈ (ggMultDatumD p nf d tw m).orbits) :
    ∃ q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length,
      (ggK1DCo_kindOrbits nf (kind q.1)).get q.2 = o := by
  have ho' : o ∈ ggK1DCo_expectedOrbits p nf d tw m := by
    rwa [ggK1DCo_kindOrbit_multiset]
  obtain ⟨k, hk, _hhas, hok⟩ := ggK1Df_exists_kind_of_mem_expectedOrbits ho'
  have hkmem : k ∈ (Finset.univ : Finset ι).val.map kind := by
    rw [hmult]; exact Multiset.mem_coe.mpr hk
  obtain ⟨i, _, hik⟩ := Multiset.mem_map.mp hkmem
  rw [← hik] at hok
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hok
  exact ⟨⟨i, j⟩, hj⟩

private lemma ggK1Df_dummy_not_mem_datum {p nf d : ℕ} {tw : Bool} {m : List ℕ} :
    ggK1DCo_dummyOrbit nf ∉ (ggMultDatumD p nf d tw m).orbits := by
  intro h
  rw [← ggK1DCo_kindOrbit_multiset] at h
  obtain ⟨k, _hk, hhas, hok⟩ := ggK1Df_exists_kind_of_mem_expectedOrbits h
  exact ggK1Df_dummy_not_mem_kindOrbits hhas hok

private theorem ggK1Df_fields_of_dict {p nf d r : ℕ} {tw : Bool} {m : List ℕ}
    {K : Type} [Field K] [Finite K]
    {ιQ : Type} [Fintype ιQ] [DecidableEq ιQ] {Q : (ιQ → K) → K}
    {x : ↥(LargeEvenOmega Q)}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (hp : p.Prime) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (kind : ι → ggK1DCo_Kind)
    (A : (i : ι) → Fin (ggK1DCo_kindOrbits nf (kind i)).length →
      Subgroup (LargeEvenProj (LargeEvenOmega Q)))
    (hkind_multiset : (Finset.univ : Finset ι).val.map kind =
      ggK1DCo_expectedKinds p nf d tw m)
    (hdict : ∀ q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length,
      let o := (ggK1DCo_kindOrbits nf (kind q.1)).get q.2
      let S := A q.1 q.2
      (o.qs = true ∧ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧ ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆) ∨
        (o.qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧
          (o ≠ ggK1DCo_dummyOrbit nf → ∃ t ∈ S, t ^ p = 1 ∧ ∃ a ∈ S, a * t ≠ t * a))) :
    (∀ (q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length),
        CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆ →
        (ggK1DCo_kindOrbits nf (kind q.1)).get q.2 ∈ (ggMultDatumD p nf d tw m).orbits) ∧
    (∀ (q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length),
        CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆ →
        ((ggK1DCo_kindOrbits nf (kind q.1)).get q.2).qs = true) ∧
    (∀ (q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length)
        (hq : CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆),
        GGHasLabel ((ggK1DCo_kindOrbits nf (kind q.1)).get q.2).lab
          (↥⁅A q.1 q.2, A q.1 q.2⁆ ⧸ Subgroup.center ↥⁅A q.1 q.2, A q.1 q.2⁆)) ∧
    (∀ o ∈ (ggMultDatumD p nf d tw m).orbits, o.qs = true →
        ∃ (q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length),
          CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆ ∧
          (ggK1DCo_kindOrbits nf (kind q.1)).get q.2 = o) ∧
    (∃ g : Subtype (fun q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length =>
          CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆) ≃
        {k : Fin (ggMultDatumD p nf d tw m).orbits.length //
          ((ggMultDatumD p nf d tw m).orbits.get k).qs = true},
      ∀ (q : Subtype (fun q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length =>
          CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆)),
        (ggMultDatumD p nf d tw m).orbits.get (g q).1 =
        (ggK1DCo_kindOrbits nf (kind q.1.1)).get q.1.2) ∧
    (∀ o ∈ (ggMultDatumD p nf d tw m).orbits, o.qs = false →
        ∃ (q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length),
          (ggK1DCo_kindOrbits nf (kind q.1)).get q.2 = o ∧
          ∃ t ∈ A q.1 q.2, t ^ p = 1 ∧ ∃ a ∈ A q.1 q.2, a * t ≠ t * a) := by
  obtain ⟨g, hg⟩ := ggK1DCo_pos_equiv (nf := nf) kind
    (ggK1DCo_expectedKindList p nf d tw m) (ggMultDatumD p nf d tw m).orbits
    hkind_multiset (ggK1DCo_kindOrbit_multiset p nf d tw m)
  have hiff : ∀ q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length,
      CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆ ↔
        ((ggK1DCo_kindOrbits nf (kind q.1)).get q.2).qs = true := by
    intro q
    rcases hdict q with ⟨hqs, hq, _⟩ | ⟨hqs, hnq, _⟩
    · exact ⟨fun _ => hqs, fun _ => hq⟩
    · refine ⟨fun h => absurd h hnq, fun h => ?_⟩
      rw [hqs] at h
      exact (Bool.false_eq_true.mp h).elim
  have hkind_mem : ∀ q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length,
      kind q.1 ∈ ggK1DCo_expectedKindList p nf d tw m := by
    intro q
    have : kind q.1 ∈ (Finset.univ : Finset ι).val.map kind :=
      Multiset.mem_map.mpr ⟨q.1, Finset.mem_univ _, rfl⟩
    rw [hkind_multiset] at this
    exact Multiset.mem_coe.mp this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hqs : ((ggK1DCo_kindOrbits nf (kind q.1)).get q.2).qs = true := (hiff q).mp hq
    exact ggK1Df_mem_datum (hkind_mem q) (List.get_mem _ _) hqs
  · intro q hq
    exact (hiff q).mp hq
  · intro q hq
    have hqs : ((ggK1DCo_kindOrbits nf (kind q.1)).get q.2).qs = true := (hiff q).mp hq
    rcases hdict q with ⟨_, hq', hm⟩ | ⟨_, hnq, _⟩
    · exact ggK1DCo_orbit_label hnf hK
        (ggK1DCo_kindOrbits_n nf (kind q.1) (List.get_mem _ _))
        (ggK1DCo_kindOrbits_rank nf (kind q.1) (List.get_mem _ _) hqs)
        hqs ⁅A q.1 q.2, A q.1 q.2⁆ hq' hm
    · exact absurd hq hnq
  · intro o ho hqs
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp ho
    let k' : {k : Fin (ggMultDatumD p nf d tw m).orbits.length //
        ((ggMultDatumD p nf d tw m).orbits.get k).qs = true} :=
      ⟨k, by rw [hk]; exact hqs⟩
    refine ⟨(g.symm k').1, ?_, ?_⟩
    · exact (hiff (g.symm k').1).mpr (g.symm k').2
    · have := hg (g.symm k')
      rw [Equiv.apply_symm_apply] at this
      exact this.symm.trans hk
  · let e1 : Subtype (fun q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length =>
        CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆) ≃
      Subtype (fun q : Σ i : ι, Fin (ggK1DCo_kindOrbits nf (kind i)).length =>
        ((ggK1DCo_kindOrbits nf (kind q.1)).get q.2).qs = true) :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun q => hiff q)
    exact ⟨e1.trans g, fun q => hg (e1 q)⟩
  · intro o ho hqs
    obtain ⟨q, hqo⟩ := ggK1Df_exists_pos hkind_multiset ho
    have ho_ne : o ≠ ggK1DCo_dummyOrbit nf := by
      intro h; exact ggK1Df_dummy_not_mem_datum (h ▸ ho)
    rcases hdict q with ⟨hqsT, _, _⟩ | ⟨_, _, hwit⟩
    · exfalso
      rw [hqo, hqs] at hqsT
      exact Bool.noConfusion hqsT
    · exact ⟨q, hqo, hwit (by rw [hqo]; exact ho_ne)⟩

theorem ggK1Df_family_of_orthBlocks {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf)
    (tw : Bool) {Q : (ι → K) → K} {Qf : QuadraticForm K (ι → K)} (hQ : Q = ⇑Qf)
    {x : ↥(LargeEvenOmega Q)} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL ι K) m) (hx : x ^ p = 1)
    (hxO : OddOrderIsometry Qf p (ggK1DLin (x : GL ι K)))
    (hscal : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥)
    (heps0 : CFSG.GroupTheory.WeirSylow.IsPlusType
        (Qf.restrict (primaryComponent (ggK1DLin (x : GL ι K)).toLinearMap (X - 1))) ↔
      ggMultEps0 p d tw m = true)
    (hob : Nonempty (OrthPrimaryBlocks K Qf nf p (ggK1DLin (x : GL ι K)))) :

    Nonempty (ggK1DCo_Family p nf d tw r m K Q x) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  obtain ⟨P⟩ := hob
  obtain ⟨AP, hcommP, hjoinP, hindepP, htameP, hisoP⟩ := ggK1Df_transport hQ hscal P
  obtain ⟨Rep, e, hRep, hkind⟩ := P.rep
  let xL : (ι → K) ≃ₗ[K] (ι → K) := ggK1DLin (x : GL ι K)
  let W : Submodule K (ι → K) := primaryComponent xL.toLinearMap (X - 1)
  let headKind : ggK1DCo_Kind := ggK1DCo_Kind.om
    (if CFSG.GroupTheory.WeirSylow.IsPlusType (Qf.restrict W) then true else false)
    (Module.finrank K W / 2)
  have heps0' : (if CFSG.GroupTheory.WeirSylow.IsPlusType (Qf.restrict W) then true else false) =
      ggMultEps0 p d tw m := by
    by_cases hp_ : CFSG.GroupTheory.WeirSylow.IsPlusType (Qf.restrict W)
    · simp [hp_, heps0.mp hp_]
    · have hne : ggMultEps0 p d tw m ≠ true := fun h => hp_ (heps0.mpr h)
      cases hb : ggMultEps0 p d tw m
      · rw [if_neg hp_]
      · exact absurd hb hne
  have hhead : headKind = ggK1DCo_Kind.om (ggMultEps0 p d tw m) (m.headD 0) := by
    dsimp only [headKind, W, xL]
    rw [heps0', hm.head_eq]
    rfl
  let D : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) :=
    ⁅TauCeti.QuadraticMap.orthogonalGroup Qf, TauCeti.QuadraticMap.orthogonalGroup Qf⁆
  have hsubD : ∀ q : Σ i, Fin (P.blk i).length, P.sub q.1 q.2 ≤ D := fun q =>
    (le_iSup (fun q : Σ i, Fin (P.blk i).length => P.sub q.1 q.2) q).trans
      (P.hjoin.le.trans inf_le_right)
  have hcomm_sub : ∀ q q' : Σ i, Fin (P.blk i).length, q ≠ q' →
      ∀ a ∈ P.sub q.1 q.2, ∀ b ∈ P.sub q'.1 q'.2, Commute a b := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hne a ha b hb
    by_cases hi : i = i'
    · subst hi
      exact P.hcomm_sub i j j' (fun h => hne (by rw [h])) a ha b hb
    · exact P.hcomm i i' hi a (P.hsub_le i j ha) b (P.hsub_le i' j' hb)
  have hkHead : ∀ i : P.ι, (e i : K[X]) = X - 1 → P.kind i = headKind := by
    intro i hi
    rw [hkind i, if_pos hi]
  let headIdx : Option {i : P.ι // (e i : K[X]) = X - 1} :=
    if h : ∃ i : P.ι, (e i : K[X]) = X - 1 then
      some ⟨Classical.choose h, Classical.choose_spec h⟩
    else none
  rcases hm.blocks_eq with ⟨hd1, P₀, hP₀, hmult⟩ | ⟨hd2, hmult⟩
  · let tailSet : Finset K[X] := P₀
    let f : ℕ → ggK1DCo_Kind := fun j => ggK1DCo_Kind.sl j
    let kfun : K[X] → ggK1DCo_Kind := fun t => f (primaryMultiplicity xL.toLinearMap t)
    let blkIdx : Type := ↥tailSet ⊕ Unit
    let kind : blkIdx → ggK1DCo_Kind
      | Sum.inl t => kfun t.1
      | Sum.inr _ => headKind
    let blk : blkIdx → List GGKacOrbit := fun i => ggK1DCo_kindOrbits nf (kind i)
    let φ : ↥tailSet → P.ι := fun t =>
      e.symm ⟨Classical.choose (hRep.2 t.1 (hP₀.1 t.1 t.2).1),
        (Classical.choose_spec (hRep.2 t.1 (hP₀.1 t.1 t.2).1)).1.1⟩
    have hφ : ∀ t : ↥tailSet, (e (φ t) : K[X]) ∈ Rep ∧
        (t.1 = e (φ t) ∨ t.1 = reciprocalPolynomial (e (φ t))) := by
      intro t
      simpa [φ] using (Classical.choose_spec (hRep.2 t.1 (hP₀.1 t.1 t.2).1)).1
    have hkφ : ∀ t : ↥tailSet, P.kind (φ t) = kfun t.1 := by
      intro t
      have ht : t.1 ∈ primaryFactors xL.toLinearMap := (hP₀.1 t.1 t.2).1
      have hpair : t.1 ≠ reciprocalPolynomial t.1 := (hP₀.1 t.1 t.2).2
      have hne : t.1 ≠ X - 1 := fun h => hpair (by rw [h,
          CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one])
      obtain ⟨hrmem, hrcases⟩ := hφ t
      have hpm := (hxO.pairedModel ht hne hpair).2.1
      have hrX : ¬ (e (φ t) : K[X]) = X - 1 := by
        rintro hX
        rcases hrcases with h | h
        · exact hne (h.trans hX)
        · rw [hX, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one] at h
          exact hne h
      have hrpair : ¬ reciprocalPolynomial (e (φ t) : K[X]) = e (φ t) := by
        rintro hp_
        rcases hrcases with h | h
        · exact hpair (by rw [h]; exact hp_.symm)
        · have h2 := congrArg reciprocalPolynomial h
          rw [hxO.reciprocal_reciprocal_eq (h := (e (φ t) : K[X])) (hRep.1 hrmem)] at h2
          have hr : (e (φ t) : K[X]) = reciprocalPolynomial t.1 := h2.symm
          rw [hr] at hp_
          exact hpair (calc t.1 = reciprocalPolynomial (reciprocalPolynomial t.1) :=
              (hxO.reciprocal_reciprocal_eq (h := t.1) ht).symm
            _ = reciprocalPolynomial t.1 := hp_)
      have hmult : primaryMultiplicity xL.toLinearMap (e (φ t)) =
          primaryMultiplicity xL.toLinearMap t.1 := by
        rcases hrcases with h | h
        · rw [← h]
        · have h2 := congrArg reciprocalPolynomial h
          rw [hxO.reciprocal_reciprocal_eq (h := (e (φ t) : K[X])) (hRep.1 hrmem)] at h2
          have hr : (e (φ t) : K[X]) = reciprocalPolynomial t.1 := h2.symm
          rw [hr, hpm]
      rw [hkind (φ t), if_neg hrX, if_neg hrpair, hmult]
    have hφ_inj : Function.Injective φ := by
      intro t t' h
      have ht := (hφ t).2
      have ht' := (hφ t').2
      have heq : (e (φ t) : K[X]) = e (φ t') := by rw [h]
      have htP : t.1 ∈ P₀ := t.2
      have ht'P : t'.1 ∈ P₀ := t'.2
      rcases ht with h1 | h1 <;> rcases ht' with h2 | h2
      · exact Subtype.ext (h1.trans (heq.trans h2.symm))
      · exfalso
        have hrec : reciprocalPolynomial t.1 ∉ P₀ := hP₀.2.2 t htP
        apply hrec
        have hthis : reciprocalPolynomial t.1 = t'.1 := by rw [h1, heq]; exact h2.symm
        rw [hthis]; exact ht'P
      · exfalso
        have hrec : reciprocalPolynomial t'.1 ∉ P₀ := hP₀.2.2 t' ht'P
        apply hrec
        have hthis : reciprocalPolynomial t'.1 = t.1 := by rw [h2, ← heq]; exact h1.symm
        rw [hthis]; exact htP
      · exact Subtype.ext (h1.trans (by rw [heq]; exact h2.symm))
    have hφ_ne_head : ∀ (hd : {i : P.ι // (e i : K[X]) = X - 1}) (t : ↥tailSet),
        φ t ≠ hd.1 := by
      intro hd t h
      have hne : t.1 ≠ X - 1 := fun hX =>
        (hP₀.1 t.1 t.2).2 (by rw [hX,
            CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one])
      have hX : (e (φ t) : K[X]) = X - 1 := by rw [h, hd.2]
      rcases (hφ t).2 with h1 | h1
      · exact hne (h1.trans hX)
      · rw [hX, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one] at h1
        exact hne h1
    let Φ : (Σ i : blkIdx, Fin (blk i).length) → Option (Σ i : P.ι, Fin (P.blk i).length)
      | ⟨Sum.inl t, j⟩ => some ⟨φ t, Fin.cast (by rw [P.blk_eq (φ t), hkφ t]) j⟩
      | ⟨Sum.inr _, j⟩ => headIdx.map (fun hd =>
          ⟨hd.1, Fin.cast (by rw [P.blk_eq hd.1, hkHead hd.1 hd.2]) j⟩)
    let A : (i : blkIdx) → Fin (ggK1DCo_kindOrbits nf (kind i)).length → Subgroup (LargeEvenProj
        (LargeEvenOmega Q)) :=
      fun i j => (Φ ⟨i, j⟩).elim ⊥ AP
    have hΦ_inj : ∀ q q' a, Φ q = some a → Φ q' = some a → q = q' := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ a hq hq'
      rcases i with t | u <;> rcases i' with t' | u'
      · simp only [Φ] at hq hq'
        obtain ⟨ha, hb⟩ := Sigma.mk.inj_iff.mp (Option.some.inj (hq.trans hq'.symm))
        obtain rfl : t = t' := hφ_inj ha
        have hb' : j = j' := Fin.cast_injective _ (eq_of_heq hb)
        subst hb'
        rfl
      · simp only [Φ] at hq hq'
        cases hh : headIdx with
        | none => simp only [hh, Option.map_none] at hq'; exact absurd hq' (by simp)
        | some hd =>
          simp only [hh, Option.map_some] at hq'
          obtain ⟨ha, _⟩ := Sigma.mk.inj_iff.mp (Option.some.inj (hq.trans hq'.symm))
          exact absurd ha (hφ_ne_head hd t)
      · simp only [Φ] at hq hq'
        cases hh : headIdx with
        | none => simp only [hh, Option.map_none] at hq; exact absurd hq (by simp)
        | some hd =>
          simp only [hh, Option.map_some] at hq
          obtain ⟨ha, _⟩ := Sigma.mk.inj_iff.mp (Option.some.inj (hq.trans hq'.symm))
          exact absurd ha.symm (hφ_ne_head hd t')
      · simp only [Φ] at hq hq'
        cases hh : headIdx with
        | none => simp only [hh, Option.map_none] at hq; exact absurd hq (by simp)
        | some hd =>
          simp only [hh, Option.map_some] at hq hq'
          obtain ⟨_, hb⟩ := Sigma.mk.inj_iff.mp (Option.some.inj (hq.trans hq'.symm))
          have hb' : j = j' := Fin.cast_injective _ (eq_of_heq hb)
          subst hb'
          rfl
    have hnot_self : ∀ i : P.ι, (e i : K[X]) ≠ X - 1 →
        reciprocalPolynomial (e i : K[X]) ≠ (e i : K[X]) := by
      intro i hne
      have hmd : ggMultOrd p nf = 1 := by rw [← hd, hd1]
      have h1 : p ∣ 2 ^ nf - 1 := by
        by_contra h1
        rw [ggMultOrd, if_neg h1] at hmd
        split at hmd <;> omega
      have heipf : (e i : K[X]) ∈ primaryFactors (ggK1DLin (x : GL ι K)).toLinearMap :=
        hRep.1 (e i).2
      have hirr : Irreducible (e i : K[X]) := irreducible_of_mem_primaryFactors heipf
      have hmon : (e i : K[X]).Monic := monic_of_mem_primaryFactors heipf
      have hdvd1 : (e i : K[X]) ∣ X ^ p - 1 := hxO.dvd_X_pow_sub_one heipf
      have hdvd2 : (e i : K[X]) ∣ cyclotomic p K :=
        ggK1Df_dvd_cyclotomic hp hirr hmon hdvd1 hne
      have hdeg : (e i : K[X]).natDegree = 1 :=
        ggK1Df_natDegree_eq_one hp (ggK1Df_cast_ne_zero hp hp2 hK) h1 hK hirr hdvd2
      have hord : orderOf (AdjoinRoot.root (e i : K[X])) = p := P.nontrivial (e i) heipf hne
      haveI : Fact (Irreducible (e i : K[X])) := ⟨hirr⟩
      exact ggK1Df_not_selfDual_of_degree_one hp hp2 hmon hdeg hord
    have hΦ_cover : ∀ a : Σ i : P.ι, Fin (P.blk i).length, ∃ q, Φ q = some a := by
      rintro ⟨i, j⟩
      by_cases hXi : (e i : K[X]) = X - 1
      · have hex : ∃ i : P.ι, (e i : K[X]) = X - 1 := ⟨i, hXi⟩
        let hd : {i : P.ι // (e i : K[X]) = X - 1} :=
          ⟨Classical.choose hex, Classical.choose_spec hex⟩
        have hhd : headIdx = some hd := by dsimp only [headIdx]; rw [dif_pos hex]
        have hdii : hd.1 = i := e.injective (Subtype.ext (hd.2.trans hXi.symm))
        have hblk : (P.blk hd.1).length = (P.blk i).length := congrArg (fun i => (P.blk i).length)
            hdii
        refine ⟨⟨Sum.inr (), Fin.cast (by rw [P.blk_eq hd.1, hkHead hd.1 hd.2] :
              (blk (Sum.inr ())).length = (P.blk hd.1).length).symm
            (Fin.cast hblk.symm j)⟩, ?_⟩
        simp only [Φ, hhd, Option.map_some, Option.some.injEq, Sigma.mk.injEq]
        exact ⟨hdii, (Fin.heq_ext_iff hblk).mpr rfl⟩
      · have hne : reciprocalPolynomial (e i : K[X]) ≠ (e i : K[X]) := hnot_self i hXi
        have hprime : (e i : K[X]) ∈ primaryFactors (ggK1DLin (x : GL ι K)).toLinearMap :=
          hRep.1 (e i).2
        obtain ⟨r, ⟨_, hrorb⟩, huniq⟩ := hRep.2 (e i) hprime
        have hrei : r = e i := (huniq (e i) ⟨(e i).2, Or.inl rfl⟩).symm
        rcases hP₀.2.1 (e i) hprime (fun h => hne h.symm) with hmem | hmem
        · let t : ↥tailSet := ⟨e i, hmem⟩
          have ht : t.1 = (e i : K[X]) := rfl
          have heφ : (e (φ t) : K[X]) = e i := by
            have hdij : (e i : K[X]) = e (φ t) ∨
                (e i : K[X]) = reciprocalPolynomial (e (φ t)) := by
              rcases (hφ t).2 with h | h
              · exact Or.inl (ht.symm.trans h)
              · exact Or.inr (ht.symm.trans h)
            exact (huniq (e (φ t)) ⟨(hφ t).1, hdij⟩).trans hrei
          have hφi : φ t = i := e.injective (Subtype.ext heφ)
          have hblk : (P.blk (φ t)).length = (P.blk i).length := congrArg (fun i => (P.blk
              i).length) hφi
          refine ⟨⟨Sum.inl t, Fin.cast (by rw [P.blk_eq (φ t), hkφ t] :
              (blk (Sum.inl t)).length = (P.blk (φ t)).length).symm
              (Fin.cast hblk.symm j)⟩, ?_⟩
          simp only [Φ, Option.some.injEq, Sigma.mk.injEq]
          exact ⟨hφi, (Fin.heq_ext_iff hblk).mpr rfl⟩
        · let t : ↥tailSet := ⟨reciprocalPolynomial (e i), hmem⟩
          have ht : t.1 = reciprocalPolynomial (e i : K[X]) := rfl
          have hφtpf : (e (φ t) : K[X]) ∈
              primaryFactors (ggK1DLin (x : GL ι K)).toLinearMap := hRep.1 (hφ t).1
          have heφ : (e (φ t) : K[X]) = e i := by
            have hdij : (e i : K[X]) = e (φ t) ∨
                (e i : K[X]) = reciprocalPolynomial (e (φ t)) := by
              rcases (hφ t).2 with h | h
              · refine Or.inr ?_
                have h2 : (e (φ t) : K[X]) = reciprocalPolynomial (e i : K[X]) := h.symm.trans ht
                rw [h2, hxO.reciprocal_reciprocal_eq (h := (e i : K[X])) hprime]
              · refine Or.inl ?_
                have h2 : reciprocalPolynomial (e (φ t) : K[X]) =
                    reciprocalPolynomial (e i : K[X]) := h.symm.trans ht
                have h3 := congrArg reciprocalPolynomial h2
                rw [hxO.reciprocal_reciprocal_eq (h := (e (φ t) : K[X])) hφtpf,
                  hxO.reciprocal_reciprocal_eq (h := (e i : K[X])) hprime] at h3
                exact h3.symm
            exact (huniq (e (φ t)) ⟨(hφ t).1, hdij⟩).trans hrei
          have hφi : φ t = i := e.injective (Subtype.ext heφ)
          have hblk : (P.blk (φ t)).length = (P.blk i).length := congrArg (fun i => (P.blk
              i).length) hφi
          refine ⟨⟨Sum.inl t, Fin.cast (by rw [P.blk_eq (φ t), hkφ t] :
              (blk (Sum.inl t)).length = (P.blk (φ t)).length).symm
              (Fin.cast hblk.symm j)⟩, ?_⟩
          simp only [Φ, Option.some.injEq, Sigma.mk.injEq]
          exact ⟨hφi, (Fin.heq_ext_iff hblk).mpr rfl⟩
    have hkind_multiset : (Finset.univ : Finset blkIdx).val.map kind =
        ggK1DCo_expectedKinds p nf d tw m := by
      have hsum : (Finset.univ : Finset (↥tailSet ⊕ Unit)) =
          (Finset.univ : Finset ↥tailSet).disjSum (Finset.univ : Finset Unit) :=
        (Finset.univ_disjSum_univ (α := ↥tailSet) (β := Unit)).symm
      rw [hsum, Finset.val_disjSum, Multiset.map_disjSum]
      rw [show Multiset.map (fun x : ↥tailSet => kind (Sum.inl x))
            (Finset.univ : Finset ↥tailSet).val =
          (Finset.univ : Finset ↥tailSet).val.map (fun t => kfun t.1) from rfl]
      rw [ggK1Df_tail_plumbing xL.toLinearMap m tailSet kfun f hmult (fun t => rfl)]
      rw [show Multiset.map (fun x : Unit => kind (Sum.inr x))
            (Finset.univ : Finset Unit).val = {headKind} from by simp [kind]]
      rw [ggK1DCo_expectedKinds, ggK1DCo_expectedKindList, ← hm.length_eq]
      rw [show (fun j => if d = 1 then ggK1DCo_Kind.sl (m.getD j 0)
            else ggK1DCo_Kind.su (m.getD j 0)) = (fun j => ggK1DCo_Kind.sl (m.getD j 0)) from by
        funext j; rw [if_pos hd1]]
      rw [ggK1CBl_tail_filter_map m (fun j => ggK1DCo_Kind.sl j)]
      rw [hhead, ← Multiset.coe_add, Multiset.coe_singleton, List.drop_one]
      exact Multiset.add_comm _ _
    have h1 : p ∣ 2 ^ nf - 1 := by
      have hmd : ggMultOrd p nf = 1 := by rw [← hd, hd1]
      by_contra h
      rw [ggMultOrd, if_neg h] at hmd
      split at hmd <;> omega
    have hdict : ∀ q : Σ i : blkIdx, Fin (ggK1DCo_kindOrbits nf (kind i)).length,
        let o := (ggK1DCo_kindOrbits nf (kind q.1)).get q.2
        let S := A q.1 q.2
        (o.qs = true ∧ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧ ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆) ∨
          (o.qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧
            (o ≠ ggK1DCo_dummyOrbit nf → ∃ t ∈ S, t ^ p = 1 ∧ ∃ a ∈ S, a * t ≠ t * a)) := by
      rintro ⟨i, j⟩
      rcases i with t | u
      · have ha : Φ ⟨Sum.inl t, j⟩ = some
            ⟨φ t, Fin.cast (by rw [P.blk_eq (φ t), hkφ t]) j⟩ := rfl
        have hA : A (Sum.inl t) j = AP
            ⟨φ t, Fin.cast (by rw [P.blk_eq (φ t), hkφ t]) j⟩ := by simp [A, ha]
        have hblk : blk (Sum.inl t) = P.blk (φ t) := by
          rw [P.blk_eq (φ t), hkφ t]
        have ho : (blk (Sum.inl t)).get j =
            (P.blk (φ t)).get (Fin.cast (by rw [P.blk_eq (φ t), hkφ t]) j) :=
          List.get_of_eq hblk j
        rw [hA, ho]
        exact ggK1Df_dict_transport (hisoP _).some.symm
          (ggK1Df_factor_dict hp hp2 hdvd hnf hK h1 hxO P (φ t) _)
      · cases hh : headIdx with
        | none =>
          have hA : A (Sum.inr u) j = ⊥ := by simp [A, Φ, hh]
          have hX1 : X - 1 ∉ primaryFactors xL.toLinearMap := by
            intro hmem
            obtain ⟨r, ⟨hrRep, hr⟩, _⟩ := hRep.2 (X - 1) hmem
            have hrX : r = X - 1 := by
              rcases hr with h | h
              · exact h.symm
              · have h2 := congrArg reciprocalPolynomial h
                rw [CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one] at h2
                rw [hxO.reciprocal_reciprocal_eq (h := r) (hRep.1 hrRep)] at h2
                exact h2.symm
            have hex : ∃ i, (e i : K[X]) = X - 1 :=
              ⟨e.symm ⟨r, hrRep⟩, by simp only [Equiv.apply_symm_apply]; exact hrX⟩
            have hsome : headIdx = some ⟨Classical.choose hex, Classical.choose_spec hex⟩ := by
              dsimp only [headIdx]; rw [dif_pos hex]
            rw [hsome] at hh
            cases hh
          have hWbot : W = ⊥ :=
            CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
              CFSG.RankThree.Classical.irreducible_X_sub_one
                  CFSG.RankThree.Classical.monic_X_sub_one hX1
          have hm0 : m.headD 0 = 0 := by
            rw [hm.head_eq]
            change Module.finrank K W / 2 = 0
            rw [hWbot, finrank_bot]
          have hblk : blk (Sum.inr u) = [ggK1DCo_dummyOrbit nf] := by
            dsimp only [blk, kind]
            rw [hhead, hm0]
            simp [ggK1DCo_kindOrbits]
          have hget : (blk (Sum.inr u)).get j = ggK1DCo_dummyOrbit nf :=
            ggK1Df_get_dummy hblk j
          refine Or.inr ⟨?_, ?_, ?_⟩
          · rw [hget]; rfl
          · rw [hA, Subgroup.commutator_bot_left]; exact ggK1Df_not_quasi_bot
          · intro ho; exact absurd hget ho
        | some hd =>
          have ha : Φ ⟨Sum.inr u, j⟩ = some
              ⟨hd.1, Fin.cast (by rw [P.blk_eq hd.1, hkHead hd.1 hd.2]) j⟩ := by
            simp [Φ, hh]
          have hA : A (Sum.inr u) j = AP
              ⟨hd.1, Fin.cast (by rw [P.blk_eq hd.1, hkHead hd.1 hd.2]) j⟩ := by
            simp [A, ha]
          have hblk : blk (Sum.inr u) = P.blk hd.1 := by
            rw [P.blk_eq hd.1, hkHead hd.1 hd.2]
          have ho : (blk (Sum.inr u)).get j =
              (P.blk hd.1).get (Fin.cast (by rw [P.blk_eq hd.1, hkHead hd.1 hd.2]) j) :=
            List.get_of_eq hblk j
          rw [hA, ho]
          exact ggK1Df_dict_transport (hisoP _).some.symm
            (ggK1Df_factor_dict hp hp2 hdvd hnf hK h1 hxO P hd.1 _)
    obtain ⟨hmem, hqs, hlab, hreal, hbij, hsolv⟩ :=
      @ggK1Df_fields_of_dict p nf d r tw m K _ _ ι _ _ Q x blkIdx _ _
        hp hnf hK kind A hkind_multiset hdict
    refine ⟨blkIdx, blk, kind, ?_, A, ?_, ?_, ?_, ?_, hkind_multiset,
      hmem, hqs, hlab, hreal, hbij, hsolv⟩
    · intro i; rfl
    · exact ggK1Df_commute_elim AP Φ hΦ_inj hcommP
    · change (⨆ q, (Φ q).elim ⊥ AP) =
        Subgroup.centralizer ({LargeEvenProjMk (LargeEvenOmega Q) x} :
          Set (LargeEvenProj (LargeEvenOmega Q)))
      rw [ggK1Df_iSup_elim AP Φ hΦ_cover, hjoinP]
    · exact ggK1Df_iSupIndep_elim AP Φ hΦ_inj hindepP
    · exact ggK1Df_tame_elim AP Φ htameP

  · let tailSet : Finset K[X] := ggK1DSelfDualFactors (x : GL ι K)
    let f : ℕ → ggK1DCo_Kind := fun j => ggK1DCo_Kind.su j
    let kfun : K[X] → ggK1DCo_Kind := fun t => f (primaryMultiplicity xL.toLinearMap t)
    let blkIdx : Type := ↥tailSet ⊕ Unit
    let kind : blkIdx → ggK1DCo_Kind
      | Sum.inl t => kfun t.1
      | Sum.inr _ => headKind
    let blk : blkIdx → List GGKacOrbit := fun i => ggK1DCo_kindOrbits nf (kind i)
    let φ : ↥tailSet → P.ι := fun t =>
      e.symm ⟨Classical.choose (hRep.2 t.1 (Finset.mem_filter.mp t.2).1),
        (Classical.choose_spec (hRep.2 t.1 (Finset.mem_filter.mp t.2).1)).1.1⟩
    have hφ : ∀ t : ↥tailSet, (e (φ t) : K[X]) ∈ Rep ∧
        (t.1 = e (φ t) ∨ t.1 = reciprocalPolynomial (e (φ t))) := by
      intro t
      simpa [φ] using (Classical.choose_spec (hRep.2 t.1 (Finset.mem_filter.mp t.2).1)).1
    have hkφ : ∀ t : ↥tailSet, P.kind (φ t) = kfun t.1 := by
      intro t
      have ht : t.1 ∈ primaryFactors xL.toLinearMap := (Finset.mem_filter.mp t.2).1
      have hne : t.1 ≠ X - 1 := (Finset.mem_filter.mp t.2).2
      have hpq : p ∣ Fintype.card K + 1 := by
        have hcard : Fintype.card K = 2 ^ nf := by rw [Fintype.card_eq_nat_card, hK]
        rw [hcard]
        have hd2' : ggMultOrd p nf = 2 := by rw [← hd]; exact hd2
        by_cases h1 : p ∣ 2 ^ nf - 1
        · rw [ggMultOrd, if_pos h1] at hd2'
          omega
        · by_cases h2 : p ∣ 2 ^ nf + 1
          · exact h2
          · rw [ggMultOrd, if_neg h1, if_neg h2] at hd2'
            omega
      have hpchar : p ≠ ringChar K := by
        rw [ringChar.eq K 2]
        exact hp2
      have hself : reciprocalPolynomial t.1 = t.1 :=
        ggK1CBl_ff_selfDual (K := K) hp hpchar hpq
          (irreducible_of_mem_primaryFactors ht) (monic_of_mem_primaryFactors ht)
          (hxO.dvd_X_pow_sub_one ht) hne
      obtain ⟨hrmem, hrcases⟩ := hφ t
      have hr : (e (φ t) : K[X]) = t.1 := by
        rcases hrcases with h | h
        · rw [← h]
        · have h2 := congrArg reciprocalPolynomial h
          rw [hxO.reciprocal_reciprocal_eq (h := (e (φ t) : K[X])) (hRep.1 hrmem)] at h2
          rw [hself] at h2
          exact h2.symm
      have hrX : ¬ (e (φ t) : K[X]) = X - 1 := by rw [hr]; exact hne
      have hrpair : reciprocalPolynomial (e (φ t) : K[X]) = e (φ t) := by rw [hr, hself]
      have hmult : primaryMultiplicity xL.toLinearMap (e (φ t)) =
          primaryMultiplicity xL.toLinearMap t.1 := by rw [hr]
      rw [hkind (φ t), if_neg hrX, if_pos hrpair, hmult]
    let Φ : (Σ i : blkIdx, Fin (blk i).length) → Option (Σ i : P.ι, Fin (P.blk i).length)
      | ⟨Sum.inl t, j⟩ => some ⟨φ t, Fin.cast (by rw [P.blk_eq (φ t), hkφ t]) j⟩
      | ⟨Sum.inr _, j⟩ => headIdx.map (fun hd =>
          ⟨hd.1, Fin.cast (by rw [P.blk_eq hd.1, hkHead hd.1 hd.2]) j⟩)
    let A : (i : blkIdx) → Fin (ggK1DCo_kindOrbits nf (kind i)).length → Subgroup (LargeEvenProj
        (LargeEvenOmega Q)) :=
      fun i j => (Φ ⟨i, j⟩).elim ⊥ AP
    have hφ_hr : ∀ t : ↥tailSet, (e (φ t) : K[X]) = t.1 := by
      intro t
      have ht : t.1 ∈ primaryFactors xL.toLinearMap := (Finset.mem_filter.mp t.2).1
      have hne : t.1 ≠ X - 1 := (Finset.mem_filter.mp t.2).2
      have hpq : p ∣ Fintype.card K + 1 := by
        have hcard : Fintype.card K = 2 ^ nf := by rw [Fintype.card_eq_nat_card, hK]
        rw [hcard]
        have hd2' : ggMultOrd p nf = 2 := by rw [← hd]; exact hd2
        by_cases h1 : p ∣ 2 ^ nf - 1
        · rw [ggMultOrd, if_pos h1] at hd2'; omega
        · by_cases h2 : p ∣ 2 ^ nf + 1
          · exact h2
          · rw [ggMultOrd, if_neg h1, if_neg h2] at hd2'; omega
      have hpchar : p ≠ ringChar K := by rw [ringChar.eq K 2]; exact hp2
      have hself : reciprocalPolynomial t.1 = t.1 :=
        ggK1CBl_ff_selfDual (K := K) hp hpchar hpq
          (irreducible_of_mem_primaryFactors ht) (monic_of_mem_primaryFactors ht)
          (hxO.dvd_X_pow_sub_one ht) hne
      obtain ⟨hrmem, hrcases⟩ := hφ t
      rcases hrcases with h | h
      · rw [← h]
      · have h2 := congrArg reciprocalPolynomial h
        rw [hxO.reciprocal_reciprocal_eq (h := (e (φ t) : K[X])) (hRep.1 hrmem)] at h2
        rw [hself] at h2
        exact h2.symm
    have hφ_inj2 : Function.Injective φ := by
      intro t t' h
      have heq : (e (φ t) : K[X]) = e (φ t') := by rw [h]
      exact Subtype.ext ((hφ_hr t).symm.trans (heq.trans (hφ_hr t')))
    have hφ_ne_head2 : ∀ (hd : {i : P.ι // (e i : K[X]) = X - 1}) (t : ↥tailSet),
        φ t ≠ hd.1 := by
      intro hd t hh
      have hne : t.1 ≠ X - 1 := (Finset.mem_filter.mp t.2).2
      have hX : (e (φ t) : K[X]) = X - 1 := by rw [hh, hd.2]
      rw [hφ_hr t] at hX
      exact hne hX
    have hΦ_inj2 : ∀ q q' a, Φ q = some a → Φ q' = some a → q = q' := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ a hq hq'
      rcases i with t | u <;> rcases i' with t' | u'
      · simp only [Φ] at hq hq'
        obtain ⟨ha, hb⟩ := Sigma.mk.inj_iff.mp (Option.some.inj (hq.trans hq'.symm))
        obtain rfl : t = t' := hφ_inj2 ha
        have hb' : j = j' := Fin.cast_injective _ (eq_of_heq hb)
        subst hb'; rfl
      · simp only [Φ] at hq hq'
        cases hh : headIdx with
        | none => simp only [hh, Option.map_none] at hq'; exact absurd hq' (by simp)
        | some hd =>
          simp only [hh, Option.map_some] at hq'
          obtain ⟨ha, _⟩ := Sigma.mk.inj_iff.mp (Option.some.inj (hq.trans hq'.symm))
          exact absurd ha (hφ_ne_head2 hd t)
      · simp only [Φ] at hq hq'
        cases hh : headIdx with
        | none => simp only [hh, Option.map_none] at hq; exact absurd hq (by simp)
        | some hd =>
          simp only [hh, Option.map_some] at hq
          obtain ⟨ha, _⟩ := Sigma.mk.inj_iff.mp (Option.some.inj (hq.trans hq'.symm))
          exact absurd ha.symm (hφ_ne_head2 hd t')
      · simp only [Φ] at hq hq'
        cases hh : headIdx with
        | none => simp only [hh, Option.map_none] at hq; exact absurd hq (by simp)
        | some hd =>
          simp only [hh, Option.map_some] at hq hq'
          obtain ⟨_, hb⟩ := Sigma.mk.inj_iff.mp (Option.some.inj (hq.trans hq'.symm))
          have hb' : j = j' := Fin.cast_injective _ (eq_of_heq hb)
          subst hb'; rfl
    have hΦ_cover2 : ∀ a : Σ i : P.ι, Fin (P.blk i).length, ∃ q, Φ q = some a := by
      rintro ⟨i, j⟩
      by_cases hXi : (e i : K[X]) = X - 1
      · have hex : ∃ i : P.ι, (e i : K[X]) = X - 1 := ⟨i, hXi⟩
        let hd : {i : P.ι // (e i : K[X]) = X - 1} :=
          ⟨Classical.choose hex, Classical.choose_spec hex⟩
        have hhd : headIdx = some hd := by dsimp only [headIdx]; rw [dif_pos hex]
        have hdii : hd.1 = i := e.injective (Subtype.ext (hd.2.trans hXi.symm))
        have hblk : (P.blk hd.1).length = (P.blk i).length := congrArg (fun i => (P.blk i).length)
            hdii
        refine ⟨⟨Sum.inr (), Fin.cast (by rw [P.blk_eq hd.1, hkHead hd.1 hd.2] :
              (blk (Sum.inr ())).length = (P.blk hd.1).length).symm
            (Fin.cast hblk.symm j)⟩, ?_⟩
        simp only [Φ, hhd, Option.map_some, Option.some.injEq, Sigma.mk.injEq]
        exact ⟨hdii, (Fin.heq_ext_iff hblk).mpr rfl⟩
      · let t : ↥tailSet := ⟨e i, Finset.mem_filter.mpr ⟨hRep.1 (e i).2, hXi⟩⟩
        have hφi : φ t = i := e.injective (Subtype.ext (hφ_hr t))
        have hblk : (P.blk (φ t)).length = (P.blk i).length := congrArg (fun i => (P.blk i).length)
            hφi
        refine ⟨⟨Sum.inl t, Fin.cast (by rw [P.blk_eq (φ t), hkφ t] :
              (blk (Sum.inl t)).length = (P.blk (φ t)).length).symm
            (Fin.cast hblk.symm j)⟩, ?_⟩
        simp only [Φ, Option.some.injEq, Sigma.mk.injEq]
        exact ⟨hφi, (Fin.heq_ext_iff hblk).mpr rfl⟩
    have hkind_multiset : (Finset.univ : Finset blkIdx).val.map kind =
        ggK1DCo_expectedKinds p nf d tw m := by
      have hsum : (Finset.univ : Finset (↥tailSet ⊕ Unit)) =
          (Finset.univ : Finset ↥tailSet).disjSum (Finset.univ : Finset Unit) :=
        (Finset.univ_disjSum_univ (α := ↥tailSet) (β := Unit)).symm
      rw [hsum, Finset.val_disjSum, Multiset.map_disjSum]
      rw [show Multiset.map (fun x : ↥tailSet => kind (Sum.inl x))
            (Finset.univ : Finset ↥tailSet).val =
          (Finset.univ : Finset ↥tailSet).val.map (fun t => kfun t.1) from rfl]
      rw [ggK1Df_tail_plumbing xL.toLinearMap m tailSet kfun f hmult (fun t => rfl)]
      rw [show Multiset.map (fun x : Unit => kind (Sum.inr x))
            (Finset.univ : Finset Unit).val = {headKind} from by simp [kind]]
      rw [ggK1DCo_expectedKinds, ggK1DCo_expectedKindList, ← hm.length_eq]
      rw [show (fun j => if d = 1 then ggK1DCo_Kind.sl (m.getD j 0)
            else ggK1DCo_Kind.su (m.getD j 0)) = (fun j => ggK1DCo_Kind.su (m.getD j 0)) from by
        funext j; rw [if_neg (by rw [hd2]; decide)]]
      rw [ggK1CBl_tail_filter_map m (fun j => ggK1DCo_Kind.su j)]
      rw [hhead, ← Multiset.coe_add, Multiset.coe_singleton, List.drop_one]
      exact Multiset.add_comm _ _
    have hdict : ∀ q : Σ i : blkIdx, Fin (ggK1DCo_kindOrbits nf (kind i)).length,
        let o := (ggK1DCo_kindOrbits nf (kind q.1)).get q.2
        let S := A q.1 q.2
        (o.qs = true ∧ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧ ggK1DCo_OrbitModel nf K o ↥⁅S, S⁆) ∨
          (o.qs = false ∧ ¬ CFSG.IsQuasisimple ↥⁅S, S⁆ ∧
            (o ≠ ggK1DCo_dummyOrbit nf → ∃ t ∈ S, t ^ p = 1 ∧ ∃ a ∈ S, a * t ≠ t * a)) := by
      rintro ⟨i, j⟩
      rcases i with t | u
      · have ha : Φ ⟨Sum.inl t, j⟩ = some
            ⟨φ t, Fin.cast (by rw [P.blk_eq (φ t), hkφ t]) j⟩ := rfl
        have hA : A (Sum.inl t) j = AP
            ⟨φ t, Fin.cast (by rw [P.blk_eq (φ t), hkφ t]) j⟩ := by simp [A, ha]
        have hblk : blk (Sum.inl t) = P.blk (φ t) := by
          rw [P.blk_eq (φ t), hkφ t]
        have ho : (blk (Sum.inl t)).get j =
            (P.blk (φ t)).get (Fin.cast (by rw [P.blk_eq (φ t), hkφ t]) j) :=
          List.get_of_eq hblk j
        rw [hA, ho]
        exact ggK1Df_dict_transport (hisoP _).some.symm
          (ggK1Df_dict_su hp hp2 hnf hK hdvd P (φ t)
            (primaryMultiplicity xL.toLinearMap t.1) (hkφ t) _)
      · cases hh : headIdx with
        | none =>
          have hA : A (Sum.inr u) j = ⊥ := by simp [A, Φ, hh]
          have hX1 : X - 1 ∉ primaryFactors xL.toLinearMap := by
            intro hmem
            obtain ⟨r, ⟨hrRep, hr⟩, _⟩ := hRep.2 (X - 1) hmem
            have hrX : r = X - 1 := by
              rcases hr with h | h
              · exact h.symm
              · have h2 := congrArg reciprocalPolynomial h
                rw [CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one] at h2
                rw [hxO.reciprocal_reciprocal_eq (h := r) (hRep.1 hrRep)] at h2
                exact h2.symm
            have hex : ∃ i, (e i : K[X]) = X - 1 :=
              ⟨e.symm ⟨r, hrRep⟩, by simp only [Equiv.apply_symm_apply]; exact hrX⟩
            have hsome : headIdx = some ⟨Classical.choose hex, Classical.choose_spec hex⟩ := by
              dsimp only [headIdx]; rw [dif_pos hex]
            rw [hsome] at hh
            cases hh
          have hWbot : W = ⊥ :=
            CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
              CFSG.RankThree.Classical.irreducible_X_sub_one
              CFSG.RankThree.Classical.monic_X_sub_one hX1
          have hm0 : m.headD 0 = 0 := by
            rw [hm.head_eq]
            change Module.finrank K W / 2 = 0
            rw [hWbot, finrank_bot]
          have hblk : blk (Sum.inr u) = [ggK1DCo_dummyOrbit nf] := by
            dsimp only [blk, kind]
            rw [hhead, hm0]
            simp [ggK1DCo_kindOrbits]
          have hget : (blk (Sum.inr u)).get j = ggK1DCo_dummyOrbit nf :=
            ggK1Df_get_dummy hblk j
          refine Or.inr ⟨?_, ?_, ?_⟩
          · rw [hget]; rfl
          · rw [hA, Subgroup.commutator_bot_left]; exact ggK1Df_not_quasi_bot
          · intro ho; exact absurd hget ho
        | some hd =>
          have ha : Φ ⟨Sum.inr u, j⟩ = some
              ⟨hd.1, Fin.cast (by rw [P.blk_eq hd.1, hkHead hd.1 hd.2]) j⟩ := by
            simp [Φ, hh]
          have hA : A (Sum.inr u) j = AP
              ⟨hd.1, Fin.cast (by rw [P.blk_eq hd.1, hkHead hd.1 hd.2]) j⟩ := by
            simp [A, ha]
          have hblk : blk (Sum.inr u) = P.blk hd.1 := by
            rw [P.blk_eq hd.1, hkHead hd.1 hd.2]
          have ho : (blk (Sum.inr u)).get j =
              (P.blk hd.1).get (Fin.cast (by rw [P.blk_eq hd.1, hkHead hd.1 hd.2]) j) :=
            List.get_of_eq hblk j
          rw [hA, ho]
          exact ggK1Df_dict_transport (hisoP _).some.symm
            (ggK1Df_dict_om hp hp2 hnf hK hdvd P hd.1
              (if CFSG.GroupTheory.WeirSylow.IsPlusType (Qf.restrict W) then true else false)
              (Module.finrank K W / 2) (hkHead hd.1 hd.2) _)
    obtain ⟨hmem, hqs, hlab, hreal, hbij, hsolv⟩ :=
      @ggK1Df_fields_of_dict p nf d r tw m K _ _ ι _ _ Q x blkIdx _ _
        hp hnf hK kind A hkind_multiset hdict
    refine ⟨blkIdx, blk, kind, ?_, A, ?_, ?_, ?_, ?_, hkind_multiset,
      hmem, hqs, hlab, hreal, hbij, hsolv⟩
    · intro i; rfl
    · exact ggK1Df_commute_elim AP Φ hΦ_inj2 hcommP
    · change (⨆ q, (Φ q).elim ⊥ AP) =
        Subgroup.centralizer ({LargeEvenProjMk (LargeEvenOmega Q) x} :
          Set (LargeEvenProj (LargeEvenOmega Q)))
      rw [ggK1Df_iSup_elim AP Φ hΦ_cover2, hjoinP]
    · exact ggK1Df_iSupIndep_elim AP Φ hΦ_inj2 hindepP
    · exact ggK1Df_tame_elim AP Φ htameP

theorem ggK1DCo_family_of_orthBlocks_plus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (Fin r ⊕ Fin r) K) m) (hx : x ^ p = 1)
    (hob : Nonempty (OrthPrimaryBlocks K (CFSG.StandardType.TableBOrth.qPlusForm K r) nf p
      (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)))) :
    Nonempty (ggK1DCo_Family p nf d false r m K (LargeEvenQPlus K r) x) := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  exact ggK1Df_family_of_orthBlocks hp hp2 hdvd hnf hK hd false
    (Q := LargeEvenQPlus K r) (Qf := CFSG.StandardType.TableBOrth.qPlusForm K r)
    (by rw [CFSG.StandardType.TableBOrth.coe_qPlusForm])
    hm hx (ggK1Df_omegaLift_plus hp hp2 hnf hK hx) (by
      by_cases hr : 1 ≤ r
      · exact TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := K) hr
      · have hr0 : r = 0 := by omega
        subst hr0
        exact Subsingleton.elim _ _)
      (by
        have hm' : GGK1DMultOf p nf (ggMultOrd p nf) r K (x : GL (Fin r ⊕ Fin r) K) m :=
          hd ▸ hm
        have hw := CFSG.StandardType.ggK1D_v0_witt_plus (p := p) (nf := nf) (r := r) (K := K)
          hp hp2 hdvd hnf hK hm' hx (CFSG.StandardType.TableBOrth.qPlusForm K r)
          (CFSG.StandardType.TableBOrth.coe_qPlusForm (K := K) r).symm
        rwa [← hd] at hw)
      hob

theorem ggK1DCo_family_of_orthBlocks_minus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (LargeEvenMinusIdx (r - 1)) K) m) (hx : x ^ p = 1)
    (hob : Nonempty (OrthPrimaryBlocks K
      (CFSG.StandardType.TableBOrth.qMinusForm K (r - 1) b c) nf p
      (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)))) :
    Nonempty (ggK1DCo_Family p nf d true r m K (LargeEvenQMinus (r - 1) b c) x) := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  exact ggK1Df_family_of_orthBlocks hp hp2 hdvd hnf hK hd true
    (Q := LargeEvenQMinus (r - 1) b c)
    (Qf := CFSG.StandardType.TableBOrth.qMinusForm K (r - 1) b c)
    (by rw [CFSG.StandardType.TableBOrth.coe_qMinusForm])
    hm hx (ggK1Df_omegaLift_minus hp hp2 hnf hK hirr hx)
    (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := r - 1) b c)
    (by
      have hm' : GGK1DMultOf p nf (ggMultOrd p nf) r K
          (x : GL (LargeEvenMinusIdx (r - 1)) K) m := hd ▸ hm
      have hw := CFSG.StandardType.ggK1D_v0_witt_minus (p := p) (nf := nf) (r := r) (K := K)
        hp hp2 hdvd hnf hK hirr hm' hx
        (CFSG.StandardType.TableBOrth.qMinusForm K (r - 1) b c)
        (CFSG.StandardType.TableBOrth.coe_qMinusForm (K := K) (r - 1) b c).symm
      rwa [← hd] at hw)
    hob

end CFSG.StandardType

end
