module

public import CFSG.ClassicalGroups.AlternatingInvolutionCentralizer
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryShortModel
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPSp
public import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak

public section
namespace CFSG.StandardType.RCKC1

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry Matrix
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.StandardType.RCKK1IIISU
open CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.StandardType.ClassicalPosition

theorem statedSpEquiv_apply
    {F : Type} [Field F] (n : ℕ) (g : StatedSp n F) (x : Fin n ⊕ Fin n → F) :
    (CFSG.LocalAnalysis.RankFourTheoremC.statedSpEquiv n F g).1 x =
      ((g : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ x := by
  let η := CFSG.LocalAnalysis.RankFourTheoremC.statedSpEquiv n F
  have h := congrArg Subtype.val (η.symm_apply_apply g)
  change basisMatrixEquiv (Pi.basisFun F (Fin n ⊕ Fin n)) (η g).1 = g.1 at h
  have h0 := basisMatrixEquiv_mulVec (Pi.basisFun F (Fin n ⊕ Fin n)) (η g).1 x
  change (basisMatrixEquiv (Pi.basisFun F (Fin n ⊕ Fin n)) (η g).1).val *ᵥ x = (η g).1 x at h0
  rw [h] at h0
  exact h0.symm

theorem sp_pCore_centralizer_of_fix_kernel
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (r : StatedSp n F) (hr : r ^ 2 = 1)
    (hAlt : ∀ x : Fin n ⊕ Fin n → F, x ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec
        ((((r : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ x) - x) = 0)
    (V : Subgroup (StatedSp n F))
    (hFix : ∀ v ∈ V, ∀ x : Fin n ⊕ Fin n → F,
      ((r : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ x = x →
      ((v : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ x = x) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({r} : Set (StatedSp n F))) ≤
      Subgroup.centralizer (V : Set (StatedSp n F)) := by
  let η := CFSG.LocalAnalysis.RankFourTheoremC.statedSpEquiv n F
  let B := pairedSympForm F n
  have hnd : ∀ w : Fin n ⊕ Fin n → F, w ≠ 0 → ∃ a, B w a ≠ 0 := by
    intro w hw
    by_contra hc
    push Not at hc
    exact hw (CFSG.LocalAnalysis.ComponentInitial.pairedSympForm_nondegenerate.1 w hc)
  have hr' : (η r) ^ 2 = 1 := by rw [← map_pow, hr, map_one]
  have hAlt' : ∀ x, B x ((η r).1 x - x) = 0 := by
    intro x
    rw [statedSpEquiv_apply]
    simpa only [B, pairedSympForm, Matrix.toBilin'_apply'] using hAlt x
  have hFix' : ∀ v ∈ V.map η.toMonoidHom,
      ∀ x ∈ LinearMap.ker (CFSG.ClassicalGroups.AlternatingCentralizer.isometryRep B (η r) - 1),
        v.1 x = x := by
    intro v hv x hx
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
    rw [LinearMap.mem_ker] at hx
    change (η r).1 x - x = 0 at hx
    have hrx : ((r : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ x = x := by
      rw [← statedSpEquiv_apply n r x]
      exact sub_eq_zero.mp hx
    change (η v₀).1 x = x
    rw [statedSpEquiv_apply]
    exact hFix v₀ hv₀ x hrx
  have hcore := CFSG.ClassicalGroups.AlternatingCentralizer.pCoreOf_centralizer_le_centralizer_of_fix_kernel
    B pairedSympForm_isAlt hnd (η r) hr' hAlt' (V.map η.toMonoidHom) hFix'
  have hmap : (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({r} : Set (StatedSp n F)))).map η.toMonoidHom =
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({η r} : Set (TauCeti.BilinForm.isometryGroup B))) := by
    rw [← CFSG.GroupTheory.map_pCoreOf_mulEquiv, CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv,
      Set.image_singleton]
    simp only [MulEquiv.coe_toMonoidHom]
  intro y hy
  have hy' : η y ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({η r} : Set (TauCeti.BilinForm.isometryGroup B))) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem η.toMonoidHom hy
  have hyc := hcore hy'
  rw [Subgroup.mem_centralizer_iff] at hyc ⊢
  intro v hv
  apply η.injective
  simpa only [map_mul] using hyc (η v) (Subgroup.mem_map_of_mem η.toMonoidHom hv)

theorem k2At_of_unitary_linear_embedding_sp
    {m n : ℕ} (hm : 4 ≤ m)
    [Algebra (GaloisField 2 1) SUF]
    (ι : SUG m →* StatedSp n (GaloisField 2 1))
    (E : (Fin m → SUF) →ₗ[GaloisField 2 1] ((Fin n ⊕ Fin n) → GaloisField 2 1))
    (hE : Function.Injective E)
    (C : Submodule (GaloisField 2 1) ((Fin n ⊕ Fin n) → GaloisField 2 1))
    (hAct : ∀ g x, ((ι g : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ E x = E (natRep (SU SUσ m) g x))
    (hFix : ∀ g w, w ∈ C → ((ι g : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ w = w)
    (hSplit : ∀ z, ∃ x, ∃ w ∈ C, z = E x + w)
    (hAlt : ∀ g, g ^ 2 = 1 → ∀ z, z ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)).mulVec
        ((((ι g : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ z) - z) = 0)
    {V : Subgroup (SUG m)} {r : SUG m}
    (hFour : FourAt (⊤ : Subgroup (SUG m)) V r)
    (hCore : CoreCommAt (⊤ : Subgroup (SUG m)) V r)
    (hRank : (mat SUσ m r - 1).rank = 2) :
    K2At (⊤ : Subgroup (StatedSp n (GaloisField 2 1))) (V.map ι) (ι r) := by
  have hr : r ^ 2 = 1 := hFour.2.2.1.2 r hFour.1
  have hSourceFix := rckSU_fixes_fixed_space_of_rank_two hm hFour hCore hRank
  have hr' : (ι r) ^ 2 = 1 := by rw [← map_pow, hr, map_one]
  have hK2 := sp_pCore_centralizer_of_fix_kernel (ι r) hr' (hAlt r hr) (V.map ι) ?_
  · simpa only [K2At, top_inf_eq] using hK2.trans (Subgroup.centralizer_le_normalizer _)
  intro v hv z hRz
  obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
  obtain ⟨x, w, hw, hz⟩ := hSplit z
  have hRx : natRep (SU SUσ m) r x = x := by
    apply hE
    rw [hz, Matrix.mulVec_add, hAct, hFix r w hw] at hRz
    exact add_right_cancel hRz
  rw [hz, Matrix.mulVec_add, hAct, hFix v₀ w hw, hSourceFix v₀ hv₀ x hRx]

section BlockCertificates


theorem k2At_of_shortAt_selfDualTwo_sp_block
    {n : ℕ} (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 1)))
    (hSU : ∀ s ∈ S, s ∈ StatedSp n (GaloisField 2 1))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 1))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 1)) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 4)
    {J V : Subgroup (StatedSp n (GaloisField 2 1))} {r : StatedSp n (GaloisField 2 1)}
    (hJ : CFSG.Assembly.IsComponentOf J ⁅glBlockCentralizer (StatedSp n (GaloisField 2 1)).subtype S e,
      glBlockCentralizer (StatedSp n (GaloisField 2 1)).subtype S e⁆)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At (⊤ : Subgroup (StatedSp n (GaloisField 2 1))) V r := by
  obtain ⟨m, A, ι, E, C, hm, hι, hRange, hE, hAct, hFix, hSplit, hAlt⟩ :=
    CFSG.StandardType.ClassicalPosition.exists_linearBlockModel_selfDualTwo_PSp_at_two
      n S hSU hS hodd he hadj hdeg₁ hdeg₂ hJ
  let : Algebra (GaloisField 2 1) SUF := A
  let ιJ : SUG m →* J := ι.codRestrict J (by
    intro g
    rw [← hRange]
    exact ⟨g, rfl⟩)
  have hιJ : Function.Bijective ιJ := by
    constructor
    · intro a b hab
      exact hι (congrArg Subtype.val hab)
    · intro j
      have hj : (j : StatedSp n (GaloisField 2 1)) ∈ ι.range := hRange.symm ▸ j.2
      obtain ⟨g, hg⟩ := hj
      exact ⟨g, Subtype.ext hg⟩
  let η : J ≃* SUG m := (MulEquiv.ofBijective ιJ hιJ).symm
  have hComp (j : J) : ι (η j) = (j : StatedSp n (GaloisField 2 1)) :=
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
    change (rJ : StatedSp n (GaloisField 2 1)) ^ 2 = 1
    rw [hr]
    exact hFour.2.2.1.2 r hFour.1
  have hRank := rckSURank_of_shortAt_model hm η hr1 hr2 hPos
  have hSub : (⟨r, hrJ⟩ : J) = rJ := Subtype.ext hr.symm
  have hRank' : (mat SUσ m (η ⟨r, hrJ⟩) - 1).rank = 2 := by
    simpa only [hSub] using hRank
  have hK2 := k2At_of_unitary_linear_embedding_sp hm ι E hE C hAct hFix hSplit hAlt
    hFour' hCore' hRank'
  have hV : ((V.subgroupOf J).map η.toMonoidHom).map ι = V := by
    rw [Subgroup.map_map]
    have hHom : ι.comp η.toMonoidHom = J.subtype := MonoidHom.ext hComp
    rw [hHom, Subgroup.map_subgroupOf_eq_of_le hFour.2.1]
  have hR : ι (η ⟨r, hrJ⟩) = r := hComp ⟨r, hrJ⟩
  rwa [hV, hR] at hK2

end BlockCertificates

end CFSG.StandardType.RCKC1
