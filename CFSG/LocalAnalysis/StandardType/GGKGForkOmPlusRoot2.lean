module

public import CFSG.LocalAnalysis.StandardType.GGKGForkOmPlusRoot1
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmPlusRoot3
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Two
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactMatrix
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Main8
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBlocks
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplit
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

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.SeitzReduction SpCoord
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.RankTwoClassical

private theorem ggKGOmR_flip_conj {m p : ℕ} {K : Type} [Field K] {ζ : Kˣ}
    (hζ : ζ ^ p = 1) (i : Fin m) (f : Fin m → Multiplicative (ZMod p)) :
    OmegaPilot.flipGL K {i} * omPlusTorusGL hζ f * (OmegaPilot.flipGL K {i})⁻¹ =
      omPlusTorusGL hζ (sgnAut i f) := by
  rw [omPlusTorusGL_apply, omPlusTorusGL_apply,
    OmegaPilot.flipGL_mul_diagOmega_mul_inv]
  congr 1
  funext j
  rw [OmegaPilot.flipParam_apply, sgnAut_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · rw [Function.update_of_ne hj]
    simp [hj]

private theorem ggKGOmR_sep {m p : ℕ} {K : Type} [Field K] {ζ : Kˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    {a b : Fin m ⊕ Fin m} (hab : a ≠ b) :
    ∃ f : Fin m → Multiplicative (ZMod p),
      diagSpEntry (fun j => TableBSymp.zmodPowHom hζ (f j)) a ≠
        diagSpEntry (fun j => TableBSymp.zmodPowHom hζ (f j)) b := by
  have hχ : TableBSymp.zmodPowHom hζ (Multiplicative.ofAdd (1 : ZMod p)) = ζ := by
    have h1 := TableBSymp.zmodPowHom_natCast hζ 1
    rwa [Nat.cast_one, pow_one] at h1
  have hζ1 : ζ ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hζo, h, orderOf_one])
  have hζ2 : ζ * ζ ≠ 1 := by
    intro h
    have h1 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [hζo] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hζinv : ζ ≠ ζ⁻¹ := fun h => hζ2 (mul_eq_one_iff_eq_inv.mpr h)
  have hfun : ∀ j : Fin m,
      (fun j_1 => TableBSymp.zmodPowHom hζ
        (Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod p)) j
          (Multiplicative.ofAdd (1 : ZMod p)) j_1)) =
      Pi.mulSingle j (TableBSymp.zmodPowHom hζ (Multiplicative.ofAdd (1 : ZMod p))) := by
    intro j
    funext j_1
    by_cases hj : j_1 = j
    · subst hj; simp
    · rw [Pi.mulSingle_apply, if_neg hj, map_one, Pi.mulSingle_apply, if_neg hj]
  have hnotinl : ∀ {j l : Fin m}, j ≠ l → (Sum.inl l : Fin m ⊕ Fin m) ∉ coords j := by
    intro j l hjl hmem
    simp only [coords, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq] at hmem
    rcases hmem with h | h
    · exact hjl h.symm
    · exact Sum.inl_ne_inr h
  have hnotinr : ∀ {j l : Fin m}, j ≠ l → (Sum.inr l : Fin m ⊕ Fin m) ∉ coords j := by
    intro j l hjl hmem
    simp only [coords, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inr.injEq] at hmem
    rcases hmem with h | h
    · exact Sum.inr_ne_inl h
    · exact hjl h.symm
  rcases a with j | j <;> rcases b with l | l
  · by_cases hjl : j = l
    · exact absurd (by rw [hjl]) hab
    · refine ⟨Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p)), ?_⟩
      rw [hfun j, diagSpEntry_mulSingle_of_not_mem j _ (hnotinl hjl),
        diagSpEntry_mulSingle_inl_self, hχ]
      exact fun h => hζ1 (Units.ext h)
  · rcases eq_or_ne j l with rfl | hjl
    · refine ⟨Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p)), ?_⟩
      rw [hfun j, diagSpEntry_mulSingle_inl_self, diagSpEntry_mulSingle_inr_self, hχ]
      exact fun h => hζinv (Units.ext h)
    · refine ⟨Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p)), ?_⟩
      rw [hfun j, diagSpEntry_mulSingle_of_not_mem j _ (hnotinr hjl),
        diagSpEntry_mulSingle_inl_self, hχ]
      exact fun h => hζ1 (Units.ext h)
  · rcases eq_or_ne j l with rfl | hjl
    · refine ⟨Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p)), ?_⟩
      rw [hfun j, diagSpEntry_mulSingle_inr_self, diagSpEntry_mulSingle_inl_self, hχ]
      exact fun h => hζinv (Units.ext h.symm)
    · refine ⟨Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p)), ?_⟩
      rw [hfun j, diagSpEntry_mulSingle_inr_self,
        diagSpEntry_mulSingle_of_not_mem j _ (hnotinl hjl), hχ]
      exact fun h => hζ1 (inv_eq_one.mp (Units.ext h))
  · by_cases hjl : j = l
    · exact absurd (by rw [hjl]) hab
    · refine ⟨Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p)), ?_⟩
      rw [hfun j, diagSpEntry_mulSingle_inr_self,
        diagSpEntry_mulSingle_of_not_mem j _ (hnotinr hjl), hχ]
      exact fun h => hζ1 (inv_eq_one.mp (Units.ext h))


theorem ggKGOmR_centralizer_diag {m p : ℕ} {K : Type} [Field K] {ζ : Kˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    {g : GL (Fin m ⊕ Fin m) K}
    (hg : ∀ f : Fin m → Multiplicative (ZMod p),
      g * omPlusTorusGL hζ f = omPlusTorusGL hζ f * g) :
    ∀ a b : Fin m ⊕ Fin m, a ≠ b →
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b = 0 := by
  intro a b hab
  obtain ⟨f, hf⟩ := ggKGOmR_sep hp hp2 hζ hζo hab
  have hdiag : (omPlusTorusGL hζ f : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      Matrix.diagonal (fun c => diagSpEntry
        (fun j => TableBSymp.zmodPowHom hζ (f j)) c) := by
    rw [omPlusTorusGL_apply, OmegaPilot.diagOmega_coe]
  have hd : ∀ a b : Fin m ⊕ Fin m, a ≠ b →
      (omPlusTorusGL hζ f : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b = 0 := by
    intro a b hab
    rw [hdiag, Matrix.diagonal_apply_ne _ hab]
  exact (commute_of_diag_iff hd g).mp (hg f) a b (by
    rw [hdiag, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    exact hf)

private theorem ggKGOmR_commRank_eq_finrank_commSpace {m : ℕ} {K : Type} [Field K]
    (M : GL (Fin m ⊕ Fin m) K) :
    commRank M = Module.finrank K (commSpace (toLinEquiv (Fin m ⊕ Fin m) K M)) := by
  have hrange : commSpace (toLinEquiv (Fin m ⊕ Fin m) K M) =
      LinearMap.range ((M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1).mulVecLin := by
    ext v
    simp [commSpace, toLinEquiv_apply]
  rw [commRank, Matrix.rank, ← hrange]

private theorem ggKGOmR_commRank_flip {m : ℕ} {K : Type} [Field K] (i : Fin m) :
    commRank (OmegaPilot.flipGL K {i}) = 1 := by
  classical
  rw [ggKGOmR_commRank_eq_finrank_commSpace]
  let φ : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K) :=
    toLinEquiv (Fin m ⊕ Fin m) K (OmegaPilot.flipGL K {i})
  let w : Fin m ⊕ Fin m → K := Pi.single (Sum.inl i) 1 - Pi.single (Sum.inr i) 1
  change Module.finrank K (commSpace φ) = 1
  have hφapply : ∀ y, φ y = fun a => y (OmegaPilot.flipPerm {i} a) := by
    intro y
    change (OmegaPilot.flipGL K {i} :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).mulVec y = _
    rw [OmegaPilot.coe_flipGL, Matrix.permMatrix_mulVec]
    rfl
  have hφsub : ∀ y, φ y - y = fun a => y (OmegaPilot.flipPerm {i} a) - y a := by
    intro y
    ext a
    rw [Pi.sub_apply, hφapply y]
  have hmem : ∀ x, x ∈ commSpace φ ↔
      ∃ y : Fin m ⊕ Fin m → K,
        (fun a => y (OmegaPilot.flipPerm {i} a) - y a) = x := by
    intro x
    rw [mem_commSpace]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [← hy, hφsub]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, hφsub y⟩
  have hwne : w ≠ 0 := by
    intro h
    have h1 := congrFun h (Sum.inl i)
    simp [w, Pi.single_eq_same] at h1
  have hw_inl : w (Sum.inl i) = 1 := by simp [w, Pi.single_eq_same]
  have hw_inr : w (Sum.inr i) = -1 := by simp [w, Pi.single_eq_same]
  have hw_inl_ne : ∀ j, j ≠ i → w (Sum.inl j) = 0 := by
    intro j hj
    simp [w, Pi.single_apply, hj, Sum.inl.injEq]
  have hw_inr_ne : ∀ j, j ≠ i → w (Sum.inr j) = 0 := by
    intro j hj
    simp [w, Pi.single_apply, hj, Sum.inr.injEq]
  have hf_inl : OmegaPilot.flipPerm {i} (Sum.inl i) = Sum.inr i := by
    simp [OmegaPilot.flipPerm_apply, OmegaPilot.flipPermFun]
  have hf_inr : OmegaPilot.flipPerm {i} (Sum.inr i) = Sum.inl i := by
    simp [OmegaPilot.flipPerm_apply, OmegaPilot.flipPermFun]
  have hf_inl_ne : ∀ j, j ≠ i → OmegaPilot.flipPerm {i} (Sum.inl j) = Sum.inl j := by
    intro j hj
    simp [OmegaPilot.flipPerm_apply, OmegaPilot.flipPermFun, hj]
  have hf_inr_ne : ∀ j, j ≠ i → OmegaPilot.flipPerm {i} (Sum.inr j) = Sum.inr j := by
    intro j hj
    simp [OmegaPilot.flipPerm_apply, OmegaPilot.flipPermFun, hj]
  have hspan : commSpace φ = K ∙ w := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, rfl⟩ := (hmem x).mp hx
      rw [Submodule.mem_span_singleton]
      refine ⟨y (Sum.inr i) - y (Sum.inl i), ?_⟩
      funext a
      rcases a with j | j
      · by_cases hj : j = i
        · subst hj
          simp [hw_inl, hf_inl]
        · simp [hw_inl_ne j hj, hf_inl_ne j hj]
      · by_cases hj : j = i
        · subst hj
          simp [hw_inr, hf_inr]
        · simp [hw_inr_ne j hj, hf_inr_ne j hj]
    · rw [Submodule.span_singleton_le_iff_mem, hmem]
      refine ⟨Pi.single (Sum.inr i) 1, ?_⟩
      funext a
      rcases a with j | j
      · by_cases hj : j = i
        · subst hj
          rw [hf_inl, hw_inl]
          simp [Pi.single_apply]
        · rw [hf_inl_ne j hj, hw_inl_ne j hj]
          simp [Pi.single_apply, hj]
      · by_cases hj : j = i
        · subst hj
          rw [hf_inr, hw_inr]
          simp [Pi.single_apply]
        · rw [hf_inr_ne j hj, hw_inr_ne j hj]
          simp [Pi.single_apply, hj]
  rw [hspan, finrank_span_singleton hwne]

private def ggKGOmR_diagEquiv {m : ℕ} {K : Type} [Field K]
    {w : Fin m ⊕ Fin m → K} (hprod : ∀ j, w (Sum.inl j) * w (Sum.inr j) = 1) :
    {a : Fin m ⊕ Fin m // w a ≠ 1} ≃ {j : Fin m // w (Sum.inl j) ≠ 1} × Bool where
  toFun a := match a with
    | ⟨Sum.inl j, ha⟩ => (⟨j, ha⟩, false)
    | ⟨Sum.inr j, ha⟩ => (⟨j, fun h => ha (by
        calc w (Sum.inr j) = 1 * w (Sum.inr j) := (one_mul _).symm
          _ = w (Sum.inl j) * w (Sum.inr j) := by rw [h]
          _ = 1 := hprod j)⟩, true)
  invFun p := match p.2 with
    | false => ⟨Sum.inl p.1.1, p.1.2⟩
    | true => ⟨Sum.inr p.1.1, fun h => p.1.2 (by
        calc w (Sum.inl p.1.1) = w (Sum.inl p.1.1) * 1 := (mul_one _).symm
          _ = w (Sum.inl p.1.1) * w (Sum.inr p.1.1) := by rw [h]
          _ = 1 := hprod p.1.1)⟩
  left_inv := by
    rintro ⟨a, ha⟩
    rcases a with j | j <;> exact Subtype.ext rfl
  right_inv := by
    rintro ⟨⟨j, hj⟩, b⟩
    cases b
    · rfl
    · exact Prod.ext (Subtype.ext rfl) rfl

private theorem ggKGOmR_even_card_diag {m : ℕ} {K : Type} [Field K] [DecidableEq K] {w : Fin m ⊕ Fin m → K}
    (hprod : ∀ j, w (Sum.inl j) * w (Sum.inr j) = 1) :
    Even (Fintype.card {a : Fin m ⊕ Fin m // w a ≠ 1}) := by
  rw [Fintype.card_congr (ggKGOmR_diagEquiv hprod), Fintype.card_prod, Fintype.card_bool]
  exact ⟨_, by ring⟩

private theorem ggKGOmR_commRank_diag_eq {m : ℕ} {K : Type} [Field K] [DecidableEq K]
    {d : GL (Fin m ⊕ Fin m) K} {w : Fin m ⊕ Fin m → K}
    (hd : (d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal w) :
    commRank d = Fintype.card {a : Fin m ⊕ Fin m // w a ≠ 1} := by
  rw [commRank, hd, ← Matrix.diagonal_one (α := K), Matrix.diagonal_sub,
    Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun a => sub_ne_zero))

private theorem ggKGOmR_diag_form_prod {m : ℕ} {K : Type} [Field K]
    {w : Fin m ⊕ Fin m → K}
    (hform : ∀ v : Fin m ⊕ Fin m → K,
      (CFSG.LieType.Universal.Spin.quadPlus m K) ((Matrix.diagonal w).mulVec v) =
        (CFSG.LieType.Universal.Spin.quadPlus m K) v)
    (j : Fin m) : w (Sum.inl j) * w (Sum.inr j) = 1 := by
  have h1 : (CFSG.LieType.Universal.Spin.quadPlus m K)
      ((Matrix.diagonal w).mulVec (Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1)) =
      w (Sum.inl j) * w (Sum.inr j) := by
    rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
    simp only [Matrix.mulVec_diagonal, Pi.add_apply, Pi.single_apply, Sum.inl.injEq,
      Sum.inr.injEq, reduceIte]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [hbj, Sum.inl_ne_inr, Sum.inr_ne_inl]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have h2 : (CFSG.LieType.Universal.Spin.quadPlus m K)
      (Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1) = 1 := by
    rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
    simp only [Pi.add_apply, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceIte]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [hbj, Sum.inl_ne_inr, Sum.inr_ne_inl]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hv := hform (Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1)
  rwa [h1, h2] at hv

private theorem ggKGOmR_commRank_diag_even {m : ℕ} {K : Type} [Field K]
    [DecidableEq K] {d : GL (Fin m ⊕ Fin m) K} {w : Fin m ⊕ Fin m → K}
    (hd : (d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal w)
    (hform : ∀ v : Fin m ⊕ Fin m → K,
      (CFSG.LieType.Universal.Spin.quadPlus m K) ((Matrix.diagonal w).mulVec v) =
        (CFSG.LieType.Universal.Spin.quadPlus m K) v) :
    Even (commRank d) := by
  rw [ggKGOmR_commRank_diag_eq hd]
  exact ggKGOmR_even_card_diag (fun j => ggKGOmR_diag_form_prod hform j)

private theorem ggKGOmR_natCast_commRank_mul {m : ℕ} {K : Type} [Field K]
    {M N : GL (Fin m ⊕ Fin m) K}
    (hM : toLinEquiv (Fin m ⊕ Fin m) K M ∈
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus m K))
    (hN : toLinEquiv (Fin m ⊕ Fin m) K N ∈
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus m K)) :
    (commRank (M * N) : ZMod 2) = commRank M + commRank N := by
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K
  rw [ggKGOmR_commRank_eq_finrank_commSpace, ggKGOmR_commRank_eq_finrank_commSpace,
    ggKGOmR_commRank_eq_finrank_commSpace]
  rw [show toLinEquiv (Fin m ⊕ Fin m) K (M * N) =
      toLinEquiv (Fin m ⊕ Fin m) K M * toLinEquiv (Fin m ⊕ Fin m) K N from map_mul _ _ _]
  exact natCast_finrank_commSpace_mul hQ hM hN

theorem ggKGOmR_not_sgnAut {m p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hm : 4 ≤ m) {ζ : Kˣ} (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1)
    (hζo : orderOf ζ = p) (i : Fin m) :
    ¬ ∃ w₀ : StatedOmega (StatedQuadPlus m K),
      ∀ f, w₀ * omPlusTorus hζ f * w₀⁻¹ = omPlusTorus hζ (sgnAut i f) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rintro ⟨w₀, hw₀⟩
  set g : GL (Fin m ⊕ Fin m) K := (w₀ : GL (Fin m ⊕ Fin m) K) with hgdef
  set flip : GL (Fin m ⊕ Fin m) K := OmegaPilot.flipGL K {i} with hflipdef
  set d : GL (Fin m ⊕ Fin m) K := g * flip⁻¹ with hddef
  have hflip_inv : flip⁻¹ = flip := by rw [hflipdef]; exact OmegaPilot.flipGL_inv {i}
  have hconj_g : ∀ f, g * omPlusTorusGL hζ f * g⁻¹ = omPlusTorusGL hζ (sgnAut i f) := by
    intro f
    have h := congrArg (fun x : StatedOmega (StatedQuadPlus m K) =>
      (x : GL (Fin m ⊕ Fin m) K)) (hw₀ f)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_omPlusTorus] using h
  have hflip_mul : ∀ f, flip * omPlusTorusGL hζ f = omPlusTorusGL hζ (sgnAut i f) * flip := by
    intro f
    rw [hflipdef, ← ggKGOmR_flip_conj (K := K) (m := m) hζ i f]
    group
  have hsgn : ∀ f : Fin m → Multiplicative (ZMod p),
      sgnAut (p := p) i (sgnAut (p := p) i f) = f := by
    intro f
    have h : (SpCoord.sgnAut (p := p) i * SpCoord.sgnAut (p := p) i :
        MulAut (Fin m → Multiplicative (ZMod p))) = 1 := by
      rw [← sq]; exact SpCoord.sgnAut_sq i
    have h' := congrArg (fun u : MulAut (Fin m → Multiplicative (ZMod p)) => u f) h
    simpa only [MulAut.mul_apply, MulAut.one_apply] using h'
  have hdcomm : ∀ f, d * omPlusTorusGL hζ f = omPlusTorusGL hζ f * d := by
    intro f
    have hg2 := hconj_g (sgnAut i f)
    rw [hsgn] at hg2
    calc d * omPlusTorusGL hζ f
        = g * flip⁻¹ * omPlusTorusGL hζ f := by rw [hddef]
      _ = g * (flip⁻¹ * omPlusTorusGL hζ f) := by group
      _ = g * (omPlusTorusGL hζ (sgnAut i f) * flip) := by rw [hflip_inv, hflip_mul]
      _ = (g * omPlusTorusGL hζ (sgnAut i f) * g⁻¹) * g * flip := by group
      _ = omPlusTorusGL hζ f * g * flip := by rw [hg2]
      _ = omPlusTorusGL hζ f * (g * flip⁻¹) := by rw [hflip_inv]; group
      _ = omPlusTorusGL hζ f * d := by rw [hddef]
  have hdiag := ggKGOmR_centralizer_diag (K := K) (m := m) hp hp2 hζ hζo hdcomm
  set w : Fin m ⊕ Fin m → K := fun a =>
    (d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a a with hwdef
  have hd_diag : (d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal w := by
    ext a b
    by_cases hab : a = b
    · subst hab; rw [Matrix.diagonal_apply_eq, hwdef]
    · rw [hdiag a b hab, Matrix.diagonal_apply_ne _ hab]
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K
  have hgO : toLinEquiv (Fin m ⊕ Fin m) K g ∈
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus m K) :=
    (mem_omegaGroup.mp (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ
      (ggKGOmR_mem_orthDerived (K := K) (m := m) hm w₀))).1
  have hflipO : toLinEquiv (Fin m ⊕ Fin m) K flip ∈
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus m K) := by
    rw [hflipdef]
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    rw [toLinEquiv_apply]
    simpa only [CFSG.LieType.Universal.Spin.coe_quadPlus] using
      OmegaPilot.flipGL_isometry {i} v
  have hdO : toLinEquiv (Fin m ⊕ Fin m) K d ∈
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus m K) := by
    rw [hddef, map_mul]
    exact mul_mem hgO (inv_mem hflipO)
  have hform : ∀ v : Fin m ⊕ Fin m → K,
      (CFSG.LieType.Universal.Spin.quadPlus m K) ((Matrix.diagonal w).mulVec v) =
        (CFSG.LieType.Universal.Spin.quadPlus m K) v := by
    intro v
    have h := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hdO) v
    rwa [toLinEquiv_apply, hd_diag] at h
  have hdEven : Even (commRank d) := ggKGOmR_commRank_diag_even hd_diag hform
  have hgEven : Even (commRank g) :=
    even_commRank_of_mem_statedOmega (CFSG.LieType.Universal.Spin.quadPlus m K) hQ
      (by rw [CFSG.LieType.Universal.Spin.coe_quadPlus]; exact w₀.2)
  have hg0 : (commRank g : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr hgEven
  have hd0 : (commRank d : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr hdEven
  have hg_eq : g = d * flip := by
    rw [hddef]
    group
  have h1 : (commRank (d * flip) : ZMod 2) = 0 := by rw [← hg_eq]; exact hg0
  rw [ggKGOmR_natCast_commRank_mul hdO hflipO, hd0, ggKGOmR_commRank_flip i] at h1
  norm_num at h1

end CFSG.StandardType

end
