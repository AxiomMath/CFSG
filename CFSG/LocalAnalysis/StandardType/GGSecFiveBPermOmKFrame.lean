module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmFrameDefs
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
import CFSG.LocalAnalysis.EvenBN.U4.Model.Perfect
import CFSG.ClassicalInvolution.Balance.Q27FuzzyModel
import CFSG.LocalAnalysis.StandardType.GGKGPosOmegaMinusFix
import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
import CFSG.ClassicalInvolution.WeakCT.SpModel
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyCanon
import CFSG.ClassicalInvolution.Balance.Q27Layers
import CFSG.ClassicalInvolution.Balance.Theorem5Models
import CFSG.ClassicalInvolution.Generic.InductionMain
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
import CFSG.ClassicalInvolution.RouteD.TypeAChain
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT CFSG.LieType
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

section OmHelpers

private theorem omk_eq_sum_single {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (X : ι → F) :
    X = ∑ idx, X idx • (Pi.single idx (1 : F) : ι → F) := by
  ext a
  rw [Finset.sum_apply,
    Finset.sum_eq_single a (fun e _ hea => ?_) (fun ha => absurd (Finset.mem_univ a) ha)]
  · simp
  · simp [hea]

private theorem omk_single_plane {n : ℕ} {F : Type} [Field F] (t : Fin 2) :
    (Pi.single (Sum.inr (Sum.inr t)) (1 : F) : Vm n F) = planeVec n (Pi.single t 1) := by
  funext z
  rcases z with a | a | a <;> simp [planeVec, Pi.single_apply]

private theorem omk_diagAct_unique {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {u v : spinGroup (quadMinus n F b c)} {ρ : Fin (n - 1) → Fˣ}
    (hu : PsiDiag.SpinM.DiagAct u ρ) (hv : PsiDiag.SpinM.DiagAct v ρ) : u = v := by
  refine RootCentOmega.spinAction_quadMinus_injective hirr (LinearEquiv.ext fun X => ?_)
  conv_lhs => rw [omk_eq_sum_single X]
  conv_rhs => rw [omk_eq_sum_single X]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [map_smul, map_smul]
  congr 1
  rcases idx with i | i | t
  · exact (hu.1 i).trans (hv.1 i).symm
  · exact (hu.2.1 i).trans (hv.2.1 i).symm
  · rw [omk_single_plane t]
    exact (hu.2.2 _).trans (hv.2.2 _).symm

private theorem omk_commute_of_diagAct {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {u v : spinGroup (quadMinus n F b c)} {ρ ρ' : Fin (n - 1) → Fˣ}
    (hu : PsiDiag.SpinM.DiagAct u ρ) (hv : PsiDiag.SpinM.DiagAct v ρ') :
    u * v = v * u := by
  refine omk_diagAct_unique hirr (hu.mul hv) ?_
  refine (hv.mul hu).congr ?_
  funext l
  simp only [Pi.mul_apply]
  exact mul_comm _ _

private theorem omk_conj_longRoot_of_diagAct {n : ℕ} {F : Type} [Field F] {b c : F}
    {g : spinGroup (quadMinus n F b c)} {χ : Fin (n - 1) → Fˣ}
    (hg : PsiDiag.SpinM.DiagAct g χ) {i j : Fin (n - 1)} (hij : i ≠ j) (hχ : χ i = χ j)
    {s t : Bool} (hst : s ≠ t) (a : F) :
    g * (minusFrame n b c).longRoot hij s t (.ofAdd a) * g⁻¹ =
      (minusFrame n b c).longRoot hij s t (.ofAdd a) := by
  cases s <;> cases t
  · exact absurd rfl hst
  · have hsc : ((χ i : F))⁻¹ * (χ j : F) = 1 := by
      rw [← hχ]
      exact inv_mul_cancel₀ (χ i).ne_zero
    have h := (minusFrame n b c).conj_longRoot g hij false true hij false true
      (by simpa [minusFrame_vec] using hg.2.1 i) (by simpa [minusFrame_vec] using hg.1 j) a
    rw [h, show ((χ i : F))⁻¹ * (χ j : F) * a = a by rw [hsc, one_mul]]
  · have hsc : (χ i : F) * ((χ j : F))⁻¹ = 1 := by
      rw [hχ]
      exact mul_inv_cancel₀ (χ j).ne_zero
    have h := (minusFrame n b c).conj_longRoot g hij true false hij true false
      (by simpa [minusFrame_vec] using hg.1 i) (by simpa [minusFrame_vec] using hg.2.1 j) a
    rw [h, show (χ i : F) * ((χ j : F))⁻¹ * a = a by rw [hsc, one_mul]]
  · exact absurd rfl hst

private theorem omk_conj_rLong_of_diagAct {n : ℕ} {F : Type} [Field F] {b c : F}
    {k : Fin (n - 1)} (hk : k.val + 1 < n - 1)
    {g : spinGroup (quadMinus n F b c)} {χ : Fin (n - 1) → Fˣ}
    (hg : PsiDiag.SpinM.DiagAct g χ) (hχ : χ k = χ ⟨k.val + 1, hk⟩) (m : SL(2, F)) :
    g * rLong n b c hk m * g⁻¹ = rLong n b c hk m := by
  have hhom : (MulAut.conj g).toMonoidHom.comp (rLong n b c hk) = rLong n b c hk := by
    refine hom_ext_sl2 (fun t => ?_) (fun t => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [rLong_tv01]
      exact omk_conj_longRoot_of_diagAct hg (succ_ne_of_lt n hk) hχ
        (s := true) (t := false) (by decide) t
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [rLong_tv10]
      exact omk_conj_longRoot_of_diagAct hg (succ_ne_of_lt n hk).symm hχ.symm
        (s := true) (t := false) (by decide) t
  have h2 := DFunLike.congr_fun hhom m
  simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h2

private theorem omk_rLong_torus_diagAct {n : ℕ} {F : Type} [Field F] {b c : F}
    {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) (ζ : Fˣ) :
    PsiDiag.SpinM.DiagAct (rLong n b c hk (CFSG.ClassicalInvolution.WeakCT.torusHom F ζ))
      (fun l => ζ ^ longCoroot k ⟨k.val + 1, hk⟩ true false l true) :=
  PsiDiag.SpinM.diagAct_longTorus (n := n) (b := b) (c := c) (j := k) hk ζ

private theorem omk_diagAct_pow {n : ℕ} {F : Type} [Field F]
    {b c : F} {g : spinGroup (quadMinus n F b c)} {χ : Fin (n - 1) → Fˣ}
    (h : PsiDiag.SpinM.DiagAct g χ) (m : ℕ) : PsiDiag.SpinM.DiagAct (g ^ m) (χ ^ m) := by
  induction m with
  | zero => simpa using PsiDiag.SpinM.diagAct_one (n := n) (K := F) (b := b) (c := c)
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul h

private theorem omk_diagAct_eigenspace {n : ℕ} {F : Type} [Field F] {b c : F}
    {t : spinGroup (quadMinus n F b c)} {m : Fin (n - 1)} {ζ : Fˣ}
    (ht : PsiDiag.SpinM.DiagAct t (Pi.mulSingle m ζ))
    (hζ1 : (ζ : F) ≠ 1) (hζinv : ((ζ : F))⁻¹ ≠ (ζ : F))
    {X : Vm n F} (hX : spinAction (quadMinus n F b c) t X = (ζ : F) • X) :
    X = X (Sum.inl m) • eVec n m := by
  classical
  set lam : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F := fun idx =>
    match idx with
    | Sum.inl i => if i = m then (ζ : F) else 1
    | Sum.inr (Sum.inl i) => if i = m then ((ζ : F))⁻¹ else 1
    | Sum.inr (Sum.inr _) => 1 with hlam
  have hstep : ∀ idx : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2,
      spinAction (quadMinus n F b c) t (Pi.single idx (1 : F) : Vm n F) =
        lam idx • Pi.single idx 1 := by
    intro idx
    rcases idx with i | i | j
    · have h := ht.1 i
      rw [show (Pi.single (Sum.inl i) (1 : F) : Vm n F) = minusVec n i true from rfl, h]
      congr 1
      by_cases hi : i = m <;> simp [hlam, Pi.mulSingle_apply, hi]
    · have h := ht.2.1 i
      rw [show (Pi.single (Sum.inr (Sum.inl i)) (1 : F) : Vm n F) = minusVec n i false from rfl, h]
      congr 1
      by_cases hi : i = m <;> simp [hlam, Pi.mulSingle_apply, hi]
    · have h := ht.2.2 (Pi.single j 1)
      rw [show (Pi.single (Sum.inr (Sum.inr j)) (1 : F) : Vm n F) = planeVec n (Pi.single j 1)
        from omk_single_plane j, h,
        show lam (Sum.inr (Sum.inr j)) = 1 from by rw [hlam], one_smul]
  have hT : ∀ Y : Vm n F, spinAction (quadMinus n F b c) t Y = fun idx => Y idx * lam idx := by
    intro Y
    conv_lhs => rw [omk_eq_sum_single Y]
    rw [map_sum]
    funext a
    rw [Finset.sum_apply,
      Finset.sum_eq_single a (fun e _ hea => by
        simp [map_smul, Pi.smul_apply, hstep, hea])
        (fun hmem => absurd (Finset.mem_univ a) hmem)]
    simp [map_smul, Pi.smul_apply, hstep, smul_eq_mul, mul_one]
  have hcoord : ∀ idx, X idx * lam idx = (ζ : F) * X idx := by
    intro idx
    have h := congrFun (hT X) idx
    rw [hX, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hzero : ∀ idx, lam idx ≠ (ζ : F) → X idx = 0 := by
    intro idx hne
    have h0 : (lam idx - (ζ : F)) * X idx = 0 := by
      rw [sub_mul, mul_comm (lam idx) (X idx), hcoord idx, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
  funext idx
  rcases idx with i | i | j
  · by_cases hi : i = m
    · rw [hi]
      simp [eVec]
    · rw [hzero (Sum.inl i) (by simp only [hlam]; rw [if_neg hi]; exact Ne.symm hζ1)]
      simp [eVec, hi]
  · by_cases hi : i = m
    · rw [hi]
      rw [hzero (Sum.inr (Sum.inl m)) (by simp only [hlam]; exact hζinv)]
      simp [eVec]
    · rw [hzero (Sum.inr (Sum.inl i)) (by simp only [hlam]; rw [if_neg hi]; exact Ne.symm hζ1)]
      simp [eVec, hi]
  · rw [hzero (Sum.inr (Sum.inr j)) (by simp only [hlam]; exact Ne.symm hζ1)]
    simp [eVec]

private theorem omk_inv_smul {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (e : V ≃ₗ[F] V) {v : V} {c : F} (hc : c ≠ 0) (h : e v = c • v) : e.symm v = c⁻¹ • v := by
  have h1 := congrArg e.symm h
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.map_smul] at h1
  calc e.symm v = c⁻¹ • (c • e.symm v) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • v := by rw [← h1]

private theorem omk_diagAct_eigenspace_f {n : ℕ} {F : Type} [Field F] {b c : F}
    {t : spinGroup (quadMinus n F b c)} {m : Fin (n - 1)} {ζ : Fˣ}
    (ht : PsiDiag.SpinM.DiagAct t (Pi.mulSingle m ζ))
    (hζ1 : ((ζ : F))⁻¹ ≠ 1) (hζinv : (ζ : F) ≠ ((ζ : F))⁻¹)
    {X : Vm n F} (hX : spinAction (quadMinus n F b c) t X = ((ζ : F))⁻¹ • X) :
    X = X (Sum.inr (Sum.inl m)) • fVec n m := by
  classical
  set lam : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F := fun idx =>
    match idx with
    | Sum.inl i => if i = m then (ζ : F) else 1
    | Sum.inr (Sum.inl i) => if i = m then ((ζ : F))⁻¹ else 1
    | Sum.inr (Sum.inr _) => 1 with hlam
  have hstep : ∀ idx : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2,
      spinAction (quadMinus n F b c) t (Pi.single idx (1 : F) : Vm n F) =
        lam idx • Pi.single idx 1 := by
    intro idx
    rcases idx with i | i | j
    · have h := ht.1 i
      rw [show (Pi.single (Sum.inl i) (1 : F) : Vm n F) = minusVec n i true from rfl, h]
      congr 1
      by_cases hi : i = m <;> simp [hlam, Pi.mulSingle_apply, hi]
    · have h := ht.2.1 i
      rw [show (Pi.single (Sum.inr (Sum.inl i)) (1 : F) : Vm n F) = minusVec n i false from rfl, h]
      congr 1
      by_cases hi : i = m <;> simp [hlam, Pi.mulSingle_apply, hi]
    · have h := ht.2.2 (Pi.single j 1)
      rw [show (Pi.single (Sum.inr (Sum.inr j)) (1 : F) : Vm n F) = planeVec n (Pi.single j 1)
        from omk_single_plane j, h,
        show lam (Sum.inr (Sum.inr j)) = 1 from by rw [hlam], one_smul]
  have hT : ∀ Y : Vm n F, spinAction (quadMinus n F b c) t Y = fun idx => Y idx * lam idx := by
    intro Y
    conv_lhs => rw [omk_eq_sum_single Y]
    rw [map_sum]
    funext a
    rw [Finset.sum_apply,
      Finset.sum_eq_single a (fun e _ hea => by
        simp [map_smul, Pi.smul_apply, hstep, hea])
        (fun hmem => absurd (Finset.mem_univ a) hmem)]
    simp [map_smul, Pi.smul_apply, hstep, smul_eq_mul, mul_one]
  have hcoord : ∀ idx, X idx * lam idx = ((ζ : F))⁻¹ * X idx := by
    intro idx
    have h := congrFun (hT X) idx
    rw [hX, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hzero : ∀ idx, lam idx ≠ ((ζ : F))⁻¹ → X idx = 0 := by
    intro idx hne
    have h0 : (lam idx - ((ζ : F))⁻¹) * X idx = 0 := by
      rw [sub_mul, mul_comm (lam idx) (X idx), hcoord idx, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
  funext idx
  rcases idx with i | i | j
  · by_cases hi : i = m
    · rw [hi]
      rw [hzero (Sum.inl m) (by simp only [hlam]; exact hζinv)]
      simp [fVec]
    · rw [hzero (Sum.inl i) (by simp only [hlam]; rw [if_neg hi]; exact Ne.symm hζ1)]
      simp [fVec, hi]
  · by_cases hi : i = m
    · rw [hi]
      simp [fVec]
    · rw [hzero (Sum.inr (Sum.inl i))
          (by simp only [hlam]; rw [if_neg hi]; exact Ne.symm hζ1)]
      simp [fVec, hi]
  · rw [hzero (Sum.inr (Sum.inr j)) (by simp only [hlam]; exact Ne.symm hζ1)]
    simp [fVec]

private theorem omk_diagAct_entries {n : ℕ} {F : Type} [Field F] {b c : F}
    {u : spinGroup (quadMinus n F b c)} {ρ ρ' : Fin (n - 1) → Fˣ}
    (h : PsiDiag.SpinM.DiagAct u ρ) (h' : PsiDiag.SpinM.DiagAct u ρ') : ρ = ρ' := by
  funext m
  refine Units.ext ?_
  have h2 := h'.1 m
  rw [h.1 m] at h2
  have h3 := congrFun h2 (Sum.inl m)
  simpa [Pi.smul_apply, smul_eq_mul, minusVec, eVec] using h3

private theorem omk_rLong_torus_mem {p n r f : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {k : Fin (r + 1)} (hk : k.val + 1 < r + 2 - 1) :
    κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ))) ∈ Bs := by
  classical
  have hirr : ∀ s : GaloisField 2 f, s ^ 2 + (minusCoeffs 2 f).1 * s + (minusCoeffs 2 f).2 ≠ 0 :=
    minusCoeffs_irr 2 f
  have htC : κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ))) ∈
      Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro hb hhb
    obtain ⟨s, hdiag, hconj⟩ := hF.2.2.2 ⟨hb, hhb⟩
    have hcomm : s * rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)) =
        rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)) * s :=
      omk_commute_of_diagAct hirr hdiag (omk_rLong_torus_diagAct hk (ggSecFiveBZeta χ))
    have hfix : s * rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)) * s⁻¹ =
        rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)) := by
      rw [hcomm]
      group
    have h1 : hb * κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ))) * hb⁻¹ =
        κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ))) := by
      have h2 := hconj (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)))
      rw [hfix] at h2
      exact h2
    calc hb * κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ))) =
        (hb * κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
          (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ))) *
            hb⁻¹) * hb := by group
      _ = κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
            (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ))) *
              hb := by rw [h1]
  refine hBs _ htC ?_
  have hp : (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)) ^
      p = 1 := by
    rw [← map_pow, ggSecFiveBZeta_pow_p (χ := χ), map_one]
  rw [← map_pow, ← map_pow, hp, map_one, map_one]

private theorem omk_eta_of_conj {p n r f : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ) (hr : 2 ≤ r) {b : ↥Bs}
    {u : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)}
    {ψ : Fin (r + 1) → (GaloisField 2 f)ˣ} (hdiag : PsiDiag.SpinM.DiagAct u ψ)
    (hconj : ∀ s, (b : G) * κ s * (b : G)⁻¹ = κ (u * s * u⁻¹)) :
    ∀ m, χ (eta b (π m.succ)) = ψ m := by
  obtain ⟨tb, htbd, htbc⟩ := hF.2.2.2 b
  have hcomm : ∀ s : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), tb * s * tb⁻¹ = u * s * u⁻¹ := by
    intro s
    refine hF.1 ?_
    rw [← htbc s, hconj s]
  have hcen : ∀ s : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), Commute (tb⁻¹ * u) s := by
    intro s
    have h := hcomm s
    show (tb⁻¹ * u) * s = s * (tb⁻¹ * u)
    calc tb⁻¹ * u * s = tb⁻¹ * (u * s * u⁻¹) * u := by group
      _ = tb⁻¹ * (tb * s * tb⁻¹) * u := by rw [h]
      _ = s * (tb⁻¹ * u) := by group
  have htriv : tb⁻¹ * u = 1 := by
    have hmem : tb⁻¹ * u ∈ Subgroup.center (spinGroup (quadMinus (r + 2) (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) := by
      rw [Subgroup.mem_center_iff]
      intro s
      first
        | exact (hcen s).eq
        | exact (hcen s).eq.symm
    rw [PsiDiag.SpinM.center_eq_bot (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2)
      (minusCoeffs_irr 2 f) (by omega : 4 ≤ r + 2), Subgroup.mem_bot] at hmem
    exact hmem
  have hu : u = tb := by
    have h := congrArg (fun x => tb * x) htriv
    simpa using h
  rw [hu] at hdiag
  intro m
  exact (congrFun (omk_diagAct_entries hdiag htbd) m).symm

private theorem omk_commutator_fix {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (e e' : V ≃ₗ[F] V) {v : V} (hv : v ≠ 0) {c c' : F}
    (h : e v = c • v) (h' : e' v = c' • v) : (e * e' * e⁻¹ * e'⁻¹) v = v := by
  have hc : c ≠ 0 := by
    intro h0
    apply hv
    have h1 := h
    rw [h0, zero_smul] at h1
    exact e.injective (by rw [h1, map_zero])
  have hc' : c' ≠ 0 := by
    intro h0
    apply hv
    have h1 := h'
    rw [h0, zero_smul] at h1
    exact e'.injective (by rw [h1, map_zero])
  have h2 : e'⁻¹ v = c'⁻¹ • v := omk_inv_smul e' hc' h'
  have h1 : e⁻¹ v = c⁻¹ • v := omk_inv_smul e hc h
  calc (e * e' * e⁻¹ * e'⁻¹) v = e (e' (e⁻¹ (e'⁻¹ v))) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    _ = e (e' (e⁻¹ (c'⁻¹ • v))) := by rw [h2]
    _ = c'⁻¹ • e (e' (e⁻¹ v)) := by simp only [map_smul]
    _ = c'⁻¹ • e (e' (c⁻¹ • v)) := by rw [h1]
    _ = (c'⁻¹ * c⁻¹) • e (e' v) := by simp only [map_smul, smul_smul]
    _ = (c'⁻¹ * c⁻¹) • e (c' • v) := by rw [h']
    _ = (c'⁻¹ * c⁻¹ * c') • e v := by simp only [map_smul, smul_smul]
    _ = (c'⁻¹ * c⁻¹ * c') • (c • v) := by rw [h]
    _ = ((c'⁻¹ * c⁻¹ * c') * c) • v := by simp only [smul_smul]
    _ = v := by
        rw [show (c'⁻¹ * c⁻¹ * c') * c = (c'⁻¹ * c') * (c⁻¹ * c) by ring,
          inv_mul_cancel₀ hc', inv_mul_cancel₀ hc, one_mul, one_smul]

end OmHelpers

theorem ggSecFiveBPermOm_rankOne_le_reflComm {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs K : Subgroup G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ) (k : Fin r) :
    (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup k.castSucc).map κ ≤
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π k.castSucc.succ) (π k.succ.succ) : Set G),
        Bs⁆ := by
  classical
  have hχ : Function.Injective χ := hF.2.2.1
  have hκ : Function.Injective κ := hF.1
  let b : GaloisField 2 f := (minusCoeffs 2 f).1
  let c : GaloisField 2 f := (minusCoeffs 2 f).2
  have hirr : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0 := minusCoeffs_irr 2 f
  let ζ : (GaloisField 2 f)ˣ := ggSecFiveBZeta χ
  have hζp : ζ ^ p = 1 := ggSecFiveBZeta_pow_p (χ := χ)
  have hζ2 : (ζ : GaloisField 2 f) ^ 2 ≠ 1 := ggSecFiveBZeta_sq_ne_one hp2 hχ
  have hk : k.castSucc.val + 1 < r + 2 - 1 := by
    have := k.isLt
    simp only [Fin.val_castSucc]
    omega
  have hRlin : (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup k.castSucc).map κ =
      (κ.comp (rLong (r + 2) b c hk)).range := by
    rw [rankOne_minusDatum_long hirr hk, ← MonoidHom.range_comp]
  have hRC : (κ.comp (rLong (r + 2) b c hk)).range ≤
      Subgroup.centralizer (ggBsCoordEq Bs eta (π k.castSucc.succ) (π k.succ.succ) : Set G) := by
    rintro _ ⟨m, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhBs : h ∈ Bs := ggBsCoordEq_le (π k.castSucc.succ) (π k.succ.succ) hh
    obtain ⟨t, hdiag, hconj⟩ := hF.2.2.2 ⟨h, hhBs⟩
    have hη : eta ⟨h, hhBs⟩ (π k.castSucc.succ) = eta ⟨h, hhBs⟩ (π k.succ.succ) :=
      (coe_mem_ggBsCoordEq (b := ⟨h, hhBs⟩)).1 hh
    have hpat : (fun m : Fin (r + 1) => χ (eta ⟨h, hhBs⟩ (π m.succ))) k.castSucc =
        (fun m : Fin (r + 1) => χ (eta ⟨h, hhBs⟩ (π m.succ))) k.succ := by
      show χ (eta ⟨h, hhBs⟩ (π k.castSucc.succ)) = χ (eta ⟨h, hhBs⟩ (π k.succ.succ))
      rw [hη]
    have hfix : t * rLong (r + 2) b c hk m * t⁻¹ = rLong (r + 2) b c hk m :=
      omk_conj_rLong_of_diagAct hk hdiag hpat m
    have h1 : h * κ (rLong (r + 2) b c hk m) * h⁻¹ = κ (rLong (r + 2) b c hk m) := by
      have h2 := hconj (rLong (r + 2) b c hk m)
      rw [hfix] at h2
      exact h2
    calc h * κ (rLong (r + 2) b c hk m) =
        (h * κ (rLong (r + 2) b c hk m) * h⁻¹) * h := by group
      _ = κ (rLong (r + 2) b c hk m) * h := by rw [h1]
  have ht₀B : κ (rLong (r + 2) b c hk
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) ζ)) ∈ Bs :=
    omk_rLong_torus_mem hF hBs hk
  have hRcomm : (κ.comp (rLong (r + 2) b c hk)).range ≤
      ⁅(κ.comp (rLong (r + 2) b c hk)).range, Subgroup.zpowers (κ (rLong (r + 2) b c hk
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) ζ)))⁆ :=
    ggRange_le_commutator_zpowers_torusHom (κ.comp (rLong (r + 2) b c hk)) hζ2
  rw [hRlin]
  exact hRcomm.trans (Subgroup.commutator_mono hRC (Subgroup.zpowers_le.mpr ht₀B))

section OmShort

variable {p n r f : ℕ} [Fact p.Prime] {Bs K : Subgroup G} {y : G}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
  {κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
    (minusCoeffs 2 f).2) →* G}
  {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}

private theorem omk_y_mem_coordZero (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ) (hr : 2 ≤ r)
    (hyB : y ∈ Bs) (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K) :
    y ∈ ggBsCoordZero Bs eta (π (Fin.last (r + 1))) := by
  rw [mem_ggBsCoordZero]
  refine ⟨hyB, ?_⟩
  have hconj : ∀ s : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2),
      ((⟨y, hyB⟩ : ↥Bs) : G) * κ s * ((⟨y, hyB⟩ : ↥Bs) : G)⁻¹ =
        κ ((1 : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2)) * s * 1⁻¹) := by
    intro s
    have hsK : κ s ∈ K := by rw [← hF.2.1]; exact ⟨s, rfl⟩
    have h1 : y * κ s = κ s * y := Subgroup.mem_centralizer_iff.mp (hK.1 hsK) y (by simp)
    rw [one_mul, inv_one, mul_one]
    calc ((⟨y, hyB⟩ : ↥Bs) : G) * κ s * ((⟨y, hyB⟩ : ↥Bs) : G)⁻¹ = y * κ s * y⁻¹ := rfl
      _ = (κ s * y) * y⁻¹ := by rw [h1]
      _ = κ s := by group
  have hentries := omk_eta_of_conj hF hr (b := ⟨y, hyB⟩) (u := 1) (ψ := 1)
    (PsiDiag.SpinM.diagAct_one (n := r + 2) (K := GaloisField 2 f) (b := (minusCoeffs 2 f).1)
      (c := (minusCoeffs 2 f).2)) hconj
  refine hF.2.2.1 ?_
  have h2 := hentries (Fin.last r)
  rw [Fin.succ_last] at h2
  rw [h2, Pi.one_apply, map_one]

private theorem omk_rLong_torus_mem_coordZero (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ)
    (hr : 2 ≤ r) (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {k : Fin (r + 1)} (hk : k.val + 1 < r + 2 - 1) (hkr : k.val + 1 < r) :
    κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ))) ∈
      ggBsCoordZero Bs eta (π (Fin.last (r + 1))) := by
  have hB := omk_rLong_torus_mem hF hBs hk
  rw [mem_ggBsCoordZero]
  refine ⟨hB, ?_⟩
  have hconj : ∀ s : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2),
      ((⟨_, hB⟩ : ↥Bs) : G) * κ s * ((⟨_, hB⟩ : ↥Bs) : G)⁻¹ =
        κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
            (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)) * s *
          (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
            (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f)
              (ggSecFiveBZeta χ)))⁻¹) := by
    intro s
    show κ _ * κ s * (κ _)⁻¹ = κ (_ * s * _⁻¹)
    rw [← map_inv, ← map_mul, ← map_mul]
  have hentries := omk_eta_of_conj hF hr (b := ⟨_, hB⟩)
    (u := rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)))
    (ψ := fun l => ggSecFiveBZeta χ ^ longCoroot k ⟨k.val + 1, hk⟩ true false l true)
    (omk_rLong_torus_diagAct hk (ggSecFiveBZeta χ)) hconj
  refine hF.2.2.1 ?_
  have h2 := hentries (Fin.last r)
  rw [Fin.succ_last] at h2
  have h3 : longCoroot k ⟨k.val + 1, hk⟩ true false (Fin.last r) true = 0 := by
    rw [longCoroot]
    have h1 : (Fin.last r) ≠ k := by
      intro hh
      have h4 := congrArg Fin.val hh
      simp only [Fin.val_last] at h4
      omega
    have h5 : (Fin.last r) ≠ (⟨k.val + 1, hk⟩ : Fin (r + 1)) := by
      intro hh
      have h4 := congrArg Fin.val hh
      simp only [Fin.val_last, Fin.val_mk] at h4
      omega
    rw [if_neg h1, if_neg h5, add_zero]
  rw [h2, h3, zpow_zero, map_one]

private theorem omk_diag_mem (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {τ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)}
    (hτ : PsiDiag.SpinM.DiagAct τ (Pi.mulSingle (Fin.last r) (ggSecFiveBZeta χ))) :
    κ τ ∈ Bs := by
  have hirr : ∀ s : GaloisField 2 f, s ^ 2 + (minusCoeffs 2 f).1 * s + (minusCoeffs 2 f).2 ≠ 0 :=
    minusCoeffs_irr 2 f
  have htC : κ τ ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro hb hhb
    obtain ⟨s, hdiag, hconj⟩ := hF.2.2.2 ⟨hb, hhb⟩
    have hcomm : s * τ = τ * s := omk_commute_of_diagAct hirr hdiag hτ
    have hfix : s * τ * s⁻¹ = τ := by rw [hcomm]; group
    have h1 : hb * κ τ * hb⁻¹ = κ τ := by
      have h2 := hconj τ
      rw [hfix] at h2
      exact h2
    calc hb * κ τ = (hb * κ τ * hb⁻¹) * hb := by group
      _ = κ τ * hb := by rw [h1]
  refine hBs _ htC ?_
  have hτpow : τ ^ p = 1 := by
    have h1 : PsiDiag.SpinM.DiagAct (τ ^ p) (1 : Fin (r + 1) → (GaloisField 2 f)ˣ) := by
      refine (omk_diagAct_pow hτ p).congr ?_
      rw [← Pi.mulSingle_pow, ggSecFiveBZeta_pow_p, Pi.mulSingle_one]
    exact omk_diagAct_unique (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2) (n := r + 2)
      hirr h1 (PsiDiag.SpinM.diagAct_one (n := r + 2) (K := GaloisField 2 f)
        (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2))
  rw [← map_pow, hτpow, map_one]

private theorem omk_eta_diag (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ) (hr : 2 ≤ r)
    {τ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)}
    (hτ : PsiDiag.SpinM.DiagAct τ (Pi.mulSingle (Fin.last r) (ggSecFiveBZeta χ)))
    (htB : κ τ ∈ Bs) (m : Fin (r + 1)) :
    eta ⟨κ τ, htB⟩ (π m.succ) = if m = Fin.last r then Multiplicative.ofAdd 1 else 1 := by
  have hconj : ∀ s : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2),
      ((⟨κ τ, htB⟩ : ↥Bs) : G) * κ s * ((⟨κ τ, htB⟩ : ↥Bs) : G)⁻¹ = κ (τ * s * τ⁻¹) := by
    intro s
    show κ τ * κ s * (κ τ)⁻¹ = κ (τ * s * τ⁻¹)
    rw [← map_inv, ← map_mul, ← map_mul]
  have hentries := omk_eta_of_conj hF hr (b := ⟨κ τ, htB⟩) (u := τ)
    (ψ := Pi.mulSingle (Fin.last r) (ggSecFiveBZeta χ)) hτ hconj m
  refine hF.2.2.1 ?_
  refine hentries.trans ?_
  by_cases hm : m = Fin.last r
  · rw [hm, Pi.mulSingle_eq_same, if_pos rfl]
  · rw [Pi.mulSingle_eq_of_ne hm, if_neg hm, map_one]

private theorem omk_centralizer_le_normalizer [Finite G]
    (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ) (hp2 : p ≠ 2) (hf : 2 ≤ f) (hr : 2 ≤ r)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K) :
    Subgroup.centralizer (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  have hζsq : ((ggSecFiveBZeta χ : (GaloisField 2 f)ˣ) : GaloisField 2 f) ^ 2 ≠ 1 :=
    ggSecFiveBZeta_sq_ne_one hp2 hF.2.2.1
  have hζ2U : (ggSecFiveBZeta χ : (GaloisField 2 f)ˣ) ^ 2 ≠ 1 := by
    intro h
    exact hζsq (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one])
  have hd0 : (0 : Fin (r + 1)).val + 1 < r + 2 - 1 := by
    show 0 + 1 < r + 1
    omega
  have hle : (0 : Fin (r + 1)).val + 1 < r := by
    show 0 + 1 < r
    omega
  have hne0 : (0 : Fin (r + 1)) ≠ Fin.last r := by
    intro h
    have h2 := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h2
    omega
  intro g hg
  let r' : G := κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hd0
    (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)))
  let J : Subgroup G := (κ.comp (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hd0)).range
  have hr'B : r' ∈ Bs := omk_rLong_torus_mem hF hBs hd0
  have hr'J : r' ∈ J := ⟨_, rfl⟩
  have hr'H : r' ∈ ggBsCoordZero Bs eta (π (Fin.last (r + 1))) :=
    omk_rLong_torus_mem_coordZero hF hr hBs hd0 hle
  have hJK : J ≤ K := by
    intro x hx
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← hF.2.1]
    exact ⟨rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hd0 s, rfl⟩
  have hval : r' = κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hd0
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ))) := rfl
  have hζ1 : ((ggSecFiveBZeta χ : (GaloisField 2 f)ˣ) : GaloisField 2 f) ≠ 1 :=
    fun h => ggSecFiveBZeta_ne_one hF.2.2.1 (Units.ext h)
  have hr'ne1 : r' ≠ 1 := by
    intro hh
    have h1 : rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hd0
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)) = 1 := by
      refine hF.1 ?_
      rw [← hval, hh, map_one]
    exact ggSecFiveBTorusHom_ne_one hζ1 (rLong_injective hd0 (by rw [h1, map_one]))
  have hr'pow : r' ^ p = 1 := by
    have hp : (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)) ^ p =
        1 := by rw [← map_pow, ggSecFiveBZeta_pow_p, map_one]
    rw [hval, ← map_pow, ← map_pow, hp, map_one, map_one]
  have hne : J ≠ ⊥ := by
    intro hbot
    have hmem : r' ∈ J := hr'J
    rw [hbot] at hmem
    exact hr'ne1 (by simpa using hmem)
  have hJq : CFSG.Assembly.IsQuasisimple ↥J :=
    CFSG.ClassicalInvolution.Balance.Q27.isQuasisimple_range_of_sl2
      (ggSecFiveBFour_le_card_galois hf) (κ.comp (rLong (r + 2) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2 hd0)) hne
  have hpJ : p ∣ Nat.card ↥J := by
    have h1 : orderOf r' = p := orderOf_eq_prime hr'pow hr'ne1
    have h2 : orderOf r' ∣ Nat.card ↥J := Subgroup.orderOf_dvd_natCard J hr'J
    rwa [h1] at h2
  have hr'C : r' ∉ Subgroup.centralizer (J : Set G) := by
    intro hmem
    rw [Subgroup.mem_centralizer_iff] at hmem
    have hcomm : κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hd0
        (CFSG.Timmesfeld.tv 0 1 1)) * r' =
        r' * κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hd0
          (CFSG.Timmesfeld.tv 0 1 1)) :=
      hmem _ (⟨CFSG.Timmesfeld.tv 0 1 1, rfl⟩ :
        κ (rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hd0
          (CFSG.Timmesfeld.tv 0 1 1)) ∈ J)
    have h3 : CFSG.Timmesfeld.tv 0 1 (1 : GaloisField 2 f) *
        CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ) =
        CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ) *
          CFSG.Timmesfeld.tv 0 1 (1 : GaloisField 2 f) := by
      have h5 : rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hd0
            (CFSG.Timmesfeld.tv 0 1 (1 : GaloisField 2 f) *
              CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ)) =
          rLong (r + 2) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hd0
            (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) (ggSecFiveBZeta χ) *
              CFSG.Timmesfeld.tv 0 1 (1 : GaloisField 2 f)) := by
        simp only [map_mul]
        exact hF.1 (by simp only [map_mul]; exact hcomm)
      exact rLong_injective hd0 h5
    rw [CFSG.ClassicalInvolution.WeakCT.tv01_eq_upperSL2,
      CFSG.ClassicalInvolution.Models.TwistedPairs.torusHom_eq_diagSL2] at h3
    have h6 := congrFun (congrFun (congrArg (fun M : SL(2, GaloisField 2 f) =>
      ((M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) h3) 0) 1
    simp only [CFSG.LocalAnalysis.EvenBN.U4.coe_upperSL2,
      CFSG.LocalAnalysis.EvenBN.U4.coe_diagSL2, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two] at h6
    have h7 : (ggSecFiveBZeta χ : (GaloisField 2 f)ˣ) = (ggSecFiveBZeta χ)⁻¹ := by
      refine Units.ext ?_
      first
        | simpa using h6
        | simpa using h6.symm
    exact hζ2U (by rw [pow_two]; nth_rewrite 2 [h7]; exact inv_mul_cancel _)
  have hgy : g ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact Subgroup.mem_centralizer_iff.mp hg y (omk_y_mem_coordZero hF hr hyB hK)
  have hgr' : g * r' = r' * g :=
    (Subgroup.mem_centralizer_iff.mp hg r' hr'H).symm
  exact ggMem_normalizer_of_pComponent hK hJK hJq hpJ hr'J hr'C hgy hgr'

private theorem omk_rankOne_short_le_centralizer
    (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ) :
    (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (Fin.last r)).map κ ≤
      Subgroup.centralizer (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G) := by
  have hirr : ∀ s : GaloisField 2 f,
      s ^ 2 + (minusCoeffs 2 f).1 * s + (minusCoeffs 2 f).2 ≠ 0 := minusCoeffs_irr 2 f
  have := fact_shortField hirr
  have hk : ¬ (Fin.last r).val + 1 < r + 2 - 1 := by
    rw [Fin.val_last]
    omega
  rw [rankOne_minusDatum_short hirr hk, ← MonoidHom.range_comp]
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhBs : h ∈ Bs := ggBsCoordZero_le (π (Fin.last (r + 1))) hh
  obtain ⟨t, hdiag, hconj⟩ := hF.2.2.2 ⟨h, hhBs⟩
  have hη : eta ⟨h, hhBs⟩ (π (Fin.last (r + 1))) = 1 :=
    (coe_mem_ggBsCoordZero (b := ⟨h, hhBs⟩)).mp hh
  have hχlast : (fun m : Fin (r + 1) => χ (eta ⟨h, hhBs⟩ (π m.succ))) (Fin.last r) = 1 := by
    show χ (eta ⟨h, hhBs⟩ (π (Fin.last r).succ)) = 1
    rw [Fin.succ_last, hη, map_one]
  have he : spinAction (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) t (eVec (r + 2) (Fin.last r)) =
      (1 : GaloisField 2 f) • eVec (r + 2) (Fin.last r) := by
    have h := hdiag.1 (Fin.last r)
    simp only [hχlast] at h
    simpa using h
  have hf : spinAction (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) t (fVec (r + 2) (Fin.last r)) =
      (1 : GaloisField 2 f) • fVec (r + 2) (Fin.last r) := by
    have h := hdiag.2.1 (Fin.last r)
    simp only [hχlast] at h
    simpa using h
  have hhom : (MulAut.conj t).toMonoidHom.comp (shortBlock hirr (r + 2) (Fin.last r)) =
      shortBlock hirr (r + 2) (Fin.last r) := by
    refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [shortBlock_tv01 (hirr := hirr) (n := r + 2) (k := Fin.last r) (t := c)]
      rw [conj_shortPosHom_of_eVec (n := r + 2) (hirr := hirr) t (Fin.last r)
        (p := fieldCoord c) (q := fieldCoord c) (r := 1) he (hdiag.2.2 _)]
      simp
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [shortBlock_tv10 (hirr := hirr) (n := r + 2) (k := Fin.last r) (t := c)]
      rw [conj_shortNegHom_of_fVec (n := r + 2) (hirr := hirr) t (Fin.last r)
        (p := starCoord c) (q := starCoord c) (r := 1) hf (hdiag.2.2 _)]
      simp
  have hfix : t * shortBlock hirr (r + 2) (Fin.last r) A * t⁻¹ =
      shortBlock hirr (r + 2) (Fin.last r) A := by
    simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      using DFunLike.congr_fun hhom A
  have h1 : h * κ (shortBlock hirr (r + 2) (Fin.last r) A) * h⁻¹ =
      κ (shortBlock hirr (r + 2) (Fin.last r) A) := by
    have h2 := hconj (shortBlock hirr (r + 2) (Fin.last r) A)
    rw [hfix] at h2
    exact h2
  calc h * κ (shortBlock hirr (r + 2) (Fin.last r) A) =
        (h * κ (shortBlock hirr (r + 2) (Fin.last r) A) * h⁻¹) * h := by group
    _ = κ (shortBlock hirr (r + 2) (Fin.last r) A) * h := by rw [h1]

private theorem omk_commutator_le_rankOne_short (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ)
    (hp2 : p ≠ 2) (hr : 2 ≤ r) :
    ⁅K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G),
        K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G)⁆ ≤
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (Fin.last r)).map κ := by
  classical
  let b : GaloisField 2 f := (minusCoeffs 2 f).1
  let c : GaloisField 2 f := (minusCoeffs 2 f).2
  have hirr : ∀ x : GaloisField 2 f, x ^ 2 + b * x + c ≠ 0 := minusCoeffs_irr 2 f
  let ζ : (GaloisField 2 f)ˣ := ggSecFiveBZeta χ
  have hκ : Function.Injective κ := hF.1
  have hχ : Function.Injective χ := hF.2.2.1
  set H : Subgroup G := ggBsCoordZero Bs eta (π (Fin.last (r + 1))) with hH
  set S : Subgroup (spinGroup (quadMinus (r + 2) (GaloisField 2 f) b c)) :=
    (K ⊓ Subgroup.centralizer (H : Set G)).comap κ with hS
  have hle : K ⊓ Subgroup.centralizer (H : Set G) ≤ κ.range := by
    rw [hF.2.1]
    exact inf_le_left
  have hKS : K ⊓ Subgroup.centralizer (H : Set G) = S.map κ := by
    rw [hS]
    exact (Subgroup.map_comap_eq_self (f := κ) hle).symm
  have hscale : ∀ u ∈ S, ∀ i : Fin (r + 2 - 1), i.val + 1 < r + 2 - 1 → ∀ σ : Bool,
      ∃ e : GaloisField 2 f,
        spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u (minusVec (r + 2) i σ) =
          e • minusVec (r + 2) i σ := by
    intro u hu i hi σ
    set bb : ↥Bs := eta.symm (Pi.mulSingle (π i.succ) (Multiplicative.ofAdd 1)) with hbb
    have hbval : eta bb = Pi.mulSingle (π i.succ) (Multiplicative.ofAdd 1) := by
      rw [hbb, MulEquiv.apply_symm_apply]
    have hne : π (Fin.last (r + 1)) ≠ π i.succ := by
      intro h
      have h2 := congrArg Fin.val (π.injective h)
      simp only [Fin.val_succ, Fin.val_last] at h2
      omega
    have hbH : (bb : G) ∈ H := by
      rw [hH, mem_ggBsCoordZero]
      refine ⟨bb.2, ?_⟩
      rw [show (⟨(bb : G), bb.2⟩ : ↥Bs) = bb from rfl, hbval]
      exact Pi.mulSingle_eq_of_ne hne _
    have hu' : κ u ∈ K ⊓ Subgroup.centralizer (H : Set G) := by
      simpa [hS] using hu
    have hcu : κ u ∈ Subgroup.centralizer (H : Set G) := hu'.2
    have hcomm : (bb : G) * κ u = κ u * (bb : G) :=
      (Subgroup.mem_centralizer_iff.mp hcu) (bb : G) hbH
    obtain ⟨t, ht, hconj⟩ := hF.2.2.2 bb
    have hconj' : (bb : G) * κ u * (bb : G)⁻¹ = κ u := by
      calc (bb : G) * κ u * (bb : G)⁻¹ = (κ u * (bb : G)) * (bb : G)⁻¹ := by rw [hcomm]
        _ = κ u := by group
    have htu : t * u = u * t := by
      have h1 : t * u * t⁻¹ = u := hκ (by rw [← hconj u, hconj'])
      calc t * u = (t * u * t⁻¹) * t := by group
        _ = u * t := by rw [h1]
    have hpat : (fun m : Fin (r + 1) => χ (eta bb (π m.succ))) = Pi.mulSingle i ζ := by
      funext m
      rw [hbval]
      by_cases hm : m = i
      · subst hm
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · have hne₂ : π m.succ ≠ π i.succ := fun h => hm (Fin.succ_inj.mp (π.injective h))
        rw [Pi.mulSingle_eq_of_ne hne₂, map_one, Pi.mulSingle_eq_of_ne hm]
    have ht' : PsiDiag.SpinM.DiagAct t (Pi.mulSingle i ζ) := ht.congr hpat
    have hζ1 : (ζ : GaloisField 2 f) ≠ 1 := fun h =>
      ggSecFiveBZeta_ne_one hχ (Units.ext h)
    have hζinv : ((ζ : GaloisField 2 f))⁻¹ ≠ (ζ : GaloisField 2 f) := by
      intro h
      apply ggSecFiveBZeta_sq_ne_one hp2 hχ
      have h1 : (ζ : GaloisField 2 f) * (ζ : GaloisField 2 f) = 1 := by
        calc (ζ : GaloisField 2 f) * (ζ : GaloisField 2 f) =
            ((ζ : GaloisField 2 f))⁻¹ * (ζ : GaloisField 2 f) := by rw [h]
          _ = 1 := inv_mul_cancel₀ (Units.ne_zero ζ)
      simpa [pow_two] using h1
    have hζ1' : ((ζ : GaloisField 2 f))⁻¹ ≠ 1 := fun h => hζ1 (inv_eq_one.mp h)
    have hζinv' : (ζ : GaloisField 2 f) ≠ ((ζ : GaloisField 2 f))⁻¹ :=
      fun h => hζinv h.symm
    have hte : spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) t (minusVec (r + 2) i true) =
        (ζ : GaloisField 2 f) • minusVec (r + 2) i true := by
      simpa [Pi.mulSingle_eq_same] using ht'.1 i
    have htf : spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) t (minusVec (r + 2) i false) =
        ((ζ : GaloisField 2 f))⁻¹ • minusVec (r + 2) i false := by
      simpa [Pi.mulSingle_eq_same, Units.val_inv_eq_inv_val] using ht'.2.1 i
    cases σ
    · refine ⟨spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u (minusVec (r + 2) i false)
        (Sum.inr (Sum.inl i)), ?_⟩
      have hX : spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) t
          (spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u (minusVec (r + 2) i false)) =
          ((ζ : GaloisField 2 f))⁻¹ •
            spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u
              (minusVec (r + 2) i false) := by
        calc spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) t
              (spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u (minusVec (r + 2) i false))
            = spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) (t * u)
                (minusVec (r + 2) i false) := by
              rw [← LinearEquiv.mul_apply, ← map_mul]
          _ = spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) (u * t)
                (minusVec (r + 2) i false) := by
              rw [htu]
          _ = spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u
                (spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) t
                  (minusVec (r + 2) i false)) := by
              rw [map_mul, LinearEquiv.mul_apply]
          _ = spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u
                (((ζ : GaloisField 2 f))⁻¹ • minusVec (r + 2) i false) := by rw [htf]
          _ = ((ζ : GaloisField 2 f))⁻¹ •
                spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u
                  (minusVec (r + 2) i false) := by
              rw [map_smul]
      have h := omk_diagAct_eigenspace_f (n := r + 2) (b := b) (c := c) ht' hζ1' hζinv' hX
      simpa [minusVec] using h
    · refine ⟨spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u
        (minusVec (r + 2) i true) (Sum.inl i), ?_⟩
      have hX : spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) t
          (spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u (minusVec (r + 2) i true)) =
          (ζ : GaloisField 2 f) •
            spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u
              (minusVec (r + 2) i true) := by
        calc spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) t
              (spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u (minusVec (r + 2) i true))
            = spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) (t * u)
                (minusVec (r + 2) i true) := by
              rw [← LinearEquiv.mul_apply, ← map_mul]
          _ = spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) (u * t)
                (minusVec (r + 2) i true) := by
              rw [htu]
          _ = spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u
                (spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) t
                  (minusVec (r + 2) i true)) := by
              rw [map_mul, LinearEquiv.mul_apply]
          _ = spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u
                ((ζ : GaloisField 2 f) • minusVec (r + 2) i true) := by rw [hte]
          _ = (ζ : GaloisField 2 f) •
                spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) u
                  (minusVec (r + 2) i true) := by
              rw [map_smul]
      have h := omk_diagAct_eigenspace (n := r + 2) (b := b) (c := c) ht' hζ1 hζinv hX
      simpa [minusVec] using h
  have hSS : ⁅S, S⁆ ≤ CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup
      (Fin.last r) := by
    rw [Subgroup.commutator_le]
    intro s hs s' hs'
    have hfix : ∀ i : Fin (r + 2 - 1), i.val + 1 < r + 2 - 1 → ∀ σ : Bool,
        spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) ⁅s, s'⁆ (minusVec (r + 2) i σ) =
          minusVec (r + 2) i σ := by
      intro i hi σ
      obtain ⟨e, he⟩ := hscale s hs i hi σ
      obtain ⟨e', he'⟩ := hscale s' hs' i hi σ
      have hv : (minusVec (r + 2) i σ : Vm (r + 2) (GaloisField 2 f)) ≠ 0 := by
        cases σ
        · intro h0
          have h1 := congrFun h0 (Sum.inr (Sum.inl i))
          simp only [minusVec, fVec, Pi.single_eq_same, Pi.zero_apply] at h1
          exact one_ne_zero h1
        · intro h0
          have h1 := congrFun h0 (Sum.inl i)
          simp only [minusVec, eVec, Pi.single_eq_same, Pi.zero_apply] at h1
          exact one_ne_zero h1
      have h := omk_commutator_fix (spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) s)
        (spinAction (quadMinus (r + 2) (GaloisField 2 f) b c) s') hv he he'
      simpa [map_commutatorElement, commutatorElement_def] using h
    have hmem : ⁅s, s'⁆ ∈ CurtisTits.rankOne (minusRootGroup (r + 2) hirr)
        (Fin.last r) := by
      have hidx : (Fin.last r : Fin (r + 2 - 1)) = ⟨r + 2 - 2, by omega⟩ :=
        Fin.ext rfl
      rw [hidx]
      exact KGPosOm.mem_rankOne_short_of_fix_lt (F := GaloisField 2 f) (b := b) (c := c)
        (hirr := hirr) (n := r + 2) (by omega) hfix
    exact hmem
  calc ⁅K ⊓ Subgroup.centralizer (H : Set G), K ⊓ Subgroup.centralizer (H : Set G)⁆
      = ⁅S.map κ, S.map κ⁆ := by rw [hKS]
    _ = ⁅S, S⁆.map κ := by rw [← Subgroup.map_commutator]
    _ ≤ (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.last r)).map κ :=
        Subgroup.map_mono hSS

private theorem omk_shortTorusElt_mem_rankOne
    (ρ : (GaloisField 2 f)ˣ) :
    shortTorusElt (r + 2) (minusCoeffs_irr 2 f) (Fin.last r)
        ((ρ : GaloisField 2 f) • planeOne) ∈
      CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup (Fin.last r) := by
  have hirr : ∀ s : GaloisField 2 f,
      s ^ 2 + (minusCoeffs 2 f).1 * s + (minusCoeffs 2 f).2 ≠ 0 := minusCoeffs_irr 2 f
  have := fact_shortField hirr
  have hk : ¬ (Fin.last r).val + 1 < r + 2 - 1 := by
    rw [Fin.val_last]
    omega
  rw [rankOne_minusDatum_short hirr hk]
  refine ⟨torusHom (ShortField (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
    (Units.map (algebraMap (GaloisField 2 f)
      (ShortField (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).toMonoidHom ρ), ?_⟩
  rw [shortBlock_torus, Units.coe_map]
  rw [← fieldCoord_algebraMap (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2)
    (K := GaloisField 2 f) (r := (ρ : GaloisField 2 f))]
  rfl

private theorem omk_rankOne_short_le_commutator
    (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ) {ρ : (GaloisField 2 f)ˣ}
    (hρ : ρ ^ 2 = ggSecFiveBZeta χ) :
    (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (Fin.last r)).map κ ≤
      ⁅(CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
          (Fin.last r)).map κ,
        Subgroup.zpowers (κ (shortTorusElt (r + 2) (minusCoeffs_irr 2 f) (Fin.last r)
          ((ρ : GaloisField 2 f) • planeOne)))⁆ := by
  have hirr : ∀ s : GaloisField 2 f,
      s ^ 2 + (minusCoeffs 2 f).1 * s + (minusCoeffs 2 f).2 ≠ 0 := minusCoeffs_irr 2 f
  have := fact_shortField hirr
  have hk : ¬ (Fin.last r).val + 1 < r + 2 - 1 := by
    rw [Fin.val_last]
    omega
  let t : (ShortField (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)ˣ :=
    Units.map (algebraMap (GaloisField 2 f)
      (ShortField (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).toMonoidHom ρ
  have hval : ((ρ : GaloisField 2 f)) ^ 2 =
      ((ggSecFiveBZeta χ : (GaloisField 2 f)ˣ) : GaloisField 2 f) := by
    rw [← Units.val_pow_eq_pow_val, hρ]
  have hζ2 :
      ((t : ShortField (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ^ 2 ≠ 1 := by
    intro h
    change (algebraMap (GaloisField 2 f)
      (ShortField (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        (ρ : GaloisField 2 f)) ^ 2 = 1 at h
    have h2 : ((ggSecFiveBZeta χ : (GaloisField 2 f)ˣ) : GaloisField 2 f) = 1 := by
      apply (algebraMap (GaloisField 2 f)
        (ShortField (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).injective
      rw [map_one, ← hval, map_pow]
      exact h
    exact ggSecFiveBZeta_ne_one hF.2.2.1 (Units.ext h2)
  rw [rankOne_minusDatum_short hirr hk, ← MonoidHom.range_comp]
  have hτ : κ (shortTorusElt (r + 2) hirr (Fin.last r)
      ((ρ : GaloisField 2 f) • planeOne)) =
      (κ.comp (shortBlock hirr (r + 2) (Fin.last r)))
        (torusHom (ShortField (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) t) := by
    rw [MonoidHom.comp_apply, shortBlock_torus (hirr := hirr) (n := r + 2)
      (k := Fin.last r) (t := t), Units.coe_map]
    rw [← fieldCoord_algebraMap (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2)
      (K := GaloisField 2 f) (r := (ρ : GaloisField 2 f))]
    rfl
  rw [hτ]
  exact ggRange_le_commutator_zpowers_torusHom
    (κ.comp (shortBlock hirr (r + 2) (Fin.last r))) hζ2

end OmShort

theorem ggSecFiveBPermOm_singletonComm_K [Finite G] {p n r f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 2 ≤ f) (hr : 2 ≤ r) {Bs K : Subgroup G} {y : G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermLinOmKFrame Bs K eta π κ χ) :
    ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G), Bs⁆ =
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (Fin.last r)).map κ := by
  obtain ⟨ρ, hρ⟩ := PsiDiag.SpinM.exists_sq_eq (ggSecFiveBZeta χ)
  have hτ : PsiDiag.SpinM.DiagAct (shortTorusElt (r + 2) (minusCoeffs_irr 2 f) (Fin.last r)
      ((ρ : GaloisField 2 f) • planeOne)) (Pi.mulSingle (Fin.last r) (ggSecFiveBZeta χ)) := by
    rw [← hρ]
    exact PsiDiag.SpinM.diagAct_shortTorusElt (n := r + 2) (minusCoeffs_irr 2 f) (Fin.last r) ρ
  have hτR := omk_shortTorusElt_mem_rankOne (r := r) ρ
  set τ := shortTorusElt (r + 2) (minusCoeffs_irr 2 f) (Fin.last r)
    ((ρ : GaloisField 2 f) • planeOne)
  set R := (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
    (Fin.last r)).map κ
  set H := ggBsCoordZero Bs eta (π (Fin.last (r + 1)))
  have htB : κ τ ∈ Bs := omk_diag_mem hF hBs hτ
  have hRC : R ≤ Subgroup.centralizer (H : Set G) := omk_rankOne_short_le_centralizer hF
  have hRt : R ≤ ⁅R, Subgroup.zpowers (κ τ)⁆ := omk_rankOne_short_le_commutator hF hρ
  have hRD : R ≤ K ⊓ Subgroup.centralizer (H : Set G) :=
    le_inf ((Subgroup.map_le_range κ _).trans hF.2.1.le) hRC
  have htR : κ τ ∈ R := Subgroup.mem_map_of_mem κ hτR
  have ht : κ τ ∈ ⁅K ⊓ Subgroup.centralizer (H : Set G), K ⊓ Subgroup.centralizer (H : Set G)⁆ :=
    Subgroup.commutator_mono hRD (Subgroup.zpowers_le.mpr (hRD htR)) (hRt htR)
  have hgen := ggSecFiveBHgen_long htB (omk_eta_diag hF hr hτ htB)
  rw [Fin.succ_last] at hgen
  exact ggCommutator_centralizer_eq (E := Bs) (H := H) (X := K) (R := R) (t := κ τ) hBc
    (ggBsCoordZero_le _) htB hgen (omk_centralizer_le_normalizer hF hp2 hf hr hBs hyB hK) ht
    (omk_commutator_le_rankOne_short hF hp2 hr) hRC hRt

end CFSG.StandardType

end
