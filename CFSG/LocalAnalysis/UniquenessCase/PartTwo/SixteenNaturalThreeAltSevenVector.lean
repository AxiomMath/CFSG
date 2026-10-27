module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Set
public import CFSG.Quasithin.Background.B4Models
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEndA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatIrr
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrNat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltEquiv
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltNorm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
import CFSG.LocalAnalysis.RankThreeUC.GN15AltBaumComb
import CFSG.LocalAnalysis.RankThreeUC.GN15AltBlockMod
import CFSG.Quasithin.H13.A7NatSix
import CFSG.GroupTheory.AlternatingThreeRank
import CFSG.CGT.PushingUpLit.BHS5.FiveFive
import CFSG.ClassicalGroups.Symplectic.StatedSpTransport
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.RankThreeUC.GN15AltBaumMod
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Irr
import CFSG.Quasithin.Background.C124B51Hyp
import CFSG.Quasithin.Background.C124BlkTransfer
import CFSG.Quasithin.Background.C124InterfaceDefs
import CFSG.Quasithin.Background.C1GNC124
import CFSG.Quasithin.Background.F918V2Defs
import CFSG.Quasithin.Background.F918V2GDA
import CFSG.Quasithin.EmptyFaithful.SmithD391Main
import CFSG.Quasithin.H13.A7IrrPlus
import CFSG.Quasithin.H13.A7NatAssembly
import CFSG.Quasithin.Vol2.Ch12Sec2Statements
import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523
import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523F
import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
import CFSG.Quasithin.Vol2.Ch6Defs
import CFSG.Quasithin.Vol2.Ch6Vocab
import CFSG.RankThree.GF2n.Stroth80.Sec41
import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
import CFSG.RankThree.OrthogonalInvolutions.Witt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Equiv CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique
open CFSG.RankThree.PartTwo (altHeart evenWeightPerm)
open CFSG.RankThree.PartTwo.Sec19.SolEven (altAct_eq_iff)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (altAct altAct_mk)
open CFSG.Quasithin.H13.A7 (altLift6 altLift6_apply_last altLift6_injective)
open CFSG.LocalAnalysis.WeakClosure81 (stableUnder_fixV stableUnder_commSub)
open CFSG.LocalAnalysis.RankThreeUC.S15.GN15
  (altBaumY altBaumY_ne_zero altBaumY_injective evenWeightPerm_altBaumY
    altHeart_mk_injective)

private noncomputable def altHeartVec (j : Fin 7) : altHeart 7 :=
  ((altBaumY (show Odd 7 from ⟨3, by norm_num⟩) j : evenWeight 7) : altHeart 7)

private theorem altHeartVec_ne_zero (j : Fin 7) : altHeartVec j ≠ 0 := by
  intro h
  have hzero : altBaumY (show Odd 7 from ⟨3, by norm_num⟩) j = 0 :=
    altHeart_mk_injective (show Odd 7 from ⟨3, by norm_num⟩)
      (by simpa [altHeartVec] using h)
  exact altBaumY_ne_zero (show Odd 7 from ⟨3, by norm_num⟩) (by norm_num : 2 ≤ 7) j hzero

private theorem altHeartVec_injective : Function.Injective altHeartVec := by
  intro j k h
  exact altBaumY_injective (show Odd 7 from ⟨3, by norm_num⟩)
    (altHeart_mk_injective (show Odd 7 from ⟨3, by norm_num⟩)
      (by simpa [altHeartVec] using h))

private theorem altAct_altHeartVec (σ : Perm (Fin 7)) (j : Fin 7) :
    altAct σ (altHeartVec j) = altHeartVec (σ j) := by
  show altAct σ ((altBaumY (show Odd 7 from ⟨3, by norm_num⟩) j : evenWeight 7) : altHeart 7) =
    ((altBaumY (show Odd 7 from ⟨3, by norm_num⟩) (σ j) : evenWeight 7) : altHeart 7)
  rw [altAct_mk]
  exact congrArg (fun x : evenWeight 7 => (x : altHeart 7))
    (evenWeightPerm_altBaumY (show Odd 7 from ⟨3, by norm_num⟩) σ j)

private noncomputable def sevenVec {W : Type} [CommGroup W] {I : Subgroup W}
    (ψ : ↥I ≃* Multiplicative (altHeart 7)) (j : Fin 7) : ↥I :=
  ψ.symm (Multiplicative.ofAdd (altHeartVec j))

private theorem sevenVec_injective {W : Type} [CommGroup W] {I : Subgroup W}
    (ψ : ↥I ≃* Multiplicative (altHeart 7)) :
    Function.Injective (fun j : Fin 7 => ((sevenVec ψ j : ↥I) : W)) := by
  intro j k h
  apply altHeartVec_injective
  have hsub : sevenVec ψ j = sevenVec ψ k := Subtype.ext h
  have hψ : Multiplicative.ofAdd (altHeartVec j) = Multiplicative.ofAdd (altHeartVec k) := by
    simpa [sevenVec] using congrArg ψ hsub
  simpa using hψ

private theorem sevenVec_ne_one {W : Type} [CommGroup W] {I : Subgroup W}
    (ψ : ↥I ≃* Multiplicative (altHeart 7)) (j : Fin 7) :
    ((sevenVec ψ j : ↥I) : W) ≠ 1 := by
  intro h
  have hsub : sevenVec ψ j = 1 := Subtype.ext h
  have hψ : Multiplicative.ofAdd (altHeartVec j) = 1 := by
    simpa [sevenVec] using congrArg ψ hsub
  have hz : altHeartVec j = 0 := by simpa using hψ
  exact altHeartVec_ne_zero j hz

private theorem sevenVec_fixed_of_fixes_point
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {I : Subgroup W}
    {π : alternatingGroup (Fin 7) →* ↥H}
    {ψ : ↥I ≃* Multiplicative (altHeart 7)}
    (hψ : ∀ (γ : alternatingGroup (Fin 7)) (u : ↥I)
        (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ I),
        ψ ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd (altAct (γ : Perm (Fin 7))
            (Multiplicative.toAdd (ψ u))))
    (hIinv : ∀ h : ↥H, ∀ u ∈ I, (h : MulAut W) u ∈ I)
    (j : Fin 7) (σ : alternatingGroup (Fin 7)) (hσj : (σ : Perm (Fin 7)) j = j) :
    ((π σ : ↥H) : MulAut W) ((sevenVec ψ j : ↥I) : W) = ((sevenVec ψ j : ↥I) : W) := by
  let u : ↥I := sevenVec ψ j
  have hmem : ((π σ : ↥H) : MulAut W) (u : W) ∈ I := hIinv (π σ) (u : W) u.2
  have h1 := hψ σ u hmem
  have hu : Multiplicative.toAdd (ψ u) = altHeartVec j := by
    simp [u, sevenVec]
  have hfix : altAct (σ : Perm (Fin 7)) (Multiplicative.toAdd (ψ u)) = altHeartVec j := by
    rw [hu, altAct_altHeartVec, hσj]
  have h2 : ψ ⟨((π σ : ↥H) : MulAut W) (u : W), hmem⟩ = ψ u := by
    rw [h1, hfix]
    simp [u, sevenVec]
  have h3 : (⟨((π σ : ↥H) : MulAut W) (u : W), hmem⟩ : ↥I) = u := ψ.injective h2
  exact congrArg Subtype.val h3

private theorem altNatural_induced_normalizer
    {W : Type} [CommGroup W] [Finite W]
    {H T : Subgroup (MulAut W)} {I : Subgroup W}
    (hTH : T ≤ Subgroup.normalizer (H : Set (MulAut W)))
    (hTI : StableUnder T I)
    {π : alternatingGroup (Fin 7) →* ↥H} (hπ : Function.Surjective π)
    {ψ : ↥I ≃* Multiplicative (altHeart 7)}
    (hψ : ∀ (γ : alternatingGroup (Fin 7)) (u : ↥I)
        (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ I),
        ψ ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd (altAct (γ : Perm (Fin 7))
            (Multiplicative.toAdd (ψ u))))
    (hIinv : ∀ h : ↥H, ∀ u ∈ I, (h : MulAut W) u ∈ I)
    {t : MulAut W} (ht : t ∈ T) :
    ∃ (tH : altHeart 7 ≃+ altHeart 7) (πt : Perm (Fin 7)),
      (∀ σ ∈ alternatingGroup (Fin 7), ∃ σ' ∈ alternatingGroup (Fin 7),
        ∀ v, tH (altAct σ v) = altAct σ' (tH v)) ∧
      (∀ v, tH v = altAct πt v) ∧
      (∀ u : ↥I, tH (Multiplicative.toAdd (ψ u)) =
        Multiplicative.toAdd (ψ ⟨t (u : W), hTI t ht (u : W) u.2⟩)) := by
  classical
  have htI : I.map t.toMonoidHom = I := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact hTI t ht y hy
    · intro x hx
      exact Subgroup.mem_map.mpr ⟨t⁻¹ x, hTI t⁻¹ (T.inv_mem ht) x hx, by simp⟩
  have htIinv : I.map t⁻¹.toMonoidHom = I := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact hTI t⁻¹ (T.inv_mem ht) y hy
    · intro x hx
      exact Subgroup.mem_map.mpr ⟨t x, hTI t ht x hx, by simp⟩
  let xI : ↥I ≃* ↥I :=
    { toFun := fun u =>
        ⟨t (u : W), by
          have h : t (u : W) ∈ I.map t.toMonoidHom :=
            Subgroup.mem_map.mpr ⟨u, u.2, rfl⟩
          rwa [htI] at h⟩
      invFun := fun u =>
        ⟨t⁻¹ (u : W), by
          have h : t⁻¹ (u : W) ∈ I.map t⁻¹.toMonoidHom :=
            Subgroup.mem_map.mpr ⟨u, u.2, rfl⟩
          rwa [htIinv] at h⟩
      left_inv := fun u => Subtype.ext (MulAut.inv_apply_self W t (u : W))
      right_inv := fun u => Subtype.ext (MulAut.apply_inv_self W t (u : W))
      map_mul' := fun u v => Subtype.ext (map_mul t (u : W) (v : W)) }
  let T' : Multiplicative (altHeart 7) ≃* Multiplicative (altHeart 7) :=
    ψ.symm.trans (xI.trans ψ)
  let tH : altHeart 7 ≃+ altHeart 7 := AddEquiv.toMultiplicative.symm T'
  have htH_apply : ∀ u : ↥I, tH (Multiplicative.toAdd (ψ u)) =
      Multiplicative.toAdd (ψ (xI u)) := by
    intro u
    show Multiplicative.toAdd (T' (Multiplicative.ofAdd
      (Multiplicative.toAdd (ψ u)))) = Multiplicative.toAdd (ψ (xI u))
    rw [ofAdd_toAdd]
    simp only [T', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hnorm : ∀ σ ∈ alternatingGroup (Fin 7), ∃ σ' ∈ alternatingGroup (Fin 7),
      ∀ v, tH (altAct σ v) = altAct σ' (tH v) := by
    intro σ hσ
    let γ : alternatingGroup (Fin 7) := ⟨σ, hσ⟩
    let g : MulAut W := ((π γ : ↥H) : MulAut W)
    have hgH : g ∈ H := (π γ).2
    have hconj : MulAut.conj t g ∈ H := by
      simpa [MulAut.conj_apply] using conj_mem_of_mem_normalizer (hTH ht) hgH
    obtain ⟨γ', hγ'⟩ := hπ ⟨MulAut.conj t g, hconj⟩
    have hγ'val : ((π γ' : ↥H) : MulAut W) = MulAut.conj t g := congrArg Subtype.val hγ'
    have hxg : ∀ e : W, ((π γ' : ↥H) : MulAut W) (t e) = t (g e) := by
      intro e
      rw [hγ'val, MulAut.conj_apply]
      simp [MulAut.mul_apply]
    refine ⟨(γ' : Perm (Fin 7)), γ'.2, ?_⟩
    intro v
    obtain ⟨u, hu⟩ : ∃ u : ↥I, Multiplicative.toAdd (ψ u) = v := by
      obtain ⟨u, hu⟩ := ψ.surjective (Multiplicative.ofAdd v)
      exact ⟨u, by rw [hu, toAdd_ofAdd]⟩
    have hgmem : g (u : W) ∈ I := hIinv ⟨g, hgH⟩ (u : W) u.2
    have htmem : t (u : W) ∈ I := hTI t ht (u : W) u.2
    have hg'mem : ((π γ' : ↥H) : MulAut W) (t (u : W)) ∈ I := hIinv (π γ') _ htmem
    have hh : ψ ⟨g (u : W), hgmem⟩ = Multiplicative.ofAdd (altAct σ v) := by
      rw [hψ γ u hgmem, hu]
    have halt : altAct σ v = Multiplicative.toAdd (ψ ⟨g (u : W), hgmem⟩) := by
      rw [hh, toAdd_ofAdd]
    have hh' : ψ ⟨((π γ' : ↥H) : MulAut W) (t (u : W)), hg'mem⟩ =
        Multiplicative.ofAdd (altAct (γ' : Perm (Fin 7))
          (Multiplicative.toAdd (ψ ⟨t (u : W), htmem⟩))) :=
      hψ γ' ⟨t (u : W), htmem⟩ hg'mem
    have hsub : (⟨t (g (u : W)), hTI t ht _ hgmem⟩ : ↥I) =
        ⟨((π γ' : ↥H) : MulAut W) (t (u : W)), hg'mem⟩ :=
      Subtype.ext (hxg (u : W)).symm
    calc tH (altAct σ v)
        = tH (Multiplicative.toAdd (ψ ⟨g (u : W), hgmem⟩)) := by rw [halt]
      _ = Multiplicative.toAdd (ψ ⟨t (g (u : W)), hTI t ht _ hgmem⟩) := htH_apply _
      _ = Multiplicative.toAdd (ψ ⟨((π γ' : ↥H) : MulAut W) (t (u : W)), hg'mem⟩) := by
            rw [hsub]
      _ = altAct (γ' : Perm (Fin 7))
            (Multiplicative.toAdd (ψ ⟨t (u : W), htmem⟩)) := by rw [hh', toAdd_ofAdd]
      _ = altAct (γ' : Perm (Fin 7)) (tH (Multiplicative.toAdd (ψ u))) := by
            rw [htH_apply]
            congr 1
      _ = altAct (γ' : Perm (Fin 7)) (tH v) := by rw [hu]
  obtain ⟨πt, hπt⟩ := s16c167_normalizerIsSym (n := 7) (by norm_num) tH hnorm
  refine ⟨tH, πt, hnorm, hπt, ?_⟩
  intro u
  rw [htH_apply]
  exact congrArg (fun z => Multiplicative.toAdd (ψ z)) (Subtype.ext rfl)

private noncomputable def altLift6At (j : Fin 7) :
    alternatingGroup (Fin 6) →* alternatingGroup (Fin 7) where
  toFun σ :=
    ⟨Equiv.swap 6 j * (altLift6 σ : Perm (Fin 7)) * (Equiv.swap 6 j)⁻¹, by
      have h := (alternatingGroup.normal (α := Fin 7)).conj_mem
        (altLift6 σ) (altLift6 σ).2 (Equiv.swap 6 j)
      simpa [MulAut.conj_apply] using h⟩
  map_one' := by ext; simp
  map_mul' := by
    intro a b
    ext
    simp [mul_assoc]

private theorem altLift6At_injective (j : Fin 7) : Function.Injective (altLift6At j) := by
  intro a b h
  apply altLift6_injective
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  have hc := congrArg
    (fun x : Perm (Fin 7) => (Equiv.swap 6 j)⁻¹ * x * Equiv.swap 6 j) h'
  simpa [altLift6At, mul_assoc] using hc

private theorem altLift6At_apply_self (j : Fin 7) (σ : alternatingGroup (Fin 6)) :
    (altLift6At j σ : Perm (Fin 7)) j = j := by
  show (Equiv.swap 6 j * (altLift6 σ : Perm (Fin 7)) * (Equiv.swap 6 j)⁻¹) j = j
  have h6 : (altLift6 σ : Perm (Fin 7)) 6 = 6 := altLift6_apply_last σ
  simp [Equiv.Perm.inv_def, h6]

theorem exists_fixed_vector_of_alternatingNatural_seven
    {W : Type} [CommGroup W] [Finite W]
    {H T : Subgroup (MulAut W)} {I : Subgroup W}
    (hT2 : IsPGroup 2 ↥T)
    (hTH : T ≤ Subgroup.normalizer (H : Set (MulAut W)))
    (hTI : StableUnder T I)
    (hI : AlternatingNatural H I ⊥ 7) :
    ∃ w : W, w ∈ I ∧ w ≠ 1 ∧ w ∈ fixV T ∧
      ∃ E : Subgroup (MulAut W), E ≤ H ∧
        IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  classical
  obtain ⟨π, ψ, hπsurj, hψeq⟩ := s16c167_altNatural_equiv (n := 7) (by norm_num) hI
  obtain ⟨_π0, hReal⟩ : ∃ π0, (FFModel.altDn 7).RealizesVia H I ⊥ π0 := hI
  have hIinv : ∀ h : ↥H, ∀ u ∈ I, (h : MulAut W) u ∈ I :=
    fun h u hu => hReal.2.2.2.1 h u hu
  have hπinj : Function.Injective π := by
    intro a b hab
    apply Subtype.ext
    refine (altAct_eq_iff (n := 7) (by norm_num)).1 ?_
    intro v
    obtain ⟨u, hu⟩ := ψ.surjective (Multiplicative.ofAdd v)
    have hua : ((π a : ↥H) : MulAut W) (u : W) ∈ I := hIinv (π a) (u : W) u.2
    have hub : ((π b : ↥H) : MulAut W) (u : W) ∈ I := hIinv (π b) (u : W) u.2
    have h1 := hψeq a u hua
    have h2 := hψeq b u hub
    rw [show Multiplicative.toAdd (ψ u) = v from by rw [hu, toAdd_ofAdd]] at h1 h2
    have hval : ((π a : ↥H) : MulAut W) = ((π b : ↥H) : MulAut W) :=
      congrArg Subtype.val hab
    have hleft : ψ ⟨((π a : ↥H) : MulAut W) (u : W), hua⟩ =
        ψ ⟨((π b : ↥H) : MulAut W) (u : W), hub⟩ := by
      refine congrArg ψ (Subtype.ext ?_)
      exact congrArg (fun z : MulAut W => z (u : W)) hval
    have hof : Multiplicative.ofAdd (altAct (a : Perm (Fin 7)) v) =
        Multiplicative.ofAdd (altAct (b : Perm (Fin 7)) v) := by
      rw [← h1, ← h2]
      exact hleft
    simpa using congrArg Multiplicative.toAdd hof
  let v : Fin 7 → ↥I := fun j => sevenVec ψ j
  let S : Finset W := Finset.univ.image (fun j : Fin 7 => (v j : W))
  have hv_inj : Function.Injective (fun j : Fin 7 => (v j : W)) := sevenVec_injective ψ
  have hS_card : S.card = 7 := by
    change (Finset.univ.image (fun j : Fin 7 => (v j : W))).card = 7
    rw [Finset.card_image_of_injective _ hv_inj, Finset.card_univ, Fintype.card_fin]
  have hS_stab : ∀ t ∈ T, ∀ w ∈ S, t w ∈ S := by
    intro t ht w hw
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hw
    obtain ⟨tH, πt, _hnorm, hπt, htH_apply⟩ :=
      altNatural_induced_normalizer hTH hTI hπsurj hψeq hIinv ht
    have hmem : t ((v j : ↥I) : W) ∈ I := hTI t ht _ (v j).2
    have h1 : tH (altHeartVec j) = altHeartVec (πt j) := by
      rw [hπt, altAct_altHeartVec]
    have h2 : Multiplicative.toAdd (ψ (v j)) = altHeartVec j := by
      simp [v, sevenVec]
    have h3 : Multiplicative.toAdd (ψ ⟨t ((v j : ↥I) : W), hmem⟩) =
        altHeartVec (πt j) := by
      rw [← htH_apply (v j), h2, h1]
    have h4 : (⟨t ((v j : ↥I) : W), hmem⟩ : ↥I) = v (πt j) := by
      apply ψ.injective
      calc ψ ⟨t ((v j : ↥I) : W), hmem⟩
          = Multiplicative.ofAdd (Multiplicative.toAdd (ψ ⟨t ((v j : ↥I) : W), hmem⟩)) :=
            (ofAdd_toAdd _).symm
        _ = Multiplicative.ofAdd (altHeartVec (πt j)) := by rw [h3]
        _ = ψ (v (πt j)) := by simp [v, sevenVec]
    rw [← hj]
    rw [show t ((v j : ↥I) : W) = (v (πt j) : W) from congrArg Subtype.val h4]
    exact Finset.mem_image.mpr ⟨πt j, Finset.mem_univ _, rfl⟩
  let step : ↥T → ↥S → ↥S :=
    fun t w => ⟨(t : MulAut W) (w : W), hS_stab t t.2 w.1 w.2⟩
  let actHom : ↥T →* Equiv.Perm ↥S :=
    { toFun := fun t =>
        { toFun := step t
          invFun := step t⁻¹
          left_inv := fun x => Subtype.ext (by
            show ((t⁻¹ : MulAut W) ((t : MulAut W) (x : W))) = (x : W)
            exact MulAut.inv_apply_self W (t : MulAut W) (x : W))
          right_inv := fun x => Subtype.ext (by
            show ((t : MulAut W) ((t⁻¹ : MulAut W) (x : W))) = (x : W)
            exact MulAut.apply_inv_self W (t : MulAut W) (x : W)) }
      map_one' := by
        ext x
        simp [step]
      map_mul' := by
        intro s t
        ext x
        simp [step, MulAut.mul_apply] }
  letI : MulAction ↥T ↥S := MulAction.compHom ↥S actHom
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ¬ 2 ∣ Nat.card ↥S := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS_card]
    norm_num
  obtain ⟨wS, hwS⟩ := hT2.nonempty_fixed_point_of_prime_not_dvd_card (↥S) hcard
  have hwSfix : ∀ t : ↥T, (t : MulAut W) (wS : W) = (wS : W) := by
    intro t
    have h : step t wS = wS := MulAction.mem_fixedPoints.mp hwS t
    exact congrArg Subtype.val h
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp wS.2
  have hwj : (wS : W) = (v j : W) := hj.symm
  have hwI : (wS : W) ∈ I := by
    rw [hwj]
    exact (v j).2
  have hw1 : (wS : W) ≠ 1 := by
    rw [hwj]
    exact sevenVec_ne_one ψ j
  have hwT : (wS : W) ∈ fixV T := by
    rw [mem_fixV]
    intro t ht
    exact hwSfix ⟨t, ht⟩
  obtain ⟨P, hP3, hPnc⟩ :=
    CFSG.GroupTheory.exists_isPGroup_three_not_isCyclic_alternatingGroup (n := 6) (by norm_num)
  let f := altLift6At j
  let g : alternatingGroup (Fin 6) →* MulAut W := H.subtype.comp (π.comp f)
  let E : Subgroup (MulAut W) := P.map g
  have hEH : E ≤ H := by
    rintro e he
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp he
    exact (π (f p)).2
  have hE3 : IsPGroup 3 ↥E := hP3.map g
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    haveI : IsCyclic ↥E := hcyc
    apply hPnc
    have hginj : Function.Injective g :=
      (Subgroup.subtype_injective H).comp (hπinj.comp (altLift6At_injective j))
    exact isCyclic_of_injective
      (Subgroup.equivMapOfInjective P g hginj).toMonoidHom
      (Subgroup.equivMapOfInjective P g hginj).injective
  have hEw : ∀ e ∈ E, e (wS : W) = (wS : W) := by
    intro e he
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp he
    rw [hwj]
    change ((π (f p) : ↥H) : MulAut W) ((v j : ↥I) : W) = ((v j : ↥I) : W)
    exact sevenVec_fixed_of_fixes_point hψeq hIinv j (f p) (altLift6At_apply_self j p)
  exact ⟨(wS : W), hwI, hw1, hwT, E, hEH, hE3, hEnc, hEw⟩

theorem ThreeNat.exists_fixed_vector_alt_seven
    {W : Type} [CommGroup W] [Finite W]
    {A H T : Subgroup (MulAut W)}
    (h : ThreeNat A H T)
    (hA7 : UC22.IsAlt ↥H 7)
    (hD7 : SumOfNat (fun H U Z => AlternatingNatural H U Z 7) H
      (commSub ⊤ H) (commSub ⊤ H ⊓ fixV H) 3) :
    ∃ w : W, w ≠ 1 ∧ w ∈ fixV T ∧
      ∃ E : Subgroup (MulAut W), E ≤ H ∧
        IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  classical
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.elem w
  have hTH : T ≤ Subgroup.normalizer (H : Set (MulAut W)) := h.sylow.le.trans h.normal
  have hTp : IsPGroup 2 ↥T := h.sylow.isPGroup
  by_cases hfix : fixV H = ⊥
  ·
    have hD7' : SumOfNat (fun H U Z => AlternatingNatural H U Z 7) H ⊤ ⊥ 3 := by
      simpa [h.comm, hfix] using hD7
    obtain ⟨I, hIirr, hIT, _hIshape⟩ := h.exists_stable_natural
    obtain ⟨I0, _hZI0, _hI0U, hI0sum⟩ := s16t3_sumOfNat_summand hD7' (0 : Fin 3)
    have hI0D7 : AlternatingNatural H I0 ⊥ 7 := s16t3_sumOfNat_one hI0sum
    have hI0shape : SumOfNatShape H I0 ⊥ 1 :=
      ⟨7, Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hA7, s16t3_sumOfNat_singleton bot_le hI0D7⟩)))⟩
    have hI0irr : IsIrrOn H I0 ⊥ := SumOfNatShape.isIrrOn h.quasi hI0shape
    have hI0inv : StableUnder H I0 := hI0irr.2.1
    have hcomm_le : commSub I0 H ≤ I0 := commSub_le_of_invariant hI0inv
    have hcomm_inv : StableUnder H (commSub I0 H) :=
      stableUnder_commSub (H := H) (X := H)
        (fun x hx y hy => H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) hI0inv
    have hcomm_ne : commSub I0 H ≠ ⊥ := by
      intro hbot
      obtain ⟨l, hl, u, hu, hlu⟩ := SumOfNatShape.exists_move h.quasi hI0shape
      have hmem : l u * u⁻¹ ∈ commSub I0 H :=
        Subgroup.subset_closure ⟨l, hl, u, hu, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hlu hmem
    have hcomm_eq : commSub I0 H = I0 := by
      rcases hI0irr.2.2.2 (commSub I0 H) hcomm_inv bot_le hcomm_le with hbot | htop
      · exact absurd hbot hcomm_ne
      · exact htop
    have hI0mem : I0 ∈ irrSet H := by
      refine ⟨hcomm_eq, ?_⟩
      simpa [hfix] using hI0irr
    obtain ⟨g, hg, hgI⟩ := h.trans I0 hI0mem I hIirr
    have hID7 : AlternatingNatural H I ⊥ 7 := by
      rw [hgI]
      simpa [AlternatingNatural, Subgroup.map_bot] using
        s16t3_realizes_map_of_mem_normalizer (D := FFModel.altDn 7) hg.2 hI0D7
    obtain ⟨w, _hwI, hw1, hwT, E, hEH, hE3, hEnc, hEw⟩ :=
      exists_fixed_vector_of_alternatingNatural_seven hTp hTH hIT hID7
    exact ⟨w, hw1, hwT, E, hEH, hE3, hEnc, hEw⟩
  ·
    have hstab : StableUnder T (fixV H) :=
      stableUnder_fixV (Y := T) (H := H)
        (fun t ht x hx => conj_mem_of_mem_normalizer (hTH ht) hx)
    obtain ⟨w, _hwH, hw1, hwT⟩ :=
      s15_Lin_exists_ne_one_mem_fixV hTp hW2 hfix hstab
    obtain ⟨eAlt⟩ := hA7
    obtain ⟨P, hP3, hPnc⟩ :=
      CFSG.GroupTheory.exists_isPGroup_three_not_isCyclic_of_mulEquiv_alternatingGroup
        (X := ↥H) (n := 7) (by norm_num) eAlt
    let E : Subgroup (MulAut W) := P.map H.subtype
    have hEH : E ≤ H := Subgroup.map_subtype_le P
    have hE3 : IsPGroup 3 ↥E := hP3.map H.subtype
    have hEnc : ¬ IsCyclic ↥E := by
      intro hcyc
      haveI : IsCyclic ↥E := hcyc
      apply hPnc
      exact isCyclic_of_injective
        (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).toMonoidHom
        (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).injective
    have hEw : ∀ e ∈ E, e w = w := by
      intro e he
      obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp he
      exact mem_fixV.mp _hwH (p : MulAut W) p.2
    exact ⟨w, hw1, hwT, E, hEH, hE3, hEnc, hEw⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
