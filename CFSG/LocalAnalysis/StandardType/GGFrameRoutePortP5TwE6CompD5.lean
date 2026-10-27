module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Real
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6A5
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6Rank
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableData
public import TauCeti.GroupTheory.FixedSubgroup
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6D5
import CFSG.LocalAnalysis.StandardType.GGNTPlaneHyperplane
import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreCommute
import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreComponent
import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreFrame
import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreHolds

public section

namespace CFSG.StandardType.FrameRoute.TwE6Model

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.TwE6DD2
  CFSG.StandardType.NTPlane

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Helpers

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups

variable {K : Type} [Field K] {σ : K ≃+* K}
  {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}

private theorem twE6D5_normal (t : ModGL TwistTag.E6.tag K)
    {C X D : Subgroup ↥(twistedE6RootGroup K σ)}
    (hXD : (Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
        (twistedE6RootGroup K σ) = X ⊔ D)
    (hX : IsCyclic X) (hXc : X ≤ Subgroup.centralizer (D : Set ↥(twistedE6RootGroup K σ)))
    (hDq : CFSG.IsQuasisimple D) (hCeq : C = (Subgroup.centralizer
        ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf (twistedE6RootGroup K σ)) :
    D ≤ C ∧ (D.subgroupOf C).Normal ∧
      (∀ _ : (D.subgroupOf C).Normal, IsSolvable (↥C ⧸ D.subgroupOf C)) ∧
      CFSG.Open.IsComponentOf D ((Subgroup.centralizer
        ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf (twistedE6RootGroup K σ)) ∧
      (∀ x ∈ D, (x : ModGL TwistTag.E6.tag K) ∈
        Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))) := by
  obtain ⟨hDleM, hNM, hsolM⟩ := normal_solvable_of_eq_sup_cyclic hXD hX hXc
  have hsolC : ∀ _ : (D.subgroupOf C).Normal, IsSolvable (↥C ⧸ D.subgroupOf C) :=
    hCeq.symm ▸ hsolM
  refine ⟨hCeq.symm ▸ hDleM, hCeq.symm ▸ hNM, hsolC,
    ⟨hDleM, CFSG.Open.IsSubnormal.step hDleM hNM (CFSG.Open.IsSubnormal.refl _),
      CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple hDq⟩, fun x hx => ?_⟩
  exact Subgroup.mem_subgroupOf.1 (hDleM hx)

variable [Finite K]

private theorem twE6D5_frame (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (hK2 : ringChar K = 2) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    (t : ModGL TwistTag.E6.tag K) (ht : t ∈ twistedE6InndiagGL K σ)
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (hta : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g =
      rootDiagUnit Tag.E6 a) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = 2 ^ 1 ∧ S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (twistedE6InndiagConj K σ ⟨t, ht⟩ c) =
        rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      (∀ c : ↥(twistedE6RootGroup K σ), ι c = g⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) * g) ∧
      (∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ →
        S.ρ γ = (show WeylGroup TwistTag.E6.tag from twE6W0) •
          permLattice TwistTag.E6.perm γ) ∧
      S.D = LangDatum.ofTwist TwistTag.E6 Fr 2 hFr twE6W0 hg hlang := by
  exact TwE6D5Core.exists_langSetup_of_twE6Frame (q := 2) σ hK hσ hK2 hFr (v := twE6W0)
    hg hlang ht hta

private theorem twE6D5_setup (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hζ : orderOf ζ = 3)
    (hR : ∀ w : X3, g * rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {v : X3} (hv : (kerRoots v).ncard = 40) :
    ∃ (τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ))
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) (t : ModGL TwistTag.E6.tag K),
      (∀ w : X3, twInndiagEquivRgrp le_rfl hK σ hσ Fr hFr
        (τ (Multiplicative.ofAdd w)) = ⟨_, hR w⟩) ∧
      t = (τ (Multiplicative.ofAdd v) : ModGL TwistTag.E6.tag K) ∧ ringChar K = 2 ∧
      ringChar (AlgebraicClosure K) = 2 ∧ t ∈ twistedE6InndiagGL K σ ∧
      (∀ i, a i ^ 3 = 1) ∧ (kernelRoots (rootCharHom a)).ncard = 40 ∧
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g =
        rootDiagUnit Tag.E6 a ∧ a = (fun i => ζ ^ (v i).val) := by
  have hCK : CharP K 2 := CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 2)
    (by rw [hK]; norm_num)
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hCL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hL2 : ringChar (AlgebraicClosure K) = 2 := ringChar.eq _ 2
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  obtain ⟨τ, -, hτspec⟩ := exists_torusHom_twInndiag le_rfl hK σ hσ Fr hFr hζ hR
  refine ⟨τ, fun i => ζ ^ (v i).val, (τ (Multiplicative.ofAdd v) : ModGL TwistTag.E6.tag K),
    hτspec, rfl, hK2, hL2, twInndiagGroup_le_twistedE6InndiagGL σ
      (τ (Multiplicative.ofAdd v)).2, ?_, ?_, ?_, rfl⟩
  · intro i
    rw [← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
  · rw [kernelRoots_rootCharHom_zeta_pow hζ v, hv]
  · exact conj_baseChangeGL_torusHom le_rfl hK σ hσ Fr hFr hR hτspec v

private theorem twE6D5_commute (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hR : ∀ w : X3, g * rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hτspec : ∀ w : X3, twInndiagEquivRgrp le_rfl hK σ hσ Fr hFr
      (τ (Multiplicative.ofAdd w)) = ⟨_, hR w⟩)
    (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hιval : ∀ c : ↥(twistedE6RootGroup K σ), ι c = g⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) * g)
    {D : Subgroup ↥(twistedE6RootGroup K σ)} {H : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))}
    (hmap : D.map ι = H) {w : X3}
    (hw : ∀ j ∈ D, rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hR w⟩ j = j) :
    ∀ x ∈ H, x * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) =
      rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * x := by
  subst hmap
  rintro _ ⟨j, hj, rfl⟩
  have h := congrArg (fun x : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) =>
    (x : ModGL TwistTag.E6.tag K)) ((DFunLike.congr_fun
      (rgrpConjAut_torusHom le_rfl hK σ hσ Fr hFr hR hτspec w) j).symm.trans (hw j hj))
  rw [RecipeExcLang.coe_twConj] at h
  have h2 := (show Commute _ _ from mul_inv_eq_iff_eq_mul.1 h).map
    (baseChangeGL (algebraMap K (AlgebraicClosure K)))
  rw [hιval j, ← conj_baseChangeGL_torusHom le_rfl hK σ hσ Fr hFr hR hτspec w]
  have h3 := (h2.conj g⁻¹).symm.eq
  rw [inv_inv] at h3
  exact h3


private theorem twE6D5_core (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    (hK2 : ringChar K = 2)
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ} (t : ModGL TwistTag.E6.tag K)
    (ht : t ∈ twistedE6InndiagGL K σ) (hap : ∀ i, a i ^ 3 = 1)
    (hk : (kernelRoots (rootCharHom a)).ncard = 40)
    (hta : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g =
      rootDiagUnit Tag.E6 a) :
    ∃ X D : Subgroup ↥(twistedE6RootGroup K σ),
      (Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
          (twistedE6RootGroup K σ) = X ⊔ D ∧
        IsCyclic X ∧ X ≤ Subgroup.centralizer (D : Set ↥(twistedE6RootGroup K σ)) ∧
        CFSG.IsQuasisimple D := by
  have hw0 : ∀ γ : Fin Tag.E6.rank → ℤ,
      (show WeylGroup TwistTag.E6.tag from twE6W0) • permLattice TwistTag.E6.perm γ = -γ := by
    intro γ
    exact (twE6W0_smul (permLattice CFSG.RankThree.E6.e6Rho γ)).trans
      (congrArg Neg.neg (TwistedDiag.permLattice_permLattice' γ))
  exact TwE6RootAs.twE6D5Core_holds K σ 2 hK hσ hK2 (by norm_num) Fr hFr
    (show WeylGroup TwistTag.E6.tag from twE6W0) hw0 g hg hlang t ht a hap hk hta

private theorem twE6D5_fix_imp (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hR : ∀ w : X3, g * rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hτspec : ∀ w : X3, twInndiagEquivRgrp le_rfl hK σ hσ Fr hFr
      (τ (Multiplicative.ofAdd w)) = ⟨_, hR w⟩)
    (hK2 : ringChar K = 2)
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    (hζ : orderOf ζ = 3) {v : X3} (hv : (kerRoots v).ncard = 40)
    (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ} (ha : a = fun i => ζ ^ (v i).val)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (hq : S.D.q = 2 ^ 1) (hΦ : S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr)
    (hSD : S.D = LangDatum.ofTwist TwistTag.E6 Fr 2 hFr twE6W0 hg hlang)
    (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hιval : ∀ c : ↥(twistedE6RootGroup K σ), ι c = g⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) * g)
    {D : Subgroup ↥(twistedE6RootGroup K σ)} {i : KernelComponent (rootCharHom a)}
    (hmap : D.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {w : X3} (hw : ∀ j ∈ D, rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hR w⟩ j = j) :
    ∃ c : ZMod 3, w = c • v := by
  have hka : kernelRoots (rootCharHom a) = kerRoots v := by
    rw [ha, kernelRoots_rootCharHom_zeta_pow hζ v]
  have hCK : CharP K 2 := ringChar.of_eq hK2
  have hCL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨S', -, -, -, hT', -, -, -, -, -, hS'D⟩ := twE6D5_frame hK hσ hK2 hFr hg hlang _
    (twInndiagGroup_le_twistedE6InndiagGL σ (τ (Multiplicative.ofAdd w)).2)
    (conj_baseChangeGL_torusHom le_rfl hK σ hσ Fr hFr hR hτspec w)
  have hb : rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) ∈ S.D.torus := by
    rw [congrArg LangDatum.torus (hSD.trans hS'D.symm)]
    exact hT'
  have hroot : ∀ γ ∈ kernelRoots (rootCharHom a),
      rootChar (fun i => ζ ^ (w i).val) γ = 1 :=
    TwE6D5Core.rootChar_eq_one_of_commute_d5 S (fun c => by rw [hq]; exact hFr c) hΦ
      (ringChar.eq _ 2) (by rw [hq]; norm_num) hT hap (by rw [hka, hv]) i hb
      (twE6D5_commute hK hσ hFr hR hτspec ι hιval hmap hw)
  refine (NTPlane.forall_pairVec_kerRoots_eq_zero_iff (Or.inr hv) w).1 fun γ hγ => ?_
  exact (rootChar_zeta_pow_eq_one_iff hζ w γ).1 (hroot γ (hka ▸ hγ))

private theorem twE6D5_component (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    (hζ : orderOf ζ = 3)
    (hR : ∀ w : X3, g * rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {v : X3} (hv : (kerRoots v).ncard = 40) :
    let φ : X3 → MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
      fun w => rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hR w⟩
    let C := TauCeti.fixedSubgroup (φ v).toMonoidHom
    ∃ J : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      CFSG.IsQuasisimple ↥J ∧ J ≤ C ∧ (J.subgroupOf C).Normal ∧
      (∀ _ : (J.subgroupOf C).Normal, IsSolvable (↥C ⧸ J.subgroupOf C)) ∧
      25920 < Nat.card (↥J ⧸ Subgroup.center ↥J) ∧
      LargeEvenMarking ↥J (fun lab _ _ _ _ _ => lab = ⟨.twD, 5, 1⟩) ∧
      (∀ w : X3, (∀ j ∈ J, φ w j = j) ↔ ∃ c : ZMod 3, w = c • v) ∧
      ∀ (J₁ : Type) [Group J₁] [Finite J₁] (π : J₁ →* ↥J), Function.Surjective π →
        π.ker ≤ Subgroup.center J₁ → Rank3Witness J₁ 4 := by
  dsimp only
  obtain ⟨τ, a, t, hτspec, rfl, hK2, hL2, ht, hap, hk, hta, ha⟩ :=
    twE6D5_setup hK hσ hFr hζ hR hv
  obtain ⟨X, D, hXD, hX, hXc, hDq⟩ := twE6D5_core hK hσ hFr hg hlang hK2 _ ht hap hk hta
  obtain ⟨hDleC, hN, hsol, hcomp, hDc⟩ := twE6D5_normal _ hXD hX hXc hDq
    (fixedSubgroup_rgrpConjAut_torusHom le_rfl hK σ hσ Fr hFr hR hτspec v)
  obtain ⟨S, ι, hq, hΦ, hT, hι, hrange, hconj, hιval, -, hSD⟩ :=
    twE6D5_frame hK hσ hK2 hFr hg hlang _ ht hta
  obtain ⟨i, hmap, hmodel⟩ :=
    TwE6D5Core.exists_map_eq_rationalComponent_d5 S hq hFr hΦ hL2 ι hι hrange ht hT hap hk hconj
      hcomp
  have hmark := largeEvenMarking_twD5_of_lieModel hDq hmodel.1
  refine ⟨D, hDq, hDleC, hN, hsol, lt_card_of_lieModel_omegaMinus_five hmodel.1, hmark,
    fun w => ⟨twE6D5_fix_imp hK hσ hFr hR hτspec hK2 hg hlang hζ hv S ha hT hap hq hΦ hSD ι
      hιval hmap, fun hc j hj => ?_⟩, fun J₁ _ _ π hπ hker =>
        rank3Witness_cover_of_marking_twD5 hmark J₁ π hπ hker⟩
  exact (DFunLike.congr_fun (rgrpConjAut_torusHom le_rfl hK σ hσ Fr hFr hR hτspec w) j).trans
    (twConj_torusHom_apply_of_mem_line σ τ
      (fun d hd => Subgroup.mem_centralizer_singleton_iff.1 (hDc d hd)) hc hj)

end Helpers

theorem exists_twE6Component_D5
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    (hR : ∀ w : X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {v : X3} (hv : (kerRoots v).ncard = 40) :
    let φ : X3 → MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
      fun w => rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hR w⟩
    let C := TauCeti.fixedSubgroup (φ v).toMonoidHom
    ∃ J : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      CFSG.IsQuasisimple ↥J ∧ J ≤ C ∧ (J.subgroupOf C).Normal ∧
      (∀ _ : (J.subgroupOf C).Normal, IsSolvable (↥C ⧸ J.subgroupOf C)) ∧
      25920 < Nat.card (↥J ⧸ Subgroup.center ↥J) ∧
      LargeEvenMarking ↥J (fun lab _ _ _ _ _ => lab = ⟨.twD, 5, 1⟩) ∧
      (∀ w : X3, (∀ j ∈ J, φ w j = j) ↔ ∃ c : ZMod 3, w = c • v) ∧
      ∀ (J₁ : Type) [Group J₁] [Finite J₁] (π : J₁ →* ↥J), Function.Surjective π →
        π.ker ≤ Subgroup.center J₁ → Rank3Witness J₁ 4 := by
  have hg' : (show ModGL TwistTag.E6.tag (AlgebraicClosure K) from g) ∈
      adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := hg
  have hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) twE6W0 :=
    inv_mul_eq_iff_eq_mul.mp hgn
  have hlang' : twistHom TwistTag.E6 (AlgebraicClosure K) Fr
      (show ModGL TwistTag.E6.tag (AlgebraicClosure K) from g) =
      (show ModGL TwistTag.E6.tag (AlgebraicClosure K) from g) *
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 := hlang
  exact twE6D5_component hK hσ hFr hg' hlang' hζ hR hv

end CFSG.StandardType.FrameRoute.TwE6Model

end
