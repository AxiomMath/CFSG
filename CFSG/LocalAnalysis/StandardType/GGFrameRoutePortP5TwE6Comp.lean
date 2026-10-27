module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Real
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6A5
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6Rank
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableData
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneHyperplane
public import TauCeti.GroupTheory.FixedSubgroup

public section

namespace CFSG.StandardType.FrameRoute.TwE6Model

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.TwE6DD2
  CFSG.StandardType.NTPlane

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem twE6A5_card_centerQuot {D : Type} [Group D] [Finite D]
    (hZ : Subgroup.center D = ⊥) (h2 : 2 ^ 15 ∣ Nat.card D) :
    25920 < Nat.card (D ⧸ Subgroup.center D) := by
  have e : (D ⧸ Subgroup.center D) ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hcard : Nat.card (D ⧸ Subgroup.center D) = Nat.card D := Nat.card_congr e.toEquiv
  have hge : 2 ^ 15 ≤ Nat.card D := Nat.le_of_dvd Nat.card_pos h2
  rw [hcard]
  calc 25920 < 2 ^ 15 := by norm_num
    _ ≤ Nat.card D := hge

section Component

open CFSG.HardMathSupport.Timmesfeld.CrossChar


private theorem twE6A5_mem_X
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ)}
    {v : X3} {t : ModGL TwistTag.E6.tag K}
    (hvt : ((τ (Multiplicative.ofAdd v) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
      ModGL TwistTag.E6.tag K) = t)
    {X D : Subgroup ↥(twistedE6RootGroup K σ)}
    (hcore : ∀ s ∈ twistedE6InndiagGL K σ, s * t = t * s →
      (∀ d ∈ D, s * (d : ModGL TwistTag.E6.tag K) =
        (d : ModGL TwistTag.E6.tag K) * s) →
        s ∈ X.map (twistedE6RootGroup K σ).subtype)
    (w : X3) (hfix : ∀ j ∈ D, RecipeExcLang.twConj K σ (τ (Multiplicative.ofAdd w)) j = j) :
    ((τ (Multiplicative.ofAdd w) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
      ModGL TwistTag.E6.tag K) ∈ X.map (twistedE6RootGroup K σ).subtype := by
  let tw : ModGL TwistTag.E6.tag K :=
    ((τ (Multiplicative.ofAdd w) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
      ModGL TwistTag.E6.tag K)
  have htwD : ∀ d ∈ D, tw * (d : ModGL TwistTag.E6.tag K) =
      (d : ModGL TwistTag.E6.tag K) * tw := by
    intro d hd
    have h := congrArg Subtype.val (hfix d hd)
    rw [RecipeExcLang.coe_twConj] at h
    have h' : tw * (d : ModGL TwistTag.E6.tag K) * tw⁻¹ =
        (d : ModGL TwistTag.E6.tag K) := by simpa only [tw] using h
    calc tw * (d : ModGL TwistTag.E6.tag K) =
        (tw * (d : ModGL TwistTag.E6.tag K) * tw⁻¹) * tw := by group
      _ = (d : ModGL TwistTag.E6.tag K) * tw := by rw [h']
  have httw : tw * t = t * tw := by
    have h : (τ (Multiplicative.ofAdd w) * τ (Multiplicative.ofAdd v) :
        ↥(RecipeExcLang.twInndiagGroup K σ)) =
        τ (Multiplicative.ofAdd v) * τ (Multiplicative.ofAdd w) := by
      simpa only [map_mul τ] using
        congrArg τ (mul_comm (Multiplicative.ofAdd w) (Multiplicative.ofAdd v))
    have h' := congrArg
      (fun x : ↥(RecipeExcLang.twInndiagGroup K σ) => (x : ModGL TwistTag.E6.tag K)) h
    simpa only [Subgroup.coe_mul, hvt, tw] using h'
  simpa only [tw] using
    hcore tw (twInndiagGroup_le_twistedE6InndiagGL σ (τ (Multiplicative.ofAdd w)).2) httw htwD

private theorem twE6A5_line
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hτinj : Function.Injective τ) {v : X3} (hv : (kerRoots v).ncard = 30)
    {t : ModGL TwistTag.E6.tag K}
    (hvt : ((τ (Multiplicative.ofAdd v) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
      ModGL TwistTag.E6.tag K) = t)
    (ht : t ∈ twistedE6InndiagGL K σ)
    {X D : Subgroup ↥(twistedE6RootGroup K σ)}
    (hXD : (Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
      (twistedE6RootGroup K σ) = X ⊔ D)
    (hXcyc : IsCyclic X)
    (hcore : ∀ s ∈ twistedE6InndiagGL K σ, s * t = t * s →
      (∀ d ∈ D, s * (d : ModGL TwistTag.E6.tag K) =
        (d : ModGL TwistTag.E6.tag K) * s) →
        s ∈ X.map (twistedE6RootGroup K σ).subtype) :
    ∀ w : X3, (∀ j ∈ D, RecipeExcLang.twConj K σ (τ (Multiplicative.ofAdd w)) j = j) →
      ∃ c : ZMod 3, w = c • v := by
  have hvne : v ≠ 0 := by
    intro h
    rw [h, NTPlane.ncard_kerRoots_zero] at hv
    omega
  have hDcomm : ∀ d ∈ D, ((d : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) * t =
      t * ((d : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 (by
      rw [hXD]; exact (le_sup_right : D ≤ X ⊔ D) hd))
  intro w hfix
  have htwX := twE6A5_mem_X σ hvt hcore w hfix
  have htX : t ∈ X.map (twistedE6RootGroup K σ).subtype :=
    hcore t ht rfl fun d hd => (hDcomm d hd).symm
  have hXcyc' : IsCyclic (X.map (twistedE6RootGroup K σ).subtype) :=
    isCyclic_of_surjective
      (Subgroup.equivMapOfInjective X (twistedE6RootGroup K σ).subtype Subtype.val_injective)
      (Subgroup.equivMapOfInjective X (twistedE6RootGroup K σ).subtype
        Subtype.val_injective).surjective
  have hτ'inj : Function.Injective
      (((RecipeExcLang.twInndiagGroup K σ).subtype).comp τ) :=
    Subtype.val_injective.comp hτinj
  have htX' : ((RecipeExcLang.twInndiagGroup K σ).subtype) (τ (Multiplicative.ofAdd v)) ∈
      X.map (twistedE6RootGroup K σ).subtype := by
    rw [show (RecipeExcLang.twInndiagGroup K σ).subtype
      (τ (Multiplicative.ofAdd v)) = t from hvt]
    exact htX
  obtain ⟨c, hc⟩ := eq_smul_of_mem_cyclic hXcyc'
    (((RecipeExcLang.twInndiagGroup K σ).subtype).comp τ) hτ'inj hvne htX' htwX
  exact ⟨c, hc⟩

private theorem twE6A5_coroot_conj
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    (hR : ∀ w : X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {v : X3} {γ : Fin Tag.E6.rank → ℤ} (hγv : TwE6EndNode3.corootVec γ = v)
    {τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hτspec : ∀ w : X3, twInndiagEquivRgrp le_rfl hK σ hσ Fr hFr (τ (Multiplicative.ofAdd w)) =
      ⟨_, hR w⟩) :
    g⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      ((τ (Multiplicative.ofAdd v) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
        ModGL TwistTag.E6.tag K) * g =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have htuple : TwE6RootAs.corootTuple γ ζ =
      CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ3 (TwE6EndNode3.corootVec γ) :=
    TwE6EndNode3.corootTuple_eq_zetaVec ζ hζ3 γ
  rw [conj_baseChangeGL_torusHom le_rfl hK σ hσ Fr hFr hR hτspec v, htuple, hγv]
  refine congrArg (rootDiagUnit Tag.E6) ?_
  funext i
  rfl

private theorem twE6A5_core
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (t : ModGL TwistTag.E6.tag K) (ht : t ∈ twistedE6InndiagGL K σ)
    (hcor : g⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)) t * g =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ)) :
    ∃ X D : Subgroup ↥(twistedE6RootGroup K σ),
      (Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
          (twistedE6RootGroup K σ) = X ⊔ D ∧
      IsCyclic X ∧ Odd (Nat.card X) ∧
      X ≤ Subgroup.centralizer (D : Set ↥(twistedE6RootGroup K σ)) ∧
      CFSG.IsQuasisimple ↥D ∧ Subgroup.center ↥D = ⊥ ∧ 7 ∣ Nat.card ↥D ∧
      (2 ^ 1) ^ 15 ∣ Nat.card ↥D ∧ CFSG.Open.StatedClassicalModel ↥D .PSU 6 2 1 ∧
      ∀ s ∈ twistedE6InndiagGL K σ, s * t = t * s →
        (∀ d ∈ D, s * (d : ModGL TwistTag.E6.tag K) =
          (d : ModGL TwistTag.E6.tag K) * s) →
          s ∈ X.map (twistedE6RootGroup K σ).subtype := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    omega
  let v₀ : WeylGroup TwistTag.E6.tag := twE6W0
  have hv₀ : ∀ δ : Fin TwistTag.E6.tag.rank → ℤ,
      v₀ • permLattice TwistTag.E6.perm δ = -δ := by
    intro δ
    exact (twE6W0_smul (permLattice CFSG.RankThree.E6.e6Rho δ)).trans
      (congrArg Neg.neg (TwistedDiag.permLattice_permLattice' δ))
  let g' : ModGL TwistTag.E6.tag (AlgebraicClosure K) := g
  have hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g' =
      g' * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v₀ :=
    inv_mul_eq_iff_eq_mul.mp hgn
  exact ggTP_core_psu_of_fuse TwE6CorootCore.exists_conj_eq_thetaSL2_pow 1 le_rfl K σ hK hσ 3
    Nat.prime_three (by norm_num) Fr hFr v₀ hv₀ g' hg hlang t ht γ hγ ζ hζ3 hζ1 hcor

private theorem twE6A5_data
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    (hR : ∀ w : X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {v : X3} (hv : (kerRoots v).ncard = 30) :
    ∃ (τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ))
      (X D : Subgroup ↥(twistedE6RootGroup K σ)),
      let t : ModGL TwistTag.E6.tag K :=
        ((τ (Multiplicative.ofAdd v) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
          ModGL TwistTag.E6.tag K)
      Function.Injective τ ∧
      (∀ w : X3, rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hR w⟩ =
        RecipeExcLang.twConj K σ (τ (Multiplicative.ofAdd w))) ∧
      (TauCeti.fixedSubgroup (rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hR v⟩).toMonoidHom =
        (Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
          (twistedE6RootGroup K σ)) ∧
      (Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
          (twistedE6RootGroup K σ) = X ⊔ D ∧
      IsCyclic X ∧ X ≤ Subgroup.centralizer (D : Set ↥(twistedE6RootGroup K σ)) ∧
      CFSG.IsQuasisimple ↥D ∧ Subgroup.center ↥D = ⊥ ∧ (2 ^ 1) ^ 15 ∣ Nat.card ↥D ∧
      CFSG.Open.StatedClassicalModel ↥D .PSU 6 2 1 ∧
      (∀ w : X3, (∀ j ∈ D, RecipeExcLang.twConj K σ (τ (Multiplicative.ofAdd w)) j = j) ↔
        ∃ c : ZMod 3, w = c • v) := by
  obtain ⟨γ, hγ, hγv⟩ := exists_isRoot_corootVec_eq hv
  obtain ⟨τ, hτinj, hτspec⟩ := exists_torusHom_twInndiag le_rfl hK σ hσ Fr hFr hζ hR
  let t : ModGL TwistTag.E6.tag K :=
    ((τ (Multiplicative.ofAdd v) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
      ModGL TwistTag.E6.tag K)
  have ht : t ∈ twistedE6InndiagGL K σ :=
    twInndiagGroup_le_twistedE6InndiagGL σ (τ (Multiplicative.ofAdd v)).2
  have hcor := twE6A5_coroot_conj hK σ hσ Fr hFr hζ hR hγv hτspec
  obtain ⟨X, D, hXD, hXcyc, -, hXcent, hDq, hDcenter, -, hD15, hDmodel, hcore⟩ :=
    twE6A5_core hK σ hσ Fr hFr hg hgn hζ hγ t ht hcor
  have hDcomm : ∀ d ∈ D, ((d : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) * t =
      t * ((d : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_subgroupOf.1 (hXD.ge (Subgroup.mem_sup_right hd)))
  refine ⟨τ, X, D, hτinj, rgrpConjAut_torusHom le_rfl hK σ hσ Fr hFr hR hτspec,
    fixedSubgroup_rgrpConjAut_torusHom le_rfl hK σ hσ Fr hFr hR hτspec v, hXD, hXcyc, hXcent,
    hDq, hDcenter, hD15, hDmodel, fun w =>
      ⟨twE6A5_line σ hτinj hv rfl ht hXD hXcyc hcore w,
        fun hw j hj => twConj_torusHom_apply_of_mem_line σ τ hDcomm hw hj⟩⟩

theorem exists_twE6Component_A5
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    (hR : ∀ w : X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {v : X3} (hv : (kerRoots v).ncard = 30) :
    let φ : X3 → MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
      fun w => rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hR w⟩
    let C := TauCeti.fixedSubgroup (φ v).toMonoidHom
    ∃ J : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      CFSG.IsQuasisimple ↥J ∧ J ≤ C ∧ (J.subgroupOf C).Normal ∧
      (∀ _ : (J.subgroupOf C).Normal, IsSolvable (↥C ⧸ J.subgroupOf C)) ∧
      25920 < Nat.card (↥J ⧸ Subgroup.center ↥J) ∧
      LargeEvenMarking ↥J (fun lab _ _ _ _ _ => lab = ⟨.twA, 5, 1⟩) ∧
      (∀ w : X3, (∀ j ∈ J, φ w j = j) ↔ ∃ c : ZMod 3, w = c • v) ∧
      ∀ (J₁ : Type) [Group J₁] [Finite J₁] (π : J₁ →* ↥J), Function.Surjective π →
        π.ker ≤ Subgroup.center J₁ → Rank3Witness J₁ 3 := by
  let φ : X3 → MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    fun w => rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hR w⟩
  let C := TauCeti.fixedSubgroup (φ v).toMonoidHom
  obtain ⟨τ, X, D, hτinj, hφ, hC, hXD, hXcyc, hXcent, hDq, hDcenter, hD15, hDmodel, hdet⟩ :=
    twE6A5_data hK σ hσ Fr hFr hg hgn hζ hR hv
  have hXD' : C = X ⊔ D := hC.trans hXD
  obtain ⟨hDleC, hDnorm, hDsolv⟩ := normal_solvable_of_eq_sup_cyclic hXD' hXcyc hXcent
  have hmark := largeEvenMarking_twA5_of_statedModel hDq hDcenter hDmodel
  refine ⟨D, hDq, hDleC, hDnorm, hDsolv, twE6A5_card_centerQuot hDcenter hD15,
    hmark, ?_, ?_⟩
  · intro w
    dsimp only
    rw [hφ w]
    exact hdet w
  · intro J₁ _ _ π hπ hker
    exact rank3Witness_cover_of_marking_twA5 hmark J₁ π hπ hker

end Component

end CFSG.StandardType.FrameRoute.TwE6Model

end
