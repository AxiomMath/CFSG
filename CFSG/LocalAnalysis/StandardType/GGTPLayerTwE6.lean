module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGTwKGLayerDefs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.StandardType.GGKGTwFrame
public import CFSG.LocalAnalysis.StandardType.GGKGTwTheta
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreOfFuse
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFuse
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot CFSG.RankThree.Chevalley

private theorem ggTP_core_thetaSL2_pow_psu
    {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]
    (σ : K ≃+* K) (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (hk : Nat.card k = 2 ^ f) {A : SL2 k}
    (hA : orderOf A = Nat.card k + 1) {m : ℕ} (hm : A ^ m ≠ 1) :
    ∃ X D : Subgroup ↥(twistedE6RootGroup K σ),
      (centralizer ({(thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m)} :
          Set (ModGL TwistTag.E6.tag K))).subgroupOf (twistedE6RootGroup K σ) = X ⊔ D ∧
        IsCyclic X ∧ Odd (Nat.card X) ∧ X ≤ centralizer (D : Set _) ∧ CFSG.IsQuasisimple D ∧
        center D = ⊥ ∧ 7 ∣ Nat.card D ∧ (2 ^ f) ^ 15 ∣ Nat.card D ∧
        CFSG.Open.StatedClassicalModel ↥D .PSU 6 2 f ∧
        ∀ s ∈ twistedE6InndiagGL K σ,
          s * (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m) =
            (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m) * s →
          (∀ d ∈ D, s * (d : ModGL TwistTag.E6.tag K) = (d : ModGL TwistTag.E6.tag K) * s) →
            s ∈ X.map (twistedE6RootGroup K σ).subtype := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have h3 : 3 ≤ orderOf (A ^ m) := by
    have hd : orderOf (A ^ m) ∣ 2 ^ f + 1 := by
      rw [← hk, ← hA]
      exact orderOf_pow_dvd m
    have hodd : Odd (orderOf (A ^ m)) :=
      Odd.of_dvd_nat (Even.add_one ((Nat.even_pow' (by omega)).2 even_two)) hd
    have h1 : orderOf (A ^ m) ≠ 1 := fun h => hm (orderOf_eq_one_iff.1 h)
    have h0 : 0 < orderOf (A ^ m) := Nat.pos_of_dvd_of_pos hd (by positivity)
    obtain ⟨j, hj⟩ := hodd
    omega
  have hcen := TwE6CorootCore.centralizer_pow_inf_eq hf hk hK hσ' hA h3
  set ρ := (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) with hρdef
  have hρinj : Function.Injective ρ := injective_thetaSL2_comp_map hK2 (algebraMap k K)
  have hXJ : zpowers (ρ A) ≤ thetaRankOneGroup (algebraMap k K) := by
    rw [zpowers_le, thetaRankOneGroup_eq_range hK2]
    exact MonoidHom.mem_range.2 ⟨A, rfl⟩
  have hXC : zpowers (ρ A) ≤ twistedE6RootGroup K σ :=
    hXJ.trans (thetaRankOneGroup_le_C0 hf hk hK hσ')
  have hDC : su6Levi σ.toRingHom ≤ twistedE6RootGroup K σ :=
    su6Levi_le_graphFixedRootGroup σ.toRingHom
  have hcard : Nat.card ↥((su6Levi σ.toRingHom).subgroupOf (twistedE6RootGroup K σ)) =
      CFSG.Open.ordTwistedA 5 (2 ^ f) :=
    F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
      (lieModel_su6Levi_subgroupOf hf hk hK hσ')
  refine ⟨(zpowers (ρ A)).subgroupOf (twistedE6RootGroup K σ),
    (su6Levi σ.toRingHom).subgroupOf (twistedE6RootGroup K σ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← inf_subgroupOf_right, hcen, subgroupOf_sup hXC hDC]
  · have := Subgroup.isCyclic_zpowers (ρ A)
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hXC).symm (MulEquiv.surjective _)
  · rw [Nat.card_congr (subgroupOfEquivOfLe hXC).toEquiv, Nat.card_zpowers,
      orderOf_injective ρ hρinj, hA, hk]
    exact Even.add_one ((Nat.even_pow' (by omega)).2 even_two)
  · exact CFSG.SeitzReduction.TwistedE6Pilot.subgroupOf_le_centralizer_subgroupOf
      (hXJ.trans (le_centralizer_iff.1 (su6Levi_facts hf hk hK hσ').1))
  · exact isQuasisimple_su6Levi_subgroupOf hf hk hK hσ'
  · have := isSimpleGroup_su6Levi hf hk hK hσ'
    have hnc : ∃ a b : su6Levi σ.toRingHom, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      have := isPerfect_su6Levi hf hk hK hσ'
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hc a b⟩⟩
    rw [← Subgroup.map_center_eq (subgroupOfEquivOfLe hDC).symm,
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2, Subgroup.map_bot]
  · rw [hcard]
    exact (TwE6CorootCore.seven_and_pow_dvd_ordTwistedA_five hf).1
  · rw [hcard]
    exact (TwE6CorootCore.seven_and_pow_dvd_ordTwistedA_five hf).2
  · exact CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num)
      (lieModel_su6Levi_subgroupOf hf hk hK hσ')
  · intro s hs hst hsD
    obtain ⟨c, hc, _, ⟨u, rfl⟩, rfl⟩ := TwE6CorootCore.exists_mul_eq_of_mem_twistedE6InndiagGL σ hs
    have hc' := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hc)
    have hz := TwE6CorootCore.mem_zpowers_of_commute_su6Levi hf hk hK hσ' hA hm hc'.1
      (compatDiag TwistTag.E6 σ.toRingHom u) rfl
      (by rw [map_mul, hc'.2, twistHom_rootDiagUnit fun i => compatDiag_perm u i]) hst
      (fun d hd => hsD ⟨d, hDC hd⟩ (Subgroup.mem_subgroupOf.2 hd))
    exact Subgroup.mem_map.2 ⟨⟨_, hXC hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩

private theorem ggTP_core_of_conj_psu {G : Type} [Group G] {C I : Subgroup G} {f : ℕ}
    {c t : G} (hc : c ∈ I) (φ : C ≃* C)
    (hφ : ∀ x : C, (φ x : G) = c⁻¹ * x * c)
    (h : ∃ X D : Subgroup C, (Subgroup.centralizer ({c * t * c⁻¹} : Set G)).subgroupOf C = X ⊔ D ∧
      IsCyclic X ∧ Odd (Nat.card X) ∧ X ≤ Subgroup.centralizer (D : Set C) ∧
      CFSG.IsQuasisimple D ∧ Subgroup.center D = ⊥ ∧ 7 ∣ Nat.card D ∧
      (2 ^ f) ^ 15 ∣ Nat.card D ∧ CFSG.Open.StatedClassicalModel ↥D .PSU 6 2 f ∧
      ∀ s ∈ I, s * (c * t * c⁻¹) = c * t * c⁻¹ * s →
        (∀ d ∈ D, s * (d : G) = (d : G) * s) → s ∈ X.map C.subtype) :
    ∃ X D : Subgroup C, (Subgroup.centralizer ({t} : Set G)).subgroupOf C = X ⊔ D ∧
      IsCyclic X ∧ Odd (Nat.card X) ∧ X ≤ Subgroup.centralizer (D : Set C) ∧
      CFSG.IsQuasisimple D ∧ Subgroup.center D = ⊥ ∧ 7 ∣ Nat.card D ∧
      (2 ^ f) ^ 15 ∣ Nat.card D ∧ CFSG.Open.StatedClassicalModel ↥D .PSU 6 2 f ∧
      ∀ s ∈ I, s * t = t * s →
        (∀ d ∈ D, s * (d : G) = (d : G) * s) → s ∈ X.map C.subtype := by
  obtain ⟨X, D, h1, h2, h3, h4, h5, h6, h7, h8, hmodel, h9⟩ := h
  have hφs : ∀ x : C, (φ.symm x : G) = c * x * c⁻¹ := fun x => by
    have e := hφ (φ.symm x)
    rw [MulEquiv.apply_symm_apply] at e
    rw [e]
    group
  have hφ' : ∀ x : C, (φ.toMonoidHom x : G) = c⁻¹ * x * c := hφ
  have eD := equivMapOfInjective D φ.toMonoidHom φ.injective
  refine ⟨X.map φ.toMonoidHom, D.map φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, ← h1]
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hφs]
    constructor
    · intro hx
      calc c * (x : G) * c⁻¹ * (c * t * c⁻¹) = c * ((x : G) * t) * c⁻¹ := by group
        _ = c * (t * (x : G)) * c⁻¹ := by rw [hx]
        _ = c * t * c⁻¹ * (c * (x : G) * c⁻¹) := by group
    · intro hx
      calc (x : G) * t = c⁻¹ * (c * (x : G) * c⁻¹ * (c * t * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * t * c⁻¹ * (c * (x : G) * c⁻¹)) * c := by rw [hx]
        _ = t * (x : G) := by group
  · have eX := equivMapOfInjective X φ.toMonoidHom φ.injective
    exact isCyclic_of_surjective eX eX.surjective
  · rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact h3
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    have e := Subgroup.mem_centralizer_iff.1 (h4 hx) d hd
    rw [← map_mul, ← map_mul, e]
  · exact CFSG.IsQuasisimple.of_mulEquiv eD.symm h5
  · rw [← Subgroup.map_center_eq eD, h6, Subgroup.map_bot]
  · rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact h7
  · rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact h8
  · exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eD hmodel
  · intro s hs hst hsD
    have hst' : c * s * c⁻¹ * (c * t * c⁻¹) = c * t * c⁻¹ * (c * s * c⁻¹) := by
      calc c * s * c⁻¹ * (c * t * c⁻¹) = c * (s * t) * c⁻¹ := by group
        _ = c * (t * s) * c⁻¹ := by rw [hst]
        _ = c * t * c⁻¹ * (c * s * c⁻¹) := by group
    have hsD' : ∀ d ∈ D, c * s * c⁻¹ * (d : G) = (d : G) * (c * s * c⁻¹) := by
      intro d hd
      have e := hsD _ (Subgroup.mem_map_of_mem φ.toMonoidHom hd)
      rw [hφ'] at e
      calc c * s * c⁻¹ * (d : G) = c * (s * (c⁻¹ * (d : G) * c)) * c⁻¹ := by group
        _ = c * (c⁻¹ * (d : G) * c * s) * c⁻¹ := by rw [e]
        _ = (d : G) * (c * s * c⁻¹) := by group
    obtain ⟨x, hx, hxs⟩ :=
      Subgroup.mem_map.1 (h9 _ (mul_mem (mul_mem hc hs) (inv_mem hc)) hst' hsD')
    refine Subgroup.mem_map.2 ⟨φ x, Subgroup.mem_map_of_mem φ.toMonoidHom hx, ?_⟩
    show (φ x : G) = s
    rw [hφ, show (x : G) = c * s * c⁻¹ from hxs]
    group

theorem ggTP_core_psu_of_fuse
    (hFuse : ∀ {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
      (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ f) {k : Type} [Field k]
      [Algebra k K] (hk : Nat.card k = 2 ^ f) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (hFr : ∀ c, Fr c = c ^ 2 ^ f) (v : WeylGroup TwistTag.E6.tag)
      (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
      (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
      (t : ModGL TwistTag.E6.tag K) (_ht : t ∈ twistedE6InndiagGL K σ)
      (γ : Fin TwistTag.E6.tag.rank → ℤ) (hγ : IsRoot TwistTag.E6.tag γ) (p : ℕ)
      (_hp : p.Prime) (hpq : p ∣ 2 ^ f + 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (hζ1 : ζ ≠ 1)
      (hcor : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
        rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ)),
      ∃ c ∈ twistedE6InndiagGL K σ, ∃ A : SL2 k, orderOf A = Nat.card k + 1 ∧ ∃ m : ℕ,
        A ^ m ≠ 1 ∧ c * t * c⁻¹ =
          (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m))
    (f : ℕ) (hf : 1 ≤ f) :
    ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ 2 ^ f) →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ f + 1 →
      ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ 2 ^ f) →
      ∀ v : WeylGroup TwistTag.E6.tag,
        (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) →
      ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
      ∀ t ∈ twistedE6InndiagGL K σ, ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ →
      ∀ ζ : (AlgebraicClosure K)ˣ, ζ ^ p = 1 → ζ ≠ 1 →
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
          rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) →
        ∃ X D : Subgroup ↥(twistedE6RootGroup K σ),
          (Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
              (twistedE6RootGroup K σ) = X ⊔ D ∧
            IsCyclic X ∧ Odd (Nat.card X) ∧ X ≤ Subgroup.centralizer (D : Set _) ∧
            CFSG.IsQuasisimple D ∧ Subgroup.center D = ⊥ ∧ 7 ∣ Nat.card D ∧
            (2 ^ f) ^ 15 ∣ Nat.card D ∧
            CFSG.Open.StatedClassicalModel ↥D .PSU 6 2 f ∧
            ∀ s ∈ twistedE6InndiagGL K σ, s * t = t * s →
              (∀ d ∈ D, s * (d : ModGL TwistTag.E6.tag K) = (d : ModGL TwistTag.E6.tag K) * s) →
                s ∈ X.map (twistedE6RootGroup K σ).subtype := by
  intro K _ _ σ hK hσ p hp hpq Fr hFr v hv g0 hg0C hg0 t ht γ hγ ζ hζ hζ1 hcor
  haveI : Fintype K := Fintype.ofFinite K
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  have hσ2 : σ ^ 2 = 1 := by
    ext c
    rw [pow_two, RingAut.mul_apply, RingAut.one_apply]
    exact TwistedE6Pilot.apply_apply_eq hK hσ' c
  have hσ1 : σ ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := TwistedE6Pilot.exists_apply_ne hf hK hσ'
    exact hc (by rw [show σ.toRingHom c = σ c from rfl, h, RingAut.one_apply])
  have hk : Nat.card (fixSubfield σ) = 2 ^ f := by
    have h := (SteinbergBT.card_fixSubfield Nat.prime_two (by omega : 1 ≤ 2 * f)
      (by rw [hK, ← pow_mul, mul_comm]) σ).2
    rwa [orderOf_eq_prime hσ2 hσ1, Nat.mul_div_cancel_left f two_pos] at h
  obtain ⟨c, hc, A, hA, m, hm, hct⟩ :=
    hFuse σ hf hK hσ hk Fr hFr v hv g0 hg0C hg0 t ht γ hγ p hp hpq ζ hζ hζ1 hcor
  refine ggTP_core_of_conj_psu hc (twistedE6InndiagConj K σ ⟨c, hc⟩⁻¹) (fun x => ?_) ?_
  · rw [twistedE6InndiagConj_apply, Subgroup.coe_inv, inv_inv]
  · rw [hct]
    exact ggTP_core_thetaSL2_pow_psu σ hf hK hσ hk hA hm

theorem ggTPLayerModel_TwE6
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* TwE6Delta.RecipeR K n) (A : Subgroup (MulAut L'))
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hA : Nat.card A = 3 ^ 5) {c : ↥A} (hc : GGCorootPt 3 (ggTorusAut A) c) :
    ∃ (ER : Subgroup (TwE6Delta.RecipeR K n)) (X : Type) (_ : Group X),
      GGLayerOf (ggRFix ψ {(c : MulAut L')}) ER ∧ Nonempty (ER ≃* X) ∧
        Subgroup.center X = ⊥ ∧ CFSG.Open.StatedClassicalModel X .PSU 6 2 n := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    obtain ⟨m, hprime, hm⟩ := FiniteField.card K (ringChar K)
    have hcard : Fintype.card K = 2 ^ (2 * n) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, Nat.mul_comm]
    rw [hcard] at hm
    have hdvd : ringChar K ∣ 2 ^ (2 * n) := by
      rw [hm]
      exact dvd_pow_self _ m.pos.ne'
    have hrc : ringChar K = 2 :=
      (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow hprime hdvd)
    exact hrc ▸ ringChar.charP K
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 n
    with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have h30 : (3 : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Lang.E6Descent.three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.exists_cube_root
      (Ω := AlgebraicClosure K) h30
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  obtain ⟨v, g, κ, tt, hF⟩ :=
    KGL.ggTwKGFrame_holds n hn h3 K hK σ hσ ε hε Fr hFr ζ hζ hζo L' ψ A hTB hA
  obtain ⟨hψ, -, -, -, -, -, -, -⟩ := hTB
  obtain ⟨β, hβroot, hβ⟩ := hF.aut.corootPt hc
  have hne : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζo
    exact absurd hζo (by norm_num)
  have hbase : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (tt (Multiplicative.toAdd (κ c))) * g =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple β ζ) := by
    rw [KGL.KGTwFrame.t_coroot hF, hβ, ← KGL.corootTuple_eq_zetaVec_kg ζ hζ β]
  obtain ⟨X', D, hCent, hXcyc, hXodd, hXD, hDq, hDcenter, hD7, hD15, hDmodel, -⟩ :=
    ggTP_core_psu_of_fuse TwE6CorootCore.exists_conj_eq_thetaSL2_pow n hn K σ hK hσ 3
      Nat.prime_three h3 Fr hFr v hF.hv g hF.hg hF.hgF (tt (Multiplicative.toAdd (κ c)))
      (hF.ht _).1 β hβroot ζ hζ hne hbase
  have hLayer : GGLayerOf ((Subgroup.centralizer
      ({tt (Multiplicative.toAdd (κ c))} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
      (twistedE6RootGroup K σ)) D := by
    have h := KGL.ggLayerOf_sup_of_cyclic hXcyc hXD hDq
    rwa [← hCent] at h
  have hLayerR : GGLayerOf (ggRFix ψ {(c : MulAut L')}) (D.comap ε.symm.toMonoidHom) := by
    refine KGL.layer_of_centralizer_tw ε.symm ψ hψ {(c : MulAut L')}
      ({tt (Multiplicative.toAdd (κ c))} : Set (ModGL TwistTag.E6.tag K)) ?_ ?_ hLayer
    · rintro f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨tt (Multiplicative.toAdd (κ c)), rfl, fun l => hF.conj c l⟩
    · rintro d hd
      rw [Set.mem_singleton_iff] at hd
      subst hd
      exact ⟨(c : MulAut L'), rfl, fun l => hF.conj c l⟩
  refine ⟨D.comap ε.symm.toMonoidHom, ↥D, inferInstance, hLayerR, ?_, hDcenter, hDmodel⟩
  exact ⟨(ε.symm.subgroupMap (D.comap ε.symm.toMonoidHom)).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective ε.symm.surjective D))⟩

end CFSG.StandardType

end
