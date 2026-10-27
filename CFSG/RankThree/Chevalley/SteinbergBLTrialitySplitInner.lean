module

public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralMain
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.LieType.Chevalley.GraphFixedSimplePairs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate117
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  TrialityFold
open Subgroup
open scoped Pointwise commutatorElement

namespace TrialitySplitInner

section Generic

theorem exists_injective_of_map_le {C M : Type*} [Group C] [Group M] (F : C →* M)
    (hF : Function.Injective F) {X : Subgroup C} {H : Subgroup M} (hX : X.map F ≤ H) :
    ∃ φ : X →* H, Function.Injective φ :=
  ⟨(F.comp X.subtype).codRestrict H fun y => hX ⟨y, y.2, rfl⟩,
    fun _ _ h => Subtype.ext (hF (congrArg Subtype.val h))⟩

theorem derived_centralizer_embedding {C M : Type*} [Group C] [Group M] (F : C →* M)
    (hF : Function.Injective F) {x : C} {D Q H : Subgroup M}
    (hmap : (centralizer ({x} : Set C)).map F = D) (hcomm : ⁅D, D⁆ = Q)
    (hQq : CFSG.IsQuasisimple Q)
    (hZ : D ⊓ centralizer (Q : Set M) = (center D).map D.subtype)
    (hZH : (center D).map D.subtype ≤ H) :
    (⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ : Subgroup C).map F = Q ∧
      CFSG.IsQuasisimple (⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ :
        Subgroup C) ∧
      ∃ φ : (centralizer ({x} : Set C) ⊓ centralizer ((⁅centralizer ({x} : Set C),
          centralizer ({x} : Set C)⁆ : Subgroup C) : Set C) : Subgroup C) →* H,
        Function.Injective φ := by
  set Y := centralizer ({x} : Set C)
  have hRmap : (⁅Y, Y⁆ : Subgroup C).map F = Q := by
    rw [Subgroup.map_commutator, hmap, hcomm]
  have eR : (⁅Y, Y⁆ : Subgroup C) ≃* Q :=
    (Subgroup.equivMapOfInjective _ F hF).trans (MulEquiv.subgroupCongr hRmap)
  refine ⟨hRmap, CFSG.LocalCores.isQuasisimple_of_mulEquiv eR.symm hQq,
    exists_injective_of_map_le F hF ?_⟩
  rintro _ ⟨z, ⟨hzY, hzR⟩, rfl⟩
  refine hZH (hZ ▸ Subgroup.mem_inf.2 ⟨hmap ▸ ⟨z, hzY, rfl⟩,
    Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩)
  rw [← hRmap] at hw
  obtain ⟨r, hr, rfl⟩ := hw
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hzR r hr]

variable {C : Type*} [Group C] [Finite C]

theorem odd_card_commutator_of_invariant_prod
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (x : C) {X : Subgroup C}
    (hXx : X ≤ centralizer ({x} : Set C)) (hXinv : ∀ η : MulAut C, η x = x → ∀ z ∈ X, η z ∈ X)
    {N₁ N₂ : Type*} [CommGroup N₁] [IsCyclic N₁] [CommGroup N₂] [IsCyclic N₂]
    (φ : X →* N₁ × N₂) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {A S : Subgroup B} (hA : IsPGroup p A)
    (hAM : A ≤ centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B))
    (hSM : S ≤ centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B))
    (hSA : ⁅S, A⁆ ≤ (X.map (MulAut.conj : C →* MulAut C)).comap B.subtype) :
    Odd (Nat.card (⁅S, A⁆ : Subgroup B)) := by
  classical
  set b : B := ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩
  set M : Subgroup B := centralizer ({b} : Set B)
  have hfix : ∀ m ∈ M, (m : MulAut C) x = x := fun m hm =>
    apply_eq_of_commute_conj hinj (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hm))
  set β : C →* B := (MulAut.conj : C →* MulAut C).codRestrict B fun c => hB ⟨c, rfl⟩
  have hβinj : Function.Injective β := fun c d h => hinj (congrArg Subtype.val h)
  have hXM : X.map β ≤ M := by
    rintro _ ⟨z, hz, rfl⟩
    refine mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    change MulAut.conj z * MulAut.conj x = MulAut.conj x * MulAut.conj z
    rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 (hXx hz))]
  set Q : Subgroup M := (X.map β).subgroupOf M
  have hQnormal : Q.Normal := by
    refine ⟨fun n hn m => ?_⟩
    obtain ⟨z, hz, hzn⟩ := hn
    refine ⟨(m : MulAut C) z, hXinv _ (hfix m m.2) z hz, Subtype.ext ?_⟩
    change MulAut.conj ((m : MulAut C) z) =
      (m : MulAut C) * ((n : B) : MulAut C) * (m : MulAut C)⁻¹
    rw [← mulAut_conj_conj_inv,
      show MulAut.conj z = ((n : B) : MulAut C) from congrArg Subtype.val hzn]
  have : Q.Normal := hQnormal
  let eQ : X ≃* Q := (Subgroup.equivMapOfInjective X β hβinj).trans
    (Subgroup.subgroupOfEquivOfLe hXM).symm
  set ψ : Q →* N₁ × N₂ := φ.comp eQ.symm.toMonoidHom
  have hψ : Function.Injective ψ := hφ.comp eQ.symm.injective
  have hQab : ∀ u ∈ Q, ∀ v ∈ Q, u * v = v * u := by
    intro u hu v hv
    have h := hψ.eq_iff.1 (show ψ (⟨u, hu⟩ * ⟨v, hv⟩) = ψ (⟨v, hv⟩ * ⟨u, hu⟩) by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  have hgen : ∃ T : Sylow 2 Q, ∃ u v : Q, closure ({u, v} : Set Q) = (T : Subgroup Q) := by
    obtain ⟨T⟩ : Nonempty (Sylow 2 Q) := inferInstance
    obtain ⟨-, u, v, huv⟩ := comm_and_two_generated_of_injective_prod
      (ψ.comp (T : Subgroup Q).subtype) (hψ.comp (T : Subgroup Q).subtype_injective)
    refine ⟨T, u, v, ?_⟩
    have h := congrArg (Subgroup.map (T : Subgroup Q).subtype) huv
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hA' : IsPGroup p (A.subgroupOf M) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAM).symm
  have hmap : ⁅S.subgroupOf M, A.subgroupOf M⁆.map M.subtype = ⁅S, A⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hSM, inf_of_le_left hAM]
  have hSA' : ⁅S.subgroupOf M, A.subgroupOf M⁆ ≤ Q := by
    intro w hw
    have h1 : (w : B) ∈ ⁅S, A⁆ := hmap ▸ Subgroup.mem_map_of_mem M.subtype hw
    obtain ⟨z, hz, hzw⟩ := hSA h1
    exact ⟨z, hz, Subtype.ext hzw⟩
  have hodd := CFSG.RankThree.GroupTheory.SteinbergBM.abelian_two_generator_two_part_commutators_odd
    hQab hgen hp hp3 hA' hSA'
  rw [← hmap, Subgroup.card_map_of_injective M.subtype_injective]
  exact hodd

end Generic

section RootPairs

theorem graphFixedRootPair_neg {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}
    (O : Set (Fin t.tag.rank → ℤ)) :
    graphFixedRootPair t K σ (-O) = graphFixedRootPair t K σ O := by
  rw [graphFixedRootPair, graphFixedRootPair, neg_neg, sup_comm]

theorem graphFixedRootPair_mono {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}
    {O₁ O₂ : Set (Fin t.tag.rank → ℤ)} (h : O₁ ⊆ O₂) :
    graphFixedRootPair t K σ O₁ ≤ graphFixedRootPair t K σ O₂ :=
  sup_le_sup (inf_le_inf_right _ (rootSpan_mono h))
    (inf_le_inf_right _ (rootSpan_mono (Set.neg_subset_neg.2 h)))

theorem orbitRankOneGroup_eq_graphFixedRootPair {t : TwistTag} {K : Type} [Field K]
    {σ : K →+* K} (b : Fin t.foldedTag.rank) :
    orbitRankOneGroup t K σ b = graphFixedRootPair t K σ (fixedOrbitImage t 1 b) := by
  have h1 : orbitConjRankOneHom t K σ 1 b = orbitRankOneHom t K σ b :=
    MonoidHom.ext fun g => by
      rw [orbitConjRankOneHom_apply, canonicalRep_one, one_mul, inv_one, mul_one]
  rw [← range_orbitConjRankOneHom (one_mem _) b, h1, orbitRankOneHom_range]
  rfl

theorem graphFixedRootGroup_D4_eq_sup (K : Type) [Field K] (σ : K ≃+* K) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom =
      orbitRankOneGroup TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ ⊔
        orbitRankOneGroup TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ := by
  rw [(exceptional_fixed_simple_pair_generation TwistTag.D4 K σ).1]
  refine le_antisymm (iSup_le fun b => ?_) (sup_le (le_iSup _ _) (le_iSup _ _))
  rcases foldedD4_cases b with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem orbitRankOneGroup_le_graphFixedRootPair {K : Type} [Field K] {σ : K →+* K}
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α)
    {b : Fin TwistTag.D4.foldedTag.rank} {i₀ : Fin TwistTag.D4.tag.rank}
    (hb : ∀ i ∈ TwistTag.D4.orbit b,
      fold (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = fold (Pi.single i₀ 1))
    (hi₀ : (Pi.single i₀ 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈
      (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ∪
        -(TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ))) :
    orbitRankOneGroup TwistTag.D4 K σ b ≤
      graphFixedRootPair TwistTag.D4 K σ
        (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
  rw [orbitRankOneGroup_eq_graphFixedRootPair]
  rcases hi₀ with h | h
  · refine graphFixedRootPair_mono fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [one_smul, Finset.mem_coe]
    refine mem_diagramOrbit_of_fold_eq hα (isRoot_single _ i) ?_
    rw [hb i hi, fold_eq_of_mem_diagramOrbit h]
  · refine (graphFixedRootPair_mono
      (O₂ := -(TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)))
      fun x hx => ?_).trans_eq (graphFixedRootPair_neg _)
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [one_smul, Set.mem_neg, Finset.mem_coe]
    refine mem_diagramOrbit_of_fold_eq hα (IsRoot.neg (isRoot_single _ i)) ?_
    rw [fold_neg, hb i hi, ← fold_neg]
    exact fold_eq_of_mem_diagramOrbit (Set.mem_neg.1 h)

end RootPairs

section Torus

theorem triality_fieldQuotient_data {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    (∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) ∧
    IsCyclic (K ≃+* K) ∧ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ := by
  rcases eq_or_ne ℓ 2 with rfl | hℓ2
  · obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, hcyc, -, -, hZ, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact ⟨⟨Θ, hΘ, hker⟩, hcyc, hZ⟩
  · obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, hcyc, -, -, hZ, -⟩ :=
      odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
    exact ⟨⟨Θ, hΘ, hker⟩, hcyc, hZ⟩

theorem card_trialityFixedField {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (trialityFixedField K σ.toRingHom) = ℓ ^ f := by
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    change σ (σ (σ c)) = c
    exact ringEquiv_cube_apply_eq hK hσ c
  obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  rw [← hL2, card_orbitField_D4_orientation hℓ hf hK (r := 1) (Or.inl rfl)
    (σ := σ.toRingHom) (by simpa using hσ) ⟨1, by decide⟩,
    show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one]

theorem exists_fixedUnit_orderOf_eq {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ ℓ ^ f - 1) :
    ∃ ζ : (trialityFixedField K σ.toRingHom)ˣ, orderOf ζ = p ∧
      orderOf (trialityFixedUnit K σ ζ) = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (trialityFixedField K σ.toRingHom)ˣ) p
    (by rw [Nat.card_units, card_trialityFixedField hℓ hf hK σ hσ]; exact hpq)
  refine ⟨ζ, hζ, ?_⟩
  rw [orderOf_injective _ (fun a b h => Units.ext (Subtype.ext (congrArg Units.val h))) ζ, hζ]

theorem trialityOuter_mul_middle_pow_eq {K : Type} [Field K] (σ : K ≃+* K)
    (ζ : (trialityFixedField K σ.toRingHom)ˣ) (u v : ℕ) :
    trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) * trialityMiddleTorus K σ (ζ ^ v) =
      rootDiagUnit TwistTag.D4.tag (d4Tuple
        ((trialityFixedUnit K σ ζ ^ u) ^ 2 * (trialityFixedUnit K σ ζ ^ v)⁻¹)
        ((trialityFixedUnit K σ ζ ^ u) ^ 2 * (trialityFixedUnit K σ ζ ^ v)⁻¹)
        ((trialityFixedUnit K σ ζ ^ u * trialityFixedUnit K σ ζ ^ u *
          trialityFixedUnit K σ ζ ^ u)⁻¹ * (trialityFixedUnit K σ ζ ^ v) ^ 2)
        ((trialityFixedUnit K σ ζ ^ u) ^ 2 * (trialityFixedUnit K σ ζ ^ v)⁻¹)) := by
  have hσz : ∀ m : ℕ, Units.map σ.toRingHom.toMonoidHom (trialityFixedUnit K σ ζ ^ m) =
      trialityFixedUnit K σ ζ ^ m := fun m =>
    Units.ext (by
      change σ ((trialityFixedUnit K σ ζ ^ m : Kˣ) : K) = ((trialityFixedUnit K σ ζ ^ m : Kˣ) : K)
      rw [Units.val_pow_eq_pow_val, map_pow, sigma_trialityFixedUnit])
  have hy : trialityFixedUnit K σ (ζ ^ v) = trialityFixedUnit K σ ζ ^ v := map_pow _ _ _
  rw [trialityOuter_mul_middle_eq, hy, hσz, hσz]

theorem exists_torus_coords_of_pow_eq_one {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {p : ℕ} (hp : p.Prime)
    (eT : (Kˣ × (trialityFixedField K σ.toRingHom)ˣ) ≃*
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom)
    (heT : ∀ a b, (eT (a, b) : ModGL TwistTag.D4.tag K) =
      trialityOuterTorus K σ a * trialityMiddleTorus K σ b)
    {ζ : (trialityFixedField K σ.toRingHom)ˣ} (hζ : orderOf ζ = p)
    (hζ' : orderOf (trialityFixedUnit K σ ζ) = p) {y : ModGL TwistTag.D4.tag K}
    (hy : y ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom) (hyp : y ^ p = 1) :
    ∃ u v : ℕ, y = trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) *
      trialityMiddleTorus K σ (ζ ^ v) := by
  set ab := eT.symm ⟨y, hy⟩ with hab
  have hab1 : ab ^ p = 1 := by
    have h1 : (⟨y, hy⟩ : graphFixedRootTorus TwistTag.D4 K σ.toRingHom) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hyp)
    rw [hab, ← map_pow, h1, map_one]
  have ha : ab.1 ^ p = 1 := by rw [← Prod.pow_fst, hab1, Prod.fst_one]
  have hb : ab.2 ^ p = 1 := by rw [← Prod.pow_snd, hab1, Prod.snd_one]
  obtain ⟨u, hu⟩ := (Submonoid.mem_powers_iff _ _).1
    ((isOfFinOrder_of_finite _).mem_powers_iff_mem_zpowers.2
      (mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hζ' ha))
  obtain ⟨v, hv⟩ := (Submonoid.mem_powers_iff _ _).1
    ((isOfFinOrder_of_finite _).mem_powers_iff_mem_zpowers.2
      (mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hζ hb))
  refine ⟨u, v, ?_⟩
  rw [hu, hv, ← heT]
  change y = ((eT ab : graphFixedRootTorus TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K)
  rw [hab, MulEquiv.apply_symm_apply]

end Torus

set_option hygiene false in
local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

theorem triality_odd_card_commutator_split_inner {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f - 1)
    (B : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hB : (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (t : B) (htE : t ∈ E) (ht1 : t ≠ 1)
    (htinn : (t : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), E⁆ :
      Subgroup B)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨⟨Θ, -, hΘker⟩, hcyc, hZ⟩ := triality_fieldQuotient_data hℓ hf K hK σ hσ
  set R := (MulAut.conj : 𝒞 →* MulAut 𝒞).range
  have hinj : Function.Injective (MulAut.conj : 𝒞 →* MulAut 𝒞) :=
    mulAut_conj_injective_of_center_eq_bot hZ
  obtain ⟨hconjH, ⟨eT, heT⟩, -, -, hcases⟩ :=
    triality_split_prime_toral_Sylow_and_centralizers hℓ hf K hK σ hσ hp hp3 hpq
  obtain ⟨ζ, hζ, hζ'⟩ := exists_fixedUnit_orderOf_eq hℓ hf hK σ hσ hp hpq
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) a ha
  obtain ⟨x, hx⟩ := htinn
  have htx : t = ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
  subst htx
  have htp : orderOf (⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B) = p := orderOf_eq_prime (hEpow _ htE) ht1
  have hxp : orderOf x = p := by
    rw [← orderOf_injective _ hinj x, ← htp, Subgroup.orderOf_mk]
  have hPx : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxp, pow_one])
  obtain ⟨g, hg⟩ := hconjH _ hPx
  have hgx : ((g * x * g⁻¹ : 𝒞) : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    Subgroup.mem_subgroupOf.1 (hg ⟨x, Subgroup.mem_zpowers x, rfl⟩)
  have hgxp : ((g * x * g⁻¹ : 𝒞) : ModGL TwistTag.D4.tag K) ^ p = 1 := by
    rw [← Subgroup.coe_pow, conj_pow, ← hxp, pow_orderOf_eq_one, mul_one, mul_inv_cancel,
      Subgroup.coe_one]
  obtain ⟨u, v, huv⟩ := exists_torus_coords_of_pow_eq_one hp eT heT hζ hζ' hgx hgxp
  have hne : trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) *
      trialityMiddleTorus K σ (ζ ^ v) ≠ 1 := by
    rw [← huv]
    intro h1
    have hx1 : x = 1 := conj_eq_one_iff.1 (Subtype.ext h1)
    rw [hx1, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  obtain ⟨a, ha, -, hcase⟩ := hcases ζ hζ u v hne
  set F := (𝒞).subtype.comp (MulAut.conj g).toMonoidHom with hFdef
  have hF : Function.Injective F := Subtype.val_injective.comp (MulAut.conj g).injective
  have hmap : (centralizer ({x} : Set 𝒞)).map F =
      𝒞 ⊓ Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} := by
    rw [hFdef, ← Subgroup.map_map, map_conj_centralizer_singleton_eq,
      map_subtype_centralizer_singleton, huv.trans ha]
  set b : B := ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩
  set S := inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set B))
  have hSM : S ≤ centralizer ({b} : Set B) := Subgroup.map_subtype_le _
  have hEM : E ≤ centralizer ({b} : Set B) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val
      (hE.is_comm.comm (⟨b, htE⟩ : E) ⟨e, he⟩)).symm
  have hfixM : ∀ m ∈ centralizer ({b} : Set B), (m : MulAut 𝒞) x = x :=
    fun m hm => apply_eq_of_commute_conj hinj
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hm))
  have hgenY : ∀ s ∈ S, ∀ e ∈ E, ∃ c ∈ centralizer ({x} : Set 𝒞),
      MulAut.conj c = ((⁅s, e⁆ : B) : MulAut 𝒞) := by
    intro s hs e he
    have hct : ⁅s, e⁆ ∈ centralizer ({b} : Set B) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hSM hs) (hEM he)) (inv_mem (hSM hs))) (inv_mem (hEM he))
    have hΘ : ((⁅s, e⁆ : B) : MulAut 𝒞) ∈ R := by
      rw [← hΘker, MonoidHom.mem_ker, show ((⁅s, e⁆ : B) : MulAut 𝒞) =
        ⁅(s : MulAut 𝒞), (e : MulAut 𝒞)⁆ from map_commutatorElement B.subtype s e,
        map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact IsMulCommutative.is_comm.comm _ _
    obtain ⟨c, hc⟩ := hΘ
    refine ⟨c, Subgroup.mem_centralizer_singleton_iff.2 (hinj ?_), hc⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hct)
    simp only [Subgroup.coe_mul] at h1
    rw [map_mul, map_mul, hc]
    exact h1
  rcases hcase with ⟨-, hMH⟩ |
    ⟨α, -, -, -, D, Q, hDdef, -, -, -, -, -, hQq, hcomm, hZD, hZH, -, -⟩
  ·
    obtain ⟨φ, hφ⟩ := exists_injective_of_map_le F hF (hmap.trans hMH).le
    refine odd_card_commutator_of_invariant_prod hinj hB x le_rfl
      (fun η hη z hz => apply_mem_centralizer_of_apply_eq hη hz) (eT.symm.toMonoidHom.comp φ)
      (eT.symm.injective.comp hφ) hp hp3 (IsElementaryAbelian.isPGroup p E) hEM hSM ?_
    rw [Subgroup.commutator_le]
    intro s hs e he
    obtain ⟨c, hc, hce⟩ := hgenY s hs e he
    exact ⟨c, hc, hce⟩
  ·
    obtain ⟨-, hRq, φ, hφ⟩ :=
      derived_centralizer_embedding F hF (hmap.trans hDdef.symm) hcomm hQq hZD hZH
    have hRY : (⁅centralizer ({x} : Set 𝒞), centralizer ({x} : Set 𝒞)⁆ : Subgroup 𝒞) ≤
        centralizer ({x} : Set 𝒞) :=
      Subgroup.commutator_le.2 fun u hu v hv => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
    have hfixR := aschbacherSolvableCore_fixes_quasisimple hinj hp hB x hRY
      (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hRq
    refine odd_card_commutator_of_invariant_prod hinj hB x inf_le_left
      (fun η hη z hz => apply_mem_centralizer_derived_of_apply_eq hη hz)
      (eT.symm.toMonoidHom.comp φ) (eT.symm.injective.comp hφ) hp hp3
      (IsElementaryAbelian.isPGroup p E) hEM hSM ?_
    rw [Subgroup.commutator_le]
    intro s hs e he
    obtain ⟨c, hc, hce⟩ := hgenY s hs e he
    refine ⟨c, Subgroup.mem_inf.2 ⟨hc, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩, hce⟩
    have he' : ((e : B) : MulAut 𝒞)⁻¹ x = x := by
      nth_rewrite 1 [← hfixM e (hEM he)]
      exact MulAut.inv_apply_self _ _ _
    have h1 : (MulAut.conj c) r = r := by
      rw [hce, show ((⁅s, e⁆ : B) : MulAut 𝒞) =
        ⁅(s : MulAut 𝒞), (e : MulAut 𝒞)⁆ from map_commutatorElement B.subtype s e]
      exact commutatorElement_apply_of_fixed (hfixR s hs r hr)
        (hfixR s hs _ (apply_mem_commutator_centralizer_of_apply_eq he' hr))
    rw [MulAut.conj_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm

theorem triality_thetaT_eq_bot_split {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f - 1)
    (B : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hB : (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    thetaT p E = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨⟨Θ, hΘ, -⟩, -, hZ⟩ := triality_fieldQuotient_data hℓ hf K hK σ hσ
  set R := (MulAut.conj : 𝒞 →* MulAut 𝒞).range
  have hinj : Function.Injective (MulAut.conj : 𝒞 →* MulAut 𝒞) :=
    mulAut_conj_injective_of_center_eq_bot hZ
  obtain ⟨hconjH, ⟨eT, heT⟩, -, -, hcases⟩ :=
    triality_split_prime_toral_Sylow_and_centralizers hℓ hf K hK σ hσ hp hp3 hpq
  obtain ⟨ζ, hζ, hζ'⟩ := exists_fixedUnit_orderOf_eq hℓ hf hK σ hσ hp hpq
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) a ha
  by_cases hEinn : E.map B.subtype ≤ R
  swap
  ·
    obtain ⟨b, hbE, hbinn⟩ : ∃ b ∈ E, (b : MulAut 𝒞) ∉ R := by
      by_contra h
      push Not at h
      exact hEinn (by rintro _ ⟨b, hb, rfl⟩; exact h b hb)
    have hb1 : b ≠ 1 := fun h => hbinn (by rw [h]; exact one_mem _)
    have hbp : orderOf b = p := orderOf_eq_prime (hEpow b hbE) hb1
    have hcore := (triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK
      σ hσ Θ hΘ hp hp3 B hB b hbinn hbp).2.2.2
    refine eq_bot_iff.2 (iInf_le_of_le b (iInf_le_of_le hbE (iInf_le_of_le hb1 ?_)))
    rw [inSubgroup, hcore, Subgroup.map_bot]
  set P : Subgroup 𝒞 := (E.map B.subtype).comap MulAut.conj
  have hPmap : P.map MulAut.conj = E.map B.subtype := Subgroup.map_comap_eq_self hEinn
  have eP : E ≃* P := (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective).trans
    ((MulEquiv.subgroupCongr hPmap.symm).trans (Subgroup.equivMapOfInjective P _ hinj).symm)
  have hPcard : Nat.card P = p ^ 2 := by rw [← Nat.card_congr eP.toEquiv, hEcard]
  have hPp : IsPGroup p P := (IsElementaryAbelian.isPGroup p E).of_equiv eP
  have hPpow : ∀ u ∈ P, u ^ p = 1 := fun u hu => by
    obtain ⟨e, he, hee⟩ := hu
    apply hinj
    rw [map_pow, ← hee, map_one]
    exact congrArg Subtype.val (hEpow e he)
  obtain ⟨g, hg⟩ := hconjH P hPp
  set F := (𝒞).subtype.comp (MulAut.conj g).toMonoidHom with hFdef
  have hF : Function.Injective F := Subtype.val_injective.comp (MulAut.conj g).injective
  have hFP : ∀ u ∈ P, F u ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := fun u hu =>
    Subgroup.mem_subgroupOf.1 (hg ⟨u, hu, rfl⟩)
  set ψ : P →* Kˣ × (trialityFixedField K σ.toRingHom)ˣ :=
    eT.symm.toMonoidHom.comp ((F.comp P.subtype).codRestrict _ fun u => hFP u u.2)
  have hψ : Function.Injective ψ := eT.symm.injective.comp fun u w h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (hF h')
  set T : Subgroup (Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :=
    (zpowers (trialityFixedUnit K σ ζ)).prod (zpowers ζ) with hTdef
  have hψT : ψ.range = T := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨u, rfl⟩
      have hu : ψ u ^ p = 1 := by
        rw [← map_pow, show u ^ p = 1 from
          Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hPpow u u.2), map_one]
      exact Subgroup.mem_prod.2 ⟨mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hζ'
        (by rw [← Prod.pow_fst, hu, Prod.fst_one]),
        mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hζ (by rw [← Prod.pow_snd, hu, Prod.snd_one])⟩
    · have h1 : Nat.card T = p * p := by
        rw [hTdef, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
          Nat.card_zpowers, Nat.card_zpowers, hζ, hζ']
      have h2 : Nat.card ψ.range = p ^ 2 := by
        rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hPcard]
      rw [h1, h2, sq]
  have hpt : ∀ u₀ v₀ : ℕ, trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u₀) *
      trialityMiddleTorus K σ (ζ ^ v₀) ≠ 1 → ∃ u ∈ P, u ≠ 1 ∧
        F u = trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u₀) *
          trialityMiddleTorus K σ (ζ ^ v₀) := by
    intro u₀ v₀ hne
    have hmem : (trialityFixedUnit K σ ζ ^ u₀, ζ ^ v₀) ∈ ψ.range := by
      rw [hψT]
      exact Subgroup.mem_prod.2 ⟨pow_mem (mem_zpowers _) _, pow_mem (mem_zpowers _) _⟩
    obtain ⟨u, hu⟩ := hmem
    have hFu : F u = trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u₀) *
        trialityMiddleTorus K σ (ζ ^ v₀) := by
      have h3 : eT (ψ u) = (F.comp P.subtype).codRestrict _ (fun u => hFP u u.2) u :=
        eT.apply_symm_apply _
      rw [← heT, ← hu, h3]
      rfl
    exact ⟨u, u.2, fun h1 => hne (by rw [← hFu, h1, map_one]), hFu⟩
  have key : ∀ (b : Fin TwistTag.D4.foldedTag.rank) (i₀ : Fin TwistTag.D4.tag.rank) (u₀ v₀ : ℕ),
      (∀ i ∈ TwistTag.D4.orbit b,
        fold (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = fold (Pi.single i₀ 1)) →
      trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u₀) *
        trialityMiddleTorus K σ (ζ ^ v₀) ≠ 1 →
      (∀ a : Fin TwistTag.D4.tag.rank → Kˣ,
        trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u₀) *
          trialityMiddleTorus K σ (ζ ^ v₀) = rootDiagUnit TwistTag.D4.tag a → a i₀ = 1) →
      ∃ u ∈ P, u ≠ 1 ∧
        orbitRankOneGroup TwistTag.D4 K σ.toRingHom b ≤
          (⁅centralizer ({u} : Set 𝒞), centralizer ({u} : Set 𝒞)⁆ : Subgroup 𝒞).map F ∧
        CFSG.IsQuasisimple (⁅centralizer ({u} : Set 𝒞), centralizer ({u} : Set 𝒞)⁆ :
          Subgroup 𝒞) := by
    intro b i₀ u₀ v₀ hb hne hai
    obtain ⟨u, huP, hu1, hFu⟩ := hpt u₀ v₀ hne
    obtain ⟨a, ha, -, hcase⟩ := hcases ζ hζ u₀ v₀ hne
    have hai₀ : (Pi.single i₀ 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ rootCharKernel a :=
      ⟨isRoot_single _ i₀, by rw [rootChar_pi_single, hai a ha]⟩
    have hmap : (centralizer ({u} : Set 𝒞)).map F =
        𝒞 ⊓ Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} := by
      rw [hFdef, ← Subgroup.map_map, map_conj_centralizer_singleton_eq,
        map_subtype_centralizer_singleton,
        show ((g * u * g⁻¹ : 𝒞) : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag a
          from hFu.trans ha]
    rcases hcase with ⟨hker, -⟩ |
      ⟨α, hαr, -, hker, D, Q, hDdef, hQdef, -, -, -, -, hQq, hcomm, hZD, hZH, -, -⟩
    · rw [hker] at hai₀
      exact absurd hai₀ (Set.notMem_empty _)
    obtain ⟨hRmap, hRq, -⟩ :=
      derived_centralizer_embedding F hF (hmap.trans hDdef.symm) hcomm hQq hZD hZH
    refine ⟨u, huP, hu1, ?_, hRq⟩
    rw [hRmap, hQdef]
    rw [hker] at hai₀
    exact orbitRankOneGroup_le_graphFixedRootPair hαr hb hai₀
  have hz1 : trialityFixedUnit K σ ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ'
    exact hp.one_lt.ne hζ'
  have hne₁ : trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ 1) *
      trialityMiddleTorus K σ (ζ ^ 2) ≠ 1 := by
    rw [trialityOuter_mul_middle_pow_eq, ← rootDiagUnit_one]
    intro h
    have h2 : (trialityFixedUnit K σ ζ ^ 1 * trialityFixedUnit K σ ζ ^ 1 *
        trialityFixedUnit K σ ζ ^ 1)⁻¹ * (trialityFixedUnit K σ ζ ^ 2) ^ 2 = 1 :=
      congrFun (rootDiagUnit_injective h) i2
    exact hz1 (calc trialityFixedUnit K σ ζ = (trialityFixedUnit K σ ζ ^ 1 *
        trialityFixedUnit K σ ζ ^ 1 * trialityFixedUnit K σ ζ ^ 1)⁻¹ *
          (trialityFixedUnit K σ ζ ^ 2) ^ 2 := by group
      _ = 1 := h2)
  have hai₁ : ∀ a : Fin TwistTag.D4.tag.rank → Kˣ,
      trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ 1) * trialityMiddleTorus K σ (ζ ^ 2) =
        rootDiagUnit TwistTag.D4.tag a → a i0 = 1 := fun a ha => by
    rw [trialityOuter_mul_middle_pow_eq] at ha
    rw [← rootDiagUnit_injective ha]
    change (trialityFixedUnit K σ ζ ^ 1) ^ 2 * (trialityFixedUnit K σ ζ ^ 2)⁻¹ = 1
    group
  have hne₂ : trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ 2) *
      trialityMiddleTorus K σ (ζ ^ 3) ≠ 1 := by
    rw [trialityOuter_mul_middle_pow_eq, ← rootDiagUnit_one]
    intro h
    have h0 : (trialityFixedUnit K σ ζ ^ 2) ^ 2 * (trialityFixedUnit K σ ζ ^ 3)⁻¹ = 1 :=
      congrFun (rootDiagUnit_injective h) i0
    exact hz1 (calc trialityFixedUnit K σ ζ =
        (trialityFixedUnit K σ ζ ^ 2) ^ 2 * (trialityFixedUnit K σ ζ ^ 3)⁻¹ := by group
      _ = 1 := h0)
  have hai₂ : ∀ a : Fin TwistTag.D4.tag.rank → Kˣ,
      trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ 2) * trialityMiddleTorus K σ (ζ ^ 3) =
        rootDiagUnit TwistTag.D4.tag a → a i2 = 1 := fun a ha => by
    rw [trialityOuter_mul_middle_pow_eq] at ha
    rw [← rootDiagUnit_injective ha]
    change (trialityFixedUnit K σ ζ ^ 2 * trialityFixedUnit K σ ζ ^ 2 *
      trialityFixedUnit K σ ζ ^ 2)⁻¹ * (trialityFixedUnit K σ ζ ^ 3) ^ 2 = 1
    group
  obtain ⟨u₁, hu₁, hu₁1, hM₁, hq₁⟩ := key ⟨0, by decide⟩ i0 1 2 (by decide) hne₁ hai₁
  obtain ⟨u₂, hu₂, hu₂1, hM₂, hq₂⟩ := key ⟨1, by decide⟩ i2 2 3 (by decide) hne₂ hai₂
  have hFtop : (⊤ : Subgroup 𝒞).map F = 𝒞 := by
    ext z
    refine ⟨fun ⟨y, _, hy⟩ => hy ▸ ((MulAut.conj g) y).2, fun hz =>
      ⟨g⁻¹ * (⟨z, hz⟩ : 𝒞) * g, Subgroup.mem_top _, ?_⟩⟩
    change ((g * (g⁻¹ * (⟨z, hz⟩ : 𝒞) * g) * g⁻¹ : 𝒞) : ModGL TwistTag.D4.tag K) = z
    rw [show g * (g⁻¹ * (⟨z, hz⟩ : 𝒞) * g) * g⁻¹ = (⟨z, hz⟩ : 𝒞) by group]
  have htop : (⁅centralizer ({u₁} : Set 𝒞), centralizer ({u₁} : Set 𝒞)⁆ : Subgroup 𝒞) ⊔
      ⁅centralizer ({u₂} : Set 𝒞), centralizer ({u₂} : Set 𝒞)⁆ = ⊤ := by
    apply Subgroup.map_injective hF
    rw [Subgroup.map_sup, hFtop]
    refine le_antisymm (sup_le ((Subgroup.map_mono le_top).trans hFtop.le)
      ((Subgroup.map_mono le_top).trans hFtop.le)) ?_
    exact (graphFixedRootGroup_D4_eq_sup K σ).le.trans (sup_le_sup hM₁ hM₂)
  have hbE : ∀ u ∈ P, (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ∈ E := fun u hu => by
    obtain ⟨e, he, hee⟩ := hu
    rwa [show (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) = e from Subtype.ext hee.symm]
  have hb1 : ∀ u : 𝒞, u ≠ 1 → (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ≠ 1 :=
    fun u hu h => hu (hinj (congrArg Subtype.val h))
  have hRY : ∀ u : 𝒞, (⁅centralizer ({u} : Set 𝒞), centralizer ({u} : Set 𝒞)⁆ : Subgroup 𝒞) ≤
      centralizer ({u} : Set 𝒞) := fun u =>
    Subgroup.commutator_le.2 fun v hv w hw => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hv hw) (inv_mem hv)) (inv_mem hw)
  have hfix₁ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₁ (hRY u₁)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₁
  have hfix₂ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₂ (hRY u₂)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₂
  rw [eq_bot_iff]
  intro s hs
  have hmem : ∀ a ∈ E, a ≠ 1 → s ∈ inSubgroup (aschbacherSolvableCore p)
      (centralizer ({a} : Set B)) := by
    simp only [thetaT, Subgroup.mem_iInf] at hs
    exact hs
  have hs₁ := hmem _ (hbE u₁ hu₁) (hb1 u₁ hu₁1)
  have hs₂ := hmem _ (hbE u₂ hu₂) (hb1 u₂ hu₂1)
  have hle : (⁅centralizer ({u₁} : Set 𝒞), centralizer ({u₁} : Set 𝒞)⁆ : Subgroup 𝒞) ⊔
      ⁅centralizer ({u₂} : Set 𝒞), centralizer ({u₂} : Set 𝒞)⁆ ≤
      MonoidHom.eqLocus (s : MulAut 𝒞).toMonoidHom (MonoidHom.id _) :=
    sup_le (fun r hr => hfix₁ s hs₁ r hr) (fun r hr => hfix₂ s hs₂ r hr)
  rw [htop] at hle
  rw [Subgroup.mem_bot]
  exact Subtype.ext (MulEquiv.ext fun y => hle (Subgroup.mem_top y))

end TrialitySplitInner

open TrialitySplitInner

theorem triality_split_prime_inner_actor_local_core_product_odd {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f - 1)
    (B : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hB : (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) (t : B)
    (htE : t ∈ E) (ht1 : t ≠ 1)
    (htinn : (t : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    thetaT p E = ⊥ ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ :
      Subgroup B)) ∧
    ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ : Subgroup B) :
        Set B) * (thetaT p E : Set B) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔ thetaT p E :
        Subgroup B) : Set B) ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔
      thetaT p E)) := by
  have hIB := triality_thetaT_eq_bot_split hℓ hf K hK σ hσ hp hp3 hpq B hB E hE hEcard
  have hodd := triality_odd_card_commutator_split_inner hℓ hf K hK σ hσ hp hp3 hpq B hB E hE t
    htE ht1 htinn
  refine ⟨hIB, hodd, ?_, ?_⟩
  · rw [hIB, sup_bot_eq, Subgroup.coe_bot, Set.singleton_one, mul_one]
  · rw [hIB, sup_bot_eq]
    exact hodd

end CFSG.RankThree.Chevalley
