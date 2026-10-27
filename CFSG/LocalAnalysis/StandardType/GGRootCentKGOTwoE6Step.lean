module

public import CFSG.Assembly.Defs
public import CFSG.Blueprint.Chevalley
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutDTwo
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExcStep
import CFSG.LocalAnalysis.StandardType.GGRootCentKGRigid
import CFSG.LocalAnalysis.StandardType.GGRootNormInner
import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
import CFSG.Monster.B.Geometry.CoxeterWords
import CFSG.RankThree.PartOne.KE.A1SL2
import CFSG.RankThree.PartOne.KE.A1Torus
import CFSG.RankThree.PartOne.KE.A2Family
import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.E6Pilot
  CFSG.Timmesfeld.LieEmbed

namespace KGE6

private theorem exists_mulAut_conj_of_mem_normalizer {U G : Type*} [Group U] [Group G]
    {ψ : U →* G} (hψ : Function.Injective ψ) {a : G}
    (ha : a ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ α : MulAut U, ∀ k : U, a * ψ k * a⁻¹ = ψ (α k) := by
  let Θ : U ≃* ψ.range := MonoidHom.ofInjective hψ
  let α : MulAut U := (Θ.trans (ψ.range.normalizerMonoidHom ⟨a, ha⟩)).trans Θ.symm
  have hΘ : ∀ x : U, ((Θ x : ψ.range) : G) = ψ x := fun x => by
    show ((MonoidHom.ofInjective hψ x : ψ.range) : G) = ψ x
    rw [MonoidHom.ofInjective_apply]
  refine ⟨α, fun k => ?_⟩
  have h1 : ((Θ (α k) : ψ.range) : G) = a * ψ k * a⁻¹ := by
    have e : Θ (α k) = ψ.range.normalizerMonoidHom ⟨a, ha⟩ (Θ k) := by
      simp only [α, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [e, GGRootNorm.coe_normalizerMonoidHom, hΘ k]
  exact h1.symm.trans (hΘ (α k))

section StepFour

variable {K : Type} [Field K] [CharP K 2]

theorem exactNormalAut_pinnedElt_highRoot {a : Fin Tag.E6.rank → Kˣ} {σ : K ≃+* K}
    {ε : Fin (exactE .E6)} (hθ : rootChar a (highRoot .E6) = 1) :
    exactNormalAut .E6 K a σ ε (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) =
      EPilot.pinnedElt .E6 (highRoot .E6) 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hσ : Units.map (entrywiseHom σ.toRingHom) (pinnedX .E6 K (highRoot .E6) 1 :
      ModGL .E6 K) = pinnedX .E6 K (highRoot .E6) 1 := by
    rw [CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX, map_one]
  have hQ : exactQ .E6 K ε * pinnedX .E6 K (highRoot .E6) 1 * (exactQ .E6 K ε)⁻¹ =
      pinnedX .E6 K (highRoot .E6) 1 := by
    rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by
      have := ε.isLt
      change (ε : ℕ) < 2 at this
      omega) with h | h
    · rw [h, exactQ_zero, one_mul, inv_one, mul_one]
    · rw [show exactQ .E6 K (ε : ℕ) = exactQ .E6 K 1 by rw [h],
        exactQ_one_conj_pinnedX h2 (isRoot_highRoot .E6) 1, permLattice_highRoot_E6.1]
  refine Subtype.ext ?_
  rw [coe_exactNormalAut]
  show rootDiagUnit .E6 a * exactQ .E6 K ε *
      Units.map (entrywiseHom σ.toRingHom) (pinnedX .E6 K (highRoot .E6) 1) *
        (exactQ .E6 K ε)⁻¹ * (rootDiagUnit .E6 a)⁻¹ = pinnedX .E6 K (highRoot .E6) 1
  rw [show rootDiagUnit .E6 a * exactQ .E6 K ε *
      Units.map (entrywiseHom σ.toRingHom) (pinnedX .E6 K (highRoot .E6) 1) *
        (exactQ .E6 K ε)⁻¹ * (rootDiagUnit .E6 a)⁻¹ = rootDiagUnit .E6 a *
      (exactQ .E6 K ε * Units.map (entrywiseHom σ.toRingHom) (pinnedX .E6 K (highRoot .E6) 1)
        * (exactQ .E6 K ε)⁻¹) * (rootDiagUnit .E6 a)⁻¹ from by group,
    hσ, hQ, rootDiagUnit_conj_pinnedX a (isRoot_highRoot .E6) 1, hθ, Units.val_one, one_mul]

end StepFour

section StepFive

variable {K : Type} [Field K] [CharP K 2]


private theorem exactNormalAutGL_pinnedX {a : Fin Tag.E6.rank → Kˣ} {σ : K ≃+* K}
    {ε : Fin (exactE .E6)} {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) (c : K) :
    exactNormalAutGL .E6 K a σ ε (pinnedX .E6 K γ c) =
      pinnedX .E6 K (permLattice (exactPerm .E6 ε) γ)
        (((rootChar a (permLattice (exactPerm .E6 ε) γ) : K)) * σ c) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hσ : Units.map (entrywiseHom σ.toRingHom) (pinnedX .E6 K γ c) =
      pinnedX .E6 K γ (σ c) :=
    CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX σ.toRingHom γ c
  have hperm : permLattice (exactPerm .E6 (ε : ℕ)) γ =
      permLattice (TwistTag.E6.perm ^ (ε : ℕ)) γ := rfl
  rw [exactNormalAutGL_apply, hσ]
  rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega) with h | h
  · have h1 : permLattice (exactPerm .E6 0) γ = γ := rfl
    rw [h, exactQ_zero, h1]
    simp only [mul_one, inv_one]
    exact rootDiagUnit_conj_pinnedX a hγ (σ c)
  · rw [show exactQ .E6 K (ε : ℕ) = exactQ .E6 K 1 by rw [h], hperm, h, pow_one]
    rw [show rootDiagUnit .E6 a * exactQ .E6 K 1 * pinnedX .E6 K γ (σ c) * (exactQ .E6 K 1)⁻¹ *
        (rootDiagUnit .E6 a)⁻¹ = rootDiagUnit .E6 a *
        (exactQ .E6 K 1 * pinnedX .E6 K γ (σ c) * (exactQ .E6 K 1)⁻¹) *
        (rootDiagUnit .E6 a)⁻¹ from by group,
      exactQ_one_conj_pinnedX h2 hγ (σ c)]
    exact rootDiagUnit_conj_pinnedX a (IsRoot.permLattice (TwistTag.cartan_perm TwistTag.E6) hγ)
      (σ c)

private theorem permLattice_exactPerm_mem_a5LeviRoots {ε : Fin (exactE .E6)}
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ a5LeviRoots) :
    permLattice (exactPerm .E6 ε) γ ∈ a5LeviRoots := by
  have hinv : (exactPerm .E6 (ε : ℕ)).symm (highNode .E6) = highNode .E6 := by
    rw [Equiv.symm_apply_eq]
    exact ((exactPerm_E6_eq_highNode_iff ε (highNode .E6)).2 rfl).symm
  rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega) with h | h
  · rw [show permLattice (exactPerm .E6 (ε : ℕ)) γ = γ by rw [h]; rfl]
    exact hγ
  · refine ⟨?_, ?_⟩
    · rw [show permLattice (exactPerm .E6 (ε : ℕ)) γ =
          permLattice TwistTag.E6.perm γ by rw [h]; rfl]
      exact IsRoot.permLattice (TwistTag.cartan_perm TwistTag.E6) hγ.1
    · show γ ((exactPerm .E6 (ε : ℕ)).symm (highNode .E6)) = 0
      rw [hinv]
      exact hγ.2

theorem exactNormalAut_mapsTo_a5Levi {a : Fin Tag.E6.rank → Kˣ} {σ : K ≃+* K}
    {ε : Fin (exactE .E6)} :
    ∀ k ∈ a5Levi K, exactNormalAut .E6 K a σ ε k ∈ a5Levi K := by
  have hmap : Subgroup.map (exactNormalAutGL .E6 K a σ ε).toMonoidHom
      (rootSpan .E6 K a5LeviRoots) ≤ rootSpan .E6 K a5LeviRoots := by
    rw [rootSpan_a5LeviRoots_eq_closure, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, ⟨i, j, hij, c, hc⟩, rfl⟩
    rw [← hc, ← rootSpan_a5LeviRoots_eq_closure]
    change exactNormalAutGL .E6 K a σ ε (pinnedX .E6 K (a5Root i j) c) ∈
      rootSpan .E6 K a5LeviRoots
    rw [exactNormalAutGL_pinnedX (isRoot_a5Root hij) c]
    exact pinnedX_mem_rootSpan_a5LeviRoots
      (permLattice_exactPerm_mem_a5LeviRoots (a5Root_mem_a5LeviRoots hij)) _
  intro k hk
  rw [mem_a5Levi_iff] at hk ⊢
  have h := hmap (Subgroup.mem_map_of_mem (exactNormalAutGL .E6 K a σ ε).toMonoidHom hk)
  rw [coe_exactNormalAut]
  exact h

end StepFive

section NormalForm

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_mulAut_conj_exactNormalAut_rootChar_one {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup .E6 K)) :
    ∃ (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K)
      (ε : Fin (exactE .E6)),
      rootChar a (highRoot .E6) = 1 ∧ α = MulAut.conj g * exactNormalAut .E6 K a σ ε := by
  classical
  letI := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hxK : ∀ x : Kˣ, x ^ 2 ^ f = x := by
    intro x
    refine Units.ext ?_
    rw [← hK']
    exact FiniteField.pow_card (x : K)
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  have hα : α = MulAut.conj g * exactNormalAut .E6 K a σ ε := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [hga k, MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [coe_exactNormalAut]
    simp only [mul_assoc]
  obtain ⟨l, hl⟩ : ∃ l : Kˣ, l ^ 2 = (rootChar a (highRoot .E6))⁻¹ := by
    refine ⟨(rootChar a (highRoot .E6))⁻¹ ^ 2 ^ (f - 1), ?_⟩
    rw [← pow_mul, show 2 ^ (f - 1) * 2 = 2 ^ f by rw [← pow_succ, Nat.sub_add_cancel hf],
      hxK]
  set t : adjointGroup .E6 K := ⟨rootDiagUnit .E6 (EPilot.highDiag .E6 l),
    EPilot.highRootSL2_le_adjointGroup
      (EPilot.rootDiagUnit_highDiag_mem_highRootSL2 (Or.inl rfl) l)⟩ with ht
  have hθ : rootChar (a * EPilot.highDiag .E6 l) (highRoot .E6) = 1 := by
    rw [rootChar_mul_tuple, EPilot.rootChar_highDiag, EPilot.highRoot_highNode (Or.inl rfl)]
    rw [zpow_ofNat, hl, mul_inv_cancel]
  have hNt : exactNormalAut .E6 K (a * EPilot.highDiag .E6 l) σ ε =
      MulAut.conj t * exactNormalAut .E6 K a σ ε := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, ht]
    rw [coe_exactNormalAut, coe_exactNormalAut, rootDiagUnit_mul]
    have hcomm : rootDiagUnit .E6 a * rootDiagUnit .E6 (EPilot.highDiag .E6 l) =
        rootDiagUnit .E6 (EPilot.highDiag .E6 l) * rootDiagUnit .E6 a := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    rw [hcomm]
    group
  refine ⟨g * t⁻¹, a * EPilot.highDiag .E6 l, σ, ε, hθ, ?_⟩
  have hNinv : exactNormalAut .E6 K a σ ε =
      MulAut.conj t⁻¹ * exactNormalAut .E6 K (a * EPilot.highDiag .E6 l) σ ε := by
    rw [hNt, ← mul_assoc, map_inv, inv_mul_cancel, one_mul]
  rw [hα, hNinv, ← mul_assoc, ← map_mul]

end NormalForm

section LeviStep

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_eq_conj_of_mem_a5Levi_fixed {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {a : Fin Tag.E6.rank → Kˣ} {σ : K ≃+* K} {ε : Fin (exactE .E6)}
    {h : adjointGroup .E6 K} (hh : h ∈ a5Levi K)
    (hkey : ∀ k ∈ a5Levi K, h * exactNormalAut .E6 K a σ ε k * h⁻¹ = k) :
    ∃ g : adjointGroup .E6 K, exactNormalAut .E6 K a σ ε = MulAut.conj g := by
  have hβD : ∀ k ∈ a5Levi K,
      (MulAut.conj h * exactNormalAut .E6 K a σ ε) k = k := by
    intro k hk
    rw [MulAut.mul_apply, MulAut.conj_apply]
    exact hkey k hk
  rcases (show Nat.card K = 2 ∨ 4 ≤ Nat.card K by
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · left
      rw [hK, pow_one]
    · right
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2) with h2 | h4
  ·
    have hunit : ∀ u : Kˣ, u = 1 := by
      have hc : Nat.card Kˣ = 1 := by rw [Nat.card_units, h2]
      have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 hc).1
      exact fun u => Subsingleton.elim u 1
    have hK01 : ∀ c : K, c = 0 ∨ c = 1 := by
      intro c
      by_cases hc : c = 0
      · exact Or.inl hc
      · exact Or.inr (congrArg Units.val (hunit (Units.mk0 c hc)))
    have ha : a = 1 := funext fun i => hunit (a i)
    have hσ : σ = RingEquiv.refl K := RingEquiv.ext fun c => by
      rcases hK01 c with rfl | rfl
      · rw [map_zero, RingEquiv.refl_apply]
      · rw [map_one, RingEquiv.refl_apply]
    subst ha hσ
    rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by
      have := ε.isLt
      change (ε : ℕ) < 2 at this
      omega) with hε | hε
    ·
      refine ⟨1, ?_⟩
      have hN1 : exactNormalAut .E6 K 1 (RingEquiv.refl K) ε = 1 := by
        refine MulEquiv.ext fun k => Subtype.ext ?_
        rw [coe_exactNormalAut, hε, exactQ_zero, rootDiagUnit_one]
        simp only [Subgroup.coe_one, MulAut.one_apply, one_mul, inv_one]
        exact Units.ext (entrywise_id _)
      rw [hN1, map_one]
    ·
      exfalso
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      have hQ1 : ∀ k : adjointGroup .E6 K,
          (exactNormalAut .E6 K 1 (RingEquiv.refl K) ε k : ModGL .E6 K) =
            exactQ .E6 K 1 * (k : ModGL .E6 K) * (exactQ .E6 K 1)⁻¹ := by
        intro k
        rw [coe_exactNormalAut, hε, rootDiagUnit_one]
        simp only [one_mul, inv_one]
        refine Eq.trans (congrArg (fun x => exactQ .E6 K 1 * x * (exactQ .E6 K 1)⁻¹) ?_) rfl
        exact Units.ext (entrywise_id _)
      refine false_of_conj_a5Root_rev (d := (h : ModGL .E6 K)) (mem_a5Levi_iff.1 hh) fun i hi => ?_
      have hi0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
      have hkD : (⟨pinnedX .E6 K (a5Root i 0) 1, pinnedX_mem_adjointGroup _ 1⟩ :
          adjointGroup .E6 K) ∈ a5Levi K := pinnedX_a5Root_mem_a5Levi hi0 1
      have e := congrArg Subtype.val (hkey _ hkD)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at e
      have hQk : (exactNormalAut .E6 K 1 (RingEquiv.refl K) ε
          ⟨pinnedX .E6 K (a5Root i 0) 1, pinnedX_mem_adjointGroup _ 1⟩ : ModGL .E6 K) =
          pinnedX .E6 K (a5Root (Fin.rev 0) (Fin.rev i)) 1 := by
        rw [hQ1, exactQ_one_conj_pinnedX h2' (isRoot_a5Root hi0) 1, permLattice_a5Root]
      rw [hQk] at e
      simpa using e
  ·
    obtain ⟨g', hg', -⟩ := exists_eq_conj_of_fix_a5Levi h4
      (MulAut.conj h * exactNormalAut .E6 K a σ ε) hβD
    refine ⟨h⁻¹ * g', ?_⟩
    have hN : exactNormalAut .E6 K a σ ε = MulAut.conj h⁻¹ * MulAut.conj g' := by
      rw [← hg', ← mul_assoc, map_inv, inv_mul_cancel, one_mul]
    rw [hN, ← map_mul]

end LeviStep

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem pCoreOf_le_range_of_highRoot_E6 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {G : Type} [Group G] {ψ : adjointGroup .E6 K →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (EPilot.pinnedElt .E6 (highRoot .E6) 1)}) ≤ ψ.range := by
  intro a ha
  have haM : a ∈ Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (EPilot.pinnedElt .E6 (highRoot .E6) 1)} :=
    GGRootNorm.pCoreOf_le _ ha
  have ha_norm : a ∈ Subgroup.normalizer (ψ.range : Set G) := haM.1
  obtain ⟨α, hα⟩ := exists_mulAut_conj_of_mem_normalizer hψ ha_norm
  obtain ⟨g, a₀, σ, ε, hθ, hnf⟩ := exists_mulAut_conj_exactNormalAut_rootChar_one hf hK α
  have hx0 : exactNormalAut .E6 K a₀ σ ε (EPilot.pinnedElt .E6 (highRoot .E6) 1) =
      EPilot.pinnedElt .E6 (highRoot .E6) 1 :=
    exactNormalAut_pinnedElt_highRoot hθ
  have hD : ∀ k ∈ a5Levi K, exactNormalAut .E6 K a₀ σ ε k ∈ a5Levi K :=
    exactNormalAut_mapsTo_a5Levi
  obtain ⟨hCx, hLQ, hdisj, hQ⟩ := KGExc.centralizer_decomp_highRoot (K := K) (Or.inl rfl)
    (show CFSG.IsQuasisimple (EPilot.perpLevi .E6 K) from isQuasisimple_a5Levi)
    (show Subgroup.center (EPilot.perpLevi .E6 K) = ⊥ from center_a5Levi_eq_bot)
  have hconj : ∀ k : adjointGroup .E6 K,
      a * ψ k * a⁻¹ = ψ (g * (exactNormalAut .E6 K a₀ σ ε).toMonoidHom k * g⁻¹) := by
    intro k
    rw [hα k, hnf, MulAut.mul_apply, MulAut.conj_apply]
    rfl
  obtain ⟨h, hh, hkey⟩ := KGRig.exists_levi_conj_eq_of_mem_pCoreOf hψ hCx hLQ hdisj hQ ha
    hx0 hconj
  have hkey' : ∀ k ∈ a5Levi K, h * exactNormalAut .E6 K a₀ σ ε k * h⁻¹ = k := by
    intro k hk
    exact hkey k hk (hD k hk)
  obtain ⟨g'', hN''⟩ := exists_eq_conj_of_mem_a5Levi_fixed hf hK hh hkey'
  have hα' : α = MulAut.conj (g * g'') := by
    rw [hnf, hN'', ← map_mul]
  refine KGRig.mem_range_of_conj_eq hC ha_norm (g := g * g'') fun k => ?_
  rw [hα k, hα', MulAut.conj_apply]

end Main

end KGE6

end CFSG.StandardType
