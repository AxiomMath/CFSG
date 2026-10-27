module 

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootNormalizer
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcRoots
public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcCore
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Inndiag
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.E6EvenRootTorusAutFix

public section

namespace CFSG.StandardType.LieKnownR2.ExcInner

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.SeitzReduction CFSG.StandardType.RootCentExc
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)

private def l10se6i_i₀ : Fin Tag.E6.rank := (1 : Fin 6)

private def l10se6i_J : Set (Fin Tag.E6.rank) := {i | i ≠ l10se6i_i₀}

private theorem l10se6i_a_eq_highRoot_of_isRoot_maxHeight
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) (h : ht (highRoot .E6) ≤ ht γ) :
    γ = highRoot .E6 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)).1 hγ
  have hall : (List.range Tag.E6.rootCertificate.roots.length).all fun k =>
      decide (ht (highRoot .E6) ≤ ht (Tag.E6.rootCertificate.root k) →
        Tag.E6.rootCertificate.root k = highRoot .E6) := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
  exact hall k hk h

private theorem l10se6i_a_highRootData :
    HighRootData .E6 (highRoot .E6) l10se6i_i₀ :=
  RootCentExc.highRootData_E6

private def l10se6i_a_scalarGroup
    (K : Type) [Field K] (θ : Fin Tag.E6.rank → ℤ) : Subgroup (ModGL .E6 K) where
  carrier := {g | ∃ l : K, ∀ c : K, g * pinnedX .E6 K θ c * g⁻¹ = pinnedX .E6 K θ (l * c)}
  one_mem' := ⟨1, by intro c; rw [one_mul, inv_one, mul_one, one_mul]⟩
  mul_mem' := by
    rintro g h ⟨l, hl⟩ ⟨l', hl'⟩
    refine ⟨l * l', fun c => ?_⟩
    calc g * h * pinnedX .E6 K θ c * (g * h)⁻¹
        = g * (h * pinnedX .E6 K θ c * h⁻¹) * g⁻¹ := by group
      _ = g * pinnedX .E6 K θ (l' * c) * g⁻¹ := by rw [hl' c]
      _ = pinnedX .E6 K θ (l * (l' * c)) := hl (l' * c)
      _ = pinnedX .E6 K θ ((l * l') * c) := by rw [mul_assoc]
  inv_mem' := by
    rintro g ⟨l, hl⟩
    have hl0 : l ≠ 0 := by
      intro h0
      have h1 := hl 1
      rw [h0, zero_mul, pinnedX_zero, mul_inv_eq_one, mul_eq_left] at h1
      exact one_ne_zero (pinnedX_injective .E6 K θ (h1.trans (pinnedX_zero .E6 K θ).symm))
    refine ⟨l⁻¹, fun c => ?_⟩
    have h2 := hl (l⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ hl0, one_mul] at h2
    calc g⁻¹ * pinnedX .E6 K θ c * (g⁻¹)⁻¹
        = g⁻¹ * (g * pinnedX .E6 K θ (l⁻¹ * c) * g⁻¹) * g := by rw [← h2]; group
      _ = pinnedX .E6 K θ (l⁻¹ * c) := by group

private theorem l10se6i_a_rootGroup_eq_subgroupOf
    (K : Type) [Field K] :
    (adjDatum (rootOperatorFamily .E6) K).rootGroup (highRoot .E6) =
      (rootSubgroup .E6 K (highRoot .E6)).subgroupOf (adjointGroup .E6 K) := by
  have hθ : IsRoot .E6 (highRoot .E6) := (l10se6i_a_highRootData).maxHeight.1
  change rootGroup (rootOperatorFamily .E6) K (highRoot .E6) = _
  rw [rootGroup_of_isRoot (F := rootOperatorFamily .E6) hθ,
    ← RootOperatorFamily.subgroupOf_rootSubgroup_eq (F := rootOperatorFamily .E6) (K := K)
      (α := ⟨highRoot .E6, hθ⟩)]

private theorem l10se6i_a_exactNormalAutGL_pinnedX_theta
    {K : Type} [Field K] [CharP K 2]
    (a : Fin TwistTag.E6.tag.rank → Kˣ) (σ : K ≃+* K) (ε : Fin 2) (c : K) :
    exactNormalAutGL TwistTag.E6.tag K a σ (ε : ℕ)
        (pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag) c) =
      pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag)
        ((rootChar a (highRoot TwistTag.E6.tag) : K) * σ c) := by
  have hθ : IsRoot TwistTag.E6.tag (highRoot TwistTag.E6.tag) :=
    (l10se6i_a_highRootData).maxHeight.1
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [exactNormalAutGL_apply]
  have hentry : Units.map (entrywiseHom σ.toRingHom)
      (pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag) c) =
      pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag) (σ c) :=
    Units.ext (entrywise_pinnedX σ.toRingHom (highRoot TwistTag.E6.tag) c)
  rw [hentry]
  have hQ : exactQ TwistTag.E6.tag K (ε : ℕ) *
      pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag) (σ c) *
      (exactQ TwistTag.E6.tag K (ε : ℕ))⁻¹ =
      pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag) (σ c) := by
    fin_cases ε
    · rw [show ((⟨0, by decide⟩ : Fin 2) : ℕ) = 0 from rfl,
        show exactQ TwistTag.E6.tag K 0 = (diagramMap TwistTag.E6 K) ^ 0 from rfl, pow_zero]
      simp
    · rw [show ((⟨1, by decide⟩ : Fin 2) : ℕ) = 1 from rfl,
        show exactQ TwistTag.E6.tag K 1 = diagramMap TwistTag.E6 K from rfl]
      have h := DFunLike.congr_fun (conj_diagramMap_eq_twistHom (t := TwistTag.E6) (K := K))
        (pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag) (σ c))
      rw [show diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag)
            (σ c) * (diagramMap TwistTag.E6 K)⁻¹ =
          (MulEquiv.toMonoidHom (MulAut.conj (diagramMap TwistTag.E6 K)))
            (pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag) (σ c)) from rfl, h,
        twistHom_id_pinnedX h2 hθ (σ c),
        show permLattice TwistTag.E6.perm (highRoot TwistTag.E6.tag) =
          highRoot TwistTag.E6.tag from by decide]
  rw [show rootDiagUnit TwistTag.E6.tag a * exactQ TwistTag.E6.tag K (ε : ℕ) *
        pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag) (σ c) *
        (exactQ TwistTag.E6.tag K (ε : ℕ))⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ =
      rootDiagUnit TwistTag.E6.tag a *
        (exactQ TwistTag.E6.tag K (ε : ℕ) *
          pinnedX TwistTag.E6.tag K (highRoot TwistTag.E6.tag) (σ c) *
          (exactQ TwistTag.E6.tag K (ε : ℕ))⁻¹) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ from by
    group]
  rw [hQ, rootDiagUnit_conj_pinnedX a hθ (σ c)]

private theorem l10se6i_a_exactNormalAutGL_pinnedX_theta'
    {K : Type} [Field K] [CharP K 2]
    (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : Fin 2) (c : K) :
    rootDiagUnit .E6 a * exactQ .E6 K (ε : ℕ) *
        Units.map (entrywiseHom σ.toRingHom) (pinnedX .E6 K (highRoot .E6) c) *
        (exactQ .E6 K (ε : ℕ))⁻¹ * (rootDiagUnit .E6 a)⁻¹ =
      pinnedX .E6 K (highRoot .E6)
        ((rootChar a (highRoot .E6) : K) * σ c) := by
  rw [← exactNormalAutGL_apply]
  exact l10se6i_a_exactNormalAutGL_pinnedX_theta a σ ε c

private theorem l10se6i_a_exactNormalAut_mem_theta
    {K : Type} [Field K] [CharP K 2]
    (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : Fin 2)
    {x : adjointGroup .E6 K} (hx : (x : ModGL .E6 K) ∈ rootSubgroup .E6 K (highRoot .E6)) :
    (exactNormalAut .E6 K a σ (ε : ℕ) x : ModGL .E6 K) ∈
      rootSubgroup .E6 K (highRoot .E6) := by
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hx
  rw [show x = ⟨pinnedX .E6 K (highRoot .E6) c, pinnedX_mem_adjointGroup _ _⟩ from
    Subtype.ext hc.symm]
  refine mem_rootSubgroup.2 ⟨(rootChar a (highRoot .E6) : K) * σ c, ?_⟩
  rw [coe_exactNormalAut]
  exact (l10se6i_a_exactNormalAutGL_pinnedX_theta' a σ ε c).symm

private theorem l10se6i_a_mem_parabolic_of_conj_theta
    {K : Type} [Field K] [CharP K 2] {g : ModGL .E6 K}
    (hg : g ∈ adjointGroup .E6 K) {c l₀ : K} (hl₀ : l₀ ≠ 0)
    (hc : g * pinnedX .E6 K (highRoot .E6) l₀ * g⁻¹ = pinnedX .E6 K (highRoot .E6) c) :
    g ∈ parabolicSubgroup .E6 K l10se6i_J := by
  have hθ : IsMaxHeight .E6 (highRoot .E6) := (l10se6i_a_highRootData).maxHeight
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨cθ, hcθ, hform⟩ := (l10se6i_a_highRootData).form
  have hW : ∀ w : WeylGroup .E6, w • (highRoot .E6) = highRoot .E6 →
      w ∈ parabolicWeylGroup .E6 l10se6i_J := fun w hw =>
    RootCentExc.mem_parabolicWeylGroup_of_smul_eq (i₀ := l10se6i_i₀) hcθ hform hw
  let u : Kˣ := Units.mk0 l₀ hl₀
  let h : ModGL .E6 K := torusElt .E6 K l10se6i_i₀ u
  have hh_mem : h ∈ adjointGroup .E6 K := torusElt_mem_adjointGroup l10se6i_i₀ u
  have hconj : h * pinnedX .E6 K (highRoot .E6) 1 * h⁻¹ =
      pinnedX .E6 K (highRoot .E6) l₀ := by
    have hexp : ∑ j, Tag.cartan .E6 l10se6i_i₀ j * highRoot .E6 j = 1 := by
      rw [(l10se6i_a_highRootData).coPair l10se6i_i₀, if_pos rfl]
    rw [conj_pinnedX_of_mem_torusGroup (torusElt_mem_torusGroup l10se6i_i₀ u) hθ.1 1,
      torusRootChar_torusElt l10se6i_i₀ u hθ.1, hexp, zpow_one, mul_one]
    simp [u]
  have hg'h : (g * h) * pinnedX .E6 K (highRoot .E6) 1 * (g * h)⁻¹ =
      pinnedX .E6 K (highRoot .E6) c := by
    calc (g * h) * pinnedX .E6 K (highRoot .E6) 1 * (g * h)⁻¹
        = g * (h * pinnedX .E6 K (highRoot .E6) 1 * h⁻¹) * g⁻¹ := by group
      _ = g * pinnedX .E6 K (highRoot .E6) l₀ * g⁻¹ := by rw [hconj]
      _ = pinnedX .E6 K (highRoot .E6) c := hc
  have hP' : g * h ∈ parabolicSubgroup .E6 K l10se6i_J :=
    RootCentExc.mem_parabolicSubgroup_of_conj h2 hθ hW (mul_mem hg hh_mem) hg'h
  have hhP : h ∈ parabolicSubgroup .E6 K l10se6i_J :=
    (show (borelGroup .E6 K : Subgroup (ModGL .E6 K)) ≤ parabolicSubgroup .E6 K l10se6i_J from
      le_sup_left) (torusGroup_le_borelGroup (torusElt_mem_torusGroup l10se6i_i₀ u))
  have : g = (g * h) * h⁻¹ := by group
  rw [this]
  exact mul_mem hP' (inv_mem hhP)

private theorem l10se6i_a_exactNormalAutGL_mem_subsystem
    {K : Type} [Field K]
    (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : Fin 2)
    {x : ModGL .E6 K} (hx : x ∈ subsystemGroup .E6 K E6GraphLevi.setA) :
    exactNormalAutGL .E6 K a σ (ε : ℕ) x ∈ subsystemGroup .E6 K E6GraphLevi.setA := by
  have hAperm : ∀ i : Fin Tag.E6.rank, i ∈ E6GraphLevi.setA →
      exactPerm .E6 (ε : ℕ) i ∈ E6GraphLevi.setA := by
    intro i hi
    fin_cases ε
    · show i ∈ E6GraphLevi.setA
      exact hi
    · simp only [E6GraphLevi.setA, Set.mem_setOf_eq] at hi ⊢
      intro h
      have h' : TwistTag.E6.perm i = 1 := h
      exact hi (by
        have h1 : TwistTag.E6.perm.symm (1 : Fin Tag.E6.rank) = 1 := by decide
        have := (TwistTag.E6.perm).symm_apply_apply i
        rw [h'] at this
        exact this.symm.trans h1)
  have hle : (subsystemGroup .E6 K E6GraphLevi.setA).map
      (exactNormalAutGL .E6 K a σ (ε : ℕ)).toMonoidHom ≤
      subsystemGroup .E6 K E6GraphLevi.setA := by
    unfold subsystemGroup
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · rw [show (MulEquiv.toMonoidHom (exactNormalAutGL .E6 K a σ (ε : ℕ)))
            (xUnit .E6 K i c) =
          exactNormalAutGL .E6 K a σ (ε : ℕ) (xUnit .E6 K i c) from rfl,
        exactNormalAutGL_xUnit]
      exact Subgroup.subset_closure ⟨exactPerm .E6 (ε : ℕ) i, hAperm i hi,
        (a (exactPerm .E6 (ε : ℕ) i) : K) * σ c, Or.inl rfl⟩
    · rw [show (MulEquiv.toMonoidHom (exactNormalAutGL .E6 K a σ (ε : ℕ)))
            (yUnit .E6 K i c) =
          exactNormalAutGL .E6 K a σ (ε : ℕ) (yUnit .E6 K i c) from rfl,
        exactNormalAutGL_yUnit]
      exact Subgroup.subset_closure ⟨exactPerm .E6 (ε : ℕ) i, hAperm i hi,
        (((a (exactPerm .E6 (ε : ℕ) i))⁻¹ : Kˣ) : K) * σ c, Or.inr rfl⟩
  exact hle ⟨x, hx, rfl⟩

private theorem l10se6i_a_exactNormalAut_mem_subsystem
    {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : Fin 2)
    {x : adjointGroup .E6 K} (hx : (x : ModGL .E6 K) ∈ subsystemGroup .E6 K E6GraphLevi.setA) :
    (exactNormalAut .E6 K a σ (ε : ℕ) x : ModGL .E6 K) ∈
      subsystemGroup .E6 K E6GraphLevi.setA :=
  l10se6i_a_exactNormalAutGL_mem_subsystem a σ ε hx

private theorem l10se6i_a_parabolicLevi_le_normalizer_subsystem
    {K : Type} [Field K] :
    parabolicLevi .E6 K l10se6i_J ≤
      Subgroup.normalizer (subsystemGroup .E6 K E6GraphLevi.setA : Set (ModGL .E6 K)) := by
  rw [show parabolicLevi .E6 K l10se6i_J =
      torusGroup .E6 K ⊔ subsystemGroup .E6 K E6GraphLevi.setA from rfl]
  exact sup_le
    (CFSG.LieType.Chevalley.RootTorus.torusGroup_le_normalizer_subsystemGroup _)
    Subgroup.le_normalizer

private theorem l10se6i_a_parabolicLevi_le_normalizer_theta
    {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] (hk : Nat.card K = 2 ^ f) :
    parabolicLevi .E6 K l10se6i_J ≤
      Subgroup.normalizer (rootSubgroup .E6 K (highRoot .E6) : Set (ModGL .E6 K)) := by
  rw [show parabolicLevi .E6 K l10se6i_J =
      torusGroup .E6 K ⊔ subsystemGroup .E6 K E6GraphLevi.setA from rfl]
  refine sup_le (RootCentExc.torusGroup_le_normalizer_rootSubgroup
    (l10se6i_a_highRootData).maxHeight.1) ?_
  have hcent : subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≤
      Subgroup.centralizer (E6GraphLevi.thetaRankOneGroup (RingHom.id K)) :=
    Subgroup.le_centralizer_iff.2
      (CFSG.LieType.Chevalley.E6EvenRootTorus.thetaRankOneGroup_le_centralizer hf hk)
  exact hcent.trans ((Subgroup.centralizer_le
      (CFSG.LieType.Chevalley.E6EvenRootTorus.rootSubgroup_le_thetaRankOneGroup (K := K))).trans
    (Subgroup.centralizer_le_normalizer _))

private theorem l10se6i_a_triv_mod
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (y : MulAut (adjointGroup .E6 K))
    (hytriv : ∀ m ∈ Subgroup.normalizer
        (((adjDatum (rootOperatorFamily .E6) K).rootGroup (highRoot .E6) :
          Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)),
      y m * m⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer
        (((adjDatum (rootOperatorFamily .E6) K).rootGroup (highRoot .E6) :
          Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))))
    {m : adjointGroup .E6 K} (hm : (m : ModGL .E6 K) ∈ parabolicSubgroup .E6 K l10se6i_J) :
    (y m * m⁻¹ : ModGL .E6 K) ∈ parabolicRadical .E6 K l10se6i_J := by
  have hX := l10se6i_a_rootGroup_eq_subgroupOf K
  have hH : rootSubgroup .E6 K (highRoot .E6) ≤ adjointGroup .E6 K :=
    rootSubgroup_le_adjointGroup (highRoot .E6)
  have hN : Subgroup.normalizer
      (((adjDatum (rootOperatorFamily .E6) K).rootGroup (highRoot .E6) :
        Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) =
      (parabolicSubgroup .E6 K l10se6i_J).subgroupOf (adjointGroup .E6 K) := by
    have h1 : Subgroup.normalizer (rootSubgroup .E6 K (highRoot .E6) : Set (ModGL .E6 K)) ⊓
        adjointGroup .E6 K = parabolicSubgroup .E6 K l10se6i_J :=
      (even_highest_root_normalizer .E6 K).1
    rw [hX, ← Subgroup.subgroupOf_normalizer_eq hH, Subgroup.subgroupOf_inj, h1,
      inf_eq_left.2 (parabolicSubgroup_le_adjointGroup .E6 K l10se6i_J)]
  have hmN : m ∈ Subgroup.normalizer
      (((adjDatum (rootOperatorFamily .E6) K).rootGroup (highRoot .E6) :
        Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) := by
    rw [hN]
    exact Subgroup.mem_subgroupOf.2 hm
  have hpc : pCoreOf 2 (parabolicSubgroup .E6 K l10se6i_J) =
      parabolicRadical .E6 K l10se6i_J ⊓ adjointGroup .E6 K :=
    (even_highest_root_normalizer .E6 K).2
  have h1 := hytriv m hmN
  rw [hN, GGRootNorm.pCoreOf_subgroupOf
    (parabolicSubgroup_le_adjointGroup .E6 K l10se6i_J), hpc] at h1
  exact (Subgroup.mem_subgroupOf.1 h1).1

private theorem l10se6i_a_normal_form_PA
    {f : ℕ}
    (y : MulAut (adjointGroup .E6 (GaloisField 2 f)))
    (hyR : ((adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup
        (highRoot .E6)).map y.toMonoidHom =
      (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup (highRoot .E6)) :
    ∃ (g : adjointGroup .E6 (GaloisField 2 f))
      (a : Fin Tag.E6.rank → (GaloisField 2 f)ˣ)
      (σ : GaloisField 2 f ≃+* GaloisField 2 f) (ε : Fin 2),
      y = MulAut.conj g * exactNormalAut .E6 (GaloisField 2 f) a σ ε ∧
      (g : ModGL .E6 (GaloisField 2 f)) ∈
        parabolicSubgroup .E6 (GaloisField 2 f) l10se6i_J := by
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  haveI : Finite (GaloisField 2 f) := inferInstance
  obtain ⟨g, a, σ, ε, hyeq⟩ := exists_conj_mul_exactNormalAut
    (K := GaloisField 2 f)
    (Or.inl rfl : Tag.E6 = Tag.E6 ∨ Tag.E6 = Tag.E7 ∨ Tag.E6 = Tag.E8) y
  refine ⟨g, a, σ, ε, hyeq, ?_⟩
  let x1 : adjointGroup .E6 (GaloisField 2 f) :=
    ⟨pinnedX .E6 (GaloisField 2 f) (highRoot .E6) 1, pinnedX_mem_adjointGroup _ _⟩
  have hx1R : x1 ∈ (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup
      (highRoot .E6) := by
    rw [l10se6i_a_rootGroup_eq_subgroupOf (GaloisField 2 f)]
    exact Subgroup.mem_subgroupOf.2 (mem_rootSubgroup.2 ⟨1, rfl⟩)
  have hyx1R : y x1 ∈ (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup
      (highRoot .E6) := by
    rw [← hyR]; exact ⟨x1, hx1R, rfl⟩
  have hyx1' : (y x1 : ModGL .E6 (GaloisField 2 f)) ∈
      rootSubgroup .E6 (GaloisField 2 f) (highRoot .E6) := by
    rw [l10se6i_a_rootGroup_eq_subgroupOf (GaloisField 2 f)] at hyx1R
    exact Subgroup.mem_subgroupOf.1 hyx1R
  obtain ⟨μ, hμ⟩ := mem_rootSubgroup.1 hyx1'
  have hNx1 : (exactNormalAut .E6 (GaloisField 2 f) a σ (ε : ℕ) x1 :
      ModGL .E6 (GaloisField 2 f)) =
      pinnedX .E6 (GaloisField 2 f) (highRoot .E6)
        (rootChar a (highRoot .E6) : GaloisField 2 f) := by
    rw [coe_exactNormalAut]
    simpa using l10se6i_a_exactNormalAutGL_pinnedX_theta' a σ ε 1
  have hyx1_eq : (y x1 : ModGL .E6 (GaloisField 2 f)) =
      (g : ModGL .E6 (GaloisField 2 f)) *
        (exactNormalAut .E6 (GaloisField 2 f) a σ (ε : ℕ) x1 :
          ModGL .E6 (GaloisField 2 f)) *
        (g : ModGL .E6 (GaloisField 2 f))⁻¹ := by
    rw [hyeq, MulAut.mul_apply]
    rfl
  have hgl : (g : ModGL .E6 (GaloisField 2 f)) *
      pinnedX .E6 (GaloisField 2 f) (highRoot .E6)
        (rootChar a (highRoot .E6) : GaloisField 2 f) *
      (g : ModGL .E6 (GaloisField 2 f))⁻¹ =
      pinnedX .E6 (GaloisField 2 f) (highRoot .E6) μ := by
    rw [← hNx1, ← hyx1_eq, ← hμ]
  exact l10se6i_a_mem_parabolic_of_conj_theta g.2 (Units.ne_zero _) hgl

private theorem l10se6i_a_exists_levi_decomp
    {K : Type} [Field K]
    {g : adjointGroup .E6 K}
    (hgP : (g : ModGL .E6 K) ∈ parabolicSubgroup .E6 K l10se6i_J) :
    ∃ q m : adjointGroup .E6 K,
      (q : ModGL .E6 K) ∈ parabolicRadical .E6 K l10se6i_J ∧
      (m : ModGL .E6 K) ∈ parabolicLevi .E6 K l10se6i_J ∧
      g = q * m := by
  obtain ⟨⟨q, m⟩, ⟨hq, hm, hgqm⟩, -⟩ :=
    (parabolic_root_radical_Levi_factors .E6 K l10se6i_J).2.2.2.2.2.2.1 g hgP
  have hqC : q ∈ adjointGroup .E6 K :=
    posUnipotent_le_adjointGroup ((parabolicRadical_le_posUnipotent l10se6i_J) hq)
  have hmC : m ∈ adjointGroup .E6 K := parabolicLevi_le_adjointGroup .E6 K l10se6i_J hm
  refine ⟨⟨q, hqC⟩, ⟨m, hmC⟩, hq, hm, ?_⟩
  exact Subtype.ext hgqm

private theorem l10se6i_a_beta_fixes_subsystem
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {y : MulAut (adjointGroup .E6 K)} {g q m : adjointGroup .E6 K}
    {a : Fin Tag.E6.rank → Kˣ} {σ : K ≃+* K} {ε : Fin 2}
    (hyeq : y = MulAut.conj g * exactNormalAut .E6 K a σ ε)
    (hgqm : g = q * m)
    (hq : (q : ModGL .E6 K) ∈ parabolicRadical .E6 K l10se6i_J)
    (hm : (m : ModGL .E6 K) ∈ parabolicLevi .E6 K l10se6i_J)
    (hytriv : ∀ n ∈ Subgroup.normalizer
        (((adjDatum (rootOperatorFamily .E6) K).rootGroup (highRoot .E6) :
          Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)),
      y n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer
        (((adjDatum (rootOperatorFamily .E6) K).rootGroup (highRoot .E6) :
          Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)))) :
    ∀ x : adjointGroup .E6 K,
      (x : ModGL .E6 K) ∈ subsystemGroup .E6 K E6GraphLevi.setA →
      ((MulAut.conj q⁻¹ * y) x : adjointGroup .E6 K) = x := by
  have hconj : MulAut.conj (q⁻¹ * g) = MulAut.conj q⁻¹ * MulAut.conj g := by
    ext z; simp only [MulAut.mul_apply, MulAut.conj_apply]; group
  have hqg : q⁻¹ * g = m := by rw [hgqm]; group
  have hβeq : MulAut.conj q⁻¹ * y = MulAut.conj m * exactNormalAut .E6 K a σ ε := by
    rw [hyeq]
    calc MulAut.conj q⁻¹ * (MulAut.conj g * exactNormalAut .E6 K a σ ε)
        = (MulAut.conj q⁻¹ * MulAut.conj g) * exactNormalAut .E6 K a σ ε := by group
      _ = MulAut.conj (q⁻¹ * g) * exactNormalAut .E6 K a σ ε := by rw [← hconj]
      _ = MulAut.conj m * exactNormalAut .E6 K a σ ε := by rw [hqg]
  have hle : subsystemGroup .E6 K E6GraphLevi.setA ≤ parabolicLevi .E6 K l10se6i_J :=
    le_sup_right
  have hbot : subsystemGroup .E6 K E6GraphLevi.setA ⊓ parabolicRadical .E6 K l10se6i_J = ⊥ := by
    refine le_bot_iff.1 ?_
    calc subsystemGroup .E6 K E6GraphLevi.setA ⊓ parabolicRadical .E6 K l10se6i_J
        ≤ parabolicLevi .E6 K l10se6i_J ⊓ parabolicRadical .E6 K l10se6i_J :=
          inf_le_inf_right _ hle
      _ = ⊥ := by rw [inf_comm, parabolicRadical_inf_parabolicLevi]
  intro x hx
  have hxP : (x : ModGL .E6 K) ∈ parabolicSubgroup .E6 K l10se6i_J :=
    (parabolicLevi_le_parabolicSubgroup l10se6i_J) (hle hx)
  have hβx : ((MulAut.conj q⁻¹ * y) x : ModGL .E6 K) =
      (q : ModGL .E6 K)⁻¹ * (y x : ModGL .E6 K) * (q : ModGL .E6 K) := by
    rw [MulAut.mul_apply, MulAut.conj_apply]
    rfl
  have hβx2 : ((MulAut.conj q⁻¹ * y) x : ModGL .E6 K) =
      (m : ModGL .E6 K) *
        (exactNormalAut .E6 K a σ (ε : ℕ) x : ModGL .E6 K) * (m : ModGL .E6 K)⁻¹ := by
    rw [hβeq, MulAut.mul_apply]
    rfl
  have hNxs : (exactNormalAut .E6 K a σ (ε : ℕ) x : ModGL .E6 K) ∈
      subsystemGroup .E6 K E6GraphLevi.setA :=
    l10se6i_a_exactNormalAut_mem_subsystem a σ ε hx
  have hβs : ((MulAut.conj q⁻¹ * y) x : ModGL .E6 K) ∈
      subsystemGroup .E6 K E6GraphLevi.setA := by
    rw [hβx2]
    exact (Subgroup.mem_normalizer_iff.1
      (l10se6i_a_parabolicLevi_le_normalizer_subsystem hm) _).1 hNxs
  have hy1 : (y x * x⁻¹ : ModGL .E6 K) ∈ parabolicRadical .E6 K l10se6i_J :=
    l10se6i_a_triv_mod y hytriv hxP
  have hQ : (((MulAut.conj q⁻¹ * y) x) * x⁻¹ : ModGL .E6 K) ∈
      parabolicRadical .E6 K l10se6i_J := by
    have hβmod : (((MulAut.conj q⁻¹ * y) x) * x⁻¹ : ModGL .E6 K) =
        (q : ModGL .E6 K)⁻¹ * (y x * x⁻¹ : ModGL .E6 K) *
          ((x : ModGL .E6 K) * (q : ModGL .E6 K) * (x : ModGL .E6 K)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hβx]
      group
    rw [hβmod]
    refine mul_mem (mul_mem (inv_mem hq) hy1) ?_
    exact (Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical l10se6i_J hxP) q).1 hq
  have hβs_prod : (((MulAut.conj q⁻¹ * y) x) * x⁻¹ : ModGL .E6 K) ∈
      subsystemGroup .E6 K E6GraphLevi.setA := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem hβs (inv_mem hx)
  have hzmem : ((((MulAut.conj q⁻¹ * y) x) * x⁻¹ : adjointGroup .E6 K) : ModGL .E6 K) ∈
      subsystemGroup .E6 K E6GraphLevi.setA ⊓ parabolicRadical .E6 K l10se6i_J :=
    Subgroup.mem_inf.2 ⟨hβs_prod, hQ⟩
  have hz : (((MulAut.conj q⁻¹ * y) x) * x⁻¹ : adjointGroup .E6 K) = 1 := by
    apply Subtype.ext
    rw [hbot, Subgroup.mem_bot] at hzmem
    exact hzmem
  exact mul_inv_eq_one.1 hz

private theorem l10se6i_a_exactNormalAutGL_pinnedX_fixed
    {K : Type} [Field K] [CharP K 2]
    (a : Fin TwistTag.E6.tag.rank → Kˣ) (σ : K ≃+* K) (ε : Fin 2)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (hfix : permLattice TwistTag.E6.perm γ = γ) (c : K) :
    rootDiagUnit TwistTag.E6.tag a * exactQ TwistTag.E6.tag K (ε : ℕ) *
        Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.E6.tag K γ c) *
        (exactQ TwistTag.E6.tag K (ε : ℕ))⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ =
      pinnedX TwistTag.E6.tag K γ ((rootChar a γ : K) * σ c) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hentry : Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.E6.tag K γ c) =
      pinnedX TwistTag.E6.tag K γ (σ c) := Units.ext (entrywise_pinnedX σ.toRingHom γ c)
  rw [hentry]
  have hQ : exactQ TwistTag.E6.tag K (ε : ℕ) * pinnedX TwistTag.E6.tag K γ (σ c) *
      (exactQ TwistTag.E6.tag K (ε : ℕ))⁻¹ = pinnedX TwistTag.E6.tag K γ (σ c) := by
    fin_cases ε
    · rw [show ((⟨0, by decide⟩ : Fin 2) : ℕ) = 0 from rfl,
        show exactQ TwistTag.E6.tag K 0 = (diagramMap TwistTag.E6 K) ^ 0 from rfl, pow_zero]
      simp
    · rw [show ((⟨1, by decide⟩ : Fin 2) : ℕ) = 1 from rfl,
        show exactQ TwistTag.E6.tag K 1 = diagramMap TwistTag.E6 K from rfl]
      have h := DFunLike.congr_fun (conj_diagramMap_eq_twistHom (t := TwistTag.E6) (K := K))
        (pinnedX TwistTag.E6.tag K γ (σ c))
      rw [show diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K γ (σ c) *
            (diagramMap TwistTag.E6 K)⁻¹ =
          (MulEquiv.toMonoidHom (MulAut.conj (diagramMap TwistTag.E6 K)))
            (pinnedX TwistTag.E6.tag K γ (σ c)) from rfl, h, twistHom_id_pinnedX h2 hγ (σ c),
        hfix]
  rw [show rootDiagUnit TwistTag.E6.tag a * exactQ TwistTag.E6.tag K (ε : ℕ) *
        pinnedX TwistTag.E6.tag K γ (σ c) * (exactQ TwistTag.E6.tag K (ε : ℕ))⁻¹ *
        (rootDiagUnit TwistTag.E6.tag a)⁻¹ =
      rootDiagUnit TwistTag.E6.tag a *
        (exactQ TwistTag.E6.tag K (ε : ℕ) * pinnedX TwistTag.E6.tag K γ (σ c) *
          (exactQ TwistTag.E6.tag K (ε : ℕ))⁻¹) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ from by
    group]
  rw [hQ, rootDiagUnit_conj_pinnedX a hγ (σ c)]

private theorem l10se6i_a_exactNormalAut_mem_negtheta
    {K : Type} [Field K] [CharP K 2]
    (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : Fin 2)
    {x : adjointGroup .E6 K} (hx : (x : ModGL .E6 K) ∈ rootSubgroup .E6 K (-(highRoot .E6))) :
    (exactNormalAut .E6 K a σ (ε : ℕ) x : ModGL .E6 K) ∈
      rootSubgroup .E6 K (-(highRoot .E6)) := by
  have hfix : permLattice TwistTag.E6.perm (-(highRoot TwistTag.E6.tag)) =
      -(highRoot TwistTag.E6.tag) := by
    rw [permLattice_neg,
      show permLattice TwistTag.E6.perm (highRoot TwistTag.E6.tag) = highRoot TwistTag.E6.tag
        from by decide]
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hx
  rw [show x = ⟨pinnedX .E6 K (-(highRoot .E6)) c, pinnedX_mem_adjointGroup _ _⟩ from
    Subtype.ext hc.symm]
  refine mem_rootSubgroup.2 ⟨(rootChar a (-(highRoot .E6)) : K) * σ c, ?_⟩
  rw [coe_exactNormalAut]
  exact (l10se6i_a_exactNormalAutGL_pinnedX_fixed a σ ε
    (IsRoot.neg (l10se6i_a_highRootData).maxHeight.1) hfix c).symm

private theorem l10se6i_a_parabolicLevi_le_normalizer_negtheta
    {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] (hk : Nat.card K = 2 ^ f) :
    parabolicLevi .E6 K l10se6i_J ≤
      Subgroup.normalizer (rootSubgroup .E6 K (-(highRoot .E6)) : Set (ModGL .E6 K)) := by
  have hneg : IsRoot .E6 (-(highRoot .E6)) :=
    IsRoot.neg (l10se6i_a_highRootData).maxHeight.1
  refine sup_le ?_ ?_
  · exact RootCentExc.torusGroup_le_normalizer_rootSubgroup (α := -(highRoot .E6)) hneg
  · have hcent : subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≤
        Subgroup.centralizer (E6GraphLevi.thetaRankOneGroup (RingHom.id K)) :=
      Subgroup.le_centralizer_iff.2
        (CFSG.LieType.Chevalley.E6EvenRootTorus.thetaRankOneGroup_le_centralizer hf hk)
    exact hcent.trans ((Subgroup.centralizer_le
        (CFSG.LieType.Chevalley.E6EvenRootTorus.negRootSubgroup_le_thetaRankOneGroup)).trans
      (Subgroup.centralizer_le_normalizer _))

private theorem l10se6i_a_beta_theta
    {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [CharP K 2] (hk : Nat.card K = 2 ^ f)
    {y : MulAut (adjointGroup .E6 K)} {g q m : adjointGroup .E6 K}
    {a : Fin Tag.E6.rank → Kˣ} {σ : K ≃+* K} {ε : Fin 2}
    (hyeq : y = MulAut.conj g * exactNormalAut .E6 K a σ ε) (hgqm : g = q * m)
    (hm : (m : ModGL .E6 K) ∈ parabolicLevi .E6 K l10se6i_J) :
    (∀ x : adjointGroup .E6 K,
      (x : ModGL .E6 K) ∈ rootSubgroup .E6 K (highRoot .E6) →
      ((MulAut.conj q⁻¹ * y) x : ModGL .E6 K) ∈ rootSubgroup .E6 K (highRoot .E6)) ∧
    (∀ x : adjointGroup .E6 K,
      (x : ModGL .E6 K) ∈ rootSubgroup .E6 K (-(highRoot .E6)) →
      ((MulAut.conj q⁻¹ * y) x : ModGL .E6 K) ∈ rootSubgroup .E6 K (-(highRoot .E6))) := by
  have hconj : MulAut.conj (q⁻¹ * g) = MulAut.conj q⁻¹ * MulAut.conj g := by
    ext z; simp only [MulAut.mul_apply, MulAut.conj_apply]; group
  have hqg : q⁻¹ * g = m := by rw [hgqm]; group
  have hβeq : MulAut.conj q⁻¹ * y = MulAut.conj m * exactNormalAut .E6 K a σ ε := by
    rw [hyeq]
    calc MulAut.conj q⁻¹ * (MulAut.conj g * exactNormalAut .E6 K a σ ε)
        = (MulAut.conj q⁻¹ * MulAut.conj g) * exactNormalAut .E6 K a σ ε := by group
      _ = MulAut.conj (q⁻¹ * g) * exactNormalAut .E6 K a σ ε := by rw [← hconj]
      _ = MulAut.conj m * exactNormalAut .E6 K a σ ε := by rw [hqg]
  have hβx : ∀ x : adjointGroup .E6 K,
      ((MulAut.conj q⁻¹ * y) x : ModGL .E6 K) =
        (m : ModGL .E6 K) *
          (exactNormalAut .E6 K a σ (ε : ℕ) x : ModGL .E6 K) * (m : ModGL .E6 K)⁻¹ := by
    intro x
    rw [hβeq, MulAut.mul_apply]
    rfl
  constructor
  · intro x hx
    rw [hβx x]
    exact (Subgroup.mem_normalizer_iff.1
      (l10se6i_a_parabolicLevi_le_normalizer_theta hf hk hm) _).1
      (l10se6i_a_exactNormalAut_mem_theta a σ ε hx)
  · intro x hx
    rw [hβx x]
    exact (Subgroup.mem_normalizer_iff.1
      (l10se6i_a_parabolicLevi_le_normalizer_negtheta hf hk hm) _).1
      (l10se6i_a_exactNormalAut_mem_negtheta a σ ε hx)

private theorem l10se6i_inner_maxHeight
    {f : ℕ} (hf : 1 ≤ f)
    {γ₀ : Fin (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rank → ℤ}
    (hγ₀ : γ₀ ∈ (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).roots)
    (hmax : ∀ δ ∈ (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).roots,
      ∑ i, δ i ≤ ∑ i, γ₀ i) :
    GGRootNormInner ((adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup γ₀) := by
  intro y hy2 hyR hytriv
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  haveI : Finite (GaloisField 2 f) := inferInstance
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hγ : IsRoot .E6 γ₀ := mem_adjDatum_roots.1 hγ₀
  have hθmem : highRoot .E6 ∈ (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).roots :=
    mem_adjDatum_roots.2 (l10se6i_a_highRootData).maxHeight.1
  have hsum : ht (highRoot .E6) ≤ ht γ₀ := by
    simpa only [ht] using hmax (highRoot .E6) hθmem
  have hγ₀eq : γ₀ = highRoot .E6 := l10se6i_a_eq_highRoot_of_isRoot_maxHeight hγ hsum
  subst hγ₀eq
  obtain ⟨g, a, σ, ε, hyeq, hgP⟩ := l10se6i_a_normal_form_PA y hyR
  obtain ⟨q, m, hq, hm, hgqm⟩ := l10se6i_a_exists_levi_decomp hgP
  have hL := l10se6i_a_beta_fixes_subsystem hyeq hgqm hq hm hytriv
  obtain ⟨hU, hV⟩ := l10se6i_a_beta_theta hf hcard hyeq hgqm hm
  obtain ⟨c, hc⟩ := CFSG.LieType.Chevalley.E6EvenRootTorus.exists_eq_conj_thetaTorusHom
    hf hcard (MulAut.conj q⁻¹ * y) hL hU hV
  let hC : adjointGroup .E6 (GaloisField 2 f) :=
    ⟨E6GraphLevi.thetaTorusHom (GaloisField 2 f) c,
      CFSG.LieType.Chevalley.E6EvenRootTorus.thetaTorusHom_mem_adjointGroup
        (CharP.cast_eq_zero (GaloisField 2 f) 2) c⟩
  have hβ : MulAut.conj q⁻¹ * y = MulAut.conj hC := MulEquiv.ext fun x => Subtype.ext (hc x)
  have hqq : MulAut.conj q * MulAut.conj q⁻¹ = 1 := by
    ext x; simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply]; group
  have h1 : y = MulAut.conj q * (MulAut.conj q⁻¹ * y) := by
    rw [← mul_assoc, hqq, one_mul]
  refine ⟨q * hC, ?_⟩
  rw [h1, hβ]
  refine MulEquiv.ext fun x => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  group

private theorem l10se6i_inner_root
    {f : ℕ} (hf : 1 ≤ f)
    {β : Fin (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rank → ℤ}
    (hβ : β ∈ (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).roots) :
    GGRootNormInner ((adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup β) := by
  have hsym : ∀ i j, (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).cartan i j =
      (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).cartan j i := cartanE_symm 6
  have hirr : CFSG.ClassicalInvolution.ModelFacts.IsIrreducible
      (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).cartan :=
    CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E6
  obtain ⟨w, γ₀, hγ₀mem, hγ₀max, hβeq⟩ :=
    ggLongRoot_of_symmetric hirr hsym rfl hβ
  have hI0 := l10se6i_inner_maxHeight hf hγ₀mem hγ₀max
  have hct := adjDatum_isCTGroupDatum (rootOperatorFamily .E6) (GaloisField 2 f)
  set m : adjointGroup .E6 (GaloisField 2 f) :=
    CFSG.LieType.Steinberg.nrep hct w with hm
  have ham : CFSG.LieType.Steinberg.ActsAs
      (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)) m w := by
    rw [hm]
    exact CFSG.LieType.Steinberg.actsAs_nrep hct w
  have hβmap : (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup β =
      ((adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup γ₀).map
        (MulAut.conj m).toMonoidHom := by
    rw [hβeq, ← ham γ₀ hγ₀mem]
  have hI := ggRootNormInner_map_mulEquiv (MulAut.conj m) hI0
  rwa [← hβmap] at hI

theorem ggRootNormInner_adj_E6
    {f : ℕ} (hf : 1 ≤ f)
    {β : Fin (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rank → ℤ}
    (hβ : β ∈ (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).roots) :
    GGRootNormInner ((adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup β) :=
  l10se6i_inner_root hf hβ

end CFSG.StandardType.LieKnownR2.ExcInner
