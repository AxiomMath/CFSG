module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsLangCube
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillsRoot
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.RankThree.PartOne.KF4.EvenDescent

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TwE6Transport

namespace TwE6RootKill

section Count


theorem exists_killed_index_le {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (D : TwLangData K σ q A) {p : ℕ} [NeZero p]
    (hA : ∀ x ∈ A, x ^ p = 1) (α : Fin TwistTag.E6.tag.rank → ℤ) :
    ∃ A' : Subgroup (ModGL TwistTag.E6.tag K), A' ≤ A ∧ Nat.card A ≤ p * Nat.card A' ∧
      ∀ x ∈ A, x ∈ A' ↔ ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1 := by
  classical
  set L := AlgebraicClosure K
  have hT : ∀ x : A, diagG D.g0 D.c x.1 ∈ (rootDiagUnitHom Tag.E6 L).range := by
    intro x
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 (D.hc x.1 x.2)
    obtain ⟨a, ha⟩ := ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup (Subgroup.mem_inf.1 hs).1
    have hsx' : D.g0 * s * D.g0⁻¹ = baseChangeGL (algebraMap K L) (D.c * x.1 * D.c⁻¹) := hsx
    have h1 : s = D.g0⁻¹ * baseChangeGL (algebraMap K L) (D.c * x.1 * D.c⁻¹) * D.g0 := by
      rw [← hsx']
      group
    exact ⟨a, ha.trans (h1.trans (diagG_apply D.g0 D.c x.1).symm)⟩
  let f : A →* (rootDiagUnitHom Tag.E6 L).range :=
    ((diagG D.g0 D.c).comp A.subtype).codRestrict _ hT
  let e := MonoidHom.ofInjective (f := rootDiagUnitHom Tag.E6 L)
    CFSG.LieType.Chevalley.rootDiagUnit_injective
  let ψ : A →* Lˣ := (ExcHighThree.rootCharHom (τ := Tag.E6) (L := L) α).comp
    (e.symm.toMonoidHom.comp f)
  have ht : ∀ x : A, rootDiagUnit Tag.E6 (e.symm (f x)) = diagG D.g0 D.c x.1 := fun x =>
    congrArg Subtype.val (e.apply_symm_apply (f x))
  have hψ : ∀ x : A, ψ x = rootChar (e.symm (f x)) α := fun _ => rfl
  have hrange : ψ.range ≤ rootsOfUnity p L := by
    rintro _ ⟨x, rfl⟩
    have hx : x ^ p = 1 := Subtype.ext (hA x.1 x.2)
    rw [mem_rootsOfUnity, ← map_pow, hx, map_one]
  have hcard : Nat.card ψ.range ≤ p :=
    (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity L p)
  refine ⟨ψ.ker.map A.subtype, Subgroup.map_subtype_le _, ?_, fun x hx => ⟨?_, ?_⟩⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective, ← Subgroup.card_mul_index ψ.ker,
      Subgroup.index_ker]
    exact (Nat.mul_le_mul_left _ hcard).trans (mul_comm _ _).le
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e.symm (f y), (ht y).trans (diagG_apply _ _ _), MonoidHom.mem_ker.1 hy⟩
  · rintro ⟨a, ha, haα⟩
    refine ⟨⟨x, hx⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    have h : e.symm (f ⟨x, hx⟩) = a :=
      CFSG.LieType.Chevalley.rootDiagUnit_injective
        ((ht ⟨x, hx⟩).trans ((diagG_apply _ _ _).trans ha.symm))
    rw [hψ, h]
    exact haα

end Count

end TwE6RootKill

section Main


theorem ggTwE6ThreeRootKernelInput_of_rootKill (hRK : TwE6RootKill.RootKill) :
    GGTwE6ThreeRootKernelInput := by
  rintro K _ _ n hn hK h3 X Y hX hXI hXc hYX hYc ⟨V, hV1, hV2, hVY⟩
  obtain ⟨σ, hσ, ε, hρ⟩ := exists_recipeConj hn hK
  have hXr : X ≤ (recipeConj σ ε).range := fun φ hφ => (hρ φ).2 (hXI hφ)
  have hYr : Y ≤ (recipeConj σ ε).range := hYX.trans hXr
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h2 : ringChar K = 2 := ringChar.eq K 2
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure K) 2 n c = c ^ 2 ^ n :=
    fun c => iterateFrobenius_def 2 n c
  have hSc : Nat.card (X.comap (MulAut.congr ε).toMonoidHom) = 3 ^ 6 :=
    (Nat.card_congr ((MulAut.congr ε).toEquiv.subtypeEquiv fun _ => Iff.rfl)).trans hXc
  obtain ⟨g, hg, hgn, hSg⟩ := TwE6DD2.exists_eq_langCube hn hK σ hσ h3 _ hFr
    (hX.comap (f := (MulAut.congr ε).toMonoidHom) (MulAut.congr ε).injective)
    (comap_congr_le_range σ ε hXr) hSc
  let D : TwLangData K σ (2 ^ n) (recipeMat σ ε X) :=
    TwE6RootAs.langCubeData hn hK σ hσ _ hFr h3 hg hgn hSg.le
  have hAYX : recipeMat σ ε Y ≤ recipeMat σ ε X := recipeMat_mono σ ε hYX
  have hAYc : Nat.card (recipeMat σ ε Y) = 3 ^ 4 := (card_recipeMat σ ε hn hK hσ hYr).trans hYc
  obtain ⟨α, hα, hkill⟩ := hRK K σ (2 ^ n) hK hσ h2 3 Nat.prime_three h3 (recipeMat σ ε Y)
    (recipeMat_le σ ε Y) (isElemAbelian_recipeMat σ ε hn hK hσ (hX.mono hYX))
    (by rw [hAYc]; norm_num) (twNormTwo_recipeMat σ ε hV1 hV2 hVY) (D.restrict hAYX)
  obtain ⟨A', hA'X, hA'c, hA'⟩ :=
    TwE6RootKill.exists_killed_index_le D (isElemAbelian_recipeMat σ ε hn hK hσ hX).2 α
  have hYA' : recipeMat σ ε Y ≤ A' := fun x hx => (hA' x (hAYX hx)).2 (hkill x hx)
  obtain ⟨u, hu, hu1, ⟨m, hum⟩, hcomm⟩ := ExcHighThree.twE6KillRoot_proof K σ (2 ^ n)
    (by rw [h2]; decide) hσ hK A' (D.restrict hA'X) α hα fun x hx => (hA' x (hA'X hx)).1 hx
  have hum' : ε ⟨u, hu⟩ ^ 2 ^ m = 1 := by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
    rw [h2] at hum
    exact Subtype.ext hum
  have hfix : ∀ φ ∈ matRecipe σ ε A', φ (ε ⟨u, hu⟩) = ε ⟨u, hu⟩ := fun φ hφ =>
    apply_eq_of_forall_commute σ ε hu hcomm hφ
  refine ⟨matRecipe σ ε A', lt_of_le_of_ne (le_matRecipe σ ε hYr hYA') fun hYY' => ?_,
    matRecipe_le σ ε hA'X, Subgroup.zpowers (ε ⟨u, hu⟩), ?_, ?_, ?_⟩
  · have hc := hA'c
    rw [(card_recipeMat σ ε hn hK hσ hXr).trans hXc,
      ← card_matRecipe σ ε hn hK hσ (hA'X.trans (recipeMat_le_twInndiagGroup σ ε X)), ← hYY',
      hYc] at hc
    norm_num at hc
  · exact Subgroup.zpowers_ne_bot.2 fun h => hu1 (congrArg Subtype.val (ε.map_eq_one_iff.1 h))
  · intro w
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 w.2
    refine ⟨m, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hum', one_zpow]
  · intro φ hφ v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [map_zpow, hfix φ hφ]⟩

end Main

end CFSG.StandardType

end
