module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherTwE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6Three
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GTwE6Fix
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6FTw
import CFSG.Adapters.GeneralizedFitting
import CFSG.Goldschmidt.Steps.G37Transport
import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04F
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Background.F2Equiv
import CFSG.Quasithin.Background.G2Relaxed
import CFSG.Quasithin.EmptyFaithful.S14117
import CFSG.Quasithin.EmptyFaithful.S14117Coprime
import CFSG.Quasithin.EmptyFaithful.S14117Rank
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
import CFSG.RankThree.PartOne.S11d.OddOutPSL2
import CFSG.RankThree.PartOne.S11d.OutEsix
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.RecipeExcLang CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley

namespace KG87B

open CFSG.LocalAnalysis.GLTheoremA in
private theorem inner_of_inndiag_comm_fieldActor
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h3 : 3 ∣ ℓ ^ f + 1) {η : K ≃+* K} (hη : orderOf η = 3)
    {δ : MulAut (twistedE6RootGroup K σ)} (hδ : δ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hcomm : δ * fieldActor σ η = fieldActor σ η * δ) : δ ∈ twistedE6Inn K σ := by
  classical
  have hσ2 : σ ^ 2 = 1 := by
    obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 hℓ hf K hK
    have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
    rw [hσσ'] at hord
    rw [← pow_orderOf_eq_one σ, hord]
    rfl
  have hσσ : ∀ c, σ (σ c) = c :=
    CFSG.SeitzReduction.TwistedE6Pilot.sigma_apply_apply_of_sq_eq_one_twistedE6 hσ2
  have h3K : 3 ∣ Nat.card K - 1 := by
    have hq : ℓ ^ f % 3 = 2 := by omega
    have h1 : (ℓ ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
    rw [hK]
    omega
  have hT' := YS04E6F.exists_cube_of_fixed η hη h3K
  obtain ⟨g, u, hδ'⟩ := (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_twJ_iff σ).1 hδ
  rw [hδ'] at hcomm
  have hmat := YS04E6F.eq_of_comm_tw σ η hcomm
  have hdC := YS04E6F.rootDiagUnit_mem_adjointGroup_of_twist η (YS04E6F.hcube_E6 η hT')
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedE6RootGroup_le σ g.2) _ hmat
  rw [hδ']
  exact YS04E6F.mem_inner_of_diag_mem σ hσσ g u hdC

private theorem mem_range_conj_model
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {f : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hf : f ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hord : orderOf f = 3)
    {φ : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hφI : φ ∈ markIDImage (IsRoot TwistTag.E6.tag) K
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hφf : φ * f = f * φ) :
    φ ∈ (MulAut.conj : LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
      MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))).range := by
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  set Ψ := MulAut.congr (centerQuotEquivOfBot hZ) with hΨ
  obtain ⟨-, -, -, -, -, -, -, hNF, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hΘf : ∀ δ : RingAut K, Θ (fieldActor σ δ) = δ := fun δ =>
    hΘ _ 1 1 δ (by rw [map_one, map_one, one_mul, one_mul])
  have hinj : Function.Injective (fieldActorHom (t := TwistTag.E6) σ) := fun δ δ' h => by
    rw [← hΘf δ, ← hΘf δ']
    exact congrArg Θ h
  obtain ⟨η, hη⟩ := hf
  have hfΨ : Ψ f = fieldActor σ η := by
    refine MulEquiv.ext fun h => ?_
    have h1 := congr_centerQuotEquivOfBot_mk hZ f h
    have h2 := hη h (fieldActor σ η h) (by beta_reduce; rw [coe_fieldActor]; rfl)
    exact congrArg (centerQuotEquivOfBot hZ) (h1.symm.trans h2)
  have hηo : orderOf η = 3 := by
    rw [← orderOf_injective _ hinj η, fieldActorHom_apply, ← hfΨ, MulEquiv.orderOf_eq, hord]
  have hΦΘ := CFSG.LocalAnalysis.GLTheoremA.T156.twE6_theta_eq_one_of_mem_markID σ Θ hΘ hφI
  obtain ⟨g, u, δ, hΦ⟩ := hNF (Ψ φ)
  have hδ : δ = 1 := by
    rw [← hΘ _ g u δ hΦ]
    exact hΦΘ
  have hmem : Ψ φ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rw [hΦ, hδ, fieldActor_one, mul_one]
    exact mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right ⟨u, rfl⟩)
  have hcomm : Ψ φ * fieldActor σ η = fieldActor σ η * Ψ φ := by
    rw [← hfΨ, ← map_mul, ← map_mul, hφf]
  have hinn : Ψ φ ∈ twistedE6Inn K σ := by
    by_cases h3 : 3 ∣ 2 ^ n + 1
    · exact inner_of_inndiag_comm_fieldActor Nat.prime_two hn hK σ hσ h3 hηo hmem hcomm
    · have h0 : ¬ 3 ∣ 2 ^ n := fun h => by
        have := Nat.le_of_dvd (by norm_num) (Nat.prime_three.dvd_of_dvd_pow h)
        omega
      rw [← CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6Inndiag_eq_inn_of_mod_three K
        (by rw [hK, ← pow_mul, mul_comm]) σ hσ (by omega)]
      exact hmem
  obtain ⟨c, hc⟩ := hinn
  refine ⟨(centerQuotEquivOfBot hZ).symm c, Ψ.injective ?_⟩
  calc Ψ (MulAut.conj ((centerQuotEquivOfBot hZ).symm c)) = MulAut.conj c := by
        rw [hΨ, CFSG.mulAut_congr_conj, MulEquiv.apply_symm_apply]
    _ = Ψ φ := hc

private theorem mem_range_conj_on
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop} (hS : S = IsRoot TwistTag.E6.tag)
    {H : Subgroup (MarkChev.GLS S K)}
    (hH : H = MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n)
    {f : MulAut (LargeEvenCenterQuot H)} (hf : f ∈ RecipeFieldExcInn.markFieldImage S K H)
    (hord : orderOf f = 3) {φ : MulAut (LargeEvenCenterQuot H)} (hφ : φ ∈ markIDImage S K H)
    (hc : φ * f = f * φ) :
    φ ∈ (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range := by
  subst hS
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  set σ : K ≃+* K := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hH' : H = graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    hH.trans ((twistedH_eq_commutator K TwistTag.E6 n σ.toRingHom hσ).trans
      (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ).2.2.1)
  subst hH'
  exact mem_range_conj_model hn hK σ hσ hf hord hφ hc

private theorem mem_range_conj_recipe
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    {f : MulAut (TwE6Delta.RecipeR K n)}
    (hf : f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n))
    (hord : orderOf f = 3) {φ : MulAut (TwE6Delta.RecipeR K n)} (hφ : φ ∈ TwE6Delta.RecipeI K n)
    (hc : φ * f = f * φ) :
    φ ∈ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range := by
  have hφ' : φ ∈ markIDImage (LargeEvenIsRoot (LargeEvenCartanE 6)) K (TwE6Delta.RecipeH K n) := by
    rw [← largeEvenChevIDImage_eq]
    exact hφ
  exact mem_range_conj_on hn hK (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag)
    (largeEvenTwistedH_eq _ K _ n) hf hord hφ' hc

theorem mem_range_conj_of_commute_field
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (hs : IsSimpleGroup (TwE6Delta.RecipeR K n))
    (hna : ∃ a b : TwE6Delta.RecipeR K n, a * b ≠ b * a)
    (hconj : GGRawFieldConj 3 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)))
    {x : MulAut (TwE6Delta.RecipeR K n)}
    (hx : x ∈ Subgroup.closure (TwE6Delta.RecipeI K n ∪
      LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)))
    (hxI : x ∉ TwE6Delta.RecipeI K n) (hx3 : x ^ 3 = 1)
    {φ : MulAut (TwE6Delta.RecipeR K n)} (hφ : φ ∈ TwE6Delta.RecipeI K n) (hcomm : φ * x = x * φ) :
    φ ∈ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range := by
  obtain ⟨D, hD⟩ : ∃ D : Subgroup (MulAut (TwE6Delta.RecipeR K n)),
      TwE6Delta.RecipeI K n = D := ⟨_, rfl⟩
  have hN : GGInndiagNormal (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
    InndiagE6.ggInndiagNormal_twE6 hn K hK
  have hle : ggInndiag (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) ≤ D := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      have hy : MulAut.conj y ∈ TwE6Delta.RecipeI K n :=
        Subgroup.subset_closure (Or.inl ⟨y, rfl⟩)
      rw [hD] at hy
      exact hy
    · rw [Subgroup.closure_le, hD]
  have : D.Normal := ⟨fun ψ hψ α => hle (hN α ψ (by rw [hD]; exact hψ))⟩
  have hcl : Subgroup.closure (TwE6Delta.RecipeI K n ∪
      LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)) ≤
      D ⊔ Subgroup.closure
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)) := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · rw [hD] at hy
      exact Subgroup.mem_sup_left hy
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure hy)
  obtain ⟨u, hu, f, hf, rfl⟩ : ∃ u ∈ D, ∃ f ∈ Subgroup.closure
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)), u * f = x := by
    have h := hcl hx
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at h
    exact Set.mem_mul.mp h
  have huI : u ∈ TwE6Delta.RecipeI K n := by
    rw [hD]
    exact hu
  obtain ⟨f', hf'F, u', hu'I, hf'o, e⟩ := hconj hs hna u huI f hf hxI hx3
  rw [e] at hcomm
  rw [hD] at hu'I hφ
  have hφ'I : u'⁻¹ * φ * u' ∈ TwE6Delta.RecipeI K n := by
    rw [hD]
    exact mul_mem (mul_mem (inv_mem hu'I) hφ) hu'I
  have hc' : (u'⁻¹ * φ * u') * f' = f' * (u'⁻¹ * φ * u') := by
    calc (u'⁻¹ * φ * u') * f' = u'⁻¹ * (φ * (u' * f' * u'⁻¹)) * u' := by group
      _ = u'⁻¹ * (u' * f' * u'⁻¹ * φ) * u' := by rw [hcomm]
      _ = f' * (u'⁻¹ * φ * u') := by group
  obtain ⟨g, hg⟩ := mem_range_conj_recipe hn hK hf'F hf'o hφ'I hc'
  refine ⟨u' g, ?_⟩
  have key : MulAut.conj (u' g) = u' * MulAut.conj g * u'⁻¹ := by
    ext h
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  rw [key, hg]
  group

end KG87B

end CFSG.StandardType
