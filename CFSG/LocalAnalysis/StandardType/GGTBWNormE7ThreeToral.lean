module

public import CFSG.LocalAnalysis.StandardType.GGExcToralInnerAction
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE7Split
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParity

public noncomputable section

namespace CFSG.StandardType.E7ThreeToral

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley



theorem ggWNormConcl_of_original_cover_toral
    {R L K : Type} [Group R] [Group L] [Finite L] [Field K] [Finite K] [CharP K 2]
    [Fact (Nat.Prime 3)]
    (ψ : L →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hR : Subgroup.center R = ⊥)
    (Λ : R →* MulAut L) (hΛψ : ∀ l, Λ (ψ l) = MulAut.conj l)
    (E : Subgroup R) (A : Subgroup (MulAut L)) (hEA : E.map Λ = A)
    (θ : R ≃* adjointGroup .E7 K) (hE : IsElemAbelian 3 E)
    (hT : ExcFramesHalf.IsToralSubgroup .E7 (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        ((adjointGroup .E7 K).subtype.comp θ.toMonoidHom))))
    {ιs V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : ιs → MulAut ↥A) (h : ιs → V)
    (α : ιs → Module.Dual (ZMod 3) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  let EK : Subgroup (adjointGroup .E7 K) := E.map θ.toMonoidHom
  have hEK : IsElemAbelian 3 EK := hE.map θ.toMonoidHom
  have hTK : ExcFramesHalf.IsToralSubgroup .E7 (AlgebraicClosure K)
      (EK.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup .E7 K).subtype)) := by
    rw [Subgroup.map_map]
    simpa only [MonoidHom.comp_assoc] using hT
  have hAut : ∀ β : MulAut R, ∃ r : R, ∀ x ∈ E, β x = r * x * r⁻¹ := by
    intro β
    obtain ⟨r, hr⟩ := ExcToralInner.exists_conj_eq_of_toral (Or.inl rfl) EK hEK hTK
      (MulAut.congr θ β)
    refine ⟨θ.symm r, fun x hx => θ.injective ?_⟩
    have he := hr (θ x) ⟨x, hx, rfl⟩
    simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] using he
  exact ggWNormConcl_of_centralCover_innerAction ψ hψ hker hR Λ hΛψ E A hEA hAut
    ι φ h α hgen hs


theorem ggWNormConcl_of_original_cover_card_ge
    {R L K : Type} [Group R] [Group L] [Finite L] [Field K] [Finite K] [CharP K 2]
    [Fact (Nat.Prime 3)]
    (ψ : L →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hR : Subgroup.center R = ⊥)
    (Λ : R →* MulAut L) (hΛ : Function.Injective Λ)
    (hΛψ : ∀ l, Λ (ψ l) = MulAut.conj l)
    (E : Subgroup R) (A : Subgroup (MulAut L)) (hEA : E.map Λ = A)
    (θ : R ≃* adjointGroup .E7 K) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 6 ≤ Nat.card A)
    {ιs V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : ιs → MulAut ↥A) (h : ιs → V)
    (α : ιs → Module.Dual (ZMod 3) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  let f : R →* ModGL .E7 (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      ((adjointGroup .E7 K).subtype.comp θ.toMonoidHom)
  let EB : Subgroup (ModGL .E7 (AlgebraicClosure K)) := E.map f
  have hfi : Function.Injective f :=
    (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp
      (Subtype.val_injective.comp θ.injective)
  have hEB : IsElemAbelian 3 EB := hE.map f
  have hEBG : EB ≤ adjointGroup .E7 (AlgebraicClosure K) := by
    rintro x ⟨r, hr, rfl⟩
    exact baseChangeGL_mem_adjointGroup _ (θ r).2
  have hEBcard : 3 ^ 6 ≤ Nat.card EB := calc
    3 ^ 6 ≤ Nat.card A := hcard
    _ = Nat.card E := by
      rw [← hEA]
      exact Subgroup.card_map_of_injective hΛ
    _ = Nat.card EB := (Subgroup.card_map_of_injective hfi).symm
  have hEBcomm : ∀ x ∈ EB, ∀ y ∈ EB, x * y = y * x := by
    let := hEB.1
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : EB) ⟨y, hy⟩)
  have hpK : ¬ 3 ∣ Nat.card K := by
    let : Fintype K := Fintype.ofFinite K
    obtain ⟨e, -, he⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, he]
    intro hdiv
    exact (by norm_num : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hdiv)
  have hT : ExcFramesHalf.IsToralSubgroup .E7 (AlgebraicClosure K) EB :=
    ExcFramesHalf.bigElemAbelianToralBar_E7_three K hpK EB hEBG hEBcomm hEB.2 hEBcard
  exact ggWNormConcl_of_original_cover_toral ψ hψ hker hR Λ hΛψ E A hEA θ hE hT
    ι φ h α hgen hs


theorem ggWNormConcl_of_recipe_torusTBGroup
    {K : Type} [Field K] [Finite K] [CharP K 2] {n r : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hr : 6 ≤ r)
    {L : Type} [Group L] [Finite L] [Fact (Nat.Prime 3)]
    (ψ : L →* TableBExc.RecipeGroup .E7 K) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup 3 r (TableBExc.RecipeGroup .E7 K)
      (TableBExc.RecipeID .E7 K) L ψ A)
    {ιs V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : ιs → MulAut ↥A) (h : ιs → V)
    (α : ιs → Module.Dual (ZMod 3) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  rcases hTB with ⟨hψ, hker, hperf, hA, hAI, hcard, -, hsc⟩
  have hcard6 : 3 ^ 6 ≤ Nat.card A := (Nat.pow_le_pow_right (by norm_num) hr).trans hcard
  obtain ⟨Λ, hΛeq, hΛinj, -, hAΛ, hE, -, -⟩ :=
    TwE6TB.exists_innerModel Nat.prime_three (TableBExc.center_recipeGroup_eq_bot .E7 K)
      (fun _ hβ _ => TableBExc.idImage_subset_inn_E7 K hβ)
      (ExcSplitL.ggCenterPrime_recipe_E7 hn hK Nat.prime_three (by decide))
      ψ hψ hker hperf hA hAI hsc
  have hΛψ : ∀ l, Λ (ψ l) = MulAut.conj l := fun l => hΛeq rfl
  have hEA : (A.comap Λ).map Λ = A := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ha
      obtain ⟨x, rfl⟩ := hAΛ a ha
      exact ⟨x, ha, rfl⟩
  exact ggWNormConcl_of_original_cover_card_ge ψ hψ hker
    (TableBExc.center_recipeGroup_eq_bot .E7 K) Λ hΛinj hΛψ (A.comap Λ) A hEA
    (TableBExc.recipeEquiv .E7 K) hE hcard6 ι φ h α hgen hs

theorem ggTorusWNormSCLift_recipe_E7_three
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    GGTorusWNormSCLift 3 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  intro L _ _ ψ hψ hker hperf A hA hAI h27 hsc hrank
  have hcard6 : 3 ^ 6 ≤ Nat.card A := by
    rcases SCFourCover.three_dvd_two_pow_add_one_or_sub_one n with h3 | h3
    · exact hrank 6
        (ggTorusLift_E7Plus Nat.prime_three (by norm_num) (by rw [hK]; exact h3))
    · exact (by norm_num : 3 ^ 6 ≤ 3 ^ 7).trans
        (hrank 7 (TableBExc.ggTorusLift_E7 Nat.prime_three (by norm_num)
          (by rw [hK]; exact h3)))
  have hTB : GGTorusTBGroup 3 6 (TableBExc.RecipeGroup .E7 K)
      (TableBExc.RecipeID .E7 K) L ψ A :=
    ⟨hψ, hker, hperf, hA, hAI, hcard6, h27, hsc⟩
  intro _ Γ _ _ M C V _ _ ι φ h α _ _ _ _ hgen s hs
  exact ggWNormConcl_of_recipe_torusTBGroup hn hK (by norm_num) ψ A hTB
    ι φ h α hgen hs

theorem largeEvenLabelAll_wnormLift_E7_three {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E7) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSCLift 3 R I := by
  obtain ⟨t, r, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn hK
  exact ⟨K, i1, i2, hK, hQK, ggTorusWNormSCLift_recipe_E7_three hn hK⟩


end CFSG.StandardType.E7ThreeToral
