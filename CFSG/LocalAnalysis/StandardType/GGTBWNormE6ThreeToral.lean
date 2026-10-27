module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGL45E67Center
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGE6ToralInnerAction
public import CFSG.LocalAnalysis.StandardType.GGE6M6cTransfer
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral

public section

namespace CFSG.StandardType.E6ThreeWNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc

theorem exists_pow_three_eq_of_not_dvd {K : Type} [Field K] [Finite K]
    (hK3 : ¬ 3 ∣ Nat.card K - 1) (s : Kˣ) : ∃ u : Kˣ, u ^ 3 = s := by
  have hcop : (Nat.card Kˣ).Coprime 3 := by
    rw [Nat.card_units]
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hK3))
  exact (powCoprime hcop).surjective s

theorem torusSubgroup_E6_eq_top_of_not_dvd {K : Type} [Field K] [Finite K]
    (hK3 : ¬ 3 ∣ Nat.card K - 1) : TableB.torusSubgroup Tag.E6.cartan K = ⊤ := by
  rw [eq_top_iff]
  intro a _
  choose u hu using fun j => exists_pow_three_eq_of_not_dvd hK3 (a j)
  have ha : a = u ^ 3 := funext fun j => (hu j).symm
  rw [ha]
  exact pow_three_mem_torusSubgroup_E6 u


theorem ggOutdiagPrime_E6_three {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K - 1) :
    GGOutdiagPrime 3 (RecipeGroup .E6 K) (RecipeID .E6 K) := by
  intro φ hφ _
  obtain ⟨x, hx⟩ := idImage_subset_inn_of_top .E6 K (torusSubgroup_E6_eq_top_of_not_dvd hK3) hφ
  exact ⟨x, hx⟩


theorem ggWNormConcl_recipe_E6_three_plus_of_inner {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK3 : 3 ∣ Nat.card K + 1)
    (hInner : ∀ E : Subgroup (adjointGroup .E6 K), IsElemAbelian 3 E → 3 ^ 4 ≤ Nat.card E →
      ∀ β : MulAut (adjointGroup .E6 K), ∃ r : adjointGroup .E6 K, ∀ x ∈ E, β x = r * x * r⁻¹)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* RecipeGroup .E6 K} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 4 (RecipeGroup .E6 K) (RecipeID .E6 K) L' ψ A)
    {Λ V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod 3) V)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L')) A) :
    GGWNormConcl ι φ h α s := by
  classical
  obtain ⟨hψ, hker, hperf, hA, hAI, h4, -, hsc⟩ := hTB
  have hK3' : ¬ 3 ∣ Nat.card K - 1 := by
    intro hd
    have h1 : 1 ≤ Nat.card K := Nat.card_pos
    omega
  have hcop : Nat.Coprime 3 (Nat.gcd 3 (Nat.card K - 1)) := by
    rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hK3')]
    exact Nat.coprime_one_right 3
  obtain ⟨Λ₀, hΛeq, -, -, hAΛ, hE, hEc, -⟩ :=
    TwE6TB.exists_innerModel Nat.prime_three (center_recipeGroup_eq_bot .E6 K)
      (ggOutdiagPrime_E6_three hK3')
      (ggCenterPrime_recipe_E6_of_coprime Nat.prime_three (by decide) hcop)
      ψ hψ hker hperf hA hAI hsc
  let ε := recipeEquiv .E6 K
  let E := (A.comap Λ₀).map ε.toMonoidHom
  have hEg : IsElemAbelian 3 E := TableB.isElemAbelian_map hE _
  have hEcard : Nat.card E = Nat.card A :=
    (Subgroup.card_map_of_injective ε.injective).trans hEc
  let ψ₁ : L' →* adjointGroup .E6 K := ε.toMonoidHom.comp ψ
  have hψ₁ : Function.Surjective ψ₁ := ε.surjective.comp hψ
  have hker₁ : ψ₁.ker ≤ Subgroup.center L' := by
    intro l hl
    apply hker
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : ε (ψ l) = 1 := hl
    rwa [ε.map_eq_one_iff] at h1
  let Λ₁ : adjointGroup .E6 K →* MulAut L' := Λ₀.comp ε.symm.toMonoidHom
  have hΛ₁ψ : ∀ l, Λ₁ (ψ₁ l) = MulAut.conj l := by
    intro l
    change Λ₀ (ε.symm (ε (ψ l))) = MulAut.conj l
    rw [ε.symm_apply_apply]
    exact hΛeq rfl
  have hEA : E.map Λ₁ = A := by
    change ((A.comap Λ₀).map ε.toMonoidHom).map (Λ₀.comp ε.symm.toMonoidHom) = A
    rw [Subgroup.map_map]
    have hcomp : (Λ₀.comp ε.symm.toMonoidHom).comp ε.toMonoidHom = Λ₀ := by
      refine MonoidHom.ext fun x => ?_
      change Λ₀ (ε.symm (ε x)) = Λ₀ x
      rw [ε.symm_apply_apply]
    rw [hcomp]
    exact Subgroup.map_comap_eq_self (fun a ha => hAΛ a ha)
  exact ggWNormConcl_of_centralCover_innerAction ψ₁ hψ₁ hker₁ center_adjointGroup_eq_bot
    Λ₁ hΛ₁ψ E A hEA (hInner E hEg (hEcard ▸ h4)) ι φ h α hgen hs


theorem isToral_of_three_pow_four_le {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK3 : 3 ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E6 K)) (hE : IsElemAbelian 3 E)
    (h4 : 3 ^ 4 ≤ Nat.card E) :
    ExcFramesHalf.IsToralSubgroup .E6 (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup .E6 K).subtype)) := by
  classical
  rcases h4.eq_or_lt with h | h
  · exact E6M6cTransfer.isToral_of_card_eq_three_pow_four hK3 E hE h.symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite E := Nat.finite_of_card_ne_zero (lt_of_le_of_lt (Nat.zero_le _) h).ne'
  have hP : IsPGroup 3 E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h5 : 3 ^ 5 ≤ Nat.card E := by
    rw [hk] at h ⊢
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 h)
  set j := (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .E6 K).subtype
  have hj : Function.Injective j := fun x y hxy =>
    Subgroup.subtype_injective _ (baseChangeGL_injective _ hxy)
  have h3K : ¬ 3 ∣ Nat.card K := fun h3 => by omega
  refine ExcFramesHalf.bigElemAbelianToralBar_E6_three K h3K (E.map j) ?_ ?_ ?_ ?_
  · rintro _ ⟨x, -, rfl⟩
    exact baseChangeGL_mem_adjointGroup _ x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg j (congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective hj]
    exact h5

theorem ggWNormConcl_recipe_E6_three_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK3 : 3 ∣ Nat.card K + 1)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* RecipeGroup .E6 K} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 4 (RecipeGroup .E6 K) (RecipeID .E6 K) L' ψ A)
    {Λ V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod 3) V)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L')) A) :
    GGWNormConcl ι φ h α s :=
  ggWNormConcl_recipe_E6_three_plus_of_inner hK3
    (fun E hE h4 β => E6ToralInner.exists_conj_eq_of_toral_E6 hK3 E hE
      (isToral_of_three_pow_four_le hK3 E hE h4) β) hTB ι φ h α hgen hs

end CFSG.StandardType.E6ThreeWNorm
