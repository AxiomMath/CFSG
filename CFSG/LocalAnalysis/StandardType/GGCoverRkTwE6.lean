module

public import CFSG.LocalAnalysis.StandardType.GGCoverRkTwE6Fuse
public import CFSG.LocalAnalysis.StandardType.GGCoverRkTwE6Auto
public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6
public import CFSG.LocalAnalysis.StandardType.GGWPlusPositionRk
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBMeta

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley

private lemma mulAut_conj_eq {G : Type*} [Group G] (a : MulAut G) (r : G) :
    a * MulAut.conj r * a⁻¹ = MulAut.conj (a r) := by
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

private lemma mulAut_conj_inv {G : Type*} [Group G] (r : G) :
    (MulAut.conj r)⁻¹ = MulAut.conj r⁻¹ :=
  inv_eq_of_mul_eq_one_right (by
    ext x
    simp [MulAut.conj_apply])

private lemma transport_id {G : Type*} [Group G] (a : MulAut G) (r i : G) :
    (MulAut.conj ((a i)⁻¹ * r * i))⁻¹ * a =
      (MulAut.conj i)⁻¹ * ((MulAut.conj r)⁻¹ * a) * MulAut.conj i := by
  have h1 : (MulAut.conj ((a i)⁻¹ * r * i))⁻¹ =
      (MulAut.conj i)⁻¹ * (MulAut.conj r)⁻¹ * MulAut.conj (a i) := by
    rw [mulAut_conj_inv,
      show ((a i)⁻¹ * r * i)⁻¹ = i⁻¹ * r⁻¹ * (a i) from by group]
    rw [map_mul, map_mul, map_inv, map_inv]
  rw [h1, ← mulAut_conj_eq a i]
  group

private theorem ofAdd_pow_three_zmod3 {n : ℕ} (x : Multiplicative (Fin n → ZMod 3)) :
    x ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  show (3 : ℕ) • Multiplicative.toAdd x = 0
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply]
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3) 3, CharP.cast_eq_zero (ZMod 3) 3, zero_smul]

private lemma commute_conj {G : Type*} [Group G] (g x y : MulAut G) (h : Commute x y) :
    Commute (g * x * g⁻¹) (g * y * g⁻¹) := by
  show g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹)
  calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [show x * y = y * x from h]
    _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

theorem ggCoverPTableBRk_twE6_three
    {K : Type} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) :
    GGCoverPTableBRk 3 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) 6 := by
  intro M _ _ L' E θ hE hP hr6 a ha
  haveI : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  haveI : Finite (MulAut (TwE6Delta.RecipeR K n)) := TwE6Delta.finite_mulAut_recipeR hK
  have hr : 3 ^ 5 ≤ Nat.card (ggLAutImage L' θ E) := by
    simpa using pow_pred_le_card_ggLAutImage hP Nat.prime_three hr6
  have hA : IsElemAbelian 3 (ggLAutImage L' θ E) :=
    ggIsElemAbelian_map (ggIsElemAbelian_subgroupOf hP.2.1 _) (ggLAut L' θ)
  have hI : (ggLAutImage L' θ E : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆
      TwE6Delta.RecipeI K n := by
    intro a ha
    simp only [ggLAutImage, Subgroup.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    have hxe : (⟨(x : M), hE hx⟩ : Subgroup.normalizer (L' : Set M)) = x :=
      Subtype.ext rfl
    rw [← hxe]
    exact hP.2.2.2.1 ⟨(x : M), hx⟩
  obtain ⟨k, hk⟩ := ha
  obtain ⟨D, X, hgood, hH, -, -, -, -, -, -, hVH⟩ := exists_langFrame_recipeR n hn hK h3
  have hĒH : ggLAutImage L' θ E ≤ D.H := by
    change (ggLAutImage L' θ E : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ (D.H : Set _)
    rw [hH]
    exact hI
  obtain ⟨γ, hγH, hγconj⟩ := hgood.shape (ggLAutImage L' θ E) hĒH hA hr
  let V' : Subgroup (MulAut (TwE6Delta.RecipeR K n)) :=
    D.diag.range.map (MulAut.conj (γ⁻¹)).toMonoidHom
  have hĒV' : ggLAutImage L' θ E ≤ V' := by
    intro x hx
    change x ∈ D.diag.range.map (MulAut.conj (γ⁻¹)).toMonoidHom
    refine Subgroup.mem_map.mpr ⟨γ * x * γ⁻¹, hγconj x hx, ?_⟩
    show MulAut.conj (γ⁻¹) (γ * x * γ⁻¹) = x
    rw [MulAut.conj_apply]
    group
  have htopel : IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (Fin Tag.E6.rank → ZMod 3))) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · exact Subtype.ext (mul_comm (a : Multiplicative (Fin Tag.E6.rank → ZMod 3)) b)
    · exact ofAdd_pow_three_zmod3 x
  have hdiagel : IsElemAbelian 3 D.diag.range := by
    have h := CFSG.Open.IsElemAbelian.map htopel D.diag
    rwa [Subgroup.map_top] at h
  have hcardDiag : Nat.card D.diag.range = 3 ^ 6 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hgood.faithful).toEquiv,
      Nat.card_congr (MulEquiv.piMultiplicative fun _ : Fin Tag.E6.rank => ZMod 3).toEquiv,
      Nat.card_fun,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3),
      Nat.card_zmod, Nat.card_fin]
    rfl
  have hV'el : IsElemAbelian 3 V' := by
    change IsElemAbelian 3 (D.diag.range.map (MulAut.conj (γ⁻¹)).toMonoidHom)
    exact ggIsElemAbelian_map hdiagel _
  have hV'card : Nat.card V' = 3 ^ 6 := by
    change Nat.card (D.diag.range.map (MulAut.conj (γ⁻¹)).toMonoidHom) = 3 ^ 6
    rw [Subgroup.card_map_of_injective (MulAut.conj (γ⁻¹)).injective, hcardDiag]
  have hV'H : V' ≤ D.H := by
    intro y hy
    change y ∈ D.diag.range.map (MulAut.conj (γ⁻¹)).toMonoidHom at hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    change MulAut.conj (γ⁻¹) v ∈ D.H
    rw [MulAut.conj_apply]
    exact D.H.mul_mem (D.H.mul_mem (D.H.inv_mem hγH) (hVH hv)) hγH
  have hV'I : (V' : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
    rw [← hH]
    exact hV'H
  obtain ⟨ι, hι⟩ :=
    exists_conj_normalized_twE6 (a := a) n hn hK h3 hV'el hV'I hV'card hk
  let A'' : Subgroup (MulAut (TwE6Delta.RecipeR K n)) :=
    V'.map (MulAut.conj (MulAut.conj ι : MulAut (TwE6Delta.RecipeR K n))).toMonoidHom
  have hA''el : IsElemAbelian 3 A'' := by
    change IsElemAbelian 3 (V'.map (MulAut.conj (MulAut.conj ι : MulAut (TwE6Delta.RecipeR K n))).toMonoidHom)
    exact ggIsElemAbelian_map hV'el _
  have hA''card : Nat.card A'' = 3 ^ 6 := by
    change Nat.card (V'.map (MulAut.conj (MulAut.conj ι : MulAut (TwE6Delta.RecipeR K n))).toMonoidHom) = 3 ^ 6
    rw [Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj ι : MulAut (TwE6Delta.RecipeR K n))).injective,
      hV'card]
  have hconjI : MulAut.conj ι ∈
      LargeEvenChevIDImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n) :=
    conj_mem_chevIDImage (TwE6Delta.RecipeH K n) ι
  have hA''I : (A'' : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
    intro y hy
    change y ∈ V'.map (MulAut.conj (MulAut.conj ι : MulAut (TwE6Delta.RecipeR K n))).toMonoidHom at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxI : x ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n) := hV'I hx
    change MulAut.conj (MulAut.conj ι) x ∈
      LargeEvenChevIDImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)
    rw [MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hconjI hxI) (Subgroup.inv_mem _ hconjI)
  obtain ⟨ρ'', hρ''⟩ :=
    exists_rho_commute_of_normalizes_twE6 (a := a) n hn hK h3 hA''el hA''I hA''card hk hι
  refine ⟨(a ι)⁻¹ * ρ'' * ι, fun e => ?_⟩
  set ē : MulAut (TwE6Delta.RecipeR K n) := ggLAut L' θ ⟨e, hE e.2⟩ with hēdef
  have hēĒ : ē ∈ ggLAutImage L' θ E := by
    rw [hēdef, ggLAutImage]
    exact Subgroup.mem_map.mpr ⟨⟨e, hE e.2⟩, Subgroup.mem_subgroupOf.mpr e.2, rfl⟩
  have hcιē : MulAut.conj ι * ē * (MulAut.conj ι)⁻¹ ∈ A'' := by
    change MulAut.conj ι * ē * (MulAut.conj ι)⁻¹ ∈
      V'.map (MulAut.conj (MulAut.conj ι : MulAut (TwE6Delta.RecipeR K n))).toMonoidHom
    refine Subgroup.mem_map.mpr ⟨ē, hĒV' hēĒ, ?_⟩
    change MulAut.conj (MulAut.conj ι) ē = MulAut.conj ι * ē * (MulAut.conj ι)⁻¹
    rw [MulAut.conj_apply]
  have hcomm : Commute ((MulAut.conj ρ'')⁻¹ * a)
      (MulAut.conj ι * ē * (MulAut.conj ι)⁻¹) := hρ'' _ hcιē
  have h1 := commute_conj (MulAut.conj ι)⁻¹ ((MulAut.conj ρ'')⁻¹ * a)
      (MulAut.conj ι * ē * (MulAut.conj ι)⁻¹) hcomm
  rw [transport_id a ρ'' ι]
  simpa [mul_assoc] using h1

end CFSG.StandardType
