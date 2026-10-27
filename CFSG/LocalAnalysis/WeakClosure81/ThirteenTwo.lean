module

public import CFSG.LocalAnalysis.WeakClosure81.Thirteen
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenVG
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.Foundations
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem conjSub_eq_of_mem (h : Assumption131 G Γ VA i) {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ)
    {a : LGL 2 V} (ha : a ∈ A) : conjSub a (VA A) = VA A := by
  have hmem : a ∈ G ⊓ Subgroup.normalizer (A : Set (LGL 2 V)) :=
    ⟨h.le_G A hA ha, Subgroup.le_normalizer ha⟩
  rw [h.normalizer_eq A hA] at hmem
  exact hmem.2

theorem VA_ne_bot (h : Assumption131 G Γ VA i) {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ)
    (hrank : mRank A ≤ i) : VA A ≠ ⊥ := by
  intro hbot
  have h1 := commSub_le_VA_of_mRank_le h hA hrank
  rw [hbot, le_bot_iff] at h1
  exact commSub_ne_bot_of_mem h hA h1

theorem conjSubgroup_UAOf_inr_inv (h : Assumption131 G Γ VA i) {A : Subgroup (LGL 2 V)}
    (hA : A ∈ Γ) (g : G) :
    conjSubgroup (UAOf G VA A) (SemidirectProduct.inr g⁻¹ : VG G) =
      UAOf G VA (cj (g : LGL 2 V) A) := by
  unfold UAOf
  rw [conjSubgroup_wHat_sup_aHat_inr_inv, ← h.equivariant A hA g g.2]

theorem thirteen_two_one_VG (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    {A B : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hB : B ∈ Γ) (hne : A ≠ B) :
    UAOf G VA A ⊓ UAOf G VA B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨v, hv, g, hg, hxe⟩ :=
    (mem_wHat_sup_aHat (fun a ha => conjSub_eq_of_mem h hA ha)).mp hx.1
  obtain ⟨w, hw, g', hg', hxe'⟩ :=
    (mem_wHat_sup_aHat (fun a ha => conjSub_eq_of_mem h hB ha)).mp hx.2
  have heq : (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G) * SemidirectProduct.inr g =
      SemidirectProduct.inl (Multiplicative.ofAdd w) * SemidirectProduct.inr g' :=
    hxe.symm.trans hxe'
  have hgg : g = g' := by
    have := congrArg (projG G) heq
    simp only [map_mul, projG_inl, projG_inr, one_mul] at this
    exact Subtype.ext this
  subst hgg
  have hvw : v = w := by
    have := mul_right_cancel heq
    exact Multiplicative.ofAdd.injective (SemidirectProduct.inl_injective this)
  subst hvw
  have hg1 : (g : LGL 2 V) ∈ A ⊓ B := ⟨hg, hg'⟩
  rw [inf_eq_bot_of_mem h hrank hA hB hne, Subgroup.mem_bot] at hg1
  have hv1 : v ∈ VA A ⊓ VA B := ⟨hv, hw⟩
  rw [h.disjoint A hA B hB hne, Submodule.mem_bot] at hv1
  have hg1' : g = 1 := Subtype.ext hg1
  rw [hxe, hg1', hv1]
  simp

theorem isElemAbelian_UAOf (h : Assumption131 G Γ VA i) {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ)
    (hVAle : VA A ≤ fixSub A) : IsElemAbelian 2 (UAOf G VA A) := by
  exact isElemAbelian_wHat_sup_aHat (h.isElemAb A hA) hVAle

theorem isTI_UAOf (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ) :
    CFSG.CGT.Timmesfeld75.IsTI (UAOf G VA A) := by
  intro y
  rw [t75_conjSubgroup_eq]
  have hnorm : vHat G ≤ Subgroup.normalizer (UAOf G VA A : Set (VG G)) :=
    vHat_le_normalizer_wHat_sup_aHat (commSub_le_VA_of_mRank_le h hA (hrank A hA))
  obtain ⟨r, hr⟩ := exists_conjSubgroup_eq_inr hnorm y⁻¹
  rw [hr]
  have h1 := conjSubgroup_UAOf_inr_inv h hA r⁻¹
  rw [inv_inv] at h1
  rw [h1]
  by_cases hAc : cj ((r⁻¹ : G) : LGL 2 V) A = A
  · rw [hAc]
    right
    exact inf_idem _
  · left
    exact thirteen_two_one_VG h hrank hA (h.invariant A hA _ (r⁻¹).2) (Ne.symm hAc)

theorem hyp7_UAOf (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hVAle : VA A ≤ fixSub A) :
    Hyp7 (UAOf G VA A) := by
  refine ⟨isElemAbelian_UAOf h hA hVAle, ?_, isTI_UAOf h hrank hA⟩
  exact two_lt_card_wHat_sup_aHat (h.le_G A hA) (VA_ne_bot h hA (hrank A hA)) (h.ne_bot A hA)

private theorem map_conjSubgroup {G' H' : Type*} [Group G'] [Group H'] (f : G' →* H')
    (U : Subgroup G') (y : G') :
    (conjSubgroup U y).map f = conjSubgroup (U.map f) (f y) := by
  ext x
  rw [Subgroup.mem_map, mem_conjSubgroup_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_conjSubgroup_iff] at hu
    exact ⟨y * u * y⁻¹, hu, by simp⟩
  · rintro ⟨w, hw, hwx⟩
    refine ⟨y⁻¹ * w * y, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have e : y * (y⁻¹ * w * y) * y⁻¹ = w := by group
      rw [e]
      exact hw
    · have : f w = f y * x * (f y)⁻¹ := hwx
      rw [map_mul, map_mul, map_inv, this]
      group

theorem thirteen_two_two (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A) {A B : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hB : B ∈ Γ)
    (hAB : ∃ g ∈ G, B = cj g A) :
    (∀ u ∈ UAOf G VA A, ∀ v ∈ UAOf G VA B, u * v = v * u) ∨ ∃ y ∈ A ⊔ B, B = cj y A := by
  obtain ⟨g, hgG, hBg⟩ := hAB
  have hUB : UAOf G VA B =
      conjSubgroup (UAOf G VA A) (SemidirectProduct.inr (⟨g, hgG⟩ : G)⁻¹ : VG G) := by
    rw [conjSubgroup_UAOf_inr_inv h hA ⟨g, hgG⟩, hBg]
  have hTI := isTI_UAOf h hrank hA
  have hV := hyp7_UAOf h hrank hA (hVAle A hA)
  have hN : UAOf G VA A ⊓ Subgroup.normalizer (UAOf G VA B : Set (VG G)) ≠ ⊥ := by
    intro hbot
    have h1 : wHat G (VA A) ≤ UAOf G VA A ⊓ Subgroup.normalizer (UAOf G VA B : Set (VG G)) :=
      le_inf le_sup_left ((wHat_le_vHat _).trans (vHat_le_normalizer_wHat_sup_aHat
        (commSub_le_VA_of_mRank_le h hB (hrank B hB))))
    rw [hbot, le_bot_iff, wHat_eq_bot_iff] at h1
    exact VA_ne_bot h hA (hrank A hA) h1
  rcases two_conj_eq_or_comm hV.1 hTI (W := UAOf G VA A) (W' := UAOf G VA B)
      ⟨1, (conjSubgroup_one _).symm⟩ ⟨_, hUB⟩ hN with hc | ⟨y, hy, hyeq⟩
  · exact Or.inl hc
  · right
    have hπA : (UAOf G VA A).map (projG G) = A :=
      map_projG_wHat_sup_aHat (h.le_G A hA)
    have hπB : (UAOf G VA B).map (projG G) = B :=
      map_projG_wHat_sup_aHat (h.le_G B hB)
    refine ⟨(projG G y)⁻¹, ?_, ?_⟩
    · have hmem : projG G y ∈ (UAOf G VA A ⊔ UAOf G VA B).map (projG G) :=
        Subgroup.mem_map_of_mem _ hy
      rw [Subgroup.map_sup, hπA, hπB] at hmem
      exact Subgroup.inv_mem _ hmem
    · have h2 := congrArg (Subgroup.map (projG G)) hyeq
      rw [hπB, map_conjSubgroup, hπA] at h2
      rw [h2]
      unfold conjSubgroup cj
      simp

theorem inf_pCoreOf_UAOf (h : Assumption131 G Γ VA i) {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ) :
    UAOf G VA A ⊓ pCoreOf 2 (⊤ : Subgroup (VG G)) = wHat G (VA A) := by
  refine le_antisymm ?_ (le_inf ?_ (wHat_le_pCoreOf _))
  · intro x hx
    obtain ⟨v, hv, g, hg, rfl⟩ :=
      (mem_wHat_sup_aHat (fun a ha => conjSub_eq_of_mem h hA ha)).mp hx.1
    have hπ : projG G (SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr g) ∈
        pCoreOf 2 G :=
      map_projG_pCoreOf_le (Subgroup.mem_map_of_mem _ hx.2)
    simp only [map_mul, projG_inl, projG_inr, one_mul] at hπ
    have hg1 : (g : LGL 2 V) ∈ A ⊓ pCoreOf 2 G := ⟨hg, hπ⟩
    rw [h.inf_pCore A hA, Subgroup.mem_bot] at hg1
    have : g = 1 := Subtype.ext hg1
    rw [this, map_one, mul_one]
    exact mem_wHat.mpr ⟨v, hv, rfl⟩
  · exact le_sup_left

theorem thirteen_two_three (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A) {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) :
    omegaSet (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) = UAOf G VA '' Γ ∧
      iSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) = ⨆ A ∈ Γ, wHat G (VA A) := by
  have hnorm : vHat G ≤ Subgroup.normalizer (UAOf G VA A₀ : Set (VG G)) :=
    vHat_le_normalizer_wHat_sup_aHat (commSub_le_VA_of_mRank_le h hA₀ (hrank A₀ hA₀))
  have hΩ : omegaSet (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) = UAOf G VA '' Γ := by
    ext U
    constructor
    · rintro ⟨y, rfl, -, -⟩
      obtain ⟨r, hr⟩ := exists_conjSubgroup_eq_inr hnorm y
      have h1 := conjSubgroup_UAOf_inr_inv h hA₀ r⁻¹
      rw [inv_inv] at h1
      exact ⟨cj ((r⁻¹ : G) : LGL 2 V) A₀, h.invariant A₀ hA₀ _ (r⁻¹).2, by rw [hr, h1]⟩
    · rintro ⟨A, hA, rfl⟩
      obtain ⟨g, hgG, hAg⟩ := htrans A₀ hA₀ A hA
      refine ⟨SemidirectProduct.inr (⟨g, hgG⟩ : G)⁻¹, ?_, ?_, ?_⟩
      · rw [conjSubgroup_UAOf_inr_inv h hA₀ ⟨g, hgG⟩, hAg]
      · intro hbot
        have h1 : wHat G (VA A) ≤ vHat G ⊓ UAOf G VA A := le_inf (wHat_le_vHat _) le_sup_left
        rw [hbot, le_bot_iff, wHat_eq_bot_iff] at h1
        exact VA_ne_bot h hA (hrank A hA) h1
      · intro hle
        have h1 : UAOf G VA A ⊓ pCoreOf 2 (⊤ : Subgroup (VG G)) = UAOf G VA A :=
          inf_eq_left.mpr hle
        rw [inf_pCoreOf_UAOf h hA] at h1
        have h2 : aHat G A ≤ wHat G (VA A) := by
          rw [h1]
          exact le_sup_right
        have h3 := Subgroup.map_mono (f := projG G) h2
        rw [map_projG_aHat (h.le_G A hA), map_projG_wHat, le_bot_iff] at h3
        exact h.ne_bot A hA h3
  refine ⟨hΩ, ?_⟩
  unfold iSub
  rw [hΩ, iSup_image]
  refine iSup_congr fun A => iSup_congr fun hA => ?_
  exact inf_pCoreOf_UAOf h hA

end CFSG.LocalAnalysis.WeakClosure81
