module

public import CFSG.LocalAnalysis.WeakClosure81.W19VGJR
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)}

theorem aHat_mono {S T : Subgroup (LGL 2 V)} (h : S ≤ T) : aHat G S ≤ aHat G T := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hx
  exact mem_aHat.mpr ⟨g, h hg, rfl⟩

theorem aHat_sup_of_le {S T : Subgroup (LGL 2 V)} (hS : S ≤ G) (hT : T ≤ G) :
    aHat G (S ⊔ T) = aHat G S ⊔ aHat G T := by
  unfold aHat
  rw [Subgroup.subgroupOf_sup hS hT, Subgroup.map_sup]

private theorem commutator_le_of_le_of_le {S T : Subgroup (LGL 2 V)} (hS : S ≤ G) (hT : T ≤ G) :
    ⁅S, T⁆ ≤ G := by
  refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
  rw [commutatorElement_def]
  exact G.mul_mem (G.mul_mem (G.mul_mem (hS hg₁) (hT hg₂)) (G.inv_mem (hS hg₁)))
    (G.inv_mem (hT hg₂))

theorem aHat_commutator_of_le {S T : Subgroup (LGL 2 V)} (hS : S ≤ G) (hT : T ≤ G) :
    aHat G ⁅S, T⁆ = ⁅aHat G S, aHat G T⁆ := by
  unfold aHat
  have h1 : (⁅S, T⁆.subgroupOf G) = ⁅S.subgroupOf G, T.subgroupOf G⁆ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hS,
      Subgroup.map_subgroupOf_eq_of_le hT, Subgroup.map_subgroupOf_eq_of_le
        (commutator_le_of_le_of_le hS hT)]
  rw [h1, Subgroup.map_commutator]

theorem thirteen_four_mod
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    {A : Subgroup (LGL 2 V)} (h : Assumption131 G {B | ∃ g ∈ G, B = cj g A} commSub 1)
    (hA2 : Nat.card A = 2) {X : Subgroup (LGL 2 V)} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXG : X ≤ G) (hXexp : ∀ x ∈ X, x ^ p = 1) (hXR : X ⊓ pCoreOf 2 G = ⊥)
    (hXab : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ pCoreOf 2 G)
    (hAn : A ≤ normalizer ((X ⊔ pCoreOf 2 G : Subgroup (LGL 2 V)) : Set (LGL 2 V)))
    (hXA : X ≤ ⁅X ⊔ pCoreOf 2 G, A⁆ ⊔ pCoreOf 2 G)
    (hfaith : ∀ a ∈ A, (∀ x ∈ X, ⁅a, x⁆ ∈ pCoreOf 2 G) → a ∈ pCoreOf 2 G) :
    Nat.card X = p := by
  classical
  have hA : A ∈ {B | ∃ g ∈ G, B = cj g A} := ⟨1, G.one_mem, (cj_one A).symm⟩
  have hAG : A ≤ G := h.le_G A hA
  have hrank : ∀ B ∈ {B | ∃ g ∈ G, B = cj g A}, mRank B ≤ 1 := by
    rintro B ⟨g, hg, rfl⟩
    exact mRank_cj_le_one hA2 g
  have hstab : ∀ a ∈ A, conjSub a (commSub A) = commSub A :=
    fun a ha => conjSub_eq_of_mem h hA ha
  have hV7 := hyp7_UAOf h hrank hA (commSub_le_fixSub_of_card_two hA2)
  obtain ⟨hΩ, hI⟩ := thirteen_two_three h hrank orbit_trans' hA
  have hUΩ : UAOf G commSub A ∈
      omegaSet (UAOf G commSub A) (⊤ : Subgroup (VG G)) (vHat G) := by
    rw [hΩ]
    exact ⟨A, hA, rfl⟩
  have hRG : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hGn : G ≤ normalizer ((pCoreOf 2 G : Subgroup (LGL 2 V)) : Set (LGL 2 V)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
  haveI hJnormal : (JR G).Normal := normal_JR
  have hker : (projG G).ker ⊓ UAOf G commSub A = wHat G (commSub A) := by
    apply le_antisymm
    · rintro x ⟨hx1, hx2⟩
      obtain ⟨v, hv, g, hg, rfl⟩ := (mem_wHat_sup_aHat hstab).mp hx2
      have h1 : projG G (SemidirectProduct.inl (Multiplicative.ofAdd v) *
          SemidirectProduct.inr g) = 1 := hx1
      simp only [map_mul, projG_inl, projG_inr, one_mul] at h1
      have hg1 : g = 1 := Subtype.ext h1
      rw [hg1, map_one, mul_one]
      exact mem_wHat.mpr ⟨v, hv, rfl⟩
    · refine le_inf ?_ le_sup_left
      intro x hx
      have : (wHat G (commSub A)).map (projG G) = ⊥ := map_projG_wHat _
      exact Subgroup.mem_bot.mp (this ▸ Subgroup.mem_map_of_mem _ hx)
  have hrel : (JR G).relIndex (UAOf G commSub A) = 2 := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, inf_UAOf_JR hstab hAG (by
      have := h.inf_pCore A hA
      exact this), ← hker, Subgroup.inf_relIndex_right, Subgroup.relIndex_ker]
    change Nat.card ((wHat G (commSub A) ⊔ aHat G A).map (projG G)) = 2
    rw [map_projG_wHat_sup_aHat hAG, hA2]
  have hXRdec : ∀ y ∈ X ⊔ pCoreOf 2 G, ∃ x ∈ X, ∃ r ∈ pCoreOf 2 G, y = x * r := by
    intro y hy
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X (pCoreOf 2 G)
      (hXG.trans hGn)] at hy
    obtain ⟨x, hx, r, hr, rfl⟩ := hy
    exact ⟨x, hx, r, hr, rfl⟩
  have haXR : aHat G (X ⊔ pCoreOf 2 G) ≤ JR G ⊔ aHat G X := by
    intro z hz
    obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hz
    obtain ⟨x, hx, r, hr, hxr⟩ := hXRdec _ hg
    have hxG : x ∈ G := hXG hx
    have hrG : r ∈ G := hRG hr
    have e : g = ⟨x, hxG⟩ * ⟨r, hrG⟩ := Subtype.ext hxr
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_aHat.mpr ⟨⟨x, hxG⟩, hx, rfl⟩))
      (Subgroup.mem_sup_left (inr_mem_JR hr))
  have hnormY : UAOf G commSub A ≤ normalizer ((JR G ⊔ aHat G X : Subgroup (VG G)) :
      Set (VG G)) := by
    refine sup_le ?_ ?_
    · exact ((wHat_le_vHat _).trans vHat_le_JR).trans
        (le_sup_left.trans Subgroup.le_normalizer)
    · intro z hz
      obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hz
      apply E1.mem_normalizer_of_conj_mem
      intro y hy
      have hle : JR G ⊔ aHat G X ≤ (JR G ⊔ aHat G X).comap
          (MulAut.conj (SemidirectProduct.inr g : VG G)).toMonoidHom := by
        refine sup_le ?_ ?_
        · intro j hj
          exact Subgroup.mem_sup_left (hJnormal.conj_mem j hj _)
        · intro k hk
          obtain ⟨x', hx', rfl⟩ := mem_aHat.mp hk
          rw [Subgroup.mem_comap]
          change (SemidirectProduct.inr g : VG G) * SemidirectProduct.inr x' *
            (SemidirectProduct.inr g : VG G)⁻¹ ∈ JR G ⊔ aHat G X
          rw [← map_mul, ← map_inv, ← map_mul]
          have hmem : (g : LGL 2 V) * (x' : LGL 2 V) * (g : LGL 2 V)⁻¹ ∈
              X ⊔ pCoreOf 2 G :=
            (Subgroup.mem_normalizer_iff.1 (hAn hg) _).1 (Subgroup.mem_sup_left hx')
          exact haXR (mem_aHat.mpr ⟨g * x' * g⁻¹, by simpa using hmem, rfl⟩)
      exact hle hy
  have hcommY : JR G ⊔ aHat G X ≤ ⁅JR G ⊔ aHat G X, UAOf G commSub A⁆ ⊔ JR G := by
    refine sup_le le_sup_right ?_
    have hXRG : X ⊔ pCoreOf 2 G ≤ G := sup_le hXG hRG
    have hCG : ⁅X ⊔ pCoreOf 2 G, A⁆ ≤ G := commutator_le_of_le_of_le hXRG hAG
    calc aHat G X ≤ aHat G (⁅X ⊔ pCoreOf 2 G, A⁆ ⊔ pCoreOf 2 G) := aHat_mono hXA
      _ = aHat G ⁅X ⊔ pCoreOf 2 G, A⁆ ⊔ aHat G (pCoreOf 2 G) := aHat_sup_of_le hCG hRG
      _ = ⁅aHat G (X ⊔ pCoreOf 2 G), aHat G A⁆ ⊔ aHat G (pCoreOf 2 G) := by
          rw [aHat_commutator_of_le hXRG hAG]
      _ ≤ ⁅JR G ⊔ aHat G X, UAOf G commSub A⁆ ⊔ JR G := by
          refine sup_le_sup (Subgroup.commutator_mono haXR le_sup_right) ?_
          intro z hz
          obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hz
          exact inr_mem_JR hg
  have hfaith' : ∀ a ∈ UAOf G commSub A, (∀ y ∈ JR G ⊔ aHat G X, ⁅a, y⁆ ∈ JR G) → a ∈ JR G := by
    intro a ha hall
    obtain ⟨v, hv, g, hg, rfl⟩ := (mem_wHat_sup_aHat hstab).mp ha
    have hgR : (g : LGL 2 V) ∈ pCoreOf 2 G := by
      apply hfaith _ hg
      intro x hx
      have hxG := hXG hx
      have h1 := hall (SemidirectProduct.inr (⟨x, hxG⟩ : G))
        (Subgroup.mem_sup_right (mem_aHat.mpr ⟨⟨x, hxG⟩, hx, rfl⟩))
      rw [mem_JR] at h1
      simp only [map_commutatorElement, map_mul, projG_inl, projG_inr, one_mul] at h1
      exact h1
    exact (JR G).mul_mem (vHat_le_JR (mem_wHat.mpr ⟨v, Submodule.mem_top, rfl⟩))
      (inr_mem_JR hgR)
  have hqj : ∀ j ∈ JR G, (QuotientGroup.mk' (JR G)) j = 1 := fun j hj =>
    (QuotientGroup.eq_one_iff j).mpr hj
  have hq : ∀ j ∈ JR G, ∀ w : VG G,
      (QuotientGroup.mk' (JR G)) (j * w) = (QuotientGroup.mk' (JR G)) w := by
    intro j hj w
    rw [map_mul, hqj j hj, one_mul]
  have hYform : ∀ y ∈ JR G ⊔ aHat G X, ∃ x' : G, (x' : LGL 2 V) ∈ X ∧
      ∃ j ∈ JR G, y = j * SemidirectProduct.inr x' := by
    intro y hy
    have h1 : y ∈ ((JR G ⊔ aHat G X : Subgroup (VG G)) : Set (VG G)) := hy
    rw [Subgroup.normal_mul] at h1
    obtain ⟨j, hj, k, hk, rfl⟩ := h1
    obtain ⟨x', hx', rfl⟩ := mem_aHat.mp hk
    exact ⟨x', hx', j, hj, rfl⟩
  have hexp : ∀ y ∈ JR G ⊔ aHat G X, y ^ p ∈ JR G := by
    intro y hy
    obtain ⟨x', hx', j, hj, rfl⟩ := hYform y hy
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (JR G)) ((j * SemidirectProduct.inr x') ^ p) = 1
    rw [map_pow, hq j hj, ← map_pow, ← map_pow]
    have h1 : x' ^ p = 1 := Subtype.ext (by simpa using hXexp _ hx')
    rw [h1, map_one, map_one]
  have hab' : ∀ y ∈ JR G ⊔ aHat G X, ∀ z ∈ JR G ⊔ aHat G X, ⁅y, z⁆ ∈ JR G := by
    intro y hy z hz
    obtain ⟨x', hx', jx, hjx, rfl⟩ := hYform y hy
    obtain ⟨y', hy', jy, hjy, rfl⟩ := hYform z hz
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (JR G))
      ⁅jx * SemidirectProduct.inr x', jy * SemidirectProduct.inr y'⁆ = 1
    have hxy : (SemidirectProduct.inr ⁅x', y'⁆ : VG G) ∈ JR G :=
      inr_mem_JR (hXab _ hx' _ hy')
    have h3 : (QuotientGroup.mk' (JR G)) (SemidirectProduct.inr ⁅x', y'⁆ : VG G) = 1 :=
      hqj _ hxy
    have h2 := map_commutatorElement ((QuotientGroup.mk' (JR G)).comp SemidirectProduct.inr)
      x' y'
    simp only [MonoidHom.comp_apply, h3] at h2
    simp only [map_commutatorElement, hq jx hjx, hq jy hjy]
    exact h2.symm
  have hres := h763 (VG G) (UAOf G commSub A) hV7 ⊤ (vHat G) (JR G) (UAOf G commSub A)
    (JR G ⊔ aHat G X) p hp hp2 le_top (normal_vHat.subgroupOf _) (isElemAbelian_wHat ⊤).1
    (hI.le.trans (iSup₂_le fun B _ => (wHat_le_vHat _).trans vHat_le_JR)) JR_le_pCoreOf
    (hJnormal.subgroupOf _) hUΩ le_top hrel le_sup_left le_top hnormY hcommY hfaith' hexp hab'
  have hcardaX : Nat.card (aHat G X) = Nat.card X := by
    unfold aHat
    rw [Subgroup.card_map_of_injective SemidirectProduct.inr_injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXG).toEquiv
  have hJaX : JR G ⊓ aHat G X = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxJ, hxa⟩
    obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hxa
    have hxJ' : (SemidirectProduct.inr g : VG G) ∈ JR G := hxJ
    rw [mem_JR, projG_inr] at hxJ'
    have h1 : (g : LGL 2 V) ∈ X ⊓ pCoreOf 2 G := ⟨hg, hxJ'⟩
    rw [hXR, Subgroup.mem_bot] at h1
    have : g = 1 := Subtype.ext h1
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hcardY : (JR G).relIndex (JR G ⊔ aHat G X) = Nat.card X := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hJaX,
      Subgroup.relIndex_bot_left, hcardaX]
  rw [← hcardY]
  exact hres

end CFSG.LocalAnalysis.WeakClosure81

end
