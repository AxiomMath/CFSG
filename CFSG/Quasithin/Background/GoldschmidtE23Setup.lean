module

public import CFSG.Quasithin.Background.FFC10C
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.B2FactorizationSolvable

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace GE23

section MinPar

variable {Γ : Type*} [Group Γ]

theorem minParabolic_map_subtype {X : Subgroup Γ} {S M' : Subgroup ↥X}
    (h : MinParabolic (⊤ : Subgroup ↥X) S M') :
    MinParabolic X (S.map X.subtype) (M'.map X.subtype) := by
  have hmem : ∀ (K : Subgroup ↥X) (z : ↥X), (z : Γ) ∈ K.map X.subtype ↔ z ∈ K := fun K z =>
    Subgroup.mem_map_iff_mem X.subtype_injective
  refine ⟨⟨Subgroup.map_subtype_le S, h.isSylow.2.1.map _, ?_⟩, ?_, ?_⟩
  · rw [map_subtype_subgroupOf' S]
    have h2 := h.isSylow.2.2
    change ¬ 2 ∣ S.relIndex ⊤ at h2
    rwa [Subgroup.relIndex_top_right] at h2
  · intro hX
    apply h.not_normal
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (hX x.2) (y : Γ)
    have e : ((x : Γ) * (y : Γ) * (x : Γ)⁻¹) = ((x * y * x⁻¹ : ↥X) : Γ) := by simp
    rw [e, hmem, hmem] at h1
    exact h1
  · rw [isUniqueMaxOver_iff]
    refine ⟨B6.isMaxSubgroupIn_map_subtype h.maximal, Subgroup.map_mono h.le, fun N hN hSN => ?_⟩
    have hNX : N ≤ X := hN.1.le
    have hmax := B6.isMaxSubgroupIn_top_subgroupOf hN
    have hSle : S ≤ N.subgroupOf X := by
      intro s hs
      exact hSN ⟨s, hs, rfl⟩
    have := h.eq_of_maximal hmax hSle
    rw [← this, Subgroup.map_subgroupOf_eq_of_le hNX]

end MinPar

section Star

variable {Γ : Type} [Group Γ] {H T M V : Subgroup Γ} (hV : IsElemAbelian 2 V)

@[expose] noncomputable def starHom (hHN : H ≤ Subgroup.normalizer (V : Set Γ)) :
    ↥H →* ↥(autI hV H) :=
  (convHom hV H hHN).codRestrict (autI hV H) (fun g => by
    rw [← range_convHom hV H hHN]
    exact ⟨g, rfl⟩)

theorem starHom_apply (hHN : H ≤ Subgroup.normalizer (V : Set Γ)) (g : ↥H) :
    ((starHom hV hHN g : ↥(autI hV H)) : MulAut (IntMod V hV)) = convHom hV H hHN g := rfl

theorem starHom_surjective (hHN : H ≤ Subgroup.normalizer (V : Set Γ)) :
    Function.Surjective (starHom hV hHN) := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hx
  exact ⟨⟨g, hgH⟩, Subtype.ext rfl⟩

theorem ker_starHom (hHN : H ≤ Subgroup.normalizer (V : Set Γ)) :
    (starHom hV hHN).ker = (H ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf H := by
  rw [← ker_convHom hV H hHN]
  ext g
  simp only [MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem minParabolic_star_top [Finite Γ] (h : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hHV : ¬ H ≤ Subgroup.centralizer (V : Set Γ)) :
    MinParabolic (⊤ : Subgroup ↥(autI hV H)) ((T.subgroupOf H).map (starHom hV hred.2.1))
      ((M.subgroupOf H).map (starHom hV hred.2.1)) := by
  refine MinParabolic.map_of_surjective h.subgroupOf (starHom_surjective hV hred.2.1) ?_
  rw [ker_starHom]
  intro g hg
  have hk : (g : Γ) ∈ kerIn M H :=
    h.inf_centralizer_le_kerIn hred hHV (Subgroup.mem_subgroupOf.1 hg)
  exact Subgroup.mem_subgroupOf.2 (kerIn_le hk)

theorem map_star_subgroupOf (hHN : H ≤ Subgroup.normalizer (V : Set Γ)) {K : Subgroup Γ}
    (hKH : K ≤ H) :
    ((K.subgroupOf H).map (starHom hV hHN)).map (autI hV H).subtype = autI hV K := by
  rw [Subgroup.map_map]
  have : (autI hV H).subtype.comp (starHom hV hHN) = convHom hV H hHN := rfl
  rw [this, ← autI_eq_map_convHom hV hHN hKH]

theorem minParabolic_star [Finite Γ] (h : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hHV : ¬ H ≤ Subgroup.centralizer (V : Set Γ)) :
    MinParabolic (autI hV H) (autI hV T) (autI hV M) := by
  have h1 := minParabolic_map_subtype (minParabolic_star_top hV h hred hHV)
  rwa [map_star_subgroupOf hV hred.2.1 h.isSylow.1,
    map_star_subgroupOf hV hred.2.1 (h.maximal.1.le)] at h1

theorem sqtk_star [Finite Γ] (hsq : SQTKGroup ↥H) (hHN : H ≤ Subgroup.normalizer (V : Set Γ)) :
    ∃ (H₀ : Type) (_ : Group H₀) (_ : Finite H₀), CFSG.Open.SQTKTauCeti.StronglyQuasithin H₀ ∧
      CFSG.SectionRank.IsKGroupCat H₀ ∧ ∃ f : H₀ →* ↥(autI hV H), Function.Surjective f :=
  ⟨↥H, inferInstance, inferInstance, hsq.1, hsq.2, starHom hV hHN, starHom_surjective hV hHN⟩

theorem pCoreOf_star [Finite Γ] (hred : IsTwoReducedIn H V) : pCoreOf 2 (autI hV H) = ⊥ := by
  refine eq_bot_of_normal_isPGroup hV hred (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_ ?_
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem not_isSolvable_star [Finite Γ] (h : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hHV : ¬ H ≤ Subgroup.centralizer (V : Set Γ)) (hns : ¬ Group.IsSolvable ↥H) :
    ¬ Group.IsSolvable ↥(autI hV H) := by
  intro hs
  apply hns
  have hker : Group.IsSolvable ↥(starHom hV hred.2.1).ker := by
    have hsol : Group.IsSolvable ↥(kerIn (M.subgroupOf H) ⊤) := h.subgroupOf.isSolvable_kerIn
    rw [B6.kerIn_subgroupOf_top] at hsol
    have hle : (starHom hV hred.2.1).ker ≤ (kerIn M H).subgroupOf H := by
      rw [ker_starHom]
      intro g hg
      exact Subgroup.mem_subgroupOf.2
        (h.inf_centralizer_le_kerIn hred hHV (Subgroup.mem_subgroupOf.1 hg))
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact Group.isSolvable_of_ker_le_range (starHom hV hred.2.1).ker.subtype (starHom hV hred.2.1)
    (by simp [Subgroup.range_subtype])

end Star

section Ctx

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}

theorem blkCtx_of_inputs (hP4 : AsB15Part4) (hComp : B69.AsB69Component)
    (hV : ∀ v : V, v ^ 2 = 1)
    (hsq : ∃ (H : Type) (_ : Group H) (_ : Finite H), CFSG.Open.SQTKTauCeti.StronglyQuasithin H ∧
      CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥X, Function.Surjective f)
    (h : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hns : ¬ Group.IsSolvable ↥X) : B69.BlkCtx X T M := by
  have hctx : B69.ShapeCtx X T M := B69.shapeCtx_of_component hComp hV hsq h hO2 hFF hns
  have hact := B69.exists_active hV hP4 h hO2 hFF hns
  have hG1 := B69.asB69AltBlock_of_component hP4 hComp
  have hG2 := B69.asB69GenByMin_of hP4 hComp
  have hffJ : ffJ X ≤ ⨆ (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X),
      B69.blk X L := by
    refine (hG2 V hV X T M hsq h hO2 hFF hns).trans ?_
    refine iSup₂_le fun A hA => iSup_le fun _ => ?_
    obtain ⟨L, hL, hLA⟩ := B69.exists_component_of_nonsolvable hV hP4 h hO2 hns hA
    exact (B69.le_blk_of hA hLA).trans
      (le_iSup₂_of_le (f := fun (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X) =>
        B69.blk X L) L hL le_rfl)
  have hG1' : ∀ A L : Subgroup (MulAut V), IsFFStarMin X A → CFSG.Open.IsComponentOf L X →
      ⁅L, A⁆ = L → B69.AltShape M A L (commV L) → ∀ A' : Subgroup (MulAut V), IsFFStarMin X A' →
        ⁅L, A'⁆ = L → A' ≤ L ⊔ A := fun A L hA hL hLA hAlt A' hA' hLA' =>
    hG1 V hV X T M A L ⟨hsq, h, hO2, hFF, hns, hA, hL, hLA⟩ (commV L)
      (B69.commV_mem_irrPlus hV hctx hA hL hLA) hAlt A' hA' hLA'
  exact ⟨hV, hP4, hctx, hO2, hact, hffJ, hG1'⟩

end Ctx

end GE23

end CFSG.Quasithin
