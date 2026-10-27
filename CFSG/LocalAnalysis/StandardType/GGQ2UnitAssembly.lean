module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open (IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] {H E : Subgroup G} {N : ℕ} {K : Type} [Field K]
  {hEN : E ≤ Subgroup.normalizer (H : Set G)} {ζ : Multiplicative (ZMod 3) →* Kˣ}

theorem UnitFrame.mem_image (fr : UnitFrame H E hEN K N ζ) (X : Subgroup G)
    (v : UnitRaw.Vfull N) :
    v ∈ fr.image X ↔ ∃ b : ↥E, (b : G) ∈ X ∧ fr.ι (Additive.ofMul b) = v := by
  rw [UnitFrame.image, AddSubgroup.mem_toZModSubmodule, AddSubgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨Additive.toMul b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨Additive.ofMul b, hb, rfl⟩

theorem UnitFrame.image_self_eq_top (fr : UnitFrame H E hEN K N ζ) (h : fr.ι.range = ⊤) :
    fr.image E = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v ∈ fr.ι.range := by
    rw [h]
    exact AddSubgroup.mem_top v
  obtain ⟨b, rfl⟩ := hv
  exact (fr.mem_image E _).mpr ⟨Additive.toMul b, (Additive.toMul b).2, rfl⟩

theorem UnitFrame.image_self_eq_heart (fr : UnitFrame H E hEN K N ζ)
    (h : fr.ι.range = (UnitRaw.heart N).toAddSubgroup) : fr.image E = UnitRaw.heart N := by
  ext v
  rw [fr.mem_image]
  constructor
  · rintro ⟨b, -, rfl⟩
    have hb : fr.ι (Additive.ofMul b) ∈ fr.ι.range := AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [h] at hb
    exact hb
  · intro hv
    have hv' : v ∈ fr.ι.range := by
      rw [h]
      exact hv
    obtain ⟨b, rfl⟩ := hv'
    exact ⟨Additive.toMul b, (Additive.toMul b).2, rfl⟩

@[expose] def UnitFrame.coordFull (fr : UnitFrame H E hEN K N ζ) (h : fr.ι.range = ⊤) :
    Additive ↥E ≃+ UnitRaw.Vfull N :=
  AddEquiv.ofBijective fr.ι ⟨fr.inj, AddMonoidHom.range_eq_top.mp h⟩

theorem UnitFrame.ggLinImage_coordFull (fr : UnitFrame H E hEN K N ζ) (h : fr.ι.range = ⊤)
    (X : Subgroup G) : ggLinImage (p := 3) (fr.coordFull h) X = fr.image X := by
  ext v
  rw [mem_ggLinImage, fr.mem_image]
  constructor
  · intro hv
    exact ⟨Additive.toMul ((fr.coordFull h).symm v), hv, (fr.coordFull h).apply_symm_apply v⟩
  · rintro ⟨b, hb, rfl⟩
    have hb' : (fr.coordFull h).symm (fr.ι (Additive.ofMul b)) = Additive.ofMul b :=
      (fr.coordFull h).symm_apply_apply (Additive.ofMul b)
    rw [hb']
    exact hb

@[expose] def UnitFrame.toHeart (fr : UnitFrame H E hEN K N ζ)
    (h : fr.ι.range = (UnitRaw.heart N).toAddSubgroup) :
    Additive ↥E →+ ↥(UnitRaw.heart N) where
  toFun b := ⟨fr.ι b, by
    have hb : fr.ι b ∈ fr.ι.range := AddMonoidHom.mem_range.mpr ⟨b, rfl⟩
    rw [h] at hb
    exact hb⟩
  map_zero' := Subtype.ext (map_zero fr.ι)
  map_add' a b := Subtype.ext (map_add fr.ι a b)

@[expose] def UnitFrame.coordHeart (fr : UnitFrame H E hEN K N ζ)
    (h : fr.ι.range = (UnitRaw.heart N).toAddSubgroup) : Additive ↥E ≃+ ↥(UnitRaw.heart N) :=
  AddEquiv.ofBijective (fr.toHeart h)
    ⟨fun a b hab => fr.inj (congrArg Subtype.val hab), fun v => by
      have hv : (v : UnitRaw.Vfull N) ∈ fr.ι.range := by
        rw [h]
        exact v.2
      obtain ⟨b, hb⟩ := hv
      exact ⟨b, Subtype.ext hb⟩⟩

theorem UnitFrame.map_ggLinImage_coordHeart (fr : UnitFrame H E hEN K N ζ)
    (h : fr.ι.range = (UnitRaw.heart N).toAddSubgroup) (X : Subgroup G) :
    (ggLinImage (p := 3) (fr.coordHeart h) X).map (UnitRaw.heart N).subtype = fr.image X := by
  ext v
  rw [Submodule.mem_map, fr.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Additive.toMul ((fr.coordHeart h).symm u), (mem_ggLinImage _ X u).mp hu,
      congrArg Subtype.val ((fr.coordHeart h).apply_symm_apply u)⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨fr.coordHeart h (Additive.ofMul b), (ofMul_mem_ggLinImage _ X b).mpr hb, rfl⟩

theorem UnitFrame.ggLinImage_coordHeart (fr : UnitFrame H E hEN K N ζ)
    (h : fr.ι.range = (UnitRaw.heart N).toAddSubgroup) (X : Subgroup G) :
    ggLinImage (p := 3) (fr.coordHeart h) X = (fr.image X).comap (UnitRaw.heart N).subtype := by
  rw [← fr.map_ggLinImage_coordHeart h X,
    Submodule.comap_map_eq_of_injective Subtype.val_injective]

theorem ker_unitDiffMap_le_cent (S : Finset (Fin N)) :
    LinearMap.ker (unitDiffMap N) ≤ UnitRaw.cent S := by
  intro v hv
  have h0 : ∀ i j : Fin N, UnitRaw.diffFun N i j v = 0 := by
    intro i j
    rw [LinearMap.mem_ker, unitDiffMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff] at hv
    exact congrFun hv (i, j)
  obtain ⟨w, rfl⟩ := (UnitRaw.oneLine N).mkQ_surjective v
  refine (UnitRaw.mem_cent_iff S _).mpr ⟨w, rfl, fun i _ j _ => ?_⟩
  have h1 := h0 i j
  rw [UnitRaw.diffFun_mk] at h1
  exact sub_eq_zero.mp h1

variable [Finite G] [Finite K]

omit [Finite G] [Finite K] in
theorem UnitFrame.component_le (fr : UnitFrame H E hEN K N ζ) (S : Finset (Fin N)) :
    fr.component S ≤ H := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.2

@[expose] def unitRealizationCoreFull (hOcc : UnitComponentOccursIff) (hCent : UnitComponentCentEq)
    (hIn : UnitComponentInsideEq) (hMk : UnitComponentMarked) (ctx : UnitCtx H E hEN K N ζ)
    (h : ctx.fr.ι.range = ⊤) : RealizationCore H E (unitFullEntry N) where
  coord := ctx.fr.coordFull h
  component := ctx.fr.component
  innerDiag := ctx.innerDiag
  component_le := fun S _ => ctx.fr.component_le S
  marked := fun S hS => hMk ctx S hS.2
  occurs_iff := fun A hA X => by
    rw [hOcc ctx A hA X]
    show _ ↔ ∃ c : Finset (Fin N), (4 ≤ N ∧ UnitRaw.admissible c) ∧
      UnitRaw.occurs (ggLinImage (p := 3) (ctx.fr.coordFull h) A) c ∧ X = ctx.fr.component c
    rw [ctx.fr.ggLinImage_coordFull h A]
    constructor
    · rintro ⟨S, hS, hocc, rfl⟩
      exact ⟨S, ⟨by have := ctx.hN; omega, hS⟩, hocc, rfl⟩
    · rintro ⟨S, hS, hocc, rfl⟩
      exact ⟨S, hS.2, hocc, rfl⟩
  cent_eq := fun S hS => by
    show ggLinImage (p := 3) (ctx.fr.coordFull h)
      (Subgroup.centralizer (ctx.fr.component S : Set G)) = UnitRaw.cent S
    rw [ctx.fr.ggLinImage_coordFull h, hCent ctx S hS.2, ctx.fr.image_self_eq_top h, inf_top_eq]
  inside_eq := fun S hS => by
    show ggLinImage (p := 3) (ctx.fr.coordFull h) (ctx.fr.component S) = UnitRaw.inside S
    rw [ctx.fr.ggLinImage_coordFull h, hIn ctx S hS.2, ctx.fr.image_self_eq_top h, inf_top_eq]
  root_le_cent := fun S _ => ker_unitDiffMap_le_cent S

@[expose] def unitRealizationCoreHeart (hOcc : UnitComponentOccursIff) (hCent : UnitComponentCentEq)
    (hIn : UnitComponentInsideEq) (hMk : UnitComponentMarked) (ctx : UnitCtx H E hEN K N ζ)
    (h3 : 3 ∣ N) (h : ctx.fr.ι.range = (UnitRaw.heart N).toAddSubgroup) :
    RealizationCore H E (unitHeartEntry N) where
  coord := ctx.fr.coordHeart h
  component := ctx.fr.component
  innerDiag := ctx.innerDiag
  component_le := fun S _ => ctx.fr.component_le S
  marked := fun S hS => hMk ctx S hS.2.2
  occurs_iff := fun A hA X => by
    rw [hOcc ctx A hA X]
    show _ ↔ ∃ c : Finset (Fin N), (4 ≤ N ∧ 3 ∣ N ∧ UnitRaw.admissible c) ∧
      UnitRaw.occursH (ggLinImage (p := 3) (ctx.fr.coordHeart h) A) c ∧ X = ctx.fr.component c
    constructor
    · rintro ⟨S, hS, hocc, rfl⟩
      refine ⟨S, ⟨by have := ctx.hN; omega, h3, hS⟩, ?_, rfl⟩
      show UnitRaw.occurs
        ((ggLinImage (p := 3) (ctx.fr.coordHeart h) A).map (UnitRaw.heart N).subtype) S
      rw [ctx.fr.map_ggLinImage_coordHeart h A]
      exact hocc
    · rintro ⟨S, hS, hocc, rfl⟩
      refine ⟨S, hS.2.2, ?_, rfl⟩
      have hocc' : UnitRaw.occurs
          ((ggLinImage (p := 3) (ctx.fr.coordHeart h) A).map (UnitRaw.heart N).subtype) S := hocc
      rwa [ctx.fr.map_ggLinImage_coordHeart h A] at hocc'
  cent_eq := fun S hS => by
    show ggLinImage (p := 3) (ctx.fr.coordHeart h)
      (Subgroup.centralizer (ctx.fr.component S : Set G)) = UnitRaw.centH S
    rw [ctx.fr.ggLinImage_coordHeart h, hCent ctx S hS.2.2, ctx.fr.image_self_eq_heart h,
      Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
    rfl
  inside_eq := fun S hS => by
    show ggLinImage (p := 3) (ctx.fr.coordHeart h) (ctx.fr.component S) = UnitRaw.insideH S
    rw [ctx.fr.ggLinImage_coordHeart h, hIn ctx S hS.2.2, ctx.fr.image_self_eq_heart h,
      Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
    rfl
  root_le_cent := fun S _ => by
    intro v hv
    have hv' : ((show ↥(UnitRaw.heart N) from v) : UnitRaw.Vfull N) ∈
        LinearMap.ker (unitDiffMap N) := hv
    exact ker_unitDiffMap_le_cent S hv'

omit [Finite G] [Finite K] in
theorem unitCtx_of_pieces (hD : UnitInnerDiagData) (hF : ExistsUnitFrame) (hR : UnitFrameRange)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, N - 1, 1⟩) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 4 ≤ Nat.card E)
    (hrk : 3 ∣ N → 3 ^ (N - 3) ≤ Nat.card E) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (ζ : Multiplicative (ZMod 3) →* Kˣ)
      (hEN : E ≤ Subgroup.normalizer (H : Set G)), Nonempty (UnitCtx H E hEN K N ζ) := by
  obtain ⟨K, _, _, hK, hN4, hHp, θ, hEN, hEI⟩ := hD hInn
  obtain ⟨ζ, hζ, hN, ⟨fr⟩⟩ := hF θ hK hN4 hHp hEab hEN hEI hC3 hcard hrk
  have hrange := hR fr hK hζ hN hSC hC3
  exact ⟨K, inferInstance, inferInstance, ζ, hEN,
    ⟨{ fr := fr, hK := hK, hζ := hζ, hHp := hHp, hEab := hEab, hC3 := hC3, hN := hN,
       innerDiag := hInn, range := hrange }⟩⟩

omit [Finite G] [Finite K] in
theorem unitPlacementCore_of_pieces (hD : UnitInnerDiagData) (hF : ExistsUnitFrame)
    (hR : UnitFrameRange) (hOcc : UnitComponentOccursIff) (hCent : UnitComponentCentEq)
    (hIn : UnitComponentInsideEq) (hMk : UnitComponentMarked)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, N - 1, 1⟩) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 4 ≤ Nat.card E)
    (hrk : 3 ∣ N → 3 ^ (N - 3) ≤ Nat.card E) :
    Nonempty (RealizationCore H E (unitFullEntry N)) ∨
      Nonempty (RealizationCore H E (unitHeartEntry N)) := by
  obtain ⟨K, _, _, ζ, hEN, ⟨ctx⟩⟩ := unitCtx_of_pieces hD hF hR hInn hEab hSC hC3 hcard hrk
  rcases ctx.range with h | ⟨h3, h⟩
  · exact Or.inl ⟨unitRealizationCoreFull hOcc hCent hIn hMk ctx h⟩
  · exact Or.inr ⟨unitRealizationCoreHeart hOcc hCent hIn hMk ctx h3 h⟩

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement
