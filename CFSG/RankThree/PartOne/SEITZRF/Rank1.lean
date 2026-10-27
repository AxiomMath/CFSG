module

public import CFSG.RankThree.PartOne.SEITZRF.Defs
public import CFSG.RankThree.PartOne.CTP.SeitzMaxLinear
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i)

open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

open CFSG.SectionRank.LargeRee (blockMat vLabel r2 r2EquivSuzuki)

open CFSG.LieType.Steinberg.Adjoint (endHom endHom_apply)

open CFSG.RankThree.PartOne.CTP (slSub mem_slSub fixedSubgroup mem_fixedSubgroup)

section Generators

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem sylowB_mem_rankOneGroupTwo (hK : Nat.card K = 2 ^ (2 * a + 1)) (b c : K) :
    sylowB a K b c ∈ rankOneGroupTwo K a :=
  Subgroup.subset_closure (Or.inl (Or.inl (sylowB_mem_U2 hK b c)))

theorem torusTwo_mem_rankOneGroupTwo (u : Kˣ) :
    pairedTorusHom a (f4i 1) (f4i 2) u ∈ rankOneGroupTwo K a :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨u, rfl⟩))

end Generators

section Torus

variable {K : Type} [Field K] {a : ℕ}

theorem units_map_entrywiseHom_pairedTorusHom (β : K ≃+* K) (j k : Fin F4.tag.rank) (u : Kˣ) :
    Units.map (entrywiseHom (τ := F4.tag) β.toRingHom) (pairedTorusHom a j k u) =
      pairedTorusHom a j k (Units.map β.toRingHom.toMonoidHom u) := by
  rw [pairedTorusHom_apply, pairedTorusHom_apply, map_mul, entrywise_torusElt, entrywise_torusElt,
    map_pow]

end Torus

section One

variable {K : Type} [Field K] {a : ℕ}

theorem units_map_entrywiseHom_largeReeRankOne (β : K ≃+* K) (i : Fin F4.tag.rank) (g : SL2 K) :
    Units.map (entrywiseHom (τ := F4.tag) β.toRingHom) (largeReeRankOne K i g) =
      largeReeRankOne K i (Matrix.SpecialLinearGroup.map β.toRingHom g) := by
  have h := SL2_hom_ext
    (φ := (Units.map (entrywiseHom (τ := F4.tag) β.toRingHom)).comp (largeReeRankOne K i))
    (ψ := (largeReeRankOne K i).comp (Matrix.SpecialLinearGroup.map β.toRingHom))
    (fun s => ?_) (fun u => ?_) ?_
  · exact DFunLike.congr_fun h g
  · simp only [MonoidHom.comp_apply, largeReeRankOne_uSL, map_uSL, units_map_entrywiseHom_xUnit]
  · simp only [MonoidHom.comp_apply, largeReeRankOne_HSL, map_HSL, entrywise_torusElt]
  · simp only [MonoidHom.comp_apply, largeReeRankOne_WSL, map_WSL, entrywise_weylElt_one]

variable [CharP K F4.prime]

theorem map_map_largeReeRhoHom (β : K ≃+* K) (g : SL2 K) :
    Matrix.SpecialLinearGroup.map β.toRingHom
        (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) g) =
      Matrix.SpecialLinearGroup.map (largeReeRhoHom K a)
        (Matrix.SpecialLinearGroup.map β.toRingHom g) := by
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, largeReeRhoHom_apply, map_pow]

theorem units_map_entrywiseHom_largeReeA1Hom (β : K ≃+* K) (g : SL2 K) :
    Units.map (entrywiseHom (τ := F4.tag) β.toRingHom) (largeReeA1Hom K a g) =
      largeReeA1Hom K a (Matrix.SpecialLinearGroup.map β.toRingHom g) := by
  rw [largeReeA1Hom_apply, largeReeA1Hom_apply, map_mul, units_map_entrywiseHom_largeReeRankOne,
    units_map_entrywiseHom_largeReeRankOne, map_map_largeReeRhoHom]

theorem largeReeA1Hom_mem_fixGL_iff (β : K ≃+* K) (g : SL2 K) :
    largeReeA1Hom K a g ∈ fixGL K β ↔ g ∈ slSub 2 (fixSubfield β) := by
  rw [mem_fixGL, units_map_entrywiseHom_largeReeA1Hom, largeReeA1Hom_injective.eq_iff,
    mem_slSub]
  constructor
  · intro h i j
    have := congrArg (fun x : SL2 K => (x : Matrix (Fin 2) (Fin 2) K) i j) h
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, mem_fixSubfield] using this
  · intro h
    ext i j
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, mem_fixSubfield] using h i j

end One

section Overgroup

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem eq_rankOneGroupOne_of_not_le (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    (hmax : ∀ M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K),
      slSub 2 (fixSubfield β) ≤ M → ¬ M ≤ slSub 2 (fixSubfield β) → M = ⊤)
    {Y : Subgroup (ModGL F4.tag K)} (hY : Y ≤ rankOneGroupOne K a)
    (hRY : rankOneGroupOne K a ⊓ Rf K a β ≤ Y) (hne : ¬ Y ≤ Rf K a β) :
    Y = rankOneGroupOne K a := by
  have hrange : rankOneGroupOne K a = (largeReeA1Hom K a).range := rankOneGroupOne_eq_range hK
  have hΓ : ∀ g : SL2 K, largeReeA1Hom K a g ∈ F4.reeGamma K a := fun g =>
    rankOneGroupOne_le_reeGamma hK (hrange ▸ ⟨g, rfl⟩)
  have hM := hmax (Y.comap (largeReeA1Hom K a))
    (fun g hg => by
      refine hRY ⟨?_, hΓ g, (largeReeA1Hom_mem_fixGL_iff β g).2 hg⟩
      exact hrange ▸ ⟨g, rfl⟩)
    (fun hle => by
      obtain ⟨y, hyY, hyR⟩ := Set.not_subset.1 hne
      obtain ⟨g, rfl⟩ : y ∈ (largeReeA1Hom K a).range := hrange ▸ hY hyY
      exact hyR ⟨hΓ g, (largeReeA1Hom_mem_fixGL_iff β g).2 (hle hyY)⟩)
  refine le_antisymm hY ?_
  rw [hrange]
  rintro _ ⟨g, rfl⟩
  have : g ∈ Y.comap (largeReeA1Hom K a) := by rw [hM]; exact Subgroup.mem_top g
  exact this

end Overgroup

section Two

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem units_map_entrywiseHom_mem_rankOneGroupTwo (β : K ≃+* K) {x : ModGL F4.tag K}
    (hx : x ∈ rankOneGroupTwo K a) :
    Units.map (entrywiseHom (τ := F4.tag) β.toRingHom) x ∈ rankOneGroupTwo K a := by
  have hle : rankOneGroupTwo K a ≤
      (rankOneGroupTwo K a).comap (Units.map (entrywiseHom (τ := F4.tag) β.toRingHom)) := by
    rw [rankOneGroupTwo, Subgroup.closure_le]
    rintro g ((hg | ⟨u, rfl⟩) | rfl)
    · exact Subgroup.subset_closure (Or.inl (Or.inl
        ⟨entrywise_mem_rootSpan (σ := β) hg.1, exactEntrywiseAut_mem_reeGamma β hg.2⟩))
    · rw [SetLike.mem_coe, Subgroup.mem_comap, units_map_entrywiseHom_pairedTorusHom]
      exact torusTwo_mem_rankOneGroupTwo _
    · rw [SetLike.mem_coe, Subgroup.mem_comap, entrywise_canonicalRep]
      exact Subgroup.subset_closure (Or.inr rfl)
  exact hle hx

omit [Finite K] [CharP K F4.prime] in
theorem blockMat_entrywise {τ : Tag} {n : ℕ} (ℓ : Fin n → Label τ) (σ : K →+* K)
    (A : Module.End K (RootModule τ K)) :
    blockMat ℓ (entrywise σ A) = (blockMat ℓ A).map σ := by
  ext i j
  simp [blockMat, entrywise_single]

theorem coe_rankOneEquivSuzuki (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (r : rankOneGroupTwo K a) :
    (((rankOneEquivSuzuki K a ha hK r : suzukiGroup a K) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) =
      blockMat vLabel ((r : ModGL F4.tag K) : Module.End K (RootModule F4.tag K)) := by
  have hK' : Nat.card K = F4.prime ^ (2 * a + 1) := hK
  have hr : (r : ModGL F4.tag K) ∈ (r2 K a hK').map (reeFixedEmb K a) := by
    rw [← rankOneGroupTwo_eq_map hK']
    exact r.2
  obtain ⟨x, hx, hxr⟩ := hr
  have h1 : (Subgroup.equivMapOfInjective (r2 K a hK') (reeFixedEmb K a)
      reeFixedEmb_injective) ⟨x, hx⟩ =
        MulEquiv.subgroupCongr (rankOneGroupTwo_eq_map hK') r := Subtype.ext hxr
  have h2 : rankOneEquivSuzuki K a ha hK r = r2EquivSuzuki K a hK' ha ⟨x, hx⟩ := by
    rw [rankOneEquivSuzuki, MulEquiv.trans_apply, MulEquiv.trans_apply, ← h1,
      MulEquiv.symm_apply_apply]
  rw [h2, CFSG.SectionRank.LargeRee.coe_r2EquivSuzuki, CFSG.SectionRank.LargeRee.coe_r2Rep]
  change blockMat vLabel (endHom K (x : adjointGroup F4.tag K)) = _
  rw [endHom_apply]
  exact congrArg
    (fun y : ModGL F4.tag K => blockMat vLabel (y : Module.End K (RootModule F4.tag K))) hxr

theorem coe_szFieldAut_rankOneEquivSuzuki (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) (r : rankOneGroupTwo K a) :
    (((szFieldAut a K β (rankOneEquivSuzuki K a ha hK r) : suzukiGroup a K) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) =
      blockMat vLabel
        ((Units.map (entrywiseHom (τ := F4.tag) β.toRingHom) (r : ModGL F4.tag K) :
          ModGL F4.tag K) : Module.End K (RootModule F4.tag K)) := by
  rw [CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.coe_szFieldAut, coe_rankOneEquivSuzuki]
  exact (blockMat_entrywise vLabel β.toRingHom _).symm

theorem rankOneEquivSuzuki_mem_fixedSubgroup_iff (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) (r : rankOneGroupTwo K a) :
    rankOneEquivSuzuki K a ha hK r ∈ fixedSubgroup (szFieldAut a K β) ↔
      (r : ModGL F4.tag K) ∈ fixGL K β := by
  rw [mem_fixedSubgroup, mem_fixGL]
  constructor
  · intro h
    have himg : rankOneEquivSuzuki K a ha hK
        ⟨_, units_map_entrywiseHom_mem_rankOneGroupTwo β r.2⟩ =
          rankOneEquivSuzuki K a ha hK r := by
      refine Subtype.ext (Units.ext ?_)
      rw [← h, coe_szFieldAut_rankOneEquivSuzuki, coe_rankOneEquivSuzuki]
    exact congrArg Subtype.val ((rankOneEquivSuzuki K a ha hK).injective himg)
  · intro h
    refine Subtype.ext (Units.ext ?_)
    rw [coe_szFieldAut_rankOneEquivSuzuki, h, coe_rankOneEquivSuzuki]

theorem eq_rankOneGroupTwo_of_not_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K)
    (hmax : ∀ M : Subgroup (suzukiGroup a K),
      fixedSubgroup (szFieldAut a K β) ≤ M → ¬ M ≤ fixedSubgroup (szFieldAut a K β) → M = ⊤)
    {Y : Subgroup (ModGL F4.tag K)} (hY : Y ≤ rankOneGroupTwo K a)
    (hRY : rankOneGroupTwo K a ⊓ Rf K a β ≤ Y) (hne : ¬ Y ≤ Rf K a β) :
    Y = rankOneGroupTwo K a := by
  have hΓ : ∀ r : rankOneGroupTwo K a, (r : ModGL F4.tag K) ∈ F4.reeGamma K a := fun r =>
    rankOneGroupTwo_le_reeGamma hK r.2
  set E := rankOneEquivSuzuki K a ha hK
  have hMmem : ∀ r : rankOneGroupTwo K a,
      E r ∈ Y.comap ((rankOneGroupTwo K a).subtype.comp E.symm.toMonoidHom) ↔
        (r : ModGL F4.tag K) ∈ Y := fun r => by
    simp
  have hM := hmax (Y.comap ((rankOneGroupTwo K a).subtype.comp E.symm.toMonoidHom))
    (fun s hs => by
      obtain ⟨r, rfl⟩ := E.surjective s
      rw [hMmem]
      exact hRY ⟨r.2, hΓ r, (rankOneEquivSuzuki_mem_fixedSubgroup_iff ha hK β r).1 hs⟩)
    (fun hle => by
      obtain ⟨y, hyY, hyR⟩ := Set.not_subset.1 hne
      have hyR2 : y ∈ rankOneGroupTwo K a := hY hyY
      have h1 := hle ((hMmem ⟨y, hyR2⟩).2 hyY)
      exact hyR ⟨hΓ ⟨y, hyR2⟩, (rankOneEquivSuzuki_mem_fixedSubgroup_iff ha hK β ⟨y, hyR2⟩).1 h1⟩)
  refine le_antisymm hY (fun y hy => ?_)
  have : E ⟨y, hy⟩ ∈ Y.comap ((rankOneGroupTwo K a).subtype.comp E.symm.toMonoidHom) := by
    rw [hM]
    exact Subgroup.mem_top _
  exact (hMmem ⟨y, hy⟩).1 this

end Two

end CFSG.RankThree.PartOne.SEITZRF
