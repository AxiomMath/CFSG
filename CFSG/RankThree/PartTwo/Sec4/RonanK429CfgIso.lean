module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts

variable {S T : Type} [Group S] [Group T]

theorem map_subgroupOf_equivMap (e : S ≃* T) (K F : Subgroup S) :
    (K.subgroupOf F).map (F.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
      (K.map e.toMonoidHom).subgroupOf (F.map e.toMonoidHom) := by
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨x, hx, ?_⟩
    exact congrArg Subtype.val hxy
  · intro h
    rw [Subgroup.mem_subgroupOf] at h
    obtain ⟨k, hk, hky⟩ := h
    obtain ⟨f, hf, hfy⟩ := hy
    have hkf : k = f := e.injective (by simpa using hky.trans hfy.symm)
    subst hkf
    exact ⟨⟨k, hf⟩, hk, Subtype.ext hky⟩

theorem CfgS429.map [Finite S] [Finite T] {A : Subgroup (MulAut S)} {σ : MulAut S}
    {K : Subgroup S} (h : CfgS429 S A σ K) (e : S ≃* T) :
    CfgS429 T (A.map (MulAut.congr e).toMonoidHom) (MulAut.congr e σ) (K.map e.toMonoidHom) := by
  have hfix := autFix_congr e σ
  refine
    { isE27 := h.isE27.map (MulAut.congr e)
      mem := Subgroup.mem_map_of_mem _ h.mem
      ne_one := fun h1 => h.ne_one ((MulAut.congr e).injective (by rw [h1, map_one]))
      le_autFix := by rw [hfix]; exact Subgroup.map_mono h.le_autFix
      isSubnormal := ?_
      isPerfect := ?_
      map_mem := ?_
      isType := ?_
      faithful := ?_ }
  · rw [hfix, ← map_subgroupOf_equivMap]
    exact h.isSubnormal.map (MulEquiv.surjective _)
  · haveI := h.isPerfect
    exact Group.IsPerfect.map _
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨k, hk, rfl⟩
    refine ⟨a k, h.map_mem a ha k hk, ?_⟩
    change e (a k) = e (a (e.symm (e k)))
    rw [MulEquiv.symm_apply_apply]
  · exact isType429_of_mulEquiv
      (quotPCoreTwoCongr (K.equivMapOfInjective e.toMonoidHom e.injective)).symm h.isType
  · rintro _ ⟨a, ha, rfl⟩ hK
    have hinj : Function.Injective (e.toMonoidHom.comp K.subtype) :=
      e.injective.comp K.subtype_injective
    have ha' : a ∈ Subgroup.zpowers σ := by
      refine h.faithful a ha fun k hk => ?_
      have h1 := hK (e k) ⟨k, hk, rfl⟩
      have h2 : ((MulAut.congr e).toMonoidHom a) (e k) * (e k)⁻¹ =
          e.toMonoidHom (a k * k⁻¹) := by
        change e (a (e.symm (e k))) * (e k)⁻¹ = e (a k * k⁻¹)
        rw [MulEquiv.symm_apply_apply, map_mul, map_inv]
      rw [h2] at h1
      exact (map_mem_pCoreOf_map_iff 2 e.toMonoidHom hinj
        (Subgroup.mul_mem _ (h.map_mem a ha k hk) (Subgroup.inv_mem _ hk))).mp h1
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    change (MulAut.congr e).toMonoidHom (σ ^ m) ∈ _
    rw [map_zpow]
    exact Subgroup.zpow_mem_zpowers _ m

theorem IsFieldAutL3.of_congr (e : S ≃* T) {σ : MulAut S} (h : IsFieldAutL3 (MulAut.congr e σ)) :
    IsFieldAutL3 σ := by
  rcases h with ⟨F, _, _, e', he'⟩ | ⟨p, f, F, _, hF, hq, e', he'⟩
  · exact Or.inl ⟨F, inferInstance, inferInstance, e.trans e', by rwa [congr_trans]⟩
  · exact Or.inr ⟨p, f, F, inferInstance, hF, hq, e.trans e', by rwa [congr_trans]⟩

theorem ConclS429.of_map [Finite S] [Finite T] {σ : MulAut S} {K : Subgroup S} (e : S ≃* T)
    (h : ConclS429 T (MulAut.congr e σ) (K.map e.toMonoidHom)) : ConclS429 S σ K := by
  obtain ⟨hO, hs⟩ := h
  have eK : K ≃* K.map e.toMonoidHom := K.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨?_, ?_⟩
  · have hc := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (autFixCongrEquiv e σ)
    rw [hO, Subgroup.map_bot] at hc
    exact hc.symm
  · rcases hs with (⟨⟨φ⟩, ⟨ψ⟩⟩ | ⟨n, hn, hKn, hD4, hout⟩) | ⟨n, hn, hKn, hSn, hfield⟩
    · exact Or.inl (Or.inl ⟨⟨eK.trans φ⟩, ⟨e.trans ψ⟩⟩)
    · exact Or.inl (Or.inr ⟨n, hn, isoLThreePi_of_mulEquiv eK hKn,
        CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hD4,
        fun hin => hout ((isInnerAut_congr e σ).mpr hin)⟩)
    · exact Or.inr ⟨n, hn, isoLThreePi_of_mulEquiv eK hKn, isoLThreePi_of_mulEquiv e hSn,
        IsFieldAutL3.of_congr e hfield⟩

theorem RowS429.of_mulEquiv [Finite S] [Finite T] (e : S ≃* T) (h : RowS429 T) : RowS429 S :=
  fun _ _ _ hc => ConclS429.of_map e (h _ _ _ (hc.map e))

theorem NoCfgS429.of_mulEquiv [Finite S] [Finite T] (e : S ≃* T) (h : NoCfgS429 T) :
    NoCfgS429 S :=
  fun _ _ _ hc => h _ _ _ (hc.map e)

theorem rowSOf429_of_rowS429 {X : Type} [Group X] [Finite X] (h : RowS429 X) : RowSOf429 X :=
  fun _ _ _ _ _ ⟨e⟩ => h.of_mulEquiv e

theorem rowSOf429_of_noCfgS429 {X : Type} [Group X] [Finite X] (h : NoCfgS429 X) :
    RowSOf429 X :=
  rowSOf429_of_rowS429 h.rowS429

end CFSG.RankThree.PartTwo.Sec4.RonanK429
