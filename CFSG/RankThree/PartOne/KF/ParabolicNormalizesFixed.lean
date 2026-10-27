module

public import CFSG.RankThree.PartOne.KF.ParabolicNormalizes
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits

section Parabolic

theorem exists_hom_into_graphFixedParabolic_of_normalizes (t : TwistTag) {K : Type} [Field K]
    [Finite K] [CharP K 2] (σ : K ≃+* K) (hH : Holds (graphFixedRootGroup t K σ.toRingHom) 2)
    {U E : Subgroup (graphFixedRootGroup t K σ.toRingHom)} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hE : E ≤ Subgroup.normalizer (U : Set (graphFixedRootGroup t K σ.toRingHom))) :
    ∃ (J : Set (Fin t.foldedTag.rank)) (φ : E →* ModGL t.tag K), J ≠ Set.univ ∧
      Function.Injective φ ∧ ∀ e, φ e ∈ graphFixedParabolic t K σ.toRingHom J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (ModGL t.tag K) := finite_modGL
  have hUC : graphFixedPosUnipotent t K σ.toRingHom ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom
  have hBC : graphFixedRootBorel t K σ.toRingHom ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedRootBorel_le t K σ.toRingHom
  obtain ⟨S, P, hPtop, hNU, -, -, hNS⟩ := hH U hU hU2
  have hUp := isPGroup_graphFixedPosUnipotent_subgroupOf 2 (t := t) (K := K) (σ := σ.toRingHom)
  have hUi := not_dvd_index_graphFixedPosUnipotent 2 (t := t) (K := K) (σ := σ.toRingHom)
    σ.surjective
  have hUc := IsPGroup.toSylow_coe hUp hUi
  have hBN : (graphFixedRootBorel t K σ.toRingHom).subgroupOf
      (graphFixedRootGroup t K σ.toRingHom) ≤ Subgroup.normalizer
        (((graphFixedPosUnipotent t K σ.toRingHom).subgroupOf
          (graphFixedRootGroup t K σ.toRingHom) : Subgroup (graphFixedRootGroup t K σ.toRingHom)) :
            Set (graphFixedRootGroup t K σ.toRingHom)) := by
    intro b hb
    have hb' : (b : ModGL t.tag K) ∈ graphFixedRootBorel t K σ.toRingHom := hb
    have : b ∈ (Subgroup.normalizer
        (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K))).subgroupOf
          (graphFixedRootGroup t K σ.toRingHom) :=
      graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent hb'
    rwa [Subgroup.subgroupOf_normalizer_eq hUC] at this
  obtain ⟨g, hg⟩ := exists_conj_le_of_normalizes (hUp.toSylow hUi) S
    ((graphFixedRootBorel t K σ.toRingHom).subgroupOf (graphFixedRootGroup t K σ.toRingHom)) P
    (by rw [hUc]; exact hBN) hNS
  have hP₁top : P.comap (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) ∈ P :=
      Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top _)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  set A : Subgroup (ModGL t.tag K) :=
    (P.comap (MulAut.conj g).toMonoidHom).map (graphFixedRootGroup t K σ.toRingHom).subtype
    with hA
  have hBA : graphFixedRootBorel t K σ.toRingHom ≤ A := fun b hb =>
    ⟨⟨b, hBC hb⟩, hg (show (⟨b, hBC hb⟩ : graphFixedRootGroup t K σ.toRingHom) ∈
      (graphFixedRootBorel t K σ.toRingHom).subgroupOf (graphFixedRootGroup t K σ.toRingHom) from
        hb), rfl⟩
  have hAC : A ≤ graphFixedRootGroup t K σ.toRingHom := Subgroup.map_subtype_le _
  obtain ⟨hAJ, -⟩ := fixed_Borel_overgroup_classification t K σ A hBA hAC
  have hE₁P : ∀ e : E, (MulAut.conj g⁻¹).toMonoidHom e ∈ P.comap (MulAut.conj g).toMonoidHom :=
    fun e => by
      rw [Subgroup.mem_comap]
      have h1 : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom
          (e : graphFixedRootGroup t K σ.toRingHom)) =
            (e : graphFixedRootGroup t K σ.toRingHom) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      rw [h1]
      exact hNU (hE e.2)
  refine ⟨{a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ A},
    ((graphFixedRootGroup t K σ.toRingHom).subtype.comp (MulAut.conj g⁻¹).toMonoidHom).comp
      E.subtype, fun huniv => hP₁top ?_,
    (graphFixedRootGroup t K σ.toRingHom).subtype_injective.comp
      ((MulAut.conj g⁻¹).injective.comp E.subtype_injective), fun e => ?_⟩
  · rw [eq_top_iff]
    intro y _
    have hy : (y : ModGL t.tag K) ∈ A := by
      rw [hAJ, huniv, (fixed_standard_parabolic_cells t K σ).2.2.2.2.2]
      exact y.2
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := Subtype.ext hyy
    rwa [← this]
  · rw [← hAJ]
    exact ⟨_, hE₁P e, rfl⟩

end Parabolic

end CFSG.RankThree.PartOne.KFU
