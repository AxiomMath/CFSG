module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7Frame
public import CFSG.LieType.Chevalley.E7Levi.Equiv

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley.E7Levi CFSG.RankThree.PartOne.KD4T


private theorem symmetrizedCartan_e7Idx {τ : Tag} [hτ : E7Sub τ] (i j : Fin Tag.E7.rank) :
    τ.symmetrizedCartan (e7Idx i) (e7Idx j) = Tag.E7.symmetrizedCartan i j := by
  cases τ
  · exact absurd hτ.rank_ge (by decide)
  · exact absurd hτ.rank_ge (by decide)
  · exact absurd hτ.rank_ge (by decide)
  · exact absurd hτ.rank_ge (by decide)
  · rw [symmetrizedCartan_apply, symmetrizedCartan_apply]
    have hidx : ∀ k : Fin Tag.E7.rank, e7Idx (τ := .E7) k = k := fun k => Fin.ext rfl
    rw [hidx i, hidx j]
  · rw [symmetrizedCartan_apply, symmetrizedCartan_apply]
    simp only [e7Idx]
    rw [hτ.cartan_eq i j]
    simp [Tag.symmetrizer]

private theorem iform_e7Lat {τ : Tag} [E7Sub τ] (δ δ' : Fin Tag.E7.rank → ℤ) :
    CFSG.LieType.Steinberg.Adjoint.iform (e7Lat τ δ) (e7Lat τ δ') =
      CFSG.LieType.Steinberg.Adjoint.iform δ δ' := by
  simp only [CFSG.LieType.Steinberg.Adjoint.iform]
  rw [sum_eq_sum_e7Idx (τ := τ)
    (f := fun i => ∑ j, e7Lat τ δ i * τ.symmetrizedCartan i j * e7Lat τ δ' j)
    (fun i hi => by rw [e7Lat_apply_of_le hi]; simp)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_eq_sum_e7Idx (τ := τ)
    (f := fun j => e7Lat τ δ (e7Idx k) * τ.symmetrizedCartan (e7Idx k) j * e7Lat τ δ' j)
    (fun j hj => by rw [e7Lat_apply_of_le hj]; simp)]
  simp only [e7Lat_apply_e7Idx]
  exact Finset.sum_congr rfl fun l _ => by rw [symmetrizedCartan_e7Idx]

theorem nonempty_rckE7Frame_of_levi {τ : Tag} [E7Sub τ]
    (v : WeylGroup τ) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : Ψ = (fun α => v • α) '' parabolicRoots τ (e7Set τ)) :
    Nonempty (RCKE7Frame Ψ) := by
  haveI : CharP GGL 2 := inferInstance
  have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
  let n : ModGL τ GGL := canonicalRep (coxeterSystem τ) GGL v
  let f : ModGL τ GGL →* ModGL τ GGL := (MulAut.conj n).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj n).injective
  have hn : n ∈ monomialSubgroup τ GGL := canonicalRep_mem_monomialSubgroup GGL v
  have hweyl : weylQuotientHom τ GGL ⟨n, hn⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hmap : (rootSpan τ GGL (parabolicRoots τ (e7Set τ))).map f = rootSpan τ GGL Ψ := by
    change (rootSpan τ GGL (parabolicRoots τ (e7Set τ))).map
      (MulAut.conj n).toMonoidHom = rootSpan τ GGL Ψ
    rw [hΨ, map_conj_rootSpan_of_mem_monomialSubgroup hn (fun γ hγ => hγ.1)]
    rw [show (fun γ => weylQuotientHom τ GGL ⟨n, hn⟩ • γ) = (fun α => v • α) from
      funext fun γ => by rw [hweyl]]
  let ε₁ : ↥(adjointGroup Tag.E7 GGL) ≃* ↥(subsystemGroup τ GGL (e7Set τ)) :=
    (e7LeviGL τ GGL).symm
  let ε₂ : ↥(subsystemGroup τ GGL (e7Set τ)) ≃*
      ↥(rootSpan τ GGL (parabolicRoots τ (e7Set τ))) :=
    MulEquiv.subgroupCongr (subsystemGroup_eq_rootSpan (e7Set τ))
  let ε₃ : ↥(rootSpan τ GGL (parabolicRoots τ (e7Set τ))) ≃* ↥(rootSpan τ GGL Ψ) :=
    (Subgroup.equivMapOfInjective _ f hf).trans (MulEquiv.subgroupCongr hmap)
  let ε : ↥(adjointGroup Tag.E7 GGL) ≃* ↥(rootSpan τ GGL Ψ) := ε₁.trans (ε₂.trans ε₃)
  have ε₃_coe : ∀ y : ↥(rootSpan τ GGL (parabolicRoots τ (e7Set τ))),
      (ε₃ y : ModGL τ GGL) = n * (y : ModGL τ GGL) * n⁻¹ := by
    intro y
    rw [show (ε₃ y : ModGL τ GGL) =
        ((Subgroup.equivMapOfInjective _ f hf y :
          ↥((rootSpan τ GGL (parabolicRoots τ (e7Set τ))).map f)) : ModGL τ GGL) from
      MulEquiv.subgroupCongr_apply hmap _]
    rw [Subgroup.coe_equivMapOfInjective_apply]
    rfl
  have ε₂_coe : ∀ z : ↥(subsystemGroup τ GGL (e7Set τ)),
      (ε₂ z : ModGL τ GGL) = (z : ModGL τ GGL) :=
    fun z => MulEquiv.subgroupCongr_apply _ z
  have ε_coe : ∀ x : ↥(adjointGroup Tag.E7 GGL),
      (ε x : ModGL τ GGL) = n * ((e7LeviGL τ GGL).symm x : ModGL τ GGL) * n⁻¹ := by
    intro x
    show (ε₃ (ε₂ (ε₁ x)) : ModGL τ GGL) =
      n * ((e7LeviGL τ GGL).symm x : ModGL τ GGL) * n⁻¹
    rw [ε₃_coe, ε₂_coe]
  let j : (Fin Tag.E7.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    { toFun := fun δ => v • e7Lat τ δ
      map_zero' := by
        rw [show e7Lat τ (0 : Fin Tag.E7.rank → ℤ) = 0 from by
          funext i
          simp [e7Lat]]
        exact smul_zero v
      map_add' := fun δ δ' => by rw [e7Lat_add, smul_add] }
  let ι : (Fin τ.rank → ℤ) →+ (Fin Tag.E7.rank → ℤ) :=
    { toFun := fun γ k => (v⁻¹ • γ) (e7Idx k)
      map_zero' := by funext k; simp
      map_add' := fun γ γ' => by funext k; simp [smul_add] }
  have hιj : ∀ δ, ι (j δ) = δ := by
    intro δ
    funext k
    show (v⁻¹ • (v • e7Lat τ δ)) (e7Idx k) = δ k
    rw [smul_smul, inv_mul_cancel, one_smul, e7Lat_apply_e7Idx]
  have hjι : ∀ γ ∈ Ψ, j (ι γ) = γ := by
    intro γ hγ
    rw [hΨ] at hγ
    obtain ⟨α, hα, rfl⟩ := hγ
    have hzero : ∀ i : Fin τ.rank, Tag.E7.rank ≤ i.val → (v⁻¹ • (v • α)) i = 0 := by
      intro i hi
      rw [smul_smul, inv_mul_cancel, one_smul]
      exact hα.2 i (by simpa [e7Set] using hi)
    show v • e7Lat τ (fun k => (v⁻¹ • (v • α)) (e7Idx k)) = v • α
    rw [e7Lat_comp_e7Idx hzero, smul_smul, mul_inv_cancel, one_smul]
  have hbij : Set.BijOn j {δ | IsRoot Tag.E7 δ} Ψ := by
    refine ⟨?_, ?_, ?_⟩
    · intro δ hδ
      rw [hΨ]
      exact ⟨e7Lat τ δ, mem_parabolicRoots_e7Set_iff.2
        ⟨δ, ⟨hδ, fun i hi => absurd (Set.mem_univ i) hi⟩, rfl⟩, rfl⟩
    · intro δ _ δ' _ h
      apply e7Lat_injective (τ := τ)
      have := congrArg (fun x => v⁻¹ • x) h
      simpa [j, smul_smul, inv_mul_cancel] using this
    · intro γ hγ
      rw [hΨ] at hγ
      obtain ⟨α, hα, rfl⟩ := hγ
      obtain ⟨δ, hδ, rfl⟩ := mem_parabolicRoots_e7Set_iff.1 hα
      exact ⟨δ, hδ.1, rfl⟩
  have hisRoot : ∀ γ ∈ Ψ, IsRoot τ γ := by
    intro γ hγ
    rw [hΨ] at hγ
    obtain ⟨α, hα, rfl⟩ := hγ
    exact IsRoot.smul hα.1 v
  have hiform : ∀ δ δ', CFSG.LieType.Steinberg.Adjoint.iform (j δ) (j δ') =
      CFSG.LieType.Steinberg.Adjoint.iform δ δ' := by
    intro δ δ'
    show CFSG.LieType.Steinberg.Adjoint.iform (v • e7Lat τ δ) (v • e7Lat τ δ') =
      CFSG.LieType.Steinberg.Adjoint.iform δ δ'
    rw [iform_smul, iform_e7Lat (τ := τ)]
  have hpinned : ∀ δ, IsRoot Tag.E7 δ → ∀ c : GGL,
      (ε ⟨pinnedX Tag.E7 GGL δ c, pinnedX_mem_adjointGroup δ c⟩ : ModGL τ GGL) =
        pinnedX τ GGL (v • e7Lat τ δ) c := by
    intro δ hδ c
    rw [ε_coe, coe_e7LeviGL_symm_pinnedX hδ c]
    simpa [n] using canonicalRep_mul_pinnedX_mul_inv_of_two h2 v (isRoot_e7Lat_iff.2 hδ) c
  exact ⟨ε, j, ι, hιj, hjι, hbij, hisRoot, hiform, hpinned⟩

end CFSG.StandardType.RCKRP

end
