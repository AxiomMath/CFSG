module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4NativeLemmas

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint

theorem rckTriD4PinnedFrame_of_native
    {τ : Tag} [E6Sub τ] {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    (ε : ↥(adjointGroup Tag.D4 GGL) ≃* ↥(subsystemGroup τ GGL (d4Set τ)))
    (hεx : ∀ (k : Fin Tag.D4.rank) (c : GGL),
      (ε ⟨xUnit Tag.D4 GGL k c, xUnit_mem_adjointGroup k c⟩ : ModGL τ GGL) =
        xUnit τ GGL (d4Id k) c)
    (hεy : ∀ (k : Fin Tag.D4.rank) (c : GGL),
      (ε ⟨yUnit Tag.D4 GGL k c, yUnit_mem_adjointGroup k c⟩ : ModGL τ GGL) =
        yUnit τ GGL (d4Id k) c)
    (hsym : ∀ k l : Fin Tag.D4.rank,
      τ.symmetrizedCartan (d4Id k) (d4Id l) = Tag.D4.symmetrizedCartan k l)
    {Ψ : Set (Fin τ.rank → ℤ)} (v : WeylGroup τ)
    (hΨ : Ψ = (fun α => v • α) '' parabolicRoots τ (d4Set τ))
    {h e : ℕ} (he : e = 1 ∨ e = 2) {q N : ModGL τ GGL}
    (hqQ : q ∈ subsystemGroup τ GGL (d4Set τ))
    (hqM : (ε.symm ⟨q, hqQ⟩ : ModGL Tag.D4 GGL) ∈ monomialSubgroup Tag.D4 GGL)
    (hN : N ∈ Subgroup.normalizer (subsystemGroup τ GGL (d4Set τ) : Set (ModGL τ GGL)))
    (hNx : ∀ (k : Fin Tag.D4.rank) (c : GGL),
      N * xUnit τ GGL (d4Id k) c * N⁻¹ = xUnit τ GGL (d4Id (d4Rho^[e] k)) c)
    (hNy : ∀ (k : Fin Tag.D4.rank) (c : GGL),
      N * yUnit τ GGL (d4Id k) c * N⁻¹ = yUnit τ GGL (d4Id (d4Rho^[e] k)) c)
    (hstep : ∀ g ∈ subsystemGroup τ GGL (d4Set τ),
      (canonicalRep (coxeterSystem τ) GGL v)⁻¹ *
          S.D.step (canonicalRep (coxeterSystem τ) GGL v * g *
            (canonicalRep (coxeterSystem τ) GGL v)⁻¹) * canonicalRep (coxeterSystem τ) GGL v =
        q * (N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) g * N⁻¹) * q⁻¹) :
    RCKTriD4PinnedFrame S Ψ h := by
  classical
  set nv := canonicalRep (coxeterSystem τ) GGL v with hnv
  have hspan : rootSpan τ GGL Ψ =
      (subsystemGroup τ GGL (d4Set τ)).map (MulAut.conj nv).toMonoidHom := by
    rw [hΨ]
    exact rootSpan_smul_d4Set v
  have hmemQ : ∀ y ∈ rootSpan τ GGL Ψ, nv⁻¹ * y * nv ∈ subsystemGroup τ GGL (d4Set τ) := by
    intro y hy
    rw [hspan] at hy
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgy
    rw [← hgy]
    rwa [show nv⁻¹ * (nv * g * nv⁻¹) * nv = g by group]
  have hmemΨ : ∀ g ∈ subsystemGroup τ GGL (d4Set τ), nv * g * nv⁻¹ ∈ rootSpan τ GGL Ψ := by
    intro g hg
    rw [hspan]
    exact Subgroup.mem_map.mpr ⟨g, hg, by simp [MulAut.conj_apply]⟩
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : ↥(rootSpan τ GGL Ψ) ≃* ↥(adjointGroup Tag.D4 GGL),
      ∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL Ψ),
        (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) = (ε.symm ⟨nv⁻¹ * y * nv, hmemQ y hy⟩ : ModGL Tag.D4 GGL) := by
    let F : ↥(rootSpan τ GGL Ψ) →* ↥(adjointGroup Tag.D4 GGL) :=
      { toFun := fun y => ε.symm ⟨nv⁻¹ * (y : ModGL τ GGL) * nv, hmemQ y y.2⟩
        map_one' := by
          apply Subtype.ext
          have h1 : (⟨nv⁻¹ * ((1 : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL) * nv,
              hmemQ 1 (one_mem _)⟩ : ↥(subsystemGroup τ GGL (d4Set τ))) = 1 :=
            Subtype.ext (by simp)
          rw [h1, map_one]
        map_mul' := fun y z => by
          apply Subtype.ext
          have h1 : (⟨nv⁻¹ * ((y * z : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL) * nv,
              hmemQ (y * z) (y * z).2⟩ : ↥(subsystemGroup τ GGL (d4Set τ))) =
              ⟨nv⁻¹ * (y : ModGL τ GGL) * nv, hmemQ y y.2⟩ *
                ⟨nv⁻¹ * (z : ModGL τ GGL) * nv, hmemQ z z.2⟩ := by
            ext
            simp only [Subgroup.coe_mul]
            group
          change (ε.symm ⟨nv⁻¹ * ((y * z : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL) * nv,
              hmemQ (y * z) (y * z).2⟩ : ModGL Tag.D4 GGL) =
            (ε.symm ⟨nv⁻¹ * (y : ModGL τ GGL) * nv, hmemQ y y.2⟩ : ModGL Tag.D4 GGL) *
              (ε.symm ⟨nv⁻¹ * (z : ModGL τ GGL) * nv, hmemQ z z.2⟩ : ModGL Tag.D4 GGL)
          rw [h1, map_mul]
          rfl }
    have hFinj : Function.Injective F := by
      intro y z hyz
      apply Subtype.ext
      have h1 : (⟨nv⁻¹ * (y : ModGL τ GGL) * nv, hmemQ y y.2⟩ :
          ↥(subsystemGroup τ GGL (d4Set τ))) =
          ⟨nv⁻¹ * (z : ModGL τ GGL) * nv, hmemQ z z.2⟩ := ε.symm.injective hyz
      have h2 : nv⁻¹ * (y : ModGL τ GGL) * nv = nv⁻¹ * (z : ModGL τ GGL) * nv :=
        Subtype.ext_iff.mp h1
      calc (y : ModGL τ GGL) = nv * (nv⁻¹ * (y : ModGL τ GGL) * nv) * nv⁻¹ := by group
        _ = nv * (nv⁻¹ * (z : ModGL τ GGL) * nv) * nv⁻¹ := by rw [h2]
        _ = (z : ModGL τ GGL) := by group
    have hFsurj : Function.Surjective F := by
      intro z
      refine ⟨⟨nv * ((ε z : ↥(subsystemGroup τ GGL (d4Set τ))) : ModGL τ GGL) * nv⁻¹,
        hmemΨ _ (ε z).2⟩, ?_⟩
      apply Subtype.ext
      have h1 : (⟨nv⁻¹ * (nv *
          ((ε z : ↥(subsystemGroup τ GGL (d4Set τ))) : ModGL τ GGL) * nv⁻¹) * nv,
          hmemQ _ (hmemΨ _ (ε z).2)⟩ : ↥(subsystemGroup τ GGL (d4Set τ))) = ε z := by
        ext
        simp only
        rw [show nv⁻¹ * (nv *
          ((ε z : ↥(subsystemGroup τ GGL (d4Set τ))) : ModGL τ GGL) * nv⁻¹) * nv =
            ((ε z : ↥(subsystemGroup τ GGL (d4Set τ))) : ModGL τ GGL) by group]
      change (ε.symm ⟨nv⁻¹ * (nv *
          ((ε z : ↥(subsystemGroup τ GGL (d4Set τ))) : ModGL τ GGL) * nv⁻¹) * nv,
          hmemQ _ (hmemΨ _ (ε z).2)⟩ : ModGL Tag.D4 GGL) = (z : ModGL Tag.D4 GGL)
      rw [h1, MulEquiv.symm_apply_apply]
    have hFbij : Function.Bijective F := by
      rw [Function.bijective_iff_existsUnique]
      intro b
      obtain ⟨a, ha⟩ := hFsurj b
      exact ⟨a, ha, fun a' ha' => hFinj (ha'.trans ha.symm)⟩
    exact ⟨MulEquiv.ofBijective F hFbij, by
      intro y hy
      rw [MulEquiv.ofBijective_apply]
      rfl⟩
  set ι : (Fin τ.rank → ℤ) →+ (Fin Tag.D4.rank → ℤ) :=
    (d4ResLat τ).comp (DistribSMul.toAddMonoidHom (Fin τ.rank → ℤ) v⁻¹) with hιdef
  have hι : ∀ β, ι (v • β) = d4ResLat τ β := by
    intro β
    show d4ResLat τ (v⁻¹ • (v • β)) = d4ResLat τ β
    rw [inv_smul_smul]
  have hY : ∀ y ∈ rootSpan τ GGL Ψ, S.D.step y ∈ rootSpan τ GGL Ψ := by
    intro y hy
    rw [hspan] at hy ⊢
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    have hstepg := hstep g hg
    have hNF : N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) (g : ModGL τ GGL) * N⁻¹
        ∈ subsystemGroup τ GGL (d4Set τ) := by
      exact (supportedFrobTwistAut (p := 2) (e := h) hN ⟨g, hg⟩).2
    refine Subgroup.mem_map.mpr ⟨q * (N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
      (g : ModGL τ GGL) * N⁻¹) * q⁻¹, ?_, ?_⟩
    · exact mul_mem (mul_mem hqQ hNF) (inv_mem hqQ)
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc nv * (q * (N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
            (g : ModGL τ GGL) * N⁻¹) * q⁻¹) * nv⁻¹
          = nv * (nv⁻¹ * S.D.step (nv * g * nv⁻¹) * nv) * nv⁻¹ := by rw [hstepg]
        _ = S.D.step (nv * g * nv⁻¹) := by group
  refine ⟨e, ε.symm ⟨q, hqQ⟩, he, hqM, (ε.symm ⟨q, hqQ⟩).2, hY, Ξ, ι, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro y hy
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp (hspan ▸ hy)
    subst y
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy ⊢
    have hΞy : (Ξ ⟨nv * g * nv⁻¹, hy⟩ : ModGL Tag.D4 GGL) =
        (ε.symm ⟨g, hg⟩ : ModGL Tag.D4 GGL) := by
      rw [hΞ]
      have harg : (⟨nv⁻¹ * (nv * g * nv⁻¹) * nv, hmemQ _ hy⟩ :
          ↥(subsystemGroup τ GGL (d4Set τ))) = ⟨g, hg⟩ := by
        ext
        simp only
        group
      rw [harg]
    have hNF : N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) (g : ModGL τ GGL) * N⁻¹
        ∈ subsystemGroup τ GGL (d4Set τ) :=
      (supportedFrobTwistAut (p := 2) (e := h) hN ⟨g, hg⟩).2
    have hNFtri : (ε.symm ⟨N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
          (g : ModGL τ GGL) * N⁻¹, hNF⟩ : ModGL Tag.D4 GGL) =
        triPsi h e (ε.symm ⟨g, hg⟩ : ModGL Tag.D4 GGL) :=
      native_symm_frobTwist ε hεx hεy hN hNx hNy ⟨g, hg⟩
    have hstepg := hstep g hg
    calc (Ξ ⟨S.D.step (nv * g * nv⁻¹), hY _ hy⟩ : ModGL Tag.D4 GGL)
        = (ε.symm ⟨nv⁻¹ * S.D.step (nv * g * nv⁻¹) * nv,
            hmemQ (S.D.step (nv * g * nv⁻¹)) (hY _ hy)⟩ :
            ModGL Tag.D4 GGL) := hΞ _ _
      _ = (ε.symm ⟨q * (N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
            (g : ModGL τ GGL) * N⁻¹) * q⁻¹,
            mul_mem (mul_mem hqQ hNF) (inv_mem hqQ)⟩ : ModGL Tag.D4 GGL) := by
          have hsub : (⟨nv⁻¹ * S.D.step (nv * g * nv⁻¹) * nv,
              hmemQ (S.D.step (nv * g * nv⁻¹)) (hY _ hy)⟩ :
              ↥(subsystemGroup τ GGL (d4Set τ))) =
              ⟨q * (N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
                (g : ModGL τ GGL) * N⁻¹) * q⁻¹,
                mul_mem (mul_mem hqQ hNF) (inv_mem hqQ)⟩ := Subtype.ext hstepg
          rw [hsub]
      _ = (ε.symm ⟨q, hqQ⟩ : ModGL Tag.D4 GGL) *
            (ε.symm ⟨N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
              (g : ModGL τ GGL) * N⁻¹, hNF⟩ : ModGL Tag.D4 GGL) *
            (ε.symm ⟨q, hqQ⟩ : ModGL Tag.D4 GGL)⁻¹ := by
          have harg : (⟨q * (N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
                (g : ModGL τ GGL) * N⁻¹) * q⁻¹,
                mul_mem (mul_mem hqQ hNF) (inv_mem hqQ)⟩ :
                ↥(subsystemGroup τ GGL (d4Set τ))) =
              ⟨q, hqQ⟩ * ⟨N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
                (g : ModGL τ GGL) * N⁻¹, hNF⟩ * ⟨q, hqQ⟩⁻¹ := by
            ext
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [harg, map_mul, map_mul, map_inv]
          rfl
      _ = (ε.symm ⟨q, hqQ⟩ : ModGL Tag.D4 GGL) *
            triPsi h e (Ξ ⟨nv * g * nv⁻¹, hy⟩ : ModGL Tag.D4 GGL) *
            (ε.symm ⟨q, hqQ⟩ : ModGL Tag.D4 GGL)⁻¹ := by
          rw [hNFtri, hΞy]
  ·
    have hbij := bijOn_d4ResLat (τ := τ)
    refine Set.BijOn.mk ?_ ?_ ?_
    · intro γ hγ
      rw [hΨ] at hγ
      obtain ⟨β, hβ, rfl⟩ := hγ
      rw [hι]
      exact hbij.mapsTo hβ
    · intro γ hγ δ hδ hγδ
      rw [hΨ] at hγ hδ
      obtain ⟨β, hβ, rfl⟩ := hγ
      obtain ⟨β', hβ', rfl⟩ := hδ
      rw [hι, hι] at hγδ
      rw [hbij.injOn hβ hβ' hγδ]
    · intro δ hδ
      obtain ⟨β, hβ, hβδ⟩ := hbij.surjOn hδ
      exact ⟨v • β, by rw [hΨ]; exact ⟨β, hβ, rfl⟩, by rw [hι, hβδ]⟩
  ·
    intro γ hγ δ hδ
    rw [hΨ] at hγ hδ
    obtain ⟨β, hβ, rfl⟩ := hγ
    obtain ⟨β', hβ', rfl⟩ := hδ
    rw [hι, hι, iform_d4ResLat hsym hβ hβ', iform_smul]
  ·
    intro γ hγ y hy
    rw [hΨ] at hγ
    obtain ⟨β, hβ, rfl⟩ := hγ
    rw [hι]
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp (hspan ▸ hy)
    subst y
    have hΞg : (Ξ ⟨(MulEquiv.toMonoidHom (MulAut.conj nv)) g, hy⟩ : ModGL Tag.D4 GGL) =
        ε.symm ⟨g, hg⟩ := by
      rw [hΞ]
      have harg : (⟨nv⁻¹ * ((MulEquiv.toMonoidHom (MulAut.conj nv)) g) * nv,
          hmemQ ((MulEquiv.toMonoidHom (MulAut.conj nv)) g) hy⟩ :
          ↥(subsystemGroup τ GGL (d4Set τ))) = ⟨g, hg⟩ := by
        apply Subtype.ext
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [harg]
    rw [hΞg]
    have hmap := (canonical_weyl_root_transport τ GGL).2.1 v β hβ.1
    rw [← hnv] at hmap
    have hmem : (MulEquiv.toMonoidHom (MulAut.conj nv)) g ∈ rootSubgroup τ GGL (v • β) ↔
        g ∈ rootSubgroup τ GGL β := by
      rw [← hmap]
      constructor
      · intro h
        obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp h
        have hu_eq : u = g := (MulAut.conj nv).injective huy
        exact hu_eq ▸ hu
      · intro hgβ
        exact Subgroup.mem_map.mpr ⟨g, hgβ, rfl⟩
    rw [hmem]
    exact native_mem_rootSubgroup_iff ε hεx hεy hβ ⟨g, hg⟩
  ·
    intro b hb
    have hnvNorm : nv ∈ Subgroup.normalizer (torusGroup τ GGL : Set (ModGL τ GGL)) :=
      (canonical_weyl_root_transport τ GGL).2.2 v
    have hb' : nv⁻¹ * b * nv ∈ torusGroup τ GGL := by
      refine (Subgroup.mem_normalizer_iff.mp hnvNorm (nv⁻¹ * b * nv)).mpr ?_
      rw [show nv * (nv⁻¹ * b * nv) * nv⁻¹ = b by group]
      exact hb
    obtain ⟨t, ht, hconj, hval⟩ := exists_native_torus ε hεx hεy hb'
    refine ⟨t, ht, ?_, ?_⟩
    · intro y hy hby
      obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp (hspan ▸ hy)
      subst y
      have hΞg : (Ξ ⟨(MulEquiv.toMonoidHom (MulAut.conj nv)) g, hy⟩ : ModGL Tag.D4 GGL) =
          ε.symm ⟨g, hg⟩ := by
        rw [hΞ]
        have harg : (⟨nv⁻¹ * ((MulEquiv.toMonoidHom (MulAut.conj nv)) g) * nv,
            hmemQ ((MulEquiv.toMonoidHom (MulAut.conj nv)) g) hy⟩ :
            ↥(subsystemGroup τ GGL (d4Set τ))) = ⟨g, hg⟩ := by
          apply Subtype.ext
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [harg]
      have hb'g : nv⁻¹ * b * nv * g * (nv⁻¹ * b * nv)⁻¹ ∈ subsystemGroup τ GGL (d4Set τ) := by
        have h : nv⁻¹ * (b * ((MulEquiv.toMonoidHom (MulAut.conj nv)) g) * b⁻¹) * nv ∈
            subsystemGroup τ GGL (d4Set τ) := hmemQ _ hby
        rwa [show nv⁻¹ * (b * ((MulEquiv.toMonoidHom (MulAut.conj nv)) g) * b⁻¹) * nv =
            nv⁻¹ * b * nv * g * (nv⁻¹ * b * nv)⁻¹ by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group] at h
      have hL : (Ξ ⟨b * ((MulEquiv.toMonoidHom (MulAut.conj nv)) g) * b⁻¹, hby⟩ :
            ModGL Tag.D4 GGL) =
          ε.symm ⟨nv⁻¹ * b * nv * g * (nv⁻¹ * b * nv)⁻¹, hb'g⟩ := by
        rw [hΞ]
        congr 1
      rw [hL, hΞg, hconj ⟨g, hg⟩ hb'g]
    · intro γ hγ
      rw [hΨ] at hγ
      obtain ⟨β, hβ, rfl⟩ := hγ
      rw [hι, hval β hβ]
      exact rckRootVal_conj_canonicalRep hb v hβ.1

end CFSG.StandardType.RCKRP

end
