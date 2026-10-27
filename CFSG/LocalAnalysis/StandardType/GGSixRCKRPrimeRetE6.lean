module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetCover
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetComp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetDiagE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePinnedTransfer
import CFSG.LocalAnalysis.StandardType.ExcPos.OrdinaryNeighbourPinned

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld CFSG.LieType.Steinberg.Minuscule
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups commutatorElement

theorem rckRet_iota_L {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {γ' : Fin Tag.E6.rank → ℤ} (hγ' : IsRoot Tag.E6 γ') :
    (∑ j : Fin 6, γ' j • β j) ∈ rootsOfFam β Set.univ ∧
      ι (∑ j : Fin 6, γ' j • β j) = γ' := by
  obtain ⟨γ, hγ, rfl⟩ := hι.1.surjOn hγ'
  have h := hι.2.2.1 γ hγ
  rw [h]
  exact ⟨hγ, rfl⟩

theorem rckRetE6_holds
    : RCKRetE6 := by
  intro τ S a hT p hp hp2 hTp i h hq hquasi hshape
  classical
  obtain ⟨hkind, h6, hn⟩ := hshape
  have hτ := rckA4_tag h6
  have hinner := rckA4_twistInner hkind h6 hn
  have hpL := rckA4_cast_ne_zero hp hp2
  have hτsl : SimplyLacedTag τ := by
    rcases hτ with h' | h' | h' <;> simp [SimplyLacedTag, h']
  obtain ⟨β, hβroot, hΨβ, hnon, hedge, -⟩ := rckE6_labelled hτ S hp hpL hTp i h6 hn
  have hrank : τ.rank < 2 * compRank (componentRoots (rootCharHom a) i) := by
    rw [h6]
    rcases hτ with rfl | rfl | rfl <;> simp [Tag.rank]
  have himg := rckRet_orbit_one S hT i hrank
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := fun γ hγ =>
    himg ▸ Set.mem_image_of_mem _ hγ
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfin hstab
  obtain ⟨ι, hι⟩ := rckRet_iota hτ hβroot hnon hedge
  obtain ⟨θ, hθ⟩ := rckE6_comparison hτ hβroot hι
  obtain ⟨σ, hσc, hfinσ, hcard, f, hf1, hf2, hf3, hz⟩ := rckInnerCoverExplicit S hT i hinner
  obtain ⟨z, hzadj, hzs, hfz, hzZ, -⟩ := hz hs1
  have hinner1 : twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin τ.rank → ℤ) → _) := by
    have h0 := hinner
    rw [hs1, Function.iterate_one] at h0
    exact h0
  obtain ⟨w, hwcl, hwγ⟩ := hinner1
  have hwcl' : w ∈ Subgroup.closure {s : WeylGroup τ |
      ∃ γ ∈ rootsOfFam β Set.univ, s = rootReflection γ} := by
    rw [← hΨβ]; exact hwcl
  obtain ⟨w', hw'⟩ := rckRet_weyl_transport hι hwcl'
  have hρΨ : ∀ γ ∈ rootsOfFam β Set.univ, S.ρ γ ∈ rootsOfFam β Set.univ := fun γ hγ => by
    rw [← hΨβ] at hγ ⊢
    exact hstab γ hγ
  have hw'' : ∀ γ ∈ rootsOfFam β Set.univ, w' • ι γ = ι (S.ρ γ) := fun γ hγ => by
    have hγ' : γ ∈ componentRoots (rootCharHom a) i := hΨβ ▸ hγ
    rw [hwγ γ hγ']
    exact (hw' γ hγ).2
  have hσq : ∀ c, σ c = c ^ S.D.q := fun c => by rw [hσc c, hs1, pow_one]
  have hcard1 : Nat.card ↥(fixSubfield σ) = S.D.q := by rw [hcard, hs1, pow_one]
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · have := S.hqpow.1
      rw [hq, h0, pow_zero] at this
      exact absurd this not_isPrimePow_one
    · exact h0
  have hKcard : Nat.card ↥(fixSubfield σ) = 2 ^ h := by rw [hcard1, hq]
  have hσ2 : ∀ c, σ c = c ^ 2 ^ h := fun c => by rw [hσq c, hq]
  unfold RCKReturnedCover
  simp only [hs1, mul_one, Function.iterate_one]
  obtain ⟨e, φ, hefix, hesurj, hφsurj, hφker, hφform, hfinM, hperfM, hsplit, hoddZ, hstd, hade,
    hRf⟩ := rckRet_cover hτ S hβroot hΨβ hι hh hfinσ hKcard f hf1 hf2 hf3 hfz
  have hRH : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ RetH τ β := by
    have h0 := rckRet_R_le_H S i hs1
    rw [hΨβ] at h0
    exact h0
  obtain ⟨zh, hzh, hcompat, hlang⟩ := rckRet_zhat hτsl S hΨβ hι hθ hρΨ hw'' hσq hzZ hzs
  obtain ⟨SK, hSKq, hSKg0, hSKn, hSKΦ, hSKρ, hSKΓ⟩ := rckRet_SK hfinσ (Q := 2 ^ h) hKcard hσ2
    ⟨h, hh, rfl⟩ hzh hlang
  have hstep : ∀ y, SK.D.step y = canonicalRep (coxeterSystem Tag.E6) GGL w' * frobGL σ y *
      (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ := fun y => by
    show SK.D.n * SK.D.Φ y * SK.D.n⁻¹ = _
    rw [hSKn, hSKΦ]
  have hCS : componentRootSpan (fixSubfield σ) (rootCharHom a) i =
      rootSpan τ ↥(fixSubfield σ) (rootsOfFam β Set.univ) := by
    show rootSpan τ ↥(fixSubfield σ) (componentRoots (rootCharHom a) i) = _
    rw [hΨβ]
  have hRmem : ∀ r, r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ↔
      ∃ x ∈ rootSpan τ ↥(fixSubfield σ) (rootsOfFam β Set.univ),
        r = z * baseChangeGL (fixSubfield σ).subtype x * z⁻¹ := by
    intro r
    rw [← hRf]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(x : ModGL τ ↥(fixSubfield σ)), ?_, hfz x⟩
      rw [← hCS]
      exact x.2
    · rintro ⟨x, hx, rfl⟩
      rw [← hCS] at hx
      exact ⟨⟨x, hx⟩, hfz ⟨x, hx⟩⟩
  have hrange'' := rckRet_kappa_range hθ hcompat (fixSubfield σ) hfinσ hRH hRmem
  have hker := rckRet_kappa_ker hθ hRH hrange'' fun y hy hc =>
    rckRet_center_SKGamma (fixSubfield σ) hy hc
  have hrangeΓ : (rckRetKappa θ hRH).range = SK.Γ := by
    rw [hSKΓ]
    exact hrange''
  have hψ : ∀ γ' : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ' → ∀ c : GaloisField 2 h,
      ((rckRetKappa θ hRH).comp φ) (e6Data_valid.xm (GaloisField 2 h) γ' c) =
        zh * pinnedX Tag.E6 GGL γ' (e c) * zh⁻¹ := by
    intro γ' hγ' c
    obtain ⟨hv, hιv⟩ := rckRet_iota_L hι hγ'
    have hy : pinnedX τ GGL (∑ j : Fin 6, γ' j • β j) (e c) ∈ RetH τ β :=
      (le_iSup₂_of_le (f := fun γ (_ : γ ∈ rootsOfFam β Set.univ) => rootSubgroup τ GGL γ)
        _ hv le_rfl) (mem_rootSubgroup.2 ⟨_, rfl⟩)
    obtain ⟨hx2, hθ2⟩ := hcompat ⟨_, hy⟩
    have hφ1 := hφform γ' hγ' c
    show θ ⟨((φ (e6Data_valid.xm (GaloisField 2 h) γ' c) :
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) : ModGL τ GGL),
          hRH (φ (e6Data_valid.xm (GaloisField 2 h) γ' c)).2⟩ = _
    have h3 : (⟨((φ (e6Data_valid.xm (GaloisField 2 h) γ' c) :
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) : ModGL τ GGL),
          hRH (φ (e6Data_valid.xm (GaloisField 2 h) γ' c)).2⟩ : ↥(RetH τ β)) =
        ⟨z * pinnedX τ GGL (∑ j : Fin 6, γ' j • β j) (e c) * z⁻¹, hx2⟩ := Subtype.ext hφ1
    rw [h3, hθ2, hθ.1 _ hv (e c) hy, hιv]
  have htor : ∀ b ∈ S.D.torus, ∃ t ∈ SK.D.torus,
      (∀ (x : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        (hx : b * (x : ModGL τ GGL) * b⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i),
        rckRetKappa θ hRH ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩ = t * rckRetKappa θ hRH x * t⁻¹) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, rckRootVal t (ι γ) = rckRootVal b γ := by
    intro b hb
    have hbT : b ∈ torusGroup τ GGL := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).1
    refine ⟨rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k)), ?_, ?_, ?_⟩
    · show _ ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf SK.D.n SK.D.Φ
      rw [hSKn, hSKΦ]
      exact rckRet_torus_fixed S hι hρΨ hw'' hσq hb
    · intro x hx
      obtain ⟨hx', h'⟩ := rckRet_theta_torus hι hθ hbT ⟨(x : ModGL τ GGL), hRH x.2⟩
      rw [rckRetKappa_apply, rckRetKappa_apply]
      exact h'
    · intro γ hγ
      exact rckRet_torus_val hι hbT γ (by rw [← hΨβ]; exact hγ)
  have hrg : ∀ γ ∈ (ggU .E6 0 h).D.roots, IsPGroup 2 ((ggU .E6 0 h).D.rootGroup γ) :=
    fun γ hγ => rootGroup_isPGroup_of_standardReturnAt hstd hγ
  have hZodd : ∀ x ∈ Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      Odd (orderOf x) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hφsurj x
    have hy : y ∈ Subgroup.center (ggU .E6 0 h).K :=
      rckA4_preimage_center φ (Group.isPerfect_def.1 hperfM) hφker hx
    have h1 : orderOf (φ y) ∣ orderOf y := orderOf_map_dvd φ y
    have h2 : orderOf y ∣ Nat.card (Subgroup.center (ggU .E6 0 h).K) :=
      Subgroup.orderOf_dvd_natCard _ hy
    exact Odd.of_dvd_nat hoddZ (h1.trans h2)
  have hdiag : ∀ b ∈ S.D.torus, GGPsiInnerDiag (ggU .E6 0 h).D
      ((rationalComponent S.ρ S.Γ (rootCharHom a) i).subtype.comp φ) b := by
    intro b hb
    have hbT : b ∈ torusGroup τ GGL := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).1
    have hFt : S.D.step b = b := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).2
    obtain ⟨t, htT, hconj, -⟩ := htor b hb
    have htadj : t ∈ adjointGroup Tag.E6 GGL :=
      CFSG.RankThree.PartOne.KE.twistedTorusOf_le_adjointGroup _ _ htT
    have htfix : canonicalRep (coxeterSystem Tag.E6) GGL w' * frobGL σ t *
        (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ = t := by
      have h0 := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 htT).2
      rw [hSKn, hSKΦ] at h0
      exact h0
    have hdiagE6 : GGPsiInnerDiag (ggU .E6 0 h).D ((rckRetKappa θ hRH).comp φ) t :=
      rckRet_innerDiag_E6 hh.ne' hσ2 e hzh htadj hlang htfix fun k c =>
        ⟨hψ _ (IsRoot.basis k) c, hψ _ (IsRoot.neg (IsRoot.basis k)) c⟩
    refine rckRet_transfer_innerDiag hrg φ (rckRetKappa θ hRH) hker.le hZodd ?_ hconj hdiagE6
    intro r hr
    refine ⟨rckRet_conj_mem_R S i hs1 hbT hFt hr, ?_⟩
    have h1 := rckRet_conj_mem_R S i hs1 (inv_mem hbT) (by rw [map_inv, hFt]) hr
    rwa [inv_inv] at h1
  refine ⟨ggU .E6 0 h, φ, Tag.E6, SK, rckRetKappa θ hRH, ι, rfl, hstd, hφsurj, hφker, hfinM,
    hperfM, hsplit, ?_, hdiag, Or.inr (Or.inl rfl), hSKq, hker, hrangeΓ, ?_, ?_, ?_, ?_, htor⟩
  · obtain ⟨β₀, hβ₀, hlong⟩ := CFSG.StandardType.LieKnownR2.ExcPos.exists_ggLongRoot_of_rckADEModel hade
    have hβ₀E : IsRoot Tag.E6 β₀ :=
      (e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField 2 h)).1 hβ₀
    exact ⟨β₀, hβ₀, hlong, β₀, hβ₀E, zh, hzh, (rckRet_pair_root hlang hstep β₀).1,
      (rckRet_pair_root hlang hstep (-β₀)).1,
      rckRet_pair_image e hefix hesurj hlang hstep hψ hβ₀E,
      rckRet_pair_image e hefix hesurj hlang hstep hψ (IsRoot.neg hβ₀E)⟩
  · rw [hΨβ]
    exact hι.1
  · intro γ hγ
    exact hι.2.2.2.1 γ (by rw [← hΨβ]; exact hγ)
  · intro γ hγ δ hδ
    exact hι.2.2.2.2 γ (by rw [← hΨβ]; exact hγ) δ (by rw [← hΨβ]; exact hδ)
  · intro γ hγ
    have hγ' : γ ∈ rootsOfFam β Set.univ := by rw [← hΨβ]; exact hγ
    rw [hSKρ (ι γ) (hι.1.mapsTo hγ')]
    exact (hw'' γ hγ').symm

end CFSG.StandardType.RCKRP

end
