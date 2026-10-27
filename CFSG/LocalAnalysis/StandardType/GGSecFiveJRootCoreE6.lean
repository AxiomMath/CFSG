module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreTags
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreE6Char
import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvAll
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint

public section

namespace CFSG.StandardType

namespace JCoreE6

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  LayerExc LayerSixE
open scoped commutatorElement

private theorem exists_eq_map_derivedPreimage_of_model {L C G : Type*} [Group L] [Group C]
    [Group G] [Finite L] [Finite G] {π : L →* C} (hπ : Function.Surjective π)
    (hπker : π.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card π.ker)) {ψ : L →* G}
    (hker : ψ.ker ≤ π.ker) {y : G} (hyN : y ∈ Subgroup.normalizer (ψ.range : Set G))
    {α : MulAut C} (hα : GGInduces π ψ y α) {β : Type} {S : β → Subgroup C}
    (hS : LayerCores.IsSubCoreFamily (autFix (Subgroup.zpowers α)) S) {J : Subgroup G}
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer {y})) :
    ∃ c, J = (derivedPreimage π (S c)).map ψ := by
  set M := (autFix (Subgroup.zpowers α)).comap π
  have hψker : ψ.ker ≤ Subgroup.center L := hker.trans hπker
  set H := ψ.range ⊓ Subgroup.centralizer ({y} : Set G)
  have hHM : H ≤ M.map ψ := by
    rintro _ ⟨⟨u, rfl⟩, hu⟩
    refine ⟨u, ?_, rfl⟩
    change π u ∈ autFix (Subgroup.zpowers α)
    rw [TagsExc.mem_autFix_zpowers]
    refine (hα u u ?_).symm
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hu]
    group
  have hMH : ⁅M, M⁆ ≤ H.comap ψ := by
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    refine ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hz : ∀ {u u' : L}, u ∈ M → ψ u' = y * ψ u * y⁻¹ → u⁻¹ * u' ∈ Subgroup.center L := by
      intro u u' hu hu'
      refine hπker ?_
      have hfix : α (π u) = π u := TagsExc.mem_autFix_zpowers.mp hu
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα u u' hu', hfix, inv_mul_cancel]
    obtain ⟨y₁', hy₁'⟩ := exists_conj_eq hyN y₁
    obtain ⟨y₂', hy₂'⟩ := exists_conj_eq hyN y₂
    have hconj : ψ ⁅y₁', y₂'⁆ = y * ψ ⁅y₁, y₂⁆ * y⁻¹ := by
      rw [map_commutatorElement, map_commutatorElement, hy₁', hy₂']
      simp only [commutatorElement_def]
      group
    have hc : ⁅y₁', y₂'⁆ = ⁅y₁, y₂⁆ := by
      calc ⁅y₁', y₂'⁆ = ⁅y₁ * (y₁⁻¹ * y₁'), y₂ * (y₂⁻¹ * y₂')⁆ := by
            rw [mul_inv_cancel_left, mul_inv_cancel_left]
        _ = ⁅y₁, y₂⁆ := by
            rw [commutatorElement_mul_central_left (hz hy₁ hy₁'),
              commutatorElement_mul_central_right (hz hy₂ hy₂')]
    rw [hc] at hconj
    calc ψ ⁅y₁, y₂⁆ * y = y * ψ ⁅y₁, y₂⁆ * y⁻¹ * y := by rw [← hconj]
      _ = y * ψ ⁅y₁, y₂⁆ := by group
  have hS' := isSubCoreFamily_comap_of_central π hπ hπker hodd hS
  have hS'' : LayerCores.IsSubCoreFamily ⁅M, M⁆ (fun c => derivedPreimage π (S c)) := by
    have h := hS'.inf_of_commutator_le (N := ⁅M, M⁆) le_rfl
    rwa [inf_eq_right.mpr (Subgroup.commutator_le_self M)] at h
  have hC₀H : (⁅M, M⁆).map ψ ≤ H := Subgroup.map_le_iff_le_comap.mpr hMH
  have hnorm : (((⁅M, M⁆).map ψ).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hC₀H]
    rintro _ k ⟨s, hs, rfl⟩ hk
    obtain ⟨u, hu, rfl⟩ := hHM hk
    exact ⟨u * s * u⁻¹, LayerSixE.conj_mem_commutator_self hu hs, by rw [map_mul, map_mul, map_inv]⟩
  have hcommH : ⁅H, H⁆ ≤ (⁅M, M⁆).map ψ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hHM hHM
  exact LayerPDiv.exists_eq_map_of_isComponentOf_sub ψ hψker hC₀H hnorm hcommH hS'' hJ

private theorem autFix_zpowers_rootDiagAutHom
    {τ : Tag} {K : Type} [Field K] (l : Fin τ.rank → Kˣ) :
    autFix (Subgroup.zpowers (rootDiagAutHom τ K l)) = famCentralizer {l} := by
  ext g
  rw [TagsExc.mem_autFix_zpowers, mem_famCentralizer]
  refine ⟨fun h a ha => ?_, fun h => Subtype.ext (h l (Set.mem_singleton l))⟩
  rw [Set.mem_singleton_iff.mp ha]
  exact congrArg Subtype.val h

private theorem isSubCoreFamily_autFix_rootDiag
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) {l : Fin τ.rank → Kˣ} (hl : l ^ p = 1) :
    LayerCores.IsSubCoreFamily (autFix (Subgroup.zpowers (rootDiagAutHom τ K l)))
      (fun i => (componentRootSpan K (famChar ({l} : Set (Fin τ.rank → Kˣ))) i).comap
        (adjointGroup τ K).subtype) := by
  obtain ⟨t, ht⟩ := TagsExc.exists_unit_sq_ne_one hK4
  rw [autFix_zpowers_rootDiagAutHom]
  exact TagsExc.isSubCoreFamily_famCentralizer {l} ht
    (exists_ggDer_famStabilizerSubgroup_le_reflection hp {l} fun b hb =>
      ⟨1, by rw [pow_one, Set.mem_singleton_iff.mp hb]; exact hl⟩)

private theorem exists_ggRootLevi_le_derivedPreimage_E6
    {k : Type} [Field k] [Finite k] [CharP k 2] {F : Set (Fin Tag.E6.rank → kˣ)}
    (i : KernelComponent (famChar F))
    (hS : Group.IsPerfect ↥((componentRootSpan k (famChar F) i).comap
      (adjointGroup .E6 k).subtype)) :
    ∃ γ ∈ (CFSG.LieType.Steinberg.Minuscule.e6Datum k).roots,
      ggRootLevi (CFSG.LieType.Steinberg.Minuscule.e6Datum k) γ ≤
        derivedPreimage (CFSG.LieType.Steinberg.Isogeny.e6Isogeny k)
          ((componentRootSpan k (famChar F) i).comap (adjointGroup .E6 k).subtype) := by
  have hodd : Odd (Nat.card (CFSG.LieType.Steinberg.Isogeny.e6Isogeny k).ker) := by
    have h2 := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker k (p := 2)
    exact Nat.not_even_iff_odd.mp fun he => h2 (even_iff_two_dvd.mp he)
  have hker := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center k
  have h2 : ∀ δ, IsPGroup 2 ((CFSG.LieType.Steinberg.Minuscule.e6Datum k).rootGroup δ) := by
    rintro δ ⟨g, hg⟩
    obtain ⟨c, rfl⟩ := (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.mem_rootGroup k).1 hg
    have hc : (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm k δ c) ^ 2 = 1 := by
      rw [sq, ← CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm_add, CharTwo.add_self_eq_zero,
        CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm_zero]
    exact ⟨1, Subtype.ext (by simpa using hc)⟩
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := Quotient.exists_rep i
  have hΨ : γ ∈ componentRoots (famChar F) ⟦⟨γ, hγ⟩⟧ := ⟨hγ, rfl⟩
  have hle : ∀ δ ∈ componentRoots (famChar F) ⟦⟨γ, hγ⟩⟧,
      (CFSG.LieType.Steinberg.Minuscule.e6Datum k).rootGroup δ ≤
        derivedPreimage (CFSG.LieType.Steinberg.Isogeny.e6Isogeny k)
          ((componentRootSpan k (famChar F) ⟦⟨γ, hγ⟩⟧).comap (adjointGroup .E6 k).subtype) := by
    intro δ hδ
    obtain ⟨hδk, -⟩ := id hδ
    refine le_derivedPreimage_of_isPGroup_two
      (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective k) hker hodd hS (h2 δ) ?_
    refine (CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup k hδk.1).le.trans ?_
    rw [CFSG.LieType.Steinberg.Adjoint.rootGroup_of_isRoot hδk.1,
      ← RootOperatorFamily.subgroupOf_rootSubgroup_eq]
    exact Subgroup.comap_mono (le_iSup₂_of_le δ hδ le_rfl)
  exact ⟨γ, (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.mem_minDatum_roots
      CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6 k).2 hγ.1,
    sup_le (hle γ hΨ) (hle (-γ) ((isRootComponent_componentRoots _).neg_mem γ hΨ))⟩

end JCoreE6

theorem ggJRootCoreAt_E6 :
    GGJRootCoreAt .E6 := by
  intro G _ _ p Bs L J n f ψ y hloc hstd hy hJ
  obtain ⟨⟨hp, -, hadm, -⟩, ⟨hker, rfl, -, hpf⟩, ⟨hEA, hBN, -⟩, -, -⟩ := hloc
  have hf2 : 2 ≤ f := by
    have h1 : 1 ≤ f := hadm.2.1
    by_contra h
    obtain rfl : f = 1 := by omega
    exact hp.ne_one (Nat.dvd_one.mp (by simpa using hpf))
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 2 f)) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' _
  have hodd : Odd (Nat.card (CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 f)).ker) := by
    have h2 := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker
      (GaloisField 2 f) (p := 2)
    exact Nat.not_even_iff_odd.mp fun he => h2 (even_iff_two_dvd.mp he)
  have hyN := hBN hy
  obtain ⟨a, hap, hα⟩ := JCoreE6.exists_induces_rootDiag_E6 (k := GaloisField 2 f) ψ hker hyN
    (hEA.2 y hy) (hstd y hy)
  have hS := JCoreE6.isSubCoreFamily_autFix_rootDiag
    (TagsExc.four_le_card_galoisField hf2) hp hap
  obtain ⟨i, rfl⟩ := JCoreE6.exists_eq_map_derivedPreimage_of_model
    (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective _)
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center _) hodd
    (LayerSixE.ker_le_ker_e6Isogeny hker) hyN hα hS hJ
  obtain ⟨γ, hγ, hle⟩ := JCoreE6.exists_ggRootLevi_le_derivedPreimage_E6 i (hS.2.2.1 i).1
  exact ⟨γ, hγ, Subgroup.map_mono hle⟩

end CFSG.StandardType

end
