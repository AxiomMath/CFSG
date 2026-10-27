module

public import CFSG.LocalAnalysis.StandardType.GGFamTame
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4A2outFixed
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Gamma
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Orbit
import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Shapes
import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Pair
import CFSG.LocalAnalysis.StandardType.GGFamSLRecogDefs
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA2FinishPart1
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.RatLayer
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Layer

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableCRes
open CFSG.Open (StatedLieTag)
open CFSG.HardMathSupport.Dickson.Sec6 (ssTw_exists_f)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (rootDiagUnit_pow_eq_one_of_forall)

private theorem l10lF3c_su3_derived {G : Type} [Group G] {f : ℕ} (hf1 : 1 ≤ f)
    (h : GGLieSU3Model G f) :
    CFSG.IsQuasisimple ↥(⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) ∨
      Group.IsSolvable ↥(⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  let : Field K := hKf
  let : Finite K := hKfin
  by_cases hf : f = 1
  · subst hf
    refine Or.inr ?_
    have hsol : Group.IsSolvable ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K) :=
      CFSG.Quasithin.isSolvable_statedSU_one hKcard
    have hG : Group.IsSolvable G :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.subtype _)
      (Subgroup.subtype_injective _)
  · refine Or.inl ?_
    have hf2 : 2 ≤ f := by omega
    have hnq : (3, 2 ^ f) ≠ (3, 2) := by
      intro hh
      have h2 : 2 ^ f = 2 := (Prod.mk.injEq 3 (2 ^ f) 3 2).mp hh |>.2
      have hle : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      rw [h2] at hle
      norm_num at hle
    have hqs : CFSG.IsQuasisimple ↥(CFSG.Open.StatedSU 3 (2 ^ f) K) :=
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := 2) (f := f)
        hKcard (n := 3) (by norm_num) hnq).1
    have hmap : Subgroup.map e.toMonoidHom (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) =
        (⊤ : Subgroup ↥(CFSG.Open.StatedSU 3 (2 ^ f) K)) := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map e.toMonoidHom,
        MonoidHom.range_eq_top.mpr e.surjective]
      show commutator ↥(CFSG.Open.StatedSU 3 (2 ^ f) K) = ⊤
      exact hqs.1.commutator_eq_top
    have hKtop : (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) = ⊤ := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [hmap, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective]
    rw [hKtop]
    exact CFSG.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv.trans e) hqs

private theorem l10lF3c_transfer_quasi {G : Type} [Group G] (H : Subgroup G)
    (h : CFSG.IsQuasisimple ↥(⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆)) :
    CFSG.IsQuasisimple ↥(⁅H, H⁆ : Subgroup G) := by
  have hmap : Subgroup.map H.subtype (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆) = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let e : ↥(⁅H, H⁆ : Subgroup G) ≃* ↥(⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆) :=
    (MulEquiv.subgroupCongr hmap.symm).trans
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).symm
  exact CFSG.IsQuasisimple.of_mulEquiv e h

private theorem l10lF3c_transfer_solv {G : Type} [Group G] (H : Subgroup G)
    (h : Group.IsSolvable ↥(⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆)) :
    Group.IsSolvable ↥(⁅H, H⁆ : Subgroup G) := by
  have hmap : Subgroup.map H.subtype (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆) = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let e : ↥(⁅H, H⁆ : Subgroup G) ≃* ↥(⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆) :=
    (MulEquiv.subgroupCongr hmap.symm).trans
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).symm
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

private theorem l10lF3c_su3_derived_sub {G : Type} [Group G] (H : Subgroup G) {f : ℕ}
    (hf1 : 1 ≤ f) (h : GGLieSU3Model ↥H f) :
    CFSG.IsQuasisimple ↥(⁅H, H⁆ : Subgroup G) ∨ Group.IsSolvable ↥(⁅H, H⁆ : Subgroup G) := by
  rcases l10lF3c_su3_derived hf1 h with hq | hs
  · exact Or.inl (l10lF3c_transfer_quasi H hq)
  · exact Or.inr (l10lF3c_transfer_solv H hs)

private theorem l10lF3c_suN_rank_ncardM {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {i : KernelComponent χ} (h : twistKindM ρ χ i = .suN) :
    2 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard =
        compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1) := by
  unfold twistKindM at h
  split_ifs at h with h1 h2 h3 h4
  exact h4

theorem langFamTame_suN_F4
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (hT₁ : rootDiagUnit Tag.F4 a₁ ∈ S.D.torus) (hT₂ : rootDiagUnit Tag.F4 a₂ ∈ S.D.torus)
    (hap₁ : ∀ j, a₁ j ^ 3 = 1) (hap₂ : ∀ j, a₂ j ^ 3 = 1)
    (hcard : Nat.card ↥(Subgroup.closure
      ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} : Set (ModGL Tag.F4 L))) = 3 ^ 2)
    (i : KernelComponent (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)))
    (hk : twistKindM S.ρ (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)) i = .suN) :
    CFSG.IsQuasisimple
        (rationalComponentM S.ρ S.Γ (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)) i) ∨
      Group.IsSolvable
        (rationalComponentM S.ρ S.Γ (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)) i) := by
  classical
  obtain ⟨f, hf, hqf⟩ := ssTw_exists_f S (ℓ := 2)
  have hH : GGLieF4PlaneHyp S.D S.ρ a₁ a₂ :=
    { frob := S.frob
      finite := S.finite
      hq := ⟨f, hf, hqf⟩
      mem₁ := hT₁
      mem₂ := hT₂
      pow₁ := rootDiagUnit_pow_eq_one_of_forall hap₁
      pow₂ := rootDiagUnit_pow_eq_one_of_forall hap₂
      card := hcard }
  obtain ⟨i', hi'⟩ := exists_jointComponent_of_famCharHom a₁ a₂ i
  set Ψ : Set (Fin Tag.F4.rank → ℤ) := componentRoots (jointChar a₁ a₂) i' with hΨ
  have hkM' : twistKindM S.ρ (jointChar a₁ a₂) i' = .suN := by
    rw [← twistKindM_eq_of_componentRoots_eq S.ρ hi']
    exact hk
  have hshape : compRank Ψ = 2 ∧ Ψ.ncard = 6 := by
    obtain ⟨h2, hn⟩ := l10lF3c_suN_rank_ncardM S.ρ hkM'
    rw [← hΨ] at h2 hn
    have h0 := ggLieF4Plane_shape hH i'
    rw [← hΨ] at h0
    unfold GGLieF4PlaneShape at h0
    rcases h0 with ⟨hr, hc⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩
    · omega
    · exact ⟨hr, hc⟩
    · rw [hr] at hn
      norm_num at hn
      omega
  have hρΨ : (S.ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) '' Ψ = Ψ := by
    rw [hΨ]
    exact ggLieF4Plane_image_eq hH i'
  have hs : componentOrbitLength S.ρ Ψ = 1 :=
    CFSG.StandardType.F4ExplicitPos.OddKernelOrbit.componentOrbitLength_eq_one_of_image_eq hρΨ
  have hout : ¬ twistInner Ψ (fun u => S.ρ u) := by
    intro h
    have h1 : twistInner Ψ
        ((S.ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ))^[componentOrbitLength S.ρ Ψ]) := by
      rw [hs]
      simpa using h
    unfold twistKindM at hkM'
    rw [if_pos h1] at hkM'
    exact absurd hkM' (by decide)
  have hG : GGLieSU3Model ↥(rootSpan Tag.F4 L Ψ ⊓ S.D.model) f :=
    ggLieF4A2out_fixedGroup hH hf hqf i' hshape hρΨ hout
  have hΓ : S.D.Γ = S.D.model := ggLieF4_gamma_eq_model S.D S.finite ⟨f, hf, hqf⟩
  have hR : rationalComponentM S.ρ S.Γ (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)) i =
      ⁅rootSpan Tag.F4 L Ψ ⊓ S.D.model, rootSpan Tag.F4 L Ψ ⊓ S.D.model⁆ := by
    rw [← ratComp_eq_rationalComponentM]
    unfold ratComp
    rw [hi', CFSG.StandardType.F4ExplicitPos.OddKernelOrbit.ratOrbit_eq_of_image_eq hρΨ,
      LangSetup.Γ, hΓ]
  rw [hR]
  exact l10lF3c_su3_derived_sub (rootSpan Tag.F4 L Ψ ⊓ S.D.model) hf hG

end CFSG.StandardType.LieCore
