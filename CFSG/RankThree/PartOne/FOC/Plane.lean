module

public import CFSG.RankThree.PartOne.S11d.FieldOuterGlue
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S11.SecTenEight

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (localRank)

namespace FOC

@[expose] def FieldInnerPlaneWith
    (P : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (J A : Subgroup H) (c u v : H) (E : Subgroup H),
    p.Prime → 5 ≤ p → localRank p H ≤ 3 → CFSG.IsQuasisimple ↥J →
    Catalog (↥J ⧸ Subgroup.center ↥J) → P H p J →
    A ≤ Subgroup.normalizer (J : Set H) → IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    c ∈ A → c ≠ 1 → c ∈ Subgroup.centralizer (J : Set H) → u ∈ A → v ∈ A →
    u ∈ J ⊔ Subgroup.centralizer (J : Set H) →
    IsComponentOf (J ⊓ Subgroup.centralizer ({v} : Set H)) E →
    u ∈ Subgroup.normalizer (E : Set H) → FieldLike p u E → False

end FOC

namespace FOC

@[expose] def SectionProviderK
    (P : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 3 → CFSG.IsKProper G → ∀ (d : G),
    Subgroup.centralizer ({d} : Set G) ≠ ⊤ → ∀ (I : Subgroup G),
    I ≤ Subgroup.centralizer ({d} : Set G) → ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ : ↥I →* Γ)
    (p : ℕ), p.Prime → 5 ≤ p → localRank p Γ ≤ 3 → CFSG.IsQuasisimple ↥φ.range →
    Catalog (↥φ.range ⧸ Subgroup.center ↥φ.range) → P Γ p φ.range

theorem sectionProviderK_and {P Q : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop}
    (hP : SectionProviderK P) (hQ : SectionProviderK Q) :
    SectionProviderK (fun H _ _ p J => P H p J ∧ Q H p J) :=
  fun G _ _ hev hKP d hd I hIC Γ _ _ φ p hp hp5 hloc hq hcat =>
    ⟨hP G hev hKP d hd I hIC Γ φ p hp hp5 hloc hq hcat,
      hQ G hev hKP d hd I hIC Γ φ p hp hp5 hloc hq hcat⟩

theorem sectionProviderK_of_sectionProvider
    {P : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop} (h : SectionProvider P) :
    SectionProviderK P :=
  fun G _ _ hev _ _ _ I _ Γ _ _ φ p hp hp5 hloc hq hcat => h G hev I Γ φ p hp hp5 hloc hq hcat

end FOC

open OutTheta in
theorem fieldOnComponentOuter_of_planeWithK
    (P : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hP : FOC.SectionProviderK P) (hplane : FOC.FieldInnerPlaneWith P) : FieldOnComponentOuter := by
  intro G _ _ p A hS d hdA hd1 I hI u huA v hvA E hE huE hfl hinn
  classical
  have hp : p.Prime := sectionTenSetup_prime hS
  have hp3 : 3 < p := sectionTenSetup_three_lt hS
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    subst h4
    norm_num at hp
  have : Fact p.Prime := ⟨hp⟩
  have hevG : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS).le
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, hAcard, -, -⟩ := id hS
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hIC : I ≤ Subgroup.centralizer ({d} : Set G) := (mem_thetaComponentsAt_iff.mp hI).1
  have hAI : A ≤ Subgroup.normalizer (I : Set G) := fun x hx =>
    mem_normalizer_of_mem_centralizer_thetaComponentsAt hp hp3 hevG hI
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm x hx d hdA)) (hApow x hx)
  have hCtop : Subgroup.centralizer ({d} : Set G) ≠ ⊤ :=
    EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hd1
  obtain ⟨Γ, _, _, φ, ψ, hker, hψinj, hcompat, hrank⟩ :=
    exists_quotient_model hp hp2 hAI (IsElementaryAbelian.isPGroup p A)
  obtain ⟨hJq, hJcat⟩ := model_quasisimple_catalog hp hbridge hKP hCtop hI φ hker
  have hEI : E ≤ I := hE.1.trans inf_le_left
  have huJC := mem_sup_centralizer_of_inner hAI φ ψ hker hcompat huA hinn
  have hEcomp := isComponentOf_image hAI φ ψ hp hker hcompat hvA (hApow v hvA) hE
  have hfl' := fieldLike_image hAI φ ψ hp hker hcompat huA (hApow u huA) hEI hE.2.1 huE hfl
  have huE' := psi_mem_normalizer_image hAI φ ψ hcompat hEI (a := ⟨u, huA⟩) huE
  have hrangeN := range_psi_le_normalizer hAI φ ψ hcompat
  have hA'e : IsElementaryAbelian p ψ.range := isElementaryAbelian_range' ψ
  have hA'card : Nat.card ψ.range = p ^ 3 := by
    rw [← hAcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hcA' : ψ ⟨d, hdA⟩ ∈ ψ.range := ⟨_, rfl⟩
  have hc1 : ψ ⟨d, hdA⟩ ≠ 1 := by
    intro h
    have := hψinj (h.trans (map_one ψ).symm)
    exact hd1 (congrArg Subtype.val this)
  have hcC : ψ ⟨d, hdA⟩ ∈ Subgroup.centralizer (φ.range : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, rfl⟩
    have h1 := hcompat ⟨d, hdA⟩ i
    have h2 : I.normalizerMonoidHom ⟨d, hAI hdA⟩ i = i := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hid : (i : G) * d = d * (i : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hIC i.2)
      exact mul_inv_eq_iff_eq_mul.mpr hid.symm
    rw [h2] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  exact hplane Γ p φ.range ψ.range (ψ ⟨d, hdA⟩) (ψ ⟨u, huA⟩) (ψ ⟨v, hvA⟩) (imageOf φ E hEI) hp hp5
    (hrank.trans hevG) hJq hJcat
    (hP G hevG hKP d hCtop I hIC Γ φ p hp hp5 (hrank.trans hevG) hJq hJcat)
    hrangeN hA'e hA'card hcA' hc1 hcC ⟨_, rfl⟩ ⟨_, rfl⟩ huJC hEcomp huE' hfl'

end CFSG.RankThree.PartOne
