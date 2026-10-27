module

public import CFSG.RankThree.PartOne.K156.Full
public import CFSG.RankThree.PartOne.S13K.Assembly

public section

namespace CFSG.RankThree.PartOne.K1320X

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_theta_of_quasisimple {p : ℕ} (hp : p.Prime) {e : G} {I : Subgroup G}
    (hI : I ∈ thetaComponentsAt p e) (hq : CFSG.IsQuasisimple ↥I) :
    I ≤ Subgroup.centralizer
      (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) : Set G) := by
  obtain ⟨hIC, hL⟩ := mem_thetaComponentsAt_iff.mp hI
  set C := Subgroup.centralizer ({e} : Set G) with hC
  set θC := inSubgroup (aschbacherSolvableCore p) C with hθC
  obtain ⟨hTn, hTs⟩ := S15K.theta_inf_normal_solvable hp (le_refl C)
  have hRs : Group.IsSolvable ((θC ⊓ C).subgroupOf C) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : θC ⊓ C ≤ C)).toMonoidHom)
      (MulEquiv.injective _)
  have hcomp : IsComponent (I.subgroupOf C) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hIC).symm hq, hL.2.1⟩
  have h := (LocalCores.component_solvable_centralizer hRs hTn.isSubnormal).1 _ hcomp
  have h2 := congrArg (Subgroup.map C.subtype) h
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hIC,
    Subgroup.map_subgroupOf_eq_of_le (inf_le_right : θC ⊓ C ≤ C), Subgroup.map_bot] at h2
  have hθle : θC ⊓ C = θC := inf_of_le_left (Subgroup.map_subtype_le _)
  rw [hθle] at h2
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2

omit [Finite G] in
theorem le_centralizer_symm {H K : Subgroup G}
    (h : H ≤ Subgroup.centralizer (K : Set G)) : K ≤ Subgroup.centralizer (H : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact ((Subgroup.mem_centralizer_iff.1 (h hx)) k hk).symm

theorem commute_of_hasTwoSub (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs)
    (h106 : K156.Full106Stmt) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hEA : E = A) {e : G} (heE : e ∈ E) (he1 : e ≠ 1)
    {K₁ K₂ I₁ I₂ : Subgroup G} (hI₁ : I₁ ∈ thetaComponentsAt p e)
    (hI₂ : I₂ ∈ thetaComponentsAt p e) (hne : I₁ ≠ I₂) (hK₁ : K₁ ≤ I₁) (hK₂ : K₂ ≤ I₂)
    (hperf : Group.IsPerfect ↥K₁) (hTS : HasTwoSub E I₁) :
    K₁ ≤ Subgroup.centralizer (K₂ : Set G) := by
  obtain ⟨S, hSI, hS1, hS2, hES, hSE⟩ := hTS
  have hmem : I₁ ∈ sectionTenZero p A :=
    ⟨mem_thetaComponentFamily_iff.2 ⟨e, hEA ▸ heE, he1, hI₁⟩, S, hSI, hS1, hS2, hEA ▸ hES,
      hEA ▸ hSE⟩
  have hq : CFSG.IsQuasisimple ↥I₁ := h106 hS hTwo G p A h.setup I₁ hmem
  exact centralizes_of_distinct_components h.prime hI₁ hI₂ hne hK₁ hK₂ hperf
    (hK₁.trans (le_centralizer_theta_of_quasisimple h.prime hI₁ hq))

@[expose] def KFCommDistinctXne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A →
    ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, KFLiftAt p E s → KFLiftAt p E t →
    s * t = t * s → ∀ e ∈ autFixedInG E s ⊓ autFixedInG E t, e ≠ 1 →
    ∀ I₁ ∈ thetaComponentsAt p e, ∀ I₂ ∈ thetaComponentsAt p e, I₁ ≠ I₂ →
      kZero p E s ≤ I₁ → kZero p E t ≤ I₂ →
      kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G)

theorem kfCommDistinctX_of_ne
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs) (h106 : K156.Full106Stmt)
    (hne : KFCommDistinctXne) : KFCommDistinctX := by
  intro G _ _ p A c L E h hF hF13 hT s hs t ht K_s K_t hKs hKt hspl hcomm e he he1 I₁ hI₁ I₂ hI₂ hI
    hK₁ hK₂
  have heE : e ∈ E := Subgroup.map_subtype_le _ (Subgroup.mem_inf.mp he).1
  by_cases hEA : E = A
  · rcases hspl with hEA' | h1 | h2
    · exact absurd hEA hEA'
    · exact commute_of_hasTwoSub hS hTwo h106 h hEA heE he1 hI₁ hI₂ hI hK₁ hK₂ hKs.2.1.1
        (h1.mono hK₁)
    · exact le_centralizer_symm (commute_of_hasTwoSub hS hTwo h106 h hEA heE he1 hI₂ hI₁ hI.symm
        hK₂ hK₁ hKt.2.1.1 (h2.mono hK₂))
  · have hexs : ¬ ∃ f, kExceptional p (kZero p E s) f :=
      (S13K.kfLiftAll_holds hGA G p A c L E h hF hF13 hT (Or.inl hEA) s hs).2.2.1
    have hext : ¬ ∃ f, kExceptional p (kZero p E t) f :=
      (S13K.kfLiftAll_holds hGA G p A c L E h hF hF13 hT (Or.inl hEA) t ht).2.2.1
    have hKsK : K_s = kZero p E s := hKs.1.2 hexs
    have hKtK : K_t = kZero p E t := hKt.1.2 hext
    subst hKsK
    subst hKtK
    have hLs : KFLiftAt p E s := ⟨hKs.2.1, hKs.2.2.1, hexs, hKs.2.2.2.1, hKs.2.2.2.2⟩
    have hLt : KFLiftAt p E t := ⟨hKt.2.1, hKt.2.2.1, hext, hKt.2.2.2.1, hKt.2.2.2.2⟩
    exact hne G p A c L E h hF hF13 hT hEA s hs t ht hLs hLt hcomm e he he1 I₁ hI₁ I₂ hI₂ hI hK₁
      hK₂

end CFSG.RankThree.PartOne.K1320X
