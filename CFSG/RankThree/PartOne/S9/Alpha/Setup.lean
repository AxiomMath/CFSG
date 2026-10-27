module

public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual

public section

namespace CFSG.RankThree.PartOne.AlphaTheory

open CFSG CFSG.RankThree.GroupTheory Subgroup

variable {G : Type*} [Group G]

@[expose] def coreTwo (a : G) : Subgroup G :=
  inSubgroup (pCore 2) (centralizer ({a} : Set G))

@[expose] def centralizerCoreTwo (B : Subgroup G) : Subgroup G :=
  inSubgroup (pCore 2) (centralizer (B : Set G))

@[expose] def gammaB (B : Subgroup G) (a : G) : Subgroup G :=
  ⁅coreTwo a, B⁆ ⊔ (centralizerCoreTwo B ⊓ centralizer ({a} : Set G))

structure AlphaSetup (p : ℕ) (A B : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  pow : ∀ x ∈ A, x ^ p = 1
  le : B ≤ A

section Elementary

theorem coreTwo_le_centralizer (a : G) : coreTwo a ≤ centralizer ({a} : Set G) :=
  SteinbergBY.inSubgroup_pCore_le 2 _

theorem isPGroup_coreTwo (a : G) : IsPGroup 2 (coreTwo a) :=
  SteinbergBY.isPGroup_inSubgroup_pCore 2 _

theorem le_normalizer_coreTwo {a : G} {X : Subgroup G} (hX : X ≤ centralizer ({a} : Set G)) :
    X ≤ normalizer (coreTwo a : Set G) :=
  hX.trans (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _)

theorem centralizerCoreTwo_le_centralizer (B : Subgroup G) :
    centralizerCoreTwo B ≤ centralizer (B : Set G) :=
  SteinbergBY.inSubgroup_pCore_le 2 _

theorem isPGroup_centralizerCoreTwo (B : Subgroup G) : IsPGroup 2 (centralizerCoreTwo B) :=
  SteinbergBY.isPGroup_inSubgroup_pCore 2 _

theorem le_normalizer_centralizerCoreTwo {B X : Subgroup G} (hX : X ≤ centralizer (B : Set G)) :
    X ≤ normalizer (centralizerCoreTwo B : Set G) :=
  hX.trans (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _)

theorem T_le_normalizer_J (B : Subgroup G) (a : G) :
    centralizerCoreTwo B ⊓ centralizer ({a} : Set G) ≤
      normalizer ((⁅coreTwo a, B⁆ : Subgroup G) : Set G) :=
  fun _ hx => SteinbergBY.mem_normalizer_commutator
    (le_normalizer_coreTwo (X := centralizerCoreTwo B ⊓ centralizer ({a} : Set G)) inf_le_right hx)
    (centralizer_le_normalizer _ (centralizerCoreTwo_le_centralizer B hx.1))

theorem isPGroup_T (B : Subgroup G) (a : G) :
    IsPGroup 2 (centralizerCoreTwo B ⊓ centralizer ({a} : Set G) : Subgroup G) :=
  (isPGroup_centralizerCoreTwo B).to_le inf_le_left

theorem commutator_coreTwo_le {B : Subgroup G} {a : G} (hBa : B ≤ centralizer ({a} : Set G)) :
    ⁅coreTwo a, B⁆ ≤ coreTwo a :=
  le_normalizer_iff_commutator_le_left.mp (le_normalizer_coreTwo hBa)

theorem isPGroup_J {B : Subgroup G} {a : G} (hBa : B ≤ centralizer ({a} : Set G)) :
    IsPGroup 2 (⁅coreTwo a, B⁆ : Subgroup G) :=
  (isPGroup_coreTwo a).to_le (commutator_coreTwo_le hBa)

theorem isPGroup_gammaB {B : Subgroup G} {a : G} (hBa : B ≤ centralizer ({a} : Set G)) :
    IsPGroup 2 (gammaB B a) :=
  IsPGroup.to_sup_of_normal_left' (isPGroup_J hBa) (isPGroup_T B a) (T_le_normalizer_J B a)

theorem gammaB_le_centralizer {B : Subgroup G} {a : G} (hBa : B ≤ centralizer ({a} : Set G)) :
    gammaB B a ≤ centralizer ({a} : Set G) :=
  sup_le ((commutator_coreTwo_le hBa).trans (coreTwo_le_centralizer a)) inf_le_right

end Elementary

namespace AlphaSetup

variable {p : ℕ} {A B : Subgroup G} (h : AlphaSetup p A B)
include h

theorem le_centralizer_singleton {a : G} (ha : a ∈ A) : A ≤ centralizer ({a} : Set G) :=
  fun _ hx => mem_centralizer_singleton_iff.mpr (h.comm _ hx a ha)

theorem le_centralizer {X : Subgroup G} (hX : X ≤ A) : A ≤ centralizer (X : Set G) :=
  fun x hx => mem_centralizer_iff.mpr fun y hy => h.comm y (hX hy) x hx

theorem le_normalizer {X : Subgroup G} (hX : X ≤ A) : A ≤ normalizer (X : Set G) :=
  (h.le_centralizer hX).trans (centralizer_le_normalizer _)

theorem B_le_centralizer_singleton {a : G} (ha : a ∈ A) : B ≤ centralizer ({a} : Set G) :=
  h.le.trans (h.le_centralizer_singleton ha)

theorem le_normalizer_coreTwo {a : G} (ha : a ∈ A) : A ≤ normalizer (coreTwo a : Set G) :=
  AlphaTheory.le_normalizer_coreTwo (h.le_centralizer_singleton ha)

theorem le_normalizer_centralizerCoreTwo : A ≤ normalizer (centralizerCoreTwo B : Set G) :=
  AlphaTheory.le_normalizer_centralizerCoreTwo (h.le_centralizer h.le)

theorem le_normalizer_J {a : G} (ha : a ∈ A) :
    A ≤ normalizer ((⁅coreTwo a, B⁆ : Subgroup G) : Set G) :=
  fun _ hx => SteinbergBY.mem_normalizer_commutator (h.le_normalizer_coreTwo ha hx)
    (h.le_normalizer h.le hx)

theorem le_normalizer_T {a : G} (ha : a ∈ A) :
    A ≤ normalizer ((centralizerCoreTwo B ⊓ centralizer ({a} : Set G) : Subgroup G) : Set G) :=
  fun _ hx => SteinbergBY.mem_normalizer_inf (h.le_normalizer_centralizerCoreTwo hx)
    (Subgroup.le_normalizer (h.le_centralizer_singleton ha hx))

theorem le_normalizer_gammaB {a : G} (ha : a ∈ A) : A ≤ normalizer (gammaB B a : Set G) :=
  fun _ hx => SteinbergBY.mem_normalizer_of_map_conj_eq (by
    rw [gammaB, Subgroup.map_sup,
      SteinbergBY.map_conj_eq_of_mem_normalizer (h.le_normalizer_J ha hx),
      SteinbergBY.map_conj_eq_of_mem_normalizer (h.le_normalizer_T ha hx)])

end AlphaSetup

end CFSG.RankThree.PartOne.AlphaTheory
