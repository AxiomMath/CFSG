module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmR
public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2C
public import CFSG.Blueprint.ChevalleyRootGroupsTriangular
public import CFSG.Foundations
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

section Units

variable {k : Type} [Field k]

theorem units_eq_zero {u : kˣ} (hu : u ≠ 1) {x : k} (h : (u : k) * x = x) : x = 0 := by
  have h1 : ((u : k) - 1) * x = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd (Units.val_eq_one.1 (sub_eq_zero.1 h2)) hu
  · exact h2

theorem zpow_ne_one_of_cube {t : kˣ} (ht : t ^ 3 = 1) (ht1 : t ≠ 1) :
    t ^ (-1 : ℤ) ≠ 1 ∧ t ^ (2 : ℤ) ≠ 1 ∧ t ^ (1 : ℤ) ≠ 1 := by
  refine ⟨?_, ?_, by rwa [zpow_one]⟩
  · rw [zpow_neg, zpow_one]
    exact inv_ne_one.2 ht1
  · intro h2
    apply ht1
    have h2' : t ^ 2 = 1 := by simpa using h2
    calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [ht, h2', inv_one, one_mul]

end Units

section TorusA

variable {k : Type} [Field k]

local notation "X" => pinnedX Tag.G2 k


theorem torus_a_conj (t : kˣ) {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (m : ℤ)
    (hm : ∑ j, Tag.G2.cartan g2ia j * α j = m) (x : k) :
    torusElt .G2 k g2ia t * X α x * (torusElt .G2 k g2ia t)⁻¹ = X α (((t ^ m : kˣ) : k) * x) := by
  rw [root_torus_conjugation g2ia hα, hm]

theorem torus_a_conj_g2N (t : kˣ) (A B C D E F : k) :
    torusElt .G2 k g2ia t * g2N A B C D E F * (torusElt .G2 k g2ia t)⁻¹ =
      g2N (((t ^ (-1 : ℤ) : kˣ) : k) * A) (((t ^ (2 : ℤ) : kˣ) : k) * B)
        (((t ^ (1 : ℤ) : kˣ) : k) * C) (((t ^ (0 : ℤ) : kˣ) : k) * D)
        (((t ^ (-1 : ℤ) : kˣ) : k) * E) (((t ^ (1 : ℤ) : kˣ) : k) * F) := by
  have e : ∀ a b : ModGL .G2 k, torusElt .G2 k g2ia t * (a * b) * (torusElt .G2 k g2ia t)⁻¹ =
      (torusElt .G2 k g2ia t * a * (torusElt .G2 k g2ia t)⁻¹) *
        (torusElt .G2 k g2ia t * b * (torusElt .G2 k g2ia t)⁻¹) := fun a b => by group
  simp only [g2N, e]
  rw [torus_a_conj t isRoot_g2r (-1) (by decide), torus_a_conj t isRoot_g2a 2 (by decide),
    torus_a_conj t isRoot_g2u 1 (by decide), torus_a_conj t isRoot_g2v 0 (by decide),
    torus_a_conj t isRoot_g2b (-1) (by decide), torus_a_conj t isRoot_g2c 1 (by decide)]

theorem orderOf_torusElt_r {t : kˣ} (ht : t ^ 3 = 1) (ht1 : t ≠ 1) :
    orderOf (torusElt .G2 k g2ir t) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : torusElt .G2 k g2ir t ^ 3 = 1 := by
    rw [show torusElt .G2 k g2ir t = torusEltHom .G2 k g2ir t from rfl, ← map_pow, ht, map_one]
  refine orderOf_eq_prime hpow fun h1 => ?_
  have hv := torus_r_v t (1 : k)
  rw [h1, one_mul, inv_one, mul_one, mul_one] at hv
  exact ht1 (Units.val_eq_one.1 (pinnedX_injective .G2 k g2v hv).symm)

end TorusA

section Weyl

variable {k : Type} [Field k] [CharP k 2]

local notation "X" => pinnedX Tag.G2 k


theorem le_g2LongRadical_of_conj {N : Subgroup (ModGL .G2 k)} (hNU : N ≤ posUnipotent .G2 k)
    (hn : ∀ g ∈ N, weylElt .G2 k g2ir 1 * g * (weylElt .G2 k g2ir 1)⁻¹ ∈ N) :
    N ≤ g2LongRadical k := by
  intro g hg
  obtain ⟨s, q, hq, rfl⟩ := exists_pinnedX_r_mul_of_mem_posUnipotent (hNU hg)
  have hq' : weylElt .G2 k g2ir 1 * q * (weylElt .G2 k g2ir 1)⁻¹ ∈ g2LongRadical k :=
    conj_mem_g2LongRadical (weylElt_mem_g2RankOne g2ir 1) hq
  have e : weylElt .G2 k g2ir 1 * (X g2r s * q) * (weylElt .G2 k g2ir 1)⁻¹ =
      X g2nr s * (weylElt .G2 k g2ir 1 * q * (weylElt .G2 k g2ir 1)⁻¹) := by
    rw [pinnedX_nr_eq]
    group
  have hU : X g2nr s ∈ posUnipotent .G2 k := by
    have h1 := hNU (hn _ hg)
    rw [e] at h1
    have h2 := (posUnipotent .G2 k).mul_mem h1
      ((posUnipotent .G2 k).inv_mem (g2LongRadical_le_posUnipotent hq'))
    rwa [mul_inv_cancel_right] at h2
  have hneg : X g2nr s ∈ negUnipotent .G2 k :=
    (le_iSup₂ (f := fun α (_ : α ∈ {α | IsRoot .G2 α ∧ height α < 0}) =>
      rootSubgroup .G2 k α) g2nr ⟨isRoot_g2nr, by decide⟩) (mem_rootSubgroup.2 ⟨s, rfl⟩)
  have h1 : X g2nr s = 1 := by
    have h := Subgroup.mem_inf.2 ⟨hU, hneg⟩
    rw [posUnipotent_inf_negUnipotent] at h
    exact Subgroup.mem_bot.1 h
  have hs : s = 0 := pinnedX_injective .G2 k g2nr (h1.trans (pinnedX_zero .G2 k g2nr).symm)
  rw [hs, pinnedX_zero, one_mul]
  exact hq

theorem eq_bot_of_commute_torusElt_a {t : kˣ} (ht : t ^ 3 = 1) (ht1 : t ≠ 1)
    {N : Subgroup (ModGL .G2 k)} (hNU : N ≤ posUnipotent .G2 k)
    (hc : ∀ g ∈ N, Commute (torusElt .G2 k g2ia t) g)
    (hr : ∀ g ∈ N, X g2r 1 * g * (X g2r 1)⁻¹ ∈ N) : N = ⊥ := by
  obtain ⟨h1, h2, h3⟩ := zpow_ne_one_of_cube ht ht1
  have key : ∀ {A B C D E F : k}, g2N A B C D E F ∈ N →
      A = 0 ∧ B = 0 ∧ C = 0 ∧ E = 0 ∧ F = 0 := by
    intro A B C D E F hg
    have h' := mul_inv_eq_of_eq_mul (hc _ hg).eq
    rw [torus_a_conj_g2N] at h'
    obtain ⟨hA, hB, hC, -, hE, hF⟩ := g2N_injective h'
    exact ⟨units_eq_zero h1 hA, units_eq_zero h2 hB, units_eq_zero h3 hC, units_eq_zero h1 hE,
      units_eq_zero h3 hF⟩
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent (hNU hg)
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := key hg
  have hg' := hr _ hg
  rw [pinnedX_inv_eq, conj_r] at hg'
  obtain ⟨-, -, -, hD, -⟩ := key hg'
  have hD' : D = 0 := by simpa using hD
  rw [hD', g2N_zero]
  exact Subgroup.one_mem _

end Weyl

section Perfect


theorem range_simpleRootSL2_le_perfectCore {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 4) (i : Fin Tag.G2.rank) :
    (simpleRootSL2 Tag.G2 k i).range ≤ perfectCore (parabolicSubgroup Tag.G2 k {i}) := by
  have hK4 : ∃ s : Finset k, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hk.ge
  have hSL : ⁅(⊤ : Subgroup (SL2 k)), ⊤⁆ = ⊤ := Group.isPerfect_def.mp
    (CFSG.LinearGroups.special_linear_dimension_two_perfect (K := k) hK4)
  have hp : ⁅(simpleRootSL2 Tag.G2 k i).range, (simpleRootSL2 Tag.G2 k i).range⁆ =
      (simpleRootSL2 Tag.G2 k i).range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hSL]
  calc (simpleRootSL2 Tag.G2 k i).range = perfectCore (simpleRootSL2 Tag.G2 k i).range :=
        (perfectCore_eq_self_of_perfect hp).symm
    _ ≤ perfectCore (parabolicSubgroup Tag.G2 k {i}) :=
        perfectCore_mono (C11P9A.range_simpleRootSL2_le_parabolic i)

end Perfect

section Sylow

theorem exists_conj_zpow_of_card {G : Type*} [Group G] [Finite G] {K : Subgroup G} {a : ℕ}
    (hK : Nat.card K = 2 ^ a * 60) {y h : G} (hy : y ∈ K) (hh : h ∈ K) (hy3 : orderOf y = 3)
    (hh3 : orderOf h = 3) : ∃ g ∈ K, ∃ n : ℤ, y = g * h ^ n * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ x : K, orderOf x = 3 →
      IsPGroup 3 (Subgroup.zpowers x) ∧ ¬ 3 ∣ (Subgroup.zpowers x).index := by
    intro x hx
    have hc : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
    refine ⟨IsPGroup.of_card (n := 1) (by rw [hc, pow_one]), fun h3 => ?_⟩
    have hmul := (Subgroup.zpowers x).card_mul_index
    rw [hc, hK] at hmul
    obtain ⟨m, hm⟩ := h3
    rw [hm] at hmul
    have h9 : 9 ∣ 2 ^ a * 60 := Dvd.intro m (by rw [← hmul]; ring)
    have hc9 : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
    have := hc9.dvd_of_dvd_mul_left h9
    omega
  have hy' : orderOf (⟨y, hy⟩ : K) = 3 := by rw [← Subgroup.orderOf_coe]; exact hy3
  have hh' : orderOf (⟨h, hh⟩ : K) = 3 := by rw [← Subgroup.orderOf_coe]; exact hh3
  obtain ⟨hPy, hiy⟩ := hsyl _ hy'
  obtain ⟨hPh, hih⟩ := hsyl _ hh'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K (hPh.toSylow hih) (hPy.toSylow hiy)
  have hmem : (⟨y, hy⟩ : K) ∈ ((g • hPh.toSylow hih : Sylow 3 K) : Subgroup K) := by
    rw [hg, IsPGroup.toSylow_coe]
    exact Subgroup.mem_zpowers _
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨p, hp, hpe⟩ := hmem
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ((IsPGroup.mem_toSylow hPh hih).1 hp)
  have hpe' : g * (⟨h, hh⟩ : K) ^ n * g⁻¹ = ⟨y, hy⟩ := hpe
  refine ⟨g, g.2, n, ?_⟩
  have := congrArg Subtype.val hpe'
  simpa using this.symm

end Sylow

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
