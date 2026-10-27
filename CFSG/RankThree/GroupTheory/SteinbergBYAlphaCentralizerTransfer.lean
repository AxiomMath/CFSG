module

public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree.GroupTheory

variable {G : Type*} [Group G]

theorem inSubgroup_pCore_inf_centralizer_mono (p : ℕ) {C N : Subgroup G} (hCN : C ≤ N)
    (hNC : N ≤ Subgroup.normalizer (C : Set G)) (b : G) :
    inSubgroup (pCore p) (C ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      inSubgroup (pCore p) (N ⊓ Subgroup.centralizer ({b} : Set G)) :=
  inSubgroup_pCore_mono (inf_le_inf_right _ hCN)
    fun _ hg => mem_normalizer_inf (hNC hg.1) (Subgroup.le_normalizer hg.2)

theorem map_twoCoreX_subgroupOf_le {C N B : Subgroup G} (hCN : C ≤ N)
    (hNC : N ≤ Subgroup.normalizer (C : Set G)) (hBC : B ≤ C) :
    (twoCoreX (B.subgroupOf C)).map C.subtype ≤ (twoCoreX (B.subgroupOf N)).map N.subtype := by
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, mem_twoCoreX_iff] at hy
  refine ⟨⟨y, hCN y.2⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_twoCoreX_iff]
  intro b hb hb1
  have hbC : (b : G) ∈ C := hBC hb
  have hb' : (⟨b, hbC⟩ : C) ∈ B.subgroupOf C := hb
  have hne : (⟨b, hbC⟩ : C) ≠ 1 := fun h =>
    hb1 (Subtype.ext (by simpa using congrArg Subtype.val h))
  have hmem := Subgroup.mem_map_of_mem C.subtype (hy _ hb' hne)
  rw [map_subtype_inSubgroup_pCore_centralizer] at hmem
  have hmem' := inSubgroup_pCore_inf_centralizer_mono 2 hCN hNC b hmem
  rw [← map_subtype_inSubgroup_pCore_centralizer] at hmem'
  obtain ⟨z, hz, hzy⟩ := hmem'
  have hzy' : z = ⟨y, hCN y.2⟩ := Subtype.ext hzy
  rwa [← hzy']

theorem map_twoCoreJ_subgroupOf_le {C N B : Subgroup G} (hCN : C ≤ N)
    (hNC : N ≤ Subgroup.normalizer (C : Set G)) (hBC : B ≤ C) :
    (twoCoreJ (B.subgroupOf C)).map C.subtype ≤ (twoCoreJ (B.subgroupOf N)).map N.subtype := by
  rw [twoCoreJ, twoCoreJ]
  simp only [Subgroup.map_iSup, Subgroup.map_commutator,
    map_subtype_inSubgroup_pCore_centralizer, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hBC, inf_eq_left.mpr (hBC.trans hCN)]
  refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
  have hbN : (b : G) ∈ N := hCN b.2
  have hb' : (⟨b, hbN⟩ : N) ∈ B.subgroupOf N := hb
  have hne : (⟨b, hbN⟩ : N) ≠ 1 := fun h =>
    hb1 (Subtype.ext (by simpa using congrArg Subtype.val h))
  exact le_iSup₂_of_le (⟨b, hbN⟩ : N) hb' (le_iSup_of_le hne
    (Subgroup.commutator_mono (inSubgroup_pCore_inf_centralizer_mono 2 hCN hNC b) le_rfl))

theorem map_twoCoreAlpha_subgroupOf_le {C N B : Subgroup G} (hCN : C ≤ N)
    (hNC : N ≤ Subgroup.normalizer (C : Set G)) (hBC : B ≤ C) :
    (twoCoreAlpha (B.subgroupOf C)).map C.subtype ≤
      (twoCoreAlpha (B.subgroupOf N)).map N.subtype := by
  rw [twoCoreAlpha, twoCoreAlpha, Subgroup.map_sup, Subgroup.map_sup]
  exact sup_le_sup (map_twoCoreJ_subgroupOf_le hCN hNC hBC)
    (map_twoCoreX_subgroupOf_le hCN hNC hBC)

theorem inSubgroup_pCore_two_le_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : G}
    (hc : orderOf c = p) {N : Subgroup G} (hcN : c ∈ N)
    (hN : N ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    inSubgroup (pCore 2) N ≤ Subgroup.centralizer ({c} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  set O := inSubgroup (pCore 2) N
  have hZ : IsPGroup p (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hdis : Disjoint O (Subgroup.zpowers c) :=
    IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) O _ (isPGroup_inSubgroup_pCore 2 N) hZ
  have hxN : x ∈ N := inSubgroup_pCore_le 2 N hx
  have h1 : x * c * x⁻¹ * c⁻¹ ∈ O := by
    have hcO : c * x⁻¹ * c⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_inSubgroup_pCore 2 N hcN) x⁻¹).mp
        (inv_mem hx)
    have := mul_mem hx hcO
    simpa only [mul_assoc] using this
  have h2 : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers c :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hN hxN) c).mp (Subgroup.mem_zpowers c))
      (inv_mem (Subgroup.mem_zpowers c))
  have h3 : x * c * x⁻¹ * c⁻¹ = 1 := Subgroup.disjoint_def.mp hdis h1 h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact Subgroup.mem_centralizer_singleton_iff.mpr h3

theorem twoCoreAlpha_transfer_of_le_normalizer {C N : Subgroup G} (hCN : C ≤ N)
    (hNC : N ≤ Subgroup.normalizer (C : Set G)) (hO : inSubgroup (pCore 2) N ≤ C) :
    inSubgroup (pCore 2) C = inSubgroup (pCore 2) N ∧
      ∀ B : Subgroup G, B ≤ C →
        (twoCoreAlpha (B.subgroupOf C)).map C.subtype ≤
            (twoCoreAlpha (B.subgroupOf N)).map N.subtype ∧
          (twoCoreAlpha (B.subgroupOf N) ≤ pCore 2 N →
            twoCoreAlpha (B.subgroupOf C) ≤ pCore 2 C) := by
  have hOeq : inSubgroup (pCore 2) C = inSubgroup (pCore 2) N := by
    rw [inSubgroup_pCore_eq_inf hCN hNC, inf_eq_right.mpr hO]
  refine ⟨hOeq, fun B hBC => ⟨map_twoCoreAlpha_subgroupOf_le hCN hNC hBC, fun h => ?_⟩⟩
  have h' := (map_twoCoreAlpha_subgroupOf_le hCN hNC hBC).trans
    (Subgroup.map_mono (f := N.subtype) h)
  change _ ≤ inSubgroup (pCore 2) N at h'
  rw [← hOeq] at h'
  exact (Subgroup.map_le_map_iff_of_injective C.subtype_injective).mp h'

theorem alpha_normal_odd_cyclic_centralizer_transfer_normalizer {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {c : G} (hc : orderOf c = p) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      ((Subgroup.centralizer ({c} : Set G)).subgroupOf
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))).Normal ∧
      inSubgroup (pCore 2) (Subgroup.centralizer ({c} : Set G)) =
        inSubgroup (pCore 2) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
      ∀ B : Subgroup G, B ≤ Subgroup.centralizer ({c} : Set G) →
        (twoCoreAlpha (B.subgroupOf (Subgroup.centralizer ({c} : Set G)))).map
            (Subgroup.centralizer ({c} : Set G)).subtype ≤
          (twoCoreAlpha (B.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)))).map
            (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype ∧
        (twoCoreAlpha (B.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ≤
            pCore 2 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
          twoCoreAlpha (B.subgroupOf (Subgroup.centralizer ({c} : Set G))) ≤
            pCore 2 (Subgroup.centralizer ({c} : Set G))) := by
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hNdef
  have hCN : C ≤ N := by
    rw [hCdef, centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.centralizer_le_normalizer _
  have hNC : N ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hCdef, centralizer_singleton_eq_centralizer_zpowers, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro hx z hz
      have hz' : g⁻¹ * z * g ∈ Subgroup.zpowers c :=
        (Subgroup.mem_normalizer_iff''.mp hg z).mp hz
      have := hx _ hz'
      calc z * (g * x * g⁻¹) = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by rw [this]
        _ = g * x * g⁻¹ * z := by group
    · intro hx z hz
      have hz' : g * z * g⁻¹ ∈ Subgroup.zpowers c :=
        (Subgroup.mem_normalizer_iff.mp hg z).mp hz
      have := hx _ hz'
      calc z * x = g⁻¹ * ((g * z * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * z * g⁻¹)) * g := by rw [this]
        _ = x * z := by group
  have hO : inSubgroup (pCore 2) N ≤ C :=
    inSubgroup_pCore_two_le_centralizer hp hp2 hc
      (Subgroup.le_normalizer (Subgroup.mem_zpowers c)) le_rfl
  obtain ⟨hOeq, hB⟩ := twoCoreAlpha_transfer_of_le_normalizer hCN hNC hO
  exact ⟨hCN, (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr hNC, hOeq, hB⟩

end CFSG.RankThree.GroupTheory.SteinbergBY
