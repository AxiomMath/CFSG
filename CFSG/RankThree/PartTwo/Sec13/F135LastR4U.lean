module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Abs
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Facts
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r4k_mem_normalizer_A {G : Type} [Group G] [Finite G] {u : G} {Y : Subgroup G} {k : G}
    (hkY : k ∈ Subgroup.centralizer (Y : Set G)) (hku : k ∈ Subgroup.centralizer ({u} : Set G)) :
    k ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
  have hkC : k ∈ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) :=
    r5gl_mem_centralizer_sup hkY hku
  have hkD : k ∈ (⊤ : Subgroup G) ⊓
      Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, hkC⟩
  have hkiD : k⁻¹ ∈ (⊤ : Subgroup G) ⊓
      Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, inv_mem hkC⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact r5gl_A_conj hkD hx
  · intro hx
    have h := r5gl_A_conj hkiD hx
    have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
    rwa [e] at h

theorem r4_u_nontrivial {G : Type} [Group G] [Finite G] {u : G} (hu2 : u * u = 1)
    {Y D U : Subgroup G} (hu : u ∈ cM Y)
    (hU : U = ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
        Subgroup.centralizer (Y : Set G),
      D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G)⁆)
    (R : Subgroup (cM Y)) [R.Normal] (hR : Odd (Nat.card R))
    (J : Subgroup (cM Y ⧸ R)) (hJp : Group.IsPerfect J) (hJ1 : J ≠ ⊥)
    (hJU : ⁅J, (U.subgroupOf (cM Y)).map (QuotientGroup.mk' R)⁆ = J) :
    ¬ (((⟨u, hu⟩ : cM Y) : cM Y ⧸ R) ∈ Subgroup.centralizer (J : Set (cM Y ⧸ R))) := by
  have hUle : U ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G) := by
    rw [hU]
    exact r5gl_commutator_le (fun b hb x hx => r5gl_A_conj hb hx)
  have hpA : IsPGroup 2 (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G) : Subgroup G) :=
    (CFSG.RankThree.PartTwo.Sec13.F135Last.isPGroup_pCoreOf 2
      (Subgroup.centralizer ({u} : Set G))).to_inf_left
  have hA₀2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G) : Subgroup G).subgroupOf (cM Y)) :=
    hpA.comap_subtype (K := cM Y)
  have hUA : U.subgroupOf (cM Y) ≤ (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G) : Subgroup G).subgroupOf (cM Y) :=
    Subgroup.subgroupOf_mono (cM Y) hUle
  have hmono : ⁅J, (U.subgroupOf (cM Y)).map (QuotientGroup.mk' R)⁆ ≤
      ⁅J, ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
        Subgroup.centralizer (Y : Set G) : Subgroup G).subgroupOf (cM Y)).map
        (QuotientGroup.mk' R)⁆ :=
    Subgroup.commutator_mono le_rfl (Subgroup.map_mono hUA)
  have hJU' : J ≤ ⁅J, ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G) : Subgroup G).subgroupOf (cM Y)).map
      (QuotientGroup.mk' R)⁆ :=
    (le_of_eq hJU.symm).trans hmono
  have hA₀N : ∀ k : cM Y, k * (⟨u, hu⟩ : cM Y) = (⟨u, hu⟩ : cM Y) * k →
      k ∈ Subgroup.normalizer (((CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
        Subgroup.centralizer (Y : Set G) : Subgroup G).subgroupOf (cM Y) : Subgroup (cM Y)) :
        Set (cM Y)) := by
    intro k hk
    have hku : (k : G) * u = u * (k : G) := congrArg Subtype.val hk
    exact r5g_subgroupOf_normalizer (cM Y) _
      (r4k_mem_normalizer_A (u := u) (Y := Y) k.2 (Subgroup.mem_centralizer_singleton_iff.mpr hku))
  intro hcent
  have hc : ∀ j ∈ J, ((⟨u, hu⟩ : cM Y) : cM Y ⧸ R) * j = j * ((⟨u, hu⟩ : cM Y) : cM Y ⧸ R) :=
    fun j hj => (Subgroup.mem_centralizer_iff.mp hcent j hj).symm
  exact r4_abs_u R hR (u := ⟨u, hu⟩) (Subtype.ext hu2) _ hA₀2 hA₀N J hJp hJ1 hJU' hc

end CFSG.RankThree.PartTwo.Sec13.F135Last
