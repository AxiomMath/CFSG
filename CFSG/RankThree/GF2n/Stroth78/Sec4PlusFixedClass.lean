module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ

import CFSG.RankThree.GF2n.Stroth78.Sec3SevenFix

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

@[expose] noncomputable def CHbar (S : Setting z E F) (a : G) : Subgroup (Hbar z) :=
  ((Subgroup.centralizer ({a} : Set G)).subgroupOf (H z)).map
    (QuotientGroup.mk' ((Q z).subgroupOf (H z)))

theorem mem_CHbar_iff (S : Setting z E F) (a : G) (y : Hbar z) :
    y ∈ CHbar S a ↔ ∃ c : ↥(H z), (c : G) ∈ Subgroup.centralizer ({a} : Set G) ∧
      (QuotientGroup.mk c : Hbar z) = y := by
  unfold CHbar
  constructor
  · intro hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨c, Subgroup.mem_subgroupOf.mp hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact Subgroup.mem_map.mpr ⟨c, Subgroup.mem_subgroupOf.mpr hc, rfl⟩

private noncomputable def stabCommHom (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    {Y : Subgroup (Hbar z)}
    (hfix : ∀ y ∈ Y, rhoLin S y (aVec S haQ) = aVec S haQ)
    (hZ : ∀ y ∈ Y, ∀ u : ↥(ZQ z), rhoZ S y u = u) :
    ↥(Y.comap (QuotientGroup.mk' ((Q z).subgroupOf (H z)))) →* ↥(ZQ z) where
  toFun ℓ := ⟨⁅a, ((ℓ : ↥(H z)) : G)⁆,
    commutator_mem_ZQ_of_fix S (ℓ : ↥(H z)) ⟨a, haQ⟩ (hfix _ (Subgroup.mem_comap.mp ℓ.2))⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := by
    intro ℓ ℓ'
    apply Subtype.ext
    have hc : ((ℓ : ↥(H z)) : G) * ⁅a, ((ℓ' : ↥(H z)) : G)⁆ * ((ℓ : ↥(H z)) : G)⁻¹ =
        ⁅a, ((ℓ' : ↥(H z)) : G)⁆ := by
      have hmem : ⁅a, ((ℓ' : ↥(H z)) : G)⁆ ∈ ZQ z :=
        commutator_mem_ZQ_of_fix S (ℓ' : ↥(H z)) ⟨a, haQ⟩
          (hfix _ (Subgroup.mem_comap.mp ℓ'.2))
      have h1 := congrArg Subtype.val
        (hZ _ (Subgroup.mem_comap.mp ℓ.2) ⟨⁅a, ((ℓ' : ↥(H z)) : G)⁆, hmem⟩)
      have h2 := rhoZ_mk S (ℓ : ↥(H z)) ⟨⁅a, ((ℓ' : ↥(H z)) : G)⁆, hmem⟩
      exact h2.symm.trans h1
    change ⁅a, ((ℓ : ↥(H z)) : G) * ((ℓ' : ↥(H z)) : G)⁆ =
      ⁅a, ((ℓ : ↥(H z)) : G)⁆ * ⁅a, ((ℓ' : ↥(H z)) : G)⁆
    rw [← hc]
    simp only [commutatorElement_def]
    group

theorem mem_CHbar_of_mem_commutator (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    {Y : Subgroup (Hbar z)}
    (hfix : ∀ y ∈ Y, rhoLin S y (aVec S haQ) = aVec S haQ)
    (hZ : ∀ y ∈ Y, ∀ u : ↥(ZQ z), rhoZ S y u = u)
    {y : Hbar z} (hy : y ∈ ⁅Y, Y⁆) : y ∈ CHbar S a := by
  set π := QuotientGroup.mk' ((Q z).subgroupOf (H z)) with hπ
  set Yhat : Subgroup ↥(H z) := Y.comap π with hYhat
  have hmap : Yhat.map π = Y :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Y
  have hcomm : ⁅Y, Y⁆ = (⁅Yhat, Yhat⁆).map π := by
    rw [Subgroup.map_commutator, hmap]
  rw [hcomm] at hy
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
  refine (mem_CHbar_iff S a _).mpr ⟨c, ?_, rfl⟩
  have hle : ⁅Yhat, Yhat⁆ ≤ (Subgroup.centralizer ({a} : Set G)).subgroupOf (H z) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff_commutator_eq_one]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    let φ := stabCommHom S haQ hfix hZ
    have h1 : φ ⁅(⟨g₁, hg₁⟩ : ↥Yhat), ⟨g₂, hg₂⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      apply Subtype.ext
      have hm1 := (φ ⟨g₁, hg₁⟩).2
      have hm2 := (φ ⟨g₂, hg₂⟩).2
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hm2).2 _
        (Subgroup.mem_inf.mp hm1).1)
    have h2 : ⁅a, (((⁅(⟨g₁, hg₁⟩ : ↥Yhat), ⟨g₂, hg₂⟩⁆ : ↥Yhat) : ↥(H z)) : G)⁆ = 1 :=
      congrArg Subtype.val h1
    exact h2
  exact Subgroup.mem_subgroupOf.mp (hle hc)

theorem le_CHbar_of_perfect (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    {Y : Subgroup (Hbar z)} (hY : ⁅Y, Y⁆ = Y)
    (hfix : ∀ y ∈ Y, rhoLin S y (aVec S haQ) = aVec S haQ)
    (hZ : ∀ y ∈ Y, ∀ u : ↥(ZQ z), rhoZ S y u = u) : Y ≤ CHbar S a := by
  intro y hy
  have hy' : y ∈ ⁅Y, Y⁆ := by rw [hY]; exact hy
  exact mem_CHbar_of_mem_commutator S haQ hfix hZ hy'

end CFSG.RankThree.GF2n.Stroth78
