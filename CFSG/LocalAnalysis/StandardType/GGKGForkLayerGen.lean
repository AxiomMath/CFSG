module

public import CFSG.LocalAnalysis.StandardType.GGLayerChevAdjoint
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem ggKG_layer_of_chevSimple
    {R : Type} [Group R] [Finite R] (hS : IsSimpleGroup R) (hnc : ∃ a b : R, a * b ≠ b * a)
    (hchev : IsChevSimple 2 R) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : R} (hap : a ^ p = 1)
    {J : Subgroup R} (hJperf : ⁅J, J⁆ = J) (hJa : J ≤ Subgroup.centralizer ({a} : Set R)) :
    J ≤ LargeEvenLayer (Subgroup.centralizer ({a} : Set R)) := by
  let Ec : Subgroup (MulAut R) := Subgroup.zpowers (MulAut.conj a)
  have hmap : (Subgroup.zpowers a).map (MulAut.conj : R →* MulAut R) = Ec := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [map_zpow]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ⟨a ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, by rw [map_zpow]⟩
  have hEcent : CFSG.LocalAnalysis.GLTheoremA.I142.centFix Ec =
      Subgroup.centralizer ({a} : Set R) := by
    have h1 := LayerCores.centFix_map_conj (Subgroup.zpowers a)
    rw [hmap] at h1
    rw [h1]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hx a (Subgroup.mem_zpowers a)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_left (hx a (Set.mem_singleton a)) k).eq
  have hEp : IsPGroup p Ec := by
    have hconjp : (MulAut.conj a : MulAut R) ^ p = 1 := by
      rw [← map_pow, hap, map_one]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hconjp) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hEc : ∀ x ∈ Ec, ∀ y ∈ Ec, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_add, ← zpow_add, add_comm]
  have hJle : J ≤ CFSG.LocalAnalysis.GLTheoremA.I142.centFix Ec := by
    rw [hEcent]
    exact hJa
  have hmain := LayerAbelian.lieSemisimpleCentAbelian R hS hnc hchev p hp hp2 Ec hEp hEc J hJle hJperf
  rw [hEcent] at hmain
  rw [CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer]
  exact hmain

end CFSG.StandardType
