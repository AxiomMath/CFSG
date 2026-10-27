module

public import CFSG.Sporadic.Recognition.JankoWongLemma14Normalizer

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

theorem exists_mem_normalizer_of_lt {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B A : Subgroup G} (hB : IsPGroup p B) (hAB : A ≤ B) (hne : A ≠ B) :
    ∃ g ∈ B, g ∉ A ∧ g ∈ normalizer (A : Set G) := by
  classical
  have : Group.IsNilpotent ↥B := hB.isNilpotent
  have hNC : NormalizerCondition ↥B := Group.normalizerCondition_of_isNilpotent
  set H₀ : Subgroup ↥B := A.subgroupOf B with hH₀
  have hlt : H₀ < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hAB
    intro x hx
    have : (⟨x, hx⟩ : ↥B) ∈ H₀ := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨g₀, hg₀N, hg₀H⟩ := IsConcreteLE.exists_of_lt (hNC H₀ hlt)
  refine ⟨(g₀ : G), g₀.2, fun hmem => hg₀H (Subgroup.mem_subgroupOf.mpr hmem), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhB : h ∈ B := hAB hh
    have := (Subgroup.mem_normalizer_iff.mp hg₀N ⟨h, hhB⟩).mp (Subgroup.mem_subgroupOf.mpr hh)
    exact Subgroup.mem_subgroupOf.mp this
  · intro hh
    have hhB : h ∈ B := by
      have h1 : (g₀ : G) * h * (g₀ : G)⁻¹ ∈ B := hAB hh
      have := B.mul_mem (B.mul_mem (B.inv_mem g₀.2) h1) g₀.2
      simpa [mul_assoc] using this
    have := (Subgroup.mem_normalizer_iff.mp hg₀N ⟨h, hhB⟩).mpr (Subgroup.mem_subgroupOf.mpr hh)
    exact Subgroup.mem_subgroupOf.mp this

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem Bg_le_NG :
    c.Bg ≤ c.NG := c.Bg_le_NH.trans c.NH_le_NG

theorem conj_z_eq_of_normalizes_Bg {g : G} (hg : g ∈ normalizer (c.Bg : Set G)) :
    g * S.z * g⁻¹ = S.z := by
  have hcenter := CFSG.QuasiDihedralFusion.centerOf_eq_zpowers_z (n := 4) (by norm_num)
    (c.Bg : Subgroup G) c.BgEquiv
  have hz : CFSG.Semidihedral.FocalFusion.ambientHom 4 (c.Bg : Subgroup G) c.BgEquiv
      (CFSG.Semidihedral.z 4) = S.z := by
    rw [← c.sdEmb_r_pow_four]
    show c.sdEmb (CFSG.Semidihedral.r 4 ^ CFSG.Semidihedral.half 4) =
      c.sdEmb (CFSG.Semidihedral.r 4 ^ 4)
    have h4 : CFSG.Semidihedral.half 4 = 4 := by norm_num [CFSG.Semidihedral.half]
    rw [h4]
  rw [hz] at hcenter
  have hmem : g * S.z * g⁻¹ ∈ CFSG.QuasiDihedralFusion.centerOf (c.Bg : Subgroup G) := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg S.z).mp c.z_mem_Bg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g ∈ c.Bg := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer (c.Bg : Set G)).inv_mem hg) y).mp hy
      simpa using this
    have hzc : (g⁻¹ * y * g) * S.z = S.z * (g⁻¹ * y * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp (c.Bg_le_H hy')
    calc y * (g * S.z * g⁻¹) = g * ((g⁻¹ * y * g) * S.z) * g⁻¹ := by group
      _ = g * (S.z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hzc]
      _ = g * S.z * g⁻¹ * y := by group
  rw [hcenter] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hmod := zpow_mod_orderOf S.z k
  rw [S.order_z] at hmod
  have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h2 with h0 | h1
  · exfalso
    rw [h0, zpow_zero] at hmod
    have : g * S.z * g⁻¹ = 1 := by rw [← hk, ← hmod]
    have h3 : S.z = 1 := by
      calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    exact z_ne_one' (S := S) h3
  · rw [h1, zpow_one] at hmod
    rw [← hk]
    exact hmod.symm

theorem isMax_Bg
    {B₁ : Subgroup G} (h2 : IsPGroup 2 B₁) (hB₁ : B₁ ≤ c.NG) (hBB : c.Bg ≤ B₁) :
    Nat.card B₁ ≤ Nat.card c.Bg := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push Not at hlt
  have hne : c.Bg ≠ B₁ := fun e => by rw [e] at hlt; exact lt_irrefl _ hlt
  obtain ⟨g, hgB, hgBg, hgN⟩ := exists_mem_normalizer_of_lt (p := 2) h2 hBB hne
  have hgz := c.conj_z_eq_of_normalizes_Bg hgN
  have hgH : g ∈ S.H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * S.z = (g * S.z * g⁻¹) * g := by group
      _ = S.z * g := by rw [hgz]
  have hgNH : g ∈ c.NH := c.NG_inf_H_le_NH ⟨hB₁ hgB, hgH⟩
  set R : Subgroup G := Subgroup.closure ((c.Bg : Set G) ∪ {g}) with hR
  have hRNH : R ≤ c.NH := (Subgroup.closure_le _).mpr
    (Set.union_subset c.Bg_le_NH (Set.singleton_subset_iff.mpr hgNH))
  have hRB₁ : R ≤ B₁ := (Subgroup.closure_le _).mpr
    (Set.union_subset hBB (Set.singleton_subset_iff.mpr hgB))
  have hR2 : IsPGroup 2 R := h2.to_le hRB₁
  have hBgR : c.Bg ≤ R := fun y hy => Subgroup.subset_closure (Or.inl hy)
  have hgR : g ∈ R := Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
  have hgt : 16 < Nat.card R := by
    by_contra hle
    push Not at hle
    have : c.Bg = R := Subgroup.eq_of_le_of_card_ge hBgR (by rw [c.card_Bg]; exact hle)
    exact hgBg (this ▸ hgR)
  have hdvd : Nat.card R ∣ 144 := by
    rw [← c.card_NH]; exact Subgroup.card_dvd_of_le hRNH
  rw [hk] at hgt hdvd
  have hk5 : 5 ≤ k := by
    by_contra hk5
    push Not at hk5
    interval_cases k <;> simp at hgt
  have : 2 ^ 5 ∣ 144 := (pow_dvd_pow 2 hk5).trans hdvd
  norm_num at this

theorem card_sylow_NG
    (T : Sylow 2 ↥c.NG) : Nat.card T = 16 := by
  rw [sylow_card_eq_of_max (C := c.NG) (A := c.Bg) c.isPGroup_Bg c.Bg_le_NG
    (fun B hB hBC hAB => c.isMax_Bg hB hBC hAB) T, c.card_Bg]

theorem factorization_two_NG :
    (Nat.card c.NG).factorization 2 = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥c.NG) := inferInstance
  have h := c.card_sylow_NG T
  rw [T.card_eq_multiplicity] at h
  exact Nat.pow_right_injective (le_refl 2) (show 2 ^ (Nat.card c.NG).factorization 2 = 2 ^ 4 by
    rw [h])

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
