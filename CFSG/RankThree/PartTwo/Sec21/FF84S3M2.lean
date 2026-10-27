module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3M0

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup

theorem M2_mem_nor_zpowers {G : Type} [Group G] (g x : G)
    (h1 : g * x * g⁻¹ ∈ Subgroup.zpowers x) (h2 : g⁻¹ * x * g⁻¹⁻¹ ∈ Subgroup.zpowers x) :
    g ∈ Nor (Subgroup.zpowers x) := by
  have hpow : ∀ u : G, u * x * u⁻¹ ∈ Subgroup.zpowers x → ∀ j : ℤ,
      u * x ^ j * u⁻¹ ∈ Subgroup.zpowers x := by
    intro u hu j
    have hc := map_zpow (MulAut.conj u) x j
    simp only [MulAut.conj_apply] at hc
    rw [hc]
    exact zpow_mem hu j
  refine Subgroup.mem_normalizer_iff.2 (fun k => ?_)
  constructor
  · intro hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact hpow g h1 j
  · intro hk
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hk' : k = g⁻¹ * x ^ j * g⁻¹⁻¹ := by
      rw [hj]
      group
    rw [hk']
    exact hpow g⁻¹ h2 j

section M2
variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem M2_claimX (h : FF84Sec3 b L B b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    ∀ g ∈ Cen b ⊓ Cen b₁, g * b₂ * g⁻¹ ∈ Subgroup.zpowers b₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e', he'⟩ := M0_quot h hZ
  have hL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp h.hyp.quasi.1
  obtain ⟨θ, hθc, -, -⟩ := M0_T0_conj hL e'
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  obtain ⟨y₁, hy₁⟩ : ∃ y : ↥L, (y : G) = b₁ := ⟨⟨b₁, hb₁L⟩, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y : ↥L, (y : G) = b₂ := ⟨⟨b₂, hb₂L⟩, rfl⟩
  obtain ⟨hm₁, hm₂⟩ := he' y₁ y₂ hy₁ hy₂
  intro g hg
  obtain ⟨hgb, hgb1⟩ := Subgroup.mem_inf.1 hg
  have hgb1' : g * b₁ = b₁ * g := Subgroup.mem_centralizer_singleton_iff.1 hgb1
  have hgN : g ∈ Nor L := h.hyp.hLN hgb
  have hb₂conj : g * b₂ * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hgN b₂).1 hb₂L
  obtain ⟨y, hy⟩ : ∃ y : ↥L, (y : G) = g * b₂ * g⁻¹ := ⟨⟨_, hb₂conj⟩, rfl⟩
  have hconj := hθc g hgN y₂ y (by rw [hy, hy₂])
  have hconj1 := hθc g hgN y₁ y₁ (by
    rw [hy₁, hgb1']
    group)
  rw [hm₁] at hconj1
  have hcomm1 : θ ⟨g, hgN⟩ * m₁ = m₁ * θ ⟨g, hgN⟩ := by
    calc θ ⟨g, hgN⟩ * m₁ = θ ⟨g, hgN⟩ * m₁ * (θ ⟨g, hgN⟩)⁻¹ * θ ⟨g, hgN⟩ := by group
      _ = m₁ * θ ⟨g, hgN⟩ := by rw [← hconj1]
  have hA4 := A4_centralizer_m₁ _ hcomm1
  rw [hm₂] at hconj
  rcases hA4 with h4 | h4
  · have hA : e' (QuotientGroup.mk y) = e' (QuotientGroup.mk y₂) := Subtype.ext (by
      rw [hconj, h4, hm₂])
    have hyy : y = y₂ := M0_mk_inj hZ y y₂ (e'.injective hA)
    have h5 : g * b₂ * g⁻¹ = b₂ := by
      rw [← hy]
      exact (congrArg Subtype.val hyy).trans hy₂
    rw [h5]
    exact Subgroup.mem_zpowers b₂
  · have hinv : ((e' (QuotientGroup.mk y₂⁻¹) : alternatingGroup (Fin 8)) : P8) = m₂⁻¹ := by
      rw [QuotientGroup.mk_inv, map_inv, Subgroup.coe_inv, hm₂]
    have hA : e' (QuotientGroup.mk y) = e' (QuotientGroup.mk y₂⁻¹) := Subtype.ext (by
      rw [hconj, h4, hinv])
    have hyy : y = y₂⁻¹ := M0_mk_inj hZ y y₂⁻¹ (e'.injective hA)
    have h5 : g * b₂ * g⁻¹ = b₂⁻¹ := by
      rw [← hy]
      exact (congrArg Subtype.val hyy).trans (by rw [Subgroup.coe_inv, hy₂])
    rw [h5]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b₂)

theorem M2_part1 (h : FF84Sec3 b L B b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    Cen b ⊓ Cen b₁ ≤ Nor (Subgroup.zpowers b₂) := fun g hg =>
  M2_mem_nor_zpowers g b₂ (M2_claimX h hZ g hg) (M2_claimX h hZ g⁻¹ (Subgroup.inv_mem _ hg))

theorem M2_part2 (h : FF84Sec3 b L B b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    CenS (B ⊓ L) ≤ Nor (Subgroup.zpowers b) := by
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  obtain ⟨n, -, hn⟩ := P_monomial h (finRotate 3).symm (fun _ => 1)
  have e0 : (finRotate 3).symm 0 = 2 := by decide
  have e1 : (finRotate 3).symm 1 = 0 := by decide
  have e2 : (finRotate 3).symm 2 = 1 := by decide
  have hnb : n * b * n⁻¹ = b₂ := by simpa [e0] using hn 0
  have hnb1 : n * b₁ * n⁻¹ = b := by simpa [e1] using hn 1
  have hnb2 : n * b₂ * n⁻¹ = b₁ := by simpa [e2] using hn 2
  have hb_eq : b = n⁻¹ * b₂ * n := by
    rw [← hnb]
    group
  have hY : ∀ g ∈ CenS (B ⊓ L), g * b * g⁻¹ ∈ Subgroup.zpowers b := by
    intro g hg
    have hgb₁ : g * b₁ = b₁ * g := by
      have hmem : b₁ ∈ B ⊓ L := Subgroup.mem_inf.2 ⟨mem_B_b₁ h, hb₁L⟩
      exact (Subgroup.mem_centralizer_iff.1 hg b₁ hmem).symm
    have hgb₂ : g * b₂ = b₂ * g := by
      have hmem : b₂ ∈ B ⊓ L := Subgroup.mem_inf.2 ⟨mem_B_b₂ h, hb₂L⟩
      exact (Subgroup.mem_centralizer_iff.1 hg b₂ hmem).symm
    obtain ⟨h', hh'⟩ : ∃ h' : G, h' = n * g * n⁻¹ := ⟨_, rfl⟩
    have hcb : h' ∈ Cen b := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [hh', ← hnb1]
      calc n * g * n⁻¹ * (n * b₁ * n⁻¹) = n * (g * b₁) * n⁻¹ := by group
        _ = n * (b₁ * g) * n⁻¹ := by rw [hgb₁]
        _ = (n * b₁ * n⁻¹) * (n * g * n⁻¹) := by group
    have hcb1 : h' ∈ Cen b₁ := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [hh', ← hnb2]
      calc n * g * n⁻¹ * (n * b₂ * n⁻¹) = n * (g * b₂) * n⁻¹ := by group
        _ = n * (b₂ * g) * n⁻¹ := by rw [hgb₂]
        _ = (n * b₂ * n⁻¹) * (n * g * n⁻¹) := by group
    have hnor : h' ∈ Nor (Subgroup.zpowers b₂) :=
      M2_part1 h hZ (Subgroup.mem_inf.2 ⟨hcb, hcb1⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
      ((Subgroup.mem_normalizer_iff.1 hnor b₂).1 (Subgroup.mem_zpowers b₂))
    have key : g * b * g⁻¹ = n⁻¹ * (h' * b₂ * h'⁻¹) * n := by
      rw [hh', hb_eq]
      group
    have hpow := map_zpow (MulAut.conj n⁻¹) b₂ j
    simp only [MulAut.conj_apply, inv_inv] at hpow
    have hconjb : n⁻¹ * b₂ * n = b := hb_eq.symm
    rw [hconjb] at hpow
    rw [key, ← hj, hpow]
    exact zpow_mem (Subgroup.mem_zpowers b) j
  intro g hg
  exact M2_mem_nor_zpowers g b (hY g hg) (hY g⁻¹ (Subgroup.inv_mem _ hg))

theorem M2_norm (h : FF84Sec3 b L B b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    Cen b ⊓ Cen b₁ ≤ Nor (Subgroup.zpowers b₂) ∧ CenS (B ⊓ L) ≤ Nor (Subgroup.zpowers b) :=
  ⟨M2_part1 h hZ, M2_part2 h hZ⟩

end M2

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
