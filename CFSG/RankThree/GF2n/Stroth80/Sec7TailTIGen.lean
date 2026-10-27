module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIConfig
public import CFSG.RankThree.GF2n.Basic
public import CFSG.CGT.Timmesfeld75.WCBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75

variable {Y : Type*} [Group Y] [Finite Y] {V N : Subgroup Y}

theorem conjSubgroup_iSup_eq' {ι : Sort*} (k : Y) (s : ι → Subgroup Y) :
    conjSubgroup k (⨆ i, s i) = ⨆ i, conjSubgroup k (s i) :=
  Subgroup.map_iSup (MulAut.conj k).toMonoidHom s

theorem TIConfig.gen_of_inv (h : TIConfig ⊤ V N)
    (hex : ∃ g : Y, conjSubgroup g V ≤ N ∧ conjSubgroup g V ≠ V)
    (hInv : ∀ A : Subgroup Y, V ≤ A → A ≤ N →
      (∀ k ∈ NormIn ⊤ V, k ∈ normalizer (A : Set Y)) → A ≠ N →
      ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    N = ⨆ (g : Y) (_ : conjSubgroup g V ≤ N), conjSubgroup g V := by
  set N₀ : Subgroup Y := ⨆ (g : Y) (_ : conjSubgroup g V ≤ N), conjSubgroup g V with hN₀
  have hN₀N : N₀ ≤ N := iSup₂_le fun g hg => hg
  have hVN₀ : V ≤ N₀ := by
    have h1 : conjSubgroup (1 : Y) V ≤ N := by
      rw [conjSubgroup_one]; exact h.V_le_N
    have h2 : conjSubgroup (1 : Y) V ≤ N₀ := le_iSup₂_of_le (1 : Y) h1 le_rfl
    rwa [conjSubgroup_one] at h2
  have hne : V ≠ N₀ := by
    intro hVeq
    obtain ⟨g, hgN, hgne⟩ := hex
    have hg0 : conjSubgroup g V ≤ N₀ := le_iSup₂_of_le g hgN le_rfl
    rw [← hVeq] at hg0
    apply hgne
    exact Subgroup.eq_of_le_of_card_ge hg0 (by rw [CFSG.RankThree.GF2n.card_conjSubgroup])
  have hinv : ∀ k ∈ NormIn ⊤ V, k ∈ normalizer (N₀ : Set Y) := by
    intro k hk
    have hkN : k ∈ normalizer (N : Set Y) := h.N_normal k hk
    have hle : conjSubgroup k N₀ ≤ N₀ := by
      rw [hN₀, conjSubgroup_iSup_eq']
      refine iSup_le fun g => ?_
      rw [conjSubgroup_iSup_eq']
      refine iSup_le fun hg => ?_
      have hkg : conjSubgroup k (conjSubgroup g V) ≤ N := by
        calc conjSubgroup k (conjSubgroup g V) ≤ conjSubgroup k N := Subgroup.map_mono hg
          _ = N := CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mpr hkN
      rw [conjSubgroup_conjSubgroup] at hkg ⊢
      exact le_iSup₂_of_le (k * g) hkg le_rfl
    refine mem_normalizer_of_conj_mem fun z hz => hle ?_
    rw [mem_conjSubgroup, show k⁻¹ * (k * z * k⁻¹) * k = z by group]
    exact hz
  by_contra hNne
  have hN0ne : N₀ ≠ N := fun e => hNne e.symm
  have hab := hInv N₀ hVN₀ hN₀N hinv hN0ne
  have hKle : N₀ ≤ NormIn ⊤ V := hN₀N.trans h.N_le
  have hEq := h.maxAb N₀ hVN₀ hKle hinv hab
  exact hne hEq.symm

end CFSG.RankThree.GF2n.Stroth80
