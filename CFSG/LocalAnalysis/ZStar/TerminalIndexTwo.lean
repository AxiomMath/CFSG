module

public import Mathlib.GroupTheory.Schreier
public import CFSG.LocalAnalysis.ZStar.TransferReduction

public section

namespace CFSG

namespace ZStar

open ZStar.TransferReduction

universe u

variable {G : Type u} [Group G] [Fintype G]

@[expose] def UniqueInvolutionIn (P : Subgroup G) (t : G) : Prop :=
  ∀ s : G, s ∈ P → s ≠ 1 → s * s = 1 → s = t

theorem uniqueInvolutionIn_or_exists_distinct
    (P : Subgroup G) (t : G) :
    UniqueInvolutionIn P t ∨
      ∃ s : G, s ∈ P ∧ s ≠ 1 ∧ s * s = 1 ∧ s ≠ t := by
  classical
  by_cases h : UniqueInvolutionIn P t
  · exact Or.inl h
  · right
    unfold UniqueInvolutionIn at h
    push Not at h
    exact h

private theorem odd_card_commutator_of_terminal_index_two_unique
    {t : G} (_ht1 : t ≠ 1) (_ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup G, H.Normal → t ∈ H → H = ⊤)
    (hindex : (commutator G).index = 2)
    (P : Sylow 2 G) (_htP : t ∈ P)
    (hunique : UniqueInvolutionIn (P : Subgroup G) t) :
    Odd (Nat.card (commutator G)) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hdvd : 2 ∣ Nat.card (commutator G) := even_iff_two_dvd.mp heven
  obtain ⟨x, hxorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := commutator G) 2 hdvd
  have hxne : x ≠ 1 := by
    intro hx
    subst x
    simp at hxorder
  have hxneG : (x : G) ≠ 1 := by
    intro hx
    exact hxne (Subtype.ext hx)
  have hxsq : (x : G) * (x : G) = 1 := by
    have hpow := pow_orderOf_eq_one x
    rw [hxorder] at hpow
    simpa [pow_two] using congrArg Subtype.val hpow
  have hzp : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
    isPGroup_zpowers_two_of_sq_eq_one (x : G) hxsq
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hxQ : (x : G) ∈ (Q : Subgroup G) :=
    hQ (Subgroup.mem_zpowers (x : G))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  let s : G := g * (x : G) * g⁻¹
  have hsP : s ∈ (P : Subgroup G) := by
    have hsSmul : g * (x : G) * g⁻¹ ∈ (g • Q : Sylow 2 G) := by
      exact (Sylow.equivSMul Q g ⟨(x : G), hxQ⟩).property
    rw [hg] at hsSmul
    exact hsSmul
  have hsne : s ≠ 1 := by
    intro hs
    apply hxneG
    calc
      (x : G) = g⁻¹ * s * g := by
        dsimp [s]
        group
      _ = 1 := by rw [hs]; simp
  have hssq : s * s = 1 := by
    dsimp [s]
    calc
      (g * (x : G) * g⁻¹) * (g * (x : G) * g⁻¹) =
          g * ((x : G) * (x : G)) * g⁻¹ := by group
      _ = 1 := by rw [hxsq]; simp
  have hst : s = t := hunique s hsP hsne hssq
  have hsComm : s ∈ commutator G := by
    exact (inferInstance : (commutator G).Normal).conj_mem
      (x : G) x.property g
  have htComm : t ∈ commutator G := by
    rw [← hst]
    exact hsComm
  have htop : commutator G = ⊤ :=
    hmin (commutator G) inferInstance htComm
  rw [htop] at hindex
  simp at hindex

theorem zStar_of_terminal_index_two_unique
    {t : G} (_ht : Isolated t) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup G, H.Normal → t ∈ H → H = ⊤)
    (hindex : (commutator G).index = 2)
    (P : Sylow 2 G) (htP : t ∈ P)
    (hunique : UniqueInvolutionIn (P : Subgroup G) t) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  refine ⟨commutator G, inferInstance,
    odd_card_commutator_of_terminal_index_two_unique
      ht1 ht2 hmin hindex P htP hunique, ?_⟩
  intro g
  rw [← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator (by simp) (by simp)

theorem terminal_index_two_zStar_or_exists_distinct
    {t : G} (ht : Isolated t) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup G, H.Normal → t ∈ H → H = ⊤)
    (hindex : (commutator G).index = 2)
    (P : Sylow 2 G) (htP : t ∈ P) :
    (∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N) ∨
      ∃ s : G, s ∈ P ∧ s ≠ 1 ∧ s * s = 1 ∧ s ≠ t := by
  rcases uniqueInvolutionIn_or_exists_distinct (P : Subgroup G) t with
    hunique | hdistinct
  · exact Or.inl
      (zStar_of_terminal_index_two_unique
        ht ht1 ht2 hmin hindex P htP hunique)
  · exact Or.inr hdistinct

end ZStar

end CFSG
