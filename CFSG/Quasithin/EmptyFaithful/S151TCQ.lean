module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.EmptyFaithful.S151V2

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem c134Q_eq_blockU {L R : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) : c134Q (L ⊔ R) L = blockU L := by
  set G₀ : Subgroup G := L ⊔ R with hG₀
  have hG₀N : G₀ ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hRN
  set P : Subgroup G := pCoreOf 2 G₀ with hP
  have hPN : G₀ ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 G₀
  have hP2 : IsPGroup 2 P := pCoreOf_isPGroup 2 G₀
  have hLG₀ : L ≤ G₀ := le_sup_left
  have hPG₀ : P ≤ G₀ := pCoreOf_le 2 G₀
  have hQdef : c134Q G₀ L = ⁅P, L⁆ := rfl
  rw [hQdef]
  have hQN : G₀ ≤ Subgroup.normalizer ((⁅P, L⁆ : Subgroup G) : Set G) := fun x hx =>
    normalizer_commutator (hPN hx) (hG₀N hx)
  have hQL : ⁅P, L⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have h1 : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hG₀N (hPG₀ hx)) l).1 hl
    have e : ⁅x, l⁆ = (x * l * x⁻¹) * l⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact L.mul_mem h1 (L.inv_mem hl)
  have hQP : ⁅P, L⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have h1 : l * x⁻¹ * l⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hPN (hLG₀ hl)) x⁻¹).1
      (P.inv_mem hx)
    have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact P.mul_mem hx h1
  have hQ2 : IsPGroup 2 ↥(⁅P, L⁆ : Subgroup G) := hP2.to_le hQP
  have hLQ : L ≤ Subgroup.normalizer ((⁅P, L⁆ : Subgroup G) : Set G) := fun x hx => hQN (hLG₀ hx)
  have hQO : ⁅P, L⁆ ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hQL hLQ hQ2
  apply le_antisymm
  ·
    have hPQ : P ≤ Subgroup.normalizer ((⁅⁅P, L⁆, L⁆ : Subgroup G) : Set G) := fun x hx =>
      normalizer_commutator (hQN (hPG₀ hx)) (hG₀N (hPG₀ hx))
    have hLQ' : L ≤ Subgroup.normalizer ((⁅⁅P, L⁆, L⁆ : Subgroup G) : Set G) := fun x hx =>
      normalizer_commutator (hQN (hLG₀ hx)) (hG₀N (hLG₀ hx))
    have key : ⁅⁅L, L⁆, P⁆ ≤ ⁅⁅P, L⁆, L⁆ :=
      s151v_three_subgroups_le (H₁ := L) (H₂ := L) (H₃ := P) (N := ⁅⁅P, L⁆, L⁆) hLQ' hLQ' hPQ
        (by rw [Subgroup.commutator_comm L P]) (by exact le_rfl)
    rw [hperf, Subgroup.commutator_comm] at key
    exact key.trans (Subgroup.commutator_mono hQO le_rfl)
  ·
    have hOP : pCoreOf 2 L ≤ P := by
      refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLG₀)
        (fun x hx => ?_) (pCoreOf_isPGroup 2 L)
      exact normalizer_le_normalizer_pCoreOf 2 L (hG₀N hx)
    exact Subgroup.commutator_mono hOP le_rfl

end CFSG.Quasithin.S151TC
