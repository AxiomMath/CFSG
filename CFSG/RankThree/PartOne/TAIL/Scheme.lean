module

public import CFSG.RankThree.PartOne.TAIL.Fusion
public import CFSG.RankThree.PartOne.TAIL.SylowG

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

variable {G : Type} [Group G] [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}

theorem SchemeHyp.scheme (h : SchemeHyp G A B c b d y₀ K M₀)
    (hadj : ∀ n ∈ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G), ∃ l ∈ M₀, l * n ∈ Subgroup.normalizer (K : Set G)) :
    ∃ P Q : Subgroup G, (P ≤ ⊤ ∧ IsPGroup 7 P ∧ ¬ 7 ∣ P.relIndex ⊤) ∧ Q ≤ P ∧
      (Q.subgroupOf P).Normal ∧ (∀ x y : ↥P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P) ∧
      c ∈ P ∧ c ∉ Q ∧ ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q := by
  obtain ⟨P, hP⟩ := h.exists_P
  exact ⟨P, Qsub K P, ⟨le_top, hP.pgroup, h.P_sylow_G hP⟩, Qsub_le K P, h.Q_normal hP,
    h.P_comm_mod_Q hP, h.c_mem_P hP, h.c_notMem_Q (P := P), fun g hg => h.fusion hP hadj hg⟩

end CFSG.RankThree.PartOne.TAIL
