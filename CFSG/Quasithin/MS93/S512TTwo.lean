module

public import CFSG.Quasithin.MS93.S512TPair

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S512T

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem exists_relIndex_eq_pow (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ) :
    ∃ d : ℕ, (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = (2 ^ k) ^ d := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  rw [S5B.relIndex_centralizer_smul h g hE₀M]
  exact ⟨_, relIndex_eq_pow_M h hd hE₀M⟩

theorem bad_indices (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ)
    (hbad : 2 ^ k < (Qv _ γ).relIndex (ZM _ μ)) :
    (Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L μ) = (2 ^ k) ^ 2 ∧
      (Qv _ μ).relIndex (ZM _ γ) = (2 ^ k) ^ 2 := by
  have hyp := h.hyp20
  obtain ⟨hμ, hγ, -, hd4, -, -, -, -, -, -, -, -⟩ := pair_facts h hb4 hc
  obtain ⟨hZρ, hst, h2, hQ⟩ := zm_facts h hb4 hc
  have hk : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
  have hc' : IsCritical _ γ μ :=
    ⟨hγ, by rw [SimpleGraph.dist_comm]; exact hd4.trans hb4.symm, hQ⟩
  have key : ∀ {μ γ : Vtx (puAmalgam h.le)}, IsCritical _ μ γ →
      2 ^ k < (Qv _ γ).relIndex (ZM _ μ) →
      (Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L μ) = (2 ^ k) ^ 2 := by
    intro μ γ hc hlt
    obtain ⟨-, hst, -, -⟩ := zm_facts h hb4 hc
    obtain ⟨d, hdeq⟩ := exists_relIndex_eq_pow h hd hc.1 hst
    have hle := relIndex_qv_zm_le_sq h hb4 hd hc
    rw [relIndex_qv_zm_eq h hb4 hc, hdeq] at hle hlt
    have h1 : 1 < d := by
      by_contra hd1
      push Not at hd1
      have := Nat.pow_le_pow_right (by omega : 0 < 2 ^ k) hd1
      rw [pow_one] at this
      omega
    have h2 : d ≤ 2 := (Nat.pow_le_pow_iff_right hk).1 hle
    rw [hdeq, show d = 2 by omega]
  refine ⟨key hc hbad, ?_⟩
  have hbad' : 2 ^ k < (Qv _ μ).relIndex (ZM _ γ) := by
    by_contra hle
    push Not at hle
    have := relIndex_qv_zm_symm h hb4 hd hc' hle
    omega
  rw [relIndex_qv_zm_eq h hb4 hc', key hc' hbad']

end S512T

end CFSG.Quasithin.MS93
