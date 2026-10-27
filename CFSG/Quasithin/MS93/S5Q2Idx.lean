module

public import CFSG.Quasithin.MS93.S5Q2UC

public section

namespace CFSG.Quasithin.MS93.S5Q2.UC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

variable (h : PUHyp M T L)

theorem relIndex_zm_eq_four (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) α') :
    (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 4 := by
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hCH := h.centHyp
  have hNF : Nat.card F = 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa using hd.card_eq
  obtain ⟨g, hgα, -, hμ, -⟩ := S33.exists_conj_of_isCritical _ h20 hb hc
  have hcμ : IsCritical _ (baseA _) (g⁻¹ • baseA (puAmalgam h.le)) := ms22_iii _ h20 hb hCH hμ
  have hgμ : g • (g⁻¹ • baseA (puAmalgam h.le)) = baseA (puAmalgam h.le) := smul_inv_smul g _
  have hconj : ∀ H K : Subgroup (puAmalgam h.le).Universal,
      (H.map (MulAut.conj g).toMonoidHom).relIndex (K.map (MulAut.conj g).toMonoidHom) =
        H.relIndex K := fun H K =>
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have e : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) =
      (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) := by
    rw [← hconj (Qv _ (baseA _)) (ZM _ (g⁻¹ • baseA _)), ← qv_smul, ← zm_smul, hgα, hgμ]
  rw [e]
  obtain ⟨hXs, hX2, -, -⟩ := X52.crit_facts h hcμ
  have hZX : ZM _ (g⁻¹ • baseA (puAmalgam h.le)) ≤ XM _ (g⁻¹ • baseA (puAmalgam h.le)) :=
    zm_le_xm _ h20 hb (hcμ.isMVtx_right _ h20)
  rw [S33.relIndex_qv_baseA_eq_card h hd (hZX.trans hXs) (hX2.to_le hZX)]
  obtain ⟨-, l, hl, hX, hZ⟩ := shape_of_not_le h hd hC hcμ
  rw [hZ, hX, MSP.card_qLine_inf_commutator hNF hl]

theorem zq_le_centralizer_of_relIndex_ne_four (hd : S5.IsSp4Data M T L 1 F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hidx : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) ≠ 4) :
    Zq M L ≤ Subgroup.centralizer (M : Set G) := by
  by_contra hC
  exact hidx (relIndex_zm_eq_four h hd hC hc)

theorem zq_le_centralizer_of_relIndex_eq {k : ℕ} (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hidx : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k) :
    Zq M L ≤ Subgroup.centralizer (M : Set G) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    exact zq_le_centralizer_of_relIndex_ne_four h hd hc (by rw [hidx]; norm_num)
  · exact S5Q2.zq_le_centralizer_of_two_le h hd hk

end CFSG.Quasithin.MS93.S5Q2.UC
