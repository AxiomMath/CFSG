module

public import CFSG.Quasithin.MS93.S46LastAbs
public import CFSG.Quasithin.MS93.S46End
public import CFSG.Quasithin.MS93.S4AFMain

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A

theorem i46sCfg_of_i46tCfg (h14 : MS14AS) (hSQ : SQTKQuot) (h463 : I463) (h465 : I465)
    (h466b : I466b) (h467 : I467) {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hT : I46TCfg M T L φ) :
    I46SCfg M T L φ := by
  intro c α hα
  obtain ⟨ψ, hψs, hψU, hQL, V₀, V₁, h₀, h₁, hinf, hsup⟩ := hT c α hα
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨n, hn⟩ := hφ.1
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨β, hαβ⟩ := exists_adj (puAmalgam h.le) α
  have hVV := (h463 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α hα).2
  have hVQ := (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α β hα hαβ).2.2
  have hne : ⁅Vv (puAmalgam h.le) α, Vv _ α⁆ ≠ ⊥ := by
    intro hbot
    apply h466b G M T L F φ ⟨h, hmin, hb4, hφ⟩ α hα
    rw [hbot]
    exact bot_le
  have hBL : ⁅centerOf (Vv (puAmalgam h.le) α), Ltil h.le L α⁆ ≤ ZM _ α := by
    rw [← h467 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α hα, Subgroup.commutator_le]
    intro x hx l hl
    exact ((mem_bloc_iff h hb hα).mp hx).2 l hl
  have hLH : LastHyp (stab (puAmalgam h.le) α) (Qv _ α) (Ltil h.le L α) (Uloc h.le L α)
      (Zloc h.le L α) (ZM _ α) (Vv _ α) ψ :=
    { fin := finite_stab h hα
      surj := hψs
      nat := hψU
      ker := toSL3_eq_one_iff_mem_qv h hφ hα hψU
      qK := qv_le_stab _ α
      ltK := ltil_le_stab h α
      ltN := stab_le_normalizer_ltil h α
      sup := (stab_eq_ltil_sup_qv h hfull hα).le
      perf := ltil_perfect h hα
      zN := stab_le_normalizer_zm _ α
      zEq := zm_eq_uloc_sup_zloc h hfull hα
      z0c := zloc_le_centralizer_stab h hfull hα
      zq := zm_le_centralizer_qv _ h.hyp20 hα
      z2 := fun z hz => sq_eq_one_of_mem_zv h hfull (ρ := α) (by rwa [zv_of_isMVtx _ hα])
      vq := vv_le_qv h hb hα
      vN := stab_le_normalizer_vv h α
      zv := zm_le_vv h hα
      vv := hVV
      vqc := hVQ
      vne := hne
      bl := hBL
      ql := hQL }
  obtain ⟨hcen, hW₀, hW₁, hinfW, hsupW, hd₀, hd₁⟩ := last_struct hLH h₀ h₁ hinf hsup h14 hSQ
    (sqtkGroup_SL3_of_sqtkQuot h hSQ hφ) hF
  exact ⟨ψ, hψs, hψU, hcen, _, _, hW₀, hW₁, hinfW, hsupW, hd₀, hd₁⟩

theorem i46s_of_i46t (h14 : MS14AS) (hSQ : SQTKQuot) (h463 : I463) (h465 : I465)
    (h466b : I466b) (h467 : I467) (hT : I46T) : I46S :=
  fun G _ _ M T L F _ _ φ => i46sCfg_of_i46tCfg h14 hSQ h463 h465 h466b h467 (hT G M T L F φ)

end CFSG.Quasithin.MS93.S46
