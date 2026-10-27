module

public import CFSG.Quasithin.MS93.S45M0

public section

namespace CFSG.Quasithin.MS93.S45R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement

section Group

variable {𝔾 : Type} [Group 𝔾]

theorem mem_sup_iff_mul_of_le_normalizer {A B : Subgroup 𝔾}
    (hAB : A ≤ Subgroup.normalizer (B : Set 𝔾)) {z : 𝔾} :
    z ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = z := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAB, Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem commutator_mul_left_mem {H : Subgroup 𝔾} {x y q : 𝔾}
    (hx : x ∈ Subgroup.normalizer (H : Set 𝔾)) (hxq : ⁅x, q⁆ ∈ H) (hyq : ⁅y, q⁆ ∈ H) :
    ⁅x * y, q⁆ ∈ H := by
  have e : ⁅x * y, q⁆ = x * ⁅y, q⁆ * x⁻¹ * ⁅x, q⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact H.mul_mem ((Subgroup.mem_normalizer_iff.mp hx _).mp hyq) hxq

end Group

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem bloc_le_zm_sup_dloc (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 18 ≤ N) :
    Bloc c.hyp.le L (p (x + 6)) ≤
      ZM (puAmalgam c.hyp.le) (p (x + 6)) ⊔ Dloc c.hyp.le L (p (x + 6)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  have hb2 : 2 < critDist (puAmalgam h.le) := by rw [c.b8]; norm_num
  have hγ := c.isMVtx_of_isGoodPath hp (k := x + 6) (by omega) (hx.add (by decide))
  have hγβ : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  have hβH : ¬ IsMVtx (puAmalgam h.le) (p (x + 7)) := by
    rw [← isMVtx_iff_of_adj _ hγβ]; exact hγ
  have hcrit : IsCritical (puAmalgam h.le) (p (x + 14)) (p (x + 6)) :=
    hp.crit (x + 6) (hx.add (by decide)) (by omega)
  have hμ : IsMVtx (puAmalgam h.le) (p (x + 14)) := hcrit.1
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hγ
  intro b hb
  have hbQ : b ∈ Qv (puAmalgam h.le) (p (x + 12)) :=
    c.bloc_le_qv hp (x := x + 6) (hx.add (by decide)) (by omega) (by omega) hb
  have hbV : b ∈ Vv (puAmalgam h.le) (p (x + 6)) := bloc_le_vv h _ hb
  have hbZQ : b ∈ ZM (puAmalgam h.le) (p (x + 6)) ⊔ Qv _ (p (x + 14)) :=
    c.vv_inf_qv_le hp (x := x + 6) (hx.add (by decide)) (by omega) (by omega) ⟨hbV, hbQ⟩
  have hZn : ZM (puAmalgam h.le) (p (x + 6)) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p (x + 14)) : Set (puAmalgam h.le).Universal) :=
    (zm_le_stab_of_isCritical _ h20 c.bpos hcrit).trans (stab_le_normalizer_qv _ _)
  rw [mem_sup_iff_mul_of_le_normalizer hZn] at hbZQ
  obtain ⟨z₀, hz₀, w, hwQμ, rfl⟩ := hbZQ
  have hwB : w ∈ Bloc h.le L (p (x + 6)) := by
    have := (Bloc h.le L (p (x + 6))).mul_mem
      ((Bloc h.le L (p (x + 6))).inv_mem (zm_le_bloc h hb2 hγ hz₀)) hb
    rwa [inv_mul_cancel_left] at this
  have hwV : w ∈ Vv (puAmalgam h.le) (p (x + 6)) := bloc_le_vv h _ hwB
  have hZμT : ZM (puAmalgam h.le) (p (x + 14)) ≤ Qv _ (p (x + 7)) :=
    zm_le_qv_of_not_isMVtx _ h20 hμ hβH (by
      rw [tdist_comm, hp.dist_eq' (i := x + 7) (j := x + 14) (by omega) (by omega), c.b8]; omega)
  have hQγT : Qv (puAmalgam h.le) (p (x + 6)) ≤ Qv _ (p (x + 7)) := qv_le_qv _ h20 hγ hγβ
  have hTs : Qv (puAmalgam h.le) (p (x + 7)) ≤ stab _ (p (x + 6)) :=
    qv_le_stab_of_adj _ hγβ.symm
  have hYT : conjCl (Qv (puAmalgam h.le) (p (x + 6))) (ZM _ (p (x + 14))) ≤
      Qv (puAmalgam h.le) (p (x + 7)) :=
    conjCl_le_of_le_normalizer hZμT
      (hQγT.trans ((qv_le_stab _ _).trans (stab_le_normalizer_qv _ _)))
  have hZγc := zloc_le_centralizer_stab h c.full hγ
  have hYw : ∀ y ∈ conjCl (Qv (puAmalgam h.le) (p (x + 6))) (ZM _ (p (x + 14))),
      y * w = w * y := by
    have hle : conjCl (Qv (puAmalgam h.le) (p (x + 6))) (ZM _ (p (x + 14))) ≤
        Subgroup.centralizer ({w} : Set (puAmalgam h.le).Universal) := by
      refine iSup₂_le fun q hq => ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzw : z * w = w * z :=
        (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hμ hz) w hwQμ).symm
      have hc₁ : q⁻¹ * w * q * w⁻¹ ∈ Zloc h.le L (p (x + 6)) := by
        have hm : ⁅w, q⁻¹⁆ ∈ ⁅Vv (puAmalgam h.le) (p (x + 6)), Qv _ (p (x + 6))⁆ :=
          Subgroup.commutator_mem_commutator hwV (inv_mem hq)
        have hm' := Subgroup.inv_mem _ (c.commutator_vv_qv_le_zloc hγ hm)
        rw [commutatorElement_inv] at hm'
        simpa [commutatorElement_def, mul_assoc] using hm'
      have hzs : z ∈ stab (puAmalgam h.le) (p (x + 6)) := hTs (hZμT hz)
      have hzc : z * (q⁻¹ * w * q * w⁻¹) = (q⁻¹ * w * q * w⁻¹) * z :=
        (Subgroup.mem_centralizer_iff.mp (hZγc hc₁) z hzs)
      have h1 : z * (q⁻¹ * w * q) = (q⁻¹ * w * q) * z := by
        calc z * (q⁻¹ * w * q) = z * (q⁻¹ * w * q * w⁻¹) * w := by group
          _ = (q⁻¹ * w * q * w⁻¹) * z * w := by rw [hzc]
          _ = (q⁻¹ * w * q * w⁻¹) * (z * w) := by group
          _ = (q⁻¹ * w * q * w⁻¹) * (w * z) := by rw [hzw]
          _ = (q⁻¹ * w * q) * z := by group
      show MulAut.conj q z * w = w * MulAut.conj q z
      simp only [MulAut.conj_apply]
      calc q * z * q⁻¹ * w = q * (z * (q⁻¹ * w * q)) * q⁻¹ := by group
        _ = q * ((q⁻¹ * w * q) * z) * q⁻¹ := by rw [h1]
        _ = w * (q * z * q⁻¹) := by group
    exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hYU : ¬ conjCl (Qv (puAmalgam h.le) (p (x + 6))) (ZM _ (p (x + 14))) ≤
      Subgroup.centralizer (Uloc h.le L (p (x + 6)) : Set (puAmalgam h.le).Universal) := by
    intro hle
    apply hcrit.2.2
    rw [← S4A.stab_inf_centralizer_uloc h c.via hγ]
    exact le_inf (hZμT.trans hTs) ((S4A.le_conjCl _ _).trans hle)
  have hwUD := S4A.mem_uloc_sup_dloc h c.full hγ hψs hψ (c.vv_le_qv' hγ hwV)
    (fun l hl => by
      have := ((mem_bloc_iff h hb2 hγ).mp hwB).2 l hl
      rw [← commutatorElement_inv]
      exact inv_mem this)
    (hYT.trans hTs) hYw (S4A.le_normalizer_conjCl _ _) ((isPGroup_qv _ h20 hβH).to_le hYT) hYU
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz₀)
    (sup_le_sup_right (uloc_le_zm h c.full hγ) _ hwUD)

end Ctx

end CFSG.Quasithin.MS93.S45R
