module

public import CFSG.Quasithin.MS93.S45RG

public section

namespace CFSG.Quasithin.MS93.S45G

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem commutator_mem_zloc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    {d : (puAmalgam c.hyp.le).Universal} (hdV : d ∈ Vv (puAmalgam c.hyp.le) δ)
    (hdL : d ∈ Subgroup.centralizer (Ltil c.hyp.le L δ : Set (puAmalgam c.hyp.le).Universal))
    {g : (puAmalgam c.hyp.le).Universal} (hg : g ∈ stab (puAmalgam c.hyp.le) δ) :
    ⁅d, g⁆ ∈ Zloc c.hyp.le L δ := by
  have h := c.hyp
  rw [stab_eq_ltil_sup_qv h c.full hδ, S45R.mem_sup_iff_mul_of_le_normalizer
    ((ltil_le_stab h _).trans (stab_le_normalizer_qv _ _))] at hg
  obtain ⟨l, hl, t, ht, rfl⟩ := hg
  have hld : l * d = d * l := Subgroup.mem_centralizer_iff.mp hdL l hl
  have e : ⁅d, l * t⁆ = l * ⁅d, t⁆ * l⁻¹ := by
    calc ⁅d, l * t⁆ = (d * l) * t * d⁻¹ * t⁻¹ * l⁻¹ := by rw [commutatorElement_def]; group
      _ = (l * d) * t * d⁻¹ * t⁻¹ * l⁻¹ := by rw [hld]
      _ = l * ⁅d, t⁆ * l⁻¹ := by rw [commutatorElement_def]; group
  have hz : ⁅d, t⁆ ∈ Zloc h.le L δ :=
    c.commutator_vv_qv_le_zloc hδ (Subgroup.commutator_mem_commutator hdV ht)
  have hc : l * ⁅d, t⁆ = ⁅d, t⁆ * l :=
    Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h c.full hδ hz) l
      (ltil_le_stab h _ hl)
  rw [e, hc, mul_inv_cancel_right]
  exact hz

theorem commute_zm_of_mem_bloc {q : ℕ → Vtx (puAmalgam c.hyp.le)} {N y : ℕ}
    (hq : IsGoodPath _ q N) (hy : Even y) (h10 : 10 ≤ y) (hyN : y + 12 ≤ N)
    {d : (puAmalgam c.hyp.le).Universal} (hdB : d ∈ Bloc c.hyp.le L (q y))
    (hdL : d ∈ Subgroup.centralizer (Ltil c.hyp.le L (q y) : Set (puAmalgam c.hyp.le).Universal))
    {z : (puAmalgam c.hyp.le).Universal} (hz : z ∈ ZM (puAmalgam c.hyp.le) (q (y + 8))) :
    d * z = z * d := by
  have h := c.hyp
  have h20 := h.hyp20
  have hγ := c.isMVtx_of_isGoodPath hq (k := y) (by omega) hy
  have hc : IsCritical (puAmalgam h.le) (q y) (q (y + 8)) :=
    c.isCritical_of_isGoodPath hq hy (by omega)
  have hμ : IsMVtx (puAmalgam h.le) (q (y + 8)) := (c.isCritical_symm hc).1
  have hdV : d ∈ Vv (puAmalgam h.le) (q y) := bloc_le_vv h _ hdB
  have hdQ : d ∈ Qv (puAmalgam h.le) (q (y + 6)) := c.bloc_le_qv hq hy h10 hyN hdB
  have hdZQ : d ∈ ZM (puAmalgam h.le) (q y) ⊔ Qv _ (q (y + 8)) :=
    c.vv_inf_qv_le hq hy (by omega) hyN ⟨hdV, hdQ⟩
  have hZn : ZM (puAmalgam h.le) (q y) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (q (y + 8)) : Set (puAmalgam h.le).Universal) :=
    (zm_le_stab_of_isCritical _ h20 c.bpos (c.isCritical_symm hc)).trans
      (stab_le_normalizer_qv _ _)
  rw [S45R.mem_sup_iff_mul_of_le_normalizer hZn] at hdZQ
  obtain ⟨z', hz', t, ht, rfl⟩ := hdZQ
  have htz : t * z = z * t :=
    Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hμ hz) t ht
  have e : ⁅z' * t, z⁆ = ⁅z', z⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc z' * t * z * (z' * t)⁻¹ * z⁻¹ = z' * (t * z) * t⁻¹ * z'⁻¹ * z⁻¹ := by group
      _ = z' * (z * t) * t⁻¹ * z'⁻¹ * z⁻¹ := by rw [htz]
      _ = z' * z * z'⁻¹ * z⁻¹ := by group
  have hU : ⁅z' * t, z⁆ ∈ Uloc h.le L (q y) := by
    rw [e]
    exact c.critR_le_uloc hc (Subgroup.commutator_mem_commutator hz' hz)
  have hzs : z ∈ stab (puAmalgam h.le) (q y) := zm_le_stab_of_isCritical _ h20 c.bpos hc hz
  have hZ : ⁅z' * t, z⁆ ∈ Zloc h.le L (q y) := commutator_mem_zloc c hγ hdV hdL hzs
  have h1 : ⁅z' * t, z⁆ = 1 := by
    rw [← Subgroup.mem_bot, ← uloc_inf_zloc h c.full (q y)]
    exact ⟨hU, hZ⟩
  rw [commutatorElement_eq_one_iff_commute] at h1
  exact h1.eq

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

end Ctx

end CFSG.Quasithin.MS93.S45G
