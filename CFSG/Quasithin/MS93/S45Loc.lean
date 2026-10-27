module

public import CFSG.Quasithin.MS93.S45Vtx
public import CFSG.Quasithin.MS93.S4ABasic

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

structure Ctx (M T L : Subgroup G) (φ : ↥M →* ↥(StatedSL 3 F)) : Prop where
  hyp : PUHyp M T L
  min : PUMin M T L
  via : IsSL3FullVia M T L φ
  cent : CentHyp (puAmalgam hyp.le)
  b8 : critDist (puAmalgam hyp.le) = 8
  c1 : ∀ α β : Vtx (puAmalgam hyp.le), IsMVtx _ α → (puAmalgam hyp.le).treeGraph.Adj α β →
    IsC1 hyp.le L (Fintype.card F) α (Vv _ α) (ZM _ α) ∧ ⁅Vv _ α, Qv _ α⁆ ≤ stabCenter _ α ∧
      (ZH _ β).relIndex (ZM _ α) = Fintype.card F ∧
      (Qv _ α).relIndex (Qv _ β) = Fintype.card F ^ 2
  c444 : ∀ α α' : Vtx (puAmalgam hyp.le), IsCritical _ α α' → IsStraight _ α α' →
    Concl444 hyp.le α α'
  exStr : ∃ α α' : Vtx (puAmalgam hyp.le), IsCritical _ α α' ∧ IsStraight _ α α'
  s43 : ∀ α α' : Vtx (puAmalgam hyp.le), IsCritical _ α α' → ¬ Vv _ α ≤ Qv _ (geo _ α' α 2)

theorem charP_two_of_card_eq_two_pow {n : ℕ} (hF : Fintype.card F = 2 ^ n) : CharP F 2 := by
  obtain ⟨m, hp, hm⟩ := FiniteField.card F (ringChar F)
  have hdvd : ringChar F ∣ 2 ^ n := by
    rw [← hF, hm]
    exact dvd_pow_self _ (PNat.ne_zero m)
  have h2 : ringChar F = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  rw [← h2]
  exact ringChar.charP F

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem full : IsSL3Full M T L :=
  isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, c.via⟩

theorem charP : CharP F 2 := by
  obtain ⟨n, hn⟩ := c.via.1
  exact charP_two_of_card_eq_two_pow hn

theorem bpos : 0 < critDist (puAmalgam c.hyp.le) := by rw [c.b8]; norm_num


theorem relIndex_zh {α β : Vtx (puAmalgam c.hyp.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam c.hyp.le).treeGraph.Adj α β) :
    (ZH _ β).relIndex (ZM _ α) = Fintype.card F := (c.c1 α β hα hαβ).2.2.1

theorem relIndex_qv {α β : Vtx (puAmalgam c.hyp.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam c.hyp.le).treeGraph.Adj α β) :
    (Qv _ α).relIndex (Qv _ β) = Fintype.card F ^ 2 := (c.c1 α β hα hαβ).2.2.2

theorem commutator_vv_qv_le_stabCenter {α : Vtx (puAmalgam c.hyp.le)} (hα : IsMVtx _ α) :
    ⁅Vv _ α, Qv _ α⁆ ≤ stabCenter _ α := by
  obtain ⟨β, hαβ⟩ := exists_adj _ α
  exact (c.c1 α β hα hαβ).2.1

theorem zloc_eq_zm_inf_centralizer {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    Zloc c.hyp.le L δ =
      ZM _ δ ⊓ Subgroup.centralizer (Ltil c.hyp.le L δ : Set (puAmalgam c.hyp.le).Universal) := by
  have h := c.hyp
  rw [Zloc, Zq, puTrans_inf_centralizer (hTM := h.le) (Xq_le M) h.L_le
    (le_normalizer_Xq M) h.le_normalizer hδ, ← h.xm_eq hδ, xm_eq_zm h c.full hδ]

theorem commutator_vv_qv_le_zloc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    ⁅Vv _ δ, Qv _ δ⁆ ≤ Zloc c.hyp.le L δ := by
  have h := c.hyp
  have hb2 : 2 < critDist (puAmalgam h.le) := by rw [c.b8]; norm_num
  have hVQ : Vv (puAmalgam h.le) δ ≤ Qv _ δ := vv_le_qv h hb2 hδ
  have hQs : Qv (puAmalgam h.le) δ ≤ stab _ δ := qv_le_stab _ δ
  have hcen := c.commutator_vv_qv_le_stabCenter hδ
  have hcent : ⁅Vv (puAmalgam h.le) δ, Qv _ δ⁆ ≤
      Subgroup.centralizer (stab (puAmalgam h.le) δ : Set (puAmalgam h.le).Universal) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hcen hx)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp hy ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hQn : ⁅Vv (puAmalgam h.le) δ, Qv _ δ⁆ ≤ Qv _ δ :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      (hVQ.trans (Subgroup.le_normalizer (H := Qv (puAmalgam h.le) δ)))
  have hgen : ∀ v ∈ Vv (puAmalgam h.le) δ, ∀ q ∈ Qv (puAmalgam h.le) δ,
      ⁅v, q⁆ ^ 2 = 1 := by
    intro v hv q hq
    have hc : ⁅v, q⁆ ∈ Subgroup.centralizer (stab (puAmalgam h.le) δ : Set _) :=
      hcent (Subgroup.commutator_mem_commutator hv hq)
    have hv2 : v ^ 2 = 1 := (isElemAbelian_vi _ h.hyp20 c.bpos (by rw [c.b8]; norm_num)).2 v hv
    have hvs : v ∈ stab (puAmalgam h.le) δ := hQs (hVQ hv)
    have h1 : v * q * v⁻¹ = ⁅v, q⁆ * q := by
      rw [commutatorElement_def]; group
    have h2 : v * (⁅v, q⁆ * q) * v⁻¹ = ⁅v, q⁆ * (v * q * v⁻¹) := by
      have hcv := (Subgroup.mem_centralizer_iff.mp hc) v hvs
      calc v * (⁅v, q⁆ * q) * v⁻¹ = (v * ⁅v, q⁆) * q * v⁻¹ := by group
        _ = (⁅v, q⁆ * v) * q * v⁻¹ := by rw [hcv]
        _ = ⁅v, q⁆ * (v * q * v⁻¹) := by group
    have hvv : v * v = 1 := by rw [← sq]; exact hv2
    have h3 : q = ⁅v, q⁆ ^ 2 * q := by
      calc q = (v * v) * q * (v * v)⁻¹ := by rw [hvv]; group
        _ = v * (v * q * v⁻¹) * v⁻¹ := by group
        _ = ⁅v, q⁆ * (⁅v, q⁆ * q) := by rw [h1, h2, h1]
        _ = ⁅v, q⁆ ^ 2 * q := by rw [sq, mul_assoc]
    have := congrArg (· * q⁻¹) h3
    simpa using this.symm
  have hZ : ⁅Vv (puAmalgam h.le) δ, Qv _ δ⁆ ≤ ZM _ δ := by
    rw [← xm_eq_zm h c.full hδ, XM, omegaOneCenterOf, omegaOneOf, Subgroup.commutator_def]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨v, hv, q, hq, rfl⟩
    have hmem := Subgroup.commutator_mem_commutator hv hq
    refine ⟨⟨hQn hmem, ?_⟩, hgen v hv q hq⟩
    exact Subgroup.centralizer_le hQs (hcent hmem)
  rw [c.zloc_eq_zm_inf_centralizer hδ]
  exact le_inf hZ (hcent.trans
    (Subgroup.centralizer_le (ltil_le_stab c.hyp δ)))

end Ctx

end CFSG.Quasithin.MS93.S45
