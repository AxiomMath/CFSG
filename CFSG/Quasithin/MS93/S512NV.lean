module

public import CFSG.Quasithin.MS93.S512NCh
public import CFSG.Quasithin.MS93.S512NQ
public import CFSG.Quasithin.MS93.S512NBase

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512N

section General

theorem sq_mem_of_iSup {Γ : Type*} [Group Γ] {ι : Sort*} {K : ι → Subgroup Γ} {N : Subgroup Γ}
    (hK : ∀ i, ∀ x ∈ K i, x ^ 2 = 1) (hc : ⁅⨆ i, K i, ⨆ i, K i⁆ ≤ N) :
    ∀ v ∈ ⨆ i, K i, v ^ 2 ∈ N := by
  let S : Subgroup Γ :=
    { carrier := {v | v ∈ ⨆ i, K i ∧ v ^ 2 ∈ N}
      one_mem' := ⟨one_mem _, by rw [one_pow]; exact one_mem _⟩
      mul_mem' := by
        rintro v w ⟨hv, hv2⟩ ⟨hw, hw2⟩
        refine ⟨mul_mem hv hw, ?_⟩
        have e : (v * w) ^ 2 = v ^ 2 * ⁅v⁻¹, w⁆ * w ^ 2 := by
          simp only [commutatorElement_def, pow_two]
          group
        rw [e]
        exact mul_mem (mul_mem hv2 (hc (Subgroup.commutator_mem_commutator (inv_mem hv) hw))) hw2
      inv_mem' := by
        rintro v ⟨hv, hv2⟩
        refine ⟨inv_mem hv, ?_⟩
        rw [inv_pow]
        exact inv_mem hv2 }
  have hle : (⨆ i, K i) ≤ S := iSup_le fun i x hx =>
    ⟨Subgroup.mem_iSup_of_mem i hx, by rw [hK i x hx]; exact one_mem _⟩
  exact fun v hv => (hle hv).2

theorem commutator_nclStab_le {A B : Type} {C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {δ : Vtx X} {K N : Subgroup X.Universal} (hK : K ≤ stab X δ)
    (hN : stab X δ ≤ Subgroup.normalizer (N : Set X.Universal))
    (hKN : ∀ g ∈ stab X δ, ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ ≤ N) :
    ⁅S5.nclStab X δ K, S5.nclStab X δ K⁆ ≤ N := by
  have hKg : ∀ g : ↥(stab X δ), K.map (MulAut.conj (g : X.Universal)).toMonoidHom ≤
      Subgroup.normalizer (N : Set X.Universal) := by
    intro g
    rintro _ ⟨x, hx, rfl⟩
    exact hN (mul_mem (mul_mem g.2 (hK hx)) (inv_mem g.2))
  have hpair : ∀ g g' : ↥(stab X δ), ⁅K.map (MulAut.conj (g : X.Universal)).toMonoidHom,
      K.map (MulAut.conj (g' : X.Universal)).toMonoidHom⁆ ≤ N := by
    intro g g'
    have h1 := hKN _ (mul_mem (inv_mem g.2) g'.2)
    have h2 := Subgroup.map_mono (f := (MulAut.conj (g : X.Universal)).toMonoidHom) h1
    rw [Subgroup.map_commutator, Subgroup.map_map, map_conj_eq_of_mem_normalizer (hN g.2)] at h2
    have e : (MulAut.conj (g : X.Universal)).toMonoidHom.comp
        (MulAut.conj ((g : X.Universal)⁻¹ * g')).toMonoidHom =
        (MulAut.conj (g' : X.Universal)).toMonoidHom := by
      ext x
      simp [mul_assoc]
    rwa [e] at h2
  refine commutator_iSup_le hKg fun g => ?_
  rw [Subgroup.commutator_comm]
  exact commutator_iSup_le hKg fun g' => hpair g' g

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)

theorem nclStab_le_vv {α ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ)
    (hd : (puAmalgam h.le).treeGraph.dist α ρ ≤ 2) : S5.nclStab _ α (ZM _ ρ) ≤ Vv _ α := by
  refine iSup_le fun g => ?_
  rw [← zm_smul]
  have hgρ : IsMVtx _ ((g : (puAmalgam h.le).Universal) • ρ) := (isMVtx_smul _ _ _).2 hρ
  have hgd : (puAmalgam h.le).treeGraph.dist α ((g : (puAmalgam h.le).Universal) • ρ) ≤ 2 := by
    have := dist_smul _ (g : (puAmalgam h.le).Universal) α ρ
    rw [(mem_stab _).1 g.2] at this
    rw [this]
    exact hd
  refine le_trans ?_ (le_iSup₂ (f := fun ρ' (_ : ρ' ∈ {ρ' : Vtx (puAmalgam h.le) |
    (puAmalgam h.le).treeGraph.dist α ρ' ≤ 2}) => Zv (puAmalgam h.le) ρ') _ hgd)
  exact (zv_of_isMVtx _ hgρ).ge

end General

section Cfg

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

structure Cfg (h : PUHyp M T L) (k : ℕ) (δ μ₁ μ₂ : Vtx (puAmalgam h.le)) : Prop where
  b4 : critDist (puAmalgam h.le) = 4
  adj : (puAmalgam h.le).treeGraph.Adj (baseB _) δ
  crit₁ : IsCritical _ μ₁ δ
  mid₁ : geo _ μ₁ δ 2 = baseA _
  conj₁ : ∃ y ∈ stab _ (baseA (puAmalgam h.le)), μ₁ = y • δ
  crit₂ : IsCritical _ (baseA (puAmalgam h.le)) μ₂
  mid₂ : geo _ (baseA (puAmalgam h.le)) μ₂ 2 = μ₁
  conj₂ : ∃ y ∈ stab _ μ₁, μ₂ = y • baseA (puAmalgam h.le)
  idxQ : (Qv _ δ).relIndex (ZM _ μ₁) = 2 ^ k
  idxB : (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k
  idxB₂ : (S5.bSub h.le L μ₁).relIndex (ZM _ μ₂) = 2 ^ k

theorem relIndex_qv_le_of_inf_le (h : PUHyp M T L) {ρ ρ' : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) {B : Subgroup (puAmalgam h.le).Universal} (hle : ZM _ ρ ⊓ B ≤ Qv _ ρ') :
    (Qv _ ρ').relIndex (ZM _ ρ) ≤ B.relIndex (ZM _ ρ) := by
  have := finite_zm h hρ
  calc (Qv _ ρ').relIndex (ZM _ ρ)
      ≤ (ZM _ ρ ⊓ B).relIndex (ZM _ ρ) :=
        Subgroup.relIndex_le_of_le_left hle Subgroup.FiniteIndex.index_ne_zero
    _ = B.relIndex (ZM _ ρ) := Subgroup.inf_relIndex_left _ _

namespace Cfg

variable {h : PUHyp M T L} {δ μ₁ μ₂ : Vtx (puAmalgam h.le)} (hc : Cfg h k δ μ₁ μ₂)
include hc

theorem two_lt : 2 < critDist (puAmalgam h.le) := by rw [hc.b4]; norm_num

theorem isMVtx_μ₁ : IsMVtx _ μ₁ := hc.crit₁.1

theorem isMVtx_δ : IsMVtx _ δ := hc.crit₁.isMVtx_right _ h.hyp20

theorem isMVtx_μ₂ : IsMVtx _ μ₂ := hc.crit₂.isMVtx_right _ h.hyp20

theorem dist_μ₁ : (puAmalgam h.le).treeGraph.dist (baseA _) μ₁ = 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, hd, -⟩ := pair_geo h hc.b4 hc.crit₁
  rw [tdist_comm, ← hc.mid₁]
  exact hd

theorem dist_δ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hd, -⟩ := pair_geo h hc.b4 hc.crit₁
  rw [← hc.mid₁]
  exact hd

theorem dist_μ₁μ₂ : (puAmalgam h.le).treeGraph.dist μ₁ μ₂ = 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hd, -⟩ := pair_geo h hc.b4 hc.crit₂
  rw [← hc.mid₂]
  exact hd

theorem crit₁' : IsCritical _ δ μ₁ := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc.crit₁

theorem crit₂' : IsCritical _ μ₂ (baseA (puAmalgam h.le)) :=
  ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc.crit₂

theorem conj₁' : ∃ y ∈ stab _ (baseA (puAmalgam h.le)), δ = y • μ₁ := by
  obtain ⟨y, hy, rfl⟩ := hc.conj₁
  exact ⟨y⁻¹, inv_mem hy, by rw [inv_smul_smul]⟩

theorem zm_μ₁_le_qv : ZM _ μ₁ ≤ Qv _ (baseA (puAmalgam h.le)) :=
  zm_le_qv_two h hc.two_lt hc.isMVtx_μ₁ hc.dist_μ₁

theorem zm_δ_le_qv : ZM _ δ ≤ Qv _ (baseA (puAmalgam h.le)) :=
  zm_le_qv_two h hc.two_lt hc.isMVtx_δ hc.dist_δ

theorem nclStab_eq :
    S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) =
      S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ) := by
  obtain ⟨y, hy, rfl⟩ := hc.conj₁
  rw [zm_smul, nclStab_map_conj_of_mem hy]

theorem nclStab_le_qv : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) ≤
    Qv _ (baseA (puAmalgam h.le)) :=
  S310.nclStab_le_qv h hc.isMVtx_μ₁ hc.dist_μ₁ hc.two_lt

theorem nclStab_le_vv : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) ≤
    Vv _ (baseA (puAmalgam h.le)) :=
  S512N.nclStab_le_vv h hc.isMVtx_μ₁ hc.dist_μ₁.le

theorem zm_δ_le : ZM _ δ ≤ S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) := by
  rw [hc.nclStab_eq]
  exact le_nclStab _ _ _

theorem relIndex_bSub_smul {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam h.le))) :
    (S5.bSub h.le L (baseA _)).relIndex (ZM _ (g • μ₁)) = 2 ^ k := by
  have := S5B.relIndex_bSub_zm_smul h g (baseA (puAmalgam h.le)) μ₁
  rw [(mem_stab _).1 hg] at this
  rw [this, hc.idxB]

theorem relIndex_bSub_δ : (S5.bSub h.le L (baseA _)).relIndex (ZM _ δ) = 2 ^ k := by
  obtain ⟨y, hy, he⟩ := hc.conj₁'
  rw [he]
  exact hc.relIndex_bSub_smul hy

theorem inf_bSub_eq_of_crit (hd : S5.IsSp4Data M T L k F a) {g g' : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam h.le))) (hg' : g' ∈ stab _ (baseA (puAmalgam h.le)))
    (hcr : IsCritical _ (g • μ₁) (g' • μ₁)) :
    ZM _ (g • μ₁) ⊓ S5.bSub h.le L (baseA _) = ZM _ (g • μ₁) ⊓ Qv _ (g' • μ₁) := by
  have hb := hc.two_lt
  have hgμ : IsMVtx _ (g • μ₁) := (isMVtx_smul _ _ _).2 hc.isMVtx_μ₁
  have hg'μ : IsMVtx _ (g' • μ₁) := (isMVtx_smul _ _ _).2 hc.isMVtx_μ₁
  have hd' : (puAmalgam h.le).treeGraph.dist (baseA _) (g' • μ₁) = 2 := by
    have := dist_smul _ g' (baseA (puAmalgam h.le)) μ₁
    rw [(mem_stab _).1 hg'] at this
    rw [this, hc.dist_μ₁]
  have hle : ZM _ (g • μ₁) ⊓ S5.bSub h.le L (baseA _) ≤ Qv _ (g' • μ₁) := by
    have := inf_bSub_le_qv h hb (isMVtx_baseA _) hg'μ hd' (mul_mem hg (inv_mem hg'))
    rwa [mul_smul, inv_smul_smul] at this
  have := finite_zm h hgμ
  refine inf_eq_of_inf_le_of_relIndex_eq hle (le_antisymm ?_ (relIndex_qv_le_of_inf_le h hgμ hle))
  rw [hc.relIndex_bSub_smul hg]
  exact le_relIndex_qv_zm h hd hcr

theorem isElemAbelian_zm_smul (g : (puAmalgam h.le).Universal) :
    CFSG.Open.IsElemAbelian 2 (ZM _ (g • μ₁)) :=
  isElemAbelian_zm _ h.hyp20 h.critDist_pos ((isMVtx_smul _ _ _).2 hc.isMVtx_μ₁)

theorem commutator_le_bSub (hd : S5.IsSp4Data M T L k F a) :
    ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁),
        S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁)⁆ ≤ S5.bSub h.le L (baseA _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  refine commutator_nclStab_le (hc.zm_μ₁_le_qv.trans (qv_le_stab _ _))
    (S310.stab_le_normalizer_bSub h _) fun g hg => ?_
  rw [← zm_smul]
  have hgμ : IsMVtx _ (g • μ₁) := (isMVtx_smul _ _ _).2 hc.isMVtx_μ₁
  by_cases hle : ZM _ (g • μ₁) ≤ Qv _ μ₁
  · have h1 : ZM _ (g • μ₁) ≤ Subgroup.centralizer (ZM _ μ₁ : Set (puAmalgam h.le).Universal) :=
      hle.trans (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hc.isMVtx_μ₁))
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.le_centralizer_iff.1 h1)]
    exact bot_le
  ·
    have hdg : (puAmalgam h.le).treeGraph.dist (g • μ₁) (baseA _) = 2 := by
      have := dist_smul _ g μ₁ (baseA (puAmalgam h.le))
      rw [(mem_stab _).1 hg] at this
      rw [this, tdist_comm, hc.dist_μ₁]
    have hd4 : (puAmalgam h.le).treeGraph.dist (g • μ₁) μ₁ = critDist (puAmalgam h.le) := by
      have h1 := dist_triangle _ (g • μ₁) (baseA (puAmalgam h.le)) μ₁
      rw [hdg, hc.dist_μ₁] at h1
      rw [hc.b4]
      by_contra hne
      exact hle (zm_le_qv_of_dist_lt _ hgμ (by rw [hc.b4]; omega))
    have hcr : IsCritical _ (g • μ₁) μ₁ := ⟨hgμ, hd4, hle⟩
    have hcr' : IsCritical _ μ₁ (g • μ₁) := ms22_iii _ hyp hb0 h.centHyp hcr
    have h1 : ⁅ZM _ μ₁, ZM _ (g • μ₁)⁆ ≤ ZM _ (g • μ₁) :=
      Subgroup.le_normalizer_iff_commutator_le_right.1
        ((zm_le_stab_of_isCritical _ hyp hb0 hcr).trans (stab_le_normalizer_zm _ _))
    have h2 : ⁅ZM _ μ₁, ZM _ (g • μ₁)⁆ ≤ Qv _ μ₁ :=
      (Subgroup.le_normalizer_iff_commutator_le_left.1
        ((zm_le_stab_of_isCritical _ hyp hb0 hcr').trans (stab_le_normalizer_zm _ _))).trans
        (zm_le_qv_self _ hc.isMVtx_μ₁ hb0)
    have h3 := hc.inf_bSub_eq_of_crit hd hg (one_mem _) (by rwa [one_smul])
    rw [one_smul] at h3
    calc ⁅ZM _ μ₁, ZM _ (g • μ₁)⁆ ≤ ZM _ (g • μ₁) ⊓ Qv _ μ₁ := le_inf h1 h2
      _ = ZM _ (g • μ₁) ⊓ S5.bSub h.le L (baseA _) := h3.symm
      _ ≤ S5.bSub h.le L (baseA _) := inf_le_right

theorem sq_mem_bSub (hd : S5.IsSp4Data M T L k F a) {v : (puAmalgam h.le).Universal}
    (hv : v ∈ S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁)) :
    v ^ 2 ∈ S5.bSub h.le L (baseA _) := by
  refine sq_mem_of_iSup (fun g x hx => ?_) (hc.commutator_le_bSub hd) v hv
  rw [← zm_smul] at hx
  exact (hc.isElemAbelian_zm_smul _).2 x hx

theorem isPGroup_zm_μ₁ : IsPGroup 2 (ZM _ μ₁) :=
  (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _)).to_le (hc.zm_μ₁_le_qv.trans
    (qv_le_qv _ h.hyp20 (isMVtx_baseA _) (adj_baseA_baseB _)))

theorem isPGroup_nclStab : IsPGroup 2 (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁)) :=
  (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _)).to_le (hc.nclStab_le_qv.trans
    (qv_le_qv _ h.hyp20 (isMVtx_baseA _) (adj_baseA_baseB _)))

theorem zm_δ_inf_bSub_le : ZM _ δ ⊓ S5.bSub h.le L (baseA _) ≤ Qv _ μ₁ := by
  obtain ⟨y, hy, he⟩ := hc.conj₁'
  rw [he]
  exact inf_bSub_le_qv h hc.two_lt (isMVtx_baseA _) hc.isMVtx_μ₁ hc.dist_μ₁ hy

theorem zm_μ₁_inf_qv : ZM _ μ₁ ⊓ Qv _ δ = ZM _ μ₁ ⊓ S5.bSub h.le L (baseA _) := by
  obtain ⟨y, hy, hμ⟩ := hc.conj₁
  exact (zm_inf_bSub_eq h hc.two_lt (isMVtx_baseA _) hc.isMVtx_δ hc.dist_δ hy hμ
    (hc.idxB.trans hc.idxQ.symm)).symm

theorem commutator_qv_le_bSub (hd : S5.IsSp4Data M T L k F a) :
    ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.bSub h.le L (baseA _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb := hc.two_lt
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hQμ : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ μ₁ :=
    qv_le_stab_of_dist_le_two _ hyp hα hc.dist_μ₁.le
  have hQδ : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ δ :=
    qv_le_stab_of_dist_le_two _ hyp hα hc.dist_δ.le
  have hQ2 : IsPGroup 2 (Qv _ (baseA (puAmalgam h.le))) :=
    (isPGroup_qv _ hyp (not_isMVtx_baseB _)).to_le (qv_le_qv _ hyp hα (adj_baseA_baseB _))
  have := finite_zm h hc.isMVtx_δ
  have hrel : (Subgroup.centralizer (ZM _ μ₁ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) ≤ 2 ^ k := by
    calc (Subgroup.centralizer (ZM _ μ₁ : Set (puAmalgam h.le).Universal)).relIndex
          (S5.uSub h.le L δ)
        ≤ (Subgroup.centralizer (ZM _ μ₁ : Set (puAmalgam h.le).Universal)).relIndex
          (ZM _ δ) :=
          Subgroup.relIndex_le_of_le_right (S5B.uSub_le_zm h.le δ)
            Subgroup.FiniteIndex.index_ne_zero
      _ ≤ (Qv _ μ₁).relIndex (ZM _ δ) :=
          Subgroup.relIndex_le_of_le_left
            (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hc.isMVtx_μ₁))
            Subgroup.FiniteIndex.index_ne_zero
      _ ≤ (S5.bSub h.le L (baseA _)).relIndex (ZM _ δ) :=
          relIndex_qv_le_of_inf_le h hc.isMVtx_δ hc.zm_δ_inf_bSub_le
      _ = 2 ^ k := hc.relIndex_bSub_δ
  have hkey : ⁅ZM _ μ₁, Qv _ (baseA (puAmalgam h.le))⁆ ≤ S5.bSub h.le L (baseA _) := by
    have h1 : ⁅ZM _ μ₁, Qv _ (baseA (puAmalgam h.le))⁆ ≤ ZM _ μ₁ :=
      Subgroup.le_normalizer_iff_commutator_le_left.1 (hQμ.trans (stab_le_normalizer_zm _ _))
    have h2 : ⁅ZM _ μ₁, Qv _ (baseA (puAmalgam h.le))⁆ ≤ Qv _ δ :=
      commutator_le_qv_of_le_normalizer h hd hc.isMVtx_δ
        (zm_le_stab_of_isCritical _ hyp hb0 hc.crit₁') hc.isPGroup_zm_μ₁ hc.crit₁.2.2 hrel
        hQδ hQ2 (hQμ.trans (stab_le_normalizer_zm _ _))
    calc ⁅ZM _ μ₁, Qv _ (baseA (puAmalgam h.le))⁆ ≤ ZM _ μ₁ ⊓ Qv _ δ := le_inf h1 h2
      _ = ZM _ μ₁ ⊓ S5.bSub h.le L (baseA _) := hc.zm_μ₁_inf_qv
      _ ≤ S5.bSub h.le L (baseA _) := inf_le_right
  refine commutator_iSup_le (fun g => ?_) fun g => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (S310.stab_le_normalizer_bSub h _) (mul_mem (mul_mem g.2 (hc.zm_μ₁_le_qv.trans
      (qv_le_stab _ _) hx)) (inv_mem g.2))
  · have hQg := map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ _ g.2)
    have hBg := map_conj_eq_of_mem_normalizer ((S310.stab_le_normalizer_bSub h _) g.2)
    rw [← hQg, ← Subgroup.map_commutator, ← hBg]
    exact Subgroup.map_mono hkey

theorem relIndex_centralizer_le {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ)
    (hdρ : (puAmalgam h.le).treeGraph.dist (baseA _) ρ = 2)
    (hV : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) =
      S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ ρ))
    (hidx : (S5.bSub h.le L (baseA _)).relIndex (ZM _ ρ) = 2 ^ k) :
    (Subgroup.centralizer (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L ρ) ≤ 2 ^ k := by
  have := finite_zm h hρ
  have hY := inf_bSub_sup_le_centralizer_nclStab h hc.two_lt (isMVtx_baseA _) hρ hdρ
  rw [← hV] at hY
  calc (Subgroup.centralizer (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) :
        Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L ρ)
      ≤ (Subgroup.centralizer (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) :
        Set (puAmalgam h.le).Universal)).relIndex (ZM _ ρ) :=
        Subgroup.relIndex_le_of_le_right (S5B.uSub_le_zm h.le ρ)
          Subgroup.FiniteIndex.index_ne_zero
    _ ≤ (ZM _ ρ ⊓ S5.bSub h.le L (baseA _)).relIndex (ZM _ ρ) :=
        Subgroup.relIndex_le_of_le_left (le_sup_left.trans hY)
          Subgroup.FiniteIndex.index_ne_zero
    _ = 2 ^ k := by rw [Subgroup.inf_relIndex_left, hidx]

theorem exists_mul_zm_δ (hd : S5.IsSp4Data M T L k F a) {x : (puAmalgam h.le).Universal}
    (hx : x ∈ S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁)) :
    ∃ z ∈ ZM _ δ, z⁻¹ * x ∈ Qv _ μ₁ :=
  S310.exists_mem_mul_qv h hd hc.isMVtx_μ₁
    (hc.nclStab_le_qv.trans (qv_le_stab_of_dist_le_two _ h.hyp20 (isMVtx_baseA _)
      hc.dist_μ₁.le)) hc.isPGroup_nclStab hc.zm_δ_le hc.crit₁'.2.2
    (hc.relIndex_centralizer_le hc.isMVtx_μ₁ hc.dist_μ₁ rfl hc.idxB)
    (le_relIndex_qv_zm h hd hc.crit₁') hx

theorem adj_ε : (puAmalgam h.le).treeGraph.Adj μ₁ (geo _ (baseA (puAmalgam h.le)) μ₂ 3) ∧
    (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) μ₂ 3) μ₂ := by
  obtain ⟨-, -, -, -, -, -, h3, h4, -⟩ := pair_geo h hc.b4 hc.crit₂
  rw [hc.mid₂] at h3
  exact ⟨h3, h4⟩

theorem commutator_mem_zm (hd : S5.IsSp4Data M T L k F a) {x w : (puAmalgam h.le).Universal}
    (hx : x ∈ S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) ⊓ Qv _ μ₁)
    (hw : w ∈ ZM _ μ₂) : ⁅x, w⁆ ∈ ZM _ (baseA (puAmalgam h.le)) := by
  obtain ⟨y, hy, hμ⟩ := hc.conj₂
  exact S310.commutator_mem_zm h hd hc.b4 hc.crit₂ hc.isMVtx_μ₁ hc.dist_μ₁ hc.adj_ε.1
    hc.adj_ε.2 hc.idxB₂.le ⟨y, hy, hμ.symm⟩ ⟨hc.nclStab_le_qv hx.1, hx.2⟩ hw

theorem relIndex_qv_zm_μ₂ (hd : S5.IsSp4Data M T L k F a) :
    (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ μ₂) = 2 ^ k := by
  obtain ⟨y, hy, hμ⟩ := hc.conj₂
  have hle : ZM _ μ₂ ⊓ S5.bSub h.le L μ₁ ≤ Qv _ (baseA (puAmalgam h.le)) := by
    rw [hμ]
    exact inf_bSub_le_qv h hc.two_lt hc.isMVtx_μ₁ (isMVtx_baseA _)
      (by rw [tdist_comm]; exact hc.dist_μ₁) hy
  refine le_antisymm ?_ (le_relIndex_qv_zm h hd hc.crit₂')
  exact (relIndex_qv_le_of_inf_le h hc.isMVtx_μ₂ hle).trans hc.idxB₂.le

theorem relIndex_centralizer_zm_μ₂ :
    (Subgroup.centralizer (ZM _ μ₂ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (baseA _)) ≤ 2 ^ k := by
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  have := finite_zm h hα
  obtain ⟨y, hy, hμ⟩ := hc.conj₂
  have hyα : y⁻¹ • μ₂ = baseA (puAmalgam h.le) := by rw [hμ, inv_smul_smul]
  have hle : ZM _ (baseA (puAmalgam h.le)) ⊓ S5.bSub h.le L μ₁ ≤ Qv _ μ₂ := by
    have := inf_bSub_le_qv h hc.two_lt hc.isMVtx_μ₁ hc.isMVtx_μ₂ hc.dist_μ₁μ₂ (inv_mem hy)
    rwa [hyα] at this
  have hidx : (S5.bSub h.le L μ₁).relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k := by
    have := S5B.relIndex_bSub_zm_smul h y μ₁ (baseA (puAmalgam h.le))
    rw [(mem_stab _).1 hy, ← hμ] at this
    rw [← this, hc.idxB₂]
  calc (Subgroup.centralizer (ZM _ μ₂ : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L (baseA _))
      ≤ (Subgroup.centralizer (ZM _ μ₂ : Set (puAmalgam h.le).Universal)).relIndex
        (ZM _ (baseA (puAmalgam h.le))) :=
        Subgroup.relIndex_le_of_le_right (S5B.uSub_le_zm h.le _)
          Subgroup.FiniteIndex.index_ne_zero
    _ ≤ (Qv _ μ₂).relIndex (ZM _ (baseA (puAmalgam h.le))) :=
        Subgroup.relIndex_le_of_le_left
          (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hc.isMVtx_μ₂))
          Subgroup.FiniteIndex.index_ne_zero
    _ ≤ (S5.bSub h.le L μ₁).relIndex (ZM _ (baseA (puAmalgam h.le))) :=
        relIndex_qv_le_of_inf_le h hα hle
    _ = 2 ^ k := hidx

theorem le_zm_δ_sup_commutator :
    S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) ≤
      ZM _ δ ⊔ ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁), puTrans h.le L (baseA _)⁆ := by
  have hV := hc.nclStab_eq
  conv_lhs => rw [hV]
  refine iSup_le fun g => ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨l, hl, t, ht, hg⟩ := S310.exists_mul_of_mem_stab h (adj_baseA_baseB _) g.2
  have hz' : t * z * t⁻¹ ∈ ZM _ δ :=
    (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _ (qv_le_stab_of_adj _ hc.adj ht))
      z).1 hz
  have hc' : ⁅l, t * z * t⁻¹⁆ ∈
      ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁), puTrans h.le L (baseA _)⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hl (hc.zm_δ_le hz')
  have e : (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom z =
      ⁅l, t * z * t⁻¹⁆ * (t * z * t⁻¹) := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_right hc') (Subgroup.mem_sup_left hz')

end Cfg

end Cfg

end S512N

end CFSG.Quasithin.MS93
