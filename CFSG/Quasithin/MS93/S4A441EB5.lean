module

public import CFSG.Quasithin.MS93.S4A441EB1
public import CFSG.Quasithin.MS93.S4A441EB

public section

namespace CFSG.Quasithin.MS93.S4A.X441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Grp

variable {Γ : Type*} [Group Γ]

theorem le_normalizer_of_le_normalizer_map_conj {H Y : Subgroup Γ} {g : Γ} (hg : g ∈ H)
    (hn : H ≤ Subgroup.normalizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup Γ) : Set Γ)) :
    H ≤ Subgroup.normalizer (Y : Set Γ) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e1 : ∀ z : Γ, g * z * g⁻¹ ∈ Y.map (MulAut.conj g).toMonoidHom ↔ z ∈ Y := fun z => by
    rw [mem_map_conj, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
  have key := (Subgroup.mem_normalizer_iff.mp
    (hn (H.mul_mem (H.mul_mem hg hl) (H.inv_mem hg)))) (g * y * g⁻¹)
  rwa [show g * l * g⁻¹ * (g * y * g⁻¹) * (g * l * g⁻¹)⁻¹ = g * (l * y * l⁻¹) * g⁻¹ by group,
    e1, e1] at key

end Grp

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem inf_stab_le_normalizer (ρ α : Vtx 𝔛) :
    stab 𝔛 ρ ⊓ stab 𝔛 α ≤
      Subgroup.normalizer ((⁅ZM 𝔛 ρ, Qv 𝔛 α⁆ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘) :=
  le_normalizer_of_map_conj_le fun t ht => by
    rw [Subgroup.map_sup, Subgroup.map_commutator, ← zm_smul, ← qv_smul, ← zm_smul,
      (mem_stab _).mp (Subgroup.mem_inf.mp ht).1, (mem_stab _).mp (Subgroup.mem_inf.mp ht).2]

theorem geo_eq_of_dist_eq (hb : 4 < critDist 𝔛) {δ α ν : Vtx 𝔛}
    (hdαδ : (puAmalgam h.le).treeGraph.dist α δ = 2)
    (hdαν : (puAmalgam h.le).treeGraph.dist α ν = critDist 𝔛 - 2)
    (hdδν : (puAmalgam h.le).treeGraph.dist δ ν = critDist 𝔛) :
    geo 𝔛 δ ν 2 = α ∧ geo 𝔛 δ ν 1 = geo 𝔛 δ α 1 := by
  have hdδα : (puAmalgam h.le).treeGraph.dist δ α = 2 := by
    rw [tdist_comm]
    exact hdαδ
  have hadd : (puAmalgam h.le).treeGraph.dist δ ν =
      (puAmalgam h.le).treeGraph.dist δ α + (puAmalgam h.le).treeGraph.dist α ν := by
    omega
  exact ⟨(eq_geo_of_dist _ hdδα (by omega)).symm, geo_eq_of_dist_eq_add _ hadd (by omega)⟩

theorem isCritical_of_not_le_normalizer_sup (hb : 4 < critDist 𝔛) {lam α δ : Vtx 𝔛}
    (hcl : IsCritical 𝔛 lam α) (h3 : ⁅ZM 𝔛 lam, Vv 𝔛 α ⊓ Qv 𝔛 (geo 𝔛 lam α 2)⁆ ≤ ZM 𝔛 α)
    (hδ : IsMVtx 𝔛 δ) (hdδ : (puAmalgam h.le).treeGraph.dist α δ = 2)
    (hN : ¬ ZM 𝔛 lam ≤ Subgroup.normalizer ((ZM 𝔛 δ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘)) :
    IsCritical 𝔛 δ (geo 𝔛 lam α 2) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist lam α = critDist 𝔛 := hcl.2.1
  have hdαν : (puAmalgam h.le).treeGraph.dist α (geo 𝔛 lam α 2) = critDist 𝔛 - 2 := by
    rw [tdist_comm, dist_geo_right _ (by omega), hd]
  have hδV : ZM 𝔛 δ ≤ Vv 𝔛 α := by
    have := zv_le_vv h (α := α) (ρ := δ) hdδ.le
    rwa [zv_of_isMVtx _ hδ] at this
  have hZn : ZM 𝔛 lam ≤ Subgroup.normalizer (ZM 𝔛 α : Set 𝔘) :=
    (zm_le_stab_right _ h20 hb0 h.centHyp hcl).trans (stab_le_normalizer_zm _ α)
  have hnot : ¬ ZM 𝔛 δ ≤ Qv 𝔛 (geo 𝔛 lam α 2) := by
    intro hle
    apply hN
    refine le_normalizer_sup_of_commutator_le hZn ?_
    rw [Subgroup.commutator_comm]
    exact ((Subgroup.commutator_mono le_rfl (le_inf hδV hle)).trans h3).trans le_sup_right
  have hdδα : (puAmalgam h.le).treeGraph.dist δ α = 2 := by
    rw [tdist_comm]
    exact hdδ
  have t := dist_triangle 𝔛 δ α (geo 𝔛 lam α 2)
  refine ⟨hδ, ?_, hnot⟩
  by_contra hne
  exact hnot (zm_le_qv_of_dist_lt _ hδ (by omega))

end Vertex

section Full

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem map_conj_uloc_inf_centralizer {μ σ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμσ : 𝔄 μ σ) (g : 𝔘) :
    (Uloc h.le L μ ⊓ Subgroup.centralizer (Qv 𝔛 σ : Set 𝔘)).map (MulAut.conj g).toMonoidHom =
      Uloc h.le L (g • μ) ⊓ Subgroup.centralizer (Qv 𝔛 (g • σ) : Set 𝔘) := by
  rw [← zh_inf_uloc h hfull hμ hμσ,
    ← zh_inf_uloc h hfull ((isMVtx_smul _ g μ).mpr hμ) ((adj_smul _ g μ σ).mpr hμσ),
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, zh_smul, uloc_smul h]

theorem le_dloc_of_le_normalizer {α β : Vtx 𝔛} (hα : IsMVtx 𝔛 α) (hαβ : 𝔄 α β)
    {X K : Subgroup 𝔘} (hXQ : X ≤ Qv 𝔛 α) (hXZ : X ≤ ZH 𝔛 β)
    (hn : stab 𝔛 α ≤ Subgroup.normalizer (X : Set 𝔘)) (hK : K ≤ Qv 𝔛 β)
    (hKQ : ¬ K ≤ Qv 𝔛 α) : X ≤ Dloc h.le L α := by
  have hXK : ⁅X, K⁆ ≤ ⊥ := by
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (hXZ.trans (zh_le_centralizer _ β)).trans (Subgroup.centralizer_le hK)
  have hbot : stab 𝔛 α ≤ Subgroup.normalizer ((⊥ : Subgroup 𝔘) : Set 𝔘) :=
    le_normalizer_of_map_conj_le fun _ _ => by rw [Subgroup.map_bot]
  have hL := S46.commutator_ltil_le_of_commutator_le h hfull hα hαβ hn hbot hXK hK hKQ
  rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hL
  rw [Dloc, h.puTrans_Dq hα]
  exact le_inf hXQ hL

theorem stab_eq_conjCl_sup_qv {lam α : Vtx 𝔛} (hcl : IsCritical 𝔛 lam α) :
    stab 𝔛 α = conjCl (stab 𝔛 α) (ZM 𝔛 lam) ⊔ Qv 𝔛 (geo 𝔛 α lam 1) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hcl' := ms22_iii _ h20 hb0 h.centHyp hcl
  have hα : IsMVtx 𝔛 α := hcl'.1
  have hαβ : 𝔄 α (geo 𝔛 α lam 1) := adj_geo_one_of_isCritical _ hb0 hcl'
  have hZs : ZM 𝔛 lam ≤ stab 𝔛 α := zm_le_stab_right _ h20 hb0 h.centHyp hcl
  refine le_antisymm ((stab_eq_ltil_sup_qv_adj h hfull hα hαβ).le.trans
    (sup_le_sup_right ?_ _)) (sup_le (conjCl_le_of_le hZs) (qv_le_stab_of_adj _ hαβ.symm))
  exact S46.ltil_le_of_normal h hfull hα hαβ (conjCl_le_of_le hZs) (le_normalizer_conjCl _ _)
    (le_conjCl _ _) (zm_le_qv_geo_one _ h20 hb0 hcl') hcl.2.2

end Full

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem false_of_not_le_dloc (hG5 : S441EndB5) (hH : Hyp40 h φ) (hb : 4 < critDist 𝔛)
    {α α' : Vtx 𝔛} (hc : IsCritical 𝔛 α α')
    (hfail : ∀ g : 𝔘, ¬ Concl441 h.le L (g • α) (g • geo 𝔛 α α' 2))
    (hc1 : ∀ g : 𝔘, ¬ IsC1 h.le L (Fintype.card F) (g • geo 𝔛 α α' 2)
      (conjCl (stab 𝔛 (g • geo 𝔛 α α' 2)) (ZM 𝔛 (g • α))) (ZM 𝔛 (g • geo 𝔛 α α' 2)))
    (hB : ¬ ⁅Vv 𝔛 α, Qv 𝔛 α⁆ ≤ Bloc h.le L α) {μ lam : Vtx 𝔛}
    (hconj : ∃ g : 𝔘, g • μ = α ∧ g • α = geo 𝔛 α α' 2)
    (hcμ : IsCritical 𝔛 μ (geo 𝔛 α' α 2)) (hgeoμ : geo 𝔛 μ (geo 𝔛 α' α 2) 2 = α)
    (h2 : ⁅⁅ZM 𝔛 μ, Qv 𝔛 α⁆, ZM 𝔛 α'⁆ ≠ ⊥) (hlam : IsMVtx 𝔛 lam)
    (hdl : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 2) lam = 2)
    (hN : ¬ ZM 𝔛 μ ≤ Subgroup.normalizer
      ((⁅ZM 𝔛 lam, Qv 𝔛 (geo 𝔛 α' α 2)⁆ ⊔ ZM 𝔛 (geo 𝔛 α' α 2) : Subgroup 𝔘) : Set 𝔘))
    (hcl : IsCritical 𝔛 lam α) (hgeol : geo 𝔛 lam α 2 = geo 𝔛 α' α 2)
    (h3l : ⁅ZM 𝔛 lam, Vv 𝔛 α ⊓ Qv 𝔛 (geo 𝔛 α' α 2)⁆ ≤ ZM 𝔛 α)
    (hX : ¬ Uloc h.le L μ ⊓ Subgroup.centralizer (Qv 𝔛 (geo 𝔛 μ α 1) : Set 𝔘) ≤
      Dloc h.le L α) : False := by
  have hφ := hH.2.2
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hα : IsMVtx 𝔛 α := hc.1
  have hμ : IsMVtx 𝔛 μ := hcμ.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hcl' := ms22_iii _ h20 hb0 hC hcl
  have h3l' : ⁅ZM 𝔛 lam, Vv 𝔛 α ⊓ Qv 𝔛 (geo 𝔛 lam α 2)⁆ ≤ ZM 𝔛 α := by
    rw [hgeol]
    exact h3l
  set ν := geo 𝔛 α' α 2 with hνdef
  have hν : IsMVtx 𝔛 ν := isMVtx_geo_two _ h20 hb0 hc'
  have hdαν : (puAmalgam h.le).treeGraph.dist α ν = critDist 𝔛 - 2 := by
    rw [hνdef, tdist_comm, dist_geo_right _ (by rw [hc'.2.1]; omega), hc'.2.1]
  have hfin : ∀ δ : Vtx 𝔛, ¬ ZM 𝔛 lam ≤ Subgroup.normalizer ((Uloc h.le L δ ⊓
      Subgroup.centralizer (Qv 𝔛 (geo 𝔛 δ α 1) : Set 𝔘) : Subgroup 𝔘) : Set 𝔘) →
      ¬ Uloc h.le L δ ⊓ Subgroup.centralizer (Qv 𝔛 (geo 𝔛 δ α 1) : Set 𝔘) ≤ ZM 𝔛 ν := by
    intro δ hn hle
    refine hn (((zm_le_centralizer_zm h hlam hν ?_).trans (Subgroup.centralizer_le hle)).trans
      (Subgroup.centralizer_le_normalizer _))
    rw [tdist_comm, hdl]
    omega
  have hgen := stab_eq_conjCl_sup_qv h hfull hcl
  have hαβ : 𝔄 α (geo 𝔛 α lam 1) := adj_geo_one_of_isCritical _ hb0 hcl'
  have hZlβ : ZM 𝔛 lam ≤ Qv 𝔛 (geo 𝔛 α lam 1) := zm_le_qv_geo_one _ h20 hb0 hcl'
  obtain ⟨β, hβdef⟩ : ∃ x : Vtx 𝔛, x = geo 𝔛 α lam 1 := ⟨_, rfl⟩
  rw [← hβdef] at hgen hαβ hZlβ
  have hdμα : (puAmalgam h.le).treeGraph.dist μ α = 2 := by
    rw [← hgeoμ, dist_geo _ (by rw [hcμ.2.1]; omega)]
  have hdαμ : (puAmalgam h.le).treeGraph.dist α μ = 2 := by
    rw [tdist_comm]
    exact hdμα
  have hμσ : 𝔄 μ (geo 𝔛 μ α 1) := adj_geo_one _ (by omega)
  have hσα : 𝔄 (geo 𝔛 μ α 1) α := by
    have := adj_geo _ (u := μ) (w := α) (i := 1) (by omega)
    rwa [show geo 𝔛 μ α (1 + 1) = α from geo_of_le _ (by omega)] at this
  obtain ⟨g₀, hg₀, hg₀σ⟩ := exists_mem_stab_smul _ hσα.symm hαβ
  have hg₀α : g₀ • α = α := (mem_stab _).mp hg₀
  obtain ⟨μ₀, hμ₀def⟩ : ∃ x : Vtx 𝔛, x = g₀ • μ := ⟨_, rfl⟩
  have hμ₀ : IsMVtx 𝔛 μ₀ := by
    rw [hμ₀def]
    exact (isMVtx_smul _ g₀ μ).mpr hμ
  have hμ₀β : 𝔄 μ₀ β := by
    rw [hμ₀def, ← hg₀σ]
    exact (adj_smul _ g₀ μ _).mpr hμσ
  have hdαμ₀ : (puAmalgam h.le).treeGraph.dist α μ₀ = 2 := by
    have := dist_smul _ g₀ α μ
    rwa [hg₀α, hdαμ, ← hμ₀def] at this
  have hX₁eq : (Uloc h.le L μ ⊓ Subgroup.centralizer (Qv 𝔛 (geo 𝔛 μ α 1) : Set 𝔘)).map
      (MulAut.conj g₀).toMonoidHom =
      Uloc h.le L μ₀ ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) := by
    rw [map_conj_uloc_inf_centralizer h hfull hμ hμσ g₀, hg₀σ, hμ₀def]
  have hX₁Z : Uloc h.le L μ₀ ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) ≤ ZH 𝔛 β := by
    rw [← zh_inf_uloc h hfull hμ₀ hμ₀β]
    exact inf_le_left
  have hX₁Q : Uloc h.le L μ₀ ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) ≤ Qv 𝔛 α :=
    inf_le_left.trans ((uloc_le_zm h hfull hμ₀).trans (zm_le_qv_of_dist_lt _ hμ₀ (by
      rw [tdist_comm, hdαμ₀]
      omega)))
  have hX₁₁ : Qv 𝔛 β ≤ Subgroup.normalizer
      ((Uloc h.le L μ₀ ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) : Subgroup 𝔘) : Set 𝔘) := by
    rw [← zh_inf_uloc h hfull hμ₀ hμ₀β]
    exact (le_inf ((qv_le_stab _ β).trans (stab_le_normalizer_zh _ β))
      ((qv_le_stab_of_adj _ hμ₀β.symm).trans (stab_le_normalizer_uloc h μ₀))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hX₁₂ : ¬ stab 𝔛 α ≤ Subgroup.normalizer
      ((Uloc h.le L μ₀ ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) : Subgroup 𝔘) : Set 𝔘) := by
    intro hn
    apply hX
    have hle := le_dloc_of_le_normalizer h hfull hα hαβ hX₁Q hX₁Z hn hZlβ hcl.2.2
    intro x hx
    have hx' : g₀ * x * g₀⁻¹ ∈ Uloc h.le L μ₀ ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) := by
      rw [← hX₁eq, mem_map_conj, show g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ = x by group]
      exact hx
    have := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_dloc h α (inv_mem hg₀))
      (g₀ * x * g₀⁻¹)).mp (hle hx')
    rwa [show g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀⁻¹⁻¹ = x by group] at this
  have hvii : ∀ X₂ : Subgroup 𝔘, Qv 𝔛 β ≤ Subgroup.normalizer (X₂ : Set 𝔘) →
      ¬ stab 𝔛 α ≤ Subgroup.normalizer (X₂ : Set 𝔘) →
      ∃ g ∈ stab 𝔛 α, ¬ ZM 𝔛 lam ≤ Subgroup.normalizer ((Uloc h.le L (g • μ₀) ⊓
          Subgroup.centralizer (Qv 𝔛 (geo 𝔛 (g • μ₀) α 1) : Set 𝔘) : Subgroup 𝔘) : Set 𝔘) ∧
        ¬ ZM 𝔛 lam ≤ Subgroup.normalizer
          ((X₂.map (MulAut.conj g).toMonoidHom : Subgroup 𝔘) : Set 𝔘) := by
    intro X₂ h₂ h₂'
    obtain ⟨g, hg, hn1, hn2⟩ := ms21_vii _ hgen hX₁₁ hX₁₂ h₂ h₂'
    refine ⟨g, hg, ?_, hn2⟩
    have hgα : g • α = α := (mem_stab _).mp hg
    have hβα : 𝔄 (g • β) α := by
      have := (adj_smul _ g β α).mpr hαβ.symm
      rwa [hgα] at this
    have hd2 : (puAmalgam h.le).treeGraph.dist (g • μ₀) α = 2 := by
      rw [← hgα, dist_smul, tdist_comm, hdαμ₀]
    have hgβ : g • β = geo 𝔛 (g • μ₀) α 1 :=
      eq_geo_one _ ((adj_smul _ g μ₀ β).mpr hμ₀β) (by
        have := dist_eq_one_of_adj _ hβα
        omega)
    rw [map_conj_uloc_inf_centralizer h hfull hμ₀ hμ₀β g, hgβ] at hn1
    exact hn1
  by_cases hY : stab 𝔛 α ≤ Subgroup.normalizer
      ((⁅ZM 𝔛 μ, Qv 𝔛 α⁆ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘)
  ·
    have h₂ : Qv 𝔛 β ≤ Subgroup.normalizer ((ZM 𝔛 μ₀ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘) :=
      (le_inf ((qv_le_stab_of_adj _ hμ₀β.symm).trans (stab_le_normalizer_zm _ μ₀))
        ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_zm _ α))).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    have h₂' : ¬ stab 𝔛 α ≤
        Subgroup.normalizer ((ZM 𝔛 μ₀ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘) := by
      have hcμ₀ : IsCritical 𝔛 μ₀ (g₀ • ν) := by
        rw [hμ₀def]
        exact (isCritical_smul _ g₀ μ ν).mpr hcμ
      have hgeo₀ : geo 𝔛 μ₀ (g₀ • ν) 2 = α := by
        rw [hμ₀def, geo_smul, hgeoμ, hg₀α]
      have := ms22_iv _ h20 hb0 hC hcμ₀
      rwa [hgeo₀, xm_eq_zm h hfull hα] at this
    obtain ⟨g, hg, hn1, hn2⟩ := hvii _ h₂ h₂'
    have hgα : g • α = α := (mem_stab _).mp hg
    rw [Subgroup.map_sup, ← zm_smul, ← zm_smul, hgα] at hn2
    obtain ⟨δ, hδdef⟩ : ∃ x : Vtx 𝔛, x = g • μ₀ := ⟨_, rfl⟩
    rw [← hδdef] at hn1 hn2
    have hδ : IsMVtx 𝔛 δ := by
      rw [hδdef]
      exact (isMVtx_smul _ g μ₀).mpr hμ₀
    have hdαδ : (puAmalgam h.le).treeGraph.dist α δ = 2 := by
      rw [hδdef, ← hgα, dist_smul]
      exact hdαμ₀
    have hcδ := isCritical_of_not_le_normalizer_sup h hb hcl h3l' hδ hdαδ hn2
    rw [hgeol] at hcδ
    have hgeoδ := (geo_eq_of_dist_eq h hb hdαδ hdαν hcδ.2.1).2
    refine hfin δ hn1 ?_
    rcases uloc_inf_centralizer_le_or h hφ hb hcδ with hle | ⟨hcen, hcard⟩
    · rw [hgeoδ] at hle
      exact hle.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((zm_le_stab_right _ h20 hb0 hC hcδ).trans (stab_le_normalizer_zm _ ν)))
    · rw [hgeoδ] at hcen
      exact hG5 G M T L h F inferInstance inferInstance φ hH hb α α' hc hfail hc1 hB μ lam δ
        hconj hcμ hgeoμ h2 hdl hN hcl hX
        ⟨g * g₀, (stab 𝔛 α).mul_mem hg hg₀, by rw [mul_smul, ← hμ₀def, hδdef]⟩
        hn1 hn2 hcδ hY hcen hcard
  ·
    have hconj₂ : (⁅ZM 𝔛 μ, Qv 𝔛 α⁆ ⊔ ZM 𝔛 α).map (MulAut.conj g₀).toMonoidHom =
        ⁅ZM 𝔛 μ₀, Qv 𝔛 α⁆ ⊔ ZM 𝔛 α := by
      rw [Subgroup.map_sup, Subgroup.map_commutator, ← zm_smul, ← qv_smul, ← zm_smul, hg₀α,
        hμ₀def]
    have h₂ : Qv 𝔛 β ≤
        Subgroup.normalizer ((⁅ZM 𝔛 μ₀, Qv 𝔛 α⁆ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘) :=
      (le_inf (qv_le_stab_of_adj _ hμ₀β.symm) (qv_le_stab_of_adj _ hαβ.symm)).trans
        (inf_stab_le_normalizer h μ₀ α)
    have h₂' : ¬ stab 𝔛 α ≤
        Subgroup.normalizer ((⁅ZM 𝔛 μ₀, Qv 𝔛 α⁆ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘) := by
      rw [← hconj₂]
      exact fun hn => hY (le_normalizer_of_le_normalizer_map_conj hg₀ hn)
    obtain ⟨g, hg, hn1, hn2⟩ := hvii _ h₂ h₂'
    have hgα : g • α = α := (mem_stab _).mp hg
    rw [Subgroup.map_sup, Subgroup.map_commutator, ← zm_smul, ← qv_smul, ← zm_smul, hgα] at hn2
    obtain ⟨δ, hδdef⟩ : ∃ x : Vtx 𝔛, x = g • μ₀ := ⟨_, rfl⟩
    rw [← hδdef] at hn1 hn2
    have hδ : IsMVtx 𝔛 δ := by
      rw [hδdef]
      exact (isMVtx_smul _ g μ₀).mpr hμ₀
    have hdαδ : (puAmalgam h.le).treeGraph.dist α δ = 2 := by
      rw [hδdef, ← hgα, dist_smul]
      exact hdαμ₀
    obtain ⟨hcδ, -, -, hle⟩ :=
      isCritical_relIndex_of_not_normalizer h hφ hb hcl hδ hdαδ hn2 h3l'
    rw [hgeol] at hcδ hle
    rw [(geo_eq_of_dist_eq h hb hdαδ hdαν hcδ.2.1).2] at hle
    exact hfin δ hn1 (hle.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp
      ((zm_le_stab_right _ h20 hb0 hC hcδ).trans (stab_le_normalizer_zm _ ν))))

end Main

end CFSG.Quasithin.MS93.S4A.X441
