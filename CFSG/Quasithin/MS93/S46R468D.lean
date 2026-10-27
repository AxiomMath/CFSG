module

public import CFSG.Quasithin.MS93.S46R468C4

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

@[expose] def DegW (c : Hyp46 M T L φ) (x x' : Vtx (puAmalgam c.pu.le)) : Prop :=
  Usup (puAmalgam c.pu.le) x (geo _ x x' 1) ⊓ Zloc c.pu.le L (geo _ x x' 2) ≠ ⊥

theorem inf_zloc_ne_bot_of_le_pt_sup (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {γ β : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) γ β P) {U : Subgroup (puAmalgam c.pu.le).Universal}
    (hUZ : U ≤ ZH (puAmalgam c.pu.le) β) (hUc : Nat.card ↥U = Fintype.card F ^ 2)
    (hle : U ≤ P ⊔ Zloc c.pu.le L γ) : U ⊓ Zloc c.pu.le L γ ≠ ⊥ := by
  intro hbot
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  obtain ⟨β₁, hγβ₁, hne₁, hPe⟩ := hP
  have hPU : P ≤ Uloc c.pu.le L γ := hPe ▸ inf_le_left.trans (usup_le_uloc' c.pu hfull hγ hγβ)
  have hPc : Nat.card ↥P = Fintype.card F := by
    rw [hPe]; exact card_usup_inf_usup h464 h465 c hγ hγβ hγβ₁ (Ne.symm hne₁)
  have hZs : ZM (puAmalgam c.pu.le) γ ≤ stab _ γ := (zm_le_qv_self _ hγ hb0).trans (qv_le_stab _ γ)
  have hUs : U ≤ stab (puAmalgam c.pu.le) γ := (hUZ.trans (zh_le_zm _ hγβ)).trans hZs
  have hZls : Zloc c.pu.le L γ ≤ stab (puAmalgam c.pu.le) γ := puTrans_le_stab c.pu.le _ γ
  have hPs : P ≤ stab (puAmalgam c.pu.le) γ := hPU.trans (puTrans_le_stab c.pu.le _ γ)
  have hZc : Zloc c.pu.le L γ ≤ Subgroup.centralizer (stab (puAmalgam c.pu.le) γ : Set _) :=
    zloc_le_centralizer_stab c.pu hfull hγ
  have : Finite ↥(stab (puAmalgam c.pu.le) γ) := finite_stab c.pu hγ
  have : Finite ↥(P ⊔ Zloc c.pu.le L γ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hPs hZls))
  have : Finite ↥(Zloc c.pu.le L γ) := Finite.of_injective _ (Subgroup.inclusion_injective hZls)
  have hPZ : P ⊓ Zloc c.pu.le L γ = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hPU).trans (uloc_inf_zloc c.pu hfull γ).le)
  have h1 := card_sup_of_commute (hZc.trans (Subgroup.centralizer_le hUs)) hbot
  have h2 := card_sup_of_commute (hZc.trans (Subgroup.centralizer_le hPs)) hPZ
  have h3 : Nat.card ↥(U ⊔ Zloc c.pu.le L γ) ≤ Nat.card ↥(P ⊔ Zloc c.pu.le L γ) :=
    Subgroup.card_le_of_le (sup_le hle le_sup_right)
  rw [h1, h2, hUc, hPc] at h3
  have hpos : 0 < Nat.card ↥(Zloc c.pu.le L γ) := Nat.card_pos
  have h4 := Nat.le_of_mul_le_mul_right h3 hpos
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have : Fintype.card F < Fintype.card F ^ 2 := by nlinarith
  omega

theorem degW_of_le_pt_sup (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {α α' : Vtx (puAmalgam c.pu.le)} (hc : IsCritical (puAmalgam c.pu.le) α α')
    {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) (geo _ α α' 2) (geo _ α α' 1) P)
    (hle : Usup (puAmalgam c.pu.le) α (geo _ α α' 1) ≤ P ⊔ Zloc c.pu.le L (geo _ α α' 2)) :
    DegW c α α' := by
  have hb4 := c.b4
  have hαβ := adj_geo_crit hb4 hc (i := 0) (by omega)
  rw [geo_zero] at hαβ
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  exact inf_zloc_ne_bot_of_le_pt_sup h464 h465 c (isMVtx_geo_two' hb4 hc) hβγ.symm hP
    (h464 G M T L F φ c α _ hc.1 hαβ) (h465 G M T L F φ c α _ hc.1 hαβ).1 hle

theorem exists_degW_of_le_pt_sup' (h464 : I464) (h465 : I465) (h467 : I467)
    (c : Hyp46 M T L φ) {α α' : Vtx (puAmalgam c.pu.le)} (hc : IsCritical (puAmalgam c.pu.le) α α')
    (hbad : ¬ S468Via (puAmalgam c.pu.le) α (geo _ α α' 1) (geo _ α α' 2))
    {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) P)
    (hle : Usup (puAmalgam c.pu.le) (geo _ α α' 2) (geo _ α α' 1) ≤ P ⊔ Zloc c.pu.le L α) :
    ∃ μ, IsCritical (puAmalgam c.pu.le) (geo _ α α' 2) μ ∧
      geo (puAmalgam c.pu.le) (geo _ α α' 2) μ 2 = α ∧ DegW c (geo _ α α' 2) μ := by
  have hb4 := c.b4
  have hb : 2 < critDist (puAmalgam c.pu.le) := by omega
  have hα := hc.1
  set β := geo (puAmalgam c.pu.le) α α' 1 with hβdef
  set γ := geo (puAmalgam c.pu.le) α α' 2 with hγdef
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj β γ := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hγ : IsMVtx (puAmalgam c.pu.le) γ := isMVtx_geo_two' hb4 hc
  have hZB : ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α := by
    intro hle'
    apply hbad
    intro g hg z hz v hv
    have hzB := hle' hz
    have hgB : g * z⁻¹ * g⁻¹ ∈ Bloc c.pu.le L α :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_bloc c.pu α hg.1) _).mp
        (Subgroup.inv_mem _ hzB)
    have hcB : ⁅z, g⁆ ∈ Bloc c.pu.le L α := by
      have e : ⁅z, g⁆ = z * (g * z⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hzB hgB
    rw [h467 G M T L F φ c α hα] at hcB
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hcB.2 v hv).symm]
    exact Subgroup.one_mem _
  have hd : (puAmalgam c.pu.le).treeGraph.dist γ α = 2 := by
    rw [tdist_comm, hγdef, dist_geo_crit hb4 hc (by omega)]
  obtain ⟨μ, hcμ, hgμ⟩ := exists_isCritical_geo_two h467 c hγ hα hd hZB
  have hg1 : geo (puAmalgam c.pu.le) γ μ 1 = β :=
    eq_geo_one_of_adj hb4 hcμ hβγ.symm (by rw [hgμ]; exact hαβ.symm)
  refine ⟨μ, hcμ, hgμ, ?_⟩
  rw [DegW, hg1, hgμ]
  exact inf_zloc_ne_bot_of_le_pt_sup h464 h465 c hα hαβ hP
    (h464 G M T L F φ c γ β hγ hβγ.symm) (h465 G M T L F φ c γ β hγ hβγ.symm).1 hle

theorem degW_of_not_farNonDeg (c : Hyp46 M T L φ) {α α' : Vtx (puAmalgam c.pu.le)}
    (hc : IsCritical (puAmalgam c.pu.le) α α') (hfar : ¬ FarNonDeg c α α') :
    IsCritical (puAmalgam c.pu.le) α' α ∧ DegW c α' α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  refine ⟨ms22_iii _ c.pu.hyp20 hb0 (centHyp_of_gen23 c.pu hfull) hc, ?_⟩
  rw [DegW, geo_rev_one c.b4 hc, geo_rev_two c.b4 hc]
  exact hfar

theorem nonDeg_and_farNonDeg_of (h464 : I464) (h465 : I465) (h467 : I467)
    (c : Hyp46 M T L φ) {α α' : Vtx (puAmalgam c.pu.le)} (hc : IsCritical (puAmalgam c.pu.le) α α')
    (hbad : ¬ S468Via (puAmalgam c.pu.le) α (geo _ α α' 1) (geo _ α α' 2))
    (hW : ∀ x x' : Vtx (puAmalgam c.pu.le), IsCritical (puAmalgam c.pu.le) x x' → ¬ DegW c x x') :
    NonDeg c α (geo _ α α' 1) (geo _ α α' 2) ∧ FarNonDeg c α α' := by
  refine ⟨⟨fun P hP hle => hW α α' hc (degW_of_le_pt_sup h464 h465 c hc hP hle),
    fun P hP hle => ?_⟩, ?_⟩
  · obtain ⟨μ, hcμ, -, hdeg⟩ := exists_degW_of_le_pt_sup' h464 h465 h467 c hc hbad hP hle
    exact hW _ μ hcμ hdeg
  · by_contra hfar
    obtain ⟨hc', hdeg⟩ := degW_of_not_farNonDeg c hc hfar
    exact hW α' α hc' hdeg

end CFSG.Quasithin.MS93.S46R
