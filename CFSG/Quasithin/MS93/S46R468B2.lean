module

public import CFSG.Quasithin.MS93.S46R468B1
public import CFSG.Quasithin.MS93.S46I4612

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

section Center

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

private theorem conj_eq_of_mem_stabCenter' {δ : Vtx X} {a z : X.Universal} (ha : a ∈ stab X δ)
    (hz : z ∈ stabCenter X δ) : a * z * a⁻¹ = z := by
  obtain ⟨w, hw, rfl⟩ := hz
  have h1 : a * (w : X.Universal) = w * a :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨a, ha⟩)
  show a * (w : X.Universal) * a⁻¹ = w
  rw [h1, mul_inv_cancel_right]

end Center

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem s468At_of_forall_s468Via (c : Hyp46 M T L φ) {α β : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    (h : ∀ γ, (puAmalgam c.pu.le).treeGraph.Adj β γ → S468Via (puAmalgam c.pu.le) α β γ) :
    S468At (puAmalgam c.pu.le) α β := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hαβ).mp hα
  intro g hg x hx v hv
  have hgV : g ∈ Subgroup.normalizer (Vv (puAmalgam c.pu.le) β : Set _) :=
    normalizer_qv_le_normalizer_vv c.pu hβ hg.2.1
  have hVs : Vv (puAmalgam c.pu.le) β ≤ stab (puAmalgam c.pu.le) α :=
    (I466b.vv_le_vv_of_adj c.pu hα hαβ).trans (vv_le_stab_self c α)
  have hgy : ∀ y ∈ Vv (puAmalgam c.pu.le) β, g * y * g⁻¹ ∈ Vv (puAmalgam c.pu.le) β :=
    fun y hy => (Subgroup.mem_normalizer_iff.mp hgV y).mp hy
  have hcV : ∀ y ∈ Vv (puAmalgam c.pu.le) β, ⁅y, g⁆ ∈ Vv (puAmalgam c.pu.le) β := fun y hy => by
    have e : ⁅y, g⁆ = y * (g * y⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hy (hgy _ (Subgroup.inv_mem _ hy))
  have hcm : ∀ y₁ ∈ Vv (puAmalgam c.pu.le) β, ∀ y₂ ∈ Vv (puAmalgam c.pu.le) β,
      ⁅y₁ * y₂, g⁆ = ⁅y₁, g⁆ * ⁅y₂, g⁆ := fun y₁ hy₁ y₂ hy₂ => by
    have hz₁ := hgy _ (Subgroup.inv_mem _ hy₁)
    have hz₂ := hgy _ (Subgroup.inv_mem _ hy₂)
    have hcomm : (y₂ * (g * y₂⁻¹ * g⁻¹)) * (g * y₁⁻¹ * g⁻¹) =
        (g * y₁⁻¹ * g⁻¹) * (y₂ * (g * y₂⁻¹ * g⁻¹)) :=
      vv_comm c.pu hb hβ (Subgroup.mul_mem _ hy₂ hz₂) hz₁
    calc ⁅y₁ * y₂, g⁆ = y₁ * ((y₂ * (g * y₂⁻¹ * g⁻¹)) * (g * y₁⁻¹ * g⁻¹)) := by
          rw [commutatorElement_def]; group
      _ = y₁ * ((g * y₁⁻¹ * g⁻¹) * (y₂ * (g * y₂⁻¹ * g⁻¹))) := by rw [hcomm]
      _ = ⁅y₁, g⁆ * ⁅y₂, g⁆ := by simp only [commutatorElement_def]; group
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {y | y ∈ Vv (puAmalgam c.pu.le) β ∧ ⁅⁅y, g⁆, v⁆ ∈ stabCenter (puAmalgam c.pu.le) α}
      one_mem' := ⟨Subgroup.one_mem _, by
        rw [commutatorElement_one_left, commutatorElement_one_left]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, hy₁'⟩ ⟨hy₂, hy₂'⟩
        refine ⟨Subgroup.mul_mem _ hy₁ hy₂, ?_⟩
        rw [hcm y₁ hy₁ y₂ hy₂]
        have e : ⁅⁅y₁, g⁆ * ⁅y₂, g⁆, v⁆ =
            ⁅y₁, g⁆ * ⁅⁅y₂, g⁆, v⁆ * ⁅y₁, g⁆⁻¹ * ⁅⁅y₁, g⁆, v⁆ := by
          simp only [commutatorElement_def]; group
        rw [e, conj_eq_of_mem_stabCenter' (hVs (hcV y₁ hy₁)) hy₂']
        exact Subgroup.mul_mem _ hy₂' hy₁'
      inv_mem' := by
        rintro y ⟨hy, hy'⟩
        refine ⟨Subgroup.inv_mem _ hy, ?_⟩
        have hinv : ⁅y⁻¹, g⁆ = ⁅y, g⁆⁻¹ := by
          have h1 := hcm y hy y⁻¹ (Subgroup.inv_mem _ hy)
          rw [mul_inv_cancel, commutatorElement_one_left] at h1
          exact eq_inv_of_mul_eq_one_right h1.symm
        rw [hinv]
        have e : ⁅⁅y, g⁆⁻¹, v⁆ = ⁅y, g⁆⁻¹ * ⁅⁅y, g⁆, v⁆⁻¹ * ⁅y, g⁆⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e, conj_eq_of_mem_stabCenter' (Subgroup.inv_mem _ (hVs (hcV y hy)))
          (Subgroup.inv_mem _ hy')]
        exact Subgroup.inv_mem _ hy' }
  have hVS : Vv (puAmalgam c.pu.le) β ≤ S := by
    rw [vv_eq_iSup_of_not_isMVtx hβ]
    refine iSup₂_le fun γ hβγ => fun z hz => ⟨?_, h γ hβγ g hg z hz v hv⟩
    have hγ : IsMVtx (puAmalgam c.pu.le) γ := by have := isMVtx_iff_of_adj _ hβγ; tauto
    exact zm_le_vv_of_adj hβγ hγ hz
  exact (hVS hx).2

theorem exists_crit_of_not_s468At (h43 : S43) (h467 : I467) (c : Hyp46 M T L φ)
    {α β : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (h : ¬ S468At (puAmalgam c.pu.le) α β) :
    ∃ α', IsCritical (puAmalgam c.pu.le) α α' ∧ geo (puAmalgam c.pu.le) α α' 1 = β ∧
      ¬ S468Via (puAmalgam c.pu.le) α β (geo _ α α' 2) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  obtain ⟨γ, hβγ, hγbad⟩ : ∃ γ, (puAmalgam c.pu.le).treeGraph.Adj β γ ∧
      ¬ S468Via (puAmalgam c.pu.le) α β γ := by
    by_contra hno
    exact h (s468At_of_forall_s468Via c hα hαβ fun γ hβγ =>
      by_contra fun hn => hno ⟨γ, hβγ, hn⟩)
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hαβ).mp hα
  have hγ : IsMVtx (puAmalgam c.pu.le) γ := by
    by_contra hn
    exact hβ ((isMVtx_iff_of_adj _ hβγ).mpr hn)
  have hne : α ≠ γ := by
    rintro rfl
    apply hγbad
    intro g hg z hz v hv
    have hzg : ⁅z, g⁆ ∈ ZM (puAmalgam c.pu.le) α := zh_le_zm _ hαβ (hg.2.2.1 z hz)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (commute_zm_vv c.pu hb hα hzg hv)]
    exact Subgroup.one_mem _
  have hZB : ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α := by
    intro hle
    apply hγbad
    intro g hg z hz v hv
    have hzB := hle hz
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
  have hd : (puAmalgam c.pu.le).treeGraph.dist α γ = 2 := dist_eq_two_of_adj_adj _ hαβ hβγ hne
  have hd' : (puAmalgam c.pu.le).treeGraph.dist γ α = 2 := by rw [tdist_comm]; exact hd
  obtain ⟨μ, hcμ, hgμ⟩ := exists_isCritical_geo_two h467 c hγ hα hd' hZB
  have hVQ : ¬ Vv (puAmalgam c.pu.le) γ ≤ Qv _ α := by
    have := h43 G M T L c.pu c.min hb hfull γ μ hcμ
    rwa [geo_rev_two c.b4 hcμ, hgμ] at this
  obtain ⟨α', hc', hg'⟩ :=
    exists_isCritical_of_not_vv_le_qv c.pu.hyp20 (centHyp_of_gen23 c.pu hfull) c.b4 hγ hd hVQ
  refine ⟨α', hc', eq_geo_one_of_adj c.b4 hc' hαβ (by rw [hg']; exact hβγ), ?_⟩
  rw [hg']
  exact hγbad

theorem BadConf.exists_center (h464 : I464) (h465 : I465) (h466a : I466a)
    {c : Hyp46 M T L φ} {α α' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α α') :
    ∃ p, IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) p ∧
      ZM (puAmalgam c.pu.le) α' ≤ Qv _ (geo _ α α' 1) ⊓ ptQ (puAmalgam c.pu.le) α p := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  have hc := hB.crit
  have hb4 := c.b4
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by omega
  have hα := hc.1
  set β := geo (puAmalgam c.pu.le) α α' 1 with hβdef
  set γ := geo (puAmalgam c.pu.le) α α' 2 with hγdef
  set β' := geo (puAmalgam c.pu.le) α α' 3 with hβ'def
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj β γ := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hγβ' : (puAmalgam c.pu.le).treeGraph.Adj γ β' := adj_geo_crit hb4 hc (i := 2) (by omega)
  have hβ'α' : (puAmalgam c.pu.le).treeGraph.Adj β' α' := by
    have := adj_geo_crit hb4 hc (i := 3) (by omega)
    rwa [show (3 : ℕ) + 1 = 4 from rfl, geo_four hb4 hc] at this
  have hγ : IsMVtx (puAmalgam c.pu.le) γ := isMVtx_geo_two' hb4 hc
  have hα' : IsMVtx (puAmalgam c.pu.le) α' := hc.isMVtx_right _ c.pu.hyp20
  have hβ' : ¬ IsMVtx (puAmalgam c.pu.le) β' := not_isMVtx_geo_three hb4 hc
  have hne : Usup (puAmalgam c.pu.le) γ β' ≠ Usup _ γ β := by
    intro heq
    have hQ : Qv (puAmalgam c.pu.le) β = Qv _ β' :=
      qv_eq_of_usup_eq h464 h465 h466a c hγ hβγ.symm hγβ' heq.symm
    have hV : Vv (puAmalgam c.pu.le) β = Vv _ β' :=
      vv_eq_of_usup_eq h464 h465 h466a c hγ hβγ.symm hγβ' heq.symm
    have hidx := (h465 G M T L F φ c α' β' hα' hβ'α'.symm).2.1
    obtain ⟨y, hy, hyβ'⟩ : ∃ y ∈ ZM (puAmalgam c.pu.le) α', y ∉ ZH (puAmalgam c.pu.le) β' := by
      by_contra hno
      have h1 : (ZH (puAmalgam c.pu.le) β').relIndex (ZM _ α') = 1 :=
        Subgroup.relIndex_eq_one.mpr fun y hy => by_contra fun hn => hno ⟨y, hy, hn⟩
      rw [h1] at hidx
      have : 2 ≤ Fintype.card F := Fintype.one_lt_card
      omega
    apply hc.2.2
    intro t ht
    have htT : t ∈ Qv (puAmalgam c.pu.le) β' :=
      hQ ▸ (zm_le_qv_self _ hα hb0).trans (qv_le_qv _ c.pu.hyp20 hα hαβ) ht
    have hcomm : t * y = y * t := by
      have htV : t ∈ Vv (puAmalgam c.pu.le) β' := hV ▸ zm_le_vv_of_adj hαβ.symm hα ht
      exact vv_comm c.pu (by omega) hβ' htV (zm_le_vv_of_adj hβ'α' hα' hy)
    exact mem_qv_of_commute c.pu c.via h464' hsq h466 hα' hβ'α'.symm hy hyβ' htT hcomm
  have hP : IsPtOn (puAmalgam c.pu.le) γ β (Usup _ γ β ⊓ Usup _ γ β') := ⟨β', hγβ', hne, rfl⟩
  obtain ⟨p, hp, hle⟩ := exists_pencil_le_ptQ h464 h465 h466a c hα hαβ hγ hβγ.symm hP
    (hB.nondeg.1 _ hP)
  exact ⟨p, hp, ((zm_le_vv_of_adj hβ'α' hα').trans (vv_le_pencil hγβ' inf_le_right)).trans hle⟩

end CFSG.Quasithin.MS93.S46R
