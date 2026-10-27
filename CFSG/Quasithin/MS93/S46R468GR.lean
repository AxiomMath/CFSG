module

public import CFSG.Quasithin.MS93.S46R468GB
public import CFSG.Quasithin.MS93.S46R468C4
public import CFSG.Quasithin.MS93.S46R468GA

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem exists_mem_zm_not_mem_zh (h465 : I465) (c : Hyp46 M T L φ)
    {x ρ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxρ : (puAmalgam c.pu.le).treeGraph.Adj x ρ) :
    ∃ y ∈ ZM (puAmalgam c.pu.le) x, y ∉ ZH (puAmalgam c.pu.le) ρ := by
  have hidx := (h465 G M T L F φ c x ρ hx hxρ).2.1
  by_contra hno
  have h1 : (ZH (puAmalgam c.pu.le) ρ).relIndex (ZM _ x) = 1 :=
    Subgroup.relIndex_eq_one.mpr fun y hy => by_contra fun hn => hno ⟨y, hy, hn⟩
  rw [h1] at hidx
  have : 2 ≤ Fintype.card F := Fintype.one_lt_card
  omega

theorem le_qv_of_commutator_zm_eq_bot (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {x ρ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxρ : (puAmalgam c.pu.le).treeGraph.Adj x ρ) {A : Subgroup (puAmalgam c.pu.le).Universal}
    (hA : A ≤ Qv (puAmalgam c.pu.le) ρ) (h : ⁅ZM (puAmalgam c.pu.le) x, A⁆ = ⊥) :
    A ≤ Qv (puAmalgam c.pu.le) x := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  obtain ⟨y, hy, hyρ⟩ := exists_mem_zm_not_mem_zh h465 c hx hxρ
  intro t ht
  have h1 : ⁅y, t⁆ = 1 := by
    have := Subgroup.commutator_mem_commutator hy ht
    rwa [h, Subgroup.mem_bot] at this
  exact mem_qv_of_commute c.pu c.via h464' hsq h466 hx hxρ hy hyρ (hA ht)
    (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem critR_eq_of_comm_le (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    (hN : ∀ x, IsMVtx (puAmalgam c.pu.le) x →
      ⁅Vv (puAmalgam c.pu.le) x, Vv _ x⁆ ≤ Uloc c.pu.le L x)
    {α α' : Vtx (puAmalgam c.pu.le)} (hc : IsCritical (puAmalgam c.pu.le) α α') :
    ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ =
        Usup (puAmalgam c.pu.le) (geo _ α α' 2) (geo _ α α' 1) ⊓
          Usup _ (geo _ α α' 2) (geo _ α α' 3) ∧
      IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ ∧
      IsPtOn (puAmalgam c.pu.le) (geo _ α α' 2) (geo _ α α' 1)
        ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hb4 := c.b4
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
  have hdαγ : (puAmalgam c.pu.le).treeGraph.dist γ α ≤ 2 := by
    rw [tdist_comm, hγdef, dist_geo_crit hb4 hc (by omega)]
  have hdα'γ : (puAmalgam c.pu.le).treeGraph.dist γ α' ≤ 2 := by
    rw [hγdef, dist_geo_crit_right hb4 hc (by omega)]
  have hZα'γ : ZM (puAmalgam c.pu.le) α' ≤ Qv _ γ := zm_le_qv_of_dist_lt _ hα' (by
    rw [tdist_comm, hγdef, dist_geo_crit_right hb4 hc (by omega)]; omega)
  have hZαγ : ZM (puAmalgam c.pu.le) α ≤ Qv _ γ := zm_le_qv_of_dist_lt _ hα (by
    rw [hγdef, dist_geo_crit hb4 hc (by omega)]; omega)
  have hZα'β : ZM (puAmalgam c.pu.le) α' ≤ Qv _ β := hZα'γ.trans (qv_le_qv _ c.pu.hyp20 hγ hβγ.symm)
  have hZαβ' : ZM (puAmalgam c.pu.le) α ≤ Qv _ β' := hZαγ.trans (qv_le_qv _ c.pu.hyp20 hγ hγβ')
  have hRV : ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ ≤ Uloc c.pu.le L γ :=
    (Subgroup.commutator_mono (zm_le_vv_of_dist_le_two hα hdαγ)
      (zm_le_vv_of_dist_le_two hα' hdα'γ)).trans (hN γ hγ)
  have hRβ : ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ ≤ ZH _ β := by
    refine le_trans ?_ (h464' α β hα hαβ)
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mono le_rfl hZα'β
  have hRβ' : ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ ≤ ZH _ β' := by
    rw [Subgroup.commutator_comm]
    refine le_trans ?_ (h464' α' β' hα' hβ'α'.symm)
    rw [Usup, zv_of_isMVtx _ hα']
    exact Subgroup.commutator_mono le_rfl hZαβ'
  have hR : ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ ≤ Usup _ γ β ⊓ Usup _ γ β' := by
    rw [← uloc_inf_sup_zloc c hγ (inf_le_left.trans (usup_le_uloc' c.pu hfull hγ hβγ.symm)),
      ← zh_inf_zh_eq h464 h465 c hγ hβγ.symm hγβ']
    exact le_inf (le_inf hRβ hRβ') hRV
  have hpγ : IsPtOn (puAmalgam c.pu.le) γ β (Usup _ γ β ⊓ Usup _ γ β') :=
    ⟨β', hγβ', usup_geo_three_ne h464 h465 h466a c hc, rfl⟩
  have hpc := card_of_isPtOn h464 h465 c hγ hβγ.symm hpγ
  have : Finite ↥(Usup (puAmalgam c.pu.le) γ β ⊓ Usup _ γ β') :=
    Nat.finite_of_card_ne_zero (by rw [hpc]; exact Fintype.card_ne_zero)
  rcases commutator_zm_trichotomy h464 h465 c hα hαβ hZα'β with h0 | ⟨P₀, hP₀, hP₀e⟩ | hU
  ·
    exfalso
    exact (ms22_iii _ c.pu.hyp20 c.pu.critDist_pos (centHyp_of_gen23 c.pu hfull) hc).2.2
      (le_qv_of_commutator_zm_eq_bot h464 h465 h466a c hα hαβ hZα'β h0)
  · have hP₀c := card_of_isPtOn h464 h465 c hα hαβ hP₀
    have heq : ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ = Usup _ γ β ⊓ Usup _ γ β' :=
      Subgroup.eq_of_le_of_card_ge hR (by rw [hP₀e, hP₀c, hpc])
    refine ⟨heq, hP₀e ▸ hP₀, heq ▸ hpγ⟩
  · exfalso
    have h1 := Subgroup.card_le_of_le (hU ▸ hR)
    rw [(h465 G M T L F φ c α β hα hαβ).1, hpc] at h1
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have : Fintype.card F < Fintype.card F ^ 2 := by nlinarith
    omega

theorem zm_le_ptQ_critR (h464 : I464) (c : Hyp46 M T L φ) {α α' : Vtx (puAmalgam c.pu.le)}
    (hc : IsCritical (puAmalgam c.pu.le) α α') :
    ZM (puAmalgam c.pu.le) α' ≤ ptQ _ α ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ := by
  have h464' := h464 G M T L F φ c
  have hb4 := c.b4
  have hα := hc.1
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hα' : IsMVtx (puAmalgam c.pu.le) α' := hc.isMVtx_right _ c.pu.hyp20
  have hγ : IsMVtx (puAmalgam c.pu.le) (geo _ α α' 2) := isMVtx_geo_two' hb4 hc
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hZT : ZM (puAmalgam c.pu.le) α' ≤ Qv _ (geo _ α α' 1) :=
    (zm_le_qv_of_dist_lt _ hα' (by
      rw [tdist_comm, dist_geo_crit_right hb4 hc (by omega)]; omega)).trans
      (qv_le_qv _ c.pu.hyp20 hγ hβγ.symm)
  have hRZ : ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ ≤ ZH _ (geo _ α α' 1) := by
    refine le_trans ?_ (h464' α _ hα hαβ)
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mono le_rfl hZT
  intro a ha
  refine ⟨qv_le_stab_of_adj _ hαβ.symm (hZT ha), Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun r hr => ?_), fun z hz => ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ _ (hRZ hr)) a (hZT ha)).symm
  · exact Subgroup.commutator_mem_commutator hz ha

theorem commutator_mem_zm_of_mem_commutator (c : Hyp46 M T L φ)
    {x m : Vtx (puAmalgam c.pu.le)} {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hVs : Vv (puAmalgam c.pu.le) m ≤ stab _ x)
    (hQ : ∀ v ∈ Vv (puAmalgam c.pu.le) m, ∀ t₁ ∈ ptQ (puAmalgam c.pu.le) x P,
      ∀ t₂ ∈ ptQ (puAmalgam c.pu.le) x P, ⁅⁅v, t₁⁆, t₂⁆ ∈ ZM (puAmalgam c.pu.le) x)
    {y : (puAmalgam c.pu.le).Universal} (hy : y ∈ ⁅Vv (puAmalgam c.pu.le) m, ptQ _ x P⁆)
    {t : (puAmalgam c.pu.le).Universal} (ht : t ∈ ptQ (puAmalgam c.pu.le) x P) :
    ⁅y, t⁆ ∈ ZM (puAmalgam c.pu.le) x := by
  have hZn : stab (puAmalgam c.pu.le) x ≤
      Subgroup.normalizer (ZM (puAmalgam c.pu.le) x : Set (puAmalgam c.pu.le).Universal) :=
    stab_le_normalizer_zm _ x
  have hQs : ptQ (puAmalgam c.pu.le) x P ≤ stab _ x := fun r hr => (mem_ptQ.mp hr).1
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {y | y ∈ stab (puAmalgam c.pu.le) x ∧
        ∀ t ∈ ptQ (puAmalgam c.pu.le) x P, ⁅y, t⁆ ∈ ZM (puAmalgam c.pu.le) x}
      one_mem' := ⟨Subgroup.one_mem _, fun t _ => by
        rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun t ht => ?_⟩
        have e : ⁅a * b, t⁆ = a * ⁅b, t⁆ * a⁻¹ * ⁅a, t⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hZn ha) _).mp (hb' t ht))
          (ha' t ht)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun t ht => ?_⟩
        have e : ⁅a⁻¹, t⁆ = a⁻¹ * ⁅a, t⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hZn (Subgroup.inv_mem _ ha)) _).mp
          (Subgroup.inv_mem _ (ha' t ht)) }
  have hle : ⁅Vv (puAmalgam c.pu.le) m, ptQ _ x P⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro v hv r hr
    refine ⟨?_, fun t ht => hQ v hv r hr t ht⟩
    have e : ⁅v, r⁆ = v * r * v⁻¹ * r⁻¹ := commutatorElement_def v r
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hVs hv) (hQs hr))
      (Subgroup.inv_mem _ (hVs hv))) (Subgroup.inv_mem _ (hQs hr))
  exact (hle hy).2 t ht

end CFSG.Quasithin.MS93.S46R
