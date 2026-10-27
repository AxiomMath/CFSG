module

public import CFSG.Quasithin.MS93.S46R468GR
public import CFSG.Quasithin.MS93.S46R468Q2E

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem usup_geo_two_eq_of_comm_le (h43 : S43) (h464 : I464) (h465 : I465) (h466a : I466a)
    (h467 : I467) (c : Hyp46 M T L φ)
    (hN : ∀ x, IsMVtx (puAmalgam c.pu.le) x →
      ⁅Vv (puAmalgam c.pu.le) x, Vv _ x⁆ ≤ Uloc c.pu.le L x)
    {α₀ β₀ : Vtx (puAmalgam c.pu.le)} (hbad : ¬ S468At (puAmalgam c.pu.le) α₀ β₀)
    (hα₀ : IsMVtx (puAmalgam c.pu.le) α₀) (hα₀β₀ : (puAmalgam c.pu.le).treeGraph.Adj α₀ β₀)
    {α α' : Vtx (puAmalgam c.pu.le)} (hc : IsCritical (puAmalgam c.pu.le) α α') :
    Usup (puAmalgam c.pu.le) (geo _ α α' 2) (geo _ α α' 1) = Usup _ α (geo _ α α' 1) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
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
  have hα' : IsMVtx (puAmalgam c.pu.le) α' := hc.isMVtx_right _ c.pu.hyp20
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hαβ).mp hα
  have hcard : ∀ {x ρ : Vtx (puAmalgam c.pu.le)} {P : Subgroup (puAmalgam c.pu.le).Universal},
      IsMVtx (puAmalgam c.pu.le) x → (puAmalgam c.pu.le).treeGraph.Adj x ρ →
      IsPtOn (puAmalgam c.pu.le) x ρ P → Nat.card ↥P = Fintype.card F :=
    fun hx hxρ hP => card_of_isPtOn h464 h465 c hx hxρ hP
  have hfin : ∀ {x ρ : Vtx (puAmalgam c.pu.le)} {P : Subgroup (puAmalgam c.pu.le).Universal},
      IsMVtx (puAmalgam c.pu.le) x → (puAmalgam c.pu.le).treeGraph.Adj x ρ →
      IsPtOn (puAmalgam c.pu.le) x ρ P → Finite ↥P := fun hx hxρ hP =>
    Nat.finite_of_card_ne_zero (by rw [hcard hx hxρ hP]; exact Fintype.card_ne_zero)
  have hptU : ∀ {x ρ : Vtx (puAmalgam c.pu.le)} {P : Subgroup (puAmalgam c.pu.le).Universal},
      IsPtOn (puAmalgam c.pu.le) x ρ P → P ≤ Usup (puAmalgam c.pu.le) x ρ := fun hP => by
    obtain ⟨_, _, _, he⟩ := hP
    rw [he]
    exact inf_le_left
  obtain ⟨-, hRα, hRγ⟩ := critR_eq_of_comm_le h464 h465 h466a c hN hc
  set p := ⁅ZM (puAmalgam c.pu.le) α, ZM _ α'⁆ with hpdef
  have hZp : ZM (puAmalgam c.pu.le) α' ≤ ptQ _ α p := zm_le_ptQ_critR h464 c hc
  have hpc : Nat.card ↥p = Fintype.card F := hcard hα hαβ hRα
  by_contra hne
  have hUc : ∀ {x ρ : Vtx (puAmalgam c.pu.le)}, IsMVtx (puAmalgam c.pu.le) x →
      (puAmalgam c.pu.le).treeGraph.Adj x ρ → Finite ↥(Usup (puAmalgam c.pu.le) x ρ) :=
    fun hx hxρ => Nat.finite_of_card_ne_zero (by
      rw [hsq _ _ hx hxρ]; exact pow_ne_zero 2 Fintype.card_ne_zero)
  have hUle₁ : Usup (puAmalgam c.pu.le) γ β ≤ Usup _ α β → False := fun h => by
    have := hUc hα hαβ
    exact hne (Subgroup.eq_of_le_of_card_ge h (by rw [hsq _ _ hγ hβγ.symm, hsq _ _ hα hαβ]))
  have hUle₂ : Usup (puAmalgam c.pu.le) α β ≤ Usup _ γ β → False := fun h => by
    have := hUc hγ hβγ.symm
    exact hne (Subgroup.eq_of_le_of_card_ge h (by rw [hsq _ _ hγ hβγ.symm, hsq _ _ hα hαβ])).symm
  have hcardpt : ∀ {x ρ k : Vtx (puAmalgam c.pu.le)} {P : Subgroup (puAmalgam c.pu.le).Universal},
      IsMVtx (puAmalgam c.pu.le) x → (puAmalgam c.pu.le).treeGraph.Adj x ρ →
      (puAmalgam c.pu.le).treeGraph.Adj x k → Usup (puAmalgam c.pu.le) x ρ ≠ Usup _ x k →
      IsPtOn (puAmalgam c.pu.le) x ρ P → P ≤ Usup (puAmalgam c.pu.le) x k →
      P = Usup (puAmalgam c.pu.le) x ρ ⊓ Usup _ x k := fun {x ρ k P} hx hxρ hxk hρk hP hPk => by
    have hc' := card_usup_inf_usup h464 h465 c hx hxρ hxk hρk
    have : Finite ↥(Usup (puAmalgam c.pu.le) _ ρ ⊓ Usup _ _ k) :=
      Nat.finite_of_card_ne_zero (by rw [hc']; exact Fintype.card_ne_zero)
    exact Subgroup.eq_of_le_of_card_ge (le_inf (hptU hP) hPk) (by rw [hc', hcard hx hxρ hP])
  have hVαβ : Vv (puAmalgam c.pu.le) α ≤ Qv _ β :=
    (vv_le_qv c.pu hb hα).trans (qv_le_qv _ c.pu.hyp20 hα hαβ)
  have hZγVα : ZM (puAmalgam c.pu.le) γ ≤ Vv _ α :=
    zm_le_vv_of_dist_le_two hγ (dist_geo_crit hb4 hc (i := 2) (by omega)).le
  have hC2 : ⁅ZM (puAmalgam c.pu.le) γ, Vv _ α⁆ ≤ Usup _ γ β := by
    rw [Usup, zv_of_isMVtx _ hγ]
    exact Subgroup.commutator_mono le_rfl hVαβ
  have hC1 : ⁅ZM (puAmalgam c.pu.le) γ, Vv _ α⁆ ≤ Usup _ α β := by
    rw [← uloc_inf_zh h464 h465 c hα hαβ]
    exact le_inf (hC2.trans (h464' γ β hγ hβγ.symm))
      ((Subgroup.commutator_mono hZγVα le_rfl).trans (hN α hα))
  have hS43 : ¬ Vv (puAmalgam c.pu.le) α ≤ Qv _ γ := by
    have := h43 G M T L c.pu c.min hb hfull α α' hc
    rwa [geo_rev_two hb4 hc] at this
  obtain ⟨P₁, hP₁γ, hP₁e⟩ : ∃ P₁, IsPtOn (puAmalgam c.pu.le) γ β P₁ ∧
      ⁅ZM (puAmalgam c.pu.le) γ, Vv _ α⁆ = P₁ := by
    rcases commutator_zm_trichotomy h464 h465 c hγ hβγ.symm hVαβ with h0 | h1 | hU
    · exact absurd (le_qv_of_commutator_zm_eq_bot h464 h465 h466a c hγ hβγ.symm hVαβ h0) hS43
    · exact h1
    · exact (hUle₁ (hU ▸ hC1)).elim
  have hZB : ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α := by
    intro hle
    apply hS43
    refine le_qv_of_commutator_zm_eq_bot h464 h465 h466a c hγ hβγ.symm hVαβ
      (le_bot_iff.mp (Subgroup.commutator_le.mpr fun z hz v hv => ?_))
    have hzB := hle hz
    rw [h467 G M T L F φ c α hα] at hzB
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hzB.2 v hv).symm]
    exact Subgroup.one_mem _
  have hd' : (puAmalgam c.pu.le).treeGraph.dist γ α = 2 := by
    rw [tdist_comm, hγdef, dist_geo_crit hb4 hc (by omega)]
  obtain ⟨μ, hcμ, hgμ⟩ := exists_isCritical_geo_two h467 c hγ hα hd' hZB
  have hg1 : geo (puAmalgam c.pu.le) γ μ 1 = β :=
    eq_geo_one_of_adj hb4 hcμ hβγ.symm (by rw [hgμ]; exact hαβ.symm)
  obtain ⟨-, hRμγ, hRμα⟩ := critR_eq_of_comm_le h464 h465 h466a c hN hcμ
  rw [hg1] at hRμγ
  rw [hgμ, hg1] at hRμα
  have hμ : IsMVtx (puAmalgam c.pu.le) μ := hcμ.isMVtx_right _ c.pu.hyp20
  have hZμVα : ZM (puAmalgam c.pu.le) μ ≤ Vv _ α :=
    zm_le_vv_of_dist_le_two hμ (by rw [← hgμ, dist_geo_crit_right hb4 hcμ (by omega)])
  have hRμP₁ : ⁅ZM (puAmalgam c.pu.le) γ, ZM _ μ⁆ = P₁ := by
    have := hfin hγ hβγ.symm hP₁γ
    refine Subgroup.eq_of_le_of_card_ge
      ((Subgroup.commutator_mono le_rfl hZμVα).trans hP₁e.le) ?_
    rw [hcard hγ hβγ.symm hP₁γ, hcard hγ hβγ.symm hRμγ]
  have hP₁α : IsPtOn (puAmalgam c.pu.le) α β P₁ := by rw [← hRμP₁]; exact hRμα
  have hP₁p : P₁ = p := by
    by_contra hP₁ne
    exact hUle₂ (usup_le_of_isPtOn_ne h464 h465 c hα hαβ hP₁α hRα hP₁ne
      (hP₁e ▸ hC2) (hptU hRγ))
  have hCp : ⁅ZM (puAmalgam c.pu.le) γ, Vv _ α⁆ = p := hP₁e.trans hP₁p
  have hinact : ∀ n, (puAmalgam c.pu.le).treeGraph.Adj α n →
      ∀ d, IsPtOn (puAmalgam c.pu.le) α β d → d ≠ p → d ≤ Usup (puAmalgam c.pu.le) α n →
      Usup (puAmalgam c.pu.le) α n ≠ Usup _ α β → Vv (puAmalgam c.pu.le) n ≤ Qv _ γ := by
    intro n hαn d hd hdp hdn hnβ
    have hn : ¬ IsMVtx (puAmalgam c.pu.le) n := (isMVtx_iff_of_adj _ hαn).mp hα
    have hVn : Vv (puAmalgam c.pu.le) n ≤ Vv _ α := I466b.vv_le_vv_of_adj c.pu hα hαn
    refine le_qv_of_commutator_zm_eq_bot h464 h465 h466a c hγ hβγ.symm (hVn.trans hVαβ) ?_
    have hd2 : (puAmalgam c.pu.le).treeGraph.dist β n ≤ 2 := by
      have h1 := dist_triangle (puAmalgam c.pu.le) β α n
      rw [tdist_comm (puAmalgam c.pu.le) β α, dist_eq_one_of_adj _ hαβ,
        dist_eq_one_of_adj _ hαn] at h1
      exact h1
    have hden := hcardpt hα hαβ hαn (Ne.symm hnβ) hd hdn
    have h2 : ⁅ZM (puAmalgam c.pu.le) γ, Vv _ n⁆ ≤ d := by
      rw [hden, ← uloc_inf_sup_zloc c hα (inf_le_left.trans (usup_le_uloc' c.pu hfull hα hαβ)),
        ← zh_inf_zh_eq h464 h465 c hα hαβ hαn]
      exact le_inf ((Subgroup.commutator_mono (zm_le_vv_of_adj hβγ hγ) le_rfl).trans
          (commutator_vv_vv_le_zh_inf h464 c hβ hn hd2))
        ((Subgroup.commutator_mono hZγVα hVn).trans (hN α hα))
    have h1 : ⁅ZM (puAmalgam c.pu.le) γ, Vv _ n⁆ ≤ p :=
      (Subgroup.commutator_mono le_rfl hVn).trans hCp.le
    exact le_bot_iff.mp
      ((le_inf h2 h1).trans (inf_eq_bot_of_isPtOn h464 h465 c hα hαβ hd hRα hdp).le)
  obtain ⟨d, -, hd, -, -, hdp, -⟩ := exists_two_isPtOn_ne h464 h465 h466a c hα hαβ p
  obtain ⟨n₀, hαn₀, hne₀, hde₀⟩ := id hd
  have hdn₀ : d ≤ Usup (puAmalgam c.pu.le) α n₀ := by rw [hde₀]; exact inf_le_right
  have hpt₂ : IsPtOn (puAmalgam c.pu.le) α n₀ d := ⟨β, hαβ, Ne.symm hne₀, by rw [hde₀, inf_comm]⟩
  have hn₀ : ¬ IsMVtx (puAmalgam c.pu.le) n₀ := (isMVtx_iff_of_adj _ hαn₀).mp hα
  obtain ⟨a₀, ha₀, ha₀B⟩ := IsConcreteLE.not_le_iff_exists.mp
    (not_commutator_vv_ptQ_le h464 h465 h466a c hbad hα₀ hα₀β₀ hα hαn₀ hpt₂)
  have hcrev := ms22_iii _ c.pu.hyp20 c.pu.critDist_pos (centHyp_of_gen23 c.pu hfull) hc
  obtain ⟨z', hz', hz'α⟩ := IsConcreteLE.not_le_iff_exists.mp hcrev.2.2
  have hz'γ : z' ∈ Vv (puAmalgam c.pu.le) γ := zm_le_vv_of_dist_le_two hα' (by
    rw [hγdef, dist_geo_crit_right hb4 hc (by omega)]) hz'
  have hz'β : z' ∈ Qv (puAmalgam c.pu.le) β :=
    ((zm_le_qv_of_dist_lt _ hα' (by
      rw [tdist_comm, hγdef, dist_geo_crit_right hb4 hc (by omega)]; omega)).trans
      (qv_le_qv _ c.pu.hyp20 hγ hβγ.symm)) hz'
  have hz'p : z' ∈ ptQ (puAmalgam c.pu.le) α p := hZp hz'
  have ha₀V : a₀ ∈ Vv (puAmalgam c.pu.le) n₀ :=
    commutator_vv_ptQ_le_vv h464 h465 h466a c hα hαn₀ hdn₀ ha₀
  have ha₀Q : a₀ ∈ Qv (puAmalgam c.pu.le) γ := hinact n₀ hαn₀ d hd hdp hdn₀ hne₀ ha₀V
  have hx₂Z : ⁅a₀, z'⁆ ∈ ZM (puAmalgam c.pu.le) γ := by
    have := (h465 G M T L F φ c γ β hγ hβγ.symm).2.2
      (Subgroup.commutator_mem_commutator hz'γ ha₀Q)
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ this
  have hz's : z' ∈ stab (puAmalgam c.pu.le) α := qv_le_stab_of_adj _ hαβ.symm hz'β
  have hz'x : z' • α = α := MulAction.mem_stabilizer_iff.mp hz's
  obtain ⟨hαn₁, hdn₁, hn₁β⟩ := le_usup_smul_of_qv h464 c hα hαβ hz'β (hptU hd) hdn₀ hne₀ hαn₀
  have hne₁ : Usup (puAmalgam c.pu.le) α (z' • n₀) ≠ Usup _ α n₀ :=
    usup_smul_ne h464 h465 c hα hαβ hαn₀ (Ne.symm hne₀) hRα
      (by rw [← hde₀]; exact Ne.symm hdp) hz'β hz'p hz'α
  have hVn₁ : Vv (puAmalgam c.pu.le) (z' • n₀) =
      (Vv (puAmalgam c.pu.le) n₀).map (MulAut.conj z').toMonoidHom := vi_smul _ z' n₀ 2
  have hw'V : z' * a₀ * z'⁻¹ ∈ Vv (puAmalgam c.pu.le) (z' • n₀) := by
    rw [hVn₁]; exact conj_mem_map_conj ha₀V
  have hVαs : Vv (puAmalgam c.pu.le) α ≤ stab _ α := vv_le_stab_self c α
  have hw's : z' * a₀ * z'⁻¹ ∈ stab (puAmalgam c.pu.le) α :=
    hVαs (I466b.vv_le_vv_of_adj c.pu hα hαn₁ hw'V)
  have hdd : d = Usup (puAmalgam c.pu.le) α n₀ ⊓ Usup _ α (z' • n₀) :=
    hcardpt hα hαn₀ hαn₁ hne₁.symm hpt₂ hdn₁
  have hcomm_pen : ∀ k, (puAmalgam c.pu.le).treeGraph.Adj α k →
      d ≤ Usup (puAmalgam c.pu.le) α k → ∀ v ∈ Vv (puAmalgam c.pu.le) k, a₀ * v = v * a₀ := by
    intro k hαk hdk v hv
    by_cases hkn : Usup (puAmalgam c.pu.le) α k = Usup _ α n₀
    · have hVk : Vv (puAmalgam c.pu.le) k = Vv _ n₀ :=
        vv_eq_of_usup_eq h464 h465 h466a c hα hαk hαn₀ hkn
      exact vv_comm c.pu hb hn₀ ha₀V (hVk ▸ hv)
    · have hpk : IsPtOn (puAmalgam c.pu.le) α n₀ d := hpt₂
      have hdk' : d = Usup (puAmalgam c.pu.le) α k ⊓ Usup _ α n₀ := by
        have := hcardpt hα hαn₀ hαk (Ne.symm hkn) hpk hdk
        rw [this, inf_comm]
      have hcen : ⁅Vv (puAmalgam c.pu.le) n₀, ptQ _ α d⁆ ≤
          Subgroup.centralizer (Vv (puAmalgam c.pu.le) k : Set (puAmalgam c.pu.le).Universal) := by
        rw [Subgroup.commutator_le]
        intro v' hv' r hr
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact commute_vv_commutator_vv_ptQ' h464 h465 h466a c hα hαk hαn₀ hkn hu hv'
          (by rw [← hdk']; exact hr)
      exact (Subgroup.mem_centralizer_iff.mp (hcen ha₀) v hv).symm
  have hx₂B : ⁅a₀, z'⁆ ∉ bzero c α := by
    intro hxB
    apply ha₀B
    have hb : (z' * a₀ * z'⁻¹)⁻¹ * ⁅a₀, z'⁆ * (z' * a₀ * z'⁻¹) ∈ bzero c α := by
      have := (Subgroup.mem_normalizer_iff.mp
        (stab_le_normalizer_bzero c α (Subgroup.inv_mem _ hw's)) _).mp hxB
      rwa [inv_inv] at this
    refine mem_bzero_of_mem_vv_mul' h464 h465 c hα hαn₀ hαn₁ hne₁.symm ha₀V hw'V hb
      (by simp only [commutatorElement_def]; group) fun k hαk hk v hv => ?_
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (hcomm_pen k hαk (by rw [hdd]; exact hk) v hv)]
    exact Subgroup.one_mem _
  obtain ⟨g, ⟨hgn, hgd⟩, hgα⟩ := exists_mem_qv_inf_ptQ h464 h465 h466a c hα hαn₀ hpt₂
  have hgs : g ∈ stab (puAmalgam c.pu.le) α := (mem_ptQ.mp hgd).1
  have hgx : g • α = α := MulAction.mem_stabilizer_iff.mp hgs
  have hgN : g ∈ Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set _) :=
    ptQ_le_normalizer_qv h464 h465 h466a c hα hαβ (hptU hd) hgd
  have hpZ : p ≤ ZM (puAmalgam c.pu.le) α :=
    (le_uloc_of_isPtOn c hα hRα).trans (uloc_le_zm c.pu hfull hα)
  have hdp' : d ⊓ p = ⊥ := inf_eq_bot_of_isPtOn h464 h465 c hα hαβ hd hRα hdp
  have hgp : p.map (MulAut.conj g).toMonoidHom ≠ p := by
    intro hgpe
    have hgpN : g ∈ Subgroup.normalizer (p : Set (puAmalgam c.pu.le).Universal) :=
      mem_normalizer_of_map_conj_eq hgpe
    have hcen : ∀ u ∈ p, g * u = u * g := by
      intro u hu
      have h1 : ⁅u, g⁆ ∈ d := (mem_ptQ.mp hgd).2.2 u (hpZ hu)
      have h2 : ⁅u, g⁆ ∈ p := by
        have e : ⁅u, g⁆ = u * (g * u⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ hu ((Subgroup.mem_normalizer_iff.mp hgpN _).mp
          (Subgroup.inv_mem _ hu))
      have h3 : ⁅u, g⁆ = 1 := Subgroup.mem_bot.mp (hdp'.le ⟨h1, h2⟩)
      exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
    obtain ⟨y, hyp, hy1⟩ : ∃ y ∈ p, y ≠ 1 := by
      by_contra hno
      have hbot : p = ⊥ := eq_bot_iff.mpr fun y hy =>
        Subgroup.mem_bot.mpr (by by_contra h1; exact hno ⟨y, hy, h1⟩)
      have h1 : Nat.card ↥p = 1 := by rw [hbot]; exact Subgroup.card_bot
      have hq : 1 < Fintype.card F := Fintype.one_lt_card
      omega
    have hyn : y ∉ ZH (puAmalgam c.pu.le) n₀ := by
      intro hyn
      have hyU : y ∈ Usup (puAmalgam c.pu.le) α n₀ := by
        rw [← uloc_inf_zh h464 h465 c hα hαn₀]
        exact ⟨hyn, le_uloc_of_isPtOn c hα hRα hyp⟩
      have hyd : y ∈ d := by rw [hde₀]; exact ⟨hptU hRα hyp, hyU⟩
      exact hy1 (Subgroup.mem_bot.mp (hdp'.le ⟨hyd, hyp⟩))
    exact hgα (mem_qv_of_commute c.pu c.via h464' hsq h466 hα hαn₀ (hpZ hyp) hyn hgn
      (hcen y hyp))
  have hUg : Usup (puAmalgam c.pu.le) α (g • β) = Usup _ α β := by
    have e : Usup (puAmalgam c.pu.le) α (g • β) =
        (Usup (puAmalgam c.pu.le) α β).map (MulAut.conj g).toMonoidHom := by
      rw [← usup_smul, hgx]
    rw [e, Usup, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
      (stab_le_normalizer_of_smul _ (fun g' δ => zv_smul _ g' δ) α hgs),
      map_conj_eq_of_mem_normalizer hgN]
  have hgpt : IsPtOn (puAmalgam c.pu.le) α β (p.map (MulAut.conj g).toMonoidHom) := by
    have h1 := (isPtOn_smul g α β p).mpr hRα
    rw [hgx] at h1
    obtain ⟨β'', h2, h3, h4⟩ := h1
    exact ⟨β'', h2, by rw [← hUg]; exact h3, by rw [← hUg]; exact h4⟩
  have hpgp : p ⊓ p.map (MulAut.conj g).toMonoidHom = ⊥ :=
    inf_eq_bot_of_isPtOn h464 h465 c hα hαβ hRα hgpt fun h => hgp h.symm
  have hz'd : z' ∈ Subgroup.normalizer (d : Set (puAmalgam c.pu.le).Universal) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β
        (h464' α β hα hαβ (hptU hd hu))) z' hz'β).symm)
  have hz'Q : z' ∈ Subgroup.normalizer (ptQ (puAmalgam c.pu.le) α d : Set _) :=
    mem_normalizer_of_map_conj_eq (by
      rw [← ptQ_smul, hz'x, map_conj_eq_of_mem_normalizer hz'd])
  have hyC : z' * a₀⁻¹ * z'⁻¹ ∈ ⁅Vv (puAmalgam c.pu.le) (z' • n₀), ptQ _ α d⁆ := by
    have hmap : (⁅Vv (puAmalgam c.pu.le) n₀, ptQ _ α d⁆ : Subgroup _).map
        (MulAut.conj z').toMonoidHom = ⁅Vv (puAmalgam c.pu.le) (z' • n₀), ptQ _ α d⁆ := by
      rw [Subgroup.map_commutator, ← hVn₁, map_conj_eq_of_mem_normalizer hz'Q]
    rw [← hmap]
    exact conj_mem_map_conj (Subgroup.inv_mem _ ha₀)
  have hdeq₁ : d = Usup (puAmalgam c.pu.le) α (z' • n₀) ⊓ Usup _ α β := by
    rw [hcardpt hα hαβ hαn₁ (Ne.symm hn₁β) hd hdn₁, inf_comm]
  obtain ⟨α'', hc'', hU'', hZQ'', hidx''⟩ :=
    exists_root_crit h464 h465 h466a c hc hRα hZp hα hαβ hd
  have hVs : Vv (puAmalgam c.pu.le) (z' • n₀) ≤ stab _ α :=
    (I466b.vv_le_vv_of_adj c.pu hα hαn₁).trans hVαs
  have hQ : ∀ v ∈ Vv (puAmalgam c.pu.le) (z' • n₀), ∀ t₁ ∈ ptQ (puAmalgam c.pu.le) α d,
      ∀ t₂ ∈ ptQ (puAmalgam c.pu.le) α d, ⁅⁅v, t₁⁆, t₂⁆ ∈ ZM (puAmalgam c.pu.le) α :=
    fun v hv t₁ ht₁ t₂ ht₂ => commutator_commutator_mem_zm_of_root h464 h465 h466a c hα hαn₁ hαβ
      (Ne.symm hn₁β) hdeq₁ hc'' hU'' hZQ'' hidx'' hv ht₁ ht₂
  set y := z' * a₀⁻¹ * z'⁻¹ with hydef
  have hyV : y ∈ Vv (puAmalgam c.pu.le) (z' • n₀) :=
    commutator_vv_ptQ_le_vv h464 h465 h466a c hα hαn₁ hdn₁ hyC
  have hys : y ∈ stab (puAmalgam c.pu.le) α := hVs hyV
  have hs₁ : a₀⁻¹ * (g * a₀ * g⁻¹) ∈ ZM (puAmalgam c.pu.le) α := by
    have e : a₀⁻¹ * (g * a₀ * g⁻¹) = ⁅a₀⁻¹, g⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact zh_le_zm _ hαn₀ (commutator_vv_qv_le_zh c.pu h464' hn₀
      (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ ha₀V) hgn))
  have hs₂ : y⁻¹ * (g * y * g⁻¹) ∈ ZM (puAmalgam c.pu.le) α := by
    have e : y⁻¹ * (g * y * g⁻¹) = ⁅y⁻¹, g⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact commutator_mem_zm_of_mem_commutator c hVs hQ (Subgroup.inv_mem _ hyC) hgd
  set s := (y⁻¹ * (a₀⁻¹ * (g * a₀ * g⁻¹)) * y) * (y⁻¹ * (g * y * g⁻¹)) with hsdef
  have hs : s ∈ ZM (puAmalgam c.pu.le) α := by
    refine Subgroup.mul_mem _ ?_ hs₂
    have := (Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_zm _ α (Subgroup.inv_mem _ hys)) _).mp hs₁
    rwa [inv_inv] at this
  have hgx₂ : g * ⁅a₀, z'⁆ * g⁻¹ = ⁅a₀, z'⁆ * s := by
    have e : ⁅a₀, z'⁆ = a₀ * y := by rw [hydef, commutatorElement_def]; group
    rw [e, hsdef]
    group
  apply hx₂B
  refine ⟨hZγVα hx₂Z, fun v hv => ?_⟩
  have hsv : s * v = v * s :=
    (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ c.pu.hyp20 hα hs) v
      (vv_le_qv c.pu hb hα hv)).symm
  have h1 : ⁅⁅a₀, z'⁆, v⁆ ∈ p := hCp ▸ Subgroup.commutator_mem_commutator hx₂Z hv
  have hgv : g⁻¹ * v * g⁻¹⁻¹ ∈ Vv (puAmalgam c.pu.le) α :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_of_smul _
      (fun g' δ => vi_smul _ g' δ 2) α (Subgroup.inv_mem _ hgs)) v).mp hv
  have h2 : ⁅⁅a₀, z'⁆, v⁆ ∈ p.map (MulAut.conj g).toMonoidHom := by
    have h3 : ⁅⁅a₀, z'⁆, g⁻¹ * v * g⁻¹⁻¹⁆ ∈ p :=
      hCp ▸ Subgroup.commutator_mem_commutator hx₂Z hgv
    have e : ⁅⁅a₀, z'⁆, v⁆ = g * ⁅⁅a₀, z'⁆, g⁻¹ * v * g⁻¹⁻¹⁆ * g⁻¹ := by
      have e1 : ⁅⁅a₀, z'⁆ * s, v⁆ = ⁅⁅a₀, z'⁆, v⁆ := by
        simp only [commutatorElement_def]
        calc ⁅a₀, z'⁆ * s * v * (⁅a₀, z'⁆ * s)⁻¹ * v⁻¹
            = ⁅a₀, z'⁆ * (s * v) * s⁻¹ * ⁅a₀, z'⁆⁻¹ * v⁻¹ := by group
          _ = ⁅a₀, z'⁆ * (v * s) * s⁻¹ * ⁅a₀, z'⁆⁻¹ * v⁻¹ := by rw [hsv]
          _ = ⁅a₀, z'⁆ * v * ⁅a₀, z'⁆⁻¹ * v⁻¹ := by group
      rw [← e1, ← hgx₂]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_map_conj h3
  rw [Subgroup.mem_bot.mp (hpgp.le ⟨h1, h2⟩)]
  exact Subgroup.one_mem _

end CFSG.Quasithin.MS93.S46R
