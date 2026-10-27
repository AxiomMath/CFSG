module

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

theorem not_zm_le_bzero_of_not_s468Via (c : Hyp46 M T L φ) {α β γ : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hbad : ¬ S468Via (puAmalgam c.pu.le) α β γ) : ¬ ZM (puAmalgam c.pu.le) γ ≤ bzero c α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  intro hle
  apply hbad
  intro g hg z hz v hv
  have hgs : g ∈ stab (puAmalgam c.pu.le) α := hg.1
  have hzB := hle hz
  have hzg : ⁅z, g⁆ ∈ bzero c α := by
    have e : ⁅z, g⁆ = z * (g * z⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hzB ((Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_bzero c α hgs) _).mp (Subgroup.inv_mem _ hzB))
  exact zloc_le_stabCenter' c.pu hfull hα (hzg.2 v hv)

theorem false_of_two (h463 : I463) (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {α α' : Vtx (puAmalgam c.pu.le)}
    (hc : IsCritical (puAmalgam c.pu.le) α α')
    (hbad : ¬ S468Via (puAmalgam c.pu.le) α (geo _ α α' 1) (geo _ α α' 2))
    (hq : Fintype.card F = 2) : False := by
  have hb4 := c.b4
  have hb : 2 < critDist (puAmalgam c.pu.le) := by omega
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
  have hγβ := hβγ.symm
  have hS : ¬ S468At (puAmalgam c.pu.le) α β := fun h => hbad (h.via hβγ hγ)
  have hBW : ∀ {x}, IsMVtx (puAmalgam c.pu.le) x → ∀ μ A,
      (puAmalgam c.pu.le).treeGraph.Adj x μ → IsPtOn (puAmalgam c.pu.le) x μ A →
      ¬ ⁅Vv (puAmalgam c.pu.le) μ, ptQ _ x A⁆ ≤ bzero c x := fun {x} hx μ A hxμ hA =>
    not_commutator_vv_ptQ_le h464 h465 h466a c hS hα hαβ hx hxμ hA
  have hZ := not_zm_le_bzero_of_not_s468Via c hα hbad
  have hZV : ZM (puAmalgam c.pu.le) α' ≤ Vv _ γ :=
    (zm_le_vv_of_adj hβ'α' hα').trans (I466b.vv_le_vv_of_adj c.pu hγ hγβ')
  have hZT : ZM (puAmalgam c.pu.le) α' ≤ Qv _ β := by
    refine (zm_le_qv_of_dist_le_three hb4 hα' ?_).trans (qv_le_qv _ c.pu.hyp20 hγ hγβ)
    have h1 := dist_triangle (puAmalgam c.pu.le) α' β' γ
    rw [tdist_comm (puAmalgam c.pu.le) α' β', dist_eq_one_of_adj _ hβ'α',
      dist_eq_one_of_adj _ hγβ'.symm] at h1
    omega
  have hcrit' := ms22_iii _ c.pu.hyp20 c.pu.critDist_pos c.pu.centHyp hc
  have hne := ms22_ii _ c.pu.hyp20 c.pu.critDist_pos c.pu.centHyp hc
  obtain ⟨z', hz'Z, hz'α⟩ := IsConcreteLE.not_le_iff_exists.mp hcrit'.2.2
  have hz'γ := hZV hz'Z
  have hz'β := hZT hz'Z
  by_cases hV : Vv (puAmalgam c.pu.le) α ⊔ Qv _ γ = Qv _ β
  ·
    have hle := zm_le_centralizer_vv_of_sup_eq h463 h464 h465 h466a c hq hα hαβ hγ hγβ
      (hBW hγ) hV
    apply hne
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hZV.trans hle
  have hVT : Vv (puAmalgam c.pu.le) α ⊔ Qv _ γ ≤ Qv _ β :=
    sup_le (vv_le_qv_of_adj_isMVtx c hα hαβ) (qv_le_qv _ c.pu.hyp20 hγ hγβ)
  have hidx : (Qv (puAmalgam c.pu.le) γ).relIndex (Vv _ α ⊔ Qv _ γ) = 2 := by
    have h4 : (Qv (puAmalgam c.pu.le) γ).relIndex (Qv _ β) = 4 := by
      rw [h466a G M T L F φ c γ β hγ hγβ, hq]; norm_num
    have hmul := Subgroup.relIndex_mul_relIndex (Qv (puAmalgam c.pu.le) γ)
      (Vv _ α ⊔ Qv _ γ) (Qv _ β) le_sup_right hVT
    rw [h4] at hmul
    have hb1 : (Vv (puAmalgam c.pu.le) α ⊔ Qv _ γ).relIndex (Qv _ β) ≠ 1 := fun h1 =>
      hV (le_antisymm hVT (Subgroup.relIndex_eq_one.mp h1))
    have ha1 : (Qv (puAmalgam c.pu.le) γ).relIndex (Vv _ α ⊔ Qv _ γ) ≠ 1 := fun h1 => hZ (by
      intro z hz
      refine ⟨(zm_le_vv_of_adj hβγ hγ).trans (I466b.vv_le_vv_of_adj c.pu hα hαβ) hz,
        fun v hv => ?_⟩
      have hvγ : v ∈ Qv (puAmalgam c.pu.le) γ :=
        Subgroup.relIndex_eq_one.mp h1 (Subgroup.mem_sup_left hv)
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp
        (zm_le_centralizer_qv _ c.pu.hyp20 hγ hz) v hvγ).symm]
      exact Subgroup.one_mem _)
    have hdvd : (Qv (puAmalgam c.pu.le) γ).relIndex (Vv _ α ⊔ Qv _ γ) ∣ 4 := ⟨_, hmul.symm⟩
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : (Qv (puAmalgam c.pu.le) γ).relIndex (Vv _ α ⊔ Qv _ γ)
    · omega
    · exact absurd rfl ha1
    · rfl
    · omega
    · omega
  obtain ⟨δ₁, δ₂, δ₃, h₁, h₂, h₃, n₁₂, n₁₃, n₂₃⟩ := exists_three_isPtOn h464 h465 c hα hαβ
  set Inact : Subgroup (puAmalgam c.pu.le).Universal → Prop := fun d =>
    ∀ m, (puAmalgam c.pu.le).treeGraph.Adj α m → d ≤ Usup (puAmalgam c.pu.le) α m →
      Vv (puAmalgam c.pu.le) m ≤ Qv _ γ with hInact
  have hact : ∀ {d d'}, IsPtOn (puAmalgam c.pu.le) α β d → IsPtOn (puAmalgam c.pu.le) α β d' →
      d ≠ d' → Inact d ∨ Inact d' := by
    intro d d' hd hd' hdd'
    by_contra hno
    push Not at hno
    obtain ⟨hn, hn'⟩ := hno
    simp only [hInact] at hn hn'
    push Not at hn hn'
    obtain ⟨m, hαm, hdm, hm⟩ := hn
    obtain ⟨m', hαm', hdm', hm'⟩ := hn'
    obtain ⟨y, hy, hyγ⟩ := IsConcreteLE.not_le_iff_exists.mp hm
    obtain ⟨y', hy', hy'γ⟩ := IsConcreteLE.not_le_iff_exists.mp hm'
    exact false_of_two_active h464 h465 h466a c hq hα hαβ hγ hγβ hZ hidx hd hd' hdd' hαm hαm'
      hdm hdm' hy hyγ hy' hy'γ
  have key : ∀ {d₁ d₂ d₃}, IsPtOn (puAmalgam c.pu.le) α β d₁ →
      IsPtOn (puAmalgam c.pu.le) α β d₂ → IsPtOn (puAmalgam c.pu.le) α β d₃ → d₁ ≠ d₂ →
      d₁ ≠ d₃ → d₂ ≠ d₃ → Inact d₁ → Inact d₂ → False := by
    intro d₁ d₂ d₃ k₁ k₂ k₃ m₁₂ m₁₃ m₂₃ hi₁ hi₂
    by_cases hz₁ : z' ∈ ptQ (puAmalgam c.pu.le) α d₁
    · exact false_of_inactive_mem_ptQ h464 h465 h466a c hq hα hαβ hγ hγβ (hBW hα) k₁ k₂ m₁₂ hi₁
        hz'γ hz'β hz₁ hz'α
    by_cases hz₂ : z' ∈ ptQ (puAmalgam c.pu.le) α d₂
    · exact false_of_inactive_mem_ptQ h464 h465 h466a c hq hα hαβ hγ hγβ (hBW hα) k₂ k₁
        (Ne.symm m₁₂) hi₂ hz'γ hz'β hz₂ hz'α
    exact false_of_two_inactive h464 h465 h466a c hq hα hαβ hγ hγβ (hBW hα) k₁ k₂ k₃ m₁₂ m₁₃
      m₂₃ hi₁ hi₂ hz'γ hz'β hz₁ hz₂
  rcases hact h₁ h₂ n₁₂ with hi₁ | hi₂
  · rcases hact h₂ h₃ n₂₃ with hi₂ | hi₃
    · exact key h₁ h₂ h₃ n₁₂ n₁₃ n₂₃ hi₁ hi₂
    · exact key h₁ h₃ h₂ n₁₃ n₁₂ (Ne.symm n₂₃) hi₁ hi₃
  · rcases hact h₁ h₃ n₁₃ with hi₁ | hi₃
    · exact key h₁ h₂ h₃ n₁₂ n₁₃ n₂₃ hi₁ hi₂
    · exact key h₂ h₃ h₁ n₂₃ (Ne.symm n₁₂) (Ne.symm n₁₃) hi₂ hi₃

end CFSG.Quasithin.MS93.S46R
