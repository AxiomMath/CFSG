module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepC1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S5Vertex
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

set_option linter.unusedSectionVars false

theorem Zv_le_stab_of_dist_le' (hA : F53Amalgam H M S) {δ μ : Geo H M}
    (h : dist δ μ ≤ bMin H M) : Zv δ ≤ stab μ :=
  Zv_le_stab_of_dist_le hA (h.trans (bMin_le_bAt δ))

theorem Zv_le_Qv_of_dist_lt' {δ μ : Geo H M} (h : dist δ μ < bMin H M) : Zv δ ≤ Qv μ :=
  Zv_le_Qv_of_dist_lt (h.trans_le (bMin_le_bAt δ))

theorem mem_nbrs_symm' {δ μ : Geo H M} (h : μ ∈ nbrs δ) : δ ∈ nbrs μ :=
  (show (graph (H ⊔ M) H M).Adj δ μ from h).symm

theorem Zv_le_Qv_of_mem_nbrs {δ μ : Geo H M} (h : μ ∈ nbrs δ) (hb2 : 2 ≤ bMin H M) :
    Zv δ ≤ Qv μ :=
  Zv_le_Qv_of_dist_lt' (by
    have : dist δ μ = 1 := dist_eq_one_iff_adj.mpr h
    omega)

section Standing

variable {α β α' : Geo H M}

theorem bAt_eq_bMin (hA : F53Amalgam H M S) (h27 : Hss27At H M) (hc : IsCritData α β α') (hv : vtype α = true)
    (hn : ¬ Zv β ≤ centerOf (stab β)) : ∀ δ : Geo H M, bAt δ = bMin H M := by
  intro δ
  have hβ : bAt β = bMin H M := by
    have h1 := bMin_le_bAt (H := H) (M := M) β
    by_contra hne
    have hlt : bMin H M < bAt β := by omega
    exact hn (hss31At_of_hss27 hA h27 α β hc.adj hv hc.bAt_eq hlt)
  have hne : vtype α ≠ vtype β := vtype_ne_of_adj hc.adj
  cases h : vtype δ
  · rw [← hβ]
    exact bAt_eq_of_vtype_eq (by cases h1 : vtype β <;> simp_all)
  · rw [← hc.bAt_eq]
    exact bAt_eq_of_vtype_eq (by rw [h, hv])

theorem centralizer_Zv_eq_Qv_all (hA : F53Amalgam H M S) (h27 : Hss27At H M) (hc : IsCritData α β α')
    (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β)) :
    ∀ δ : Geo H M, stab δ ⊓ Subgroup.centralizer (Zv δ : Set G) = Qv δ :=
  fun δ => centralizer_Zv_eq_Qv_of_bAt hA (bAt_eq_bMin hA h27 hc hv hn δ)

theorem Zv_not_central_all (hA : F53Amalgam H M S) (h27 : Hss27At H M) (hc : IsCritData α β α')
    (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β)) :
    ∀ δ : Geo H M, ¬ Zv δ ≤ centerOf (stab δ) := by
  intro δ hz
  have h1 := centralizer_Zv_eq_Qv_all hA h27 hc hv hn δ
  have hcen : stab δ ≤ Subgroup.centralizer (Zv δ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hzz
    exact ((Subgroup.mem_centralizer_iff.mp (hz hzz).2) x hx).symm
  rw [inf_eq_left.mpr hcen] at h1
  exact pCoreOf_ne_stab hA δ h1.symm

theorem comm_symm_ne_bot (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) : ⁅Zv α', Zv α⁆ ≠ ⊥ := by
  rwa [Subgroup.commutator_comm]

theorem Zv_le_stab_pair (hA : F53Amalgam H M S) (hc : IsCritData α β α')
    (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) : Zv α' ≤ stab α ∧ Zv α ≤ stab α' :=
  ⟨(Zv_le_stab_of_comm_ne hA hc hcomm).2,
    Zv_le_stab_of_dist_le' hA (by rw [hc.dist_eq])⟩

theorem exists_critData_symm' (hA : F53Amalgam H M S) (h27 : Hss27At H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hn : ¬ Zv β ≤ centerOf (stab β)) :
    ∃ β' : Geo H M, IsCritData α' β' α ∧ ⁅Zv α', Zv α⁆ ≠ ⊥ ∧ ¬ Zv β' ≤ centerOf (stab β') := by
  obtain ⟨β', hc'⟩ := exists_critData_symm hA hc hcomm
  exact ⟨β', hc', comm_symm_ne_bot hcomm, Zv_not_central_all hA h27 hc hv hn β'⟩

theorem vtype_alpha'_of_even (hA : F53Amalgam H M S) (hc : IsCritData α β α')
    (hv : vtype α = true) (heven : Even (bMin H M)) : vtype α' = true := by
  have heven' : Even (dist α α') := by rw [hc.dist_eq]; exact heven
  have := (vtype_eq_iff_even_dist hA.amalgam.gen α α').mpr heven'
  rw [← this]; exact hv

theorem vtype_alpha'_of_odd (hA : F53Amalgam H M S) (hc : IsCritData α β α')
    (hv : vtype α = true) (hodd : Odd (bMin H M)) : vtype α' = false := by
  by_contra h
  have h' : vtype α' = true := by simpa using h
  have : vtype α = vtype α' := by rw [hv, h']
  have heven := (vtype_eq_iff_even_dist hA.amalgam.gen α α').mp this
  rw [hc.dist_eq] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem not_le_stab_alpha'_of_even (hA : F53Amalgam H M S) (h27 : Hss27At H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hb3 : 3 ≤ bMin H M) (hn : ¬ Zv β ≤ centerOf (stab β)) (heven : Even (bMin H M)) :
    ∀ γ ∈ nbrs α, γ ≠ β → ¬ Zv γ ≤ stab α' := by
  intro γ hγn hγβ hγ
  obtain ⟨hα', hZα'G⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  obtain ⟨-, hZαα'⟩ := Zv_le_stab_pair hA hc hcomm
  have hvα' := vtype_alpha'_of_even hA hc hv heven
  have hZγQ : Zv γ ≤ Qv α := Zv_le_Qv_of_mem_nbrs (mem_nbrs_symm' hγn) (by omega)
  have hdec : ∀ x ∈ Zv γ, ∃ a ∈ Zv α, ∃ q ∈ Qv α', x = a * q := by
    have hK : IsPGroup 2 ↥(Zv α ⊔ Zv γ) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab α)).to_le
        (sup_le (Zv_le_Qv hA α) hZγQ)
    exact fun x hx => exists_mul_of_isPGroup_of_vtype_true hA hvα' hK (sup_le hZαα' hγ)
      le_sup_left hc.not_le x (Subgroup.mem_sup_right hx)
  refine claim1_left hA (Hss27S3At_of_Hss27At h27) hc hv hcomm (by omega) hn γ hγn hγβ ?_
  rw [Subgroup.commutator_le]
  intro b hb z hz
  obtain ⟨a, ha, q, hq, rfl⟩ := hdec b hb
  have hqz : q * z = z * q := ((Subgroup.mem_centralizer_iff.mp
    (Zv_le_centerOf_Qv hA α' hz).2) q hq)
  have hzN := stab_le_normalizer_Zv hA α (hZα'G hz)
  have h1 : z * a⁻¹ * z⁻¹ ∈ Zv α := (Subgroup.mem_normalizer_iff.mp hzN _).mp ((Zv α).inv_mem ha)
  rw [commutatorElement_def]
  have : a * q * z * (a * q)⁻¹ * z⁻¹ = a * (z * a⁻¹ * z⁻¹) := by
    have : q * z * q⁻¹ = z := by rw [hqz]; group
    calc a * q * z * (a * q)⁻¹ * z⁻¹ = a * (q * z * q⁻¹) * a⁻¹ * z⁻¹ := by group
      _ = _ := by rw [this]; group
  rw [this]
  exact (Zv α).mul_mem ha h1

theorem dist_nbr_alpha'_of_even (hA : F53Amalgam H M S) (h27 : Hss27At H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hb3 : 3 ≤ bMin H M) (hn : ¬ Zv β ≤ centerOf (stab β)) (heven : Even (bMin H M)) :
    ∀ γ ∈ nbrs α, γ ≠ β → dist γ α' = bMin H M + 1 := by
  intro γ hγn hγβ
  have h1 := dist_triangle hA.amalgam.gen γ α α'
  have hγα : dist γ α = 1 := dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj γ α from hγn.symm)
  rw [hγα, hc.dist_eq] at h1
  by_contra hne
  have h2 : dist γ α' ≤ bMin H M := by omega
  exact not_le_stab_alpha'_of_even hA h27 hc hv hcomm hb3 hn heven γ hγn hγβ
    (Zv_le_stab_of_dist_le' hA h2)

omit [Finite G] in
theorem commutator_le_left_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : ⁅A, B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 : b * a⁻¹ * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hB hb) _).mp (A.inv_mem ha)
  rw [commutatorElement_def]
  have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
  rw [this]
  exact A.mul_mem ha h1

theorem dist_beta_nbr_le (hA : F53Amalgam H M S) (hc : IsCritData α β α') {c' : Geo H M}
    (hc'n : c' ∈ nbrs α') : dist β c' ≤ bMin H M := by
  have h1 := dist_triangle hA.amalgam.gen β α' c'
  have h2 : dist α' c' = 1 := dist_eq_one_iff_adj.mpr hc'n
  have h3 := hc.dist_eq'
  omega

theorem Zv_nbr_le_stab_beta (hA : F53Amalgam H M S) (hc : IsCritData α β α') {c' : Geo H M}
    (hc'n : c' ∈ nbrs α') : Zv c' ≤ stab β :=
  Zv_le_stab_of_dist_le' hA (by rw [CosetGeom.dist_comm]; exact dist_beta_nbr_le hA hc hc'n)

theorem Zv_beta_le_stab_nbr (hA : F53Amalgam H M S) (hc : IsCritData α β α') {c' : Geo H M}
    (hc'n : c' ∈ nbrs α') : Zv β ≤ stab c' :=
  Zv_le_stab_of_dist_le' hA (dist_beta_nbr_le hA hc hc'n)

theorem R₁_le_inf (hA : F53Amalgam H M S) (hc : IsCritData α β α') {c' : Geo H M}
    (hc'n : c' ∈ nbrs α') : ⁅Zv β, Zv c'⁆ ≤ Zv β ⊓ Zv c' := by
  refine le_inf ?_ ?_
  · exact commutator_le_left_of_le_normalizer
      ((Zv_nbr_le_stab_beta hA hc hc'n).trans (stab_le_normalizer_Zv hA β))
  · rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer
      ((Zv_beta_le_stab_nbr hA hc hc'n).trans (stab_le_normalizer_Zv hA c'))

theorem comm_eq_bot_of_le_Qv (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : Zv δ ≤ Qv μ) :
    ⁅Zv δ, Zv μ⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hz).2) x (h hx)).symm

theorem comm_ne_bot_iff_not_le_Qv (hA : F53Amalgam H M S) (h27 : Hss27At H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β))
    {c' : Geo H M} (hc'n : c' ∈ nbrs α') : ⁅Zv β, Zv c'⁆ ≠ ⊥ ↔ ¬ Zv c' ≤ Qv β := by
  constructor
  · intro h hle
    exact h (by rw [Subgroup.commutator_comm]; exact comm_eq_bot_of_le_Qv hA hle)
  · intro hnle h
    apply hnle
    rw [← centralizer_Zv_eq_Qv_all hA h27 hc hv hn β]
    refine le_inf (Zv_nbr_le_stab_beta hA hc hc'n) ?_
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact h

theorem not_le_Qv_beta_of_claim1 {c' : Geo H M} (hRle : ⁅Zv α, Qv β⁆ ≤ Zv α')
    (hclaim : ¬ ⁅Zv c', Zv α⁆ ≤ Zv α') : ¬ Zv c' ≤ Qv β := by
  intro h
  apply hclaim
  calc ⁅Zv c', Zv α⁆ ≤ ⁅Qv β, Zv α⁆ := Subgroup.commutator_mono h le_rfl
    _ = ⁅Zv α, Qv β⁆ := Subgroup.commutator_comm _ _
    _ ≤ Zv α' := hRle

theorem not_le_Qv_beta_of_even (hA : F53Amalgam H M S) (h27 : Hss27At H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hb3 : 3 ≤ bMin H M) (hn : ¬ Zv β ≤ centerOf (stab β)) (heven : Even (bMin H M))
    {β' : Geo H M} (hc' : IsCritData α' β' α) (hRle : ⁅Zv α, Qv β⁆ ≤ Zv α') :
    ∀ c' ∈ nbrs α', c' ≠ β' → ¬ Zv c' ≤ Qv β := fun c' hc'n hc'β =>
  not_le_Qv_beta_of_claim1 hRle
    (claim1_right hA (Hss27S3At_of_Hss27At h27) hc hc' hv
      (vtype_alpha'_of_even hA hc hv heven) hcomm (by omega) hn c' hc'n hc'β)

theorem dist_beta_nbr_eq (hA : F53Amalgam H M S) (hc : IsCritData α β α') {c' : Geo H M}
    (hc'n : c' ∈ nbrs α') (hnle : ¬ Zv c' ≤ Qv β) : dist β c' = bMin H M := by
  have h1 := dist_beta_nbr_le hA hc hc'n
  by_contra hne
  exact hnle (Zv_le_Qv_of_dist_lt' (by rw [CosetGeom.dist_comm]; omega))

theorem isCritPair₁_beta_nbr (hA : F53Amalgam H M S) (h27 : Hss27At H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β))
    {c' : Geo H M} (hc'n : c' ∈ nbrs α') (hnle : ¬ Zv c' ≤ Qv β) :
    IsCritPair₁ β c' ∧ ⁅Zv β, Zv c'⁆ ≠ ⊥ := by
  have hne := (comm_ne_bot_iff_not_le_Qv hA h27 hc hv hn hc'n).mpr hnle
  exact ⟨⟨fun hle => hne (comm_eq_bot_of_le_Qv hA hle), dist_beta_nbr_eq hA hc hc'n hnle⟩, hne⟩

theorem exists_nbr_ne (hA : F53Amalgam H M S) (δ : Geo H M) {ν : Geo H M} (hν : ν ∈ nbrs δ) :
    ∃ μ ∈ nbrs δ, μ ≠ ν := by
  have h : 1 < Nat.card (nbrs δ) := by
    cases hv : vtype δ
    · rw [card_nbrs_false hA hv]; norm_num
    · rw [card_nbrs_true hA hv]; norm_num
  have : Finite (nbrs δ) := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial (nbrs δ) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨μ, hμ⟩, hne⟩ := exists_ne (⟨ν, hν⟩ : nbrs δ)
  exact ⟨μ, hμ, fun h => hne (Subtype.ext h)⟩

theorem exists_choice_c' (hA : F53Amalgam H M S) (h28 : Hss28At H M)
    (hc : IsCritData α β α') {β' : Geo H M} (hc' : IsCritData α' β' α) (hb2 : 2 ≤ bMin H M) :
    ∃ c' ∈ nbrs α', c' ≠ β' ∧ stab α' = Zv α ⊔ (stab α' ⊓ stab c') ∧
      stab α' ⊓ stab c' = Qv α' ⊔ Qv c' := by
  have hβ'n : β' ∈ nbrs α' := hc'.adj
  have hZαβ' : Zv α ≤ stab β' :=
    Zv_le_stab_of_dist_le' hA (by have := hc'.dist_eq'; rw [CosetGeom.dist_comm]; omega)
  have hZαα' : Zv α ≤ stab α' := Zv_le_stab_of_dist_le' hA (by rw [hc.dist_eq])
  have key : ∃ c' ∈ nbrs α', c' ≠ β' ∧ stab α' = Zv α ⊔ (stab α' ⊓ stab c') := by
    cases hv : vtype α'
    · obtain ⟨μ, hμn, hμeq⟩ := exists_nbr_sup_eq_stab_of_vtype_false hA hv hZαα'
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab α)).to_le (Zv_le_Qv hA α))
        hc.not_le
      refine ⟨μ, hμn, ?_, hμeq.symm⟩
      rintro rfl
      obtain ⟨ν, hνn, hνμ⟩ := exists_nbr_ne hA α' hμn
      have hle : stab α' ≤ stab μ := by
        rw [← hμeq]
        exact sup_le hZαβ' inf_le_right
      obtain ⟨g, hg, hgν⟩ := stab_transitive_on_nbrs hμn hνn
      have : g • μ = μ := smul_eq_of_mem_stab (g := g) (hle hg)
      exact hνμ (hgν.symm.trans this)
    · obtain ⟨c', hc'n, hc'ne⟩ := exists_nbr_ne hA α' hβ'n
      exact ⟨c', hc'n, hc'ne, (sup_edge_eq_stab hA hv hβ'n hc'n hc'ne.symm
        (le_inf hZαα' hZαβ') hc.not_le).symm⟩
  obtain ⟨c', hc'n, hc'ne, hst⟩ := key
  exact ⟨c', hc'n, hc'ne, hst, (h28 (by omega) α' c' hc'n hc'.bAt_eq).symm⟩

theorem R₁_le_Zv_nbr (hA : F53Amalgam H M S) (hc : IsCritData α β α') (hb2 : 2 ≤ bMin H M)
    {c' : Geo H M} (hc'n : c' ∈ nbrs α') (hstab : stab α' = Zv α ⊔ (stab α' ⊓ stab c'))
    (hedge : stab α' ⊓ stab c' = Qv α' ⊔ Qv c') :
    ∀ ν ∈ nbrs α', ⁅Zv β, Zv c'⁆ ≤ Zv ν := by
  intro ν hνn
  have hR := R₁_le_inf hA hc hc'n
  set R : Subgroup G := ⁅Zv β, Zv c'⁆ with hRdef
  have hZαQβ : Zv α ≤ Qv β := Zv_le_Qv_of_mem_nbrs hc.adj hb2
  have hZα : Zv α ≤ Subgroup.centralizer (R : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β (hR hr).1).2) x (hZαQβ hx)).symm
  have hQc : Qv c' ≤ Subgroup.centralizer (R : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA c' (hR hr).2).2) x hx).symm
  have hZαst : Zv α ≤ stab α' := hstab ▸ le_sup_left
  have hQcst : Qv c' ≤ stab α' := Qv_le_stab_of_mem_nbrs hA (mem_nbrs_symm' hc'n)
  set Y : Subgroup G := Zv α ⊔ Qv c' with hY
  have hYst : Y ≤ stab α' := sup_le hZαst hQcst
  have hYc : Y ≤ Subgroup.centralizer (R : Set G) := sup_le hZα hQc
  have hYN : Y ≤ Subgroup.normalizer (Qv α' : Set G) :=
    hYst.trans (le_normalizer_pCoreOf 2 (stab α'))
  have hstab' : stab α' ≤ Y ⊔ Qv α' := by
    rw [hstab, hedge]
    exact sup_le (le_sup_of_le_left le_sup_left)
      (sup_le (le_sup_right) (le_sup_of_le_left le_sup_right))
  obtain ⟨g, hg, hgν⟩ := stab_transitive_on_nbrs hc'n hνn
  obtain ⟨y, hy, q, hq, hyq⟩ := exists_mul_of_mem_sup_of_le_normalizer hYN (g : G)
    (hstab' hg)
  have hqc' : q ∈ stab c' := Qv_le_stab_of_mem_nbrs hA hc'n hq
  have hZν : Zv ν = conjSub (g : G) (Zv c') := by rw [← hgν, Zv_smul]
  intro r hr
  rw [hZν, mem_conjSub, hyq]
  have hyr : y⁻¹ * r * y = r := by
    have := Subgroup.mem_centralizer_iff.mp (hYc hy) r hr
    calc y⁻¹ * r * y = y⁻¹ * (r * y) := mul_assoc _ _ _
      _ = r := by rw [this]; group
  have h2 : (y * q)⁻¹ * r * (y * q) = q⁻¹ * r * q := by
    calc (y * q)⁻¹ * r * (y * q) = q⁻¹ * (y⁻¹ * r * y) * q := by group
      _ = _ := by rw [hyr]
  rw [h2]
  have hrc : r ∈ Zv c' := (hR hr).2
  have := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA c' ((stab c').inv_mem hqc')) r).mp
    hrc
  simpa using this

theorem exists_c'_R₁_of_even (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h28 : Hss28At H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hb3 : 3 ≤ bMin H M) (hn : ¬ Zv β ≤ centerOf (stab β)) (heven : Even (bMin H M))
    (hRle : ⁅Zv α, Qv β⁆ ≤ Zv α') :
    ∃ β' : Geo H M, IsCritData α' β' α ∧ ∃ c' ∈ nbrs α', c' ≠ β' ∧ ¬ Zv c' ≤ Qv β ∧
      IsCritPair₁ β c' ∧ ⁅Zv β, Zv c'⁆ ≠ ⊥ ∧ ⁅Zv β, Zv c'⁆ ≤ Zv β ⊓ Zv c' ∧
      stab α' = Zv α ⊔ (stab α' ⊓ stab c') ∧ stab α' ⊓ stab c' = Qv α' ⊔ Qv c' ∧
      ∀ ν ∈ nbrs α', ⁅Zv β, Zv c'⁆ ≤ Zv ν := by
  obtain ⟨β', hc', -, -⟩ := exists_critData_symm' hA h27 hc hv hcomm hn
  obtain ⟨c', hc'n, hc'ne, hst, hed⟩ := exists_choice_c' hA h28 hc hc' (by omega)
  have hnle := not_le_Qv_beta_of_even hA h27 hc hv hcomm hb3 hn heven hc' hRle c' hc'n hc'ne
  obtain ⟨hcp, hne⟩ := isCritPair₁_beta_nbr hA h27 hc hv hn hc'n hnle
  exact ⟨β', hc', c', hc'n, hc'ne, hnle, hcp, hne, R₁_le_inf hA hc hc'n, hst, hed,
    R₁_le_Zv_nbr hA hc (by omega) hc'n hst hed⟩

end Standing

end F53.Stellmacher

end CFSG.Quasithin
