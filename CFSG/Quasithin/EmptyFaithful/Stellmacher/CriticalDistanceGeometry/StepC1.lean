module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Claim1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.CritEdgeIndex

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

variable (hA : F53Amalgam H M S) (h27 : Hss27S3At H M) {α β α' : Geo H M}
  (hc : IsCritData α β α') (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
  (hb2 : bMin H M = 2) (hn : ¬ Zv β ≤ centerOf (stab β))

set_option linter.unusedSectionVars false

omit [Finite G] in
theorem Qv_conj_mem (δ : Geo H M) {x q : G} (hx : x ∈ stab δ) (hq : q ∈ Qv δ) :
    x * q * x⁻¹ ∈ Qv δ :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab δ) hx) q).mp hq

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    ∀ w ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, w = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro x y ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        have h1 : a2⁻¹ * b1 * a2 ∈ B := by
          have := (Subgroup.mem_normalizer_iff.mp (h ((A).inv_mem ha2)) b1).mp hb1
          simpa using this
        refine ⟨a1 * a2, A.mul_mem ha1 ha2, (a2⁻¹ * b1 * a2) * b2, B.mul_mem h1 hb2, by group⟩
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        have h1 : a * b⁻¹ * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (h ha) b⁻¹).mp (B.inv_mem hb)
        exact ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, h1, by group⟩ }
  have : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact fun w hw => this hw

include hA h27 hc hv hcomm hb2 hn

theorem alpha'_mem_nbrs_beta : α' ∈ nbrs β := by
  have h1 := hc.dist_eq'
  have : dist β α' = 1 := by omega
  rw [CosetGeom.dist_comm] at this
  exact (dist_eq_one_iff_adj.mp this).symm

theorem vtype_alpha' : vtype α' = true := by
  have heven : Even (dist α α') := by rw [hc.dist_eq, hb2]; exact ⟨1, rfl⟩
  have := (vtype_eq_iff_even_dist hA.amalgam.gen α α').mpr heven
  rw [← this]; exact hv

theorem bAt_beta : bAt β = 2 := by
  have h1 := bMin_le_bAt (H := H) (M := M) β
  by_contra hne
  have hlt : bMin H M < bAt β := by omega
  exact hn (hss31At_of_hss27S3 hA h27 α β hc.adj hv hc.bAt_eq hlt)

theorem bAt_eq_two : ∀ δ : Geo H M, bAt δ = 2 := by
  intro δ
  have hβ := bAt_beta hA h27 hc hv hcomm hb2 hn
  have hα : bAt α = 2 := hc.bAt_eq.trans hb2
  have hne : vtype α ≠ vtype β := vtype_ne_of_adj hc.adj
  cases h : vtype δ
  · rw [← hβ]
    exact bAt_eq_of_vtype_eq (by cases h1 : vtype β <;> simp_all)
  · rw [← hα]
    exact bAt_eq_of_vtype_eq (by rw [h, hv])

theorem Zv_le_Qv_alpha_of_nbr {γ : Geo H M} (hγn : γ ∈ nbrs α) : Zv γ ≤ Qv α := by
  refine Zv_le_Qv_of_dist_lt ?_
  have : dist γ α = 1 := dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj γ α from hγn.symm)
  rw [this, bAt_eq_two hA h27 hc hv hcomm hb2 hn]; omega

theorem not_le_stab_alpha' {γ : Geo H M} (hγn : γ ∈ nbrs α) (hγβ : γ ≠ β) :
    ¬ Zv γ ≤ stab α' := by
  intro hγ
  obtain ⟨hα', hZα'G⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  have hZαα' : Zv α ≤ stab α' :=
    Zv_le_stab_of_dist_le hA (by rw [hc.dist_eq, hc.bAt_eq])
  have hvα' := vtype_alpha' hA h27 hc hv hcomm hb2 hn
  have hZγQ := Zv_le_Qv_alpha_of_nbr hA h27 hc hv hcomm hb2 hn hγn
  have hdec : ∀ x ∈ Zv γ, ∃ a ∈ Zv α, ∃ q ∈ Qv α', x = a * q := by
    have hK : IsPGroup 2 ↥(Zv α ⊔ Zv γ) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab α)).to_le
        (sup_le (Zv_le_Qv hA α) hZγQ)
    exact fun x hx => exists_mul_of_isPGroup_of_vtype_true hA hvα' hK (sup_le hZαα' hγ)
      le_sup_left hc.not_le x (Subgroup.mem_sup_right hx)
  refine claim1_left hA h27 hc hv hcomm (hb2 ▸ le_rfl) hn γ hγn hγβ ?_
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

theorem not_le_Qv_beta {γ : Geo H M} (hγn : γ ∈ nbrs α) (hγβ : γ ≠ β) : ¬ Zv γ ≤ Qv β :=
  fun h => not_le_stab_alpha' hA h27 hc hv hcomm hb2 hn hγn hγβ
    (h.trans (Qv_le_stab_of_mem_nbrs hA (alpha'_mem_nbrs_beta hA h27 hc hv hcomm hb2 hn)))

theorem Zv_alpha'_le_Qv_beta : Zv α' ≤ Qv β := by
  refine Zv_le_Qv_of_dist_lt ?_
  have h1 := hc.dist_eq'
  have : dist α' β = 1 := by rw [CosetGeom.dist_comm]; omega
  rw [this, bAt_eq_two hA h27 hc hv hcomm hb2 hn α']; omega

theorem not_Qv_le_of_nbr {μ : Geo H M} (hμ : μ ∈ nbrs α) : ¬ Qv μ ≤ Qv α := by
  intro h
  have hβn : β ∈ nbrs α := hc.adj
  obtain ⟨g, hg, hgμ⟩ := stab_transitive_on_nbrs hμ hβn
  have h1 : Qv β = conjSub (g : G) (Qv μ) := by rw [← hgμ, Qv_smul]
  have h2 : conjSub (g : G) (Qv α) = Qv α := by
    rw [← Qv_smul, smul_eq_of_mem_stab hg]
  have h3 : Qv β ≤ Qv α := by
    rw [h1, ← h2]; exact conjSub_mono _ h
  exact not_le_Qv_of_comm_ne hA hcomm (Zv_alpha'_le_Qv_beta hA h27 hc hv hcomm hb2 hn |>.trans h3)

theorem sup_Qv_eq_of_nbr {μ : Geo H M} (hμ : μ ∈ nbrs α) :
    Qv μ ⊔ Qv α = stab α ⊓ stab μ := by
  rcases CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.Qv_le_or_sup_eq hA
    (show α ∈ nbrs μ from (show (graph (H ⊔ M) H M).Adj α μ from hμ).symm) hv with h | h
  · exact absurd h (not_Qv_le_of_nbr hA h27 hc hv hcomm hb2 hn hμ)
  · rw [h, inf_comm]

theorem sup_Qv_eq : Qv β ⊔ Qv α = stab α ⊓ stab β :=
  sup_Qv_eq_of_nbr hA h27 hc hv hcomm hb2 hn hc.adj

theorem relIndex_N : (Qv α ⊓ Qv β).relIndex (Qv β) = 2 := by
  have hβn : β ∈ nbrs α := hc.adj
  set T := stab α ⊓ stab β with hT
  have hAT : Qv α ≤ T := Qv_le_inf hA hβn
  have hBT : Qv β ≤ T := by
    rw [hT, inf_comm]; exact Qv_le_inf hA (show α ∈ nbrs β from (show (graph (H ⊔ M) H M).Adj α β from hβn).symm)
  have hnorm : (Qv α).subgroupOf T |>.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAT]
    intro h k hh hk
    exact Qv_conj_mem α (show k ∈ stab α ⊓ stab β from hk).1 hh
  have hsup : (Qv α).subgroupOf T ⊔ (Qv β).subgroupOf T = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ Qv α ⊔ Qv β := by
      rw [sup_comm, sup_Qv_eq hA h27 hc hv hcomm hb2 hn]; exact x.2
    have hmap : ((Qv α).subgroupOf T ⊔ (Qv β).subgroupOf T).map T.subtype = Qv α ⊔ Qv β := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
      rw [inf_eq_left.mpr hAT, inf_eq_left.mpr hBT]
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have h1 := Subgroup.relIndex_sup_left ((Qv β).subgroupOf T) ((Qv α).subgroupOf T)
  rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBT] at h1
  rw [Subgroup.inf_relIndex_right, ← h1]
  exact relIndex_Qv_inf_true hA hβn hv

theorem Zv_le_inf_edge {γ : Geo H M} (hγn : γ ∈ nbrs α) :
    Zv γ ≤ stab α ⊓ stab β :=
  (Zv_le_Qv_alpha_of_nbr hA h27 hc hv hcomm hb2 hn hγn).trans (Qv_le_inf hA hc.adj)

theorem normalizes_Zv_mod_Qv_beta {γ : Geo H M} (hγn : γ ∈ nbrs α) :
    ∀ s ∈ stab α ⊓ stab β, ∀ z ∈ Zv γ, ∃ z' ∈ Zv γ, ∃ q ∈ Qv β, s * z * s⁻¹ = z' * q := by
  intro s hs z hz
  have hβn : β ∈ nbrs α := hc.adj
  have hZβ : Zv γ ≤ stab β := (Zv_le_inf_edge hA h27 hc hv hcomm hb2 hn hγn).trans inf_le_right
  have hQα : Qv α ≤ Subgroup.normalizer ((Zv γ ⊔ Qv β : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer
      ((Qv_le_stab_of_mem_nbrs hA hγn).trans (stab_le_normalizer_Zv hA γ))
      ((Qv_le_stab_of_mem_nbrs hA hβn).trans (le_normalizer_pCoreOf 2 (stab β)))
  have hQβ : Qv β ≤ Subgroup.normalizer ((Zv γ ⊔ Qv β : Subgroup G) : Set G) :=
    le_sup_right.trans Subgroup.le_normalizer
  have hTN : stab α ⊓ stab β ≤ Subgroup.normalizer ((Zv γ ⊔ Qv β : Subgroup G) : Set G) := by
    rw [← sup_Qv_eq hA h27 hc hv hcomm hb2 hn]; exact sup_le hQβ hQα
  have hw : s * z * s⁻¹ ∈ Zv γ ⊔ Qv β :=
    (Subgroup.mem_normalizer_iff.mp (hTN hs) z).mp (Subgroup.mem_sup_left hz)
  exact exists_mul_of_mem_sup_of_le_normalizer (hZβ.trans (le_normalizer_pCoreOf 2 (stab β)))
    _ hw

theorem alpha_mem_nbrs_beta : α ∈ nbrs β :=
  (show (graph (H ⊔ M) H M).Adj α β from hc.adj).symm

theorem family_trans : ∀ μ ν : ↥(nbrs β), ∃ g ∈ stab β,
    Qv (ν : Geo H M) ⊓ Qv β = (Qv (μ : Geo H M) ⊓ Qv β).map (MulAut.conj g).toMonoidHom := by
  intro μ ν
  obtain ⟨g, hg, hgμ⟩ := stab_transitive_on_nbrs μ.2 ν.2
  refine ⟨(g : G), hg, ?_⟩
  have h1 : Qv (ν : Geo H M) = conjSub (g : G) (Qv (μ : Geo H M)) := by rw [← hgμ, Qv_smul]
  have h2 : conjSub (g : G) (Qv β) = Qv β := by rw [← Qv_smul, smul_eq_of_mem_stab hg]
  show _ = conjSub (g : G) _
  rw [conjSub_inf, h2, ← h1]

theorem family_inv : ∀ g ∈ stab β, ∀ μ : ↥(nbrs β), ∃ ν : ↥(nbrs β),
    Qv (ν : Geo H M) ⊓ Qv β = (Qv (μ : Geo H M) ⊓ Qv β).map (MulAut.conj g).toMonoidHom := by
  intro g hg μ
  let g' : ↥(H ⊔ M) := ⟨g, stab_le β hg⟩
  have hg' : g' • β = β := smul_eq_of_mem_stab (g := g') hg
  have hadj : (graph (H ⊔ M) H M).Adj β (g' • (μ : Geo H M)) := by
    have := (smul_adj g').mpr μ.2
    rwa [hg'] at this
  refine ⟨⟨g' • (μ : Geo H M), hadj⟩, ?_⟩
  have h1 : Qv (g' • (μ : Geo H M)) = conjSub g (Qv (μ : Geo H M)) := Qv_smul g' _
  have h2 : conjSub g (Qv β) = Qv β := by
    have := Qv_smul g' β
    rw [hg'] at this
    exact this.symm
  show _ = conjSub g _
  show Qv (g' • (μ : Geo H M)) ⊓ Qv β = _
  rw [conjSub_inf, h2, h1]

theorem family_relIndex : ∀ μ : ↥(nbrs β), (Qv (μ : Geo H M) ⊓ Qv β).relIndex (Qv β) = 2 := by
  intro μ
  obtain ⟨g, hg, hgμ⟩ := family_trans hA h27 hc hv hcomm hb2 hn
    ⟨α, alpha_mem_nbrs_beta hA h27 hc hv hcomm hb2 hn⟩ μ
  have h2 : Qv β = (Qv β).map (MulAut.conj g).toMonoidHom := by
    have := Qv_smul (⟨g, stab_le β hg⟩ : ↥(H ⊔ M)) β
    rw [smul_eq_of_mem_stab (g := ⟨g, stab_le β hg⟩) hg] at this
    exact this
  calc (Qv (μ : Geo H M) ⊓ Qv β).relIndex (Qv β)
      = ((Qv α ⊓ Qv β).map (MulAut.conj g).toMonoidHom).relIndex
          ((Qv β).map (MulAut.conj g).toMonoidHom) := by rw [← hgμ, ← h2]
    _ = (Qv α ⊓ Qv β).relIndex (Qv β) :=
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
    _ = 2 := relIndex_N hA h27 hc hv hcomm hb2 hn

theorem Zv_beta_le_iInf_family :
    Zv β ≤ ⨅ μ : ↥(nbrs β), (Qv (μ : Geo H M) ⊓ Qv β) := by
  refine le_iInf fun μ => le_inf ?_ (Zv_le_Qv hA β)
  refine Zv_le_Qv_of_dist_lt ?_
  have : dist β (μ : Geo H M) = 1 := dist_eq_one_iff_adj.mpr μ.2
  rw [this, bAt_eq_two hA h27 hc hv hcomm hb2 hn]; omega

end F53.Stellmacher

end CFSG.Quasithin
