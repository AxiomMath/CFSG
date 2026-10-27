module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 CFSG.Quasithin.EmptyFaithful.Stellmacher

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem isPGroup_two_of_sq {K : Subgroup G} (h : ∀ x ∈ K, x ^ 2 = 1) : IsPGroup 2 K := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using h g.1 g.2

theorem relIndex_inf_eq_card_range {F V Q : Subgroup G} {P : Type*} [Group P] (θ : ↥F →* P)
    (hker : ∀ x : ↥F, θ x = 1 ↔ (x : G) ∈ Q) (hVF : V ≤ F) :
    (V ⊓ Q).relIndex V = Nat.card (θ.comp (Subgroup.inclusion hVF)).range := by
  have hk : (θ.comp (Subgroup.inclusion hVF)).ker = Q.subgroupOf V := by
    ext v
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    exact hker _
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex, ← hk, Subgroup.index_ker]

namespace Step3Ctx

variable {α β α' : Geo H M} (C : Step3Ctx H M S α β α')

include C

theorem ofCrit {μ ξ μ' : Geo H M} (hc : IsCritData μ ξ μ') (hv : vtype μ = true)
    (hcomm : ⁅Zv μ, Zv μ'⁆ ≠ ⊥) : Step3Ctx H M S μ ξ μ' where
  hA := C.hA
  h28 := C.h28
  h32 := C.h32
  h113a := C.h113a
  hc := hc
  hv := hv
  hcomm := hcomm
  heven := C.heven
  hb6 := C.hb6

theorem vtype_of_crit {μ μ' : Geo H M} (hμ : vtype μ = true) (hd : dist μ μ' = bMin H M) :
    vtype μ' = true := by
  have heven' : Even (dist μ μ') := by rw [hd]; exact C.heven
  have := (vtype_eq_iff_even_dist C.hA.amalgam.gen μ μ').mpr heven'
  rw [← this]; exact hμ

theorem crit_comm_eq_Zv_first {μ μ' ξ : Geo H M} (hμ : vtype μ = true) (hd : dist μ μ' = bMin H M)
    (hcomm : ⁅Zv μ, Zv μ'⁆ ≠ ⊥) (hξ : ξ ∈ nbrs μ) (hξd : dist ξ μ' + 1 = bMin H M) :
    ⁅Zv μ, Zv μ'⁆ = Zv ξ := by
  have hcomm' : ⁅Zv μ', Zv μ⁆ ≠ ⊥ := by rwa [Subgroup.commutator_comm]
  have hc : IsCritData μ ξ μ' :=
    ⟨hξ, C.bAt_eq_of_true hμ, hd, hξd, not_le_Qv_of_comm_ne C.hA hcomm'⟩
  exact (C.ofCrit hc hμ hcomm).comm_eq_Zv_beta

theorem crit_comm_eq_Zv_last {μ μ' ξ' : Geo H M} (hμ : vtype μ = true) (hd : dist μ μ' = bMin H M)
    (hcomm : ⁅Zv μ, Zv μ'⁆ ≠ ⊥) (hξ : ξ' ∈ nbrs μ') (hξd : dist μ ξ' + 1 = bMin H M) :
    ⁅Zv μ, Zv μ'⁆ = Zv ξ' := by
  have hμ' := C.vtype_of_crit hμ hd
  have hcomm' : ⁅Zv μ', Zv μ⁆ ≠ ⊥ := by rwa [Subgroup.commutator_comm]
  have hc : IsCritData μ' ξ' μ :=
    ⟨hξ, C.bAt_eq_of_true hμ', by rw [CosetGeom.dist_comm]; exact hd,
      by rw [CosetGeom.dist_comm]; exact hξd, not_le_Qv_of_comm_ne C.hA hcomm⟩
  rw [Subgroup.commutator_comm]
  exact (C.ofCrit hc hμ' hcomm').comm_eq_Zv_beta

theorem comm_ne_of_not_le_Qv {μ ν : Geo H M} (hμ : vtype μ = true) (hν : vtype ν = true)
    (hd : dist μ ν ≤ bMin H M) (hn : ¬ Zv μ ≤ Qv ν) : ⁅Zv μ, Zv ν⁆ ≠ ⊥ := by
  intro h
  apply hn
  have hst : Zv μ ≤ stab ν :=
    F53.Zv_le_stab_of_dist_le C.hA (by rw [C.bAt_eq_of_true hμ]; exact hd)
  rw [← centralizer_Zv_eq_Qv_of_bAt C.hA (C.bAt_eq_of_true hν)]
  exact le_inf hst (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)

theorem vtype_p_odd (P : CritPath α β α') {j : ℕ} (hj : j ≤ bMin H M) (hodd : ¬ Even j) :
    vtype (P.p j) = false := by
  have := C.vtype_path_iff P hj
  cases hv : vtype (P.p j)
  · rfl
  · exact absurd (this.mp hv) hodd

theorem vtype_p_even (P : CritPath α β α') {j : ℕ} (hj : j ≤ bMin H M) (heven : Even j) :
    vtype (P.p j) = true :=
  (C.vtype_path_iff P hj).mpr heven

theorem Zv_le_Qv_p2 (P : CritPath α β α') {l μ : Geo H M} (hl : l ∈ nbrs α') (hlγ : l ≠ P.γ)
    (hμ : μ ∈ nbrs l) : Zv μ ≤ Qv (P.p 2) := by
  have hb := C.hb6
  by_contra hnot
  have hvα' := C.vtype_alpha'
  have hvl := vtype_false_of_mem_nbrs_true hl hvα'
  have hvμ := vtype_true_of_mem_nbrs_false hμ hvl
  have hv2 : vtype (P.p 2) = true := C.vtype_p_even P (by omega) even_two
  have hv3 : vtype (P.p 3) = false := C.vtype_p_odd P (by omega) (by decide)
  have hd1 : dist α' l = 1 := dist_eq_one_iff_adj.mpr hl
  have hd2 : dist l μ = 1 := dist_eq_one_iff_adj.mpr hμ
  have he2 : dist (P.p 2) α' = bMin H M - 2 := P.dist_end (by omega)
  have he3 : dist (P.p 3) α' = bMin H M - 3 := P.dist_end (by omega)
  have hgen := C.hA.amalgam.gen
  have t1 := dist_triangle hgen μ l α'
  have t2 := dist_triangle hgen μ α' (P.p 2)
  have t3 := dist_triangle hgen μ α' (P.p 3)
  have t4 := dist_triangle hgen l α' (P.p 2)
  have t5 := dist_triangle hgen μ l (P.p 2)
  have t6 := dist_triangle hgen μ (P.p 3) (P.p 2)
  have hd1' : dist l α' = 1 := by rw [CosetGeom.dist_comm]; exact hd1
  have hd2' : dist μ l = 1 := by rw [CosetGeom.dist_comm]; exact hd2
  have hd32 : dist (P.p 3) (P.p 2) = 1 := by
    rw [CosetGeom.dist_comm, P.dist_of_le (by omega) (by omega)]
  rw [CosetGeom.dist_comm l α'] at t1
  rw [CosetGeom.dist_comm α' (P.p 2)] at t2 t4
  rw [CosetGeom.dist_comm α' (P.p 3)] at t3
  have hge : bMin H M ≤ dist μ (P.p 2) := by
    by_contra hlt
    exact hnot (Zv_le_Qv_of_dist_lt (by rw [C.bAt_eq_of_true hvμ]; omega))
  have hd : dist μ (P.p 2) = bMin H M := by omega
  have hcomm : ⁅Zv μ, Zv (P.p 2)⁆ ≠ ⊥ :=
    C.comm_ne_of_not_le_Qv hvμ hv2 (by omega) hnot
  have h1 := C.crit_comm_eq_Zv_first hvμ hd hcomm (ξ := l) (mem_nbrs_comm hμ) (by omega)
  have h2 := C.crit_comm_eq_Zv_last hvμ hd hcomm (ξ' := P.p 3)
    (P.isGeodesic.mem_nbrs_succ (i := 2) (by omega)) (by omega)
  have hZ : Zv l = Zv (P.p 3) := h1.symm.trans h2
  have hα3 : Zv α ≤ Qv (P.p 3) :=
    Zv_le_Qv_of_dist_lt_bMin (by rw [P.dist_start (by omega)]; omega)
  have hcl : Zv l ≤ Subgroup.centralizer (Zv α : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hz' := C.Zv_le_center hv3 (hZ ▸ hz)
    exact Subgroup.mem_centralizer_iff.mp hz'.2 x (pCoreOf_le 2 _ (hα3 hx))
  have hcγ : Zv P.γ ≤ Subgroup.centralizer (Zv α : Set G) := by
    rw [← C.Zv_beta_eq_Zv_γ P]
    have hβα : β ∈ nbrs α := C.hc.adj
    have h0 : ⁅Zv β, Zv α⁆ = ⊥ :=
      comm_Zv_eq_bot_of_le_Qv C.hA (K := Zv β) (x := α)
        (Zv_le_Qv_of_mem_nbrs (mem_nbrs_comm hβα) C.hb2)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
  apply C.hcomm
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [← (C.Zv_sup_eq_and_inf_eq_bot hvα' (mem_nbrs_comm (P.γ_adj (by omega))) hl (Ne.symm hlγ)).1]
  exact sup_le hcγ hcl

theorem Vn_le_Qv_p2 (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α') (hlγ : l ≠ P.γ) :
    Vn l ≤ Qv (P.p 2) :=
  iSup₂_le fun _ hμ => C.Zv_le_Qv_p2 P hl hlγ hμ

theorem Vn_le_stab_beta (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α') (hlγ : l ≠ P.γ) :
    Vn l ≤ stab β := by
  have h1 : P.p 1 ∈ nbrs (P.p 2) := P.isGeodesic.mem_nbrs_pred (i := 1) (by have := C.hb6; omega)
  rw [P.p_one] at h1
  exact (C.Vn_le_Qv_p2 P hl hlγ).trans (Qv_le_stab_of_mem_nbrs C.hA h1)

theorem Wv_inf_stab_decomp :
    ∀ x ∈ Wv α ⊓ stab α', ∃ a ∈ Zv α, ∃ q ∈ Qv α', x = a * q := by
  obtain ⟨-, hZαα'⟩ := Zv_le_stab_pair C.hA C.hc C.hcomm
  have hK : IsPGroup 2 ↥(Wv α ⊓ stab α') :=
    isPGroup_two_of_sq fun x hx => (C.isElemAbelian_Wv α).2 x hx.1
  exact exists_mul_of_isPGroup_of_vtype_true C.hA C.vtype_alpha' hK inf_le_right
    (le_inf (C.Zv_le_Wv_of_true C.hv) hZαα') C.hc.not_le

theorem comm_Wv_inf_stab_le : ⁅Wv α ⊓ stab α', Zv α'⁆ ≤ Zv α :=
  commutator_le_of_decomp C.hA (Zv_le_stab_of_comm_ne C.hA C.hc C.hcomm).2
    C.Wv_inf_stab_decomp

theorem γ_ne_ε (P : CritPath α β α') : P.γ ≠ P.ε := by
  have hb := C.hb6
  intro h
  have h1 := P.dist_start_γ (by omega)
  have h2 := P.dist_start_ε (by omega)
  rw [h] at h1
  omega

theorem Zv_ne_Zv_ε_of_mem_nbrs_ne (P : CritPath α β α') {l₁ : Geo H M} (hl₁ : l₁ ∈ nbrs α)
    (hne : l₁ ≠ β) (hZ : Zv l₁ = Zv P.ε) : False := by
  have hb := C.hb6
  have h1 := (C.Zv_sup_eq_and_inf_eq_bot C.hv C.hc.adj hl₁ (Ne.symm hne)).1
  have h2 := (C.Zv_sup_eq_and_inf_eq_bot (C.vtype_δ P) (P.δ_adj (by omega))
    (mem_nbrs_comm (P.ε_adj (by omega))) (C.γ_ne_ε P)).1
  rw [C.Zv_beta_eq_Zv_γ P, hZ, h2] at h1
  apply C.hc.not_le
  rw [← h1]
  exact Zv_le_Qv_of_dist_lt_bMin (by rw [P.dist_end (by omega)]; omega)

theorem comm_Zv_Zv_ε (P : CritPath α β α') {l μ : Geo H M} (hl : vtype l = true)
    (hdl : dist α l = 2) (hμ : μ ∈ nbrs P.ε) : ⁅Zv l, Zv μ⁆ = ⊥ := by
  have hb := C.hb6
  by_contra hne
  have hvμ : vtype μ = true := vtype_true_of_mem_nbrs_false hμ (C.vtype_ε P)
  have hgen := C.hA.amalgam.gen
  have hdε : dist α P.ε = bMin H M - 3 := P.dist_start_ε (by omega)
  have hdμ : dist P.ε μ = 1 := dist_eq_one_iff_adj.mpr hμ
  have hdl' : dist l α = 2 := by rw [CosetGeom.dist_comm]; exact hdl
  have t1 := dist_triangle hgen l α P.ε
  have t2 := dist_triangle hgen l P.ε μ
  have hle : dist l μ ≤ bMin H M := by omega
  have hn : ¬ Zv l ≤ Qv μ := fun h => hne (comm_Zv_eq_bot_of_le_Qv C.hA h)
  have hge : bMin H M ≤ dist l μ := by
    by_contra hlt
    exact hn (Zv_le_Qv_of_dist_lt (by rw [C.bAt_eq_of_true hl]; omega))
  have hd : dist l μ = bMin H M := by omega
  obtain ⟨l₁, hll₁, hdl₁⟩ := exists_adj_dist_eq hgen (α := α) (δ := l) (d := 1) (by omega)
  have hl₁ : l₁ ∈ nbrs l := hll₁
  have hd1 : dist l l₁ = 1 := dist_eq_one_iff_adj.mpr hl₁
  have t3 := dist_triangle hgen l₁ α P.ε
  have t4 := dist_triangle hgen l₁ P.ε μ
  have t5 := dist_triangle hgen l l₁ μ
  have t6 := dist_triangle hgen l P.ε μ
  rw [CosetGeom.dist_comm l₁ α] at t3
  have hcomm : ⁅Zv l, Zv μ⁆ ≠ ⊥ := hne
  have hdl₁ε : dist l P.ε + 1 = bMin H M := by omega
  have h1 := C.crit_comm_eq_Zv_first hl hd hcomm (ξ := l₁) hl₁ (by omega)
  have h2 := C.crit_comm_eq_Zv_last hl hd hcomm (ξ' := P.ε) (mem_nbrs_comm hμ) hdl₁ε
  have hZ : Zv l₁ = Zv P.ε := h1.symm.trans h2
  have hl₁α : l₁ ∈ nbrs α := dist_eq_one_iff_adj.mp hdl₁
  refine C.Zv_ne_Zv_ε_of_mem_nbrs_ne P hl₁α ?_ hZ
  rintro rfl
  have hdβε : dist (P.p 1) P.ε = bMin H M - 3 - 1 := P.dist_of_le (by omega) (by omega)
  rw [P.p_one] at hdβε
  omega

theorem comm_Wv_Vn_ε (P : CritPath α β α') : ⁅Wv α, Vn P.ε⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, C.Wv_eq_iSup_Vn C.hv]
  refine iSup_le fun l => ?_
  rw [C.Vn_eq_Zv l.2.1]
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun μ hμ => ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact C.comm_Zv_Zv_ε P l.2.1 l.2.2 hμ

theorem Zv_γ_le_inter (P : CritPath α β α') : Zv P.γ ≤ Vn P.γ ⊓ Vn P.ε := by
  have hb := C.hb6
  refine le_inf (Zv_le_Vn_self C.hA _) ?_
  exact (C.Zv_le_Zv_of_mem_nbrs (C.vtype_δ P) (P.δ_adj (by omega))).trans
    (Zv_le_Vn_of_mem_nbrs (P.ε_adj (by omega)))

theorem inter_Vn_normal (P : CritPath α β α') :
    stab P.γ ⊓ stab P.δ ≤ Subgroup.normalizer ((Vn P.γ ⊓ Vn P.ε : Subgroup G) : Set G) := by
  have hb := C.hb6
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hε : P.ε ∈ nbrs P.δ := mem_nbrs_comm (P.ε_adj (by omega))
  have hedge := C.Qv_sup_Qv_eq_edge (C.vtype_δ P) hγ
  rw [inf_comm, ← hedge]
  refine sup_le ?_ ?_
  · refine le_normalizer_of_conj_mem fun x hx w hw => ?_
    have hxγ : x ∈ stab P.γ := Qv_le_stab_of_mem_nbrs C.hA hγ hx
    have hxε : x ∈ stab P.ε := Qv_le_stab_of_mem_nbrs C.hA hε hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn P.γ hxγ) w).mp hw.1,
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn P.ε hxε) w).mp hw.2⟩
  · refine le_normalizer_of_conj_mem fun x hx w hw => ?_
    have hxγ : x ∈ stab P.γ := pCoreOf_le 2 _ hx
    have hcomm : x * w * x⁻¹ * w⁻¹ ∈ Zv P.γ := by
      rw [← C.comm_Vn_Qv_eq (C.vtype_γ P), Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx hw.1
    have hZ := C.Zv_γ_le_inter P hcomm
    have : x * w * x⁻¹ = (x * w * x⁻¹ * w⁻¹) * w := by group
    rw [this]
    exact Subgroup.mul_mem _ hZ hw

theorem Vn_beta_le_stab : Vn β ≤ stab α' := by
  refine iSup₂_le fun μ hμ => ?_
  have hvμ := vtype_true_of_mem_nbrs_false hμ C.vtype_beta
  have h1 : dist β μ = 1 := dist_eq_one_iff_adj.mpr hμ
  have h2 := dist_triangle C.hA.amalgam.gen μ β α'
  have h3 := C.hc.dist_eq'
  rw [CosetGeom.dist_comm μ β] at h2
  exact F53.Zv_le_stab_of_dist_le C.hA (by rw [C.bAt_eq_of_true hvμ]; omega)

theorem index_Vn_beta_Qv : (Vn β ⊓ Qv α').relIndex (Vn β) = 2 := by
  obtain ⟨ψ, -, hker⟩ := exists_quotHom_true C.hA C.vtype_alpha'
  have hV := C.Vn_beta_le_stab
  have hle : (Vn β ⊓ Qv α').relIndex (Vn β) ≤ 2 := by
    rw [relIndex_inf_eq_card_range ψ hker hV]
    refine perm3_card_le_two_of_isPGroup _ (isPGroup_two_of_sq ?_)
    rintro _ ⟨v, rfl⟩
    rw [← map_pow]
    have : v ^ 2 = 1 := Subtype.ext (by
      have := (C.isElemAbelian_Vn' β).2 _ v.2
      simpa using this)
    rw [this, map_one]
  have hne1 : (Vn β ⊓ Qv α').relIndex (Vn β) ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact C.hc.not_le ((Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm (show β ∈ nbrs α from C.hc.adj))).trans
      (h.trans inf_le_right))
  have hne0 := relIndex_ne_zero' (Vn β ⊓ Qv α') (Vn β)
  omega

theorem Vn_inf_stab_le_Vn_beta {c : Geo H M} (hc : c ∈ nbrs α) (hcβ : c ≠ β) :
    Vn c ⊓ stab α' ≤ Vn β := by
  have hb := C.hb6
  have hβn : β ∈ nbrs α := C.hc.adj
  have hvc : vtype c = false := vtype_false_of_mem_nbrs_true hc C.hv
  obtain ⟨-, hZα'G⟩ := Zv_le_stab_of_comm_ne C.hA C.hc C.hcomm
  obtain ⟨-, hZαα'⟩ := Zv_le_stab_pair C.hA C.hc C.hcomm
  have hZα'β : Zv α' ≤ stab β :=
    Zv_le_stab_of_dist_le_bMin C.hA (by have := C.hc.dist_eq'; rw [CosetGeom.dist_comm]; omega)
  have hnle := not_le_Qv_of_comm_ne C.hA C.hcomm
  have hcα : Zv α ≤ Vn c := Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hc)
  have hHW : Vn c ⊓ stab α' ≤ Wv α ⊓ stab α' :=
    inf_le_inf_right _ (C.Vn_le_Wv_of_mem_nbrs C.hv hc)
  have hcommH : ∀ x ∈ Vn c ⊓ stab α', ∀ z ∈ Zv α', x * z * x⁻¹ * z⁻¹ ∈ Zv α := fun x hx z hz => by
    have := C.comm_Wv_inf_stab_le (Subgroup.commutator_mem_commutator (hHW hx) hz)
    rwa [commutatorElement_def] at this
  have hN : Qv c ⊔ Zv α' ≤ Subgroup.normalizer ((Vn c ⊓ stab α' : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · refine le_normalizer_of_conj_mem fun q hq w hw => ?_
      have hqc : q ∈ stab c := pCoreOf_le 2 _ hq
      have hcomm : q * w * q⁻¹ * w⁻¹ ∈ Zv c := by
        rw [← C.comm_Vn_Qv_eq hvc, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hq hw.1
      have hcα' : q * w * q⁻¹ * w⁻¹ ∈ stab α' :=
        hZαα' (C.Zv_le_Zv_of_mem_nbrs C.hv hc hcomm)
      have : q * w * q⁻¹ = (q * w * q⁻¹ * w⁻¹) * w := by group
      rw [this]
      exact ⟨Subgroup.mul_mem _ (Zv_le_Vn_self C.hA c hcomm) hw.1,
        Subgroup.mul_mem _ hcα' hw.2⟩
    · refine le_normalizer_of_conj_mem fun z hz w hw => ?_
      have hc2 : w * z * w⁻¹ * z⁻¹ ∈ Zv α := hcommH w hw z hz
      have hinv := (Zv α).inv_mem hc2
      have : z * w * z⁻¹ = (w * z * w⁻¹ * z⁻¹)⁻¹ * w := by group
      rw [this]
      exact ⟨Subgroup.mul_mem _ (hcα hinv) hw.1, Subgroup.mul_mem _ (hZαα' hinv) hw.2⟩
  have hst : Zv α' ⊔ (stab α ⊓ stab c) = stab α :=
    sup_edge_eq_stab C.hA C.hv hβn hc (Ne.symm hcβ) (le_inf hZα'G hZα'β) hnle
  have h28' : Qv α ⊔ Qv c = stab α ⊓ stab c := C.Qv_sup_Qv_eq_edge C.hv hc
  have hXQ : stab α ≤ (Qv c ⊔ Zv α') ⊔ Qv α := by
    rw [← hst, ← h28']
    exact sup_le (le_sup_of_le_left le_sup_right)
      (sup_le le_sup_right (le_sup_of_le_left le_sup_left))
  have hQcst : Qv c ≤ stab α := Qv_le_stab_of_mem_nbrs C.hA (mem_nbrs_comm hc)
  have hXN : Qv c ⊔ Zv α' ≤ Subgroup.normalizer (Qv α : Set G) :=
    (sup_le hQcst hZα'G).trans (le_normalizer_pCoreOf 2 (stab α))
  obtain ⟨g, hg, hgc⟩ := stab_transitive_on_nbrs hc hβn
  obtain ⟨x, hx, q, hq, hxq⟩ := exists_mul_of_mem_sup_of_le_normalizer hXN (g : G) (hXQ hg)
  have hqst : q ∈ stab c := Qv_le_stab_of_mem_nbrs C.hA hc hq
  have hVβ : Vn β = conjSub x (Vn c) := by
    rw [← hgc, Vn_smul, hxq, conjSub_mul, conjSub_eq_of_mem_normalizer (stab_le_normalizer_Vn c hqst)]
  calc Vn c ⊓ stab α' = conjSub x (Vn c ⊓ stab α') := (conjSub_eq_of_mem_normalizer (hN hx)).symm
    _ ≤ conjSub x (Vn c) := conjSub_mono x inf_le_left
    _ = Vn β := hVβ.symm

theorem Vn_index_le {c : Geo H M} (hc : c ∈ nbrs α) (hcβ : c ≠ β) :
    (Vn c ⊓ Vn β).relIndex (Vn c) ≤ (Wv α ⊓ stab α').relIndex (Wv α) := by
  calc (Vn c ⊓ Vn β).relIndex (Vn c)
      ≤ (Vn c ⊓ stab α').relIndex (Vn c) :=
        Subgroup.relIndex_le_of_le_left (le_inf inf_le_left (C.Vn_inf_stab_le_Vn_beta hc hcβ))
          (relIndex_ne_zero' _ _)
    _ = (stab α').relIndex (Vn c) := by rw [Subgroup.inf_relIndex_left]
    _ ≤ (stab α').relIndex (Wv α) :=
        Subgroup.relIndex_le_of_le_right (C.Vn_le_Wv_of_mem_nbrs C.hv hc) (relIndex_ne_zero' _ _)
    _ = (Wv α ⊓ stab α').relIndex (Wv α) := by rw [Subgroup.inf_relIndex_left]

theorem Vn_index_le_γ_ε (P : CritPath α β α') :
    (Vn P.γ ⊓ Vn P.ε).relIndex (Vn P.γ) ≤ (Wv α ⊓ stab α').relIndex (Wv α) := by
  have hb := C.hb6
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hε : P.ε ∈ nbrs P.δ := mem_nbrs_comm (P.ε_adj (by omega))
  have hβn : β ∈ nbrs α := C.hc.adj
  obtain ⟨g0, hg0⟩ := exists_smul_of_vtype_eq (δ := α) (δ' := P.δ) (by rw [C.vtype_δ P, C.hv])
  have hg0β : g0 • β ∈ nbrs P.δ := by
    have := (smul_mem_nbrs_iff g0 (l := α) (δ := β)).mpr hβn
    rwa [← hg0] at this
  obtain ⟨h, hh, hhβ⟩ := stab_transitive_on_nbrs hg0β hε
  have hgα : (h * g0) • α = P.δ := by
    rw [mul_smul, ← hg0]; exact smul_eq_of_mem_stab hh
  have hgβ : (h * g0) • β = P.ε := by rw [mul_smul]; exact hhβ
  set g : ↥(H ⊔ M) := h * g0 with hgdef
  have hc : g⁻¹ • P.γ ∈ nbrs α := by
    have h1 : g • (g⁻¹ • P.γ) ∈ nbrs (g • α) := by rw [smul_inv_smul, hgα]; exact hγ
    exact (smul_mem_nbrs_iff g).mp h1
  have hcβ : g⁻¹ • P.γ ≠ β := by
    intro h2
    apply C.γ_ne_ε P
    calc P.γ = g • (g⁻¹ • P.γ) := (smul_inv_smul g _).symm
      _ = g • β := by rw [h2]
      _ = P.ε := hgβ
  have key := C.Vn_index_le hc hcβ
  refine le_trans (le_of_eq ?_) key
  have e1 : Vn P.γ = conjSub (g : G) (Vn (g⁻¹ • P.γ)) := by rw [← Vn_smul, smul_inv_smul]
  have e2 : Vn P.ε = conjSub (g : G) (Vn β) := by rw [← Vn_smul, hgβ]
  rw [e1, e2, ← conjSub_inf]
  exact Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj (g : G)).toMonoidHom) _ _
    (MulAut.conj (g : G)).injective

theorem Zv_α'_le_Vn_γ (P : CritPath α β α') : Zv α' ≤ Vn P.γ :=
  Zv_le_Vn_of_mem_nbrs (P.γ_adj (by have := C.hb6; omega))

theorem not_Zv_α'_le_Vn_ε (P : CritPath α β α') : ¬ Zv α' ≤ Vn P.ε := by
  intro h
  apply C.hcomm
  rw [← le_bot_iff, ← C.comm_Wv_Vn_ε P]
  exact Subgroup.commutator_mono (C.Zv_le_Wv_of_true C.hv) h

theorem two_le_relIndex_Vn_γ_ε (P : CritPath α β α') :
    2 ≤ (Vn P.γ ⊓ Vn P.ε).relIndex (Vn P.γ) := by
  have h1 : (Vn P.γ ⊓ Vn P.ε).relIndex (Vn P.γ) ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact C.not_Zv_α'_le_Vn_ε P ((C.Zv_α'_le_Vn_γ P).trans (h.trans inf_le_right))
  have h0 := relIndex_ne_zero' (Vn P.γ ⊓ Vn P.ε) (Vn P.γ)
  omega

theorem two_le_index_Wv (P : CritPath α β α') : 2 ≤ (Wv α ⊓ stab α').relIndex (Wv α) :=
  (C.two_le_relIndex_Vn_γ_ε P).trans (C.Vn_index_le_γ_ε P)

theorem exists_smul_γ_δ (P : CritPath α β α') :
    ∃ g : ↥(H ⊔ M), g • P.γ = P.γ ∧ g • P.δ = α' := by
  have hb := C.hb6
  obtain ⟨g, hg, hgδ⟩ := stab_transitive_on_nbrs
    (mem_nbrs_comm (P.δ_adj (by omega)) : P.δ ∈ nbrs P.γ) (P.γ_adj (by omega) : α' ∈ nbrs P.γ)
  exact ⟨g, smul_eq_of_mem_stab hg, hgδ⟩

theorem conj_Wv_le (P : CritPath α β α') {g : ↥(H ⊔ M)} (hgγ : g • P.γ = P.γ)
    (hgδ : g • P.δ = α') : conjSub (g : G) (Wv α) ≤ stab α' ⊓ stab P.γ := by
  refine le_inf ?_ ?_
  · rw [← hgδ, stab_smul]
    exact conjSub_mono _ (C.Wv_le_stab_δ P)
  · conv_rhs => rw [← hgγ, stab_smul]
    exact conjSub_mono _ (C.Wv_le_stab_γ P)

theorem comm_conj_Wv_Vn (P : CritPath α β α') (g : ↥(H ⊔ M)) :
    ⁅conjSub (g : G) (Wv α), Vn (g • P.ε)⁆ = ⊥ := by
  rw [Vn_smul, conjSub_commutator, C.comm_Wv_Vn_ε P]
  exact conjSub_bot _

end Step3Ctx
end F53.Stellmacher
end CFSG.Quasithin
