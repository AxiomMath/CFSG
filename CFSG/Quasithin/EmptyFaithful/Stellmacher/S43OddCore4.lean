module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCore3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseB2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Core

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem relIndex_ne_zero_of_finite (A B : Subgroup G) : A.relIndex B ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem relIndex_Zv_Qv_beta_le (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    {α' ν β l : Geo H M} (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hβ : β ∈ nbrs α)
    (hdβ : dist β ν + 2 = bMin H M) (hl : l ∈ nbrs α') : (Qv β).relIndex (Zv l) ≤ 2 := by
  have hb := hs.b1
  have hdβ' := dist_beta_crit hA hc hν hβ hdβ
  obtain ⟨γ, hγ, hdγ⟩ := exists_nbr_dist hA (x := α') (y := β) (n := bMin H M - 2)
    (by rw [CosetGeom.dist_comm]; omega)
  have hγv : vtype γ = false := Sit43.vtype_false_of_adj (vtype_beta hs hβ) hγ
  have hlv : vtype l = false := vtype_nu hA hs ho hc hl
  have hlγ : Zv l ≤ stab γ := by
    have h1 := dist_le_of_mem_nbrs hA (x := l) hγ
    have h2 := dist_triangle hA.amalgam.gen l α' β
    have h3 : dist l α' = 1 := by rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hl
    have h4 := dist_triangle hA.amalgam.gen l α' γ
    exact hs.Zv_le_stab_of_dist_le_false hA hlv (by omega)
  have hle : Zv l ≤ stab γ ⊓ stab β := le_inf hlγ (Zv_le_stab_beta hA hs ho hc hdβ' hl)
  have h2 : (Qv β).relIndex (stab γ ⊓ stab β) = 2 :=
    Sit43.relIndex_Qv_edge hA hγv (nbrs_symm hγ)
  exact h2 ▸ Subgroup.relIndex_le_of_le_right hle (by rw [h2]; omega)

end Core

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem crit4a (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {α' ν β l : Geo H M}
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M)
    (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M) (hl : l ∈ nbrs α') (hlν : l ≠ ν) :
    ¬ Zv l ≤ Qv β := by
  intro hle
  have hdβ' := Core.dist_beta_crit hA hc hν hβ hdβ
  apply Core.not_Vn_le_Qv_crit hA h26 hs ho hb hc hβ hdβ'
  obtain ⟨a₂, a₃, h29⟩ := Core.exists_sit29_nu hA h26 hs ho hc hν
  obtain ⟨z, hz, hzQ⟩ : ∃ z ∈ Zv α, z ∉ Qv α' := by
    by_contra hcon
    push Not at hcon
    exact hc.1 fun x hx => hcon x hx
  have hconj := Core.conj_swap_of_crit hA hs h29 hdν hz hzQ
  have hzβ : z ∈ stab β := by
    refine hs.Zv_le_stab_of_dist_le_false hA hs.vα ?_ hz
    rw [dist_eq_one_iff_adj.mpr hβ]
    omega
  have hQβ : conjSub z (Qv β) = Qv β :=
    conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 _ hzβ)
  have h23 : Zv a₂ ≤ Qv β ∧ Zv a₃ ≤ Qv β := by
    rcases h29.nbrs_eq l hl with h | h | h
    · exact absurd h hlν
    · subst h
      refine ⟨hle, ?_⟩
      rw [← hconj.1, ← hQβ]
      exact conjSub_mono z hle
    · subst h
      refine ⟨?_, hle⟩
      rw [← hconj.2, ← hQβ]
      exact conjSub_mono z hle
  refine iSup₂_le fun w hw => ?_
  rcases h29.nbrs_eq w hw with rfl | rfl | rfl
  · exact Core.Zv_nu_le_Qv_beta hA hs ho hc hν hdβ
  · exact h23.1
  · exact h23.2

theorem crit4b (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {α' ν β l : Geo H M}
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M)
    (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M) (hl : l ∈ nbrs α') (_hlν : l ≠ ν) :
    Zv l ⊓ Subgroup.centralizer ((Zv α ⊓ Qv α' : Subgroup G) : Set G) ≤ Qv β := by
  rintro u ⟨hul, huC⟩
  by_contra huQ
  have hb1 := hs.b1
  have hdβ' := Core.dist_beta_crit hA hc hν hβ hdβ
  have hβv := Core.vtype_beta hs hβ
  obtain ⟨γ, hγ, hdγ⟩ := Core.exists_nbr_dist hA (x := α') (y := β) (n := bMin H M - 2)
    (by rw [CosetGeom.dist_comm]; omega)
  have hlv : vtype l = false := Core.vtype_nu hA hs ho hc hl
  have huβ : u ∈ stab β := Core.Zv_le_stab_beta hA hs ho hc hdβ' hl hul
  have huγ : u ∈ stab γ := by
    have h1 := Core.dist_le_of_mem_nbrs hA (x := l) hγ
    have h4 := dist_triangle hA.amalgam.gen l α' γ
    have h3 : dist l α' = 1 := by rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hl
    exact hs.Zv_le_stab_of_dist_le_false hA hlv (by omega) hul
  have hγα : γ ≠ α := by
    intro h
    rw [h, CosetGeom.dist_comm, hc.2] at hdγ
    omega
  obtain ⟨c₂, c₃, h29⟩ := hs.exists_sit29 hA h26 hβv hγ
  have hsw := h29.smul_swap ⟨u, stab_le β huβ⟩ huγ huβ huQ
  have hmov : (⟨u, stab_le β huβ⟩ : ↥(H ⊔ M)) • α ≠ α := by
    rcases h29.nbrs_eq α (nbrs_symm hβ) with h | h | h
    · exact absurd h.symm hγα
    · rw [h, hsw.1]; exact h29.ne₂₃.symm
    · rw [h, hsw.2]; exact h29.ne₂₃
  have hUY : Zv α ⊓ Qv α' ≤ Yv β := by
    refine hs.le_Yv_of_normalizes hA h26 hβv (nbrs_symm hβ) inf_le_left huβ hmov ?_
    exact Core.conjSub_eq_of_commute fun v hv => (Subgroup.mem_centralizer_iff.mp huC v hv).symm
  have h4 := hs.four_le_relIndex hA h26 hβv (nbrs_symm hβ) inf_le_left hUY
  rw [Core.relIndex_Zv_inf_Qv_crit hA hs ho hc hν hdν] at h4
  omega

theorem crit4c (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (_hb : 3 ≤ bMin H M) {α' ν β l : Geo H M}
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M)
    (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M) (hl : l ∈ nbrs α') (hlν : l ≠ ν) :
    ¬ (Zv l ⊓ Qv β ≤ Qv α) := by
  intro hle
  have hα'v := Core.vtype_crit hA hs ho hc
  obtain ⟨a₂, a₃, h29⟩ := Core.exists_sit29_nu hA h26 hs ho hc hν
  obtain ⟨z, hz, hzQ⟩ : ∃ z ∈ Zv α, z ∉ Qv α' := by
    by_contra hcon
    push Not at hcon
    exact hc.1 fun x hx => hcon x hx
  obtain ⟨hz', hsw1, hsw2⟩ := Core.smul_swap_of_crit hA hs h29 hdν hz hzQ
  have hzst : z ∈ stab α' := Core.Zv_le_stab_crit hA hs hc hz
  have hmov : (⟨z, stab_le α' hzst⟩ : ↥(H ⊔ M)) • l ≠ l := by
    rcases h29.nbrs_eq l hl with h | h | h
    · exact absurd h hlν
    · rw [h]
      intro h'
      exact h29.ne₂₃ (hsw1.symm.trans h').symm
    · rw [h]
      intro h'
      exact h29.ne₂₃ (hsw2.symm.trans h')
  have hUY : Zv l ⊓ Qv β ≤ Yv α' := by
    refine hs.le_Yv_of_normalizes hA h26 hα'v hl inf_le_left hzst hmov ?_
    exact Core.conjSub_eq_of_commute fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hz).2 v (hle hv)).symm
  have h4 := hs.four_le_relIndex hA h26 hα'v hl inf_le_left hUY
  rw [inf_comm, Subgroup.inf_relIndex_right] at h4
  have h2 := Core.relIndex_Zv_Qv_beta_le hA hs ho hc hν hβ hdβ hl
  omega

theorem crit4d (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {α' ν β l : Geo H M}
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M)
    (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M) (hl : l ∈ nbrs α') (hlν : l ≠ ν) :
    ⁅Zv l, Zv α ⊓ Qv α'⁆ ≠ ⊥ ∧
      ⁅Zv l, Zv α ⊓ Qv α'⁆ ≤ ⁅Vn β ⊓ Qv α', Vn α'⁆ ⊓ Yv α' := by
  have hα'v := Core.vtype_crit hA hs ho hc
  refine ⟨fun h => ?_, le_inf ?_ ?_⟩
  · apply crit4a hA h26 hs ho hb hc hν hdν hβ hdβ hl hlν
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact (le_inf le_rfl h1).trans (crit4b hA h26 hs ho hb hc hν hdν hβ hdβ hl hlν)
  · rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono (inf_le_inf_right _ (Core.Zv_le_Vn (nbrs_symm hβ)))
      (Core.Zv_le_Vn hl)
  · have hYQ := Core.Yv_le_Qv hA hs ho hc hν hdν
    have hst : Zv α ⊓ Qv α' ≤ Qst α' := fun x hx =>
      ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hx.1).2 y (hYQ hy))⟩
    rw [← hs.comm_Zv_Qst hA h26 hα'v hl]
    exact Subgroup.commutator_mono le_rfl hst

theorem four_le_relIndex_comm_Vn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (_ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {δ δ' : Geo H M} (h : IsCritPair₃ δ δ') :
    4 ≤ (Yv δ').relIndex (⁅Vn δ, Vn δ'⁆ ⊔ Yv δ') := by
  obtain ⟨hδ, hδ', hd, hV⟩ := h
  obtain ⟨x, hx, hxQ⟩ : ∃ x ∈ Vn δ, x ∉ Qv δ' := by
    by_contra hcon
    push Not at hcon
    exact hV fun y hy => hcon y hy
  have hxst : x ∈ stab δ' := Core.Vn_le_stab_of_dist hA hs hδ (le_of_eq hd) hx
  have h2b := hs.claim2b hA h26 hb hδ' hxst hxQ
  have hle : ⁅Vn δ', Subgroup.zpowers x⁆ ⊔ Yv δ' ≤ ⁅Vn δ, Vn δ'⁆ ⊔ Yv δ' := by
    refine sup_le_sup_right ?_ _
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hx) le_rfl
  exact h2b.trans (Subgroup.relIndex_le_of_le_right hle (Core.relIndex_ne_zero_of_finite _ _))

theorem comm_Vn_inf_Yv_ne_bot (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {δ δ' : Geo H M} (h : IsCritPair₃ δ δ') :
    ⁅Vn δ, Vn δ'⁆ ⊓ Yv δ' ≠ ⊥ := by
  obtain ⟨l₀, hl₀, hl₀v, hc⟩ := Core.exists_crit_of_crit3 hA hs h
  have hs' := hs.of_vtype_false hl₀v
  have hβ : δ ∈ nbrs l₀ := nbrs_symm hl₀
  obtain ⟨ν, hν, hdν, hdβν⟩ := Core.exists_nu hA hs' hc hβ h.2.2.1
  obtain ⟨a₂, a₃, h29⟩ := Core.exists_sit29_nu hA h26 hs' ho hc hν
  obtain ⟨hne, hle⟩ := crit4d hA h26 hs' ho hb hc hν hdν hβ hdβν h29.n₂ h29.ne₁₂.symm
  intro hbot
  apply hne
  refine le_bot_iff.mp (hbot ▸ hle.trans (inf_le_inf_right _ ?_))
  exact Subgroup.commutator_mono inf_le_left le_rfl

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
