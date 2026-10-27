module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.CardZvTwoSec
public import CFSG.Quasithin.EmptyFaithful.SzF53MConj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits

namespace F53.Stellmacher.S43

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem nbrs_symm {δ l : Geo H M} (h : l ∈ nbrs δ) : δ ∈ nbrs l :=
  SimpleGraph.Adj.symm (show (graph (H ⊔ M) H M).Adj δ l from h)

theorem exists_adj_of_vtype_false (hA : F53Amalgam H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    ∃ β : Geo H M, (graph (H ⊔ M) H M).Adj δ β := by
  have h15 := card_nbrs_false hA hδ
  by_contra hcon
  push Not at hcon
  have : nbrs δ = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => hcon x hx
  rw [this] at h15
  simp at h15

theorem exists_adj_of_vtype_true (hA : F53Amalgam H M S) {δ : Geo H M} (hδ : vtype δ = true) :
    ∃ β : Geo H M, (graph (H ⊔ M) H M).Adj δ β := by
  have h3 := card_nbrs_true hA hδ
  by_contra hcon
  push Not at hcon
  have : nbrs δ = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => hcon x hx
  rw [this] at h3
  simp at h3

namespace Sit43

variable {α : Geo H M}

omit [Finite G] in
theorem smul (hs : Sit43 α) (g : ↥(H ⊔ M)) : Sit43 (g • α) := by
  refine ⟨?_, ?_, fun β hβ => ?_, ?_, hs.b1⟩
  · rw [vtype_smul]; exact hs.vα
  · rw [bAt_smul]; exact hs.bα
  · have h : (graph (H ⊔ M) H M).Adj α (g⁻¹ • β) :=
      (smul_adj g).mp (by rw [smul_inv_smul]; exact hβ)
    have := hs.lt _ h
    rwa [bAt_smul] at this
  · rw [stab_smul, Zv_smul]
    have := IsOrthSec.conj hs.orth (g : G)
    rwa [conjSub_bot] at this

omit [Finite G] in
theorem of_vtype_false (hs : Sit43 α) {δ : Geo H M} (hδ : vtype δ = false) : Sit43 δ := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (hs.vα.trans hδ.symm)
  exact hs.smul g

omit [Finite G] in
theorem vtype_true_of_adj {δ β : Geo H M} (hδ : vtype δ = false)
    (h : (graph (H ⊔ M) H M).Adj δ β) : vtype β = true := by
  have hne := vtype_ne_of_adj h
  rw [hδ] at hne
  cases hv : vtype β
  · exact absurd hv.symm hne
  · rfl

omit [Finite G] in
theorem vtype_false_of_adj {δ β : Geo H M} (hδ : vtype δ = true)
    (h : (graph (H ⊔ M) H M).Adj δ β) : vtype β = false := by
  have hne := vtype_ne_of_adj h
  rw [hδ] at hne
  cases hv : vtype β
  · rfl
  · exact absurd hv.symm hne

theorem exists_adj (hA : F53Amalgam H M S) (hs : Sit43 α) :
    ∃ β : Geo H M, (graph (H ⊔ M) H M).Adj α β :=
  exists_adj_of_vtype_false hA hs.vα

theorem bMin_lt_bAt_of_true (hA : F53Amalgam H M S) (hs : Sit43 α) {μ : Geo H M}
    (hμ : vtype μ = true) : bMin H M < bAt μ := by
  obtain ⟨β, hβ⟩ := hs.exists_adj hA
  have hβv : vtype β = true := vtype_true_of_adj hs.vα hβ
  rw [← bAt_eq_of_vtype_eq (hβv.trans hμ.symm)]
  exact hs.lt β hβ

theorem lt_of_adj (hA : F53Amalgam H M S) (hs : Sit43 α) {δ μ : Geo H M} (hδ : vtype δ = false)
    (h : (graph (H ⊔ M) H M).Adj δ μ) : bMin H M < bAt μ :=
  bMin_lt_bAt_of_true hA hs (vtype_true_of_adj hδ h)

omit [Finite G] in
theorem bAt_of_vtype_false (hs : Sit43 α) {δ : Geo H M} (hδ : vtype δ = false) :
    bAt δ = bMin H M :=
  (hs.of_vtype_false hδ).bα

theorem centralizer_Zv (hA : F53Amalgam H M S) (hs : Sit43 α) {δ : Geo H M}
    (hδ : vtype δ = false) :
    stab δ ⊓ Subgroup.centralizer (Zv δ : Set G) = Qv δ :=
  centralizer_Zv_eq_Qv_of_bAt hA (hs.bAt_of_vtype_false hδ)

omit [Finite G] in
theorem card_Zv_false (hs : Sit43 α) {δ : Geo H M} (hδ : vtype δ = false) :
    Nat.card (Zv δ) = 16 := by
  rw [IsModelSec.card_bot (hs.of_vtype_false hδ).orth]
  exact card_orth

theorem Zv_le_centerOf (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {μ : Geo H M}
    (hμ : vtype μ = true) : Zv μ ≤ centerOf (stab μ) := by
  obtain ⟨l, hl⟩ := exists_adj_of_vtype_true hA hμ
  have hlv : vtype l = false := vtype_false_of_adj hμ hl
  have hs' := hs.of_vtype_false hlv
  exact hss41At_of_hss26A hA h26 l μ hl.symm hlv hs'.bα (hs.lt_of_adj hA hlv hl.symm)

theorem centerOf_eq_bot (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ β : Geo H M} (hδ : vtype δ = false) (hβ : (graph (H ⊔ M) H M).Adj δ β) :
    centerOf (stab δ) = ⊥ :=
  centerOf_eq_bot_of_Zv_central hA hβ.symm
    (hs.Zv_le_centerOf hA h26 (vtype_true_of_adj hδ hβ))

theorem Zv_eq_inf (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {μ l : Geo H M}
    (hμ : vtype μ = true) (hl : l ∈ nbrs μ) :
    Zv μ = quasithinOmegaOneCenter (stab μ ⊓ stab l) ∧ Zv μ ≤ Zv l :=
  Zv_eq_omegaOneCenter_inf hA hl (hs.Zv_le_centerOf hA h26 hμ)

theorem Zv_le_Zv_nbr (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {μ l : Geo H M}
    (hμ : vtype μ = true) (hl : l ∈ nbrs μ) : Zv μ ≤ Zv l :=
  (hs.Zv_eq_inf hA h26 hμ hl).2

theorem Zv_inf_centralizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {μ l : Geo H M} (hμ : vtype μ = true) (hl : l ∈ nbrs μ) :
    Zv l ⊓ Subgroup.centralizer ((stab l ⊓ stab μ : Subgroup G) : Set G) = Zv μ :=
  EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_inf_centralizer_edge_eq hA
    (show (graph (H ⊔ M) H M).Adj l μ from hl.symm) (hs.Zv_le_centerOf hA h26 hμ)

theorem card_Zv_true (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {μ : Geo H M}
    (hμ : vtype μ = true) : Nat.card (Zv μ) = 2 := by
  obtain ⟨l, hl⟩ := exists_adj_of_vtype_true hA hμ
  have hlv : vtype l = false := vtype_false_of_adj hμ hl
  exact EmptyFaithful.Stellmacher.OrdinaryProofs.card_Zv_eq_two_of_sec hA hlv hl.symm
    (hs.Zv_le_centerOf hA h26 hμ) (Or.inl (hs.of_vtype_false hlv).orth)

theorem Vn_eq_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {δ : Geo H M}
    (hδ : vtype δ = false) : Vn δ = Zv δ := by
  obtain ⟨μ, hμ⟩ := exists_adj_of_vtype_false hA hδ
  have hT := sylow_stab_inf_left hA (show μ ∈ nbrs δ from hμ)
  have hμv : vtype μ = true := vtype_true_of_adj hδ hμ
  apply le_antisymm
  · exact iSup₂_le fun l hl => hs.Zv_le_Zv_nbr hA h26 (vtype_true_of_adj hδ hl) (nbrs_symm hl)
  · rw [Zv_eq_conjClosure hT]
    refine conjClosure_le fun h hh z hz => ?_
    have hz' : z ∈ Vn δ := by
      have h1 := (hs.Zv_eq_inf hA h26 hμv (show δ ∈ nbrs μ from hμ.symm)).1
      rw [inf_comm] at h1
      have h2 : z ∈ Zv μ := h1 ▸ hz
      exact le_iSup₂_of_le (f := fun (m : Geo H M) (_ : m ∈ nbrs δ) => Zv m) μ hμ le_rfl h2
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hh) z).mp hz'

omit [Finite G] in
theorem Zv_le_Qv_of_dist_lt_false (hs : Sit43 α) {δ ν : Geo H M} (hδ : vtype δ = false)
    (h : dist δ ν < bMin H M) : Zv δ ≤ Qv ν :=
  Zv_le_Qv_of_dist_lt (by rw [hs.bAt_of_vtype_false hδ]; exact h)

theorem Zv_le_stab_of_dist_le_false (hA : F53Amalgam H M S) (hs : Sit43 α) {δ ν : Geo H M}
    (hδ : vtype δ = false) (h : dist δ ν ≤ bMin H M) : Zv δ ≤ stab ν :=
  Zv_le_stab_of_dist_le hA (by rw [hs.bAt_of_vtype_false hδ]; exact h)

theorem exists_crit_partner (hA : F53Amalgam H M S) (hs : Sit43 α) :
    ∃ α' : Geo H M, IsCritPair₁ α α' := by
  obtain ⟨μ, hd, hn⟩ := bAt_spec hA α
  exact ⟨μ, hn, by rw [hd, hs.bα]⟩

theorem vtype_crit (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') : vtype α' = false := by
  have h := (vtype_eq_iff_even_dist hA.amalgam.gen α α').mpr (by rw [hc.2]; exact he)
  rw [hs.vα] at h
  exact h.symm

theorem Zv_le_stab_crit (hA : F53Amalgam H M S) (hs : Sit43 α) {α' : Geo H M}
    (hc : IsCritPair₁ α α') : Zv α ≤ stab α' :=
  hs.Zv_le_stab_of_dist_le_false hA hs.vα (le_of_eq hc.2)

theorem comm_ne_bot_crit (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') : ⁅Zv α, Zv α'⁆ ≠ ⊥ := by
  intro h
  have h1 : Zv α ≤ Subgroup.centralizer (Zv α' : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have h2 := hs.centralizer_Zv hA (hs.vtype_crit hA he hc)
  exact hc.1 (h2 ▸ le_inf (hs.Zv_le_stab_crit hA hc) h1)

theorem not_Zv_le_Qv_crit (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') : ¬ Zv α' ≤ Qv α := by
  intro h
  apply hs.comm_ne_bot_crit hA he hc
  rw [Subgroup.commutator_comm]
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hy).2 x (h hx)).symm

theorem isCritPair₁_symm (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') : IsCritPair₁ α' α :=
  ⟨hs.not_Zv_le_Qv_crit hA he hc, by rw [CosetGeom.dist_comm]; exact hc.2⟩

theorem sit_crit (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M)) {α' : Geo H M}
    (hc : IsCritPair₁ α α') : Sit43 α' :=
  hs.of_vtype_false (hs.vtype_crit hA he hc)

theorem Zv_le_stab_crit' (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') : Zv α' ≤ stab α :=
  (hs.sit_crit hA he hc).Zv_le_stab_crit hA (hs.isCritPair₁_symm hA he hc)

omit [Finite G] in
theorem relIndex_sup_of_le_normalizer {A N : Subgroup G}
    (h : A ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (A ⊔ N) = N.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A N h).toEquiv.symm

theorem sup_Qv_edge (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {δ l : Geo H M}
    (hδ : vtype δ = false) (hl : l ∈ nbrs δ) : Qv δ ⊔ Qv l = stab δ ⊓ stab l :=
  hss28At_of_hss26A hA h26 hs.b1 δ l hl (hs.bAt_of_vtype_false hδ)

theorem relIndex_Qv_edge (hA : F53Amalgam H M S) {δ l : Geo H M}
    (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    (Qv l).relIndex (stab δ ⊓ stab l) = 2 := by
  have h := relIndex_Qv_inf_true hA (show δ ∈ nbrs l from nbrs_symm hl) (vtype_true_of_adj hδ hl)
  rwa [inf_comm] at h

theorem relIndex_Qv_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    (Qv l).relIndex (Qv δ) = 2 := by
  have h1 := relIndex_sup_of_le_normalizer (A := Qv δ) (N := Qv l)
    ((Qv_le_stab_of_mem_nbrs hA hl).trans (le_normalizer_pCoreOf 2 (stab l)))
  rw [hs.sup_Qv_edge hA h26 hδ hl] at h1
  rw [← h1]
  exact relIndex_Qv_edge hA hδ hl

theorem not_Qv_le_Qv_nbr (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) : ¬ Qv δ ≤ Qv l := by
  intro h
  have h1 := relIndex_Qv_edge hA hδ hl
  rw [← hs.sup_Qv_edge hA h26 hδ hl, sup_eq_right.mpr h, Subgroup.relIndex_self] at h1
  omega

end Sit43

end F53.Stellmacher.S43

end CFSG.Quasithin
