module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Base
public import CFSG.Quasithin.EmptyFaithful.SzF53B3Conj
public import CFSG.Quasithin.EmptyFaithful.SzF53B3NSec

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure Ctx (H M S : Subgroup G) (α β α' : Geo H M) : Prop where
  hA : F53Amalgam H M S
  h28 : Hss28At H M
  h32 : Hss32At H M
  hc : IsCritData α β α'
  hv : vtype α = true
  hcomm : ⁅Zv α, Zv α'⁆ = ⊥
  hZα : Nat.card (Zv α) = 4
  hZβ : Nat.card (Zv β) = 2
  hnat : IsNatSec (stab β) (Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)) (Vn β)
  hb5 : 5 ≤ bMin H M

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem hb1 : 1 < bMin H M := by have := C.hb5; omega

theorem hb3 : 3 ≤ bMin H M := by have := C.hb5; omega

theorem vtype_beta : vtype β = false := vtype_false_of_mem_nbrs_true C.hc.adj C.hv

theorem hss114 : Zv α' = quasithinOmegaOneCenter (stab α') ∧ Odd (bMin H M) ∧
    vtype α' = vtype β :=
  hss114_ab C.hA C.hc C.hcomm C.hb1

theorem hodd : Odd (bMin H M) := C.hss114.2.1

theorem vtype_alpha' : vtype α' = false := C.hss114.2.2.trans C.vtype_beta

theorem Zv_le_center {ν : Geo H M} (hν : vtype ν = false) : Zv ν ≤ centerOf (stab ν) := by
  have hz := C.h32 α β C.hc.adj C.hv C.hc.bAt_eq
  have h1 := Zv_eq_omegaOneCenter_of_central C.hA hz
  have h2 := Zv_central_of_conj C.hA (show vtype β = vtype ν by rw [C.vtype_beta, hν]) h1
  rw [h2]; exact omegaOneCenter_le_centerOf_self _

theorem Zv_eq_omega {ν : Geo H M} (hν : vtype ν = false) :
    Zv ν = quasithinOmegaOneCenter (stab ν) :=
  Zv_eq_omegaOneCenter_of_central C.hA (C.Zv_le_center hν)

theorem bAt_eq_of_true {ℓ : Geo H M} (hℓ : vtype ℓ = true) : bAt ℓ = bMin H M := by
  rw [← C.hc.bAt_eq]; exact bAt_eq_of_vtype_eq (by rw [hℓ, C.hv])

theorem bMin_lt_bAt {ν : Geo H M} (hν : vtype ν = false) : bMin H M < bAt ν := by
  have h1 := bMin_le_bAt (H := H) (M := M) ν
  by_contra hne
  have heq : bAt ν = bMin H M := by omega
  have h12 := centralizer_Zv_eq_Qv_of_bAt C.hA heq
  have hcen : stab ν ≤ Subgroup.centralizer (Zv ν : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.mp (C.Zv_le_center hν hz).2) x hx).symm
  rw [inf_eq_left.mpr hcen] at h12
  exact pCoreOf_ne_stab C.hA ν h12.symm

theorem Zv_le_stab_of_dist_le {ν x : Geo H M} (hν : vtype ν = false)
    (h : dist ν x ≤ bMin H M + 1) : Zv ν ≤ stab x := by
  have := C.bMin_lt_bAt hν
  exact _root_.CFSG.Quasithin.F53.Zv_le_stab_of_dist_le C.hA (by omega)

theorem Zv_le_Qv_of_true {ℓ x : Geo H M} (hℓ : vtype ℓ = true) (h : dist ℓ x < bMin H M) :
    Zv ℓ ≤ Qv x :=
  Zv_le_Qv_of_dist_lt (by rw [C.bAt_eq_of_true hℓ]; exact h)

theorem Zv_le_stab_of_true {ℓ x : Geo H M} (hℓ : vtype ℓ = true) (h : dist ℓ x ≤ bMin H M) :
    Zv ℓ ≤ stab x :=
  _root_.CFSG.Quasithin.F53.Zv_le_stab_of_dist_le C.hA (by rw [C.bAt_eq_of_true hℓ]; exact h)

theorem centerOf_eq_bot {ℓ : Geo H M} (hℓ : vtype ℓ = true) : centerOf (stab ℓ) = ⊥ := by
  obtain ⟨e, he⟩ := exists_adj ℓ
  have hv := vtype_false_of_mem_nbrs_true (show e ∈ nbrs ℓ from he) hℓ
  exact centerOf_eq_bot_of_Zv_central C.hA (show ℓ ∈ nbrs e from he.symm) (C.Zv_le_center hv)

theorem card_Zv_true {ℓ : Geo H M} (hℓ : vtype ℓ = true) : Nat.card (Zv ℓ) = 4 := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (δ := α) (δ' := ℓ) (by rw [hℓ, C.hv])
  rw [Zv_smul, card_conjSub]
  exact C.hZα

theorem card_Zv_false {ν : Geo H M} (hν : vtype ν = false) : Nat.card (Zv ν) = 2 := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (δ := β) (δ' := ν) (by rw [hν, C.vtype_beta])
  rw [Zv_smul, card_conjSub]
  exact C.hZβ

theorem zgen_spec' {ν : Geo H M} (hν : vtype ν = false) :
    zgen ν ∈ Zv ν ∧ zgen ν ≠ 1 ∧ ∀ x ∈ Zv ν, x = 1 ∨ x = zgen ν :=
  zgen_spec (C.card_Zv_false hν)

theorem Zv_le_Zv_of_mem_nbrs {ℓ ν : Geo H M} (hℓ : vtype ℓ = true) (hν : ν ∈ nbrs ℓ) :
    Zv ν ≤ Zv ℓ := by
  have hvν := vtype_false_of_mem_nbrs_true hν hℓ
  rw [C.Zv_eq_omega hvν]
  have h := omegaOneCenter_le_Zv C.hA (show ℓ ∈ nbrs ν from (nbr_adj hν).symm)
  exact h.1.trans h.2.2

theorem Zv_sup_eq_and_inf_eq_bot {ℓ ν ν' : Geo H M} (hℓ : vtype ℓ = true) (hν : ν ∈ nbrs ℓ)
    (hν' : ν' ∈ nbrs ℓ) (hne : ν ≠ ν') : Zv ν ⊔ Zv ν' = Zv ℓ ∧ Zv ν ⊓ Zv ν' = ⊥ :=
  OrdinaryProofs.Zv_sup_eq_and_inf_eq_bot C.hA hℓ (C.bAt_eq_of_true hℓ) hν hν' hne
    (C.Zv_le_center (vtype_false_of_mem_nbrs_true hν hℓ))

theorem Zv_ne_of_mem_nbrs {ℓ ν ν' : Geo H M} (hℓ : vtype ℓ = true) (hν : ν ∈ nbrs ℓ)
    (hν' : ν' ∈ nbrs ℓ) (hne : ν ≠ ν') : Zv ν ≠ Zv ν' := by
  intro h
  have := (C.Zv_sup_eq_and_inf_eq_bot hℓ hν hν' hne).2
  rw [h, inf_idem] at this
  exact Zv_ne_bot C.hA ν' this

theorem not_Qv_le_Qv {ℓ ν : Geo H M} (hℓ : vtype ℓ = true) (hν : ν ∈ nbrs ℓ) :
    ¬ Qv ν ≤ Qv ℓ := by
  intro h
  have h28 := C.h28 C.hb1 ℓ ν hν (C.bAt_eq_of_true hℓ)
  rw [sup_eq_left.mpr h] at h28
  have h2 := relIndex_Qv_inf_true C.hA hν hℓ
  rw [← h28, Subgroup.relIndex_self] at h2
  omega

theorem comm_Zv_Qv_eq {ℓ ν : Geo H M} (hℓ : vtype ℓ = true) (hν : ν ∈ nbrs ℓ) :
    ⁅Zv ℓ, Qv ν⁆ = Zv ν := by
  have hvν := vtype_false_of_mem_nbrs_true hν hℓ
  have hle : ⁅Zv ℓ, Qv ν⁆ ≤ Zv ν := by
    rw [Subgroup.commutator_le]
    intro x hx q hq
    exact OrdinaryProofs.comm_Zv_Qv_mem_Zv C.hA hvν (C.Zv_le_center hvν)
      (mem_nbrs_comm hν) hx hq
  have hne : ⁅Zv ℓ, Qv ν⁆ ≠ ⊥ := by
    intro hbot
    apply C.not_Qv_le_Qv hℓ hν
    have hcen := centralizer_Zv_eq_Qv_of_bAt C.hA (C.bAt_eq_of_true hℓ)
    rw [← hcen]
    refine le_inf ((Qv_le_inf C.hA (mem_nbrs_comm hν)).trans inf_le_right) ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact Subgroup.le_centralizer_iff.mp hbot
  have hcard := C.card_Zv_false hvν
  have h1 : 1 < Nat.card ↥⁅Zv ℓ, Qv ν⁆ := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have h2 : Nat.card ↥⁅Zv ℓ, Qv ν⁆ ≤ Nat.card ↥(Zv ν) := Subgroup.card_le_of_le hle
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

theorem comm_Vn_Qv_eq {ν : Geo H M} (hν : vtype ν = false) : ⁅Vn ν, Qv ν⁆ = Zv ν := by
  apply le_antisymm
  · exact OrdinaryProofs.commutator_Vn_Qv_le C.hA hν (C.Zv_le_center hν)
  · obtain ⟨ℓ, hℓ⟩ := exists_adj ν
    have hℓn : ℓ ∈ nbrs ν := hℓ
    have hvℓ := vtype_true_of_mem_nbrs_false hℓn hν
    rw [← C.comm_Zv_Qv_eq hvℓ (mem_nbrs_comm hℓn)]
    exact Subgroup.commutator_mono (Zv_le_Vn_of_mem_nbrs hℓn) le_rfl

theorem Vn_le_Qv_of_dist {δ x : Geo H M} (hδ : vtype δ = false) (h : dist δ x + 2 ≤ bMin H M) :
    Vn δ ≤ Qv x := by
  refine iSup₂_le fun ℓ hℓ => ?_
  have hvℓ := vtype_true_of_mem_nbrs_false hℓ hδ
  have h1 : dist ℓ x ≤ dist δ x + 1 := by
    have := dist_le_dist_nbr hℓ x
    rw [CosetGeom.dist_comm x ℓ, CosetGeom.dist_comm x δ] at this
    exact this
  exact C.Zv_le_Qv_of_true hvℓ (by omega)

theorem Vn_le_stab_of_dist {δ x : Geo H M} (hδ : vtype δ = false) (h : dist δ x + 1 ≤ bMin H M) :
    Vn δ ≤ stab x := by
  refine iSup₂_le fun ℓ hℓ => ?_
  have hvℓ := vtype_true_of_mem_nbrs_false hℓ hδ
  have h1 : dist ℓ x ≤ dist δ x + 1 := by
    have := dist_le_dist_nbr hℓ x
    rw [CosetGeom.dist_comm x ℓ, CosetGeom.dist_comm x δ] at this
    exact this
  exact C.Zv_le_stab_of_true hvℓ (by omega)

theorem Vn_le_Qv_self {δ : Geo H M} (hδ : vtype δ = false) : Vn δ ≤ Qv δ :=
  C.Vn_le_Qv_of_dist hδ (by rw [CosetGeom.dist_self]; have := C.hb5; omega)

theorem smul_eq_third {ν δ δ' δ'' : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν)
    (hδ' : δ' ∈ nbrs ν) (hδ'' : δ'' ∈ nbrs ν) (h1 : δ ≠ δ') (h2 : δ ≠ δ'') (h3 : δ' ≠ δ'')
    {q : ↥(H ⊔ M)} (hqδ : (q : G) ∈ Qv δ) (hqν : (q : G) ∉ Qv ν) : q • δ' = δ'' := by
  have hqs : (q : G) ∈ stab δ ⊓ stab ν := Qv_le_inf C.hA (mem_nbrs_comm hδ) hqδ
  have hqδfix : q • δ = δ := smul_eq_of_mem_stab hqs.1
  have hqνfix : q • ν = ν := smul_eq_of_mem_stab hqs.2
  have hmem : q • δ' ∈ nbrs ν := by
    have : (graph (H ⊔ M) H M).Adj (q • ν) (q • δ') := (smul_adj q).mpr hδ'
    rw [hqνfix] at this
    exact this
  have hne1 : q • δ' ≠ δ := by
    intro h
    rw [← hqδfix] at h
    exact h1 (smul_left_cancel q h).symm
  have hne2 : q • δ' ≠ δ' := by
    intro h
    exact hqν (mem_Qv_of_fixes_two_nbrs C.hA hν hδ hδ' h1 hqs.2 hqs.1 (mem_stab_of_smul_eq h))
  have hnb := eq_of_three_mem_nbrs C.hA hν h1 h2 h3 hδ hδ' hδ''
  rw [hnb] at hmem
  rcases hmem with h | h | h
  · exact absurd h hne1
  · exact absurd h hne2
  · exact h

end Ctx

@[expose] def Iv (ν : Geo H M) : Subgroup G := ⨅ δ ∈ nbrs ν, Vn δ

theorem Iv_le_Vn {ν δ : Geo H M} (hδ : δ ∈ nbrs ν) : Iv ν ≤ Vn δ :=
  iInf₂_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs ν) => Vn δ) δ hδ

theorem stab_le_normalizer_Iv (ν : Geo H M) : stab ν ≤ Subgroup.normalizer (Iv ν : Set G) := by
  have key : ∀ g ∈ stab ν, ∀ x ∈ Iv ν, g * x * g⁻¹ ∈ Iv ν := by
    intro g hg x hx
    obtain ⟨hgX, hgfix⟩ := mem_stab.mp hg
    simp only [Iv, Subgroup.mem_iInf] at hx ⊢
    intro ε hε
    set g' : ↥(H ⊔ M) := ⟨g, hgX⟩
    have hε' : g'⁻¹ • ε ∈ nbrs ν := by
      have : (graph (H ⊔ M) H M).Adj (g'⁻¹ • ν) (g'⁻¹ • ε) := (smul_adj g'⁻¹).mpr hε
      rwa [show g'⁻¹ • ν = ν by rw [inv_smul_eq_iff, hgfix]] at this
    have hx' := hx _ hε'
    have e : Vn ε = conjSub (g' : G) (Vn (g'⁻¹ • ε)) := by
      rw [← Vn_smul, smul_inv_smul]
    rw [e, mem_conjSub]
    simpa [g', mul_assoc] using hx'
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem Vn_inf_Vn_eq_Iv {ν δ δ' : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν)
    (hδ' : δ' ∈ nbrs ν) (hne : δ ≠ δ') : Vn δ ⊓ Vn δ' = Iv ν := by
  refine le_antisymm ?_ (le_inf (Iv_le_Vn hδ) (Iv_le_Vn hδ'))
  intro x hx
  obtain ⟨δ'', hδ'', h2, h3⟩ := exists_third_mem_nbrs C.hA hν hne
  have hvδ := vtype_false_of_mem_nbrs_true hδ hν
  have hx'' : x ∈ Vn δ'' := by
    obtain ⟨q, hqδ, hqν⟩ := Set.not_subset.mp (C.not_Qv_le_Qv hν hδ)
    have hqX : q ∈ H ⊔ M := stab_le δ ((Qv_le_inf C.hA (mem_nbrs_comm hδ) hqδ).1)
    set q' : ↥(H ⊔ M) := ⟨q, hqX⟩
    have hsw : q' • δ' = δ'' :=
      C.smul_eq_third hν hδ hδ' hδ'' hne h2.symm h3.symm hqδ hqν
    have h1 : q * x * q⁻¹ ∈ Vn δ'' := by
      rw [← hsw, Vn_smul, mem_conjSub]
      simpa [q', mul_assoc] using hx.2
    have h2' : ⁅x⁻¹, q⁆ ∈ Zv δ := by
      rw [← C.comm_Vn_Qv_eq hvδ]
      exact Subgroup.commutator_mem_commutator ((Vn δ).inv_mem hx.1) hqδ
    have hZ : Zv δ ≤ Vn δ'' :=
      (C.Zv_le_Zv_of_mem_nbrs hν hδ).trans (Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hδ''))
    have e : x = (q * x * q⁻¹) * ⁅x⁻¹, q⁆⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact (Vn δ'').mul_mem h1 ((Vn δ'').inv_mem (hZ h2'))
  simp only [Iv, Subgroup.mem_iInf]
  intro ε hε
  rw [eq_of_three_mem_nbrs C.hA hν hne h2.symm h3.symm hδ hδ' hδ''] at hε
  rcases hε with rfl | rfl | rfl
  · exact hx.1
  · exact hx.2
  · exact hx''

end Ctx

theorem mem_normalizer_of_commute {K : Subgroup G} {x : G} (h : ∀ z ∈ K, x * z = z * x) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have e : x * z * x⁻¹ = z := by rw [h z hz]; group
    rw [e]; exact hz
  · intro hz
    have h1 := h _ hz
    have h2 : x * z * x⁻¹ = z := by
      have : x * (x * z * x⁻¹) = x * z := by rw [h1]; group
      exact mul_left_cancel this
    rw [← h2]; exact hz

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem isNatSec {δ : Geo H M} (hδ : vtype δ = false) :
    IsNatSec (stab δ) (F53B3.Cv δ) (Vn δ) :=
  F53B3.isNatSec_all C.hA C.vtype_beta C.hnat δ hδ

theorem Zv_le_Cv {δ : Geo H M} (hδ : vtype δ = false) : Zv δ ≤ F53B3.Cv δ := by
  obtain ⟨ℓ, hℓ⟩ := exists_adj δ
  have hℓn : ℓ ∈ nbrs δ := hℓ
  have hvℓ := vtype_true_of_mem_nbrs_false hℓn hδ
  refine le_inf ((C.Zv_le_Zv_of_mem_nbrs hvℓ (mem_nbrs_comm hℓn)).trans
    (Zv_le_Vn_of_mem_nbrs hℓn)) ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact ((Subgroup.mem_centralizer_iff.mp (C.Zv_le_center hδ hz).2) l (oTwoRes_le _ hl))

theorem cSecIn_eq_Qv {δ : Geo H M} (hδ : vtype δ = false) :
    cSecIn (stab δ) (F53B3.Cv δ) (Vn δ) = Qv δ := by
  have hq := quot_stab_five C.hA hδ
  refine F53B3.N37.cSecIn_eq_pCoreOf_of_nat hq (C.isNatSec hδ) fun q hq' => ?_
  refine Subgroup.subset_closure ⟨pCoreOf_le 2 (stab δ) hq', fun v hv => ?_⟩
  have h1 : v * q * v⁻¹ * q⁻¹ ∈ ⁅Vn δ, Qv δ⁆ := Subgroup.commutator_mem_commutator hv hq'
  rw [C.comm_Vn_Qv_eq hδ] at h1
  have e : q * v * q⁻¹ * v⁻¹ = (v * q * v⁻¹ * q⁻¹)⁻¹ := by group
  rw [e]
  exact C.Zv_le_Cv hδ (Zv δ |>.inv_mem h1)

theorem oTwoRes_not_le_Qv {δ : Geo H M} : ¬ oTwoRes (stab δ) ≤ Qv δ := by
  intro h
  obtain ⟨ν, hν⟩ := exists_adj δ
  have hνn : ν ∈ nbrs δ := hν
  obtain ⟨ν', hν', hne⟩ := exists_mem_nbrs_ne C.hA δ hνn
  have hT := sylow_stab_inf_left C.hA hνn
  have hle := le_oTwoRes_sup_of_isSylowTwoOf hT
  rw [sup_eq_right.mpr (h.trans (Qv_le_inf C.hA hνn))] at hle
  obtain ⟨g, hg, hgν⟩ := stab_transitive_on_nbrs hνn hν'
  exact hne (by rw [← hgν]; exact smul_eq_of_mem_stab (hle hg).2)

theorem exists_oTwoRes_smul {δ ν ν' : Geo H M} (hν : ν ∈ nbrs δ) (hν' : ν' ∈ nbrs δ) :
    ∃ x : ↥(H ⊔ M), (x : G) ∈ oTwoRes (stab δ) ∧ x • ν = ν' :=
  exists_smul_eq_of_normal_not_le C.hA hν hν' (oTwoRes_le _) (le_normalizer_oTwoRes _)
    C.oTwoRes_not_le_Qv

theorem Zv_inf_Cv_eq {δ ν : Geo H M} (hδ : vtype δ = false) (hν : ν ∈ nbrs δ) :
    Zv ν ⊓ F53B3.Cv δ = Zv δ := by
  have hvν := vtype_true_of_mem_nbrs_false hν hδ
  have hle : Zv δ ≤ Zv ν ⊓ F53B3.Cv δ :=
    le_inf (C.Zv_le_Zv_of_mem_nbrs hvν (mem_nbrs_comm hν)) (C.Zv_le_Cv hδ)
  by_contra hne
  have hlt : Zv δ < Zv ν ⊓ F53B3.Cv δ := lt_of_le_of_ne hle (Ne.symm hne)
  have h4 := C.card_Zv_true hvν
  have h2 := C.card_Zv_false hδ
  have hZC : Zv ν ≤ F53B3.Cv δ := by
    have hc1 : Nat.card ↥(Zv δ) < Nat.card ↥(Zv ν ⊓ F53B3.Cv δ) :=
      Subgroup.card_lt_of_lt hlt
    have hdvd : Nat.card ↥(Zv ν ⊓ F53B3.Cv δ) ∣ Nat.card ↥(Zv ν) :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [h4] at hdvd
    rw [h2] at hc1
    have hc4 : Nat.card ↥(Zv ν ⊓ F53B3.Cv δ) = 4 := by
      have : Nat.card ↥(Zv ν ⊓ F53B3.Cv δ) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card ↥(Zv ν ⊓ F53B3.Cv δ) <;> simp_all
    have := Subgroup.eq_of_le_of_card_ge (inf_le_left : Zv ν ⊓ F53B3.Cv δ ≤ Zv ν) (by omega)
    rw [← this]; exact inf_le_right
  have hU : Zv ν ≤ stab δ ⊓ stab ν :=
    le_inf ((Zv_le_Qv C.hA ν).trans (Qv_le_inf C.hA (mem_nbrs_comm hν)) |>.trans inf_le_right)
      ((Zv_le_Qv C.hA ν).trans (pCoreOf_le 2 (stab ν)))
  have hbot := eq_bot_of_normalizer_transitive_vertex C.hA hν hU
    (fun ε hε ε' hε' => by
      obtain ⟨x, hxL, hxε⟩ := C.exists_oTwoRes_smul hε hε'
      refine ⟨x, mem_normalizer_of_commute fun z hz => ?_, smul_eq_of_mem_stab (oTwoRes_le _ hxL),
        hxε⟩
      exact (Subgroup.mem_centralizer_iff.mp (hZC hz).2) x hxL)
    (fun ε hε ε' hε' => by
      obtain ⟨g, hg, hgε⟩ := stab_transitive_on_nbrs hε hε'
      exact ⟨g, stab_le_normalizer_Zv C.hA ν hg, smul_eq_of_mem_stab hg, hgε⟩)
  exact Zv_ne_bot C.hA ν hbot

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
