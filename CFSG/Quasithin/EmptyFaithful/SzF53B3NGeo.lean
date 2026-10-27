module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3Defs
public import CFSG.Quasithin.EmptyFaithful.SzF53B3NSec
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.F53
open CFSG.Quasithin.F53Mod CFSG.Quasithin.CosetGeom

namespace F53B3

namespace N37

variable {G : Type} [Group G] {H M S : Subgroup G}

theorem elemAbelian_comm {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem le_normalizer_centralizer_of_le {X S : Subgroup G}
    (h : X ≤ Subgroup.normalizer (S : Set G)) :
    X ≤ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have hconj : ∀ g ∈ X, ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp (h hg) s).mp hs
    have key := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [key]
      _ = g * c * g⁻¹ * s := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨hconj g hg c, fun hc => ?_⟩
  have := hconj g⁻¹ (X.inv_mem hg) _ hc
  simpa [mul_assoc] using this

theorem Qv_le_stab_self (δ : Geo H M) : Qv δ ≤ stab δ := pCoreOf_le 2 (stab δ)

theorem stab_le_normalizer_Qv (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Qv δ : Set G) :=
  le_normalizer_pCoreOf 2 (stab δ)

theorem Vn_le_Qv_self (hBl : B3Block H M S) (δ : Geo H M) : Vn δ ≤ Qv δ :=
  hBl.vn_le_qv δ δ (by rw [CosetGeom.dist_self]; exact Nat.zero_le _)

theorem Vn_le_stab_self (hBl : B3Block H M S) (δ : Geo H M) : Vn δ ≤ stab δ :=
  (Vn_le_Qv_self hBl δ).trans (Qv_le_stab_self δ)

theorem Cv_le_Vn (δ : Geo H M) : Cv δ ≤ Vn δ := inf_le_left

theorem Zv_le_Cv (hBl : B3Block H M S) {x : Geo H M} (hx : vtype x = false) :
    Zv x ≤ Cv x := by
  obtain ⟨α, hα⟩ := exists_adj x
  have h := hBl.cv_inf_zv x α hx hα
  exact (le_of_eq h.symm).trans inf_le_left

theorem stab_le_normalizer_Cv (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Cv δ : Set G) :=
  F7.le_normalizer_inf (stab_le_normalizer_Vn δ)
    (le_normalizer_centralizer_of_le (le_normalizer_oTwoRes (stab δ)))

theorem Vn_le_Kq (hBl : B3Block H M S) (δ : Geo H M) : Vn δ ≤ Kq δ :=
  le_inf (Vn_le_Qv_self hBl δ) fun _ hv => Subgroup.mem_centralizer_iff.mpr fun _ hh =>
    elemAbelian_comm (hBl.elemAbelian_vn δ) hh hv

theorem Kq_le_Qv (δ : Geo H M) : Kq δ ≤ Qv δ := inf_le_left

theorem Kq_le_stab (δ : Geo H M) : Kq δ ≤ stab δ := (Kq_le_Qv δ).trans (Qv_le_stab_self δ)

theorem stab_le_normalizer_Kq (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Kq δ : Set G) :=
  F7.le_normalizer_inf (stab_le_normalizer_Qv δ)
    (le_normalizer_centralizer_of_le (stab_le_normalizer_Vn δ))

theorem Zv_le_Vn_of_adj {α β : Geo H M} (h : (graph (H ⊔ M) H M).Adj β α) : Zv α ≤ Vn β :=
  le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs β) => Zv μ) α h le_rfl

theorem dist_le_one_of_adj {u v : Geo H M} (h : (graph (H ⊔ M) H M).Adj u v) : dist u v ≤ 1 :=
  (dist_eq_one_iff_adj.mpr h).le

theorem dist_eq_two_of_nbrs {α β γ : Geo H M} (hβ : (graph (H ⊔ M) H M).Adj α β)
    (hγ : (graph (H ⊔ M) H M).Adj α γ) (hne : β ≠ γ) : dist β γ = 2 := by
  have h1 : dist β γ ≤ 2 := by
    have := dist_triangle_of_adj hβ.symm γ
    have h2 : dist β α = 1 := dist_eq_one_iff_adj.mpr hβ.symm
    have h3 : dist α γ = 1 := dist_eq_one_iff_adj.mpr hγ
    omega
  have h0 : dist β γ ≠ 0 := fun h => hne ((dist_eq_zero_iff rfl).mp h)
  have h1' : dist β γ ≠ 1 := by
    intro h
    have hadj := dist_eq_one_iff_adj.mp h
    have e1 := vtype_ne_of_adj hβ
    have e2 := vtype_ne_of_adj hγ
    have e3 := vtype_ne_of_adj hadj
    cases a : vtype α <;> cases b : vtype β <;> cases c : vtype γ <;> simp_all
  omega

theorem exists_arc [Finite G] (hA : F53Amalgam H M S) {β : Geo H M} (hβ : vtype β = false) :
    ∃ α γ : Geo H M, (graph (H ⊔ M) H M).Adj β α ∧ (graph (H ⊔ M) H M).Adj α γ ∧ γ ≠ β ∧
      vtype α = true ∧ vtype γ = false ∧ dist β γ = 2 := by
  obtain ⟨α, hα⟩ := exists_adj β
  have hvα : vtype α = true := vtype_nbr_of_false hα hβ
  have hcard : 1 < (nbrs α).ncard := by
    rw [← Nat.card_coe_set_eq, card_nbrs_true hA hvα]
    norm_num
  obtain ⟨γ, hγ, hne⟩ := Set.exists_ne_of_one_lt_ncard hcard β
  have hγα : (graph (H ⊔ M) H M).Adj α γ := hγ
  have hvγ : vtype γ = false := by
    have := vtype_ne_of_adj hγα
    cases h : vtype γ
    · rfl
    · exact absurd (hvα.trans h.symm) this
  exact ⟨α, γ, hα, hγα, hne, hvα, hvγ, dist_eq_two_of_nbrs hα.symm hγα hne.symm⟩

theorem sylow_inf_stab [Finite G] (hA : F53Amalgam H M S) {x α : Geo H M}
    (h : (graph (H ⊔ M) H M).Adj x α) : IsSylowTwoOf (stab α ⊓ stab x) (stab x) := by
  rw [inf_comm]
  exact sylow_stab_inf_left hA h

theorem cSecIn_nat_eq_Qv [Finite G] (hB : B3Facts H M S) (hBl : B3Block H M S) {x : Geo H M}
    (hx : vtype x = false) : cSecIn (stab x) (Cv x) (Vn x) = Qv x := by
  have hq := quot_stab_five hB.amalgam hx
  refine N37.cSecIn_eq_pCoreOf_of_nat hq (hB.nat x hx) fun q hq' => ?_
  refine Subgroup.subset_closure ⟨Qv_le_stab_self x hq', fun v hv => ?_⟩
  have h1 : v * q * v⁻¹ * q⁻¹ ∈ ⁅Vn x, Qv x⁆ := Subgroup.commutator_mem_commutator hv hq'
  rw [hBl.comm_vn_qv x hx] at h1
  have e : q * v * q⁻¹ * v⁻¹ = (v * q * v⁻¹ * q⁻¹)⁻¹ := by group
  rw [e]
  exact Zv_le_Cv hBl hx (Zv x |>.inv_mem h1)

end N37

end F53B3

end CFSG.Quasithin
