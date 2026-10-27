module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Sit43

variable {α : Geo H M}

theorem exists_nbr_dist (hA : F53Amalgam H M S) (hs : Sit43 α) {α' : Geo H M}
    (hc : IsCritPair₁ α α') : ∃ ν : Geo H M, ν ∈ nbrs α' ∧ dist α ν + 1 = bMin H M := by
  have hb := hs.b1
  obtain ⟨ν, hν, hd⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α) (δ := α')
    (d := bMin H M - 1) (by rw [hc.2]; omega)
  exact ⟨ν, hν, by omega⟩

theorem relIndex_Zv_eq (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') :
    (Zv α ⊓ Qv α').relIndex (Zv α) = (Zv α' ⊓ Qv α).relIndex (Zv α') :=
  hss113aAt_of hA α α' hc (hs.comm_ne_bot_crit hA he hc)

theorem inf_centralizer_Zv_eq (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') :
    Zv α ⊓ Subgroup.centralizer (Zv α' : Set G) = Zv α ⊓ Qv α' := by
  rw [← hs.centralizer_Zv hA (hs.vtype_crit hA he hc)]
  apply le_antisymm
  · exact fun x hx => ⟨hx.1, hs.Zv_le_stab_crit hA hc hx.1, hx.2⟩
  · exact fun x hx => ⟨hx.1, hx.2.2⟩

theorem inf_centralizer_Zv_eq' (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') :
    Zv α' ⊓ Subgroup.centralizer (Zv α : Set G) = Zv α' ⊓ Qv α :=
  (hs.sit_crit hA he hc).inf_centralizer_Zv_eq hA he (hs.isCritPair₁_symm hA he hc)

theorem offender_dichotomy_crit (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) {α' ν : Geo H M} (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hd : dist α ν < bMin H M) :
    ⁅Zv α', Zv α⁆ ≤ Yv ν ∧
      (((Zv α ⊓ Qv α').relIndex (Zv α) = 2 ∧
        (∃ z ∈ Zv α, z ∉ Qv α' ∧
          (Zv α' ⊓ Subgroup.centralizer ({z} : Set G)).relIndex (Zv α') = 2 ∧
          Zv α ≤ Subgroup.zpowers z ⊔ Qv α') ∧
        Nat.card ↥⁅Zv α', Zv α⁆ = 2 ∧ ⁅Zv α', Zv α⁆ ≠ Zv ν ∧ ⁅Zv α', Zv α⁆ ⊔ Zv ν = Yv ν) ∨
      ((Zv α ⊓ Qv α').relIndex (Zv α) = 4 ∧
        Zv α ⊔ Qv α' = (stab α' ⊓ stab ν) ⊓ Subgroup.centralizer (Yv ν : Set G) ∧
        ⁅Zv α', Zv α⁆ = Yv ν)) := by
  have hα'v : vtype α' = false := hs.vtype_crit hA he hc
  have hs' : Sit43 α' := hs.sit_crit hA he hc
  have hνv : vtype ν = true := vtype_true_of_adj hα'v hν
  have hα'ν : α' ∈ nbrs ν := nbrs_symm hν
  have hZQ : Zv α ≤ Qv ν := hs.Zv_le_Qv_of_dist_lt_false hs.vα hd
  have hBS : Zv α ≤ stab α' ⊓ stab ν :=
    le_inf (hZQ.trans (Qv_le_stab_of_mem_nbrs hA hα'ν)) (hZQ.trans (pCoreOf_le 2 _))
  have hY := hs.Yv_eq_comm_comm hA h26 hνv hα'ν
  have hZν := hs.Zv_inf_centralizer hA h26 hνv hα'ν
  have hidx : (pCoreOf 2 (stab α') ⊓ Zv α).relIndex (Zv α) =
      (Zv α' ⊓ Subgroup.centralizer (Zv α : Set G)).relIndex (Zv α') := by
    rw [hs.inf_centralizer_Zv_eq' hA he hc, inf_comm]
    exact hs.relIndex_Zv_eq hA he hc
  obtain ⟨hcomm, hcase⟩ := offender_trichotomy (quot_stab_five hA hα'v) (sylow_stab_inf_left hA hν)
    hs'.orth hBS (isElemAbelian_Zv hA α) hidx
  rw [← hY] at hcomm
  refine ⟨hcomm, ?_⟩
  rcases hcase with h1 | ⟨⟨z, hz, hzQ, hzidx, hzB⟩, hr, hcard, hne, hsup⟩ | ⟨hr, hsup, hcomm4⟩
  · exact absurd h1 hc.1
  · left
    rw [inf_comm] at hr
    rw [hZν, ← hY] at hsup
    rw [hZν] at hne
    exact ⟨hr, ⟨z, hz, hzQ, hzidx, hzB⟩, hcard, hne, hsup⟩
  · right
    rw [inf_comm] at hr
    rw [← hY] at hsup hcomm4
    exact ⟨hr, hsup, hcomm4⟩

theorem relIndex_Zv_two_or_four (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) {α' ν : Geo H M} (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hd : dist α ν < bMin H M) :
    (Zv α ⊓ Qv α').relIndex (Zv α) = 2 ∨ (Zv α ⊓ Qv α').relIndex (Zv α) = 4 := by
  rcases (hs.offender_dichotomy_crit hA h26 he hc hν hd).2 with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem Zv_sup_Qv_eq_of_four (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) {α' ν : Geo H M} (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hd : dist α ν < bMin H M) (h4 : (Zv α ⊓ Qv α').relIndex (Zv α) = 4) :
    Zv α ⊔ Qv α' = (stab α' ⊓ stab ν) ⊓ Subgroup.centralizer (Yv ν : Set G) := by
  rcases (hs.offender_dichotomy_crit hA h26 he hc hν hd).2 with h | h
  · have := h.1.symm.trans h4
    omega
  · exact h.2.1

theorem exists_transposition_of_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) {α' ν : Geo H M} (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hd : dist α ν < bMin H M) (h2 : (Zv α ⊓ Qv α').relIndex (Zv α) = 2) :
    ∃ z ∈ Zv α, z ∉ Qv α' ∧
      (Zv α' ⊓ Subgroup.centralizer ({z} : Set G)).relIndex (Zv α') = 2 ∧
      Zv α ≤ Subgroup.zpowers z ⊔ Qv α' := by
  rcases (hs.offender_dichotomy_crit hA h26 he hc hν hd).2 with h | h
  · exact h.2.1
  · have := h2.symm.trans h.1
    omega

theorem comm_le_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) {α' ν : Geo H M} (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hd : dist α ν < bMin H M) : ⁅Zv α, Zv α'⁆ ≤ Yv ν := by
  rw [Subgroup.commutator_comm]
  exact (hs.offender_dichotomy_crit hA h26 he hc hν hd).1

theorem comm_eq_Yv_of_four (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) {α' ν : Geo H M} (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hd : dist α ν < bMin H M) (h4 : (Zv α ⊓ Qv α').relIndex (Zv α) = 4) :
    ⁅Zv α, Zv α'⁆ = Yv ν := by
  rw [Subgroup.commutator_comm]
  rcases (hs.offender_dichotomy_crit hA h26 he hc hν hd).2 with h | h
  · have := h.1.symm.trans h4
    omega
  · exact h.2.2

theorem comm_of_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) {α' ν : Geo H M} (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hd : dist α ν < bMin H M) (h2 : (Zv α ⊓ Qv α').relIndex (Zv α) = 2) :
    Nat.card ↥⁅Zv α, Zv α'⁆ = 2 ∧ ⁅Zv α, Zv α'⁆ ≠ Zv ν ∧ ⁅Zv α, Zv α'⁆ ⊔ Zv ν = Yv ν := by
  rw [Subgroup.commutator_comm]
  rcases (hs.offender_dichotomy_crit hA h26 he hc hν hd).2 with h | h
  · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · have := h2.symm.trans h.1
    omega

theorem vtype_of_dist_two (hA : F53Amalgam H M S) (hs : Sit43 α) {l : Geo H M}
    (h : dist l α = 2) : vtype l = false := by
  have h1 := (vtype_eq_iff_even_dist hA.amalgam.gen α l).mpr (by
    rw [CosetGeom.dist_comm, h]; exact even_two)
  rw [hs.vα] at h1
  exact h1.symm

theorem exists_common_nbr_of_dist_two (hA : F53Amalgam H M S) {l : Geo H M} (h : dist l α = 2) :
    ∃ μ : Geo H M, μ ∈ nbrs α ∧ l ∈ nbrs μ := by
  obtain ⟨μ, hμ, hd⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α) (δ := l) (d := 1)
    (by rw [CosetGeom.dist_comm, h])
  exact ⟨μ, dist_eq_one_iff_adj.mp hd, nbrs_symm hμ⟩

theorem exists_dist_two (hA : F53Amalgam H M S) (hs : Sit43 α) {μ : Geo H M}
    (hμ : μ ∈ nbrs α) : ∃ l : Geo H M, l ∈ nbrs μ ∧ dist l α = 2 := by
  have hμv : vtype μ = true := vtype_true_of_adj hs.vα hμ
  have h3 := card_nbrs_true hA hμv
  have hex : ∃ l : Geo H M, l ∈ nbrs μ ∧ l ≠ α := by
    by_contra hcon
    push Not at hcon
    have hsub : nbrs μ ⊆ {α} := fun x hx => hcon x hx
    have := Set.ncard_le_ncard hsub (Set.finite_singleton α)
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq, h3] at this
    omega
  obtain ⟨l, hl, hne⟩ := hex
  refine ⟨l, hl, ?_⟩
  have hlμ : dist l μ = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm hl)
  have hμα : dist μ α = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm hμ)
  have h1 := dist_triangle hA.amalgam.gen l μ α
  have h0 : dist l α ≠ 0 := fun h => hne ((dist_eq_zero_iff hA.amalgam.gen).mp h)
  have h1' : dist l α ≠ 1 := by
    intro h
    have hadj := dist_eq_one_iff_adj.mp h
    have hlv : vtype l = false := vtype_false_of_adj hμv hl
    exact vtype_ne_of_adj hadj (hlv.trans hs.vα.symm)
  omega

omit [Finite G] in
theorem Vn_le_Qv_of_true (hs : Sit43 α) {δ : Geo H M} (hδ : vtype δ = true) : Vn δ ≤ Qv δ := by
  refine iSup₂_le fun l hl => hs.Zv_le_Qv_of_dist_lt_false (vtype_false_of_adj hδ hl) ?_
  have : dist l δ = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm hl)
  have := hs.b1
  omega

theorem isElemAbelian_Vn_of_three (hA : F53Amalgam H M S) (hb : 3 ≤ bMin H M) (δ : Geo H M) :
    IsElemAbelian 2 (Vn δ) :=
  isElemAbelian_Vn hA hb δ

omit [Finite G] in
theorem Zv_le_Wn_of_dist {l : Geo H M} (h : dist l α = 2) : Zv l ≤ Wn α :=
  le_iSup₂_of_le (f := fun (l : Geo H M) (_ : dist l α = 2) => Zv l) l h le_rfl

theorem Wn_le_Qv (hA : F53Amalgam H M S) (hs : Sit43 α) (hb : 3 ≤ bMin H M) : Wn α ≤ Qv α :=
  iSup₂_le fun l hl => hs.Zv_le_Qv_of_dist_lt_false (hs.vtype_of_dist_two hA hl)
    (by rw [hl]; omega)

theorem Zv_le_Wn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) :
    Zv α ≤ Wn α := by
  rw [← hs.Vn_eq_Zv hA h26 hs.vα]
  refine iSup₂_le fun μ hμ => ?_
  obtain ⟨l, hl, hd⟩ := hs.exists_dist_two hA hμ
  exact (hs.Zv_le_Zv_nbr hA h26 (vtype_true_of_adj hs.vα hμ) hl).trans (Zv_le_Wn_of_dist hd)

theorem Wn_le_centralizer (hA : F53Amalgam H M S) (hs : Sit43 α) (hb : 3 ≤ bMin H M) :
    Wn α ≤ Subgroup.centralizer (Zv α : Set G) :=
  (hs.Wn_le_Qv hA hb).trans (Qv_le_centralizer_Zv hA α)

theorem isElemAbelian_Wn (hA : F53Amalgam H M S) (hs : Sit43 α) (hb : 6 ≤ bMin H M) :
    IsElemAbelian 2 (Wn α) := by
  have e : Wn α = ⨆ l : {l : Geo H M // dist l α = 2}, Zv l.1 := by
    unfold Wn; exact iSup_subtype'
  rw [e]
  refine isElemAbelian_iSup _ (fun l => isElemAbelian_Zv hA l.1) (fun l l' x hx y hy => ?_)
  have h3 := dist_triangle hA.amalgam.gen l.1 α l'.1
  rw [CosetGeom.dist_comm α l'.1, l.2, l'.2] at h3
  have hxQ : x ∈ Qv l'.1 :=
    hs.Zv_le_Qv_of_dist_lt_false (hs.vtype_of_dist_two hA l.2) (by omega) hx
  exact Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA l'.1 hy).2 x hxQ

theorem comm_le_Zv_of_dist_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) {l l' : Geo H M} (hl : dist l α = 2) (hl' : dist l' α = 2) :
    ⁅Zv l, Zv l'⁆ ≤ Zv α := by
  have hlv := hs.vtype_of_dist_two hA hl
  by_cases hle : Zv l ≤ Qv l'
  · refine le_trans (le_of_eq ?_) bot_le
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA l' hy).2 x (hle hx)).symm
  · have h3 := dist_triangle hA.amalgam.gen l α l'
    rw [CosetGeom.dist_comm α l', hl, hl'] at h3
    have hd : dist l l' = bMin H M := by
      by_contra hne
      exact hle (hs.Zv_le_Qv_of_dist_lt_false hlv (by omega))
    have he : Even (bMin H M) := by
      have : bMin H M = 4 := by omega
      rw [this]; decide
    obtain ⟨μ, hμα, hμl'⟩ := exists_common_nbr_of_dist_two (α := α) hA hl'
    have hdl : dist l μ < bMin H M := by
      have h4 := dist_triangle hA.amalgam.gen l α μ
      have h5 : dist α μ = 1 := dist_eq_one_iff_adj.mpr hμα
      omega
    have hαμ : α ∈ nbrs μ := nbrs_symm hμα
    exact ((hs.of_vtype_false hlv).comm_le_Yv hA h26 he ⟨hle, hd⟩ (nbrs_symm hμl') hdl).trans
      (Yv_le_Zv hαμ)

omit [Finite G] in
theorem Wn_eq_iSup (α : Geo H M) : Wn α = ⨆ l : {l : Geo H M // dist l α = 2}, Zv l.1 := by
  unfold Wn; exact iSup_subtype'

theorem Wn_le_centralizer_Zv (hA : F53Amalgam H M S) (hs : Sit43 α) (hb : 3 ≤ bMin H M) :
    Zv α ≤ Subgroup.centralizer (Wn α : Set G) := fun _ hz => by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hz).2 w (hs.Wn_le_Qv hA hb hw)

theorem comm_Wn_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) : ⁅Wn α, Wn α⁆ ≤ Zv α := by
  have hn : Wn α ≤ Subgroup.normalizer (Zv α : Set G) :=
    ((hs.Wn_le_Qv hA (by omega)).trans (pCoreOf_le 2 _)).trans (stab_le_normalizer_Zv hA α)
  have hX : ∀ l : {l : Geo H M // dist l α = 2}, Zv l.1 ≤ Wn α := fun l => Zv_le_Wn_of_dist l.2
  have e := Wn_eq_iSup α
  have step1 : ∀ l' : {l : Geo H M // dist l α = 2}, ⁅Wn α, Zv l'.1⁆ ≤ Zv α := by
    intro l'
    have := commutator_iSup_le (X := Wn α) (Q := Zv l'.1) hX hn fun l =>
      hs.comm_le_Zv_of_dist_two hA h26 hb l.2 l'.2
    rwa [← e] at this
  have key : ⁅⨆ l : {l : Geo H M // dist l α = 2}, Zv l.1, Wn α⁆ ≤ Zv α :=
    commutator_iSup_le (X := Wn α) hX hn fun l => by
      rw [Subgroup.commutator_comm]
      exact step1 l
  calc ⁅Wn α, Wn α⁆ = ⁅⨆ l : {l : Geo H M // dist l α = 2}, Zv l.1, Wn α⁆ := by rw [← e]
    _ ≤ Zv α := key

theorem sq_mem_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) : ∀ x ∈ Wn α, x ^ 2 ∈ Zv α := by
  have hcomm := hs.comm_Wn_le hA h26 hb
  have hcen : ∀ y ∈ Zv α, ∀ w ∈ Wn α, w * y = y * w := fun y hy w hw =>
    Subgroup.mem_centralizer_iff.mp (hs.Wn_le_centralizer_Zv hA (by omega) hy) w hw
  intro x hx
  have hx' := hx
  rw [Wn_eq_iSup α] at hx'
  refine (Subgroup.iSup_induction (fun l : {l : Geo H M // dist l α = 2} => Zv l.1)
    (C := fun x => x ∈ Wn α ∧ x ^ 2 ∈ Zv α) hx' (fun l y hy => ⟨Zv_le_Wn_of_dist l.2 hy, ?_⟩)
    ⟨one_mem _, by simp⟩ ?_).2
  · have := (isElemAbelian_Zv hA l.1).2 y hy
    rw [this]; exact one_mem _
  · rintro x y ⟨hxW, hx2⟩ ⟨hyW, hy2⟩
    refine ⟨Subgroup.mul_mem _ hxW hyW, ?_⟩
    have hc : x * y * x⁻¹ * y⁻¹ ∈ Zv α :=
      hcomm (Subgroup.commutator_mem_commutator hxW hyW)
    have hyx2 : y * x ^ 2 = x ^ 2 * y := hcen _ hx2 y hyW
    have e : (x * y) ^ 2 = (x * y * x⁻¹ * y⁻¹) * x ^ 2 * y ^ 2 := by
      calc (x * y) ^ 2 = (x * y * x⁻¹ * y⁻¹) * (y * x ^ 2 * y) := by
            simp only [pow_two]; group
        _ = (x * y * x⁻¹ * y⁻¹) * (x ^ 2 * y * y) := by rw [hyx2]
        _ = (x * y * x⁻¹ * y⁻¹) * x ^ 2 * y ^ 2 := by simp only [pow_two, mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hx2) hy2

end Sit43

end F53.Stellmacher.S43

end CFSG.Quasithin
