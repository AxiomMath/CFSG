module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCore4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE

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

theorem comm_Vn_le_inf (hA : F53Amalgam H M S) (hs : Sit43 α) {δ δ' : Geo H M}
    (h : IsCritPair₃ δ δ') : ⁅Vn δ, Vn δ'⁆ ≤ Vn δ ⊓ Vn δ' := by
  obtain ⟨hδ, hδ', hd, -⟩ := h
  refine commutator_le_inf_of_normalizes ?_ ?_
  · exact (Vn_le_stab_of_dist hA hs hδ (le_of_eq hd)).trans (stab_le_normalizer_Vn δ')
  · exact (Vn_le_stab_of_dist hA hs hδ' (by rw [CosetGeom.dist_comm]; exact le_of_eq hd)).trans
      (stab_le_normalizer_Vn δ)

theorem card_comm_Vn_ge (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {δ δ' : Geo H M} (h : IsCritPair₃ δ δ') :
    8 ≤ Nat.card ↥⁅Vn δ, Vn δ'⁆ := by
  set R := ⁅Vn δ, Vn δ'⁆ with hR
  have h4 := four_le_relIndex_comm_Vn hA h26 hs ho hb h
  have hne := comm_Vn_inf_Yv_ne_bot hA h26 hs ho hb h
  have hRn : R ≤ Subgroup.normalizer (Yv δ' : Set G) :=
    (comm_Vn_le_inf hA hs h).trans (inf_le_right.trans
      ((Vn_le_stab_of_dist hA hs h.2.1 (by rw [CosetGeom.dist_self]; omega)).trans
        (hs.stab_le_normalizer_Yv hA h26 h.2.1)))
  rw [Sit43.relIndex_sup_of_le_normalizer hRn] at h4
  have hmul := Subgroup.relIndex_mul_card (Yv δ') R
  have h2 : 1 < Nat.card ↥(Yv δ' ⊓ R) := by
    rw [Subgroup.one_lt_card_iff_ne_bot, inf_comm]
    exact hne
  rw [← hmul]
  calc 8 = 4 * 2 := by norm_num
    _ ≤ (Yv δ').relIndex R * Nat.card ↥(Yv δ' ⊓ R) := Nat.mul_le_mul h4 h2

theorem comm_Vn_le_Zv_gamma (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {α' β γ : Geo H M} (hc : IsCritPair₁ α α')
    (hβ : β ∈ nbrs α) (hdβ : dist β α' + 1 = bMin H M) (hγ : γ ∈ nbrs β)
    (hdγ : dist γ α' + 2 = bMin H M) (h4 : Nat.card (Vn β) = 2 ^ 6) :
    ⁅Vn β, Vn α'⁆ ≤ Zv γ := by
  have hβv := vtype_beta hs hβ
  have hα'v := vtype_crit hA hs ho hc
  have hγv : vtype γ = false := Sit43.vtype_false_of_adj hβv hγ
  have hcrit := isCritPair₃_crit hA hs ho hc hβ hdβ
  have hRV := comm_Vn_le_inf hA hs hcrit
  have hV'ab : IsElemAbelian 2 (Vn α') := isElemAbelian_Vn hA hb α'
  have hdαγ : dist γ α ≤ 2 := by
    have h1 := dist_le_of_mem_nbrs' hA (x := γ) hβ
    rw [CosetGeom.dist_comm γ β, dist_eq_one_iff_adj.mpr hγ] at h1
    omega
  have hαγ : α ≠ γ := by
    intro h
    rw [← h, hc.2] at hdγ
    omega
  have hVeq : Zv α ⊔ Zv γ = Vn β := hs.Zv_sup_Zv_eq hA h26 hb hβv (nbrs_symm hβ) hγ hαγ h4
  obtain ⟨x, hx, hxQ⟩ : ∃ x ∈ Vn α', x ∉ Qv β := by
    by_contra hcon
    push Not at hcon
    exact not_Vn_le_Qv_crit hA h26 hs ho hb hc hβ hdβ fun y hy => hcon y hy
  have hxγ : x ∈ Qv γ :=
    Vn_le_Qv_of_dist hA hs hα'v (by rw [CosetGeom.dist_comm]; omega) hx
  have hxβ : x ∈ stab β := Vn_le_stab_beta hA hs ho hc hdβ hx
  obtain ⟨c₂, c₃, h29⟩ := hs.exists_sit29 hA h26 hβv hγ
  have hsw := h29.smul_swap ⟨x, stab_le β hxβ⟩ (pCoreOf_le 2 _ hxγ) hxβ hxQ
  have hmov : (⟨x, stab_le β hxβ⟩ : ↥(H ⊔ M)) • α ≠ α := by
    rcases h29.nbrs_eq α (nbrs_symm hβ) with h | h | h
    · exact absurd h hαγ
    · rw [h, hsw.1]; exact h29.ne₂₃.symm
    · rw [h, hsw.2]; exact h29.ne₂₃
  have hγα : Zv γ ≤ Subgroup.normalizer (Zv α : Set G) :=
    (hs.Zv_le_stab_of_dist_le_false hA hγv (by omega)).trans (stab_le_normalizer_Zv hA α)
  intro r hr
  have hr₁ : r ∈ Vn β := (hRV hr).1
  have hrx : r * x = x * r := isElemAbelian_comm hV'ab (hRV hr).2 hx
  rw [← hVeq] at hr₁
  obtain ⟨a, ha, c, hcγ, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hγα).mp hr₁
  have hcx : c * x = x * c :=
    (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA γ hcγ).2 x hxγ).symm
  have hax : a * x = x * a := by
    have e : a * c * x = x * (a * c) := hrx
    have e2 : a * x * c = x * a * c := by
      calc a * x * c = a * (c * x) := by rw [mul_assoc, hcx]
        _ = x * (a * c) := by rw [← mul_assoc, e]
        _ = x * a * c := by group
    exact mul_right_cancel e2
  set U : Subgroup G := Zv α ⊓ Subgroup.centralizer ({x} : Set G) with hU
  have haU : a ∈ U := ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr hax⟩
  have hUY : U ≤ Yv β := by
    refine hs.le_Yv_of_normalizes hA h26 hβv (nbrs_symm hβ) inf_le_left hxβ hmov ?_
    exact conjSub_eq_of_commute fun v hv =>
      (Subgroup.mem_centralizer_singleton_iff.mp hv.2).symm
  exact (Zv γ).mul_mem (Yv_le_Zv hγ (hUY haU)) hcγ

theorem comm_Vn_le_Zv_nu (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {α' β ν : Geo H M} (hc : IsCritPair₁ α α')
    (hβ : β ∈ nbrs α) (hdβ : dist β α' + 1 = bMin H M) (hν : ν ∈ nbrs α')
    (hdν : dist α ν + 1 = bMin H M) (h4 : Nat.card (Vn α') = 2 ^ 6) :
    ⁅Vn β, Vn α'⁆ ≤ Zv ν := by
  have hα'v := vtype_crit hA hs ho hc
  have hcrit := isCritPair₃_crit hA hs ho hc hβ hdβ
  have hRV := comm_Vn_le_inf hA hs hcrit
  have hVab : IsElemAbelian 2 (Vn β) := isElemAbelian_Vn hA hb β
  obtain ⟨a₂, a₃, h29⟩ := exists_sit29_nu hA h26 hs ho hc hν
  have hlv : vtype a₂ = false := vtype_nu hA hs ho hc h29.n₂
  have hVeq : Zv ν ⊔ Zv a₂ = Vn α' := hs.Zv_sup_Zv_eq hA h26 hb hα'v hν h29.n₂ h29.ne₁₂ h4
  obtain ⟨z, hz, hzQ⟩ : ∃ z ∈ Zv α, z ∉ Qv α' := by
    by_contra hcon
    push Not at hcon
    exact hc.1 fun y hy => hcon y hy
  have hzν : z ∈ Qv ν := Zv_le_Qv_nu hs hdν hz
  have hzst : z ∈ stab α' := Zv_le_stab_crit hA hs hc hz
  obtain ⟨hz', hsw, -⟩ := smul_swap_of_crit hA hs h29 hdν hz hzQ
  have hlν : Zv a₂ ≤ Subgroup.normalizer (Zv ν : Set G) := by
    have h1 := dist_le_of_mem_nbrs hA (x := a₂) hν
    have h2 : dist a₂ α' = 1 := by
      rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr h29.n₂
    have := hs.b1
    exact (hs.Zv_le_stab_of_dist_le_false hA hlv (by omega)).trans (stab_le_normalizer_Zv hA ν)
  intro r hr
  have hr' : r ∈ Vn α' := (hRV hr).2
  have hrz : r * z = z * r := isElemAbelian_comm hVab (hRV hr).1 (Zv_le_Vn (nbrs_symm hβ) hz)
  rw [← hVeq] at hr'
  obtain ⟨c, hcν, u, hu, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hlν).mp hr'
  have hcz : c * z = z * c :=
    (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA ν hcν).2 z hzν).symm
  have huz : u * z = z * u := by
    have e : c * u * z = z * (c * u) := hrz
    have e2 : c * (u * z) = c * (z * u) := by
      calc c * (u * z) = c * u * z := by group
        _ = z * (c * u) := e
        _ = (z * c) * u := by group
        _ = c * (z * u) := by rw [← hcz]; group
    exact mul_left_cancel e2
  set U : Subgroup G := Zv a₂ ⊓ Subgroup.centralizer ({z} : Set G) with hU
  have huU : u ∈ U := ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr huz⟩
  have hUY : U ≤ Yv α' := by
    refine hs.le_Yv_of_normalizes hA h26 hα'v h29.n₂ inf_le_left hzst ?_ ?_
    · intro h
      exact h29.ne₂₃ (hsw.symm.trans h).symm
    · exact conjSub_eq_of_commute fun v hv =>
        (Subgroup.mem_centralizer_singleton_iff.mp hv.2).symm
  exact (Zv ν).mul_mem hcν (Yv_le_Zv hν (hUY huU))

end Core

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem bMin_ne_five_of_caseS (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (h4 : Nat.card (Vn β) = 2 ^ 6) : bMin H M ≠ 5 := by
  intro h5
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  obtain ⟨α', hc⟩ := hs.exists_crit_partner hA
  have hα'v := Core.vtype_crit hA hs ho hc
  obtain ⟨β₁, hβ₁, hd₁⟩ := Core.exists_nbr_dist hA (x := α') (y := α) (n := 4)
    (by rw [CosetGeom.dist_comm, hc.2, h5])
  obtain ⟨γ, hγ, hd₂⟩ := Core.exists_nbr_dist hA (x := α') (y := β₁) (n := 3) hd₁
  obtain ⟨κ, hκ, hd₃⟩ := Core.exists_nbr_dist hA (x := α') (y := γ) (n := 2) hd₂
  obtain ⟨ν, hνκ, hd₄⟩ := Core.exists_nbr_dist hA (x := α') (y := κ) (n := 1) hd₃
  have hν : ν ∈ nbrs α' := dist_eq_one_iff_adj.mp hd₄
  have e₁ : dist α β₁ = 1 := dist_eq_one_iff_adj.mpr hβ₁
  have e₂ : dist β₁ γ = 1 := dist_eq_one_iff_adj.mpr hγ
  have e₃ : dist γ κ = 1 := dist_eq_one_iff_adj.mpr hκ
  have e₄ : dist κ ν = 1 := dist_eq_one_iff_adj.mpr hνκ
  have hαα' : dist α α' = 5 := by rw [hc.2, h5]
  have t₁ := dist_triangle hA.amalgam.gen α β₁ γ
  have t₂ := dist_triangle hA.amalgam.gen α γ κ
  have t₃ := dist_triangle hA.amalgam.gen α κ ν
  have t₄ := dist_triangle hA.amalgam.gen α γ α'
  have t₅ := dist_triangle hA.amalgam.gen α κ α'
  have t₆ := dist_triangle hA.amalgam.gen α ν α'
  have s₂ : dist γ α' = 3 := by rw [CosetGeom.dist_comm]; exact hd₂
  have s₃ : dist κ α' = 2 := by rw [CosetGeom.dist_comm]; exact hd₃
  have s₁ : dist β₁ α' = 4 := by rw [CosetGeom.dist_comm]; exact hd₁
  have s₄ : dist ν α' = 1 := by rw [CosetGeom.dist_comm]; exact hd₄
  have dγ : dist α γ = 2 := by omega
  have dκ : dist α κ = 3 := by omega
  have dν : dist α ν = 4 := by omega
  have hβ₁v := Core.vtype_beta hs hβ₁
  have hS : ∀ δ : Geo H M, vtype δ = true → Nat.card (Vn δ) = 2 ^ 6 := fun δ hδ => by
    rw [card_Vn_eq hδ hβv]; exact h4
  have hdβ₁ : dist β₁ α' + 1 = bMin H M := by omega
  have hcrit := Core.isCritPair₃_crit hA hs ho hc hβ₁ hdβ₁
  have hRγ := Core.comm_Vn_le_Zv_gamma hA h26 hs ho hb hc hβ₁ hdβ₁ hγ (by omega)
    (hS β₁ hβ₁v)
  have hRν := Core.comm_Vn_le_Zv_nu hA h26 hs ho hb hc hβ₁ hdβ₁ hν (by omega) (hS α' hα'v)
  have hκv : vtype κ = true := Core.vtype_of_odd hA hs (by rw [dκ]; decide)
  have hγν : γ ≠ ν := by
    intro h
    rw [h] at dγ
    omega
  have hY := hs.inf_Zv_eq_Yv hA h26 hκv (nbrs_symm hκ) hνκ hγν
  have hcard := Subgroup.card_le_of_le (hY ▸ le_inf hRγ hRν)
  rw [hs.card_Yv hA h26 hκv] at hcard
  have h8 := Core.card_comm_Vn_ge hA h26 hs ho hb hcrit
  omega

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
