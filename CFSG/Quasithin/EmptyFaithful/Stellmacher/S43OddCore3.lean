module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCoreData
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCoreMod
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseC2

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

omit [Finite G] in
theorem conjSub_eq_of_commute {z : G} {U : Subgroup G} (h : ∀ u ∈ U, z * u = u * z) :
    conjSub z U = U := by
  refine conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ ?_)
  rw [Subgroup.mem_centralizer_iff]
  exact fun u hu => (h u hu).symm

theorem mem_Qv_of_commute (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) {α' ν : Geo H M} (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hdν : dist α ν + 1 = bMin H M) (hV : Vn α' ≤ stab α) {z x : G} (hz : z ∈ Zv α)
    (hzQ : z ∉ Qv α') (hx : x ∈ Vn α') (hxz : z * x = x * z) : x ∈ Qv α := by
  obtain ⟨l, l', h29⟩ := exists_sit29_nu hA h26 hs ho hc hν
  have hα'v := vtype_crit hA hs ho hc
  have hzν : z ∈ Qv ν := Zv_le_Qv_nu hs hdν hz
  have hzst : z ∈ stab α' := Zv_le_stab_crit hA hs hc hz
  obtain ⟨hz', hsw, -⟩ := smul_swap_of_crit hA hs h29 hdν hz hzQ
  have hconj := (conj_swap_of_crit hA hs h29 hdν hz hzQ).1
  have hνα : Zv ν ≤ Qv α := Zv_nu_le_Qv hA hs ho hc hν hdν
  have hlα : Zv l ≤ stab α := (Zv_le_Vn h29.n₂).trans hV
  have hnα : stab α ≤ Subgroup.normalizer (Zv α : Set G) := stab_le_normalizer_Zv hA α
  have hK : Zv ν ⊔ Zv l ≤ Subgroup.normalizer (Zv α : Set G) :=
    (sup_le (hνα.trans (pCoreOf_le 2 _)) hlα).trans hnα
  have hlν : Zv l ≤ Subgroup.normalizer (Zv ν : Set G) := by
    have hlv : vtype l = false := vtype_nu hA hs ho hc h29.n₂
    have hd : dist l ν ≤ bMin H M := by
      have h1 := dist_le_of_mem_nbrs hA (x := l) hν
      have h2 : dist l α' = 1 := by
        rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr h29.n₂
      have := hs.b1
      omega
    exact (hs.Zv_le_stab_of_dist_le_false hA hlv hd).trans (stab_le_normalizer_Zv hA ν)
  have hcover : Vn α' ≤ Zv α ⊔ (Zv ν ⊔ Zv l) := by
    refine iSup₂_le fun w hw => ?_
    rcases h29.nbrs_eq w hw with rfl | rfl | rfl
    · exact le_sup_of_le_right le_sup_left
    · exact le_sup_of_le_right le_sup_right
    · intro g hg
      rw [← hconj, mem_conjSub] at hg
      set u := z⁻¹ * g * z with hu
      have huα : u ∈ stab α := hlα hg
      have h1 : u * z⁻¹ * u⁻¹ ∈ Zv α :=
        (Subgroup.mem_normalizer_iff.mp (hnα huα) z⁻¹).mp ((Zv α).inv_mem hz)
      have e : g = (z * (u * z⁻¹ * u⁻¹)) * u := by rw [hu]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((Zv α).mul_mem hz h1))
        (Subgroup.mem_sup_right (Subgroup.mem_sup_right hg))
  obtain ⟨t, ht, y, hy, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hK).mp (hcover hx)
  obtain ⟨a, ha, u, hu, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hlν).mp hy
  have hzt : z * t = t * z := isElemAbelian_comm (isElemAbelian_Zv hA α) hz ht
  have hza : z * a = a * z :=
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA ν ha).2 z hzν
  have hzu : z * u = u * z := by
    have e1 : z * (t * (a * u)) = t * a * (z * u) := by
      calc z * (t * (a * u)) = (z * t) * a * u := by group
        _ = t * (z * a) * u := by rw [hzt]; group
        _ = t * (a * z) * u := by rw [hza]
        _ = t * a * (z * u) := by group
    have e2 : t * (a * u) * z = t * a * (u * z) := by group
    rw [e1, e2] at hxz
    exact mul_left_cancel hxz
  set U : Subgroup G := Zv l ⊓ Subgroup.centralizer ({z} : Set G) with hUdef
  have huU : u ∈ U := ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr hzu.symm⟩
  have hUY : U ≤ Yv α' := by
    refine hs.le_Yv_of_normalizes hA h26 hα'v h29.n₂ inf_le_left hzst ?_ ?_
    · intro h
      exact h29.ne₂₃ (hsw.symm.trans h).symm
    · exact conjSub_eq_of_commute fun v hv =>
        (Subgroup.mem_centralizer_singleton_iff.mp hv.2).symm
  have huQ : u ∈ Qv α := hνα (Yv_le_Zv hν (hUY huU))
  exact Subgroup.mul_mem _ (Zv_le_Qv hA α ht) (Subgroup.mul_mem _ (hνα ha) huQ)

theorem not_Vn_le_Qv_crit (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {α' β : Geo H M} (hc : IsCritPair₁ α α')
    (hβ : β ∈ nbrs α) (hdβ : dist β α' + 1 = bMin H M) : ¬ Vn α' ≤ Qv β := by
  intro hV
  obtain ⟨ν, hν, hdν, -⟩ := exists_nu hA hs hc hβ hdβ
  have hα'v := vtype_crit hA hs ho hc
  have hVα : Vn α' ≤ stab α := hV.trans (Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ))
  have hVS : Vn α' ≤ stab α ⊓ stab β := le_inf hVα (hV.trans (pCoreOf_le 2 _))
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  have hVab : IsElemAbelian 2 (Vn α') := isElemAbelian_Vn hA hb α'
  have hZα' : Zv α ≤ stab α' := Zv_le_stab_crit hA hs hc
  obtain ⟨z₀, hz₀, hz₀Q⟩ : ∃ z ∈ Zv α, z ∉ Qv α' := by
    by_contra hcon
    push Not at hcon
    exact hc.1 fun x hx => hcon x hx
  have hAS : D.bar (Vn α') ≤ S5Syl := by
    intro σ hσ
    obtain ⟨x, hx, rfl⟩ := (D.mem_bar_iff σ).mp hσ
    exact (D.mem_S_iff x).mp (hVS hx)
  have hquad : ∀ a ∈ D.bar (Vn α'), ∀ b ∈ D.bar (Vn α'), ∀ w : orth.W,
      orth.act a (orth.act b w * w⁻¹) = orth.act b w * w⁻¹ := by
    intro a ha b hb w
    obtain ⟨x, hx, rfl⟩ := (D.mem_bar_iff a).mp ha
    obtain ⟨y, hy, rfl⟩ := (D.mem_bar_iff b).mp hb
    apply D.inj
    rw [D.act_eq x, map_mul, map_inv, D.act_eq y]
    have hc' : (y : G) * D.φ w * (y : G)⁻¹ * (D.φ w)⁻¹ ∈ Vn α' := by
      have h1 : D.φ w * (y : G)⁻¹ * (D.φ w)⁻¹ ∈ Vn α' :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn α' (hZα' (D.φ_mem w))) _).mp
          ((Vn α').inv_mem hy)
      have e : (y : G) * D.φ w * (y : G)⁻¹ * (D.φ w)⁻¹ =
          (y : G) * (D.φ w * (y : G)⁻¹ * (D.φ w)⁻¹) := by group
      rw [e]
      exact (Vn α').mul_mem hy h1
    rw [isElemAbelian_comm hVab hx hc']
    group
  have hcard : 4 ≤ Nat.card (D.bar (Vn α')) := by
    obtain ⟨l, l', h29⟩ := exists_sit29_nu hA h26 hs ho hc hν
    obtain ⟨hz', hsw, -⟩ := smul_swap_of_crit hA hs h29 hdν hz₀ hz₀Q
    have hlα : Zv l ≤ stab α := (Zv_le_Vn h29.n₂).trans hVα
    have hUY : Qv α ⊓ Zv l ≤ Yv α' := by
      refine hs.le_Yv_of_normalizes hA h26 hα'v h29.n₂ inf_le_right (hZα' hz₀) ?_ ?_
      · intro h
        exact h29.ne₂₃ (hsw.symm.trans h).symm
      · exact conjSub_eq_of_commute fun v hv =>
          (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hz₀).2 v hv.1).symm
    have h4 := hs.four_le_relIndex hA h26 hα'v h29.n₂ inf_le_right hUY
    have hle : D.bar (Zv l) ≤ D.bar (Vn α') := by
      unfold Dict5.bar
      exact Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr (Zv_le_Vn h29.n₂ (Subgroup.mem_subgroupOf.mp hx))
    calc 4 ≤ (Qv α ⊓ Zv l).relIndex (Zv l) := h4
      _ = Nat.card (D.bar (Zv l)) := (D.card_bar hlα).symm
      _ ≤ Nat.card (D.bar (Vn α')) := Subgroup.card_le_of_le hle
  obtain ⟨h02, h13⟩ := swap_mem_of_quadratic _ hAS hquad hcard
  obtain ⟨x₁, hx₁, hψ₁⟩ := (D.mem_bar_iff _).mp h02
  obtain ⟨x₂, hx₂, hψ₂⟩ := (D.mem_bar_iff _).mp h13
  obtain ⟨w, rfl⟩ : z₀ ∈ D.φ.range := D.range_eq.ge hz₀
  obtain ⟨w₁, w₂, hw₁, hw₂, rfl⟩ := exists_fix_mul_fix w
  have key : ∀ (x : ↥(stab α)) (u : orth.W) (σ : Equiv.Perm (Fin 5)), (x : G) ∈ Vn α' →
      D.ψ x = σ → σ ≠ 1 → orth.act σ u = u → D.φ u ∉ Qv α' → False := by
    intro x u σ hx hψ hσ hu huQ
    have hcomm : D.φ u * (x : G) = (x : G) * D.φ u := by
      have h1 := D.act_eq x u
      rw [hψ, hu] at h1
      calc D.φ u * (x : G) = ((x : G) * D.φ u * (x : G)⁻¹) * x := by rw [← h1]
        _ = (x : G) * D.φ u := by group
    have hxQ := mem_Qv_of_commute hA h26 hs ho hc hν hdν hVα (D.φ_mem u) huQ hx hcomm
    exact hσ (hψ.symm.trans ((D.ker_iff x).mpr hxQ))
  rw [map_mul] at hz₀Q
  by_cases h1 : D.φ w₁ ∈ Qv α'
  · exact key x₂ w₂ _ hx₂ hψ₂ swap_ne_one.2 hw₂ fun h2 => hz₀Q ((Qv α').mul_mem h1 h2)
  · exact key x₁ w₁ _ hx₁ hψ₁ swap_ne_one.1 hw₁ h1

end Core

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem crit3_symm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {δ δ' : Geo H M} (h : IsCritPair₃ δ δ') :
    IsCritPair₃ δ' δ := by
  obtain ⟨l, hl, hlv, hc⟩ := Core.exists_crit_of_crit3 hA hs h
  obtain ⟨hδ, hδ', hd, -⟩ := h
  refine ⟨hδ', hδ, by rw [CosetGeom.dist_comm]; exact hd, ?_⟩
  exact Core.not_Vn_le_Qv_crit hA h26 (hs.of_vtype_false hlv) ho hb hc (nbrs_symm hl) hd

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
