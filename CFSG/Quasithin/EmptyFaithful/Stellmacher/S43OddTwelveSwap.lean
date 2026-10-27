module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveGeo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Twelve

variable {G : Type} [Group G]

theorem comm_φ_eq {X S Z : Subgroup G} (D : Dict5 X S Z) {a : G}
    (ha : a ∈ X) (w : orth.W) : ⁅a, D.φ w⁆ = D.φ (orth.act (D.ψ ⟨a, ha⟩) w * w⁻¹) := by
  rw [map_mul, map_inv, D.act_eq ⟨a, ha⟩ w, commutatorElement_def]

theorem comm_φ_eq' {X S Z : Subgroup G} (D : Dict5 X S Z) {x : G}
    (hx : x ∈ X) (w : orth.W) : ⁅D.φ w, x⁆ = D.φ (w * (orth.act (D.ψ ⟨x, hx⟩) w)⁻¹) := by
  rw [map_mul, map_inv, D.act_eq ⟨x, hx⟩ w, commutatorElement_def]
  group

variable [Finite G] {H M S : Subgroup G} {α : Geo H M} {α' ν β l : Geo H M}

theorem Data.mem_Qv_of_commute (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) (d : Data α α' ν β l) {z : G} (hz : z ∈ Zv α)
    (hzQ : z ∉ Qv α') {x : G} (hx : x ∈ Vn α') (hzx : z * x = x * z) : x ∈ Qv α := by
  obtain ⟨hα'v, -, -⟩ := d.vtypes hA hs ho
  obtain ⟨l₁, l₂, h29⟩ := Core.exists_sit29_nu hA h26 hs ho d.crit d.hν
  have hV : IsElemAbelian 2 (Vn α') := Sit43.isElemAbelian_Vn_of_three hA hb α'
  have hcV : ∀ a ∈ Vn α', ∀ b ∈ Vn α', a * b = b * a := fun a ha b hb' =>
    comm_of_elemAbelian hV ha hb'
  have h0 : Zv ν ≤ Vn α' := Core.Zv_le_Vn h29.n₁
  have h1 : Zv l₁ ≤ Vn α' := Core.Zv_le_Vn h29.n₂
  have h2 : Zv l₂ ≤ Vn α' := Core.Zv_le_Vn h29.n₃
  have hVle : Vn α' ≤ (Zv ν ⊔ Zv l₁) ⊔ Zv l₂ := by
    refine iSup₂_le fun μ hμ => ?_
    rcases h29.nbrs_eq μ hμ with h | h | h <;> subst h
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have hn1 : Zv l₂ ≤ Subgroup.normalizer ((Zv ν ⊔ Zv l₁ : Subgroup G) : Set G) :=
    h2.trans (le_normalizer_of_comm hcV (sup_le h0 h1))
  have hn0 : Zv l₁ ≤ Subgroup.normalizer (Zv ν : Set G) :=
    h1.trans (le_normalizer_of_comm hcV h0)
  obtain ⟨y, hy, v', hv', rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hn1).mp (hVle hx)
  obtain ⟨a, ha, v, hv, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hn0).mp hy
  obtain ⟨hc1, hc2⟩ := Core.conj_swap_of_crit hA hs h29 d.dν hz hzQ
  have hp : z * v * z⁻¹ ∈ Zv l₂ := by
    rw [← hc1, mem_conjSub]
    simpa [mul_assoc] using hv
  have hp' : z * v' * z⁻¹ ∈ Zv l₁ := by
    rw [← hc2, mem_conjSub]
    simpa [mul_assoc] using hv'
  have hza : z * a * z⁻¹ = a := by
    have h3 := Subgroup.mem_centralizer_iff.mp
      (Qv_le_centralizer_Zv hA ν (Core.Zv_le_Qv_nu hs d.dν hz)) a ha
    rw [← h3]
    group
  have hvv : z * (v * v') * z⁻¹ = v * v' := by
    have e1 : z * (a * v * v') * z⁻¹ = a * v * v' := by
      rw [hzx]
      group
    calc z * (v * v') * z⁻¹ = (z * a * z⁻¹)⁻¹ * (z * (a * v * v') * z⁻¹) := by group
      _ = a⁻¹ * (a * v * v') := by rw [hza, e1]
      _ = v * v' := by group
  have hy₀ : (z * v * z⁻¹)⁻¹ * v' = (z * v' * z⁻¹) * v⁻¹ := by
    calc (z * v * z⁻¹)⁻¹ * v' = (z * v * z⁻¹)⁻¹ * (v' * v) * v⁻¹ := by group
      _ = (z * v * z⁻¹)⁻¹ * (v * v') * v⁻¹ := by rw [hcV v' (h2 hv') v (h1 hv)]
      _ = (z * v * z⁻¹)⁻¹ * (z * (v * v') * z⁻¹) * v⁻¹ := by rw [hvv]
      _ = (z * v' * z⁻¹) * v⁻¹ := by group
  have hYm : (z * v * z⁻¹)⁻¹ * v' ∈ Yv α' := by
    rw [← hs.inf_Zv_eq_Yv hA h26 hα'v h29.n₂ h29.n₃ h29.ne₂₃]
    refine ⟨?_, (Zv l₂).mul_mem ((Zv l₂).inv_mem hp) hv'⟩
    rw [hy₀]
    exact (Zv l₁).mul_mem hp' ((Zv l₁).inv_mem hv)
  have hvinv : v⁻¹ = v := by
    have := (isElemAbelian_Zv hA l₁).2 v hv
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact this)
  have hvβ : v ∈ stab β :=
    Core.Zv_le_stab_beta hA hs ho d.crit (d.dist_beta hA) h29.n₂ hv
  have hzV : z ∈ Vn β := Sit43.Zv_le_Vn d.hβ hz
  have hvz : v * z * v⁻¹ ∈ Vn β :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β hvβ) z).mp hzV
  have hVQ : Vn β ≤ Qv α := hs.Vn_le_Qv_of_nbr hA h26 hb hs.vα d.hβ
  have e : a * v * v' = a * ((v * z * v⁻¹) * z⁻¹) * ((z * v * z⁻¹)⁻¹ * v') := by
    calc a * v * v' = a * (v * (z * v * z⁻¹)) * ((z * v * z⁻¹)⁻¹ * v') := by group
      _ = a * ((v * z * v⁻¹) * z⁻¹) * ((z * v * z⁻¹)⁻¹ * v') := by
          congr 2
          conv_rhs => rw [hvinv]
          group
  rw [e]
  refine (Qv α).mul_mem ((Qv α).mul_mem (Core.Zv_nu_le_Qv hA hs ho d.crit d.hν d.dν ha)
    (hVQ ((Vn β).mul_mem hvz ((Vn β).inv_mem hzV)))) ?_
  exact Core.Yv_le_Qv hA hs ho d.crit d.hν d.dν hYm

theorem Data.commute_of_swap (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) (d : Data α α' ν β l)
    (D : Dict5 (stab α) (stab α ⊓ stab β) (Zv α)) {u : G} (hu : u ∈ Zv l ⊓ Qv β)
    (huQ : u ∉ Qv α) (hsw : (D.ψ ⟨u, d.Qv_beta_le hA hu.2⟩).IsSwap) {z : G}
    (hz : z ∈ Zv α ⊓ Qv α') : z * u = u * z := by
  have hC := (D.relIndex_centralizer_eq_two_iff ⟨u, d.Qv_beta_le hA hu.2⟩).mpr hsw
  have hQ := Core.relIndex_Zv_inf_Qv_crit hA hs ho d.crit d.hν d.dν
  have hle : Zv α ⊓ Subgroup.centralizer ({u} : Set G) ≤ Zv α ⊓ Qv α' := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    by_contra hyQ
    have hyu : y * u = u * y := (Subgroup.mem_centralizer_iff.mp hy.2 u rfl).symm
    exact huQ (d.mem_Qv_of_commute hA h26 hs ho hb hy.1 hyQ (Core.Zv_le_Vn d.hl hu.1) hyu)
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_left
  rw [show ((Zv α ⊓ Subgroup.centralizer ({u} : Set G)).relIndex (Zv α)) = 2 from hC, hQ] at hmul
  have h1 : (Zv α ⊓ Subgroup.centralizer ({u} : Set G)).relIndex (Zv α ⊓ Qv α') = 1 := by
    omega
  have := Subgroup.relIndex_eq_one.mp h1 hz
  exact (Subgroup.mem_centralizer_iff.mp this.2 u rfl).symm

theorem Data.commute_of_swap' (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) (d : Data α α' ν β l)
    (D : Dict5 (stab α) (stab α ⊓ stab β) (Zv α)) {u : G} (hu : u ∈ Zv l ⊓ Qv β)
    (huQ : u ∉ Qv α) (hsw : (D.ψ ⟨u, d.Qv_beta_le hA hu.2⟩).IsSwap) {z : G}
    (hz : z ∈ Zv α ⊓ Qv α') {v : G} (hv : v ∈ Zv l ⊓ Qv β) : z * v = v * z := by
  have hzc := Qv_le_centralizer_Zv hA ν (Core.Zv_le_Qv_nu hs d.dν hz.1)
  by_cases hvQ : v ∈ Qv α
  · have hvY : v ∈ Yv α' := d.Zv_inf_Qv_le_Yv hA h26 hs ho ⟨hv.1, hvQ⟩
    exact (Subgroup.mem_centralizer_iff.mp hzc v (Yv_le_Zv d.hν hvY)).symm
  · have hy := d.inv_mul_mem_Yv hA h26 hs ho hb hu huQ hv hvQ
    have h1 := d.commute_of_swap hA h26 hs ho hb D hu huQ hsw hz
    have h2 : z * (u⁻¹ * v) = (u⁻¹ * v) * z :=
      (Subgroup.mem_centralizer_iff.mp hzc _ (Yv_le_Zv d.hν hy)).symm
    calc z * v = (z * u) * (u⁻¹ * v) := by group
      _ = u * (z * (u⁻¹ * v)) := by rw [h1]; group
      _ = u * ((u⁻¹ * v) * z) := by rw [h2]
      _ = v * z := by group

theorem Data.exists_z₁ (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) (d : Data α α' ν β l) :
    ∃ z₁ ∈ Zv α ⊓ Qv α', ∃ v₀ ∈ Zv l, ⁅v₀, z₁⁆ ≠ 1 := by
  have h := (crit4d hA h26 hs ho hb d.crit d.hν d.dν d.hβ d.dβ d.hl d.lν).1
  by_contra hcon
  push Not at hcon
  apply h
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro v hv z hz
  rw [hcon z hz v hv]
  exact Subgroup.one_mem _

theorem Data.ψ_isSwap (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 4 ≤ bMin H M) (d : Data α α' ν β l)
    (D : Dict5 (stab α) (stab α ⊓ stab β) (Zv α)) {u : G} (hu : u ∈ Zv l ⊓ Qv β)
    (huQ : u ∉ Qv α) (hsw : (D.ψ ⟨u, d.Qv_beta_le hA hu.2⟩).IsSwap)
    (D' : Dict5 (stab l) (stab l ⊓ stab α') (Zv l)) {z₁ : G} (hz₁ : z₁ ∈ Zv α ⊓ Qv α')
    {v₀ : G} (hv₀ : v₀ ∈ Zv l) (hne : ⁅v₀, z₁⁆ ≠ 1) :
    (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩).IsSwap := by
  refine (D'.relIndex_centralizer_eq_two_iff _).mp ?_
  have hle : Zv l ⊓ Qv β ≤ Zv l ⊓ Subgroup.centralizer ({z₁} : Set G) := fun v hv =>
    ⟨hv.1, Subgroup.mem_centralizer_iff.mpr fun g hg => by
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact d.commute_of_swap' hA h26 hs ho (by omega) D hu huQ hsw hz₁ hv⟩
  have h3 : (Zv l ⊓ Subgroup.centralizer ({z₁} : Set G)).relIndex (Zv l) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite).trans
      (d.relIndex_le_two hA hs ho hb)
  have h4 : (Zv l ⊓ Subgroup.centralizer ({z₁} : Set G)).relIndex (Zv l) ≠ 1 := by
    intro h1
    apply hne
    have := Subgroup.relIndex_eq_one.mp h1 hv₀
    have hc : z₁ * v₀ = v₀ * z₁ := Subgroup.mem_centralizer_iff.mp this.2 z₁ rfl
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hc.symm
  have h5 : 0 < (Zv l ⊓ Subgroup.centralizer ({z₁} : Set G)).relIndex (Zv l) :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  show (Zv l ⊓ Subgroup.centralizer ({z₁} : Set G)).relIndex (Zv l) = 2
  omega

end Twelve

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
