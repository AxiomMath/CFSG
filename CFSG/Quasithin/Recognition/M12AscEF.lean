module

public import CFSG.Quasithin.Recognition.M12AscModel
public import CFSG.Quasithin.Recognition.M12AscStrong

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G] {z : G}

open CFSG.GH74.M12 (Asc03Hyp)

namespace AscModel

variable (m : AscModel z)

include m

theorem Qg_normalizes_F [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z)
    (hEF : ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom = m.fSub)
    {q : G} (hq : q ∈ (ascQ z).map (MulAut.conj g).toMonoidHom) {f : G} (hf : f ∈ m.fSub) :
    q * f * q⁻¹ ∈ m.fSub := by
  have hEg := (extraspecialAt_ascQ hyp).conj g
  have hsF := m.conj_mem_fSub hyp hgz hsQ
  have hfQg : f ∈ (ascQ z).map (MulAut.conj g).toMonoidHom := by
    rw [← hEF] at hf; exact hf.2
  rcases hEg.comm_mem q hq f hfQg with h | h
  · have : q * f * q⁻¹ = f := by
      calc q * f * q⁻¹ = (q * f * q⁻¹ * f⁻¹) * f := by group
        _ = f := by rw [h, one_mul]
    rw [this]; exact hf
  · have : q * f * q⁻¹ = (g * z * g⁻¹) * f := by
      calc q * f * q⁻¹ = (q * f * q⁻¹ * f⁻¹) * f := by group
        _ = _ := by rw [h]
    rw [this]; exact mul_mem hsF hf

theorem mem_normalizer_fSub {h : G} (hh : h ∈ ascH z) :
    h ∈ Subgroup.normalizer (m.fSub : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro f
  refine ⟨fun hf => m.fSub_normal hh hf, fun hf => ?_⟩
  have := m.fSub_normal (inv_mem hh) hf
  rwa [show h⁻¹ * (h * f * h⁻¹) * h⁻¹⁻¹ = f by group] at this

theorem exists_conj_mem_tSub [Finite G] (hyp : Asc03Hyp G z) {N : Subgroup G} (hTN : m.tSub ≤ N)
    {y : G} (hyN : y ∈ N) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ c ∈ N, c * y * c⁻¹ ∈ m.tSub := by
  classical
  have hmapcard : ∀ W : Subgroup N, Nat.card (W.map N.subtype) = Nat.card W := fun W =>
    (Nat.card_congr (Subgroup.equivMapOfInjective W N.subtype N.subtype_injective)).symm
  have hT'card : Nat.card (m.tSub.subgroupOf N) = 64 := by
    rw [← m.card_tSub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  let P : Sylow 2 N :=
    { toSubgroup := m.tSub.subgroupOf N
      isPGroup' := IsPGroup.of_card (n := 6) (by rw [hT'card]; norm_num)
      is_maximal' := by
        intro Q hQ hle
        have hQp : IsPGroup 2 (Q.map N.subtype) := by
          obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ
          refine (IsPGroup.iff_card).2 ⟨n, ?_⟩
          rw [hmapcard, hn]
        have hle' : m.tSub ≤ Q.map N.subtype := by
          intro t ht
          exact ⟨⟨t, hTN ht⟩, hle (Subgroup.mem_subgroupOf.2 ht), rfl⟩
        have := m.le_tSub_of_isPGroup hyp hQp hle'
        refine le_antisymm (fun x hx => ?_) hle
        exact Subgroup.mem_subgroupOf.2 (this ⟨x, hx, rfl⟩) }
  set yN : N := ⟨y, hyN⟩ with hyN'
  have hyN2 : yN ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hy2)
  have hyNne : yN ≠ 1 := fun e => hy1 (congrArg Subtype.val e)
  have hyp2 : IsPGroup 2 (Subgroup.zpowers yN) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hyN2 hyNne]; simp
  obtain ⟨S1, hS1⟩ := hyp2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N P S1
  have hmem : yN ∈ ((c • P : Sylow 2 N) : Subgroup N) := by
    rw [hc]; exact hS1 (Subgroup.mem_zpowers yN)
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hmem
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.1 hmem
  have hwy' : (c : G) * (w : G) * (c : G)⁻¹ = y := by
    simpa [MulAut.conj_apply, hyN'] using congrArg Subtype.val hwy
  have hwT : (w : G) ∈ m.tSub := Subgroup.mem_subgroupOf.1 hw
  refine ⟨((c⁻¹ : N) : G), (c⁻¹).2, ?_⟩
  have : ((c⁻¹ : N) : G) * y * ((c⁻¹ : N) : G)⁻¹ = (w : G) := by
    rw [← hwy']
    simp only [Subgroup.coe_inv]
    group
  rw [this]
  exact hwT

theorem E_ne_fSub [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) {g : G}
    (hgz : g * z * g⁻¹ ≠ z) (hsQ : g * z * g⁻¹ ∈ ascQ z) :
    ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom ≠ m.fSub := by
  intro hEF
  set s := g * z * g⁻¹ with hs
  have hz2 : z * z = 1 := asc_z_sq hyp
  have hz1 : z ≠ 1 := asc_z_ne_one hyp
  have hEg := (extraspecialAt_ascQ hyp).conj g
  have hsF : s ∈ m.fSub := m.conj_mem_fSub hyp hgz hsQ
  have hs1 : s ≠ 1 := asc_conj_ne_one hyp g
  obtain ⟨hzQ', -, -, -, -⟩ := config_of_conj hyp hgz hsQ
  have hzQg : z ∈ (ascQ z).map (MulAut.conj g).toMonoidHom := (mem_map_conj_iff _ g z).2 hzQ'
  have hmoves : ∃ q' ∈ (ascQ z).map (MulAut.conj g).toMonoidHom, q' * z * q'⁻¹ = s * z := by
    by_contra hno
    push Not at hno
    have hcen : z = 1 ∨ z = s := by
      refine hEg.center_le z hzQg (fun y hy => ?_)
      by_contra hne
      apply hno y hy
      rcases hEg.comm_mem y hy z hzQg with h | h
      · exfalso
        apply hne
        calc z * y = (y * z * y⁻¹ * z⁻¹)⁻¹ * (y * z) := by group
          _ = y * z := by rw [h]; group
      · calc y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
          _ = s * z := by rw [h]
    rcases hcen with h | h
    · exact hz1 h
    · exact hgz h.symm
  obtain ⟨q', hq', hq'z⟩ := hmoves
  set N := Subgroup.normalizer (m.fSub : Set G) with hN
  have hHN : ∀ h : G, h ∈ ascH z → h ∈ N := fun h hh => m.mem_normalizer_fSub hh
  have hq'N : q' ∈ N := by
    rw [hN, Subgroup.mem_normalizer_iff]
    intro f
    refine ⟨fun hf => m.Qg_normalizes_F hyp hgz hsQ hEF hq' hf, fun hf => ?_⟩
    have := m.Qg_normalizes_F hyp hgz hsQ hEF (Subgroup.inv_mem _ hq') hf
    rwa [show q'⁻¹ * (q' * f * q'⁻¹) * q'⁻¹⁻¹ = f by group] at this
  have htrans : ∀ e ∈ m.fSub, e ≠ 1 → ∃ n ∈ N, n * z * n⁻¹ = e := by
    intro e he he1
    by_cases hez : e = z
    · exact ⟨1, one_mem _, by rw [hez]; group⟩
    · have hsz1F : s * z ∈ m.fSub := mul_mem hsF m.z_mem_fSub
      have hne1 : s * z ≠ 1 := by
        intro h
        apply hgz
        rw [eq_inv_of_mul_eq_one_left h]
        exact inv_eq_of_mul_eq_one_right hz2
      have hnez : s * z ≠ z := by
        intro h
        apply hs1
        simpa using h
      obtain ⟨h, hhH, hh⟩ := m.fSub_orbit hsz1F hne1 hnez he he1 hez
      refine ⟨h * q', mul_mem (hHN h hhH) hq'N, ?_⟩
      calc h * q' * z * (h * q')⁻¹ = h * (q' * z * q'⁻¹) * h⁻¹ := by group
        _ = h * (s * z) * h⁻¹ := by rw [hq'z]
        _ = e := by rw [hh]; group
  have hFH : ∀ h : G, h * z = z * h → h ∈ N := fun h hc =>
    hHN h (Subgroup.mem_centralizer_singleton_iff.2 hc)
  have hTN : m.tSub ≤ N := fun t ht => hHN t (m.tSub_le_ascH ht)
  have hsc : ∀ x : G, x * z * x⁻¹ ∈ N → x * z * x⁻¹ ∈ m.fSub := by
    intro x hx
    set y := x * z * x⁻¹ with hy
    have hy2 : y * y = 1 := asc_conj_sq hyp x
    have hy1 : y ≠ 1 := asc_conj_ne_one hyp x
    obtain ⟨c, hcN, hcT⟩ := m.exists_conj_mem_tSub hyp hTN hx hy2 hy1
    set y' := c * y * c⁻¹ with hy'
    have hy'2 : y' * y' = 1 := by
      calc y' * y' = c * (y * y) * c⁻¹ := by rw [hy']; group
        _ = 1 := by rw [hy2]; group
    have hy'1 : y' ≠ 1 := by
      intro e
      apply hy1
      calc y = c⁻¹ * y' * c := by rw [hy']; group
        _ = 1 := by rw [e]; group
    have hy'conj : ∃ k : G, k * z * k⁻¹ = y' := ⟨c * x, by rw [hy', hy]; group⟩
    have hy'H : y' ∈ ascH z := m.tSub_le_ascH hcT
    have hy'F : y' ∈ m.fSub := by
      by_cases hy'Q : y' ∈ ascQ z
      · exact (m.conj_mem_Q_iff hyp hy'Q hy'1).1 hy'conj
      · exfalso
        obtain ⟨-, -, -, -, v₀, hv₀, hv₀o, hv₀Q⟩ := config_of_conj hyp hgz hsQ
        have hv₀2 : v₀ * v₀ = 1 := by
          have := pow_orderOf_eq_one v₀
          rwa [hv₀o, pow_two] at this
        obtain ⟨h, hhH, hhv⟩ := m.outInv_orbit_G hyp hv₀.1 hv₀Q hv₀2 hy'H hy'Q hy'2
        obtain ⟨w, hwN, hws⟩ := htrans s hsF hs1
        have hwg : w⁻¹ * g ∈ ascH z := by
          rw [ascH, Subgroup.mem_centralizer_singleton_iff]
          calc w⁻¹ * g * z = w⁻¹ * (g * z * g⁻¹) * g := by group
            _ = w⁻¹ * (w * z * w⁻¹) * g := by rw [← hs, hws]
            _ = z * (w⁻¹ * g) := by group
        obtain ⟨q, hq, hqv⟩ := Subgroup.mem_map.1 hv₀.2
        have hqv' : g * q * g⁻¹ = v₀ := by simpa [MulAut.conj_apply] using hqv
        have hv₀Q' : w⁻¹ * v₀ * w ∈ ascQ z := by
          rw [m.ascQ_eq_qSub hyp] at hq ⊢
          have := m.qSub_normal hwg hq
          rwa [show w⁻¹ * g * q * (w⁻¹ * g)⁻¹ = w⁻¹ * (g * q * g⁻¹) * w by group, hqv'] at this
        have hv₀1 : w⁻¹ * v₀ * w ≠ 1 := by
          intro e
          have hv0 : v₀ = 1 := by
            calc v₀ = w * (w⁻¹ * v₀ * w) * w⁻¹ := by group
              _ = 1 := by rw [e]; group
          apply hv₀Q
          rw [hv0]; exact one_mem _
        obtain ⟨k, hk⟩ := hy'conj
        have hconj' : ∃ k' : G, k' * z * k'⁻¹ = w⁻¹ * v₀ * w := by
          refine ⟨w⁻¹ * h⁻¹ * k, ?_⟩
          have hv0 : v₀ = h⁻¹ * y' * h := by
            calc v₀ = h⁻¹ * (h * v₀) * 1 := by group
              _ = h⁻¹ * (y' * h) := by rw [hhv]; group
              _ = _ := by group
          rw [hv0, ← hk]; group
        have hF' := (m.conj_mem_Q_iff hyp hv₀Q' hv₀1).1 hconj'
        have := (Subgroup.mem_normalizer_iff.1 hwN _).1 hF'
        rw [show w * (w⁻¹ * v₀ * w) * w⁻¹ = v₀ by group] at this
        exact hv₀Q (m.fSub_le_ascQ hyp this)
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hcN) y').1 hy'F
    rwa [show c⁻¹ * y' * c⁻¹⁻¹ = y by rw [hy']; group] at this
  obtain ⟨t, htQ, htF, ht2⟩ := m.exists_inv_Q_notF
  have ht1 : t ≠ 1 := fun e => htF (e ▸ one_mem _)
  have htz : ¬ IsConj z t := by
    intro hc
    obtain ⟨c, hc'⟩ := isConj_iff.1 hc
    exact htF ((m.conj_mem_Q_iff hyp (by rw [m.ascQ_eq_qSub hyp]; exact htQ) ht1).1 ⟨c, hc'⟩)
  exact asc_false_of_strongly_closed_E8 hyp.orderTwo m.fSub m.card_fSub
    (fun x hx y hy => m.fSub_elab hx hy) m.z_mem_fSub hFH (fun g' hg' => m.le_fSub_of_centralizes hg')
    htrans hsc (t := t) (orderOf_eq_prime (by rwa [pow_two]) ht1) htz

end AscModel

end CFSG.Quasithin
