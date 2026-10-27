module

public import CFSG.Walter.ReeOrder.Ward.LTable
public import CFSG.Walter.ReeOrder.JT.Section6F

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

namespace JTHyp

variable (h : JTHyp G)

@[expose] noncomputable def κ : PSL(2, GaloisField h.p h.f) →* G :=
  h.F.subtype.comp h.iso.symm.toMonoidHom

theorem κ_injective : Function.Injective h.κ :=
  h.F.subtype_injective.comp h.iso.symm.injective

theorem κ_mem (y : PSL(2, GaloisField h.p h.f)) : h.κ y ∈ h.F := (h.iso.symm y).2

theorem κ_comm (y : PSL(2, GaloisField h.p h.f)) : h.κ y * h.t = h.t * h.κ y :=
  h.commute_of_mem_F (h.κ_mem y)

theorem κ_ne_t (y : PSL(2, GaloisField h.p h.f)) : h.κ y ≠ h.t := fun h0 =>
  h.t_not_mem (h0 ▸ h.κ_mem y)

theorem exists_κ_eq {x : G} (hx : x ∈ h.F) : ∃ y, h.κ y = x :=
  ⟨h.iso ⟨x, hx⟩, by simp [κ]⟩

theorem centralizer_κ {g : G} (hg : g * h.t = h.t * g) :
    ∃ y, g = h.κ y ∨ g = h.t * h.κ y := by
  rcases h.mem_centralizer_t.mp (Subgroup.mem_centralizer_singleton_iff.mpr hg) with hgF | hgF
  · obtain ⟨y, hy⟩ := h.exists_κ_eq hgF
    exact ⟨y, Or.inl hy.symm⟩
  · obtain ⟨y, hy⟩ := h.exists_κ_eq hgF
    refine ⟨y, Or.inr ?_⟩
    rw [hy, ← mul_assoc, h.t_mul_t, one_mul]

theorem isConj_t
    (hp : h.p ≠ 2) {x : G} (hx : orderOf x = 2) : IsConj x h.t := by
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp hx
  exact isConj_iff.mpr ⟨g, hg⟩

variable (hp : h.p ≠ 2) (hp3 : h.p ≠ 3) (hS : SuzukiFourGroupTheorem)
  (hH : HuppertMetacyclicTheorem)
include hp hp3 hS hH

theorem twentyseven_le_q :
    27 ≤ h.q := by
  have h8 := h.lemma_4_6_c hp hp3 hS hH
  have h3 := h.q_mod_three hp hp3 hS hH
  have h5 := h.five_lt
  rw [← JTHyp.q_eq] at h5
  omega

theorem wardSign_eq :
    Ward.wardSign h.q = 1 := by
  have h8 := h.lemma_4_6_c hp hp3 hS hH
  unfold Ward.wardSign
  rw [ite_eq_right_iff.mpr (fun h3 => by omega)]

variable [Fintype (GaloisField h.p h.f)] [DecidableEq (GaloisField h.p h.f)]

theorem exists_A
    (W : Ward.WardL PSL(2, GaloisField h.p h.f) h.q 1) :
    ∃ A : G, orderOf A = 3 ∧ A⁻¹ * h.t * A = h.κ W.J' ∧
      A⁻¹ * h.κ W.J' * A = h.t * h.κ W.J' ∧
      (∀ ρ ∈ W.So, ∃ ρ' ∈ W.So, A⁻¹ * h.κ ρ * A = h.κ ρ') ∧
      ∃ ρ ∈ W.So, A * h.κ ρ ≠ h.κ ρ * A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set v := h.κ W.J' with hvdef
  have hvo : orderOf v = 2 := by rw [hvdef, orderOf_injective h.κ h.κ_injective, W.orderOf_J']
  have hvv : v * v = 1 := by rw [← pow_two, ← hvo, pow_orderOf_eq_one]
  have hv1 : v ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at hvo
    omega
  have hvt : v ≠ h.t := h.κ_ne_t _
  have hct : Commute h.t v := (h.κ_comm W.J').symm
  set T := GorensteinWalter.kleinFourOfCommutingInvolutions h.t v h.t_mul_t hvv hct with hTdef
  have hT : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    _ _ _ _ h.t_ne_one hv1 (Ne.symm hvt) hct
  have hmemT : ∀ x, x ∈ T ↔ x = h.t * v ∨ x = h.t ∨ x = v ∨ x = 1 := fun x => Iff.rfl
  have htT : h.t ∈ T := (hmemT _).mpr (Or.inr (Or.inl rfl))
  have hvT : v ∈ T := (hmemT _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (hT.card_four.trans (by norm_num))
  obtain ⟨S, hTS⟩ := hT2.exists_le_sylow
  set s : Setup h := ⟨S, hTS htT, T, hTS, hT, htT⟩ with hsdef
  obtain ⟨c, hc⟩ := s.exists_config hp
  have hcT : c.T = T := by
    show c.toSetup.T = T
    rw [hc]
  set μ := c.μ with hμdef
  have hμ3 : orderOf μ = 3 := c.orderOf_μ
  have hμN : μ ∈ Subgroup.normalizer (T : Set G) := hcT ▸ c.μ_mem_NT
  have hfix : ∀ x ∈ T, μ * x * μ⁻¹ = x → x = 1 := fun x hx => c.μ_fpf x (hcT ▸ hx)
  have hconj : ∀ x ∈ T, μ⁻¹ * x * μ ∈ T := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hμN) x).mp hx
    simpa using this
  have hconj' : ∀ x ∈ T, μ * x * μ⁻¹ ∈ T := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hμN x).mp hx
  have hfix' : ∀ x ∈ T, μ⁻¹ * x * μ = x → x = 1 := fun x hx hx' => hfix x hx (by
    calc μ * x * μ⁻¹ = μ * (μ⁻¹ * x * μ) * μ⁻¹ := by rw [hx']
      _ = x := by group)
  have htv1 : h.t * v ≠ 1 := by
    intro h0
    apply hvt
    calc v = h.t⁻¹ * (h.t * v) := by group
      _ = h.t := by rw [h0, mul_one, h.t_inv]
  have htvt : h.t * v ≠ h.t := by
    intro h0
    apply hv1
    calc v = h.t⁻¹ * (h.t * v) := by group
      _ = 1 := by rw [h0, inv_mul_cancel]
  have htvv : h.t * v ≠ v := by
    intro h0
    apply h.t_ne_one
    calc h.t = h.t * v * v⁻¹ := by group
      _ = 1 := by rw [h0, mul_inv_cancel]
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have htvinv : (h.t * v)⁻¹ = h.t * v := by
    rw [mul_inv_rev, hvinv, h.t_inv]
    exact hct.symm.eq
  have hprops : ∀ a : G, (a = μ ∨ a = μ⁻¹) →
      (∀ x ∈ T, a⁻¹ * x * a ∈ T) ∧ (∀ x ∈ T, a⁻¹ * x * a = x → x = 1) := by
    intro a ha
    rcases ha with rfl | rfl
    · exact ⟨hconj, hfix'⟩
    · exact ⟨fun x hx => by simpa using hconj' x hx, fun x hx hx' =>
        hfix x hx (by simpa using hx')⟩
  have hmul : ∀ a : G, a⁻¹ * (h.t * v) * a = (a⁻¹ * h.t * a) * (a⁻¹ * v * a) := fun a => by
    group
  have hcyc : ∀ a : G, (a = μ ∨ a = μ⁻¹) → a⁻¹ * h.t * a = v → a⁻¹ * v * a = h.t * v := by
    intro a ha hat
    obtain ⟨haT, hafix⟩ := hprops a ha
    rcases (hmemT _).mp (haT v hvT) with h1 | h1 | h1 | h1
    · exact h1
    · exfalso
      have : a⁻¹ * (h.t * v) * a = h.t * v := by rw [hmul, hat, h1]; exact hct.symm.eq
      exact htv1 (hafix _ ((hmemT _).mpr (Or.inl rfl)) this)
    · exact absurd (hafix v hvT h1) hv1
    · exfalso
      have : v = 1 := by
        calc v = a * (a⁻¹ * v * a) * a⁻¹ := by group
          _ = 1 := by rw [h1]; group
      exact hv1 this
  obtain ⟨A, hA, hAt⟩ : ∃ A : G, (A = μ ∨ A = μ⁻¹) ∧ A⁻¹ * h.t * A = v := by
    rcases (hmemT _).mp (hconj h.t htT) with h1 | h1 | h1 | h1
    ·
      refine ⟨μ⁻¹, Or.inr rfl, ?_⟩
      obtain ⟨haT, hafix⟩ := hprops μ⁻¹ (Or.inr rfl)
      rcases (hmemT _).mp (haT h.t htT) with h2 | h2 | h2 | h2
      · exfalso
        rw [inv_inv] at h2
        have e1 : μ * (h.t * v) * μ⁻¹ = h.t := by
          rw [← h1]
          group
        have e2 : μ * v * μ⁻¹ = v := by
          have : μ * (h.t * v) * μ⁻¹ = (μ * h.t * μ⁻¹) * (μ * v * μ⁻¹) := by group
          rw [e1, h2] at this
          calc μ * v * μ⁻¹ = (h.t * v)⁻¹ * ((h.t * v) * (μ * v * μ⁻¹)) := by group
            _ = (h.t * v)⁻¹ * h.t := by rw [← this]
            _ = v := by
              rw [htvinv, mul_assoc, hct.symm.eq, ← mul_assoc, h.t_mul_t, one_mul]
        exact absurd (hfix v hvT e2) hv1
      · exact absurd (hafix h.t htT h2) h.t_ne_one
      · exact h2
      · exfalso
        have : h.t = 1 := by
          calc h.t = μ⁻¹⁻¹⁻¹ * (μ⁻¹⁻¹ * h.t * μ⁻¹) * μ⁻¹⁻¹ := by group
            _ = 1 := by rw [h2]; group
        exact h.t_ne_one this
    · exact absurd (hfix' h.t htT h1) h.t_ne_one
    · exact ⟨μ, Or.inl rfl, h1⟩
    · exfalso
      have : h.t = 1 := by
        calc h.t = μ * (μ⁻¹ * h.t * μ) * μ⁻¹ := by group
          _ = 1 := by rw [h1]; group
      exact h.t_ne_one this
  have hAv := hcyc A hA hAt
  have hA3 : orderOf A = 3 := by
    rcases hA with rfl | rfl
    · exact hμ3
    · rw [orderOf_inv, hμ3]
  refine ⟨A, hA3, hAt, hAv, fun ρ hρ => ?_, ?_⟩
  ·
    set g := A⁻¹ * h.κ ρ * A with hg
    have hρv : h.κ ρ * v = v * h.κ ρ := by
      rw [hvdef, ← map_mul, ← map_mul, W.So_comm ρ hρ]
    have hc1 : g * v = v * g := by
      rw [hg, ← hAt]
      calc A⁻¹ * h.κ ρ * A * (A⁻¹ * h.t * A) = A⁻¹ * (h.κ ρ * h.t) * A := by group
        _ = A⁻¹ * (h.t * h.κ ρ) * A := by rw [h.κ_comm]
        _ = A⁻¹ * h.t * A * (A⁻¹ * h.κ ρ * A) := by group
    have hc2 : g * (h.t * v) = (h.t * v) * g := by
      rw [hg, ← hAv]
      calc A⁻¹ * h.κ ρ * A * (A⁻¹ * v * A) = A⁻¹ * (h.κ ρ * v) * A := by group
        _ = A⁻¹ * (v * h.κ ρ) * A := by rw [hρv]
        _ = A⁻¹ * v * A * (A⁻¹ * h.κ ρ * A) := by group
    have hcJ : g * h.t = h.t * g := by
      have e : h.t = (h.t * v) * v := by rw [mul_assoc, hvv, mul_one]
      rw [e, ← mul_assoc, hc2, mul_assoc, hc1, ← mul_assoc]
    have hodd : Odd (orderOf g) := by
      rw [hg, show A⁻¹ * h.κ ρ * A = A⁻¹ * h.κ ρ * A⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
        MulEquiv.orderOf_eq, orderOf_injective h.κ h.κ_injective]
      have hdvd : orderOf ρ ∣ Nat.card W.So := by
        have := orderOf_dvd_natCard (⟨ρ, hρ⟩ : W.So)
        rwa [Subgroup.orderOf_mk] at this
      have hSo : Odd (Nat.card W.So) := by
        have h1 := W.So_card
        have h2 := W.q_mod
        exact Nat.odd_iff.mpr (by omega)
      exact Odd.of_dvd_nat hSo hdvd
    obtain ⟨y, hy | hy⟩ := h.centralizer_κ hcJ
    · have hyJ' : y * W.J' = W.J' * y := by
        apply h.κ_injective
        rw [map_mul, map_mul, ← hy]
        exact hc1
      have hyodd : Odd (orderOf y) := by
        rw [← orderOf_injective h.κ h.κ_injective, ← hy]
        exact hodd
      exact ⟨y, W.centralizer_J' y hyJ' hyodd, hy⟩
    · exfalso
      obtain ⟨k, hk⟩ := hodd
      have hpow : g ^ (2 * k + 1) = 1 := by rw [← hk, pow_orderOf_eq_one]
      have hc : Commute h.t (h.κ y) := (h.κ_comm y).symm
      rw [hy, hc.mul_pow, pow_succ, pow_mul, sq, h.t_mul_t, one_pow, one_mul] at hpow
      apply h.κ_ne_t (y ^ (2 * k + 1))
      rw [map_pow]
      calc h.κ y ^ (2 * k + 1) = h.t * (h.t * h.κ y ^ (2 * k + 1)) := by
            rw [← mul_assoc, h.t_mul_t, one_mul]
        _ = h.t := by rw [hpow, mul_one]
  ·
    have hSo1 : 1 < Nat.card W.So := by
      have h1 := W.So_card
      have h2 := h.twentyseven_le_q hp hp3 hS hH
      omega
    have := Finite.one_lt_card_iff_nontrivial.mp hSo1
    obtain ⟨⟨ρ, hρ⟩, hρ1⟩ := exists_ne (1 : W.So)
    refine ⟨ρ, hρ, fun hAρ => ?_⟩
    have hρ1' : ρ ≠ 1 := fun h0 => hρ1 (Subtype.ext h0)
    have hρQ : h.κ ρ ∈ c.Q := by
      rw [c.toSetup.mem_Q_iff hp, hcT]
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_, ?_⟩
      · have hρv : h.κ ρ * v = v * h.κ ρ := by
          rw [hvdef, ← map_mul, ← map_mul, W.So_comm ρ hρ]
        have hρt := h.κ_comm ρ
        rcases (hmemT x).mp hx with rfl | rfl | rfl | rfl
        · calc h.t * v * h.κ ρ = h.t * (v * h.κ ρ) := by group
            _ = h.t * (h.κ ρ * v) := by rw [hρv]
            _ = (h.t * h.κ ρ) * v := by group
            _ = (h.κ ρ * h.t) * v := by rw [hρt]
            _ = h.κ ρ * (h.t * v) := by group
        · exact hρt.symm
        · exact hρv.symm
        · rw [one_mul, mul_one]
      · rw [orderOf_injective h.κ h.κ_injective]
        have hdvd : orderOf ρ ∣ Nat.card W.So := by
          have := orderOf_dvd_natCard (⟨ρ, hρ⟩ : W.So)
          rwa [Subgroup.orderOf_mk] at this
        have hSo : Odd (Nat.card W.So) := by
          have h1 := W.So_card
          have h2 := W.q_mod
          exact Nat.odd_iff.mpr (by omega)
        exact Odd.of_dvd_nat hSo hdvd
    have hμρ : c.μ * h.κ ρ = h.κ ρ * c.μ := by
      rcases hA with rfl | rfl
      · exact hAρ
      · have := (Commute.inv_left (hAρ : Commute c.μ⁻¹ (h.κ ρ)))
        rw [inv_inv] at this
        exact this.eq
    have := c.lemma_4_6_a hp hp3 hS hH (h.κ ρ) hρQ hμρ
    apply hρ1'
    apply h.κ_injective
    rw [this, map_one]

end JTHyp

end CFSG.Walter.JT
