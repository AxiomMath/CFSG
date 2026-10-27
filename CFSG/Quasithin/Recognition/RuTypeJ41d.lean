module

public import CFSG.Quasithin.Recognition.RuTypeJ41c

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G) [Finite G]

theorem actQ_HCbar_of_mem_K {k : G} (hk : k ∈ M.K) {a : M.Qbar} (ha : a ∈ M.HCbar) :
    M.actQ ⟨k, M.K_le_H hk⟩ a = a := by
  obtain ⟨c, hc, rfl⟩ := ha
  have hcG : (c : G) ∈ M.HC := Subgroup.mem_subgroupOf.mp hc
  show M.actQ ⟨k, M.K_le_H hk⟩ (c : M.Qbar) = (c : M.Qbar)
  rw [M.actQ_mk, M.mk_eq_mk_iff]
  have h := M.conj_HC_of_mem_K hk hcG
  have e : ((M.conjQ ⟨k, M.K_le_H hk⟩ c : ruQ M.T) : G)⁻¹ * c =
      ((c : G)⁻¹ * (k * c * k⁻¹))⁻¹ := by
    show (k * (c : G) * k⁻¹)⁻¹ * c = ((c : G)⁻¹ * (k * c * k⁻¹))⁻¹
    group
  rw [e]
  exact inv_mem h

theorem dQ_HCbar_of_mem_K {k : G} (hk : k ∈ M.K) {a : M.Qbar} (ha : a ∈ M.HCbar) :
    M.dQ ⟨k, M.K_le_H hk⟩ a = 1 := by
  rw [M.dQ_apply, M.actQ_HCbar_of_mem_K hk ha, mul_inv_cancel]

theorem actQ_mem_HCbar (h : ruH M.T) {a : M.Qbar} (ha : a ∈ M.HCbar) : M.actQ h a ∈ M.HCbar := by
  obtain ⟨c, hc, rfl⟩ := ha
  have hcG : (c : G) ∈ M.HC := Subgroup.mem_subgroupOf.mp hc
  show M.actQ h (c : M.Qbar) ∈ M.HCbar
  rw [M.actQ_mk, M.mem_HCbar_mk]
  exact M.conj_mem_HC h.2 hcG

theorem actQ_HCbar_of_not_mem_K {h : G} (hh : h ∈ ruH M.T) (hK : h ∉ M.K) {a : M.Qbar}
    (ha : a ∈ M.HCbar) : M.actQ ⟨h, hh⟩ a = M.actQ ⟨M.nel, M.nel_mem_H⟩ a := by
  obtain ⟨c, hc, rfl⟩ := ha
  have hcG : (c : G) ∈ M.HC := Subgroup.mem_subgroupOf.mp hc
  show M.actQ ⟨h, hh⟩ (c : M.Qbar) = M.actQ ⟨M.nel, M.nel_mem_H⟩ (c : M.Qbar)
  rw [M.actQ_mk, M.actQ_mk, M.mk_eq_mk_iff]
  exact M.conj_HC_of_not_mem_K hh hK hcG

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem dQ_range_le_Q5bar
    {w : G} (hwK : w ∈ M.K) {k : ℕ} {q : G} (hq : q ∈ ruQ M.T)
    (hwb : w * b * w⁻¹ = b ^ k * q) :
    (M.dQ ⟨w, M.K_le_H hwK⟩).range ≤ M.Q5bar ⟨b, hbH⟩ := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩ := ((Q5bar_isComplement hbH hb5).existsUnique a).exists
  have hxy' : x * y = a := hxy
  rw [← hxy', map_mul, M.dQ_HCbar_of_mem_K hwK hy, mul_one, M.dQ_apply]
  exact mul_mem (M.Q5bar_conj hbH (M.K_le_H hwK) hq hwb hx) (inv_mem hx)

end Five

theorem ker_ψQbar : M.ψQbar.ker = M.HCbar := by
  ext a
  induction a using QuotientGroup.induction_on with
  | H q =>
  rw [MonoidHom.mem_ker, M.ψQbar_mk, M.mem_HCbar_mk]
  have : M.ψQ q = 1 ↔ q ∈ M.ψQ.ker := Iff.rfl
  rw [this, M.ψQ_ker, Subgroup.mem_subgroupOf]

theorem card_ker_dQ_le {w : G} (hwH : w ∈ ruH M.T) (hwQ : w ∉ ruQ M.T) :
    Nat.card (M.dQ ⟨w, hwH⟩).ker ≤ 16 := by
  classical
  set C := (M.dQ ⟨w, hwH⟩).ker
  set f := M.ψQbar.comp C.subtype
  have h := Subgroup.card_ker_mul_card_range f
  have hk : Nat.card f.ker ≤ 4 := by
    have hmem : ∀ x : f.ker, ((x : C) : M.Qbar) ∈ M.HCbar := by
      intro x
      rw [← M.ker_ψQbar]
      exact x.2
    calc Nat.card f.ker ≤ Nat.card M.HCbar :=
          Nat.card_le_card_of_injective (fun x => (⟨((x : C) : M.Qbar), hmem x⟩ : M.HCbar))
            (fun x y hxy => by
              have h1 := congrArg Subtype.val hxy
              simp only at h1
              exact Subtype.ext (Subtype.ext h1))
      _ = 4 := M.card_HCbar
  have hφw : M.φ ⟨w, hwH⟩ ≠ 1 := by
    intro h1
    apply hwQ
    have hk : (⟨w, hwH⟩ : ruH M.T) ∈ M.φ.ker := h1
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hr : Nat.card f.range ≤ 4 := by
    have hfix := Sigma.card_fix_le_four hφw
    have hf : ∀ y : f.range, sigmaAct (M.φ ⟨w, hwH⟩) (Multiplicative.toAdd (y : _)) =
        Multiplicative.toAdd (y : Multiplicative (Fin 2 → F4)) := by
      rintro ⟨_, ⟨c, rfl⟩⟩
      have hc : M.dQ ⟨w, hwH⟩ c = 1 := c.2
      rw [M.dQ_apply, mul_inv_eq_one] at hc
      show sigmaAct _ (Multiplicative.toAdd (M.ψQbar c)) = Multiplicative.toAdd (M.ψQbar c)
      rw [← M.ψQbar_actQ, hc]
    calc Nat.card f.range ≤ Nat.card {v : Fin 2 → F4 // sigmaAct (M.φ ⟨w, hwH⟩) v = v} :=
          Nat.card_le_card_of_injective (fun y => ⟨Multiplicative.toAdd (y : _), hf y⟩)
            (fun y y' hyy => by
              have h1 := congrArg Subtype.val hyy
              simp only at h1
              exact Subtype.ext (Multiplicative.toAdd.injective h1))
      _ = (Finset.univ.filter (fun v : Fin 2 → F4 =>
            sigmaAct (M.φ ⟨w, hwH⟩) v = v)).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ ≤ 4 := hfix
  have := Nat.mul_le_mul hk hr
  rw [h] at this
  exact this

theorem four_le_card_dQ_range {w : G} (hwH : w ∈ ruH M.T) (hwQ : w ∉ ruQ M.T) :
    4 ≤ Nat.card (M.dQ ⟨w, hwH⟩).range := by
  have h := Subgroup.card_ker_mul_card_range (M.dQ ⟨w, hwH⟩)
  rw [M.card_Qbar] at h
  have hk := M.card_ker_dQ_le hwH hwQ
  by_contra hlt
  push Not at hlt
  have : Nat.card (M.dQ ⟨w, hwH⟩).ker * Nat.card (M.dQ ⟨w, hwH⟩).range ≤ 16 * 3 :=
    Nat.mul_le_mul hk (by omega)
  omega

noncomputable abbrev Q0bar : Subgroup M.Qbar := M.HCbar ⊓ (M.dQ ⟨M.nel, M.nel_mem_H⟩).ker

noncomputable abbrev Q0 : Subgroup G :=
  (M.Q0bar.comap (QuotientGroup.mk' M.UQ)).map (ruQ M.T).subtype

theorem mem_Q0 {x : G} :
    x ∈ M.Q0 ↔ ∃ hx : x ∈ ruQ M.T, ((⟨x, hx⟩ : ruQ M.T) : M.Qbar) ∈ M.Q0bar := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem nel_mul_self_mem_K : (M.nel : G) * M.nel ∈ M.K := by
  have h : M.θ (M.nel * M.nel) = 1 := by
    rw [map_mul, M.θ_nel]
    decide
  have : M.nel * M.nel ∈ M.θ.ker := h
  rw [M.θ_ker, Subgroup.mem_subgroupOf] at this
  exact M.S_le_K this

theorem actQ_nel_nel {a : M.Qbar} (ha : a ∈ M.HCbar) :
    M.actQ ⟨M.nel, M.nel_mem_H⟩ (M.actQ ⟨M.nel, M.nel_mem_H⟩ a) = a := by
  rw [← M.actQ_mul_apply]
  exact M.actQ_HCbar_of_mem_K M.nel_mul_self_mem_K ha

theorem t1bar_mem_HCbar :
    ((⟨M.t1el, M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)⟩ : ruQ M.T) : M.Qbar) ∈ M.HCbar :=
  (M.mem_HCbar_mk _).mpr (M.HB_le_HC M.t1el_mem_HB)

theorem dQ_nel_t1bar_ne_one :
    M.dQ ⟨M.nel, M.nel_mem_H⟩ ((⟨M.t1el, M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)⟩ : ruQ M.T) :
      M.Qbar) ≠ 1 := by
  rw [M.dQ_apply, Ne, mul_inv_eq_one, M.actQ_mk, M.mk_eq_mk_iff]
  intro h
  apply M.nel_moves M.t1el_mem_S M.χ_t1el
  have e : M.t1el⁻¹ * ((M.nel : G) * M.t1el * (M.nel : G)⁻¹) =
      ((((M.conjQ ⟨M.nel, M.nel_mem_H⟩ ⟨M.t1el, M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)⟩) :
        ruQ M.T) : G)⁻¹ * M.t1el)⁻¹ := by
    show M.t1el⁻¹ * ((M.nel : G) * M.t1el * (M.nel : G)⁻¹) =
      (((M.nel : G) * M.t1el * (M.nel : G)⁻¹)⁻¹ * M.t1el)⁻¹
    group
  rw [e]
  exact inv_mem h

theorem card_Q0bar : Nat.card M.Q0bar = 2 := by
  set t := ((⟨M.t1el, M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)⟩ : ruQ M.T) : M.Qbar)
  set x := M.dQ ⟨M.nel, M.nel_mem_H⟩ t
  have htC : t ∈ M.HCbar := M.t1bar_mem_HCbar
  have hxC : x ∈ M.HCbar := by
    show M.actQ _ t * t⁻¹ ∈ M.HCbar
    exact mul_mem (M.actQ_mem_HCbar _ htC) (inv_mem htC)
  have hxfix : x ∈ M.Q0bar := by
    refine ⟨hxC, ?_⟩
    show M.dQ ⟨M.nel, M.nel_mem_H⟩ x = 1
    rw [M.dQ_apply, mul_inv_eq_one]
    show M.actQ _ (M.actQ _ t * t⁻¹) = M.actQ _ t * t⁻¹
    rw [map_mul, map_inv, M.actQ_nel_nel htC]
    have hsq : ∀ y : M.Qbar, y⁻¹ = y := fun y => inv_eq_of_mul_eq_one_right (M.Qbar_sq y)
    rw [hsq t, hsq (M.actQ _ t), M.Qbar_comm]
  have hx1 : x ≠ 1 := M.dQ_nel_t1bar_ne_one
  have ht : t ∉ M.Q0bar := fun h => by
    have h2 : M.dQ ⟨M.nel, M.nel_mem_H⟩ t = 1 := h.2
    exact M.dQ_nel_t1bar_ne_one h2
  have hle : M.Q0bar ≤ M.HCbar := inf_le_left
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [M.card_HCbar] at hdvd
  have hne4 : Nat.card M.Q0bar ≠ 4 := by
    intro h4
    have : M.Q0bar = M.HCbar := Subgroup.eq_of_le_of_card_ge hle (by rw [h4, M.card_HCbar])
    exact ht (this ▸ htC)
  have hne1 : Nat.card M.Q0bar ≠ 1 := by
    intro h1
    have : M.Q0bar = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have := this ▸ hxfix
    exact hx1 (Subgroup.mem_bot.mp this)
  have h4 : Nat.card M.Q0bar ∣ 2 ^ 2 := by simpa using hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
  interval_cases k <;> simp_all

theorem card_Q0 : Nat.card M.Q0 = 2 ^ 6 := by
  rw [Subgroup.card_map_of_injective (ruQ M.T).subtype_injective]
  have h := QuotientGroup.card_preimage_mk M.UQ (M.Q0bar : Set M.Qbar)
  have hpre : (QuotientGroup.mk : ruQ M.T → M.Qbar) ⁻¹' (M.Q0bar : Set M.Qbar) =
      ((M.Q0bar.comap (QuotientGroup.mk' M.UQ)) : Set (ruQ M.T)) := rfl
  rw [hpre] at h
  have h1 : Nat.card (M.Q0bar : Set M.Qbar) = 2 := M.card_Q0bar
  rw [h1, card_subgroupOf_of_le M.U_le_Q, M.toRuData.card_U] at h
  have h2 : Nat.card ((M.Q0bar.comap (QuotientGroup.mk' M.UQ)) : Set (ruQ M.T)) =
      Nat.card (M.Q0bar.comap (QuotientGroup.mk' M.UQ)) := rfl
  rw [h2] at h
  rw [h]
  norm_num

theorem U_le_Q0 : ruU M.L M.T ≤ M.Q0 := fun u hu => by
  refine M.mem_Q0.mpr ⟨M.U_le_Q hu, ?_⟩
  have : ((⟨u, M.U_le_Q hu⟩ : ruQ M.T) : M.Qbar) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hu)
  rw [this]
  exact one_mem _

theorem Q0_le_HC : M.Q0 ≤ M.HC := fun x hx => by
  obtain ⟨hxQ, hx0⟩ := M.mem_Q0.mp hx
  exact (M.mem_HCbar_mk _).mp hx0.1

theorem Q0_le_Q : M.Q0 ≤ ruQ M.T := Subgroup.map_subtype_le _

theorem conj_mem_Q0 {h x : G} (hh : h ∈ ruH M.T) (hx : x ∈ M.Q0) : h * x * h⁻¹ ∈ M.Q0 := by
  obtain ⟨hxQ, hx0⟩ := M.mem_Q0.mp hx
  have hmem : h * x * h⁻¹ ∈ ruQ M.T := M.conj_mem_Q hh hxQ
  refine M.mem_Q0.mpr ⟨hmem, ?_⟩
  have e : ((⟨h * x * h⁻¹, hmem⟩ : ruQ M.T) : M.Qbar) =
      M.actQ ⟨h, hh⟩ ((⟨x, hxQ⟩ : ruQ M.T) : M.Qbar) := rfl
  rw [e]
  refine ⟨M.actQ_mem_HCbar _ hx0.1, ?_⟩
  show M.dQ ⟨M.nel, M.nel_mem_H⟩ (M.actQ ⟨h, hh⟩ ((⟨x, hxQ⟩ : ruQ M.T) : M.Qbar)) = 1
  rw [M.dQ_apply, mul_inv_eq_one]
  have hfix : M.actQ ⟨M.nel, M.nel_mem_H⟩ ((⟨x, hxQ⟩ : ruQ M.T) : M.Qbar) =
      ((⟨x, hxQ⟩ : ruQ M.T) : M.Qbar) := by
    have h2 : M.dQ ⟨M.nel, M.nel_mem_H⟩ ((⟨x, hxQ⟩ : ruQ M.T) : M.Qbar) = 1 := hx0.2
    rwa [M.dQ_apply, mul_inv_eq_one] at h2
  by_cases hK : h ∈ M.K
  · have := M.actQ_HCbar_of_mem_K hK hx0.1
    rw [this, hfix]
  · rw [M.actQ_HCbar_of_not_mem_K hh hK hx0.1, hfix, hfix]

theorem Q0_inf_Q5
    {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    M.Q0 ⊓ M.Q5 hbH = ruU M.L M.T := by
  refine le_antisymm ?_ (le_inf M.U_le_Q0 (M.U_le_Q5 hbH))
  rintro x ⟨hx0, hx5⟩
  rw [← Q5_inf_HC hbH hb5]
  exact ⟨hx5, M.Q0_le_HC hx0⟩

end RuDataM

end CFSG.Quasithin.RuType
