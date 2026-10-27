module

public import CFSG.Quasithin.Vol2.Ch10SecKITn
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3L3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF
open CFSG.Quasithin.Vol2.Ch11.SecA (oSL2 BarData)

variable {G : Type} [Group G] [Finite G] {L X : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem IsNatBlock.fpf (h : IsNatBlock X n) (hn : 1 ≤ n) (x : ↥X) (hx : orderOf x = 3)
    (u : ↥X) (hu : u ∈ CFSG.pCore 2 ↥X) (hxu : x * u = u * x) : u = 1 := by
  obtain ⟨F, _, _, hF, α, hαs, hαk, β, hβs, hβk, hβ⟩ := h.2.1
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hn hF'
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, h.2.2.1]
    simp
  set u' : ↥(blockU X) := ⟨u, (h.mem_blockU_iff u).mpr hu⟩ with hu'
  have hfix : (α x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u')) =
      Multiplicative.toAdd (β u') := by
    refine (hβ x u' u' ?_).symm
    show (u : G) = x * u * x⁻¹
    have := congrArg Subtype.val hxu
    simp only [Subgroup.coe_mul] at this
    rw [Subgroup.coe_inv, this, mul_inv_cancel_right]
  by_contra hne
  have hw : Multiplicative.toAdd (β u') ≠ 0 := by
    intro h0
    have h1 : β u' = 1 := by
      rw [← ofAdd_toAdd (β u'), h0]
      rfl
    have h2 : u' = 1 := hinj (by rw [h1, map_one])
    have h3 : (u : G) = 1 := by
      have := congrArg Subtype.val h2
      simpa [hu'] using this
    exact hne (Subtype.ext h3)
  have h3 : α x ^ 3 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have h1 := CFSG.QuasithinUnique.A5.G3.sl2_eq_one_of_fixed (α x) h3 ⟨_, hw, Or.inr hfix⟩
  have hxk : x ∈ CFSG.pCore 2 ↥X := by rw [← hαk]; exact h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥X) ⟨x, hxk⟩
  have h4 : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h5 : 3 ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one h4
  have h6 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5)
  omega

theorem natCond_xbar (h : IsNatBlock X 2) (hXL : X ≤ L)
    (hA : X ⊓ pCoreOf 2 L = ⊥) :
    IsElemAbelianOfRank 2 4 ↥(CFSG.pCore 2 ↥(modO2Image L X)) ∧
      IsAlt 5 (ModO2 (modO2Image L X)) ∧
      ∀ x : ↥(modO2Image L X), orderOf x = 3 → ∀ u ∈ CFSG.pCore 2 ↥(modO2Image L X),
        x * u = u * x → u = 1 := by
  obtain ⟨e⟩ := xbar_equiv_of_inf_eq_bot hXL hA
  have hmap := CFSG.pCore_map_iso 2 e.symm
  refine ⟨?_, isAlt5_modO2_xbar h hXL, ?_⟩
  · refine Vol2Native.A312L.PermLat.isElemAbelianOfRank_of_card (abO2_xbar h le_rfl hXL).1
      (fun v => ?_) (by rw [(xbar_card_A h hXL hA).2])
    have hv : e.symm v ∈ CFSG.pCore 2 ↥X := hmap ▸ ⟨v, v.2, rfl⟩
    have hw : ((e.symm v : ↥X) : G) ∈ blockU X := (h.mem_blockU_iff _).mpr hv
    have h2 := h.1.2.2.1.2 _ hw
    apply Subtype.ext
    have h3 : e.symm v * e.symm v = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two]; exact h2)
    have h4 := congrArg e h3
    simp only [map_mul, MulEquiv.apply_symm_apply, map_one] at h4
    exact h4
  · intro x hx u hu hxu
    have hu' : e.symm u ∈ CFSG.pCore 2 ↥X := hmap ▸ ⟨u, hu, rfl⟩
    have hx' : orderOf (e.symm x) = 3 := by rw [MulEquiv.orderOf_eq, hx]
    have hxu' : e.symm x * e.symm u = e.symm u * e.symm x := by
      rw [← map_mul, ← map_mul, hxu]
    have h1 := h.fpf (by norm_num) _ hx' _ hu' hxu'
    have h2 := congrArg e h1
    simpa using h2

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
