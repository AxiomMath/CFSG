module

public import CFSG.Quasithin.Vol2.Ch6OrthIrred
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModCoord

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Quasithin.H13 CFSG.Quasithin CFSG.Open
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem pow_apply_iter {V : Subgroup G} (θ : MulAut ↥V) (n : ℕ) (w : ↥V) :
    (θ ^ n) w = (⇑θ)^[n] w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    show (θ ^ n) (θ w) = _
    rw [ih, Function.iterate_succ_apply]

theorem eq_one_of_two_pow_centralizes {L V : Subgroup G} (horth : IsOrthCh5 L V 4)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 ↥V) (hVne : V ≠ ⊥)
    (θ : MulAut ↥V) {k : ℕ} (hθ : θ ^ 2 ^ k = 1)
    (hcomm : ∀ x ∈ autOn L V, x * θ = θ * x) : θ = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype ↥V := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hV2
  have hV1 : 1 < Nat.card ↥V := (Subgroup.one_lt_card_iff_ne_bot V).mpr hVne
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero] at hn
      omega
    · exact hpos
  have hpar : 2 ∣ Fintype.card ↥V := by
    rw [← Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 (by omega)
  have hiter : (⇑θ : ↥V → ↥V)^[2 ^ k] = id := by
    funext w
    rw [← pow_apply_iter, hθ]
    rfl
  let f : Function.End ↥V := ⇑θ
  have hf : f ^ 2 ^ k = 1 := by
    funext w
    exact congrFun hiter w
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := k) hf
  have hfix1 : (1 : ↥V) ∈ f.fixedPoints := by
    show θ 1 = 1
    rw [map_one]
  have hcardpos : 1 ≤ Fintype.card f.fixedPoints :=
    Fintype.card_pos_iff.mpr ⟨⟨1, hfix1⟩⟩
  have hcard2 : 2 ≤ Fintype.card f.fixedPoints := by
    have h2 : 2 ∣ Fintype.card f.fixedPoints :=
      (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hpar))
    obtain ⟨c, hc⟩ := h2
    omega
  obtain ⟨⟨w0, hw0⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card
    (by omega : 1 < Fintype.card f.fixedPoints) ⟨1, hfix1⟩
  have hw0θ : θ w0 = w0 := hw0
  have hw0_ne : w0 ≠ 1 := fun h => hne (Subtype.ext h)
  let Wfix : Subgroup ↥V :=
    { carrier := {w | θ w = w}
      mul_mem' := fun {a b} ha hb => by
        show θ (a * b) = a * b
        have ha' : θ a = a := ha
        have hb' : θ b = b := hb
        rw [map_mul, ha', hb']
      one_mem' := by
        show θ 1 = 1
        rw [map_one]
      inv_mem' := fun {a} ha => by
        show θ a⁻¹ = a⁻¹
        have ha' : θ a = a := ha
        rw [map_inv, ha'] }
  let W : Subgroup G := Wfix.map V.subtype
  have hWV : W ≤ V := Subgroup.map_subtype_le _
  have hW0 : W ≠ ⊥ := by
    intro hW
    have hmem : (w0 : G) ∈ W := Subgroup.mem_map.mpr ⟨w0, hw0θ, rfl⟩
    rw [hW, Subgroup.mem_bot] at hmem
    exact hw0_ne (Subtype.ext hmem)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    intro ℓ hℓ
    apply mem_normalizer_of_conj_mem
    intro g hg
    obtain ⟨w, hwW, rfl⟩ := Subgroup.mem_map.mp hg
    have hc : conjAct V ⟨(ℓ : G), hLV hℓ⟩ ∈ autOn L V := AutOn.conjAct_mem_autOn_of_mem (hLV hℓ) hℓ
    have hwθ : θ w = w := hwW
    have hcw : θ (conjAct V ⟨(ℓ : G), hLV hℓ⟩ w) = conjAct V ⟨(ℓ : G), hLV hℓ⟩ w := by
      have e2 : θ (conjAct V ⟨(ℓ : G), hLV hℓ⟩ w) = conjAct V ⟨(ℓ : G), hLV hℓ⟩ (θ w) :=
        (congrArg (fun φ : MulAut ↥V => φ w) (hcomm _ hc)).symm
      rw [e2, hwθ]
    refine Subgroup.mem_map.mpr ⟨conjAct V ⟨(ℓ : G), hLV hℓ⟩ w, hcw, ?_⟩
    exact AutOn.coe_conjAct_apply V ⟨(ℓ : G), hLV hℓ⟩ w
  have hWeq : W = V := (IsOrthCh5.irreducible_ch6 horth (by norm_num) W hWV hLW).resolve_left hW0
  refine MulEquiv.ext fun w => ?_
  have hwW : (w : G) ∈ W := by
    rw [hWeq]
    exact w.2
  obtain ⟨w', hw'θ, hw'eq⟩ := Subgroup.mem_map.mp hwW
  have hw'w : w' = w := Subtype.ext hw'eq
  have hfixw : θ w = w := by
    rw [← hw'w]
    exact hw'θ
  rw [hfixw]
  rfl

end CFSG.Quasithin.H13.T614
