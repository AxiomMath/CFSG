module

public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Subgroup Matrix
open scoped commutatorElement

section Unipotent

variable {K : Type} [Field K]

theorem mul_self_eq_one_of_mulVec_eq [CharP K 2] (A : Matrix (Fin 2) (Fin 2) K) (hdet : A.det = 1)
    {v : Fin 2 → K} (hv : v ≠ 0) (hAv : A.mulVec v = v) : A * A = 1 := by
  have hker : (A - 1).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, hAv, Matrix.one_mulVec, sub_self]
  have hdet0 : (A - 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, hker⟩
  rw [Matrix.det_fin_two] at hdet hdet0
  simp only [Matrix.sub_apply, Matrix.one_apply_eq] at hdet0
  have h01 : (1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have h10 : (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  rw [h01, h10, sub_zero, sub_zero] at hdet0
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have htr : A 0 0 + A 1 1 = 0 := by linear_combination hdet - hdet0 + h2
  have e : A * A = !![A 0 0 * A 0 0 + A 0 1 * A 1 0, A 0 0 * A 0 1 + A 0 1 * A 1 1;
      A 1 0 * A 0 0 + A 1 1 * A 1 0, A 1 0 * A 0 1 + A 1 1 * A 1 1] := by
    conv_lhs => rw [Matrix.eta_fin_two A]
    rw [Matrix.mul_fin_two]
  have e00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by linear_combination A 0 0 * htr - hdet - h2
  have e01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0 := by linear_combination A 0 1 * htr
  have e10 : A 1 0 * A 0 0 + A 1 1 * A 1 0 = 0 := by linear_combination A 1 0 * htr
  have e11 : A 1 0 * A 0 1 + A 1 1 * A 1 1 = 1 := by linear_combination A 1 1 * htr - hdet - h2
  rw [e, Matrix.one_fin_two, e00, e01, e10, e11]

theorem det_of_mem_statedSL {n : ℕ} (γ : ↥(StatedSL n K)) :
    ((γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL γ.2

variable {V : Type} [CommGroup V]

theorem mul_self_eq_one_of_binaryNaturalSL {H : Subgroup (MulAut V)} {U Z : Subgroup V} {a : ℕ}
    (hnat : BinaryNaturalSL H U Z 2 a) {t : MulAut V} (ht : t ∈ H) {u : V} (huU : u ∈ U)
    (huZ : u ∉ Z) (htu : t u = u) : t * t = 1 := by
  obtain ⟨F, _, _, hF, π, hπs, -, -, -, -, -, -, β, -, hβZ, hβeq⟩ := hnat
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hF
      have : Nontrivial F := inferInstance
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      omega
    · exact h0
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      ha hF
  obtain ⟨γ, hγ⟩ := hπs ⟨t, ht⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, huU⟩)
  have hγt : ((π γ : ↥H) : MulAut V) = t := congrArg Subtype.val hγ
  have hu' : ((π γ : ↥H) : MulAut V) u ∈ U := by rw [hγt, htu]; exact huU
  have hmem : (FFModel.nat (StatedSL 2 F)).act γ (m : (FFModel.nat (StatedSL 2 F)).Amb) ∈
      (FFModel.nat (StatedSL 2 F)).sec := Subgroup.mem_top _
  have h1 := hβeq γ ⟨u, huU⟩ m hu' hmem hm.symm
  have h2 : (⟨((π γ : ↥H) : MulAut V) u, hu'⟩ : ↥U) = ⟨u, huU⟩ := by
    apply Subtype.ext
    show ((π γ : ↥H) : MulAut V) u = u
    rw [hγt]
    exact htu
  rw [h2, ← hm, QuotientGroup.eq] at h1
  have h3 : (m : (FFModel.nat (StatedSL 2 F)).Amb)⁻¹ *
      (FFModel.nat (StatedSL 2 F)).act γ (m : (FFModel.nat (StatedSL 2 F)).Amb) = 1 := by
    have := h1
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have hfix : (FFModel.nat (StatedSL 2 F)).act γ (m : (FFModel.nat (StatedSL 2 F)).Amb) =
      (m : (FFModel.nat (StatedSL 2 F)).Amb) := by
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  have hm1 : (m : (FFModel.nat (StatedSL 2 F)).Amb) ≠ 1 := by
    intro hm1
    apply huZ
    have : β ⟨u, huU⟩ = 1 := by
      rw [← hm]
      have : m = 1 := Subtype.ext hm1
      rw [this]
      rfl
    exact (hβZ ⟨u, huU⟩).1 this
  set mv : Multiplicative (Fin 2 → F) :=
    ((m : (FFModel.nat (StatedSL 2 F)).Amb) : Multiplicative (Fin 2 → F)) with hmv
  set v : Fin 2 → F := Multiplicative.toAdd mv with hv
  have hv0 : v ≠ 0 := by
    intro h0
    apply hm1
    show mv = 1
    show Multiplicative.ofAdd v = 1
    rw [h0]
    rfl
  let γs : ↥(StatedSL 2 F) := γ
  have hγv : ((γs : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v = v := by
    have := congrArg Multiplicative.toAdd hfix
    exact this
  have hsq := mul_self_eq_one_of_mulVec_eq _ (det_of_mem_statedSL γs) hv0 hγv
  have hγγ : γ * γ = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact hsq
  have h4 : π γ * π γ = 1 := by rw [← map_mul, hγγ, map_one]
  rw [hγ] at h4
  exact congrArg Subtype.val h4

theorem false_of_binaryNaturalSL_of_fix {H X : Subgroup (MulAut V)} {U Z : Subgroup V} {a : ℕ}
    (hnat : BinaryNaturalSL H U Z 2 a) (hXH : X ≤ H) {k : MulAut V} (hk : k ∈ X) {w₁ w₂ : V}
    (hw₁U : w₁ ∈ U) (hw₁Z : w₁ ∉ Z) (hkw : k w₁ = w₁) (hk2 : (k * k) w₂ ≠ w₂) : False :=
  hk2 (by rw [mul_self_eq_one_of_binaryNaturalSL hnat (hXH hk) hw₁U hw₁Z hkw]; rfl)

end Unipotent

section SLQuot

theorem false_of_surj_statedSL {n : ℕ} {F : Type} [Field F] [Finite F]
    (hn : n = 3 ∨ (Nat.card F = 2 ∧ (n = 4 ∨ n = 5))) {Ω : Type*} [Group Ω]
    {X Kst : Subgroup Ω} (π : ↥(StatedSL n F) →* ↥X) (hπ : Function.Surjective π)
    (hKX : Kst ≤ X) (hXK : X ≤ normalizer (Kst : Set Ω))
    (hna : ∃ a ∈ Kst, ∃ b ∈ Kst, a * b ≠ b * a) (h60 : Nat.card Kst = 60) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple m F hm
  set ψ : SpecialLinearGroup (Fin (m + 1)) F →* ↥X :=
    π.comp (specialLinearGroupEquivStatedSL (m + 1) F).toMonoidHom with hψ
  have hψs : Function.Surjective ψ :=
    hπ.comp (specialLinearGroupEquivStatedSL (m + 1) F).surjective
  have hX1 : ∃ x : ↥X, x ≠ 1 := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    refine ⟨⟨a, hKX ha⟩, fun h1 => hab ?_⟩
    have : a = 1 := congrArg Subtype.val h1
    rw [this, one_mul, mul_one]
  have hker : ψ.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq ψ.normal_ker with h | h
    · exfalso
      obtain ⟨x, hx⟩ := hX1
      obtain ⟨s, rfl⟩ := hψs x
      exact hx (MonoidHom.mem_ker.1 (h ▸ mem_top s))
    · exact h
  have hXq : CFSG.IsQuasisimple ↥X := CFSG.LocalCores.isQuasisimple_of_surjective hq ψ hψs hker
  have hKn : (Kst.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKX).2 hXK
  have hKeq : Kst = X := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq hKn with h | h
    · exact le_antisymm hKX (fun x hx => by
        have := (Subgroup.subgroupOf_eq_top.1 h) hx
        exact this)
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hna
      have hc := Subgroup.mem_center_iff.1 (h (show (⟨a, hKX ha⟩ : ↥X) ∈ Kst.subgroupOf X from ha))
        ⟨b, hKX hb⟩
      exact hab (congrArg Subtype.val hc).symm
  have hX60 : Nat.card ↥X = 60 := by rw [← hKeq, h60]
  have hcard : Nat.card (SpecialLinearGroup (Fin (m + 1)) F) = 60 * Nat.card ψ.ker := by
    rw [← hX60, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hZ : Nat.card ψ.ker ≤ m + 1 := by
    have h1 : Nat.card ψ.ker ≤ Nat.card (center (SpecialLinearGroup (Fin (m + 1)) F)) :=
      Subgroup.card_le_of_le hker
    have h2 := Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity
      (n := Fin (m + 1)) (R := F)).toEquiv
    have e1 : max (Fintype.card (Fin (m + 1))) 1 = m + 1 := by rw [Fintype.card_fin]; omega
    rw [e1] at h2
    have h3 : Nat.card (rootsOfUnity (m + 1) F) ≤ m + 1 := card_rootsOfUnity F (m + 1)
    omega
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  obtain ⟨c, hc⟩ : ∃ c, Nat.card ψ.ker = c := ⟨_, rfl⟩
  rw [hc] at hcard hZ hpos
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega)] at hcard
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases hn with h3 | ⟨hF2, h45⟩
  · obtain rfl : m = 2 := by omega
    have hI : Finset.Icc 2 3 = {2, 3} := by decide
    rw [hI, Finset.prod_pair (by norm_num)] at hcard
    norm_num at hcard
    set q := Nat.card F with hqdef
    rcases Nat.lt_or_ge q 3 with hq3 | hq3
    · have hq2' : q = 2 := by omega
      rw [hq2'] at hcard
      norm_num at hcard
      omega
    · have h1 : 27 ≤ q ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
      have h2 : 8 ≤ q ^ 2 - 1 := by
        have : 9 ≤ q ^ 2 := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ q ^ 2 := Nat.pow_le_pow_left hq3 2
        omega
      have h3' : 26 ≤ q ^ 3 - 1 := by omega
      have h4 : 27 * (8 * 26) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3')
      omega
  · rw [hF2] at hcard
    rcases h45 with h4 | h5
    · obtain rfl : m = 3 := by omega
      have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
      rw [hI] at hcard
      norm_num at hcard
      omega
    · obtain rfl : m = 4 := by omega
      have hI : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
      rw [hI] at hcard
      norm_num at hcard
      omega

end SLQuot

section Perfect

variable {V : Type} [CommGroup V]

theorem commOf_commV_eq_of_perfect {X : Subgroup (MulAut V)} (hX : Group.IsPerfect ↥X) :
    XMod.commOf ↥X (commV X) = commV X := by
  set I := commV X with hI
  set I₂ := XMod.commOf ↥X I with hI₂
  have hI₂I : I₂ ≤ I := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, l, hl, rfl⟩
    exact Subgroup.subset_closure ⟨a, a.2, l, rfl⟩
  refine le_antisymm hI₂I ?_
  have hcI : ∀ (x : ↥X) (v : V), (x : MulAut V) v * v⁻¹ ∈ I := fun x v =>
    Subgroup.subset_closure ⟨x, x.2, v, rfl⟩
  have hcI₂ : ∀ (x : ↥X), ∀ i ∈ I, (x : MulAut V) i * i⁻¹ ∈ I₂ := fun x i hi =>
    Subgroup.subset_closure ⟨x, i, hi, rfl⟩
  let d : ↥X →* (V → V ⧸ I₂) :=
    { toFun := fun x v => QuotientGroup.mk ((x : MulAut V) v * v⁻¹)
      map_one' := by
        funext v
        simp
      map_mul' := fun x y => by
        funext v
        have hyv := hcI y v
        have h1 : ((x * y : ↥X) : MulAut V) v * v⁻¹ =
            ((x : MulAut V) ((y : MulAut V) v * v⁻¹) * ((y : MulAut V) v * v⁻¹)⁻¹) *
              (((y : MulAut V) v * v⁻¹) * ((x : MulAut V) v * v⁻¹)) := by
          simp only [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
          group
        show (QuotientGroup.mk (((x * y : ↥X) : MulAut V) v * v⁻¹) : V ⧸ I₂) =
          (QuotientGroup.mk ((x : MulAut V) v * v⁻¹) : V ⧸ I₂) *
            QuotientGroup.mk ((y : MulAut V) v * v⁻¹)
        have e1 : (QuotientGroup.mk (((x * y : ↥X) : MulAut V) v * v⁻¹) : V ⧸ I₂) =
            QuotientGroup.mk ((x : MulAut V) ((y : MulAut V) v * v⁻¹) *
              ((y : MulAut V) v * v⁻¹)⁻¹) *
            QuotientGroup.mk (((y : MulAut V) v * v⁻¹) * ((x : MulAut V) v * v⁻¹)) := by
          rw [h1, QuotientGroup.mk_mul]
        rw [e1, (QuotientGroup.eq_one_iff _).2 (hcI₂ x _ hyv), one_mul, QuotientGroup.mk_mul,
          mul_comm] }
  have hd : d.ker = ⊤ := by
    rw [eq_top_iff, ← Group.isPerfect_def.mp hX]
    exact Abelianization.commutator_subset_ker d
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, v, rfl⟩
  have h1 : (⟨x, hx⟩ : ↥X) ∈ d.ker := hd ▸ mem_top _
  have h2 := congrFun (MonoidHom.mem_ker.1 h1) v
  exact (QuotientGroup.eq_one_iff _).1 h2

theorem commOf_mono {X : Subgroup (MulAut V)} {S S' : Subgroup V} (h : S ≤ S') :
    XMod.commOf ↥X S ≤ XMod.commOf ↥X S' :=
  Subgroup.closure_mono fun _ ⟨a, l, hl, hc⟩ => ⟨a, l, h hl, hc⟩

theorem commOf_sup_le {X : Subgroup (MulAut V)} {P C : Subgroup V}
    (hPinv : ∀ x ∈ X, ∀ p ∈ P, x p ∈ P) (hC : C ≤ fixV X) : XMod.commOf ↥X (P ⊔ C) ≤ P := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, l, hl, rfl⟩
  obtain ⟨p, hp, c, hc, rfl⟩ := Subgroup.mem_sup.1 hl
  have hac : (a : MulAut V) c = c := hC hc a a.2
  show (a : MulAut V) (p * c) * (p * c)⁻¹ ∈ P
  rw [map_mul, hac, show (a : MulAut V) p * c * (p * c)⁻¹ = (a : MulAut V) p * p⁻¹ by group]
  exact P.mul_mem (hPinv _ a.2 p hp) (P.inv_mem hp)

theorem eq_of_isIrrPlus {X : Subgroup (MulAut V)} {M P : Subgroup V}
    (hM : XMod.IsIrrPlus ↥X M) (hPM : P ≤ M) (hPinv : ∀ x ∈ X, ∀ p ∈ P, x p ∈ P)
    (hPfix : P ⊓ fixV X = ⊥) (hP1 : P ≠ ⊥) : M = P := by
  obtain ⟨-, hcomm, -, hirr⟩ := hM
  set F := XMod.fixed ↥X M with hF
  have hFfix : F ≤ fixV X := fun v hv x hx => hv.2 ⟨x, hx⟩
  have hJinv : XMod.IsInv ↥X (P ⊔ F) := by
    intro a l hl
    obtain ⟨p, hp, f, hf, rfl⟩ := Subgroup.mem_sup.1 hl
    show (a : MulAut V) (p * f) ∈ P ⊔ F
    rw [map_mul, hFfix hf a a.2]
    exact Subgroup.mul_mem_sup (hPinv _ a.2 p hp) hf
  rcases hirr (P ⊔ F) hJinv le_sup_right (sup_le hPM fun v hv => hv.1) with h | h
  · exfalso
    apply hP1
    have hle : P ≤ P ⊓ fixV X := le_inf le_rfl ((le_sup_left.trans h.le).trans hFfix)
    rw [hPfix] at hle
    exact le_bot_iff.1 hle
  · refine le_antisymm ?_ hPM
    calc M = XMod.commOf ↥X M := hcomm.symm
      _ = XMod.commOf ↥X (P ⊔ F) := by rw [h]
      _ ≤ P := commOf_sup_le hPinv hFfix

theorem eq_of_card_le [Finite V] {X : Subgroup (MulAut V)} (hX : Group.IsPerfect ↥X)
    {P W C : Subgroup V} (hPX : P ≤ commV X) (hPinv : ∀ x ∈ X, ∀ p ∈ P, x p ∈ P)
    (hPfix : P ⊓ fixV X = ⊥) (hXW : commV X ≤ W) (hCX : C ≤ fixV X) (hCW : C ≤ W)
    (hcard : Nat.card W ≤ Nat.card P * Nat.card C) : commV X = P := by
  have hPC : P ⊓ C = ⊥ := le_bot_iff.1 (hPfix ▸ inf_le_inf_left P hCX)
  set f : ↥P × ↥C → ↥(P ⊔ C) :=
    fun pc => ⟨(pc.1 : V) * pc.2, Subgroup.mul_mem_sup pc.1.2 pc.2.2⟩ with hf
  have hinj : Function.Injective f := by
    rintro ⟨p, c⟩ ⟨p', c'⟩ hpc
    have h1 : (p : V) * c = p' * c' := congrArg Subtype.val hpc
    have h2 : (p' : V)⁻¹ * p = c' * (c : V)⁻¹ := by
      calc (p' : V)⁻¹ * p = (p' : V)⁻¹ * (p * c) * (c : V)⁻¹ := by group
        _ = (p' : V)⁻¹ * (p' * c') * (c : V)⁻¹ := by rw [h1]
        _ = c' * (c : V)⁻¹ := by group
    have hmem : (p' : V)⁻¹ * p ∈ P ⊓ C :=
      ⟨P.mul_mem (P.inv_mem p'.2) p.2, h2 ▸ C.mul_mem c'.2 (C.inv_mem c.2)⟩
    rw [hPC, Subgroup.mem_bot] at hmem
    have hpp : (p : V) = p' := by
      calc (p : V) = p' * ((p' : V)⁻¹ * p) := by group
        _ = p' := by rw [hmem, mul_one]
    have hcc : (c : V) = c' := by
      rw [hpp] at h1
      exact mul_left_cancel h1
    rw [Subtype.ext hpp, Subtype.ext hcc]
  have h1 : Nat.card ↥P * Nat.card ↥C ≤ Nat.card ↥(P ⊔ C) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective f hinj
  have heq : P ⊔ C = W :=
    Subgroup.eq_of_le_of_card_ge (sup_le (hPX.trans hXW) hCW) (hcard.trans h1)
  refine le_antisymm ?_ hPX
  calc commV X = XMod.commOf ↥X (commV X) := (commOf_commV_eq_of_perfect hX).symm
    _ ≤ XMod.commOf ↥X (P ⊔ C) := commOf_mono (heq ▸ hXW)
    _ ≤ P := commOf_sup_le hPinv hCX

end Perfect

theorem isQuasisimple_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  have hZ : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (mem_center_iff.1 (h ▸ mem_top b) a)
  have hperf : Group.IsPerfect X := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator X := Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  let e : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hna
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end CFSG.Quasithin.H13.A7
