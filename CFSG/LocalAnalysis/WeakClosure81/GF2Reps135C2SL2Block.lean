module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import Mathlib.RepresentationTheory.Basic
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcMonomial

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Chevalley

section SL2Facts

variable {F : Type*} [Field F]

private theorem uSL_mul_uSL_eq (a b : F) : (uSL a : SL2 F) * uSL b = uSL (a + b) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem uSL_zero_eq_one : (uSL (0 : F) : SL2 F) = 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_uSL]

private theorem WSL_mul_WSL_eq_one_of_charTwo [CharP F 2] : (WSL : SL2 F) * WSL = 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      CharTwo.neg_eq]

private theorem WSL_mul_uSL_mul_WSL_eq_of_charTwo [CharP F 2] {c : F} (hc : c ≠ 0) :
    (WSL : SL2 F) * uSL c * WSL =
      uSL c⁻¹ * WSL * HSL (Units.mk0 c hc) * uSL c⁻¹ := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, coe_WSL, coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero, hc]

end SL2Facts

section Representation

variable {F k V : Type*} [Field F] [Fintype F] [CharP F 2]
  [Field k] [Finite k] [CharP k 2] [AddCommGroup V] [Module k V]

omit [Fintype F] [CharP F 2] [Finite k] [CharP k 2] in
private theorem map_uSL_mul (π : Representation k (SL2 F) V) (d c : F) (v : V) :
    π (uSL d) (π (uSL c) v) = π (uSL (c + d)) v := by
  rw [← Module.End.mul_apply, ← map_mul, uSL_mul_uSL_eq, add_comm]

omit [Fintype F] [Finite k] [CharP k 2] in
private theorem map_WSL_WSL (π : Representation k (SL2 F) V) (z : V) :
    π WSL (π WSL z) = z := by
  have h := congrArg (fun g : SL2 F => π g z) (WSL_mul_WSL_eq_one_of_charTwo (F := F))
  simpa [map_mul] using h

omit [Fintype F] [Finite k] [CharP k 2] in
private theorem map_WSL_uSL_WSL (π : Representation k (SL2 F) V) {z : V}
    (hu : ∀ c : F, π (uSL c) z = z) (hh : ∀ t : Fˣ, π (HSL t) z = z)
    {c : F} (hc : c ≠ 0) :
    π WSL (π (uSL c) (π WSL z)) = π (uSL c⁻¹) (π WSL z) := by
  have h := congrArg (fun g : SL2 F => π g z) (WSL_mul_uSL_mul_WSL_eq_of_charTwo (F := F) hc)
  simpa [map_mul, Module.End.mul_apply, hu, hh] using h

omit [Finite k] [CharP k 2] in
private theorem sum_uSL_WSL_ne_zero (π : Representation k (SL2 F) V) {z : V}
    (hu : ∀ c : F, π (uSL c) z = z) (hh : ∀ t : Fˣ, π (HSL t) z = z)
    (hW : π WSL z ≠ z) :
    (∑ c : F, π (uSL c) (π WSL z)) ≠ 0 := by
  classical
  intro hN
  set w : V := π WSL z
  set e : F → V := fun c => π (uSL c) w
  have h0 : e 0 = w := by simp [e, uSL_zero_eq_one]
  have h1 : π WSL (∑ c : F, e c) =
      z + ∑ c : {c : F // c ≠ 0}, e c.1⁻¹ := by
    rw [map_sum, Fintype.sum_eq_add_sum_subtype_ne (fun c : F => π WSL (e c)) 0]
    congr 1
    · simpa [e, w, uSL_zero_eq_one] using map_WSL_WSL π z
    · apply Finset.sum_congr rfl
      intro c _
      simpa [e, w] using map_WSL_uSL_WSL π hu hh c.2
  have hreindex : (∑ c : {c : F // c ≠ 0}, e c.1⁻¹) =
      ∑ c : {c : F // c ≠ 0}, e c.1 := by
    let σ : {c : F // c ≠ 0} ≃ {c : F // c ≠ 0} :=
      { toFun := fun c => ⟨c.1⁻¹, inv_ne_zero c.2⟩
        invFun := fun c => ⟨c.1⁻¹, inv_ne_zero c.2⟩
        left_inv := fun c => Subtype.ext (inv_inv c.1)
        right_inv := fun c => Subtype.ext (inv_inv c.1) }
    calc
      (∑ c : {c : F // c ≠ 0}, e c.1⁻¹)
          = ∑ c : {c : F // c ≠ 0}, e (σ c).1 := by simp [σ]
      _ = ∑ c : {c : F // c ≠ 0}, e c.1 :=
        Equiv.sum_comp σ (fun c : {c : F // c ≠ 0} => e c.1)
  have h2 : (∑ c : F, e c) = w + ∑ c : {c : F // c ≠ 0}, e c.1 := by
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun c : F => e c) 0, h0]
  have hwS : w + ∑ c : {c : F // c ≠ 0}, e c.1 = 0 := by
    rw [← h2]
    exact hN
  have hzS : z + ∑ c : {c : F // c ≠ 0}, e c.1 = 0 := by
    have hzT : z + ∑ c : {c : F // c ≠ 0}, e c.1⁻¹ = 0 := by
      rw [← h1, hN, map_zero]
    rwa [hreindex] at hzT
  have hzw : z = w := by
    have hz : z = -(∑ c : {c : F // c ≠ 0}, e c.1) :=
      eq_neg_of_add_eq_zero_left hzS
    have hw : w = -(∑ c : {c : F // c ≠ 0}, e c.1) :=
      eq_neg_of_add_eq_zero_left hwS
    rw [hz, hw]
  exact hW hzw.symm

private theorem exists_ne_zero_const_of_ne_bot
    (K : Submodule k (F → k)) (hK : K ≠ ⊥)
    (hT : ∀ (d : F) {a : F → k}, a ∈ K → (fun c => a (c + d)) ∈ K) :
    ∃ lam : k, lam ≠ 0 ∧ (fun _ : F => lam) ∈ K := by
  have : Algebra (ZMod 2) k := ZMod.algebra k 2
  have : Algebra (ZMod 2) F := ZMod.algebra F 2
  let act : Multiplicative F → ↥K → ↥K := fun d a =>
    ⟨fun c => a.1 (c + d.toAdd), hT d.toAdd a.2⟩
  have act_one : ∀ a : ↥K, act 1 a = a := by
    intro a
    apply Subtype.ext
    funext c
    simp [act]
  have act_mul : ∀ (d e : Multiplicative F) (a : ↥K),
      act (d * e) a = act d (act e a) := by
    intro d e a
    apply Subtype.ext
    funext c
    simp [act, add_assoc]
  let : MulAction (Multiplicative F) ↥K :=
    { smul := act
      one_smul := act_one
      mul_smul := act_mul }
  have hcard : Nat.card ↥K = Nat.card k ^ Module.finrank k ↥K :=
    Module.natCard_eq_pow_finrank
  have hpos : 0 < Module.finrank k ↥K := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hK (Submodule.finrank_eq_zero.1 h0)
  have h2k : 2 ∣ Nat.card k := by
    have hkpos : 0 < Module.finrank (ZMod 2) k := Module.finrank_pos
    have hk : Nat.card k = 2 ^ Module.finrank (ZMod 2) k := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := k)
      simpa [Nat.card_zmod] using h
    rw [hk]
    exact dvd_pow_self 2 hkpos.ne'
  have hdvd : 2 ∣ Nat.card ↥K := by
    rw [hcard]
    exact dvd_pow h2k hpos.ne'
  have hFcard : Nat.card (Multiplicative F) = 2 ^ Module.finrank (ZMod 2) F := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)]
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    simpa [Nat.card_zmod] using h
  have hP : IsPGroup 2 (Multiplicative F) := IsPGroup.of_card hFcard
  have hzero : (0 : ↥K) ∈ MulAction.fixedPoints (Multiplicative F) ↥K := by
    rw [MulAction.mem_fixedPoints]
    intro d
    apply Subtype.ext
    funext c
    change ((act d 0).1 c : k) = 0
    simp [act]
  obtain ⟨b, hb, hb0⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥K hdvd hzero
  have hbfix : ∀ d : Multiplicative F, d • b = b :=
    MulAction.mem_fixedPoints.1 hb
  let lam : k := b.1 0
  have hconst : b.1 = fun _ : F => lam := by
    funext c
    have h := congrFun (congrArg Subtype.val (hbfix (Multiplicative.ofAdd c))) 0
    change (((act (Multiplicative.ofAdd c) b).1) 0 : k) = b.1 0 at h
    simpa [act, lam] using h
  refine ⟨lam, ?_, ?_⟩
  · intro hlam
    have hbzero : b = 0 := by
      apply Subtype.ext
      rw [hconst]
      funext c
      simp [lam, hlam]
    exact hb0 hbzero.symm
  · rw [← hconst]
    exact b.2

private theorem linearIndependent_uSL_WSL (π : Representation k (SL2 F) V) {z : V}
    (hu : ∀ c : F, π (uSL c) z = z) (hh : ∀ t : Fˣ, π (HSL t) z = z)
    (hW : π WSL z ≠ z) :
    LinearIndependent k (fun c : F => π (uSL c) (π WSL z)) := by
  classical
  set w : V := π WSL z
  set e : F → V := fun c => π (uSL c) w
  have hN : (∑ c : F, e c) ≠ 0 := by
    simpa [e, w] using sum_uSL_WSL_ne_zero π hu hh hW
  let Φ : (F → k) →ₗ[k] V := Fintype.linearCombination k e
  have hΦ (a : F → k) : Φ a = ∑ c : F, a c • e c :=
    Fintype.linearCombination_apply k e a
  have htranslate (d : F) (a : F → k) :
      Φ (fun c => a (c + d)) = π (uSL d) (Φ a) := by
    rw [hΦ, hΦ, map_sum]
    have hstep : (∑ c : F, a (c + d) • e c) = ∑ c : F, a c • e (c + d) := by
      rw [← Equiv.sum_comp (Equiv.addRight d) (fun c : F => a c • e (c + d)),
        Equiv.coe_addRight]
      apply Finset.sum_congr rfl
      intro c _
      simp [CharTwo.add_self_eq_zero, add_assoc]
    rw [hstep]
    apply Finset.sum_congr rfl
    intro c _
    rw [map_smul]
    congr 1
    exact (map_uSL_mul π d c w).symm
  have hT : ∀ (d : F) {a : F → k}, a ∈ LinearMap.ker Φ →
      (fun c => a (c + d)) ∈ LinearMap.ker Φ := by
    intro d a ha
    rw [LinearMap.mem_ker] at ha ⊢
    rw [htranslate, ha, map_zero]
  rw [Fintype.linearIndependent_iff]
  intro a ha c
  by_contra hc
  have haK : a ∈ LinearMap.ker Φ := by
    rw [LinearMap.mem_ker, hΦ]
    exact ha
  have hker : LinearMap.ker Φ ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at haK
    exact hc (by rw [haK]; rfl)
  obtain ⟨lam, hlam, hconst⟩ := exists_ne_zero_const_of_ne_bot (LinearMap.ker Φ) hker hT
  have hΦc : Φ (fun _ : F => lam) = 0 := (LinearMap.mem_ker).1 hconst
  have hzero : (∑ c : F, e c) = 0 := by
    have hsm : lam • (∑ c : F, e c) = 0 := by
      rw [← hΦc, hΦ, Finset.smul_sum]
    exact (smul_eq_zero.1 hsm).resolve_left hlam
  exact hN hzero

end Representation

theorem sl2_le_finrank_range_uSL_sub_one {F k V : Type} [Field F] [Finite F] [CharP F 2]
    [Field k] [Finite k] [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (π : Representation k (SL2 F) V) {z : V} (hu : ∀ c : F, π (uSL c) z = z)
    (hh : ∀ t : Fˣ, π (HSL t) z = z) (hW : π WSL z ≠ z) {d : F} (hd : d ≠ 0) :
    Nat.card F / 2 ≤ Module.finrank k (LinearMap.range (π (uSL d) - 1)) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set w : V := π WSL z
  set e : F → V := fun c => π (uSL c) w
  have hli : LinearIndependent k e := by
    simpa [e, w] using linearIndependent_uSL_WSL π hu hh hW
  let H : AddSubgroup F := AddSubgroup.zmultiples d
  have hHcard : Nat.card ↥H = 2 := by
    change Nat.card ↥(AddSubgroup.zmultiples d) = 2
    rw [Nat.card_zmultiples]
    exact addOrderOf_eq_prime (by rw [two_nsmul]; exact CharTwo.add_self_eq_zero d) hd
  let R : ℕ := Nat.card (F ⧸ H)
  have hR : R = Nat.card F / 2 := by
    have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
    rw [hHcard] at h
    change Nat.card (F ⧸ H) = Nat.card F / 2
    omega
  let q : Fin R → F ⧸ H := fun i => (Finite.equivFin (F ⧸ H)).symm i
  let r : Fin R → F := fun i => Quotient.out (q i)
  have hrq : ∀ i, (r i : F ⧸ H) = q i := fun i => Quotient.out_eq (q i)
  have hdH : d ∈ H := AddSubgroup.mem_zmultiples d
  have hinj : Function.Injective (Sum.elim r (fun i => r i + d)) := by
    intro x y h
    rcases x with i | i <;> rcases y with j | j
    · simp only [Sum.elim_inl] at h
      have hq : q i = q j := by rw [← hrq i, ← hrq j, h]
      rw [(Finite.equivFin (F ⧸ H)).symm.injective hq]
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      have hqd : ((r j + d : F) : F ⧸ H) = ((r j : F) : F ⧸ H) := by
        rw [QuotientAddGroup.eq]
        have hneg : -(r j + d) + r j = d := by
          simp [CharTwo.neg_eq, CharTwo.add_self_eq_zero, add_comm, add_left_comm]
        rwa [hneg]
      have hq : q i = q j := by
        rw [← hrq i, ← hrq j]
        exact (congrArg (fun x : F => (x : F ⧸ H)) h).trans hqd
      have hij : i = j := (Finite.equivFin (F ⧸ H)).symm.injective hq
      exfalso
      have hii : r i = r i + d := by rw [← hij] at h; exact h
      have h0 : r i + d = r i + 0 := by simpa using hii.symm
      exact hd (add_left_cancel h0)
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      have hqd : ((r i + d : F) : F ⧸ H) = ((r i : F) : F ⧸ H) := by
        rw [QuotientAddGroup.eq]
        have hneg : -(r i + d) + r i = d := by
          simp [CharTwo.neg_eq, CharTwo.add_self_eq_zero, add_comm, add_left_comm]
        rwa [hneg]
      have hq : q i = q j := by
        rw [← hrq i, ← hrq j]
        exact hqd.symm.trans (congrArg (fun x : F => (x : F ⧸ H)) h)
      have hij : i = j := (Finite.equivFin (F ⧸ H)).symm.injective hq
      exfalso
      have hii : r i + d = r i := by rw [← hij] at h; exact h
      have h0 : r i + d = r i + 0 := by simpa using hii
      exact hd (add_left_cancel h0)
    · simp only [Sum.elim_inr] at h
      have h' : r i = r j := add_right_cancel h
      have hq : q i = q j := by rw [← hrq i, ← hrq j, h']
      rw [(Finite.equivFin (F ⧸ H)).symm.injective hq]
  have hpair : LinearIndependent k
      (Sum.elim (fun i => e (r i)) (fun i => e (r i + d))) := by
    have hcomp := hli.comp (Sum.elim r (fun i => r i + d)) hinj
    have hfun : (Sum.elim (fun i => e (r i)) (fun i => e (r i + d)))
        = e ∘ Sum.elim r (fun i => r i + d) := by
      funext x
      cases x <;> simp [Sum.elim_inl, Sum.elim_inr]
    rw [hfun]
    exact hcomp
  have hA : ∀ i : Fin R, π (uSL d) (e (r i)) = (1 : k) • e (r i + d) := by
    intro i
    rw [one_smul]
    exact map_uSL_mul π d (r i) w
  have hle : R ≤ Module.finrank k (LinearMap.range (π (uSL d) - 1)) :=
    le_finrank_range_sub_one_of_pairs (π (uSL d)) (fun i => e (r i))
      (fun i => e (r i + d)) hpair (fun _ => 1) hA
  rwa [hR] at hle

end CFSG.LocalAnalysis.WeakClosure81
