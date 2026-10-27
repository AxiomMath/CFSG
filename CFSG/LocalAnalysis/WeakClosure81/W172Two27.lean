module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.GroupTheory.CoprimeCosetFixed
public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

private lemma w172_lcs_one (S : Subgroup Γ) :
    S.lowerCentralSeries 1 = (⁅S, S⁆ : Subgroup Γ) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, Subgroup.lowerCentralSeries_succ,
    Subgroup.lowerCentralSeries_zero]

private lemma w172_lcs_two (S : Subgroup Γ) :
    S.lowerCentralSeries 2 = (⁅⁅S, S⁆, S⁆ : Subgroup Γ) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ, w172_lcs_one]

private lemma w172_odd_card_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Subgroup Γ} (hH : IsPGroup p H) : Odd (Nat.card H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

private lemma w172_conj_mul (p q x : Γ) :
    (p * q) * x * (p * q)⁻¹ = p * (q * x * q⁻¹) * p⁻¹ := by
  group

private lemma w172_conj_mem_commutator {H K : Subgroup Γ} {g : Γ}
    (hH : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hK : ∀ x ∈ K, g * x * g⁻¹ ∈ K) :
    ∀ z ∈ (⁅H, K⁆ : Subgroup Γ), g * z * g⁻¹ ∈ ⁅H, K⁆ := by
  intro z hz
  rw [Subgroup.commutator_def] at hz
  induction hz using Subgroup.closure_induction with
  | mem w hw =>
      obtain ⟨x, hx, y, hy, hxy⟩ := hw
      rw [← hxy, conjugate_commutatorElement]
      exact Subgroup.commutator_mem_commutator (hH x hx) (hK y hy)
  | one => simp
  | mul u v _ _ ihu ihv =>
      have h : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
      rw [h]
      exact (⁅H, K⁆).mul_mem ihu ihv
  | inv u _ ihu =>
      have h : g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ := by group
      rw [h]
      exact (⁅H, K⁆).inv_mem ihu

private lemma w172_conj_mem_g3 {S : Subgroup Γ} {g x : Γ} (hx : x ∈ S)
    (hm : g ∈ S.lowerCentralSeries 2) : x * g * x⁻¹ ∈ S.lowerCentralSeries 2 :=
  (Subgroup.mem_set_normalizer_iff.mp (S.self_le_normalizer_lowerCentralSeries 2 hx) g).mp hm

private lemma w172_inv_left_commutator_mem {S : Subgroup Γ} {x y : Γ}
    (hx : x ∈ S) (hy : y ∈ S) :
    ⁅x⁻¹, y⁆ * ⁅x, y⁆ ∈ S.lowerCentralSeries 2 := by
  have hm : ⁅x, y⁆⁻¹ ∈ (⁅S, S⁆ : Subgroup Γ) :=
    (⁅S, S⁆ : Subgroup Γ).inv_mem (Subgroup.commutator_mem_commutator hx hy)
  have h2 : ⁅⁅x, y⁆⁻¹, x⁆ ∈ S.lowerCentralSeries 2 := by
    rw [w172_lcs_two]
    exact Subgroup.commutator_mem_commutator hm hx
  have hconj := w172_conj_mem_g3 (S := S) (x := x⁻¹) (S.inv_mem hx) h2
  have heq : ⁅x⁻¹, y⁆ * ⁅x, y⁆ = x⁻¹ * ⁅⁅x, y⁆⁻¹, x⁆ * x := by
    have hyx : ⁅y, x⁆ = ⁅x, y⁆⁻¹ := (commutatorElement_inv (g₁ := x) (g₂ := y)).symm
    rw [commutatorElement_inv_left, hyx]
    simp only [commutatorElement_def]
    group
  rw [heq]
  simpa only [inv_inv] using hconj

private lemma w172_inv_right_commutator_mem {S : Subgroup Γ} {x y : Γ}
    (hx : x ∈ S) (hy : y ∈ S) :
    ⁅x, y⁻¹⁆ * ⁅x, y⁆ ∈ S.lowerCentralSeries 2 := by
  have hm : ⁅x, y⁆⁻¹ ∈ (⁅S, S⁆ : Subgroup Γ) :=
    (⁅S, S⁆ : Subgroup Γ).inv_mem (Subgroup.commutator_mem_commutator hx hy)
  have h2 : ⁅⁅x, y⁆⁻¹, y⁆ ∈ S.lowerCentralSeries 2 := by
    rw [w172_lcs_two]
    exact Subgroup.commutator_mem_commutator hm hy
  have hconj := w172_conj_mem_g3 (S := S) (x := y⁻¹) (S.inv_mem hy) h2
  have heq : ⁅x, y⁻¹⁆ * ⁅x, y⁆ = y⁻¹ * ⁅⁅x, y⁆⁻¹, y⁆ * y := by
    have hyx : ⁅y, x⁆ = ⁅x, y⁆⁻¹ := (commutatorElement_inv (g₁ := x) (g₂ := y)).symm
    rw [commutatorElement_inv_right, hyx]
    simp only [commutatorElement_def]
    group
  rw [heq]
  simpa only [inv_inv] using hconj

private lemma w172_inv_inv_commutator_mem {S : Subgroup Γ} {x y : Γ}
    (hx : x ∈ S) (hy : y ∈ S) :
    ⁅x⁻¹, y⁻¹⁆ * ⁅x, y⁆⁻¹ ∈ S.lowerCentralSeries 2 := by
  have hA := w172_inv_left_commutator_mem (S := S) hx hy
  have hB := w172_inv_right_commutator_mem (S := S) (S.inv_mem hx) hy
  have hcomm : ⁅x, y⁆ ∈ S :=
    Subgroup.commutator_le_self S (Subgroup.commutator_mem_commutator hx hy)
  have hconj : ⁅x, y⁆ * (⁅x⁻¹, y⁆ * ⁅x, y⁆)⁻¹ * ⁅x, y⁆⁻¹ ∈ S.lowerCentralSeries 2 :=
    w172_conj_mem_g3 (S := S) hcomm ((S.lowerCentralSeries 2).inv_mem hA)
  have hprod : (⁅x⁻¹, y⁻¹⁆ * ⁅x⁻¹, y⁆) *
      (⁅x, y⁆ * (⁅x⁻¹, y⁆ * ⁅x, y⁆)⁻¹ * ⁅x, y⁆⁻¹) ∈
        S.lowerCentralSeries 2 :=
    (S.lowerCentralSeries 2).mul_mem hB hconj
  have heq : ⁅x⁻¹, y⁻¹⁆ * ⁅x, y⁆⁻¹ =
      (⁅x⁻¹, y⁻¹⁆ * ⁅x⁻¹, y⁆) *
        (⁅x, y⁆ * (⁅x⁻¹, y⁆ * ⁅x, y⁆)⁻¹ * ⁅x, y⁆⁻¹) := by
    group
  rwa [heq]

private lemma w172_commutator_le_of_mem {S N : Subgroup Γ} {x y : Γ}
    (hgen : S = Subgroup.closure ({x, y} : Set Γ))
    (hN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N)
    (hxy : ⁅x, y⁆ ∈ N) : (⁅S, S⁆ : Subgroup Γ) ≤ N := by
  have hxS : x ∈ S := by rw [hgen]; exact Subgroup.subset_closure (by simp)
  have hyS : y ∈ S := by rw [hgen]; exact Subgroup.subset_closure (by simp)
  let T : Subgroup Γ :=
    { carrier := {u | u ∈ S ∧ ∀ v ∈ S, ⁅u, v⁆ ∈ N}
      one_mem' := ⟨S.one_mem, by intro v hv; simp⟩
      mul_mem' := by
        rintro u₁ u₂ ⟨hu₁S, hu₁⟩ ⟨hu₂S, hu₂⟩
        refine ⟨S.mul_mem hu₁S hu₂S, fun v hv => ?_⟩
        rw [commutatorElement_mul_left_eq_conj_mul]
        have := N.mul_mem (hN u₁ hu₁S _ (hu₂ v hv)) (hu₁ v hv)
        simpa only [mul_assoc] using this
      inv_mem' := by
        rintro u ⟨huS, hu⟩
        refine ⟨S.inv_mem huS, fun v hv => ?_⟩
        rw [commutatorElement_inv_left]
        have := hN u⁻¹ (S.inv_mem huS) ⁅u, v⁆⁻¹ (N.inv_mem (hu v hv))
        simpa only [commutatorElement_inv, inv_inv, mul_assoc] using this }
  have hxT : x ∈ T := by
    refine ⟨hxS, ?_⟩
    have hxT' : ∀ v ∈ Subgroup.closure ({x, y} : Set Γ), ⁅x, v⁆ ∈ N := by
      intro v hv
      induction hv using Subgroup.closure_induction with
      | mem w hw =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with rfl | rfl
          · simp
          · exact hxy
      | one => simp
      | mul v₁ v₂ hv₁ hv₂ ih₁ ih₂ =>
          rw [commutatorElement_mul_right_eq_mul_conj]
          have := N.mul_mem ih₁ (hN v₁ (by rwa [hgen]) _ ih₂)
          simpa only [mul_assoc] using this
      | inv v₁ hv₁ ih =>
          rw [commutatorElement_inv_right]
          have := hN v₁⁻¹ (S.inv_mem (by rwa [hgen])) ⁅x, v₁⁆⁻¹ (N.inv_mem ih)
          simpa only [commutatorElement_inv, inv_inv] using this
    intro v hv
    exact hxT' v (by rwa [← hgen])
  have hyT : y ∈ T := by
    refine ⟨hyS, ?_⟩
    have hyT' : ∀ v ∈ Subgroup.closure ({x, y} : Set Γ), ⁅y, v⁆ ∈ N := by
      intro v hv
      induction hv using Subgroup.closure_induction with
      | mem w hw =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with rfl | rfl
          · simpa only [commutatorElement_inv] using N.inv_mem hxy
          · simp
      | one => simp
      | mul v₁ v₂ hv₁ hv₂ ih₁ ih₂ =>
          rw [commutatorElement_mul_right_eq_mul_conj]
          have := N.mul_mem ih₁ (hN v₁ (by rwa [hgen]) _ ih₂)
          simpa only [mul_assoc] using this
      | inv v₁ hv₁ ih =>
          rw [commutatorElement_inv_right]
          have := hN v₁⁻¹ (S.inv_mem (by rwa [hgen])) ⁅y, v₁⁆⁻¹ (N.inv_mem ih)
          simpa only [commutatorElement_inv, inv_inv] using this
    intro v hv
    exact hyT' v (by rwa [← hgen])
  have hS_T : S ≤ T := by
    intro s hs
    rw [hgen] at hs
    induction hs using Subgroup.closure_induction with
    | mem w hw =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact hxT
        · exact hyT
    | one => exact T.one_mem
    | mul u v _ _ ihu ihv => exact T.mul_mem ihu ihv
    | inv u _ ihu => exact T.inv_mem ihu
  rw [Subgroup.commutator_le]
  intro u hu v hv
  exact (hS_T hu).2 v hv

private lemma w172_mem_normalizer_inf_centralizer {S : Subgroup Γ} {g x : Γ}
    (hxN : ∀ z ∈ S.lowerCentralSeries 2, x * z * x⁻¹ ∈ S.lowerCentralSeries 2)
    (hxNi : ∀ z ∈ S.lowerCentralSeries 2, x⁻¹ * z * x ∈ S.lowerCentralSeries 2)
    (hxg : Commute x g) :
    x ∈ Subgroup.normalizer
      ((S.lowerCentralSeries 2) ⊓ Subgroup.centralizer ({g} : Set Γ) : Subgroup Γ) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    refine Subgroup.mem_inf.mpr ⟨hxN h hh.1, ?_⟩
    have h1 : Commute h g := Subgroup.mem_centralizer_singleton_iff.mp hh.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((hxg.mul_left h1).mul_left hxg.inv_left).eq
  · intro hh
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := hxNi (x * h * x⁻¹) hh.1
      convert this using 1
      group
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h1 : Commute (x * h * x⁻¹) g := Subgroup.mem_centralizer_singleton_iff.mp hh.2
      have hcomm : Commute (x⁻¹ * (x * h * x⁻¹) * x) g :=
        (hxg.inv_left.mul_left h1).mul_left hxg
      have heq : x⁻¹ * (x * h * x⁻¹) * x = h := by group
      rwa [heq] at hcomm

theorem w172_two27 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup Γ} (hX : IsPGroup p X)
    {e f : Γ} (he : e ^ 2 = 1) (hf : f ^ 2 = 1) (hef : e ≠ f) (hcomm : e * f = f * e)
    (heX : ∀ x ∈ X, e * x * e⁻¹ ∈ X) (hfX : ∀ x ∈ X, f * x * f⁻¹ ∈ X)
    (hno : ∀ u ∈ X, e * u * e⁻¹ = u⁻¹ → f * u * f⁻¹ = u⁻¹ → u = 1)
    {a b : Γ} (ha : a ∈ X) (hb : b ∈ X) (hae : e * a * e⁻¹ = a⁻¹) (haf : f * a * f⁻¹ = a)
    (hbe : e * b * e⁻¹ = b) (hbf : f * b * f⁻¹ = b⁻¹) : a * b = b * a := by
  by_contra hab
  let Y : Subgroup Γ := Subgroup.closure ({a, b} : Set Γ)
  have haY : a ∈ Y := Subgroup.subset_closure (by simp)
  have hbY : b ∈ Y := Subgroup.subset_closure (by simp)
  have hYX : Y ≤ X := by
    intro y hy
    change y ∈ Subgroup.closure ({a, b} : Set Γ) at hy
    induction hy using Subgroup.closure_induction with
    | mem w hw =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact ha
        · exact hb
    | one => exact X.one_mem
    | mul u v _ _ ihu ihv => exact X.mul_mem ihu ihv
    | inv u _ ihu => exact X.inv_mem ihu
  haveI : Fact p.Prime := ⟨hp⟩
  have hYp : IsPGroup p Y :=
    hX.of_injective (Subgroup.inclusion hYX) (Subgroup.inclusion_injective hYX)
  have hYnil : Group.IsNilpotent Y := IsPGroup.isNilpotent hYp
  have hYodd : Odd (Nat.card Y) := w172_odd_card_of_isPGroup hp hp2 hYp
  let c : Γ := ⁅a, b⁆
  have hc : c = ⁅a, b⁆ := rfl
  have hc1 : c ≠ 1 := by
    intro h
    apply hab
    rw [hc] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have he_mul : e * e = 1 := by rwa [pow_two] at he
  have hf_mul : f * f = 1 := by rwa [pow_two] at hf
  have he_inv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he_mul
  have hf_inv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf_mul
  have heY : ∀ y ∈ Y, e * y * e⁻¹ ∈ Y := by
    intro y hy
    change y ∈ Subgroup.closure ({a, b} : Set Γ) at hy
    induction hy using Subgroup.closure_induction with
    | mem w hw =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · rw [hae]; exact Y.inv_mem haY
        · rw [hbe]; exact hbY
    | one => simp
    | mul u v _ _ ihu ihv =>
        have h : e * (u * v) * e⁻¹ = (e * u * e⁻¹) * (e * v * e⁻¹) := by group
        rw [h]
        exact Y.mul_mem ihu ihv
    | inv u _ ihu =>
        have h : e * u⁻¹ * e⁻¹ = (e * u * e⁻¹)⁻¹ := by group
        rw [h]
        exact Y.inv_mem ihu
  have hfY : ∀ y ∈ Y, f * y * f⁻¹ ∈ Y := by
    intro y hy
    change y ∈ Subgroup.closure ({a, b} : Set Γ) at hy
    induction hy using Subgroup.closure_induction with
    | mem w hw =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · rw [haf]; exact haY
        · rw [hbf]; exact Y.inv_mem hbY
    | one => simp
    | mul u v _ _ ihu ihv =>
        have h : f * (u * v) * f⁻¹ = (f * u * f⁻¹) * (f * v * f⁻¹) := by group
        rw [h]
        exact Y.mul_mem ihu ihv
    | inv u _ ihu =>
        have h : f * u⁻¹ * f⁻¹ = (f * u * f⁻¹)⁻¹ := by group
        rw [h]
        exact Y.inv_mem ihu
  have he_g2 : ∀ z ∈ (⁅Y, Y⁆ : Subgroup Γ), e * z * e⁻¹ ∈ ⁅Y, Y⁆ :=
    w172_conj_mem_commutator heY heY
  have hf_g2 : ∀ z ∈ (⁅Y, Y⁆ : Subgroup Γ), f * z * f⁻¹ ∈ ⁅Y, Y⁆ :=
    w172_conj_mem_commutator hfY hfY
  have he_g3 : ∀ z ∈ Y.lowerCentralSeries 2, e * z * e⁻¹ ∈ Y.lowerCentralSeries 2 := by
    intro z hz
    rw [w172_lcs_two] at hz ⊢
    exact w172_conj_mem_commutator he_g2 heY z hz
  have hf_g3 : ∀ z ∈ Y.lowerCentralSeries 2, f * z * f⁻¹ ∈ Y.lowerCentralSeries 2 := by
    intro z hz
    rw [w172_lcs_two] at hz ⊢
    exact w172_conj_mem_commutator hf_g2 hfY z hz
  have hc_g2 : c ∈ Y.lowerCentralSeries 1 := by
    rw [hc, w172_lcs_one]
    exact Subgroup.commutator_mem_commutator haY hbY
  have hc_notin_g3 : c ∉ Y.lowerCentralSeries 2 := by
    intro hc3
    have hle : (⁅Y, Y⁆ : Subgroup Γ) ≤ Y.lowerCentralSeries 2 :=
      w172_commutator_le_of_mem (S := Y) (N := Y.lowerCentralSeries 2) (x := a) (y := b) rfl
        (fun s hs n hn =>
          (Subgroup.mem_set_normalizer_iff.mp
            (Y.self_le_normalizer_lowerCentralSeries 2 hs) n).mp hn)
        (hc ▸ hc3)
    have heq : Y.lowerCentralSeries 1 = Y.lowerCentralSeries 2 := by
      refine le_antisymm ?_ ?_
      · rwa [w172_lcs_one]
      · exact Subgroup.lowerCentralSeries_antitone (S := Y) (show 1 ≤ 2 from by norm_num)
    have hstab : ∀ n, Y.lowerCentralSeries (n + 1) = Y.lowerCentralSeries 1 := by
      intro n
      induction n with
      | zero => rfl
      | succ k ih =>
          rw [Subgroup.lowerCentralSeries_succ, ih,
            ← Subgroup.lowerCentralSeries_succ (S := Y) 1]
          exact heq.symm
    obtain ⟨m, hm⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries Y).mp hYnil
    have hbot : Y.lowerCentralSeries 1 = ⊥ := by
      cases m with
      | zero =>
          have hle1 : Y.lowerCentralSeries 1 ≤ Y.lowerCentralSeries 0 :=
            Subgroup.lowerCentralSeries_antitone (S := Y) (Nat.zero_le 1)
          exact le_bot_iff.mp (hm ▸ hle1)
      | succ k => exact (hstab k).symm.trans hm
    rw [hbot] at hc_g2
    exact hc1 (Subgroup.mem_bot.mp hc_g2)
  have hef2 : (e * f) ^ 2 = 1 := by
    rw [pow_two]
    calc e * f * (e * f) = e * (f * e) * f := by group
      _ = e * (e * f) * f := by rw [← hcomm]
      _ = (e * e) * (f * f) := by group
      _ = 1 := by rw [he_mul, hf_mul, one_mul]
  have hef_ne : e * f ≠ 1 := by
    intro h
    apply hef
    have hfe : f = e := by
      have h2 : e * (e * f) = e * 1 := by rw [h]
      rwa [← mul_assoc, he_mul, one_mul, mul_one] at h2
    rw [hfe]
  have hord : orderOf (e * f) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hef2 hef_ne
  have hγ3X : Y.lowerCentralSeries 2 ≤ X :=
    (Subgroup.lowerCentralSeries_le_self Y 2).trans hYX
  have hγ3p : IsPGroup p (Y.lowerCentralSeries 2) :=
    hX.of_injective (Subgroup.inclusion hγ3X) (Subgroup.inclusion_injective hγ3X)
  have hγ3odd : Odd (Nat.card (Y.lowerCentralSeries 2)) :=
    w172_odd_card_of_isPGroup hp hp2 hγ3p
  have hcop : Nat.Coprime (orderOf (e * f)) (Nat.card (Y.lowerCentralSeries 2)) := by
    rw [hord]
    exact hγ3odd.coprime_two_left
  have hef_g3 : ∀ z ∈ Y.lowerCentralSeries 2,
      (e * f) * z * (e * f)⁻¹ ∈ Y.lowerCentralSeries 2 := by
    intro z hz
    have h1 := hf_g3 z hz
    have h2 := he_g3 (f * z * f⁻¹) h1
    convert h2 using 1
    group
  have hEc : e * c * e⁻¹ = ⁅a⁻¹, b⁆ := by
    rw [hc, conjugate_commutatorElement, hae, hbe]
  have hFc : f * c * f⁻¹ = ⁅a, b⁻¹⁆ := by
    rw [hc, conjugate_commutatorElement, haf, hbf]
  have hbe' : e * b⁻¹ * e⁻¹ = b⁻¹ := by
    have := congrArg Inv.inv hbe
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
  have hef_c : (e * f) * c * (e * f)⁻¹ = ⁅a⁻¹, b⁻¹⁆ := by
    rw [hc, conjugate_commutatorElement, w172_conj_mul e f a, w172_conj_mul e f b,
      haf, hae, hbf, hbe']
  have hm : (e * c * e⁻¹) * c ∈ Y.lowerCentralSeries 2 := by
    rw [hEc, hc]
    exact w172_inv_left_commutator_mem haY hbY
  have hcY : c ∈ Y := by
    rw [hc]
    exact Subgroup.commutator_le_self Y (Subgroup.commutator_mem_commutator haY hbY)
  have hA_g : ((e * f) * c * (e * f)⁻¹) * c⁻¹ ∈ Y.lowerCentralSeries 2 := by
    rw [hef_c, hc]
    exact w172_inv_inv_commutator_mem haY hbY
  have hg : c⁻¹ * ((e * f) * c * (e * f)⁻¹) ∈ Y.lowerCentralSeries 2 := by
    have hconj := w172_conj_mem_g3 (S := Y) (x := c⁻¹) (Y.inv_mem hcY) hA_g
    convert hconj using 1
    group
  obtain ⟨n, hn_g3, hn_fix⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime (Y.lowerCentralSeries 2) hef_g3 hg hcop
  let c' : Γ := c * n
  have hc'_fix : (e * f) * c' * (e * f)⁻¹ = c' := hn_fix
  have hc'_g2 : c' ∈ Y.lowerCentralSeries 1 := by
    have h2 : n ∈ Y.lowerCentralSeries 1 :=
      Subgroup.lowerCentralSeries_antitone (S := Y) (show 1 ≤ 2 from by norm_num) hn_g3
    rw [show c' = c * n from rfl]
    exact (Y.lowerCentralSeries 1).mul_mem hc_g2 h2
  have hc'_Y : c' ∈ Y := Subgroup.lowerCentralSeries_le_self Y 1 hc'_g2
  have hc'_cent : c' * (e * f) = (e * f) * c' := by
    calc c' * (e * f) = ((e * f) * c' * (e * f)⁻¹) * (e * f) := by rw [hc'_fix]
      _ = (e * f) * c' := by group
  let Y₀ : Subgroup Γ := Y.lowerCentralSeries 2 ⊓ Subgroup.centralizer ({e * f} : Set Γ)
  let K : Subgroup Γ := Y₀ ⊔ Subgroup.zpowers c' ⊔ Subgroup.zpowers e
  have hY0Y : Y₀ ≤ Y := inf_le_left.trans (Subgroup.lowerCentralSeries_le_self Y 2)
  have hY0p : IsPGroup p Y₀ :=
    hYp.of_injective (Subgroup.inclusion hY0Y) (Subgroup.inclusion_injective hY0Y)
  have hY0odd : Odd (Nat.card Y₀) := w172_odd_card_of_isPGroup hp hp2 hY0p
  have he_g_comm : e * (e * f) = (e * f) * e := by
    calc e * (e * f) = (e * e) * f := by group
      _ = f := by rw [he_mul, one_mul]
      _ = (e * f) * e := by rw [mul_assoc, ← hcomm, ← mul_assoc, he_mul, one_mul]
  have he_norm : e ∈ Subgroup.normalizer (Y₀ : Set Γ) :=
    w172_mem_normalizer_inf_centralizer (S := Y)
      (fun z hz => he_g3 z hz)
      (fun z hz => by simpa [he_inv] using he_g3 z hz)
      he_g_comm
  have hc'_norm : c' ∈ Subgroup.normalizer (Y₀ : Set Γ) :=
    w172_mem_normalizer_inf_centralizer (S := Y)
      (fun z hz =>
        (Subgroup.mem_set_normalizer_iff.mp
          (Y.self_le_normalizer_lowerCentralSeries 2 hc'_Y) z).mp hz)
      (fun z hz => by
        have h := (Subgroup.mem_set_normalizer_iff.mp
          (Y.self_le_normalizer_lowerCentralSeries 2 (Y.inv_mem hc'_Y)) z).mp hz
        simpa [inv_inv] using h)
      hc'_cent
  have hKnorm : K ≤ Subgroup.normalizer (Y₀ : Set Γ) := by
    refine sup_le (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hc'_norm))
      (Subgroup.zpowers_le.mpr he_norm)
  have hYn : ∀ k ∈ K, ∀ y ∈ Y₀, k * y * k⁻¹ ∈ Y₀ := by
    intro k hk y hy
    exact (Subgroup.mem_set_normalizer_iff.mp (hKnorm hk) y).mp hy
  have he_K : e ∈ K := (le_sup_right : Subgroup.zpowers e ≤ K) (Subgroup.mem_zpowers e)
  have hc'_K : c' ∈ K := by
    refine (le_sup_left : Y₀ ⊔ Subgroup.zpowers c' ≤ K) ?_
    exact (le_sup_right : Subgroup.zpowers c' ≤ Y₀ ⊔ Subgroup.zpowers c')
      (Subgroup.mem_zpowers c')
  have hYK : Y₀ ≤ K :=
    (le_sup_left : Y₀ ≤ Y₀ ⊔ Subgroup.zpowers c').trans
      (le_sup_left : Y₀ ⊔ Subgroup.zpowers c' ≤ K)
  have he4 : e ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, he, one_pow]
  have hY0g : (e * c' * e⁻¹) * c' ∈ Y₀ := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : e * c' * e⁻¹ = (e * c * e⁻¹) * (e * n * e⁻¹) := by
        rw [show c' = c * n from rfl]; group
      have hen : e * n * e⁻¹ ∈ Y.lowerCentralSeries 2 := he_g3 n hn_g3
      have hconj : c⁻¹ * (e * n * e⁻¹) * c ∈ Y.lowerCentralSeries 2 := by
        simpa only [inv_inv] using
          w172_conj_mem_g3 (S := Y) (x := c⁻¹) (Y.inv_mem hcY) hen
      rw [h1, show c' = c * n from rfl]
      have heq2 : ((e * c * e⁻¹) * (e * n * e⁻¹)) * (c * n) =
          ((e * c * e⁻¹) * c) * (c⁻¹ * (e * n * e⁻¹) * c) * n := by group
      rw [heq2]
      exact (Y.lowerCentralSeries 2).mul_mem
        ((Y.lowerCentralSeries 2).mul_mem hm hconj) hn_g3
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h1 : Commute c' (e * f) := hc'_cent
      have h2 : Commute e (e * f) := he_g_comm
      have h3 : Commute (e * c' * e⁻¹) (e * f) := (h2.mul_left h1).mul_left h2.inv_left
      exact (h3.mul_left h1).eq
  obtain ⟨u, huK, huc'Y0, hue⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.exists_exact_inverted_lift_gen (K := K) (Y := Y₀)
      hYK hYn hY0odd he_K hc'_K he4 hY0g
  have huc'Y : c'⁻¹ * u ∈ Y := (Subgroup.lowerCentralSeries_le_self Y 2) huc'Y0.1
  have huY : u ∈ Y := by
    have : u = c' * (c'⁻¹ * u) := by group
    rw [this]
    exact Y.mul_mem hc'_Y huc'Y
  have huX : u ∈ X := hYX huY
  have hu_notin_g3 : u ∉ Y.lowerCentralSeries 2 := by
    intro hu3
    have hc'_in : c' ∈ Y.lowerCentralSeries 2 := by
      have : c' = u * (c'⁻¹ * u)⁻¹ := by group
      rw [this]
      exact (Y.lowerCentralSeries 2).mul_mem hu3 ((Y.lowerCentralSeries 2).inv_mem huc'Y0.1)
    have hc_in : c ∈ Y.lowerCentralSeries 2 := by
      have : c = c' * n⁻¹ := by rw [show c' = c * n from rfl]; group
      rw [this]
      exact (Y.lowerCentralSeries 2).mul_mem hc'_in ((Y.lowerCentralSeries 2).inv_mem hn_g3)
    exact hc_notin_g3 hc_in
  have hu_ne_one : u ≠ 1 := by
    intro h
    exact hu_notin_g3 (by rw [h]; exact (Y.lowerCentralSeries 2).one_mem)
  have hgu : (e * f) * u * (e * f)⁻¹ = u := by
    have hgu_c' : (e * f) * c' * (e * f)⁻¹ = c' := hc'_fix
    have hgu_m : (e * f) * (c'⁻¹ * u) * (e * f)⁻¹ = c'⁻¹ * u := by
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp huc'Y0.2
      calc (e * f) * (c'⁻¹ * u) * (e * f)⁻¹ = ((e * f) * (c'⁻¹ * u)) * (e * f)⁻¹ := by
            group
        _ = ((c'⁻¹ * u) * (e * f)) * (e * f)⁻¹ := by rw [hcomm]
        _ = c'⁻¹ * u := by group
    calc (e * f) * u * (e * f)⁻¹ = (e * f) * (c' * (c'⁻¹ * u)) * (e * f)⁻¹ := by
          conv_lhs => rw [show u = c' * (c'⁻¹ * u) from by group]
      _ = ((e * f) * c' * (e * f)⁻¹) * ((e * f) * (c'⁻¹ * u) * (e * f)⁻¹) := by group
      _ = c' * (c'⁻¹ * u) := by rw [hgu_c', hgu_m]
      _ = u := by group
  have hfu : f * u * f⁻¹ = u⁻¹ := by
    have h1 : e * (f * u * f⁻¹) * e⁻¹ = u := by
      calc e * (f * u * f⁻¹) * e⁻¹ = (e * f) * u * (e * f)⁻¹ := by group
        _ = u := hgu
    have h3 : f * u * f⁻¹ = e⁻¹ * u * e := by
      calc f * u * f⁻¹ = e⁻¹ * (e * (f * u * f⁻¹) * e⁻¹) * e := by group
        _ = e⁻¹ * u * e := by rw [h1]
    have hue' : e * u * e = u⁻¹ := by
      have := hue
      rwa [he_inv] at this
    rw [h3, he_inv]
    exact hue'
  have hu_one : u = 1 := hno u huX hue hfu
  exact hu_ne_one hu_one

end CFSG.LocalAnalysis.WeakClosure81

end
