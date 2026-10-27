module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord CFSG.StandardType.SpCoord
open Multiplicative
open Subgroup
open scoped BigOperators

theorem qTwoLMH_exists_ne_three {m : ℕ} (hm : 4 ≤ m) (a b c : Fin m) :
    ∃ x : Fin m, x ≠ a ∧ x ≠ b ∧ x ≠ c := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c} : Finset (Fin m))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]
        exact Finset.card_le_three.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  exact ⟨i, hi.1, hi.2.1, hi.2.2⟩

theorem qTwoLMH_card_comap_subtype {X : Type} [Group X] (B H : Subgroup X) (hHB : H ≤ B) :
    Nat.card (H.comap B.subtype) = Nat.card H := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hHB y.2⟩, y.2⟩
      left_inv := fun x => by ext <;> rfl
      right_inv := fun y => by ext <;> rfl }

theorem qTwoLMH_card_of_surjective_ker {X V : Type} [Group X] [Group V] [Fintype X]
    (z : X) (π : X →* V) (hsurj : Function.Surjective π)
    (hker : ∀ v : X, π v = 1 ↔ v ∈ Subgroup.zpowers z) :
    Nat.card V * Nat.card (Subgroup.zpowers z) = Nat.card X := by
  have hker_eq : π.ker = Subgroup.zpowers z := by
    ext v
    rw [MonoidHom.mem_ker]
    exact hker v
  have h1 : Nat.card X = Nat.card (X ⧸ π.ker) * Nat.card π.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have h2 : Nat.card (X ⧸ π.ker) = Nat.card V :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hsurj).toEquiv
  rw [hker_eq] at h1 h2
  rw [h2] at h1
  exact h1.symm

theorem qTwoLMH_card_ker_of_surjective_zmod3 {X : Type} [Group X] [Fintype X]
    (ψ : X →* Multiplicative (ZMod 3)) (hsurj : Function.Surjective ψ) :
    Nat.card ψ.ker * 3 = Nat.card X := by
  have h1 : Nat.card X = Nat.card (X ⧸ ψ.ker) * Nat.card ψ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have hrange : Nat.card ψ.range = 3 := by
    rw [MonoidHom.range_eq_top.mpr hsurj]
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
    show Nat.card (ZMod 3) = 3
    rw [Nat.card_zmod]
  have h2 : Nat.card (X ⧸ ψ.ker) = 3 :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv).trans hrange
  rw [h2] at h1
  exact (mul_comm _ _).trans h1.symm

theorem qTwoLMH_card_fix_of_index_three {X V : Type} [Group X] [Group V] [Fintype X]
    {z : X} (π : X →* V) (hsurj : Function.Surjective π)
    (hker : ∀ v : X, π v = 1 ↔ v ∈ Subgroup.zpowers z)
    {m : ℕ} (s : Equiv.Perm (Fin m)) (ρ : Equiv.Perm (Fin m) →* MulAut V)
    (B : Subgroup X) (hBk : Subgroup.zpowers z ≤ B)
    (hBidx : Nat.card B * 3 = Nat.card X)
    (hBfix : ∀ w : X, w ∈ B ↔ ρ s (π w) = π w) :
    Nat.card {v : V // ρ s v = v} * 3 = Nat.card V := by
  haveI : Fintype B := Fintype.ofFinite B
  let fixV : Subgroup V :=
    { carrier := {v | ρ s v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        rw [Set.mem_setOf_eq] at ha hb
        show (ρ s) (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        rw [Set.mem_setOf_eq] at ha
        show (ρ s) a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  let φ : B →* V := π.comp B.subtype
  have hkerφ : Nat.card φ.ker = Nat.card (Subgroup.zpowers z) := by
    have h_eq : φ.ker = (Subgroup.zpowers z).comap B.subtype := by
      ext w
      simp only [MonoidHom.mem_ker, Subgroup.mem_comap]
      change π (w : X) = 1 ↔ (w : X) ∈ Subgroup.zpowers z
      exact hker (w : X)
    rw [h_eq]
    exact qTwoLMH_card_comap_subtype B _ hBk
  have hquot : Nat.card (B ⧸ φ.ker) = Nat.card {v : V // ρ s v = v} := by
    have hrange : φ.range = fixV := by
      ext v
      constructor
      · rintro ⟨w, rfl⟩
        exact (hBfix w).mp w.2
      · intro hv
        obtain ⟨w, hw⟩ := hsurj v
        exact ⟨⟨w, (hBfix w).mpr (by rw [hw]; exact hv)⟩, hw⟩
    calc Nat.card (B ⧸ φ.ker)
        = Nat.card φ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
      _ = Nat.card fixV := by rw [hrange]
      _ = Nat.card {v : V // ρ s v = v} := rfl
  have hcardX : Nat.card V * Nat.card (Subgroup.zpowers z) = Nat.card X :=
    qTwoLMH_card_of_surjective_ker z π hsurj hker
  have h1 : Nat.card B = Nat.card (B ⧸ φ.ker) * Nat.card φ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hEq : Nat.card V * Nat.card (Subgroup.zpowers z)
      = (Nat.card {v : V // ρ s v = v} * 3) * Nat.card (Subgroup.zpowers z) := by
    rw [hcardX, ← hBidx, h1, hquot, hkerφ]
    ring
  have hpos : 0 < Nat.card (Subgroup.zpowers z) := Nat.card_pos
  exact (Nat.mul_right_cancel hpos hEq).symm

theorem qTwoLMH_ofAdd_one_pow (n : ℕ) :
    (ofAdd (1 : ZMod 3)) ^ n = ofAdd (n : ZMod 3) := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← ofAdd_add, Nat.cast_succ]

theorem qTwoLMH_card_perm (m : ℕ) :
    Nat.card (Fin m → Multiplicative (ZMod 3)) = 3 ^ m := by
  rw [Nat.card_fun, Nat.card_fin]
  congr 1
  show Nat.card (ZMod 3) = 3
  rw [Nat.card_zmod]

theorem qTwoLMH_crd_oneVec {m : ℕ} (h3 : 3 ∣ m) (k : Fin m) :
    crd (qTwoOneVec m h3) k = 1 := by
  change toAdd ((fun _ : Fin m => Multiplicative.ofAdd (1 : ZMod 3)) k) = 1
  simp

theorem qTwoLMH_mem_zpowers_oneVec {m : ℕ} (h3 : 3 ∣ m) (hm : 1 ≤ m)
    (w : ↥(sumZero m 3)) :
    w ∈ Subgroup.zpowers (qTwoOneVec m h3) ↔ ∀ i j, crd w i = crd w j := by
  constructor
  · intro hw
    rw [mem_zpowers_iff_mem_range_orderOf] at hw
    obtain ⟨n, -, hn⟩ := Finset.mem_image.mp hw
    rw [← hn]
    intro i j
    simp only [crd_pow, qTwoLMH_crd_oneVec, mul_one]
  · intro hw
    have h0 : w = (qTwoOneVec m h3) ^ (crd w ⟨0, hm⟩).val := by
      apply ext_crd
      intro k
      rw [crd_pow, qTwoLMH_crd_oneVec, mul_one, ZMod.natCast_zmod_val]
      exact hw k ⟨0, hm⟩
    rw [h0]
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨((crd w ⟨0, hm⟩).val : ℤ), by rw [zpow_natCast]⟩

theorem qTwoLMH_card_zpowers_oneVec {m : ℕ} (h3 : 3 ∣ m) (hm : 1 ≤ m) :
    Nat.card (Subgroup.zpowers (qTwoOneVec m h3)) = 3 := by
  rw [Nat.card_zpowers]
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · simpa using pow_p_eq_one (qTwoOneVec m h3)
  · intro h
    have hc := congrArg (fun w => crd w ⟨0, hm⟩) h
    rw [qTwoLMH_crd_oneVec h3 ⟨0, hm⟩, crd_one] at hc
    exact one_ne_zero hc

theorem qTwoLMH_card_sumZero {m : ℕ} (hm : 1 ≤ m) :
    Nat.card ↥(sumZero m 3) = 3 ^ (m - 1) := by
  let aug : (Fin m → Multiplicative (ZMod 3)) →* Multiplicative (ZMod 3) :=
    { toFun := fun f => ofAdd (∑ i, toAdd (f i))
      map_one' := by simp
      map_mul' := by
        intro f g
        simp only [Pi.mul_apply, toAdd_mul, Finset.sum_add_distrib]
        rw [ofAdd_add] }
  have hker : aug.ker = sumZero m 3 := by
    ext f
    rw [MonoidHom.mem_ker, mem_sumZero]
    constructor
    · intro h
      exact congrArg toAdd h
    · intro h
      exact congrArg ofAdd h
  have hsurj : Function.Surjective aug := by
    intro y
    refine ⟨(Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) ⟨0, hm⟩ y :
      Fin m → Multiplicative (ZMod 3)), ?_⟩
    show ofAdd (∑ i, toAdd ((Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3))
      ⟨0, hm⟩ y) i)) = y
    rw [Finset.sum_eq_single ⟨0, hm⟩
      (fun b _ hb => by rw [Pi.mulSingle_eq_of_ne hb]; simp)
      (fun hmem => absurd (Finset.mem_univ _) hmem)]
    simp
  have hcard : Nat.card ↥(sumZero m 3) * 3 = Nat.card (Fin m → Multiplicative (ZMod 3)) := by
    have h1 : Nat.card (Fin m → Multiplicative (ZMod 3))
        = Nat.card ((Fin m → Multiplicative (ZMod 3)) ⧸ aug.ker) * Nat.card aug.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup aug.ker
    have hrange : Nat.card aug.range = 3 := by
      rw [MonoidHom.range_eq_top.mpr hsurj]
      rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
      show Nat.card (ZMod 3) = 3
      rw [Nat.card_zmod]
    have h2 : Nat.card ((Fin m → Multiplicative (ZMod 3)) ⧸ aug.ker) = 3 :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange aug).toEquiv).trans hrange
    rw [h2, hker] at h1
    exact (mul_comm _ _).trans h1.symm
  have hcardP : Nat.card (Fin m → Multiplicative (ZMod 3)) = 3 ^ m := qTwoLMH_card_perm m
  have hpow : 3 ^ m = 3 ^ (m - 1) * 3 := by
    rw [← pow_succ]
    congr 1
    omega
  have hEq : Nat.card ↥(sumZero m 3) * 3 = 3 ^ (m - 1) * 3 := by
    rw [hcard, hcardP, hpow]
  exact Nat.mul_right_cancel (by norm_num : 0 < 3) hEq

end CFSG.StandardType.QTwo

end
