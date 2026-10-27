module

public import CFSG.Quasithin.EmptyFaithful.S143UE

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

namespace S143

namespace InspW2

theorem sl23_dihedral : ∃ i j : SL(2, ZMod 3), (i * i) * (i * i) = 1 ∧ i * i ≠ 1 ∧
    j * j = i * i ∧ i * j ≠ j * i ∧ ((i * i) * (i * j)) ^ 4 = 1 ∧
    (∀ g : SL(2, ZMod 3), g * g = 1 → g = 1 ∨ g = i * i) := by
  decide +kernel

theorem exists_dihedral_of_z4StarSL23 {P : Type*} [Group P] [Finite P] (hP : IsZ4StarSL23 P) :
    ∃ w a b : P, orderOf w = 4 ∧ (∀ k : P, k * w = w * k) ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b ≠ b * a ∧ (a * b) ^ 4 = 1 := by
  obtain ⟨hcard, A, B, ⟨hAB, hsup⟩, hA4, hAcyc, ⟨eB⟩⟩ := hP
  obtain ⟨i₀, j₀, hi4, hi1, hji, hij, hijo, huniq⟩ := sl23_dihedral
  have hB24 : Nat.card B = 24 := by
    rw [Nat.card_congr eB.toEquiv]
    exact SL23.card_sl3
  have hprod := card_sup_mul_card_inf_of_le_centralizer hAB
  rw [hsup, Subgroup.card_top, hcard, hA4, hB24] at hprod
  have hinf : Nat.card ↥(A ⊓ B) = 2 := by omega
  obtain ⟨c, hc⟩ := hAcyc.exists_generator
  have hcord : orderOf c = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hc, hA4]
  have hcP : orderOf (c : P) = 4 := by rw [Subgroup.orderOf_coe, hcord]
  have hc4 : (c : P) ^ 4 = 1 := by rw [← hcP]; exact pow_orderOf_eq_one _
  have hcomm : ∀ b ∈ B, b * (c : P) = (c : P) * b := fun b hb =>
    Subgroup.mem_centralizer_iff.mp (hAB c.2) b hb
  obtain ⟨t, htAB, ht1⟩ : ∃ t ∈ A ⊓ B, t ≠ 1 := by
    by_contra hcon
    have h0 : A ⊓ B = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 fun x hx => by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    rw [h0, Subgroup.card_bot] at hinf
    omega
  have htt : t * t = 1 := by
    have := pow_card_eq_one' (x := (⟨t, htAB⟩ : ↥(A ⊓ B)))
    rw [hinf] at this
    have h2 : t ^ 2 = 1 := congrArg Subtype.val this
    rwa [pow_two] at h2
  have htc : t = (c : P) * (c : P) := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨t, htAB.1⟩)
    have hm' : (c : P) ^ m = t := congrArg Subtype.val hm
    have hmod : (c : P) ^ (m % 4) = t := by
      rw [← hm']
      conv_rhs => rw [← Int.emod_add_mul_ediv m 4, zpow_add, zpow_mul]
      simp [hc4]
    have hsq : (c : P) * (c : P) ≠ 1 := fun h => by
      have h2 : orderOf (c : P) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
      rw [hcP] at h2
      omega
    have hr : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hr with h | h | h | h
    · rw [h, zpow_zero] at hmod
      exact absurd hmod.symm ht1
    · rw [h, zpow_one] at hmod
      rw [← hmod] at htt
      exact absurd htt hsq
    · rw [h, zpow_two] at hmod
      exact hmod.symm
    · rw [h] at hmod
      have h3 : (c : P) ^ ((3 : ℤ)) = (c : P) * (c : P) * (c : P) := by
        simp [zpow_ofNat, pow_succ]
      rw [h3] at hmod
      rw [← hmod] at htt
      exfalso
      have h6 : (c : P) ^ 6 = 1 := by
        have : (c : P) ^ 6 = (c : P) * (c : P) * (c : P) * ((c : P) * (c : P) * (c : P)) := by
          simp [pow_succ, mul_assoc]
        rw [this]
        exact htt
      have h2 : orderOf (c : P) ∣ 6 := orderOf_dvd_of_pow_eq_one h6
      rw [hcP] at h2
      omega
  have htB : t ∈ B := htAB.2
  set ι : B := ⟨t, htB⟩ with hι
  have hιι : eB ι = i₀ * i₀ := by
    have h1 : eB ι * eB ι = 1 := by
      rw [← map_mul]
      have : ι * ι = 1 := Subtype.ext htt
      rw [this, map_one]
    have h2 : eB ι ≠ 1 := fun h =>
      ht1 (congrArg Subtype.val (eB.injective (h.trans (map_one eB).symm)))
    exact (huniq _ h1).resolve_left h2
  have hιeq : ι = eB.symm (i₀ * i₀) := by rw [← hιι]; simp
  set i : B := eB.symm i₀ with hi
  set j : B := eB.symm j₀ with hj
  have hii : i * i = ι := by rw [hιeq, hi, ← map_mul]
  have hjj : j * j = ι := by rw [hιeq, hj, ← map_mul, hji]
  have hiP : (i : P) * (i : P) = t := congrArg Subtype.val hii
  have hjP : (j : P) * (j : P) = t := congrArg Subtype.val hjj
  have hmix : ∀ u v : B, ((c : P) * (u : P)) * ((c : P) * (v : P)) = t * ((u : P) * (v : P)) := by
    intro u v
    calc ((c : P) * (u : P)) * ((c : P) * (v : P))
        = (c : P) * ((u : P) * (c : P)) * (v : P) := by group
      _ = (c : P) * ((c : P) * (u : P)) * (v : P) := by rw [hcomm u u.2]
      _ = ((c : P) * (c : P)) * ((u : P) * (v : P)) := by group
      _ = t * ((u : P) * (v : P)) := by rw [← htc]
  refine ⟨(c : P), (c : P) * (i : P), (c : P) * (j : P), hcP, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have hle : A ⊔ B ≤ Subgroup.centralizer ({(c : P)} : Set P) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨x, hx⟩)
        have : (x : P) = (c : P) ^ n := (congrArg Subtype.val hn).symm
        rw [Subgroup.mem_centralizer_singleton_iff, this]
        exact (Commute.zpow_left (Commute.refl _) n).eq
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcomm x hx
    have := hle (hsup ▸ Subgroup.mem_top k)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  · rw [hmix, hiP, htt]
  · rw [hmix, hjP, htt]
  · intro h
    rw [hmix, hmix] at h
    have h2 := mul_left_cancel h
    have h3 : i * j = j * i := Subtype.ext h2
    have h4 : eB (i * j) = eB (j * i) := by rw [h3]
    rw [map_mul, map_mul, hi, hj, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h4
    exact hij h4
  · rw [hmix]
    have : t * ((i : P) * (j : P)) = ((ι * (i * j) : B) : P) := rfl
    rw [this, ← Subgroup.coe_pow]
    have h5 : (ι * (i * j)) ^ 4 = 1 := by
      apply eB.injective
      rw [map_pow, map_mul, map_mul, hιι, hi, hj, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, map_one]
      exact hijo
    rw [h5]
    rfl

end InspW2

end S143

end CFSG.Quasithin
