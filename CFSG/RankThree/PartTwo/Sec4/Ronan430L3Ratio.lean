module

public import CFSG.RankThree.PartTwo.Sec4.Ronan430L3Group
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan430L3

open CFSG

variable {G : Type*} [Group G]

theorem false_of_ratio [Finite G] {K : Type*} [Field K] {A B : Subgroup G} {a c P T : G}
    {r : G → K × K} (hA : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    (haA : a ∈ A) (hcA : c ∈ A) (hca : c ∉ Subgroup.zpowers a)
    (hsup : Subgroup.zpowers c ⊔ B = A) (hinf : Subgroup.zpowers c ⊓ B = ⊥)
    (hPc : P ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hPB : P ∈ Subgroup.normalizer (B : Set G))
    (hTc : T ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hTB : T ∈ Subgroup.normalizer (B : Set G)) (hTa : T * a = a * T)
    (hr1 : r 1 = 1) (hrmul : ∀ x ∈ A, ∀ y ∈ A, r (x * y) = r x * r y)
    (hrker : ∀ x ∈ A, r x = 1 → x ∈ Subgroup.zpowers a)
    (hrP : ∀ x ∈ A, r (P * x * P⁻¹) = ((r x).2⁻¹, (r x).1 * (r x).2⁻¹))
    (hrT : ∀ x ∈ A, r (T * x * T⁻¹) = ((r x).1⁻¹, (r x).2 * (r x).1⁻¹)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBA : B ≤ A := hsup ▸ le_sup_right
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.2
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc1 : c ≠ 1 := fun h => hca (h ▸ Subgroup.one_mem _)
  have hco : orderOf c = 3 := orderOf_eq_prime (hA3 c hcA) hc1
  have hzc : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
  have hrcube : ∀ x ∈ A, r x ^ 3 = 1 := by
    intro x hx
    have h1 : r (x * x * x) = r x ^ 3 := by
      rw [hrmul _ (A.mul_mem hx hx) _ hx, hrmul _ hx _ hx, pow_three']
    rw [← h1, ← pow_three', hA3 x hx, hr1]
  have hr3 : ∀ x ∈ A, (r x).1 ^ 3 = 1 ∧ (r x).2 ^ 3 = 1 := fun x hx =>
    ⟨by simpa using congrArg Prod.fst (hrcube x hx),
      by simpa using congrArg Prod.snd (hrcube x hx)⟩
  have hne0 : ∀ {u : K}, u ^ 3 = 1 → u ≠ 0 := fun hu h0 => by
    rw [h0] at hu
    norm_num at hu
  have hrinv : ∀ x ∈ A, r x⁻¹ = ((r x).1⁻¹, (r x).2⁻¹) := by
    intro x hx
    have h := hrmul x hx x⁻¹ (A.inv_mem hx)
    rw [mul_inv_cancel, hr1] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one] at h1 h2
    exact Prod.ext (eq_inv_of_mul_eq_one_right h1.symm) (eq_inv_of_mul_eq_one_right h2.symm)
  have hcB : c ∉ B := fun h => by
    have hmem : c ∈ Subgroup.zpowers c ⊓ B := ⟨Subgroup.mem_zpowers c, h⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  have hrc1 : r c ≠ 1 := fun h => hca (hrker c hcA h)
  obtain ⟨hs3, ht3⟩ := hr3 c hcA
  have ht0 : (r c).2 ≠ 0 := hne0 ht3
  have hs0 : (r c).1 ≠ 0 := hne0 hs3
  have hconj1 : ∀ {g : G}, g * c * g⁻¹ = 1 → False := fun {g} h => hc1 (by
    have : c = g⁻¹ * (g * c * g⁻¹) * g := by group
    rw [this, h]
    group)
  have hst : (r c).1 = (r c).2⁻¹ := by
    have hPr := hrP c hcA
    rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers hco
      ((Subgroup.mem_normalizer_iff.mp hPc c).mp (Subgroup.mem_zpowers c)) with h | h | h
    · exact (hconj1 h).elim
    · rw [h] at hPr
      exact congrArg Prod.fst hPr
    · exfalso
      rw [h, pow_two, hrmul c hcA c hcA] at hPr
      have h1 := congrArg Prod.fst hPr
      have h2 := congrArg Prod.snd hPr
      simp only [Prod.fst_mul, Prod.snd_mul] at h1 h2
      have hs : (r c).1 = 1 := by
        have e : (r c).1 = (r c).2 * (r c).2 * (r c).2 := by
          calc (r c).1 = (r c).1 * (r c).2⁻¹ * (r c).2 := by
                rw [mul_assoc, inv_mul_cancel₀ ht0, mul_one]
            _ = (r c).2 * (r c).2 * (r c).2 := by rw [← h2]
        rw [e]
        linear_combination ht3
      have ht : (r c).2 = 1 := by
        rw [hs, one_mul] at h1
        exact inv_eq_one.mp h1.symm
      exact hrc1 (Prod.ext hs ht)
  have ht1 : (r c).2 ≠ 1 := fun h => hrc1 (Prod.ext (by simp [hst, h]) h)
  have hTcc : T * c * T⁻¹ = c ^ 2 := by
    have hTr := hrT c hcA
    rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers hco
      ((Subgroup.mem_normalizer_iff.mp hTc c).mp (Subgroup.mem_zpowers c)) with h | h | h
    · exact (hconj1 h).elim
    · exfalso
      rw [h] at hTr
      have h2 := congrArg Prod.snd hTr
      simp only at h2
      rw [hst, inv_inv] at h2
      apply ht1
      have : (r c).2 * (r c).2 = (r c).2 * 1 := by rw [mul_one]; exact h2.symm
      exact mul_left_cancel₀ ht0 this
    · exact h
  have hTh : ∀ h ∈ Subgroup.zpowers c, T * h * T⁻¹ = h⁻¹ := by
    intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow, hTcc]
    apply eq_inv_of_mul_eq_one_left
    have hcc : Commute (c ^ 2) c := (Commute.refl c).pow_left 2
    rw [← hcc.mul_zpow, show c ^ 2 * c = c ^ 3 by group, hA3 c hcA, one_zpow]
  have hcBc : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    hcomm x (hzc hx) y (hBA hy)
  have haB : a ∈ B := by
    obtain ⟨h, hh, k, hk, hhk⟩ := exists_mul_of_mem_sup hcBc (hsup.symm ▸ haA)
    have hk' : T * k * T⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hTB k).mp hk
    have hTa' : T * a * T⁻¹ = a := by rw [hTa, mul_inv_cancel_right]
    have e1 : T * a * T⁻¹ = h⁻¹ * (T * k * T⁻¹) := by
      rw [← hhk, ← hTh h hh]
      group
    rw [hTa', ← hhk] at e1
    have hh2 : h * h ∈ B := by
      have : h * h = (T * k * T⁻¹) * k⁻¹ := by
        calc h * h = h * (h * k) * k⁻¹ := by group
          _ = h * (h⁻¹ * (T * k * T⁻¹)) * k⁻¹ := by rw [e1]
          _ = (T * k * T⁻¹) * k⁻¹ := by group
      rw [this]
      exact B.mul_mem hk' (B.inv_mem hk)
    have hh2' : h * h = 1 := by
      have hmem : h * h ∈ Subgroup.zpowers c ⊓ B := ⟨Subgroup.mul_mem _ hh hh, hh2⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact hmem
    have hh1 : h = 1 := by
      calc h = h ^ 3 * (h * h)⁻¹ := by group
        _ = 1 := by rw [hA3 h (hzc hh), hh2']; group
    rw [← hhk, hh1, one_mul]
    exact hk
  have key : ∀ x ∈ B, ∀ u : K, u ≠ 1 → r x = (u, u⁻¹) → False := by
    intro x hx u hu1 hrx
    have hxA := hBA hx
    have hu3 : u ^ 3 = 1 := by
      have := (hr3 x hxA).1
      rwa [hrx] at this
    have hcInB : x * c ∈ B ∨ x * c⁻¹ ∈ B → False := by
      rintro (h | h)
      · exact hcB (by
          have : c = x⁻¹ * (x * c) := by group
          rw [this]
          exact B.mul_mem (B.inv_mem hx) h)
      · exact hcB (by
          have : c = (x * c⁻¹)⁻¹ * x := by group
          rw [this]
          exact B.mul_mem (B.inv_mem h) hx)
    have hzaB : Subgroup.zpowers a ≤ B := Subgroup.zpowers_le.mpr haB
    rcases eq_one_or_eq_or_eq_inv_of_pow_three hu3 ht3 ht1 with h | h | h
    · exact hu1 h
    ·
      have hxc : r (x * c) = 1 := by
        rw [hrmul x hxA c hcA, hrx, h]
        refine Prod.ext ?_ ?_
        · show (r c).2 * (r c).1 = 1
          rw [hst, mul_inv_cancel₀ ht0]
        · show (r c).2⁻¹ * (r c).2 = 1
          rw [inv_mul_cancel₀ ht0]
      exact hcInB (Or.inl (hzaB (hrker _ (A.mul_mem hxA hcA) hxc)))
    ·
      have hxc : r (x * c⁻¹) = 1 := by
        rw [hrmul x hxA c⁻¹ (A.inv_mem hcA), hrinv c hcA, hrx, h]
        refine Prod.ext ?_ ?_
        · show (r c).2⁻¹ * (r c).1⁻¹ = 1
          rw [hst, inv_inv, inv_mul_cancel₀ ht0]
        · show (r c).2⁻¹⁻¹ * (r c).2⁻¹ = 1
          rw [inv_inv, mul_inv_cancel₀ ht0]
      exact hcInB (Or.inr (hzaB (hrker _ (A.mul_mem hxA (A.inv_mem hcA)) hxc)))
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcBc
  rw [hsup, h27, hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hco] at hcard
  have hB9 : Nat.card B = 9 := by omega
  obtain ⟨d, hdB, hda⟩ : ∃ d ∈ B, d ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers a from hcon)
    rw [hB9, Nat.card_zpowers] at hle
    have := orderOf_le_of_pow_eq_one (by norm_num) (hA3 a haA)
    omega
  have hdA := hBA hdB
  have hd1 : r d ≠ 1 := fun h => hda (hrker d hdA h)
  obtain ⟨hs'3, ht'3⟩ := hr3 d hdA
  have hs'0 := hne0 hs'3
  have ht'0 := hne0 ht'3
  by_cases hst' : (r d).1 * (r d).2 = 1
  · have ht' : (r d).2 = (r d).1⁻¹ := eq_inv_of_mul_eq_one_right hst'
    refine key d hdB (r d).1 (fun hs1 => hd1 (Prod.ext hs1 ?_)) (Prod.ext rfl ht')
    simp [ht', hs1]
  · have hd'B : P * d * P⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hPB d).mp hdB
    refine key (d * (P * d * P⁻¹)⁻¹) (B.mul_mem hdB (B.inv_mem hd'B)) _ hst' ?_
    have ht'inv : (r d).2⁻¹ = (r d).2 * (r d).2 :=
      inv_eq_of_mul_eq_one_right (by linear_combination ht'3)
    rw [hrmul _ hdA _ (A.inv_mem (hBA hd'B)), hrinv _ (hBA hd'B), hrP d hdA]
    refine Prod.ext ?_ ?_
    · show (r d).1 * ((r d).2⁻¹)⁻¹ = (r d).1 * (r d).2
      rw [inv_inv]
    · show (r d).2 * ((r d).1 * (r d).2⁻¹)⁻¹ = ((r d).1 * (r d).2)⁻¹
      rw [mul_inv_rev, inv_inv, mul_inv_rev, ht'inv]
      ring

end CFSG.RankThree.PartTwo.Sec4.Ronan430L3
