module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3XbarS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3XbarT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

private theorem s16h_isElemAbelian_three_of_card {X : Type*} [Group X] {H : Subgroup X}
    (h : Nat.card ↥H = 3) : IsElemAbelian 3 H := by
  have hcyc : IsCyclic ↥H := isCyclic_of_prime_card h
  refine ⟨hcyc.isMulCommutative, fun x hx => ?_⟩
  have hx3 : (⟨x, hx⟩ : ↥H) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥H) (x := ⟨x, hx⟩)
    rwa [h] at this
  simpa using congrArg (Subtype.val) hx3

private theorem s16h_z3_inv_mul_inv {X : Type*} [Group X] {a : X} (ha : a ^ 3 = 1) :
    a⁻¹ * a⁻¹ = a := by
  have h : a * a = a⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [pow_succ, pow_two] at ha
    exact ha
  calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by rw [mul_inv_rev]
    _ = (a⁻¹)⁻¹ := by rw [h]
    _ = a := by rw [inv_inv]

private theorem s16h_z3_card_sup_eq {X : Type*} [Group X] {L L₂ : Subgroup X}
    (hcomm : ∀ a ∈ L, ∀ b ∈ L₂, a * b = b * a) (hinf : L ⊓ L₂ = ⊥) :
    Nat.card ↥(L ⊔ L₂) = Nat.card ↥L * Nat.card ↥L₂ := by
  let f : ↥L × ↥L₂ → ↥(L ⊔ L₂) := fun p =>
    ⟨(p.1 : X) * (p.2 : X), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    simp only [f, Subtype.mk.injEq] at h
    have hkey : (a₂ : X)⁻¹ * a₁ = (b₂ : X) * (b₁ : X)⁻¹ := by
      calc (a₂ : X)⁻¹ * a₁ = (a₂ : X)⁻¹ * ((a₁ : X) * b₁) * (b₁ : X)⁻¹ := by group
        _ = (a₂ : X)⁻¹ * ((a₂ : X) * b₂) * (b₁ : X)⁻¹ := by rw [h]
        _ = (b₂ : X) * (b₁ : X)⁻¹ := by group
    have hmem : (a₂ : X)⁻¹ * a₁ ∈ L ⊓ L₂ :=
      ⟨L.mul_mem (L.inv_mem a₂.2) a₁.2, by rw [hkey]; exact L₂.mul_mem b₂.2 (L₂.inv_mem b₁.2)⟩
    have h1 : (a₂ : X)⁻¹ * a₁ = 1 := by simpa [hinf] using hmem
    have ha : (a₁ : X) = a₂ := by
      calc (a₁ : X) = (a₂ : X) * ((a₂ : X)⁻¹ * a₁) := by group
        _ = (a₂ : X) := by rw [h1, mul_one]
    have hb : (b₁ : X) = b₂ := by
      have hh : (a₁ : X) * (b₁ : X) = (a₁ : X) * b₂ := by
        rw [h, ha]
      exact mul_left_cancel hh
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm x.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have e : ↥L × ↥L₂ ≃ ↥(L ⊔ L₂) := Equiv.ofBijective f ⟨hinj, hsurj⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr e).symm

theorem s16h_z3_xbar {X : Type*} [Group X] {A L L₂ : Subgroup X} {x : X} (hxA : x ∈ A)
    (hL₂ : L₂ = L.map (MulAut.conj x).toMonoidHom) (hL : Nat.card ↥L = 3) (hLd : L ≤ ⁅A, A⁆)
    (hperm : ∀ g ∈ A,
      (L.map (MulAut.conj g).toMonoidHom = L ∧ L₂.map (MulAut.conj g).toMonoidHom = L₂) ∨
      (L.map (MulAut.conj g).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj g).toMonoidHom = L))
    (hcomm : ⁅L, L₂⁆ = ⊥) (hinf : L ⊓ L₂ = ⊥) :
    L ⊔ L₂ ≤ ⁅A, A⁆ ∧ (∀ q ∈ A, ∀ y ∈ L ⊔ L₂, q * y * q⁻¹ ∈ L ⊔ L₂) ∧
      IsElemAbelian 3 (L ⊔ L₂) ∧ Nat.card ↥(L ⊔ L₂) = 3 ^ 2 := by
  have hcardL2 : Nat.card ↥L₂ = 3 := by
    rw [hL₂, Subgroup.card_map_of_injective (MulAut.conj x).injective, hL]
  have hmapA : A.map (MulAut.conj x).toMonoidHom = A := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact A.mul_mem (A.mul_mem hxA ha) (A.inv_mem hxA)
    · intro hy
      exact ⟨x⁻¹ * y * x, A.mul_mem (A.mul_mem (A.inv_mem hxA) hy) hxA, by
        simp [MulAut.conj_apply, mul_assoc]⟩
  have hL2_le : L₂ ≤ ⁅A, A⁆ := by
    rw [hL₂]
    refine le_trans (Subgroup.map_mono hLd) ?_
    rw [Subgroup.map_commutator, hmapA]
  have hsup_le : L ⊔ L₂ ≤ ⁅A, A⁆ := sup_le hLd hL2_le
  have hcommLR : ∀ a ∈ L, ∀ b ∈ L₂, a * b = b * a := fun a ha b hb =>
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) ha b hb).symm
  have hnorm : ∀ q ∈ A, ∀ y ∈ L ⊔ L₂, q * y * q⁻¹ ∈ L ⊔ L₂ := by
    intro q hq y hy
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommLR hy
    rcases hperm q hq with ⟨hLq, hL2q⟩ | ⟨hLq, hL2q⟩
    · have ha' : q * a * q⁻¹ ∈ L := by
        have hmem : (MulAut.conj q) a ∈ L.map (MulAut.conj q).toMonoidHom := ⟨a, ha, rfl⟩
        rwa [hLq] at hmem
      have hb' : q * b * q⁻¹ ∈ L₂ := by
        have hmem : (MulAut.conj q) b ∈ L₂.map (MulAut.conj q).toMonoidHom := ⟨b, hb, rfl⟩
        rwa [hL2q] at hmem
      rw [show q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) by group]
      exact Subgroup.mul_mem_sup ha' hb'
    · have ha' : q * a * q⁻¹ ∈ L₂ := by
        have hmem : (MulAut.conj q) a ∈ L.map (MulAut.conj q).toMonoidHom := ⟨a, ha, rfl⟩
        rwa [hLq] at hmem
      have hb' : q * b * q⁻¹ ∈ L := by
        have hmem : (MulAut.conj q) b ∈ L₂.map (MulAut.conj q).toMonoidHom := ⟨b, hb, rfl⟩
        rwa [hL2q] at hmem
      rw [show q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) by group]
      rw [sup_comm]
      exact Subgroup.mul_mem_sup ha' hb'
  refine ⟨hsup_le, hnorm, ?_, ?_⟩
  · exact (s16h_isElemAbelian_three_of_card hL).sup_of_commute
      (s16h_isElemAbelian_three_of_card hcardL2) hcommLR
  · rw [s16h_z3_card_sup_eq hcommLR hinf, hL, hcardL2]
    norm_num

theorem s16h_z3_sub_of_invariant {X : Type*} [Group X] {L L₂ : Subgroup X}
    (hL : Nat.card ↥L = 3) (hL₂ : Nat.card ↥L₂ = 3) (hcomm : ⁅L, L₂⁆ = ⊥) (hinf : L ⊓ L₂ = ⊥)
    {τ : X}
    (hτ : ((∀ l ∈ L, τ * l * τ⁻¹ = l⁻¹) ∧ ∀ l ∈ L₂, τ * l = l * τ) ∨
      ((∀ l ∈ L₂, τ * l * τ⁻¹ = l⁻¹) ∧ ∀ l ∈ L, τ * l = l * τ))
    {Y : Subgroup X} (hY : Y ≤ L ⊔ L₂) (hτY : τ ∈ normalizer (Y : Set X)) :
    Y = ⊥ ∨ Y = L ∨ Y = L₂ ∨ Y = L ⊔ L₂ := by
  have hcommLR : ∀ a ∈ L, ∀ b ∈ L₂, a * b = b * a := fun a ha b hb =>
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) ha b hb).symm
  have hcard9 : Nat.card ↥(L ⊔ L₂) = 9 := by
    rw [s16h_z3_card_sup_eq hcommLR hinf, hL, hL₂]
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  haveI : Finite ↥L₂ := Nat.finite_of_card_ne_zero (by rw [hL₂]; norm_num)
  haveI : Finite ↥(L ⊔ L₂) := Nat.finite_of_card_ne_zero (by rw [hcard9]; norm_num)
  have hYdvd : Nat.card ↥Y ∣ 9 := by
    rw [← hcard9]
    exact Subgroup.card_dvd_of_le hY
  have hYdvd' : Nat.card ↥Y ∣ 3 ^ 2 := by simpa using hYdvd
  rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hYdvd' with ⟨k, hk, hcard_eq⟩
  interval_cases k
  ·
    left
    exact by simpa using hcard_eq
  ·
    have hYcard3 : Nat.card ↥Y = 3 := by simpa using hcard_eq
    haveI : Finite ↥Y := Nat.finite_of_card_ne_zero (by rw [hYcard3]; norm_num)
    have hYne : Y ≠ ⊥ := by
      intro hbot
      rw [hbot] at hYcard3
      simp at hYcard3
    obtain ⟨y, hyY, hy_ne⟩ := (Subgroup.bot_or_exists_ne_one Y).resolve_left hYne
    obtain ⟨a, ha, b, hb, hy_eq⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommLR (hY hyY)
    have ha3 : a ^ 3 = 1 := (s16h_isElemAbelian_three_of_card hL).2 a ha
    have hb3 : b ^ 3 = 1 := (s16h_isElemAbelian_three_of_card hL₂).2 b hb
    have hyord : orderOf y = 3 := by
      have hdvd : orderOf y ∣ 3 := by
        rw [← hYcard3]
        exact Subgroup.orderOf_dvd_natCard Y hyY
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hy_ne
      · exact h3
    have hYeq : Y = Subgroup.zpowers y := by
      symm
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyY)
        (by simp [Nat.card_zpowers, hyord, hYcard3])
    have hτy : τ * y * τ⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hτY y).mp hyY
    rcases hτ with ⟨hτinv, hτcen⟩ | ⟨hτinv, hτcen⟩
    ·
      have hτy_eq : τ * y * τ⁻¹ = a⁻¹ * b := by
        rw [← hy_eq]
        calc τ * (a * b) * τ⁻¹ = (τ * a * τ⁻¹) * (τ * b * τ⁻¹) := by group
          _ = a⁻¹ * b := by rw [hτinv a ha, hτcen b hb]; group
      have haY : a ∈ Y := by
        have h1 : (τ * y * τ⁻¹) * y⁻¹ ∈ Y := Y.mul_mem hτy (Y.inv_mem hyY)
        have h2 : (τ * y * τ⁻¹) * y⁻¹ = a := by
          rw [hτy_eq, ← hy_eq, mul_inv_rev]
          rw [show (a⁻¹ * b) * (b⁻¹ * a⁻¹) = a⁻¹ * a⁻¹ by group]
          exact s16h_z3_inv_mul_inv ha3
        rwa [h2] at h1
      by_cases ha1 : a = 1
      ·
        right; right; left
        have hyL2 : y ∈ L₂ := by
          rw [← hy_eq, ha1, one_mul]
          exact hb
        have hzple : Subgroup.zpowers y ≤ L₂ := Subgroup.zpowers_le.mpr hyL2
        have hEq : Subgroup.zpowers y = L₂ :=
          Subgroup.eq_of_le_of_card_ge hzple (by simp [Nat.card_zpowers, hyord, hL₂])
        rw [hYeq, hEq]
      ·
        right; left
        have hazp : Subgroup.zpowers a = L := by
          have hle : Subgroup.zpowers a ≤ L := Subgroup.zpowers_le.mpr ha
          refine Subgroup.eq_of_le_of_card_ge hle ?_
          have haord : orderOf a = 3 := by
            have hdvd : orderOf a ∣ 3 := by
              rw [← hL]
              exact Subgroup.orderOf_dvd_natCard L ha
            rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
            · exact absurd (orderOf_eq_one_iff.mp h1) ha1
            · exact h3
          simp [Nat.card_zpowers, haord, hL]
        have hLY : L ≤ Y := by
          rw [← hazp]
          exact Subgroup.zpowers_le.mpr haY
        exact (Subgroup.eq_of_le_of_card_ge hLY (by simp [hYcard3, hL])).symm
    ·
      have hτy_eq : τ * y * τ⁻¹ = a * b⁻¹ := by
        rw [← hy_eq]
        calc τ * (a * b) * τ⁻¹ = (τ * a * τ⁻¹) * (τ * b * τ⁻¹) := by group
          _ = a * b⁻¹ := by rw [hτcen a ha, hτinv b hb]; group
      have hbY : b ∈ Y := by
        have h1 : y⁻¹ * (τ * y * τ⁻¹) ∈ Y := Y.mul_mem (Y.inv_mem hyY) hτy
        have h2 : y⁻¹ * (τ * y * τ⁻¹) = b := by
          rw [hτy_eq, ← hy_eq, mul_inv_rev]
          rw [show (b⁻¹ * a⁻¹) * (a * b⁻¹) = b⁻¹ * b⁻¹ by group]
          exact s16h_z3_inv_mul_inv hb3
        rwa [h2] at h1
      by_cases hb1 : b = 1
      ·
        right; left
        have hyL : y ∈ L := by
          rw [← hy_eq, hb1, mul_one]
          exact ha
        have hzple : Subgroup.zpowers y ≤ L := Subgroup.zpowers_le.mpr hyL
        have hEq : Subgroup.zpowers y = L :=
          Subgroup.eq_of_le_of_card_ge hzple (by simp [Nat.card_zpowers, hyord, hL])
        rw [hYeq, hEq]
      ·
        right; right; left
        have hbzp : Subgroup.zpowers b = L₂ := by
          have hle : Subgroup.zpowers b ≤ L₂ := Subgroup.zpowers_le.mpr hb
          refine Subgroup.eq_of_le_of_card_ge hle ?_
          have hbord : orderOf b = 3 := by
            have hdvd : orderOf b ∣ 3 := by
              rw [← hL₂]
              exact Subgroup.orderOf_dvd_natCard L₂ hb
            rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
            · exact absurd (orderOf_eq_one_iff.mp h1) hb1
            · exact h3
          simp [Nat.card_zpowers, hbord, hL₂]
        have hL2Y : L₂ ≤ Y := by
          rw [← hbzp]
          exact Subgroup.zpowers_le.mpr hbY
        exact (Subgroup.eq_of_le_of_card_ge hL2Y (by simp [hYcard3, hL₂])).symm
  ·
    right; right; right
    have hYcard9 : Nat.card ↥Y = 9 := by simpa using hcard_eq
    exact Subgroup.eq_of_le_of_card_ge hY (by simp [hcard9, hYcard9])

theorem s16h_z3_xbar_irr {X : Type*} [Group X] [Finite X] {A L L₂ T : Subgroup X} {x t : X}
    (hxA : x ∈ A) (hL₂ : L₂ = L.map (MulAut.conj x).toMonoidHom) (hne : L₂ ≠ L)
    (hL : Nat.card ↥L = 3)
    (hperm : ∀ g ∈ A,
      (L.map (MulAut.conj g).toMonoidHom = L ∧ L₂.map (MulAut.conj g).toMonoidHom = L₂) ∨
      (L.map (MulAut.conj g).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj g).toMonoidHom = L))
    (hcomm : ⁅L, L₂⁆ = ⊥) (hinf : L ⊓ L₂ = ⊥) (htA : t ∈ A) (ht2 : t ^ 2 = 1)
    (htinv : ∀ l ∈ L, t * l * t⁻¹ = l⁻¹) (htc : ∀ l ∈ L₂, t * l = l * t)
    (hT : IsSylowIn 2 T A) :
    ∀ Y : Subgroup X, Y ≤ L ⊔ L₂ → T ≤ normalizer (Y : Set X) → Y = ⊥ ∨ Y = L ⊔ L₂ := by
  intro Y hY hTY
  obtain ⟨σ, hσT, hσL, hσL₂⟩ := s16h_z3_exists_swap_mem_sylow hxA hL₂ hne hperm hT
  obtain ⟨τ, hτT, hτ⟩ := s16h_z3_exists_tau_mem_sylow hperm htA ht2 htinv htc hT
  have hL₂c : Nat.card ↥L₂ = 3 := by
    rw [hL₂, Subgroup.card_map_of_injective (MulAut.conj x).injective, hL]
  have hσN : ∀ Z : Subgroup X, Y = Z → Z.map (MulAut.conj σ).toMonoidHom = Z := fun Z hZ => by
    subst hZ
    simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTY hσT)
  rcases s16h_z3_sub_of_invariant hL hL₂c hcomm hinf hτ hY (hTY hτT) with h | h | h | h
  · exact Or.inl h
  · exact absurd (hσL.symm.trans (hσN L h)) hne
  · exact absurd (hσL₂.symm.trans (hσN L₂ h)) hne.symm
  · exact Or.inr h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
