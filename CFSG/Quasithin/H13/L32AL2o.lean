module

public import CFSG.Quasithin.H13.L32AL2l

public section

namespace CFSG.Quasithin.H13.L32A.L2

open Equiv CFSG.Quasithin

theorem commSub_eq_of_fixV_eq {W' : Type} [CommGroup W'] [Finite W'] (hV : ∀ w : W', w ^ 2 = 1)
    {a₁ a₂ : MulAut W'} {m₁ m₂ : ℕ} (hm₁ : Odd m₁) (hm₂ : Odd m₂) (ha₁ : a₁ ^ m₁ = 1)
    (ha₂ : a₂ ^ m₂ = 1) (hc : a₁ * a₂ = a₂ * a₁)
    (hfix : fixV (Subgroup.zpowers a₁) = fixV (Subgroup.zpowers a₂)) :
    commSub ⊤ (Subgroup.zpowers a₁) = commSub ⊤ (Subgroup.zpowers a₂) := by
  have key : ∀ {b₁ b₂ : MulAut W'} {n₁ n₂ : ℕ}, Odd n₁ → Odd n₂ → b₁ ^ n₁ = 1 → b₂ ^ n₂ = 1 →
      b₁ * b₂ = b₂ * b₁ → fixV (Subgroup.zpowers b₁) = fixV (Subgroup.zpowers b₂) →
      commSub ⊤ (Subgroup.zpowers b₂) ≤ commSub ⊤ (Subgroup.zpowers b₁) := by
    intro b₁ b₂ n₁ n₂ hn₁ hn₂ hb₁ hb₂ hbc hbf
    have hbc' : Commute b₁ b₂ := hbc
    obtain ⟨-, hinf₂, -, -⟩ := B1.zpowers_decomp hV hn₂ hb₂
    have hinv : ∀ y ∈ Subgroup.zpowers b₁, ∀ m ∈ commSub ⊤ (Subgroup.zpowers b₂),
        y m ∈ commSub ⊤ (Subgroup.zpowers b₂) := by
      intro y hy m hm
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine B1.commSub_smul_mem (b₁ ^ j) (fun z hz => ?_) (fun _ _ => Subgroup.mem_top _) m hm
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [((hbc'.zpow_left j).zpow_right i).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers _ i
    have hYodd : Odd (Nat.card (Subgroup.zpowers b₁)) := by
      rw [Nat.card_zpowers]
      exact Odd.of_dvd_nat hn₁ (orderOf_dvd_of_pow_eq_one hb₁)
    obtain ⟨hsup, -⟩ := B1.coprime_decomp hV hYodd hinv
    have hbot : commSub ⊤ (Subgroup.zpowers b₂) ⊓ fixV (Subgroup.zpowers b₁) = ⊥ := by
      rw [hbf, inf_comm]
      exact hinf₂
    rw [hbot, bot_sup_eq] at hsup
    rw [← hsup]
    exact commSub_mono le_top le_rfl
  exact le_antisymm (key hm₂ hm₁ ha₂ ha₁ hc.symm hfix.symm) (key hm₁ hm₂ ha₁ ha₂ hc hfix)

namespace WrData

variable {W' : Type} [CommGroup W'] {H' P₁ P₂ : Subgroup (MulAut W')}

theorem exists_five₁ (Y : WrData H' P₁ P₂) : ∃ u ∈ P₁, u ≠ 1 ∧ u ^ 5 = 1 :=
  Y.symm.exists_five₂

variable [Finite W']

theorem not_isTransvection_of_swap (Y : WrData H' P₁ P₂) {s : MulAut W'} (hs2 : s * s = 1)
    (hsw : ∀ a ∈ P₁, s * a * s⁻¹ ∈ P₂) : ¬ IsTransvection s := by
  intro hs
  obtain ⟨y, hy, hy1, hy5⟩ := Y.exists_five₁
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hy'P : s * y * s⁻¹ ∈ P₂ := hsw y hy
  have hc : Commute y (s * y * s⁻¹) := Y.comm y hy _ hy'P
  have hss : s * (s * y * s⁻¹) * s⁻¹ = y := by
    rw [hinv]
    calc s * (s * y * s) * s = (s * s) * y * (s * s) := by group
      _ = y := by rw [hs2, one_mul, mul_one]
  have hx5 : (y * (s * y * s⁻¹)⁻¹) ^ 5 = 1 := by
    rw [hc.inv_right.mul_pow, hy5, one_mul, inv_pow, conj_pow, hy5, mul_one, mul_inv_cancel,
      inv_one]
  have hx1 : y * (s * y * s⁻¹)⁻¹ ≠ 1 := by
    intro h
    have he : y = s * y * s⁻¹ := mul_inv_eq_one.mp h
    have hm : y ∈ P₁ ⊓ P₂ := Subgroup.mem_inf.mpr ⟨hy, he ▸ hy'P⟩
    rw [Y.inf, Subgroup.mem_bot] at hm
    exact hy1 hm
  have hsx : s * (y * (s * y * s⁻¹)⁻¹) * s⁻¹ = (y * (s * y * s⁻¹)⁻¹)⁻¹ := by
    have e1 : s * (y * (s * y * s⁻¹)⁻¹) * s⁻¹ =
        (s * y * s⁻¹) * (s * (s * y * s⁻¹) * s⁻¹)⁻¹ := by group
    rw [e1, hss, mul_inv_rev, inv_inv]
  exact false_of_inv_five (fun w => by rw [pow_two]; exact Y.sq w) hs hx5 hx1 hsx

theorem four_le_card_range (Y : WrData H' P₁ P₂) {s : MulAut W'} (hs2 : s * s = 1)
    (hs1 : s ≠ 1) (hsw : ∀ a ∈ P₁, s * a * s⁻¹ ∈ P₂) : 4 ≤ Nat.card (commHom s).range := by
  have hnt := Y.not_isTransvection_of_swap hs2 hsw
  have hdvd : Nat.card (commHom s).range ∣ 2 ^ 8 := by
    have := Subgroup.card_subgroup_dvd_card (commHom s).range
    rwa [Y.card] at this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  by_contra hlt
  push Not at hlt
  have hk2 : k < 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hmove : ∃ w : W', s w ≠ w := by
    by_contra h
    push Not at h
    exact hs1 (MulEquiv.ext h)
  obtain ⟨w, hw1⟩ := hmove
  have hw : commHom s w ≠ 1 := by rw [commHom_apply, Ne, mul_inv_eq_one]; exact hw1
  interval_cases k
  · have h1 : (commHom s).range = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hk]; norm_num)
    have hmem : commHom s w ∈ (commHom s).range := ⟨w, rfl⟩
    rw [h1, Subgroup.mem_bot] at hmem
    exact hw hmem
  · apply hnt
    refine ⟨hs1, commHom s w, hw, fun v => ?_⟩
    by_cases hv : s v = v
    · exact Or.inl hv
    · right
      have hv' : commHom s v ≠ 1 := by rw [commHom_apply, Ne, mul_inv_eq_one]; exact hv
      have he := eq_of_card_le_two (Z := (commHom s).range) (by rw [hk]; norm_num)
        ⟨v, rfl⟩ ⟨w, rfl⟩ hv' hw
      rw [commHom_apply, commHom_apply] at he
      calc s v = s v * v⁻¹ * v := by rw [inv_mul_cancel_right]
        _ = (s w * w⁻¹) * v := by rw [he]
        _ = v * (commHom s w) := by rw [mul_comm, commHom_apply]

end WrData

end CFSG.Quasithin.H13.L32A.L2
