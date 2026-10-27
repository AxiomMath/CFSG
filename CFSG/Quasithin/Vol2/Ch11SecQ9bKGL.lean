module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGK
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace C11P9B

theorem eq_one_of_centralizes {Q : Type} [Group Q] [Finite Q] {S : Subgroup Q} {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hK : Nat.card K = p)
    (e : ↥S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) {B : Subgroup Q} (hBS : B ≤ S)
    (hB60 : Nat.card B = 60) (hBns : ¬ Group.IsSolvable B)
    (hZB : ∀ b ∈ B, (∀ c ∈ B, b * c = c * b) → b = 1) {s₀ : Q} (hs₀S : s₀ ∈ S)
    (hs₀3 : s₀ ^ 3 = 1) (hcomm : ∀ b ∈ B, s₀ * b = b * s₀) : s₀ = 1 := by
  let φ : ↥B × ↥(Subgroup.zpowers s₀) →* Q :=
    MonoidHom.noncommCoprod B.subtype (Subgroup.zpowers s₀).subtype (fun b c => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp c.2
      show Commute (b : Q) (c : Q)
      rw [← hk]
      exact Commute.zpow_right (hcomm b b.2).symm k)
  have hBJ : B ≤ φ.range := fun b hb => ⟨(⟨b, hb⟩, 1), by simp [φ]⟩
  have hs₀J : s₀ ∈ φ.range := ⟨(1, ⟨s₀, Subgroup.mem_zpowers s₀⟩), by simp [φ]⟩
  have hJS : φ.range ≤ S := by
    rintro _ ⟨⟨b, c⟩, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp c.2
    have hc : (c : Q) ∈ S := by
      rw [← hk]
      exact S.zpow_mem hs₀S k
    simpa [φ] using S.mul_mem (hBS b.2) hc
  have hJcard : Nat.card φ.range ∣ 180 := by
    have h1 := Subgroup.card_range_dvd φ
    rw [Nat.card_prod, hB60, Nat.card_zpowers] at h1
    exact h1.trans (Nat.mul_dvd_mul_left 60 (orderOf_dvd_of_pow_eq_one hs₀3))
  have hJp : ¬ p ∣ Nat.card φ.range := by
    intro h
    have h180 : p ∣ 2 ^ 2 * 3 ^ 2 * 5 := by
      have := h.trans hJcard
      norm_num
      exact this
    rcases (Nat.Prime.dvd_mul hp).mp h180 with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
  have hJns : ¬ Group.IsSolvable φ.range := fun hs =>
    hBns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hBJ)
      (Subgroup.inclusion_injective hBJ))
  have hJ60 := card_eq_sixty_of_le hp hK e hJS hJp hJns
  have hJB : B = φ.range := Subgroup.eq_of_le_of_card_ge hBJ (by rw [hJ60, hB60])
  rw [← hJB] at hs₀J
  exact hZB s₀ hs₀J fun c hc => hcomm c hc

end C11P9B

open C11P9B

theorem factCentL2p_holds : FactCentL2p := by
  intro Q _ _ S hSn ⟨p, hp, hp11, hS⟩ B hBS ⟨F, _, _, hF, ⟨eB⟩⟩ x hx3 hxsc s hs
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_psl2_equiv hS
  obtain ⟨hBns, k, hBk⟩ := facts_of_SL2_four hF eB
  have hBp : ¬ p ∣ Nat.card B := by
    intro h
    rw [hBk] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · have h60 : p ∣ 2 ^ 2 * 3 * 5 := by norm_num; exact h1
      rcases (Nat.Prime.dvd_mul hp).mp h60 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
          omega
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h1)
      omega
  have hB60 := card_eq_sixty_of_le hp hK e hBS hBp hBns
  obtain ⟨hP, hZ⟩ := pCore_eq_bot_of_card hF eB hB60
  have hPB : pCoreOf 2 B = ⊥ := by
    rw [pCoreOf, hP, Subgroup.map_bot]
  have hxB : ∀ b ∈ B, x * b = b * x := by
    intro b hb
    have h1 := hxsc.2.2 b hb
    rw [hPB, Subgroup.mem_bot] at h1
    have h2 : x * b * x⁻¹ = b := by
      calc x * b * x⁻¹ = x * b * x⁻¹ * b⁻¹ * b := by group
        _ = b := by rw [h1, one_mul]
    calc x * b = x * b * x⁻¹ * x := by group
      _ = b * x := by rw [h2]
  have hx3' : x ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
  obtain ⟨s₀, hs₀S, hs₀3, hconj⟩ := exists_inner_of_order_three hp (by omega) hK e hx3'
  have hs₀B : ∀ b ∈ B, s₀ * b = b * s₀ := by
    intro b hb
    have h1 := hconj b (hBS hb)
    have h2 : x * b * x⁻¹ = b := by rw [hxB b hb]; group
    rw [h2] at h1
    calc s₀ * b = s₀ * b * s₀⁻¹ * s₀ := by group
      _ = b * s₀ := by rw [← h1]
  have hZB : ∀ b ∈ B, (∀ c ∈ B, b * c = c * b) → b = 1 := by
    intro b hb hbc
    have := hZ ⟨b, hb⟩ fun c => Subtype.ext (hbc c c.2)
    exact congrArg Subtype.val this
  have hs₀1 := eq_one_of_centralizes hp (by omega) hK e hBS hB60
    (fun hsol => hBns hsol) hZB hs₀S hs₀3 hs₀B
  have h1 := hconj s hs
  rw [hs₀1, one_mul, inv_one, mul_one] at h1
  calc x * s = x * s * x⁻¹ * x := by group
    _ = s * x := by rw [h1]

end CFSG.Quasithin.Vol2.Ch11.SecA
