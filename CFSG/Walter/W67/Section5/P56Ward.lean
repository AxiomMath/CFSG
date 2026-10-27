module

public import CFSG.Walter.W67.Section5.Prop56N

public section

namespace CFSG.Walter.W67

open scoped commutatorElement MatrixGroups
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec56

theorem le_of_coprime_trivial {Q M R₀ : Subgroup G} (hQ3 : IsPGroup 3 Q) (hMQ : M ≤ Q)
    (hR₀3 : ¬ 3 ∣ Nat.card R₀) (hR₀Q : R₀ ≤ Subgroup.normalizer (Q : Set G))
    (hR₀M : R₀ ≤ Subgroup.normalizer (M : Set G)) (hQM : Q ≤ Subgroup.normalizer (M : Set G))
    (htriv : ∀ r ∈ R₀, ∀ y ∈ Q, r * y * r⁻¹ * y⁻¹ ∈ M)
    (hfix : ∀ y ∈ Q, (∀ r ∈ R₀, r * y = y * r) → y ∈ M) : Q ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let := JT.conjAct R₀ Q hR₀Q
  have hM'n : (M.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMQ).mpr hQM
  have hinv : CFSG.IsInvariant R₀ Q (M.subgroupOf Q) := ⟨fun r a => by
    change (a : G) ∈ M ↔ (r : G) * a * (r : G)⁻¹ ∈ M
    exact Subgroup.mem_normalizer_iff.mp (hR₀M r.2) a⟩
  have hM'3 : IsPGroup 3 (M.subgroupOf Q) := hQ3.to_subgroup _
  have hsolv : Group.IsSolvable (M.subgroupOf Q) := by
    have := hM'3.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card R₀) (Nat.card (M.subgroupOf Q)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hM'3
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR₀3)))
  have key := SolvableHall.coprime_solvable_kernel_fixed_point_lifting (G := Q) (A := R₀)
    (M.subgroupOf Q) hinv hsolv hcop
  let : MulDistribMulAction R₀ (Q ⧸ M.subgroupOf Q) :=
    quotientMulDistribMulAction (A := R₀) (G := Q) (M.subgroupOf Q) hinv
  let : MulAction.QuotientAction R₀ (M.subgroupOf Q) :=
    quotientAction_of_isInvariant (A := R₀) (M.subgroupOf Q) hinv
  intro y hy
  have hvfix : ((⟨y, hy⟩ : Q) : Q ⧸ M.subgroupOf Q) ∈
      fixedPointSubgroup R₀ (Q ⧸ M.subgroupOf Q) := by
    rw [FixedPoints.mem_subgroup]
    intro r
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
    change ((r : G) * y * (r : G)⁻¹)⁻¹ * y ∈ M
    have h1 := htriv r r.2 y⁻¹ (Q.inv_mem hy)
    have h2 : ((r : G) * y * (r : G)⁻¹)⁻¹ * y = (r : G) * y⁻¹ * (r : G)⁻¹ * y⁻¹⁻¹ := by group
    rw [h2]
    exact h1
  rw [key] at hvfix
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hvfix
  have haM : (a : G) ∈ M := hfix a a.2 fun r hr => by
    have h1 : (r : G) * a * (r : G)⁻¹ = a :=
      congrArg Subtype.val ((FixedPoints.mem_subgroup R₀ Q a).mp ha ⟨r, hr⟩)
    calc (r : G) * a = (r : G) * a * (r : G)⁻¹ * r := by group
      _ = a * r := by rw [h1]
  have hay' : ((a : Q) : Q ⧸ M.subgroupOf Q) = ((⟨y, hy⟩ : Q) : Q ⧸ M.subgroupOf Q) := hay
  have h3 : a⁻¹ * (⟨y, hy⟩ : Q) ∈ M.subgroupOf Q := QuotientGroup.eq.mp hay'
  rw [Subgroup.mem_subgroupOf] at h3
  have h4 := M.mul_mem haM h3
  simpa using h4

end Sec56

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

theorem B_ne_bot : f5.B ≠ ⊥ := by
  intro h
  have h1 := f5.card_B
  rw [h, Subgroup.card_bot] at h1
  have := s.three_lt_q
  omega

omit f5 in
theorem _root_.CFSG.Walter.W67.Std.H_le_normalizer_K (s : Std G) :
    s.H ≤ Subgroup.normalizer (s.K : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer s.K_le_H).mp s.normal

omit f5 in
theorem _root_.CFSG.Walter.W67.Std.card_le_q_of_le_K (s : Std G) (hp : s.p = 3) {Q : Subgroup G}
    (hQ : IsPGroup 3 Q) (hQK : Q ≤ s.K) :
    Nat.card Q ≤ s.q := by
  have hdvd := Subgroup.card_dvd_of_le hQK
  have hFcard : Nat.card (GaloisField s.p s.f) = s.p ^ s.f := GaloisField.card _ _ s.f_pos.ne'
  rw [Nat.card_congr s.iso.toEquiv, psl2_card_formula _ ⟨s.p, s.f, Fact.out, s.odd_p,
    s.f_pos, hFcard⟩, hFcard, hp] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  rw [hk] at hdvd ⊢
  rw [Hyp.q, hp]
  have hev := Borel5.even_mul_sq_sub_one (Odd.pow (by decide : Odd 3) : Odd (3 ^ s.f))
  have h1 : 3 ^ k ∣ 3 ^ s.f * ((3 ^ s.f) ^ 2 - 1) :=
    hdvd.trans (Nat.div_dvd_of_dvd (even_iff_two_dvd.mp hev))
  have hcop : Nat.Coprime (3 ^ k) ((3 ^ s.f) ^ 2 - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    have h3 : 3 ∣ (3 ^ s.f) ^ 2 := dvd_pow (dvd_pow_self 3 s.f_pos.ne') two_ne_zero
    have := Nat.dvd_sub h3 h
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by positivity))] at this
    norm_num at this
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right h1)

theorem inf_H_eq_P₁ (hp : s.p = 3) {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hP₁Q : f5.P₁ ≤ Q)
    (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hfpf : ∀ b ∈ f5.B, b ≠ 1 → ∀ y ∈ Q, b * y = y * b → y = 1) : Q ⊓ s.H = f5.P₁ := by
  have hHK := s.H_le_normalizer_K
  have hBH : f5.B ≤ s.H := f5.B_le.trans s.K_le_H
  have hQ₁3 : IsPGroup 3 (Q ⊓ s.H : Subgroup G) := hQ.to_le inf_le_left
  have hBQ₁ : f5.B ≤ Subgroup.normalizer ((Q ⊓ s.H : Subgroup G) : Set G) := fun b hb =>
    Sec54.mem_normalizer_inf (hBQ hb) (Subgroup.le_normalizer (hBH hb))
  obtain ⟨b₀, hb₀, hb₀1⟩ := (Subgroup.bot_or_exists_ne_one f5.B).resolve_left f5.B_ne_bot
  have hle : (Q ⊓ s.H : Subgroup G) ≤ s.K := by
    have := Sec56.le_of_coprime_trivial (Q := Q ⊓ s.H) (M := Q ⊓ s.H ⊓ s.K) (R₀ := f5.B) hQ₁3
      inf_le_left (f5.three_not_dvd_B hp) hBQ₁
      (fun b hb => Sec54.mem_normalizer_inf (hBQ₁ hb) (Subgroup.le_normalizer (f5.B_le hb)))
      (fun y hy => Sec54.mem_normalizer_inf (Subgroup.le_normalizer hy)
        (hHK (Subgroup.mem_inf.mp hy).2))
      (fun b hb y hy => by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hBQ₁ hb) y).mp hy)
            (Subgroup.inv_mem _ hy)
        · have h1 : y * b⁻¹ * y⁻¹ ∈ s.K :=
            (Subgroup.mem_normalizer_iff.mp (hHK (Subgroup.mem_inf.mp hy).2) b⁻¹).mp
              (s.K.inv_mem (f5.B_le hb))
          rw [show b * y * b⁻¹ * y⁻¹ = b * (y * b⁻¹ * y⁻¹) by group]
          exact s.K.mul_mem (f5.B_le hb) h1)
      (fun y hy hyB => by
        have := hfpf b₀ hb₀ hb₀1 y (Subgroup.mem_inf.mp hy).1 (hyB b₀ hb₀)
        rw [this]
        exact Subgroup.one_mem _)
    exact this.trans inf_le_right
  have hP₁le : f5.P₁ ≤ Q ⊓ s.H := le_inf hP₁Q (f5.P₁_le.trans s.K_le_H)
  symm
  apply Subgroup.eq_of_le_of_card_ge hP₁le
  rw [f5.card_P₁]
  exact s.card_le_q_of_le_K hp hQ₁3 hle

end Frame5

end CFSG.Walter.W67
