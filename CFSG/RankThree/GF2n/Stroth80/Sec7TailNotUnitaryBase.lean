module

public import CFSG.RankThree.GF2n.Stroth80.Sec7ArtinOrders
public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def UnitarySixLeviStatement : Prop :=
  ∀ (q : ℕ), (∃ f : ℕ, 1 ≤ f ∧ q = 2 ^ f) → ∀ (Y : Type) [Group Y] [Finite Y] (U : Subgroup Y),
    IsPSUModel 6 q ↥U → ∀ A : Subgroup Y, A ≤ U → A ≠ ⊥ → IsPGroup 2 A →
      ∃ P O : Subgroup Y, P ≤ U ∧ O ≤ P ∧ A ≤ O ∧ IsPGroup 2 O ∧
        (∀ p ∈ P, ∀ o ∈ O, p * o * p⁻¹ ∈ O) ∧
        (∀ g ∈ U, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ P) ∧
        ∀ S : Subgroup Y, S ≤ P → commutator ↥S = ⊤ →
          Nat.card S ∣ Nat.card ↥(S ⊓ O) * (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) ∨
          Nat.card S ∣ Nat.card ↥(S ⊓ O) * (q ^ 3 * (q ^ 2 - 1) * (q ^ 4 - 1)) ∨
          Nat.card S ∣ Nat.card ↥(S ⊓ O) * (q ^ 6 * (q ^ 4 - 1) * (q ^ 6 - 1))

theorem notUnitary_arith {q : ℕ} (hq4 : 4 ≤ q) :
    ¬ (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) ∣
        q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) ∧
    ¬ (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 4 - 1)) ∧
    ¬ (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) ∣ q ^ 6 * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  have h16 : 16 ≤ q ^ 2 := by
    calc (16 : ℕ) = 4 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq4 2
  have h64 : 64 ≤ q ^ 3 := by
    calc (64 : ℕ) = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
  have h256 : 256 ≤ q ^ 4 := by
    calc (256 : ℕ) = 4 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq4 4
  have h4q : 4 * q ≤ q ^ 2 := by nlinarith
  have hq0 : 0 < q := by omega
  have hpos3 : 0 < q ^ 3 := pow_pos hq0 3
  have hpos6 : 0 < q ^ 6 := pow_pos hq0 6
  obtain ⟨A, hA⟩ : ∃ A, q ^ 2 - 1 = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, q ^ 3 - 1 = B := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, q ^ 4 - 1 = C := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, q ^ 6 - 1 = D := ⟨_, rfl⟩
  have hA2 : q ^ 2 = A + 1 := by omega
  have hB2 : q ^ 3 = B + 1 := by omega
  have hC2 : q ^ 4 = C + 1 := by omega
  have hD2 : q ^ 6 = D + 1 := by omega
  have hA_pos : 0 < A := by omega
  have hB_pos : 63 ≤ B := by omega
  have hC_pos : 0 < C := by omega
  rw [hA, hB, hC, hD]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hc : 0 < q ^ 6 * A * C := Nat.mul_pos (Nat.mul_pos hpos6 hA_pos) hC_pos
    have e1 : q ^ 6 * A * B * C = q ^ 6 * A * C * B := by ring
    have e2 : q ^ 6 * A * (q ^ 3 + 1) * C = q ^ 6 * A * C * (q ^ 3 + 1) := by ring
    rw [e1, e2] at h
    have hB' : B ∣ q ^ 3 + 1 := Nat.dvd_of_mul_dvd_mul_left hc h
    have e3 : q ^ 3 + 1 = B + 2 := by omega
    rw [e3] at hB'
    have h2 := Nat.dvd_sub hB' (Nat.dvd_refl B)
    rw [Nat.add_sub_cancel_left] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  · intro h
    have hX : 0 < q ^ 3 * A * C := Nat.mul_pos (Nat.mul_pos hpos3 hA_pos) hC_pos
    have hY0 : 2 * 1 ≤ q ^ 3 * B := Nat.mul_le_mul (by omega) (by omega)
    have hY : 2 ≤ q ^ 3 * B := by omega
    have e1 : q ^ 6 * A * B * C = q ^ 3 * A * C * (q ^ 3 * B) := by ring
    rw [e1] at h
    have hle := Nat.le_of_dvd hX h
    have hmul : q ^ 3 * A * C * 2 ≤ q ^ 3 * A * C * (q ^ 3 * B) :=
      Nat.mul_le_mul (Nat.le_refl _) hY
    linarith
  · intro h
    have hDB : D = B * (B + 2) := by
      have hsq : q ^ 6 = (q ^ 3) ^ 2 := by ring
      rw [hB2] at hsq
      nlinarith [hsq, hD2]
    have e3 : q ^ 3 + 1 = B + 2 := by omega
    have hDB' : D = B * (q ^ 3 + 1) := by rw [e3]; exact hDB
    have hc : 0 < q ^ 6 * C * B := Nat.mul_pos (Nat.mul_pos hpos6 hC_pos) (by omega)
    have e1 : q ^ 6 * A * B * C = q ^ 6 * C * B * A := by ring
    have e2 : q ^ 6 * C * D = q ^ 6 * C * B * (q ^ 3 + 1) := by rw [hDB']; ring
    rw [e1, e2] at h
    have hA' : A ∣ q ^ 3 + 1 := Nat.dvd_of_mul_dvd_mul_left hc h
    have hq3A : q ^ 3 = q * A + q := by
      rw [show q ^ 3 = q * q ^ 2 by ring, hA2]
      ring
    have hq3A' : q ^ 3 + 1 = q * A + (q + 1) := by omega
    rw [hq3A'] at hA'
    have h1 := Nat.dvd_sub hA' (Nat.dvd_mul_left A q)
    rw [Nat.add_sub_cancel_left] at h1
    have h2 := Nat.le_of_dvd (by omega) h1
    omega

theorem card_L4_eq_of_even {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q)
    (hq2 : ∃ f : ℕ, 1 ≤ f ∧ q = 2 ^ f) :
    Nat.card (StatedProj (StatedSL 4 K)) = q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) := by
  obtain ⟨f, hf, hq⟩ := hq2
  have hq1 : 1 ≤ q := by
    rw [hq]
    exact Nat.one_le_two_pow
  have hq2dvd : 2 ∣ q := by
    rw [hq]
    exact dvd_pow_self 2 (by omega)
  have hodd : Odd (q - 1) := Nat.odd_iff.mpr (by omega)
  have hcop2 : Nat.Coprime 2 (q - 1) := Nat.coprime_two_left.mpr hodd
  have hg : Nat.gcd 4 (q - 1) = 1 := by
    have h22 : Nat.Coprime (2 ^ 2) (q - 1) := Nat.Coprime.pow_left 2 hcop2
    exact h22
  have h := card_statedProj_statedSL_mul_gcd (K := K) (a := 4) (by norm_num)
  have hI : Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) := by decide
  have h23 : (2 : ℕ) ∉ ({3, 4} : Finset ℕ) := by decide
  have h34 : (3 : ℕ) ∉ ({4} : Finset ℕ) := by decide
  rw [hI, Finset.prod_insert h23, Finset.prod_insert h34, Finset.prod_singleton,
    show 4 * (4 - 1) / 2 = 6 by norm_num, hK, hg, mul_one] at h
  rw [h]
  ring

theorem exists_surj_ker_eq_one {Y : Type} [Group Y] {E N R : Subgroup Y}
    (hER : E ≤ R) (hNR : N ≤ R) (hEN : E ⊔ N = R) [(N.subgroupOf R).Normal]
    {S : Type} [Group S] (eRN : (↥R ⧸ N.subgroupOf R) ≃* S) :
    ∃ θ : ↥E →* S, Function.Surjective θ ∧ ∀ e : ↥E, θ e = 1 ↔ (e : Y) ∈ N := by
  classical
  let θ : ↥E →* S :=
    eRN.toMonoidHom.comp ((QuotientGroup.mk' (N.subgroupOf R)).comp (Subgroup.inclusion hER))
  have hθ : ∀ e : ↥E, θ e = eRN (QuotientGroup.mk (⟨(e : Y), hER e.2⟩ : ↥R)) := fun e => rfl
  refine ⟨θ, ?_, ?_⟩
  · intro s
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (eRN.symm s)
    have hsup : E.subgroupOf R ⊔ N.subgroupOf R = ⊤ := by
      apply Subgroup.map_injective R.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hER,
        Subgroup.map_subgroupOf_eq_of_le hNR, hEN, Subgroup.map_top, Subgroup.range_subtype]
    have hcm : c ∈ E.subgroupOf R ⊔ N.subgroupOf R := by
      rw [hsup]
      exact Subgroup.mem_top c
    obtain ⟨e₁, he₁, n₁, hn₁, hen⟩ := Subgroup.mem_sup_of_normal_right.mp hcm
    refine ⟨⟨(e₁ : Y), Subgroup.mem_subgroupOf.mp he₁⟩, ?_⟩
    rw [hθ]
    have h1 : (QuotientGroup.mk c : ↥R ⧸ N.subgroupOf R) = QuotientGroup.mk e₁ := by
      rw [← hen, QuotientGroup.mk_mul]
      have h3 : (QuotientGroup.mk n₁ : ↥R ⧸ N.subgroupOf R) = 1 :=
        (QuotientGroup.eq_one_iff n₁).mpr hn₁
      rw [h3, mul_one]
    have h2 : (⟨(e₁ : Y), hER (Subgroup.mem_subgroupOf.mp he₁)⟩ : ↥R) = e₁ := rfl
    show eRN (QuotientGroup.mk (⟨(e₁ : Y), _⟩ : ↥R)) = s
    rw [h2, ← h1, hc]
    exact eRN.apply_symm_apply s
  · intro e
    rw [hθ, map_eq_one_iff _ eRN.injective, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem card_eq_card_inf_mul_quot {Y : Type} [Group Y] [Finite Y] {E N R : Subgroup Y} (hER : E ≤ R)
    (hNR : N ≤ R) (hEN : E ⊔ N = R) [(N.subgroupOf R).Normal] {S : Type} [Group S]
    (eRN : (↥R ⧸ N.subgroupOf R) ≃* S) : Nat.card ↥E = Nat.card ↥(E ⊓ N) * Nat.card S := by
  obtain ⟨θ, hsurj, hθx⟩ := exists_surj_ker_eq_one hER hNR hEN eRN
  have hker : θ.ker = (E ⊓ N).subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hθx]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hcard_ker : Nat.card ↥θ.ker = Nat.card ↥(E ⊓ N) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hquot : Nat.card (↥E ⧸ θ.ker) = Nat.card S :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hsurj).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker, hquot, hcard_ker]
  exact Nat.mul_comm _ _

theorem yNn_normalizes_subgroupOf {Γ : Type} [Group Γ] {N K H : Subgroup Γ} (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) :
    ∀ k ∈ K.subgroupOf H, k ∈ Subgroup.normalizer (N.subgroupOf H : Set ↥H) := by
  have key : ∀ k : ↥H, k ∈ K.subgroupOf H → ∀ h : ↥H, h ∈ N.subgroupOf H →
      k * h * k⁻¹ ∈ N.subgroupOf H := by
    intro k hk h hh
    have hk' : (k : Γ) ∈ K := Subgroup.mem_subgroupOf.1 hk
    have hh' : (h : Γ) ∈ N := Subgroup.mem_subgroupOf.1 hh
    have hhK : (h : Γ) ∈ K := hNK hh'
    have hconj := hN.conj_mem ⟨(h : Γ), hhK⟩ (Subgroup.mem_subgroupOf.2 hh') ⟨(k : Γ), hk'⟩
    rw [Subgroup.mem_subgroupOf] at hconj ⊢
    simpa using hconj
  intro k hk
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  refine ⟨key k hk h, fun hh => ?_⟩
  have hk_inv : k⁻¹ ∈ K.subgroupOf H := (K.subgroupOf H).inv_mem hk
  have h2 := key k⁻¹ hk_inv (k * h * k⁻¹) hh
  have heq : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
  rw [heq] at h2
  exact h2

theorem Ctx.yNn {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hNK : bar M Q (hc.CN t) ≤ bar M Q (NormH0 M Z Z0))
    (hKH : bar M Q (NormH0 M Z Z0) ≤ bar M Q (H0 M Z)) :
    ∀ k ∈ (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)),
      k ∈ Subgroup.normalizer
        (((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) :
          Subgroup ↥(bar M Q (H0 M Z))) : Set ↥(bar M Q (H0 M Z))) := by
  have hN : ((bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))).Normal := by
    have h := (CFSG.LocalCores.generalized_fitting_characteristic
      (G := ↥(bar M Q (NormH0 M Z Z0)))).2
    rw [hF] at h
    exact h
  exact yNn_normalizes_subgroupOf hNK hN

end CFSG.RankThree.GF2n.Stroth80
