module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusHDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {p : ℕ} {K : Type*} [Group K] {R : Type} [Group R] {I : Set (MulAut R)}
  {θ : K ⧸ Subgroup.center K ≃* R} {ψ : MulAut K} {E : Subgroup (MulAut K)}

private theorem ggL45_zpow_congr {M : Type*} [Group M] {x : M} {n : ℕ} (hx : x ^ n = 1)
    {a b : ℤ} (hab : a ≡ b [ZMOD (n : ℤ)]) : x ^ a = x ^ b := by
  rw [zpow_eq_zpow_iff_modEq]
  have hd : (orderOf x : ℤ) ∣ (n : ℤ) := by
    exact_mod_cast orderOf_dvd_of_pow_eq_one hx
  exact Int.modEq_of_dvd (hd.trans hab.dvd)

private theorem ggL45_c_mul_c'_modEq {s : ℕ} (hs : 2 ≤ s) {c : ℤ} {k : ℕ}
    (hc : c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s]) :
    c * (1 - (p : ℤ) ^ (s - 1) * k) ≡ 1 [ZMOD (p : ℤ) ^ s] := by
  have h1 : c * (1 - (p : ℤ) ^ (s - 1) * k) ≡
      (1 + (p : ℤ) ^ (s - 1) * k) * (1 - (p : ℤ) ^ (s - 1) * k)
        [ZMOD (p : ℤ) ^ s] :=
    Int.ModEq.mul_right (1 - (p : ℤ) ^ (s - 1) * k) hc
  have h2 : (1 + (p : ℤ) ^ (s - 1) * k) * (1 - (p : ℤ) ^ (s - 1) * k) ≡ 1
      [ZMOD (p : ℤ) ^ s] := by
    rw [Int.modEq_iff_dvd]
    have hprod : (1 + (p : ℤ) ^ (s - 1) * k) * (1 - (p : ℤ) ^ (s - 1) * k) =
        1 - ((p : ℤ) ^ (s - 1) * k) ^ 2 := by ring
    have hsub : (1 : ℤ) - (1 + (p : ℤ) ^ (s - 1) * k) * (1 - (p : ℤ) ^ (s - 1) * k) =
        ((p : ℤ) ^ (s - 1) * k) ^ 2 := by
      rw [hprod]
      ring
    rw [hsub]
    have hle : s ≤ 2 * (s - 1) := by omega
    have hdiv1 : (p : ℤ) ^ s ∣ (p : ℤ) ^ (2 * (s - 1)) := pow_dvd_pow (p : ℤ) hle
    have hu : ((p : ℤ) ^ (s - 1)) ^ 2 = (p : ℤ) ^ (2 * (s - 1)) := by
      rw [← pow_mul]
      congr 1
      omega
    refine hdiv1.trans ⟨k ^ 2, ?_⟩
    rw [show ((p : ℤ) ^ (s - 1) * k) ^ 2 = ((p : ℤ) ^ (s - 1)) ^ 2 * k ^ 2 by ring, hu]
  exact h1.trans h2

private theorem ggL45_psi_inv_zpow {s : ℕ} (hs : 2 ≤ s) {c : ℤ} {k : ℕ} {h : K}
    (hps : h ^ p ^ s = 1) (hψh : ψ h = h ^ c)
    (hc : c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s]) :
    ψ⁻¹ h = h ^ (1 - (p : ℤ) ^ (s - 1) * k) := by
  have hmod : ((p ^ s : ℕ) : ℤ) = (p : ℤ) ^ s := by push_cast; ring
  have hcc' : c * (1 - (p : ℤ) ^ (s - 1) * k) ≡ 1 [ZMOD ((p ^ s : ℕ) : ℤ)] := by
    rw [hmod]
    exact ggL45_c_mul_c'_modEq hs hc
  have hψeq : ψ (h ^ (1 - (p : ℤ) ^ (s - 1) * k)) = h := by
    rw [map_zpow, hψh, ← zpow_mul]
    have hcongr : h ^ (c * (1 - (p : ℤ) ^ (s - 1) * k)) = h ^ (1 : ℤ) :=
      ggL45_zpow_congr hps hcc'
    rw [hcongr, zpow_one]
  rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
  exact hψeq.symm

private theorem ggL45_mul_psi_inv {s : ℕ} (hs : 2 ≤ s) {c : ℤ} {k : ℕ} {h : K}
    (hps : h ^ p ^ s = 1) (hψh : ψ h = h ^ c)
    (hc : c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s]) :
    h * (ψ⁻¹ h)⁻¹ = (h ^ p ^ (s - 1)) ^ k := by
  have hψinv := ggL45_psi_inv_zpow hs hps hψh hc
  rw [hψinv]
  have hmul : h * (h ^ (1 - (p : ℤ) ^ (s - 1) * k))⁻¹ =
      h ^ ((p : ℤ) ^ (s - 1) * k) := by
    rw [show h * (h ^ (1 - (p : ℤ) ^ (s - 1) * k))⁻¹ =
        h ^ (1 : ℤ) * (h ^ (1 - (p : ℤ) ^ (s - 1) * k))⁻¹ by rw [zpow_one],
      ← zpow_sub]
    congr 1
    ring
  rw [hmul]
  rw [show (h ^ p ^ (s - 1)) ^ k = h ^ ((p : ℤ) ^ (s - 1) * k) by
    have hcast : ((p ^ (s - 1) * k : ℕ) : ℤ) = (p : ℤ) ^ (s - 1) * k := by
      push_cast
      ring
    rw [← pow_mul, ← zpow_natCast h (p ^ (s - 1) * k), ← hcast]]

private theorem ggL45_pow_pred_pow_p {s : ℕ} (hs : 2 ≤ s) {h : K}
    (hps : h ^ p ^ s = 1) : (h ^ p ^ (s - 1)) ^ p = 1 := by
  have hsp : p ^ (s - 1) * p = p ^ s := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s)]
  rw [← pow_mul, hsp, hps]

private theorem ggL45_pow_mul_pow_eq_one {M : Type*} [Monoid M] {n k : ℕ} {b : M}
    (hb : b ^ n = 1) : (b ^ k) ^ n = 1 := by
  rw [← pow_mul, Nat.mul_comm k n, pow_mul, hb, one_pow]

private theorem ggL45_inCIp_inducedAut {α : MulAut K}
    (hα : GGL45InP p θ I E α) : GGL45InCIp p I θ E (ggInducedAut θ α) := by
  refine ⟨(ggL45_inducesIn_iff θ I α).1 hα.2.2, ?_, ?_⟩
  · intro e he
    have h := congrArg (ggInducedAut θ) (hα.2.1 e he)
    simpa only [map_mul] using h
  · obtain ⟨n, hn⟩ := hα.1
    exact ⟨n, by simpa using congrArg (ggInducedAut θ) hn⟩

theorem ggL45TorusP1_of_H (hK : commutator K = ⊤) {s : ℕ} {c : ℤ} {k : ℕ}
    (hc : c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s])
    (H1 : GGL45HOne p I θ E (ggInducedAut θ ψ) s c) :
    (∀ α β : MulAut K, GGL45InP p θ I E α → GGL45InP p θ I E β → α * β = β * α) ∧
      ∀ α : MulAut K, GGL45InP p θ I E α → ψ * α * ψ⁻¹ = α ^ (1 + p ^ (s - 1) * k) := by
  constructor
  · intro α β hα hβ
    have hCIα := ggL45_inCIp_inducedAut hα
    have hCIβ := ggL45_inCIp_inducedAut hβ
    have hcomm := H1.1 _ _ hCIα hCIβ
    exact ggInducedAut_injective_of_perfect hK θ (by
      rw [map_mul, map_mul]
      exact hcomm)
  · intro α hα
    have hCI := ggL45_inCIp_inducedAut hα
    obtain ⟨hps, hconj⟩ := H1.2 _ hCI
    have hmod : ((p ^ s : ℕ) : ℤ) = (p : ℤ) ^ s := by push_cast; ring
    have hcast : ((1 + p ^ (s - 1) * k : ℕ) : ℤ) = 1 + (p : ℤ) ^ (s - 1) * k := by
      push_cast
      ring
    have hcp : c ≡ ((1 + p ^ (s - 1) * k : ℕ) : ℤ) [ZMOD ((p ^ s : ℕ) : ℤ)] := by
      rw [hmod, hcast]
      exact hc
    have hpow : (ggInducedAut θ α) ^ c =
        (ggInducedAut θ α) ^ (1 + p ^ (s - 1) * k) := by
      simpa only [zpow_natCast] using
        ggL45_zpow_congr (x := ggInducedAut θ α) hps hcp
    have himg : ggInducedAut θ (ψ * α * ψ⁻¹) =
        ggInducedAut θ (α ^ (1 + p ^ (s - 1) * k)) := by
      rw [map_mul, map_mul, map_inv, map_pow, hconj]
      exact hpow
    exact ggInducedAut_injective_of_perfect hK θ himg

theorem ggL45TorusP2_of_H {s : ℕ} {c : ℤ} (H2 : GGL45HTwo p I θ ψ E s c)
    (H3 : GGL45HThree p E s) :
    (∀ h t : K, GGL45InS p E h → GGL45InS p E t → h * t = t * h ∧ GGL45IsPElt p (h * t)) ∧
      (∀ h : K, GGL45InS p E h → h ^ p ^ s = 1) ∧
      (∃ h : K, GGL45InS p E h ∧ h ^ p ^ (s - 1) ∉ Subgroup.center K) ∧
      ∀ α : MulAut K, GGL45InP p θ I E α → ∀ h : K, GGL45InS p E h → α h = h := by
  obtain ⟨hcomm, hexp, hfix⟩ := H2
  obtain ⟨hH3, -⟩ := H3
  refine ⟨?_, ?_, hH3, ?_⟩
  · intro h t hh ht
    refine ⟨hcomm h t hh ht, s, ?_⟩
    have hhps := (hexp h hh).1
    have htps := (hexp t ht).1
    have hct : Commute h t := hcomm h t hh ht
    calc (h * t) ^ p ^ s = h ^ p ^ s * t ^ p ^ s := Commute.mul_pow hct (p ^ s)
      _ = 1 := by rw [hhps, htps, one_mul]
  · intro h hh
    exact (hexp h hh).1
  · intro α hα h hh
    exact hfix α hα.2.2 hα.2.1 h hh

theorem ggL45TorusP3_of_H (hp : p.Prime) {s : ℕ} (hs : 2 ≤ s) {c : ℤ} {k : ℕ} (hk : ¬ p ∣ k)
    (hc : c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s])
    (H2 : GGL45HTwo p I θ ψ E s c) (H3 : GGL45HThree p E s) :
    ∃ a₁ a₂ : K, GGL45InS p E a₁ ∧ GGL45InS p E a₂ ∧
      (a₁ * (ψ⁻¹ a₁)⁻¹) ^ p = 1 ∧ (a₂ * (ψ⁻¹ a₂)⁻¹) ^ p = 1 ∧
      a₁ * (ψ⁻¹ a₁)⁻¹ ∉ Subgroup.center K ∧
      ∀ i j : ℕ, (a₁ * (ψ⁻¹ a₁)⁻¹) ^ i * (a₂ * (ψ⁻¹ a₂)⁻¹) ^ j = 1 → p ∣ i ∧ p ∣ j := by
  obtain ⟨-, hexp, -⟩ := H2
  obtain ⟨-, b₁, b₂, ⟨h₁, hh₁S, hb₁⟩, ⟨h₂, hh₂S, hb₂⟩, hb₁Z, hindep⟩ := H3
  haveI : Fact p.Prime := ⟨hp⟩
  have hh₁ps : h₁ ^ p ^ s = 1 := (hexp h₁ hh₁S).1
  have hh₂ps : h₂ ^ p ^ s = 1 := (hexp h₂ hh₂S).1
  have hψ₁ : ψ h₁ = h₁ ^ c := (hexp h₁ hh₁S).2
  have hψ₂ : ψ h₂ = h₂ ^ c := (hexp h₂ hh₂S).2
  have hkey₁ : h₁ * (ψ⁻¹ h₁)⁻¹ = (h₁ ^ p ^ (s - 1)) ^ k :=
    ggL45_mul_psi_inv hs hh₁ps hψ₁ hc
  have hkey₂ : h₂ * (ψ⁻¹ h₂)⁻¹ = (h₂ ^ p ^ (s - 1)) ^ k :=
    ggL45_mul_psi_inv hs hh₂ps hψ₂ hc
  have hb₁pow : b₁ ^ p = 1 := by
    rw [hb₁]
    exact ggL45_pow_pred_pow_p hs hh₁ps
  have hb₂pow : b₂ ^ p = 1 := by
    rw [hb₂]
    exact ggL45_pow_pred_pow_p hs hh₂ps
  have hb₁ne : b₁ ≠ 1 := by
    intro h
    exact hb₁Z (by rw [h]; exact Subgroup.one_mem (Subgroup.center K))
  have hord : orderOf b₁ = p := orderOf_eq_prime hb₁pow hb₁ne
  have hcop : Nat.Coprime k (orderOf b₁) := by
    rw [hord]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hk)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := b₁) (n := k) hcop
  have hbkZ : b₁ ^ k ∉ Subgroup.center K := by
    intro hmem
    apply hb₁Z
    rw [← hm]
    exact Subgroup.pow_mem (Subgroup.center K) hmem m
  refine ⟨h₁, h₂, hh₁S, hh₂S, ?_, ?_, ?_, ?_⟩
  · rw [hkey₁, ← hb₁]
    exact ggL45_pow_mul_pow_eq_one hb₁pow
  · rw [hkey₂, ← hb₂]
    exact ggL45_pow_mul_pow_eq_one hb₂pow
  · rw [hkey₁, ← hb₁]
    exact hbkZ
  · intro i j hij
    rw [hkey₁, hkey₂, ← hb₁, ← hb₂, ← pow_mul, ← pow_mul] at hij
    obtain ⟨hpi, hpj⟩ := hindep (k * i) (k * j) hij
    constructor
    · rcases (Nat.Prime.dvd_mul hp).1 hpi with h | h
      · exact absurd h hk
      · exact h
    · rcases (Nat.Prime.dvd_mul hp).1 hpj with h | h
      · exact absurd h hk
      · exact h

end CFSG.StandardType
