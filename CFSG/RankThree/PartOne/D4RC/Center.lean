module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.RankThree.PartOne.D4RC

open Subgroup

variable {K : Type*} [Group K]

theorem rcs_inf_eq_bot_of_odd [Finite K] {M X : Subgroup K} (hM : IsPGroup 2 M)
    (hX : Odd (Nat.card X)) : M ⊓ X = ⊥ := by
  have h2 : IsPGroup 2 (M ⊓ X : Subgroup K) := hM.to_le inf_le_left
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hdvd : Nat.card (M ⊓ X : Subgroup K) ∣ Nat.card X := card_dvd_of_le inf_le_right
  have hodd : Odd (Nat.card (M ⊓ X : Subgroup K)) := hX.of_dvd_nat hdvd
  rw [hn] at hodd
  have hn0 : n = 0 := by
    by_contra h
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' h).mpr even_two)
  rw [hn0, pow_zero] at hn
  exact card_eq_one.mp hn

theorem rcs_mem_sup_of_comm {R C : Subgroup K} (hcomm : ∀ r ∈ R, ∀ c ∈ C, r * c = c * r)
    {x : K} (hx : x ∈ R ⊔ C) : ∃ r ∈ R, ∃ c ∈ C, x = r * c := by
  let S : Subgroup K :=
    { carrier := {x | ∃ r ∈ R, ∃ c ∈ C, x = r * c}
      mul_mem' := by
        rintro _ _ ⟨r₁, hr₁, c₁, hc₁, rfl⟩ ⟨r₂, hr₂, c₂, hc₂, rfl⟩
        refine ⟨r₁ * r₂, R.mul_mem hr₁ hr₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
        calc r₁ * c₁ * (r₂ * c₂) = r₁ * (c₁ * r₂) * c₂ := by group
          _ = r₁ * (r₂ * c₁) * c₂ := by rw [← hcomm r₂ hr₂ c₁ hc₁]
          _ = r₁ * r₂ * (c₁ * c₂) := by group
      one_mem' := ⟨1, R.one_mem, 1, C.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨r, hr, c, hc, rfl⟩
        refine ⟨r⁻¹, R.inv_mem hr, c⁻¹, C.inv_mem hc, ?_⟩
        rw [mul_inv_rev, hcomm r⁻¹ (R.inv_mem hr) c⁻¹ (C.inv_mem hc)] }
  have hle : R ⊔ C ≤ S := sup_le (fun r hr => ⟨r, hr, 1, C.one_mem, by simp⟩)
    (fun c hc => ⟨1, R.one_mem, c, hc, by simp⟩)
  exact hle hx

theorem rcs_mem_of_pow_mem {g : K} {n : ℕ} (hcop : Nat.Coprime n (orderOf g))
    {S : Subgroup K} (h : g ^ n ∈ S) : g ∈ S := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact S.pow_mem h m

theorem rcs_two_elt [Finite K] {H R C : Subgroup K} (hRH : R ≤ H) (hCH : C ≤ H)
    (hcomm : ∀ r ∈ R, ∀ c ∈ C, r * c = c * r)
    (hnorm : H ≤ normalizer ((R ⊔ C : Subgroup K) : Set K))
    (hidx : Odd ((R ⊔ C).relIndex H)) (hC : Odd (Nat.card C)) :
    ∀ x ∈ H, IsPGroup 2 (zpowers x) → x ∈ R := by
  intro x hxH hx2
  obtain ⟨k, hk⟩ := hx2.exists_card_eq
  rw [Nat.card_zpowers] at hk
  have hSH : R ⊔ C ≤ H := sup_le hRH hCH
  have hN : ((R ⊔ C).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hSH).mpr hnorm
  have hxS : x ∈ R ⊔ C := by
    have hpow : (⟨x, hxH⟩ : H) ^ ((R ⊔ C).subgroupOf H).index ∈ (R ⊔ C).subgroupOf H :=
      pow_index_mem _ _
    have hord : orderOf (⟨x, hxH⟩ : H) = 2 ^ k := by rw [← hk]; exact Subgroup.orderOf_mk x hxH
    have hcop : Nat.Coprime ((R ⊔ C).subgroupOf H).index (orderOf (⟨x, hxH⟩ : H)) := by
      rw [hord]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hidx)
    exact rcs_mem_of_pow_mem hcop hpow
  obtain ⟨r, hr, c, hc, rfl⟩ := rcs_mem_sup_of_comm hcomm hxS
  have hcr : Commute r c := hcomm r hr c hc
  have hpow : (r * c) ^ (2 ^ k) = 1 := by
    rw [← hk]; exact pow_orderOf_eq_one _
  rw [hcr.mul_pow] at hpow
  have hcpow : c ^ (2 ^ k) ∈ R := by
    have : c ^ (2 ^ k) = (r ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hpow
    rw [this]; exact R.inv_mem (R.pow_mem hr _)
  have hcodd : Odd (orderOf c) := hC.of_dvd_nat (Subgroup.orderOf_dvd_natCard C hc)
  have hcc : c ∈ R := rcs_mem_of_pow_mem
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hcodd)) hcpow
  exact R.mul_mem hr hcc

theorem rcs_mem_normalizer_of_conj {S : Subgroup K} {g : K} (h1 : ∀ y ∈ S, g * y * g⁻¹ ∈ S)
    (h2 : ∀ y ∈ S, g⁻¹ * y * g ∈ S) : g ∈ normalizer (S : Set K) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  have := h2 _ hy
  simpa [mul_assoc] using this

@[expose] def TwoCoreLocal (Γ : Subgroup K) (e : K) : Prop :=
  Odd (Nat.card (centralizer ({e} : Set K))) ∨
    ∃ R C : Subgroup K, R ≤ Γ ∧
      (∀ M : Subgroup K, M ≤ R → R ≤ normalizer (M : Set K) → IsPGroup 2 M → M = ⊥) ∧
      Odd (Nat.card C) ∧ (∀ r ∈ R, ∀ c ∈ C, r * c = c * r) ∧
      R ≤ centralizer ({e} : Set K) ∧ C ≤ centralizer ({e} : Set K) ∧
      centralizer ({e} : Set K) ≤ normalizer ((R ⊔ C : Subgroup K) : Set K) ∧
      Odd ((R ⊔ C).relIndex (centralizer ({e} : Set K)))

theorem rcs_local_bot [Finite K] {Γ N : Subgroup K} {e : K}
    (hnorm : Γ ≤ normalizer (N : Set K)) (hN : IsPGroup 2 N) (h : TwoCoreLocal Γ e) :
    N ⊓ centralizer ({e} : Set K) = ⊥ := by
  rcases h with hodd | ⟨R, C, hRΓ, hO2, hC, hcomm, hRe, hCe, hnormRC, hidx⟩
  · exact rcs_inf_eq_bot_of_odd hN hodd
  · have hY2 : IsPGroup 2 (N ⊓ centralizer ({e} : Set K) : Subgroup K) := hN.to_le inf_le_left
    have hYR : N ⊓ centralizer ({e} : Set K) ≤ R := by
      intro y hy
      have h2 : IsPGroup 2 (zpowers y) := hY2.to_le (zpowers_le.mpr hy)
      exact rcs_two_elt hRe hCe hcomm hnormRC hidx hC y hy.2 h2
    have hconj : ∀ r ∈ R, ∀ y ∈ N ⊓ centralizer ({e} : Set K),
        r * y * r⁻¹ ∈ N ⊓ centralizer ({e} : Set K) := by
      intro r hr y hy
      refine ⟨?_, ?_⟩
      · exact (mem_normalizer_iff.mp (hnorm (hRΓ hr)) y).mp hy.1
      · exact (centralizer ({e} : Set K)).mul_mem
          ((centralizer ({e} : Set K)).mul_mem (hRe hr) hy.2)
          ((centralizer ({e} : Set K)).inv_mem (hRe hr))
    refine hO2 _ hYR (fun r hr => rcs_mem_normalizer_of_conj (hconj r hr) ?_) hY2
    intro y hy
    have := hconj r⁻¹ (R.inv_mem hr) y hy
    simpa using this

theorem rcs_twoCore [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Γ E : Subgroup K}
    (hEΓ : E ≤ Γ) (hEp : ∀ x : E, x ^ p = 1) (hEcard : Nat.card E = p ^ 2)
    (hloc : ∀ e ∈ E, e ≠ 1 → TwoCoreLocal Γ e) :
    ∀ N : Subgroup K, Γ ≤ normalizer (N : Set K) → IsPGroup 2 N → N = ⊥ := by
  intro N hnorm hN
  have hcomp : ¬ p ∣ Nat.card N := by
    obtain ⟨n, hn⟩ := hN.exists_card_eq
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    p hp E N hEp hEcard hcomp (hEΓ.trans hnorm)
  refine hgen.trans (le_bot_iff.mp (iSup₂_le fun e he => ?_))
  exact (rcs_local_bot hnorm hN (hloc e e.2 (fun h => he (Subtype.ext h)))).le

theorem rcs_hyp_twoCore [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Γ E : Subgroup K}
    (hEΓ : E ≤ Γ) (hEp : ∀ x : E, x ^ p = 1) (hEcard : Nat.card E = p ^ 2)
    (hloc : ∀ e ∈ E, e ≠ 1 → TwoCoreLocal Γ e) :
    ∀ N : Subgroup ↥Γ, N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hN2
  have hmem : ∀ g ∈ Γ, ∀ h ∈ N.map Γ.subtype, g * h * g⁻¹ ∈ N.map Γ.subtype := by
    rintro g hg _ ⟨n, hn, rfl⟩
    exact ⟨⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹, hN.conj_mem n hn ⟨g, hg⟩, by simp⟩
  have h := rcs_twoCore hp hp2 hEΓ hEp hEcard hloc (N.map Γ.subtype)
    (fun g hg => rcs_mem_normalizer_of_conj (hmem g hg)
      (fun y hy => by simpa using hmem g⁻¹ (Γ.inv_mem hg) y hy))
    (hN2.map Γ.subtype)
  exact (Subgroup.map_eq_bot_iff_of_injective N Γ.subtype_injective).mp h

end CFSG.RankThree.PartOne.D4RC
