module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319S3Wr
public import CFSG.Quasithin.Vol2.Ch3y319

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

section Aux

variable {G : Type} [Group G] [Finite G]

theorem exists_noncentral_of_series {G₂ U N : Subgroup G} {n : ℕ}
    (h : IsChiefSeriesFrom G₂ U N n) (hn : n ≠ 0) :
    ∃ L' N' : Subgroup G, IsChiefStep G₂ U L' N' ∧ ¬ IsCentralStep G₂ L' N' := by
  induction h with
  | bot => exact absurd rfl hn
  | central hs _ _ ih => exact ih hn
  | noncentral hs hnc _ _ => exact ⟨_, _, hs, hnc⟩

theorem prime_dvd_seventy_two {q : ℕ} (hq : q.Prime) (h : q ∣ 72) : q = 2 ∨ q = 3 := by
  have h72 : (72 : ℕ) = 2 ^ 3 * 3 ^ 2 := by norm_num
  rw [h72] at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h1))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h1))

theorem not_quotIso_perm_three {H U L N A : Subgroup G} (hAH : A ≤ H) (hAe : ∀ a ∈ A, a * a = 1)
    (hL : IsNormalIn H U L) (hcA : cSecIn A L N = A ⊓ pCoreOf 2 H)
    (hrk : 2 ≤ secRank A (A ⊓ pCoreOf 2 H))
    (φ : ↥H →* Equiv.Perm (Fin 3)) (hφk : φ.ker = (cSecIn H L N).subgroupOf H) : False := by
  set ψ : ↥A →* Equiv.Perm (Fin 3) := φ.comp (Subgroup.inclusion hAH) with hψ
  have hrange : Nat.card ψ.range ≤ 2 := by
    refine perm_three_elemAbelian_card_le_two ψ.range ?_
    rintro _ ⟨a, rfl⟩
    have h1 : a * a = 1 := Subtype.ext (hAe a a.2)
    rw [← map_mul, h1, map_one]
  have hker : ψ.ker ≤ (A ⊓ pCoreOf 2 H).subgroupOf A := by
    intro a ha
    have h1 : φ (Subgroup.inclusion hAH a) = 1 := ha
    have h2 : Subgroup.inclusion hAH a ∈ φ.ker := h1
    rw [hφk] at h2
    have h3 : (a : G) ∈ cSecIn H L N := h2
    rw [cSecIn_eq_centralizerMod le_rfl hL] at h3
    have h4 : (a : G) ∈ cSecIn A L N := by
      rw [cSecIn_eq_centralizerMod hAH hL]
      exact ⟨a.2, h3.2⟩
    rw [hcA] at h4
    exact h4
  have hdvd : (A ⊓ pCoreOf 2 H).relIndex A ∣ Nat.card ψ.range := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le hker
  have hle2 : (A ⊓ pCoreOf 2 H).relIndex A ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans hrange
  have hpos : 0 < (A ⊓ pCoreOf 2 H).relIndex A := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : 2 ^ 2 ∣ (A ⊓ pCoreOf 2 H).relIndex A :=
    (pow_dvd_pow 2 hrk).trans (pow_padicValNat_dvd (p := 2) (n := (A ⊓ pCoreOf 2 H).relIndex A))
  have := Nat.le_of_dvd hpos h4
  omega

end Aux

end CFSG.Quasithin.H13.L319
