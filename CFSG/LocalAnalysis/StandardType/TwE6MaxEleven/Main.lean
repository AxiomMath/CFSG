module

public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.MinNormal
public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.ThreeNormal
public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Cases

public section

namespace CFSG.StandardType.TwE6MaxEleven

open Subgroup CFSG.Assembly

variable {X : Type} [Group X] [Finite X]

theorem inCatalog_of_kProper {N : Subgroup X} (hK : KProper InCatalog X) (hN : N ≠ ⊤)
    (hNs : IsSimpleGroup N) (hNab : ∃ a b : N, a * b ≠ b * a) : InCatalog N := by
  haveI : ((⊥ : Subgroup X).subgroupOf N).Normal := by
    rw [bot_subgroupOf]; infer_instance
  let e : N ⧸ (⊥ : Subgroup X).subgroupOf N ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf N)).trans QuotientGroup.quotientBot
  have hs : IsSimpleGroup (N ⧸ (⊥ : Subgroup X).subgroupOf N) := e.isSimpleGroup
  have hnab : ∃ a b : N ⧸ (⊥ : Subgroup X).subgroupOf N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hNab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  obtain ⟨i, ⟨f⟩⟩ := hK N ⊥ hN bot_le hs hnab
  exact ⟨i, ⟨e.symm.trans f⟩⟩

theorem le_normalizer_inf_centralizer {M N : Subgroup X} (hMN : M ≤ normalizer (N : Set X)) :
    M ≤ normalizer ((M ⊓ centralizer (N : Set X) : Subgroup X) : Set X) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro c
  have hm' := hMN hm
  rw [mem_normalizer_iff] at hm'
  constructor
  · intro hc
    obtain ⟨hcM, hcN⟩ := mem_inf.mp hc
    refine mem_inf.mpr ⟨M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm), ?_⟩
    rw [mem_centralizer_iff] at hcN ⊢
    intro n hn
    have h1 : m⁻¹ * n * m⁻¹⁻¹ ∈ N := (hMN (M.inv_mem hm) |> mem_normalizer_iff.mp) n |>.mp hn
    have h2 := hcN _ h1
    simp only [inv_inv] at h1 h2
    calc n * (m * c * m⁻¹) = m * ((m⁻¹ * n * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * n * m)) * m⁻¹ := by rw [h2]
      _ = m * c * m⁻¹ * n := by group
  · intro hc
    obtain ⟨hcM, hcN⟩ := mem_inf.mp hc
    have hcM' : c ∈ M := by
      have := M.mul_mem (M.mul_mem (M.inv_mem hm) hcM) hm
      simpa [mul_assoc] using this
    refine mem_inf.mpr ⟨hcM', ?_⟩
    rw [mem_centralizer_iff] at hcN ⊢
    intro n hn
    have h1 : m * n * m⁻¹ ∈ N := (hm' n).mp hn
    have h2 := hcN _ h1
    have : m * (n * c) * m⁻¹ = m * (c * n) * m⁻¹ := by
      calc m * (n * c) * m⁻¹ = (m * n * m⁻¹) * (m * c * m⁻¹) := by group
        _ = (m * c * m⁻¹) * (m * n * m⁻¹) := by rw [h2]
        _ = m * (c * n) * m⁻¹ := by group
    simpa using this

theorem maxElevenProp_of_facts (hSp : SporadicFacts) (hE : ElevenSimpleCases) (hX : LocalFacts X)
    (hK : KProper InCatalog X) {M : Subgroup X} (hM : IsCoatom M) (h11 : 11 ∣ Nat.card M) :
    (∃ N : Subgroup X, N ≤ M ∧ Nat.card N = 9196830720 ∧
      ∀ P : Subgroup X, P ≤ M → ⁅P, P⁆ = P → P ≤ N) ∨
    (∀ y ∈ M, orderOf y = 3 → ¬ 11 ∣ Nat.card (M ⊓ Subgroup.centralizer {y} : Subgroup X)) ∨
    ¬ 3 ^ 7 ∣ Nat.card M := by
  classical
  by_cases hd : 3 ^ 7 ∣ Nat.card M
  swap
  · exact Or.inr (Or.inr hd)
  by_cases hc : ∀ y ∈ M, orderOf y = 3 →
      ¬ 11 ∣ Nat.card (M ⊓ Subgroup.centralizer {y} : Subgroup X)
  · exact Or.inr (Or.inl hc)
  refine Or.inl ?_
  push Not at hc
  obtain ⟨y, hyM, hy, h11y⟩ := hc
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ centralizer {y})) 11 h11y
  obtain ⟨htM, htC⟩ := mem_inf.mp t'.2
  set t : X := (t' : X) with ht_def
  have ht : orderOf t = 11 := by rw [ht_def, orderOf_coe]; exact ht'
  have hyt : Commute y t := by
    have := mem_centralizer_iff.mp htC y (Set.mem_singleton y)
    exact this
  have hM1 : M ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at htM
    rw [htM, orderOf_one] at ht
    norm_num at ht
  have hA : ∀ N : Subgroup X, N ≠ ⊥ → N ≤ M → M ≤ normalizer (N : Set X) →
      (∀ L : Subgroup X, L ≠ ⊥ → L ≤ N → M ≤ normalizer (L : Set X) → L = N) →
      ∀ p : ℕ, p.Prime → IsPGroup p N → ∃ N' : Subgroup X, N' ≤ M ∧
        Nat.card N' = 9196830720 ∧ ∀ P : Subgroup X, P ≤ M → ⁅P, P⁆ = P → P ≤ N' := by
    intro N hN1 hNM hMN hmin p hp hNp
    have htN : t ∈ normalizer (N : Set X) := hMN htM
    by_cases hp2 : p = 2
    · subst hp2
      exact absurd hd (hX.twoLocal M hM N hN1 hNp hMN)
    by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨h3, hcomm⟩ := minNormal_isElemAbelian hp hNp hN1 hNM hMN hmin
      exact maxElevenB_of_elemAbelian_three hX hM htM ht hN1 hNM hMN h3 hcomm
    by_cases hp11 : p = 11
    · subst hp11
      have hNt := eq_zpowers_of_isPGroup_eleven hX ht hNp hN1 htN
      have hMle : M ≤ normalizer (zpowers t : Set X) := by rw [← hNt]; exact hMN
      have h660 : Nat.card M ∣ 660 :=
        (card_dvd_of_le hMle).trans (card_normalizer_zpowers_eleven_dvd hX ht)
      exact absurd (hd.trans h660) (by norm_num)
    · exact absurd (eq_bot_of_isPGroup_of_mem_normalizer hX ht hp hp2 hp3 hp11 hNp htN) hN1
  by_cases hAll : ∃ N : Subgroup X, N ≠ ⊥ ∧ N ≤ M ∧ M ≤ normalizer (N : Set X) ∧
      (∀ L : Subgroup X, L ≠ ⊥ → L ≤ N → M ≤ normalizer (L : Set X) → L = N) ∧
      ∃ p : ℕ, p.Prime ∧ IsPGroup p N
  · obtain ⟨N, hN1, hNM, hMN, hmin, p, hp, hNp⟩ := hAll
    exact hA N hN1 hNM hMN hmin p hp hNp
  have hS : ∀ N : Subgroup X, N ≠ ⊥ → N ≤ M → M ≤ normalizer (N : Set X) →
      (∀ L : Subgroup X, L ≠ ⊥ → L ≤ N → M ≤ normalizer (L : Set X) → L = N) →
      IsSimpleGroup N ∧ (∃ a b : N, a * b ≠ b * a) ∧ t ∈ N := by
    intro N hN1 hNM hMN hmin
    rcases minNormal_isPGroup_or_simple hX htM ht hN1 hNM hMN hmin with ⟨p, hp, hNp⟩ | h
    · exact absurd ⟨N, hN1, hNM, hMN, hmin, p, hp, hNp⟩ hAll
    · exact h
  obtain ⟨N, -, hN1, hNM, hMN, hmin⟩ := exists_minNormal_le hM1 le_rfl le_normalizer
  obtain ⟨hNs, hNab, htN⟩ := hS N hN1 hNM hMN hmin
  have hcent : ∀ g ∈ M, (∀ n ∈ N, g * n = n * g) → g = 1 := by
    intro g hgM hgN
    by_contra hg1
    have hgC : g ∈ M ⊓ centralizer (N : Set X) :=
      ⟨hgM, mem_centralizer_iff.mpr fun n hn => (hgN n hn).symm⟩
    have hC1 : M ⊓ centralizer (N : Set X) ≠ ⊥ := by
      intro h
      rw [h, mem_bot] at hgC
      exact hg1 hgC
    obtain ⟨N', hN'C, hN'1, hN'M, hMN', hmin'⟩ :=
      exists_minNormal_le hC1 inf_le_left (le_normalizer_inf_centralizer hMN)
    obtain ⟨-, -, htN'⟩ := hS N' hN'1 hN'M hMN' hmin'
    have htc : t ∈ centralizer (N : Set X) := (mem_inf.mp (hN'C htN')).2
    haveI := hNs
    have hcen : center N = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center N) with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := hNab
        exact absurd ((mem_center_iff.mp (h ▸ mem_top b)) a) hab
    have : (⟨t, htN⟩ : N) ∈ center N := by
      rw [mem_center_iff]
      intro n
      apply Subtype.ext
      exact (mem_centralizer_iff.mp htc n.1 n.2)
    rw [hcen, mem_bot] at this
    have ht1 : t = 1 := congrArg Subtype.val this
    rw [ht1, orderOf_one] at ht
    norm_num at ht
  have hNtop : N ≠ ⊤ := fun h => hM.1 (top_le_iff.mp (h ▸ hNM))
  exact maxElevenB_of_simple hSp hE hX hM hd hyM hy ht hyt hNM hMN hNs hNab htN hcent
    (inCatalog_of_kProper hK hNtop hNs hNab)

end CFSG.StandardType.TwE6MaxEleven
