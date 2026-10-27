module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7E16
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Pre

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G} {z : G}

@[expose] noncomputable def yB : Bh := ⟨yA, That_le_Bh yA_mem⟩

section Transport


theorem e16_G (iso : AutIso M₁ M₂) {X : Subgroup G}
    (hX : X ≤ iso.imgG That) (hcard : Nat.card ↥X = 16) (hab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hsq : ∀ a ∈ X, a * a = 1) :
    X = iso.imgG A1h ∨ X = iso.imgG A2h ∨ X = B6.conjSub (iso.toG yB) (iso.imgG A2h) ∨
      X = iso.imgG VA := by
  obtain ⟨K, hKT, hKX⟩ := iso.exists_pre hX
  have hKB : K ≤ Bh := hKT.trans That_le_Bh
  have hcK : Nat.card ↥K = 16 := by
    rw [← hcard, ← hKX, iso.card_imgG hKB]
  have hmemK : ∀ a : Ah, a ∈ K → ∀ h : a ∈ Bh, iso.toG ⟨a, h⟩ ∈ X := fun a ha h => by
    rw [← hKX]
    exact iso.mem_imgG.2 ⟨⟨a, h⟩, ha, rfl⟩
  have habK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    have h1 := hab _ (hmemK a ha (hKB ha)) _ (hmemK b hb (hKB hb))
    rw [← AutIso.toG_mul, ← AutIso.toG_mul] at h1
    have h2 := iso.toG_injective h1
    exact congrArg (fun x : Bh => (x : Ah)) h2
  have hsqK : ∀ a ∈ K, a * a = 1 := by
    intro a ha
    have h1 := hsq _ (hmemK a ha (hKB ha))
    rw [← AutIso.toG_mul, ← iso.toG_one] at h1
    have h2 := iso.toG_injective h1
    exact congrArg (fun x : Bh => (x : Ah)) h2
  rcases e16_classify hKT hcK habK hsqK with h | h | h | h
  · exact Or.inl (by rw [← hKX, h])
  · exact Or.inr (Or.inl (by rw [← hKX, h]))
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [← hKX, h]
    exact iso.imgG_conjSub yB A2h
  · exact Or.inr (Or.inr (Or.inr (by rw [← hKX, h])))

theorem imgG_E16 (iso : AutIso M₁ M₂) {K : Subgroup Ah}
    (hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hsq : ∀ a ∈ K, a * a = 1) :
    (∀ a ∈ iso.imgG K, ∀ b ∈ iso.imgG K, a * b = b * a) ∧
      ∀ a ∈ iso.imgG K, a * a = 1 := by
  constructor
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := iso.mem_imgG.1 ha
    obtain ⟨b', hb', rfl⟩ := iso.mem_imgG.1 hb
    rw [← AutIso.toG_mul, ← AutIso.toG_mul]
    congr 1
    exact Subtype.ext (hab _ ha' _ hb')
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := iso.mem_imgG.1 ha
    rw [← AutIso.toG_mul]
    have : a' * a' = 1 := Subtype.ext (hsq _ ha')
    rw [this]
    exact iso.toG_one

theorem conjSub_E16 {X : Subgroup G} (γ : G) (hab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hsq : ∀ a ∈ X, a * a = 1) :
    (∀ a ∈ B6.conjSub γ X, ∀ b ∈ B6.conjSub γ X, a * b = b * a) ∧
      ∀ a ∈ B6.conjSub γ X, a * a = 1 := by
  constructor
  · intro a ha b hb
    rw [B6.mem_conjSub] at ha hb
    have := hab _ ha _ hb
    have e1 : γ⁻¹ * a * γ * (γ⁻¹ * b * γ) = γ⁻¹ * (a * b) * γ := by group
    have e2 : γ⁻¹ * b * γ * (γ⁻¹ * a * γ) = γ⁻¹ * (b * a) * γ := by group
    rw [e1, e2] at this
    exact mul_left_cancel (mul_right_cancel this)
  · intro a ha
    rw [B6.mem_conjSub] at ha
    have := hsq _ ha
    have e1 : γ⁻¹ * a * γ * (γ⁻¹ * a * γ) = γ⁻¹ * (a * a) * γ := by group
    rw [e1] at this
    have h2 : γ⁻¹ * (a * a) * γ = γ⁻¹ * 1 * γ := by rw [this]; group
    exact mul_left_cancel (mul_right_cancel h2)

end Transport

section Burnside

variable [Finite G]

theorem not_conj_of_sylow {T A Q : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hAT : T ≤ Subgroup.normalizer (A : Set G)) (hQT : T ≤ Subgroup.normalizer (Q : Set G))
    (hne : A ≠ Q)
    (hpair : ∀ s ∈ Subgroup.normalizer (T : Set G), B6.conjSub s A = A ∨ B6.conjSub s A = Q)
    {γ : G} (h : B6.conjSub γ A = Q) : False := by
  have hAQ : A = B6.conjSub γ⁻¹ Q := by
    rw [← h, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  set T₁ := B6.conjSub γ⁻¹ T with hT₁
  have hT₁S : IsSylowTwoOf T₁ ⊤ := by
    have := B6.isSylowTwoOf_conjSub hT γ⁻¹
    rwa [(B6.conjSub γ⁻¹).map_top] at this
  have hT₁N : T₁ ≤ Subgroup.normalizer (A : Set G) := by
    intro x hx
    rw [hT₁, B6.mem_conjSub] at hx
    have ht : γ * x * γ⁻¹ ∈ Subgroup.normalizer (Q : Set G) := hQT (by simpa using hx)
    refine mem_normalizer_of_conjSub_eq ?_
    have e : γ⁻¹ * (γ * x * γ⁻¹) * γ = x := by group
    calc B6.conjSub x A = B6.conjSub (γ⁻¹ * (γ * x * γ⁻¹) * γ) A := by rw [e]
      _ = B6.conjSub (γ⁻¹ * (γ * x * γ⁻¹)) (B6.conjSub γ A) := B6.conjSub_mul _ _ _
      _ = B6.conjSub (γ⁻¹ * (γ * x * γ⁻¹)) Q := by rw [h]
      _ = B6.conjSub γ⁻¹ (B6.conjSub (γ * x * γ⁻¹) Q) := B6.conjSub_mul _ _ _
      _ = B6.conjSub γ⁻¹ Q := by rw [B6.conjSub_eq_self ht]
      _ = A := hAQ.symm
  have hTS_N : IsSylowTwoOf T (Subgroup.normalizer (A : Set G)) :=
    B6.isSylowTwoOf_mono hT hAT le_top
  have hT₁S_N : IsSylowTwoOf T₁ (Subgroup.normalizer (A : Set G)) :=
    B6.isSylowTwoOf_mono hT₁S hT₁N le_top
  obtain ⟨n, hn, hTn⟩ := B6.isSylowTwoOf_exists_conj hT₁S_N hTS_N
  have hs : n * γ⁻¹ ∈ Subgroup.normalizer (T : Set G) := by
    refine mem_normalizer_of_conjSub_eq ?_
    rw [B6.conjSub_mul, ← hT₁, ← hTn]
  have hsQ : B6.conjSub (n * γ⁻¹) Q = A := by
    rw [B6.conjSub_mul, ← hAQ, B6.conjSub_eq_self hn]
  exact no_swap hT hQT hne hpair hs hsQ

end Burnside

end CFSG.Quasithin.H13.F431.U42Aut
