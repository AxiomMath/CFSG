module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.C126A5PermBasic

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

section TwoRes

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_le_normalizer_twoResidual (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (twoResidual X : Set G) := by
  intro g hg
  have hgX : ∀ x, x ∈ X ↔ g * x * g⁻¹ ∈ X := Subgroup.mem_normalizer_iff.1 hg
  set K' : Subgroup G := X ⊓ (twoResidual X).comap (MulAut.conj g).toMonoidHom with hK'
  have hmemK' : ∀ x, x ∈ K' ↔ x ∈ X ∧ g * x * g⁻¹ ∈ twoResidual X := fun x => by
    simp [hK']
  have hN : X ≤ Subgroup.normalizer (K' : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' := (hmemK' n).1 hn
    refine (hmemK' _).2 ⟨X.mul_mem (X.mul_mem hx hn'.1) (X.inv_mem hx), ?_⟩
    have hxg : g * x * g⁻¹ ∈ X := (hgX x).1 hx
    have h2 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_twoResidual X hxg)
      (g * n * g⁻¹)).1 hn'.2
    have e : g * (x * n * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * n * g⁻¹) * (g * x * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact h2
  have h2q : ∀ y ∈ X, ∃ k : ℕ, y ^ 2 ^ k ∈ K' := by
    intro y hy
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient X (g * y * g⁻¹) ((hgX y).1 hy)
    refine ⟨k, (hmemK' _).2 ⟨X.pow_mem hy _, ?_⟩⟩
    rw [conj_pow.symm]
    exact hk
  have hle : twoResidual X ≤ K' := twoResidual_le_of_isTwoQuotient inf_le_left hN h2q
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  exact ((hmemK' n).1 (hle hn)).2

end TwoRes

section Fam

variable {A : Type*} [Group A]

theorem mem_normalizer_of_commute {B : Subgroup A} {a : A} (h : ∀ c ∈ B, a * c = c * a) :
    a ∈ Subgroup.normalizer (B : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have h2 : a * b * a⁻¹ = b := by
      rw [h b hb]
      group
    rw [h2]
    exact hb
  · intro hb
    have h1 := h _ hb
    have h3 : a * (a * b * a⁻¹) = a * b := by
      rw [h1]
      group
    have h2 : a * b * a⁻¹ = b := mul_left_cancel h3
    rw [h2] at hb
    exact hb

theorem iSup_inf_le_normalizer (I : Finset (Subgroup A))
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    {L₀ : Subgroup A} (hL₀ : L₀ ∈ I) {B : Subgroup A} (hBL : B ≤ L₀) (E : Subgroup A)
    (hB : L₀ ⊓ E ≤ Subgroup.normalizer (B : Set A)) :
    (⨆ L ∈ I, L ⊓ E) ≤ Subgroup.normalizer (B : Set A) := by
  refine iSup₂_le fun L hL => ?_
  by_cases hLe : L = L₀
  · rw [hLe]
    exact hB
  · intro a ha
    exact mem_normalizer_of_commute fun c hc => hcomm L hL L₀ hL₀ hLe a ha.1 c (hBL hc)

end Fam

section Emb

variable {A : Type*} [Group A] (L : Subgroup A) (θ : ↥L ≃* Perm (Fin 5))

@[expose] def embL : Perm (Fin 5) →* A := L.subtype.comp θ.symm.toMonoidHom

theorem embL_injective : Function.Injective (embL L θ) :=
  L.subtype_injective.comp θ.symm.injective

theorem embL_apply (σ : Perm (Fin 5)) : embL L θ σ = ((θ.symm σ : ↥L) : A) := rfl

theorem embL_mem (σ : Perm (Fin 5)) : embL L θ σ ∈ L := (θ.symm σ).2

theorem embL_theta (x : ↥L) : embL L θ (θ x) = (x : A) := by
  simp [embL_apply]

variable {L θ}

theorem mem_normalizer_map_embL [Finite A] {x : A} (hx : x ∈ L) {B : Subgroup (Perm (Fin 5))}
    (hxB : θ ⟨x, hx⟩ ∈ Subgroup.normalizer (B : Set (Perm (Fin 5)))) :
    x ∈ Subgroup.normalizer ((B.map (embL L θ) : Subgroup A) : Set A) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨b, hb, rfl⟩ := hn
  refine ⟨θ ⟨x, hx⟩ * b * (θ ⟨x, hx⟩)⁻¹, (Subgroup.mem_normalizer_iff.1 hxB b).1 hb, ?_⟩
  rw [map_mul, map_mul, map_inv, embL_theta]

end Emb

theorem closure_swaps_le_normalizer (π : Perm (Fin 5)) :
    Subgroup.closure {swap (π 0) (π 1), swap (π 2) (π 3)} ≤
      Subgroup.normalizer (Subgroup.closure {cyc3 π} : Set (Perm (Fin 5))) := by
  rw [Subgroup.closure_le]
  have key : ∀ a : Perm (Fin 5), a * cyc3 π * a⁻¹ ∈ Subgroup.zpowers (cyc3 π) →
      a ∈ Subgroup.normalizer (Subgroup.closure {cyc3 π} : Set (Perm (Fin 5))) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' : n ∈ Subgroup.zpowers (cyc3 π) := by
      rw [Subgroup.zpowers_eq_closure]
      exact hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn'
    have : a * cyc3 π ^ k * a⁻¹ ∈ Subgroup.zpowers (cyc3 π) := by
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ ha k
    rw [Subgroup.zpowers_eq_closure] at this
    exact this
  intro w hw
  rcases hw with rfl | rfl
  · apply key
    rw [cyc3_comm π]
    simp [Subgroup.mem_zpowers]
  · apply key
    rw [swap_inv, swap_cyc3_swap π]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

theorem card_closure_cyc3 (π : Perm (Fin 5)) :
    Nat.card (Subgroup.closure {cyc3 π} : Subgroup (Perm (Fin 5))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  exact orderOf_eq_prime (cyc3_pow_three π) (cyc3_ne_one π)

end CFSG.Quasithin.C126.A5
