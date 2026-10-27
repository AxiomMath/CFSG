module

public import CFSG.Quasithin.Background.G64PermAut
public import CFSG.Quasithin.EmptyFaithful.S153EB6H
public import CFSG.Quasithin.EmptyFaithful.S153EB6J

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem sign_commutator_eq_one {n : ℕ} (g₁ g₂ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign ⁅g₁, g₂⁆ = 1 := by
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)

theorem simple_core_of_perm {V : Type} [CommGroup V] {G Kb : Subgroup (MulAut V)} {n : ℕ}
    (hn : 5 ≤ n) (π : Equiv.Perm (Fin n) →* ↥G) (hsurj : Function.Surjective π)
    (hinj : Function.Injective π) (hsq : ∀ g ∈ G, g ^ 2 ∈ Kb)
    (hperf : Kb ≤ ⁅Kb, Kb⁆) (hKbG : Kb ≤ G) :
    ∀ M : Subgroup (MulAut V), M ≤ Kb → (∀ k ∈ Kb, ∀ m ∈ M, k * m * k⁻¹ ∈ M) → M ≠ ⊥ →
      M = Kb := by
  intro M hMK hMnorm hMne
  let π' : Equiv.Perm (Fin n) →* MulAut V := G.subtype.comp π
  have hπ'inj : Function.Injective π' := fun x y h => hinj (Subtype.ext h)
  let A : Subgroup (Equiv.Perm (Fin n)) := Kb.comap π'
  have hAmem : ∀ σ, σ ∈ A ↔ π' σ ∈ Kb := fun σ => Iff.rfl
  have hAltA : alternatingGroup (Fin n) ≤ A := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    rw [SetLike.mem_coe, hAmem]
    have h3 : (π' σ) ^ 3 = 1 := by
      have h0 : σ ^ 3 = 1 := by
        have := pow_orderOf_eq_one σ
        rwa [hσ.orderOf] at this
      rw [← map_pow, h0]
      exact map_one π'
    have h1 : (π' σ) ^ 2 ∈ Kb := hsq _ (π σ).2
    have h2 : ((π' σ) ^ 2) ^ 2 = π' σ := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
    rw [← h2]
    exact Kb.pow_mem h1 2
  have hKbπ : ∀ k ∈ Kb, ∃ τ, π' τ = k := fun k hk => by
    obtain ⟨τ, hτ⟩ := hsurj ⟨k, hKbG hk⟩
    exact ⟨τ, congrArg Subtype.val hτ⟩
  have hAeven : ∀ σ ∈ A, σ ∈ alternatingGroup (Fin n) := by
    intro σ hσ
    by_contra hodd
    have hsgn : Equiv.Perm.sign σ = -1 :=
      (Int.units_eq_one_or _).resolve_left (fun h => hodd (Equiv.Perm.mem_alternatingGroup.2 h))
    have hAtop : ∀ τ : Equiv.Perm (Fin n), τ ∈ A := by
      intro τ
      by_cases hτ : τ ∈ alternatingGroup (Fin n)
      · exact hAltA hτ
      · have hτs : Equiv.Perm.sign τ = -1 :=
          (Int.units_eq_one_or _).resolve_left (fun h => hτ (Equiv.Perm.mem_alternatingGroup.2 h))
        have h1 : τ * σ⁻¹ ∈ alternatingGroup (Fin n) := by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hτs, hsgn]
          decide
        have := A.mul_mem (hAltA h1) hσ
        simpa using this
    have hGKb : ∀ g ∈ G, g ∈ Kb := by
      intro g hg
      obtain ⟨τ, hτ⟩ := hsurj ⟨g, hg⟩
      have h1 := hAtop τ
      rw [hAmem] at h1
      have h' : π' τ = g := congrArg Subtype.val hτ
      rwa [h'] at h1
    have hcomm : ⁅Kb, Kb⁆ ≤ (alternatingGroup (Fin n)).map π' := by
      refine Subgroup.commutator_le.2 fun k₁ hk₁ k₂ hk₂ => ?_
      obtain ⟨τ₁, rfl⟩ := hKbπ k₁ hk₁
      obtain ⟨τ₂, rfl⟩ := hKbπ k₂ hk₂
      refine ⟨⁅τ₁, τ₂⁆, Equiv.Perm.mem_alternatingGroup.2 (sign_commutator_eq_one _ _), ?_⟩
      rw [map_commutatorElement]
    let x₀ : Fin n := ⟨0, by omega⟩
    let x₁ : Fin n := ⟨1, by omega⟩
    have hx : x₀ ≠ x₁ := by simp [x₀, x₁, Fin.ext_iff]
    have hsw : π' (Equiv.swap x₀ x₁) ∈ Kb := hGKb _ (π _).2
    obtain ⟨τ, hτ, hτe⟩ := hcomm (hperf hsw)
    have : τ = Equiv.swap x₀ x₁ := hπ'inj hτe
    have hτ' : Equiv.swap x₀ x₁ ∈ alternatingGroup (Fin n) := this ▸ hτ
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hx] at hτ'
    exact absurd hτ' (by decide)
  have hAeq : A = alternatingGroup (Fin n) := le_antisymm (fun σ hσ => hAeven σ hσ) hAltA
  let M' : Subgroup (Equiv.Perm (Fin n)) := M.comap π'
  have hM'A : M' ≤ A := fun σ hσ => hMK hσ
  have hM'norm : ∀ σ ∈ A, ∀ m ∈ M', σ * m * σ⁻¹ ∈ M' := by
    intro σ hσ m hm
    show π' (σ * m * σ⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact hMnorm _ hσ _ hm
  have hM'ne : M' ≠ ⊥ := by
    intro hbot
    apply hMne
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨τ, hτ⟩ := hsurj ⟨g, hKbG (hMK hg)⟩
    have hτ' : π' τ = g := congrArg Subtype.val hτ
    have : τ ∈ M' := by
      show π' τ ∈ M
      rw [hτ']
      exact hg
    rw [hbot, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, ← hτ', this, map_one]
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  have hAltM' : alternatingGroup (Fin n) ≤ M' := by
    have hnormal : (M'.subgroupOf (alternatingGroup (Fin n))).Normal := by
      refine ⟨fun m hm g => ?_⟩
      show ((g * m * g⁻¹ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) ∈ M'
      have hgA : (g : Equiv.Perm (Fin n)) ∈ A := by rw [hAeq]; exact g.2
      exact hM'norm _ hgA _ hm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M'.subgroupOf (alternatingGroup (Fin n))) with h | h
    · exfalso
      apply hM'ne
      rw [eq_bot_iff]
      intro σ hσ
      have hσA : σ ∈ alternatingGroup (Fin n) := by
        have := hM'A hσ
        rwa [hAeq] at this
      have : (⟨σ, hσA⟩ : ↥(alternatingGroup (Fin n))) ∈ M'.subgroupOf (alternatingGroup (Fin n)) := hσ
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    · intro σ hσ
      have : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin n))) ∈ M'.subgroupOf (alternatingGroup (Fin n)) := by
        rw [h]; exact Subgroup.mem_top _
      exact this
  refine le_antisymm hMK fun k hk => ?_
  obtain ⟨τ, hτ⟩ := hKbπ k hk
  have hτA : τ ∈ A := by
    rw [hAmem, hτ]
    exact hk
  have hτA' : τ ∈ alternatingGroup (Fin n) := by rwa [hAeq] at hτA
  have := hAltM' hτA'
  have h2 : π' τ ∈ M := this
  rwa [hτ] at h2

section PermFacts

variable {V : Type} [CommGroup V]

theorem modelFacts_of_perm [Finite V] {G Kb : Subgroup (MulAut V)} {a : MulAut V}
    (hI : Induced V G Kb a) {n : ℕ} (hn : 5 ≤ n) {Z : Subgroup (G6.PermMod n)}
    (hZ : Z ≤ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n)
    (hF : (G64.permModel n Z).Faithful) (hreal : (G64.permModel n Z).Realizes G ⊤ ⊥) :
    ModelFacts V G Kb a := by
  obtain ⟨π₀, hπ₀⟩ := hreal
  let π : Equiv.Perm (Fin n) →* ↥G := π₀
  have hπ : (G64.permModel n Z).RealizesVia G ⊤ ⊥ π := hπ₀
  have hinj : Function.Injective π := G64.RealizesVia.injective_of_faithful' hF hπ
  refine ⟨fun p => exists_three_fix_of_mt hI.mt hI.big p,
    simple_core_of_perm hn π hπ.1 hinj hI.sq hI.perf hI.KbG, Or.inr ?_⟩
  have hsw := G64.isSwap_of_realization hn hZ hπ hinj hI.aG hI.card
  obtain ⟨x, y, hxy, hσ⟩ := hsw
  set e := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩ with he
  set σ := e.symm ⟨a, hI.aG⟩ with hσdef
  have hπσ : ((π σ : ↥G) : MulAut V) = a := by
    have : e σ = ⟨a, hI.aG⟩ := e.apply_symm_apply _
    exact congrArg Subtype.val this
  obtain ⟨c₁, c₂, c₃, h12, h13, h23, hc₁, hc₂, hc₃⟩ : ∃ c₁ c₂ c₃ : Fin n, c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧
      c₂ ≠ c₃ ∧ (c₁ ≠ x ∧ c₁ ≠ y) ∧ (c₂ ≠ x ∧ c₂ ≠ y) ∧ (c₃ ≠ x ∧ c₃ ≠ y) := by
    have hc : 2 < ((Finset.univ : Finset (Fin n)).erase x |>.erase y).card := by
      rw [Finset.card_erase_of_mem (by simp [Ne.symm hxy]), Finset.card_erase_of_mem (Finset.mem_univ x)]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.1 hc
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at h₁ h₂ h₃
    exact ⟨c₁, c₂, c₃, h12, h13, h23, ⟨h₁.2, h₁.1⟩, ⟨h₂.2, h₂.1⟩, ⟨h₃.2, h₃.1⟩⟩
  set τ : Equiv.Perm (Fin n) := Equiv.swap c₁ c₂ * Equiv.swap c₂ c₃ with hτ
  have hτ3 : τ ^ 3 = 1 := cyc3_pow h12 h13 h23
  have hτcomm : τ * σ = σ * τ := by
    rw [hσ, hτ]
    have e1 : Equiv.swap c₁ c₂ * Equiv.swap x y = Equiv.swap x y * Equiv.swap c₁ c₂ :=
      G64.swap_mul_swap_comm_of_ne hc₁.1 hc₁.2 hc₂.1 hc₂.2
    have e2 : Equiv.swap c₂ c₃ * Equiv.swap x y = Equiv.swap x y * Equiv.swap c₂ c₃ :=
      G64.swap_mul_swap_comm_of_ne hc₂.1 hc₂.2 hc₃.1 hc₃.2
    rw [mul_assoc, e2, ← mul_assoc, e1, mul_assoc]
  have hτne : τ ≠ 1 := by
    intro h1
    have := congrArg (fun f : Equiv.Perm (Fin n) => f c₁) h1
    simp [hτ, Equiv.swap_apply_def, h12, h13, h12.symm] at this
  refine ⟨((π τ : ↥G) : MulAut V), (π τ).2, ?_, ?_⟩
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · have := congrArg (fun f : Equiv.Perm (Fin n) => ((π f : ↥G) : MulAut V)) hτ3
      simpa [map_pow] using this
    · intro h1
      apply hτne
      apply hinj
      apply Subtype.ext
      rw [h1]
      simp
  · rw [← hπσ]
    have := congrArg (fun f : Equiv.Perm (Fin n) => ((π f : ↥G) : MulAut V)) hτcomm
    simpa [map_mul] using this

end PermFacts

end S153EB6

end CFSG.Quasithin
