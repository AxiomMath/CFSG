module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S29

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.ABGLocalTools

theorem inf_eq_bot_of_isPGroup_of_not_dvd {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    {E K : Subgroup L} (hE : IsPGroup p E) (hK : ¬ p ∣ Nat.card K) : E ⊓ K = ⊥ := by
  have h1 : Nat.card ↥(E ⊓ K) ∣ Nat.card E := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(E ⊓ K) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨n, hn⟩ := hE.exists_card_eq
  rw [hn] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
  by_cases hj0 : j = 0
  · rw [hj0, pow_zero] at hj
    exact Subgroup.eq_bot_of_card_eq _ hj
  · exfalso
    apply hK
    refine Dvd.dvd.trans ?_ h2
    rw [hj]
    exact dvd_pow_self p hj0

theorem exists_inverting_of_surjective {L M₀ : Type*} [Group L] [Finite L] [Group M₀] [Finite M₀]
    {p : ℕ} [Fact p.Prime] (ψ : L →* M₀) (hψ : Function.Surjective ψ) (hker : ¬ p ∣ Nat.card ψ.ker)
    {E : Subgroup L} (hE : IsSylowOf p E ⊤) (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {E₀ : Subgroup M₀} (hE₀ : IsSylowOf p E₀ ⊤) {x₀ : M₀} (hx₀ : x₀ ∈ normalizer (E₀ : Set M₀))
    (hinv : ∀ e ∈ E₀, x₀ * x₀ * e * (x₀ * x₀)⁻¹ = e⁻¹) :
    ∃ x : L, x ∈ normalizer (E : Set L) ∧ ∀ e ∈ E, x * x * e * (x * x)⁻¹ = e⁻¹ := by
  classical
  have hEp : IsPGroup p E := hE.isPGroup
  have hEker : E ⊓ ψ.ker = ⊥ := inf_eq_bot_of_isPGroup_of_not_dvd hEp hker
  have hinjE : Function.Injective (ψ.domRestrict E) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, ha⟩ hk
    have h1 : a ∈ E ⊓ ψ.ker := ⟨ha, hk⟩
    rw [hEker, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hcardψE : Nat.card (E.map ψ) = Nat.card E := by
    rw [← MonoidHom.domRestrict_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjE).toEquiv).symm
  have hcardL : Nat.card ψ.ker * Nat.card M₀ = Nat.card L :=
    Subgroup.card_ker_mul_card_of_surjective hψ
  have hv : (Nat.card L).factorization p = (Nat.card M₀).factorization p := by
    rw [← hcardL, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
  have hψEsyl : IsSylowOf p (E.map ψ) ⊤ := by
    apply isSylowOf_of_card le_top
    rw [hcardψE, hE.card_eq, Subgroup.card_top, Subgroup.card_top, hv]
  obtain ⟨g, -, hg⟩ := hE₀.exists_mem_conj hψEsyl
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : M₀, x₁ = g * x₀ * g⁻¹ := ⟨_, rfl⟩
  have hx₁N : ∀ y ∈ E.map ψ, x₁ * y * x₁⁻¹ ∈ E.map ψ := by
    intro y hy
    rw [hg] at hy ⊢
    have h := (mem_normalizer_iff.1 hx₀ (g⁻¹ * y * g)).1 hy
    have e : g⁻¹ * (x₁ * y * x₁⁻¹) * g = x₀ * (g⁻¹ * y * g) * x₀⁻¹ := by rw [hx₁]; group
    rw [e]
    exact h
  have hx₁inv : ∀ y ∈ E.map ψ, x₁ * x₁ * y * (x₁ * x₁)⁻¹ = y⁻¹ := by
    intro y hy
    rw [hg] at hy
    have h := hinv _ hy
    have e : x₁ * x₁ * y * (x₁ * x₁)⁻¹ =
        g * (x₀ * x₀ * (g⁻¹ * y * g) * (x₀ * x₀)⁻¹) * g⁻¹ := by rw [hx₁]; group
    rw [e, h]
    group
  obtain ⟨x', hx'⟩ := hψ x₁
  haveI : (ψ.ker).Normal := MonoidHom.normal_ker ψ
  have hconjmem : ∀ e ∈ E, x' * e * x'⁻¹ ∈ E ⊔ ψ.ker := by
    intro e he
    have h1 : ψ (x' * e * x'⁻¹) ∈ E.map ψ := by
      rw [map_mul, map_mul, map_inv, hx']
      exact hx₁N _ (Subgroup.mem_map_of_mem ψ he)
    obtain ⟨e', he', hee'⟩ := Subgroup.mem_map.1 h1
    have hk : e'⁻¹ * (x' * e * x'⁻¹) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hee', inv_mul_cancel]
    have : x' * e * x'⁻¹ = e' * (e'⁻¹ * (x' * e * x'⁻¹)) := by group
    rw [this]
    exact Subgroup.mul_mem_sup he' hk
  have hEH : IsSylowOf p E (E ⊔ ψ.ker) := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_left, hEp, ?_⟩
    have h3 := Subgroup.relIndex_mul_card E ψ.ker
    rw [hEker, Subgroup.card_bot, mul_one] at h3
    have h4 := relIndex_sup_eq_relIndex_of_normal ψ.ker E
    rw [sup_comm, h4, h3]
    exact hker
  set E' : Subgroup L := E.map (MulAut.conj x').toMonoidHom with hE'
  have hE'le : E' ≤ E ⊔ ψ.ker := by
    rintro _ ⟨e, he, rfl⟩
    exact hconjmem e he
  have hE'H : IsSylowOf p E' (E ⊔ ψ.ker) := by
    apply isSylowOf_of_card hE'le
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj x').injective, hEH.card_eq]
  obtain ⟨c, hcH, hc⟩ := hEH.exists_mem_conj hE'H
  obtain ⟨x, hxdef⟩ : ∃ x : L, x = c⁻¹ * x' := ⟨_, rfl⟩
  have hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro e he
    have h1 : x' * e * x'⁻¹ ∈ E' := ⟨e, he, by simp [MulAut.conj_apply]⟩
    have h2 := (hc _).1 h1
    have : x * e * x⁻¹ = c⁻¹ * (x' * e * x'⁻¹) * c := by rw [hxdef]; group
    rw [this]
    exact h2
  refine ⟨x, mem_normalizer_of_forward_uc6 hxE, ?_⟩
  intro e he
  have hxx : x * x * e * (x * x)⁻¹ ∈ E := by
    have h1 := hxE e he
    have h2 := hxE _ h1
    have : x * x * e * (x * x)⁻¹ = x * (x * e * x⁻¹) * x⁻¹ := by group
    rw [this]
    exact h2
  have hinj' : ∀ a ∈ E, ∀ b ∈ E, ψ a = ψ b → a = b := by
    intro a ha b hb h
    have := hinjE (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h
    exact congrArg Subtype.val this
  have hab : ∀ a ∈ E.map ψ, ∀ b ∈ E.map ψ, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hEab a ha b hb]
  have hψc : ψ c ∈ E.map ψ := by
    have hmul := Subgroup.mul_normal E ψ.ker
    have : c ∈ (↑(E ⊔ ψ.ker) : Set L) := hcH
    rw [hmul] at this
    obtain ⟨e', he', k, hk, rfl⟩ := this
    rw [map_mul, (MonoidHom.mem_ker.1 hk), mul_one]
    exact Subgroup.mem_map_of_mem ψ he'
  have hz : (ψ c)⁻¹ ∈ E.map ψ := (E.map ψ).inv_mem hψc
  obtain ⟨z, hzdef⟩ : ∃ z : M₀, z = (ψ c)⁻¹ := ⟨_, rfl⟩
  rw [← hzdef] at hz
  have hψx : ψ x = z * x₁ := by rw [hxdef, map_mul, map_inv, hx', hzdef]
  have hz' : x₁ * z * x₁⁻¹ ∈ E.map ψ := hx₁N z hz
  have hw : ψ e ∈ E.map ψ := Subgroup.mem_map_of_mem ψ he
  have key : ψ (x * x * e * (x * x)⁻¹) = (ψ e)⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_mul, hψx]
    have e1 : z * x₁ * (z * x₁) * ψ e * (z * x₁ * (z * x₁))⁻¹ =
        (z * (x₁ * z * x₁⁻¹)) * (x₁ * x₁ * ψ e * (x₁ * x₁)⁻¹) * (z * (x₁ * z * x₁⁻¹))⁻¹ := by
      group
    rw [e1, hx₁inv _ hw]
    have hmem : z * (x₁ * z * x₁⁻¹) ∈ E.map ψ := (E.map ψ).mul_mem hz hz'
    have hcomm := hab _ hmem _ ((E.map ψ).inv_mem hw)
    rw [hcomm, mul_inv_cancel_right]
  exact hinj' _ hxx _ (E.inv_mem he) (by rw [key, map_inv])

end CFSG.LocalAnalysis.UniquenessCase.UC6
