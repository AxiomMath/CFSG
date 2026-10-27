module

public import CFSG.Quasithin.EmptyFaithful.S146zRPair
public import CFSG.Quasithin.EmptyFaithful.S146zRWr

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

section Pure

variable {X : Type} [Group X] [Finite X] {N₁ N₂ : Subgroup X} {ŝ : X}

omit [Finite X] in
theorem q_card_conj_eq (hF : CaseIFacts N₁ N₂ ŝ) : Nat.card N₂ = Nat.card N₁ := by
  rw [hF.conj]
  exact Subgroup.card_map_of_injective (MulAut.conj ŝ).injective

omit [Finite X] in
theorem q_card_sup_pair (hF : CaseIFacts N₁ N₂ ŝ) : Nat.card ↥(N₁ ⊔ N₂) = Nat.card N₁ ^ 2 := by
  rw [SBc15.card_sup_eq_mul_of_commute hF.comm (disjoint_iff.mpr hF.disj), q_card_conj_eq hF, sq]

omit [Finite X] in
theorem q_ne_pair (hF : CaseIFacts N₁ N₂ ŝ) (hbot : N₁ ≠ ⊥) : N₁ ≠ N₂ := fun h => by
  apply hbot
  have := hF.disj
  rwa [← h, inf_idem] at this

omit [Finite X] in
theorem q_normalizes_of_comm {A B : Subgroup X} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set X) := fun x hx => by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ = y := by rw [hc x hx y hy]; group
    rw [this]; exact hy
  · intro hy
    have e1 := hc x hx _ hy
    have e2 : x * y * x⁻¹ = y := by
      have e3 : x * (x * y * x⁻¹) = x * y := by rw [e1]; group
      exact mul_left_cancel e3
    rw [e2] at hy
    exact hy

omit [Finite X] in
theorem q_sup_le_normalizer (hF : CaseIFacts N₁ N₂ ŝ) :
    N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₁ : Set X) :=
  sup_le Subgroup.le_normalizer
    (q_normalizes_of_comm (A := N₂) (B := N₁) fun b hb a ha => (hF.comm a ha b hb).symm)

omit [Finite X] in
theorem q_exists_mul_of_mem_sup (hF : CaseIFacts N₁ N₂ ŝ) {x : X} (hx : x ∈ N₁ ⊔ N₂) :
    ∃ a ∈ N₁, ∃ b ∈ N₂, x = a * b := by
  have hmul : (↑(N₁ ⊔ N₂) : Set X) = ↑N₁ * ↑N₂ :=
    Subgroup.coe_mul_of_left_le_normalizer_right N₁ N₂ (q_normalizes_of_comm hF.comm)
  have hx' : x ∈ (↑(N₁ ⊔ N₂) : Set X) := hx
  rw [hmul] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

omit [Finite X] in
theorem q_mem_normalizer_snd (hF : CaseIFacts N₁ N₂ ŝ) (hbot : N₁ ≠ ⊥) {x : X}
    (hx : x ∈ Subgroup.normalizer (N₁ : Set X)) : x ∈ Subgroup.normalizer (N₂ : Set X) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rcases QWr.conj_N₂_cases hF.conj hF.perm x with h | h
  · exact absurd (QWr.map_conj_injective x ((Subgroup.mem_normalizer_iff_map_conj_eq.mp hx).trans
      h.symm)) (q_ne_pair hF hbot)
  · exact h

omit [Finite X] in
theorem q_not_mem_sup (hF : CaseIFacts N₁ N₂ ŝ) (hbot : N₁ ≠ ⊥) : ŝ ∉ N₁ ⊔ N₂ := by
  intro h
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (q_sup_le_normalizer hF h)
  exact q_ne_pair hF hbot (h1.symm.trans hF.conj.symm)

theorem q_card_lower_wreath (hF : CaseIFacts N₁ N₂ ŝ) (hbot : N₁ ≠ ⊥) :
    2 * Nat.card N₁ ^ 2 ≤ Nat.card X := by
  have hN : N₁ ⊔ N₂ ≠ ⊤ := fun h => q_not_mem_sup hF hbot (h ▸ Subgroup.mem_top ŝ)
  have h2 : 2 ≤ (N₁ ⊔ N₂).index := by
    have h0 : (N₁ ⊔ N₂).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : (N₁ ⊔ N₂).index ≠ 1 := fun h => hN (Subgroup.index_eq_one.mp h)
    omega
  have := Subgroup.index_mul_card (N₁ ⊔ N₂)
  rw [q_card_sup_pair hF] at this
  rw [← this]
  exact Nat.mul_le_mul_right _ h2

omit [Finite X] in
theorem q_eq_one_of_centralizes (hF : CaseIFacts N₁ N₂ ŝ) {x : X}
    (h₁ : ∀ n ∈ N₁, x * n = n * x) (h₂ : ∀ n ∈ N₂, x * n = n * x) : x = 1 := by
  have hZ₂ : ∀ n ∈ N₂, (∀ m ∈ N₂, n * m = m * n) → n = 1 := by
    rw [hF.conj]
    exact q_centreless_conj hF.centreless _
  have hZ := q_centreless_sup hF.comm hF.centreless hZ₂
  have hall : ∀ n ∈ N₁ ⊔ N₂, x * n = n * x := by
    intro n hn
    have hmul : (↑(N₁ ⊔ N₂) : Set X) = ↑N₁ * ↑N₂ :=
      Subgroup.coe_mul_of_left_le_normalizer_right N₁ N₂ (q_normalizes_of_comm hF.comm)
    have hn' : n ∈ (↑(N₁ ⊔ N₂) : Set X) := hn
    rw [hmul] at hn'
    obtain ⟨a, ha, b, hb, rfl⟩ := hn'
    show x * (a * b) = a * b * x
    rw [← mul_assoc, h₁ a ha, mul_assoc, h₂ b hb, ← mul_assoc]
  have hx : x ∈ N₁ ⊔ N₂ := hF.cen x hall
  exact hZ x hx fun m hm => hall m hm

theorem q_isPGroup_quotient_of_card_aut [(N₁ ⊔ N₂).Normal] (hF : CaseIFacts N₁ N₂ ŝ)
    (hbot : N₁ ≠ ⊥) (hA : Nat.card (MulAut ↥N₁) = 2 * Nat.card ↥N₁) :
    IsPGroup 2 (X ⧸ (N₁ ⊔ N₂)) := by
  classical
  have hne := q_ne_pair hF hbot
  obtain ⟨σ, hσs, hσ⟩ := QWr.exists_sigma hF.conj hne hF.perm
  have hX₀ : ∀ x, x ∈ σ.ker ↔ N₁.map (MulAut.conj x).toMonoidHom = N₁ := fun x => by
    rw [MonoidHom.mem_ker]
    exact hσ x
  have hidx : σ.ker.index ∣ 2 := by
    rw [Subgroup.index_ker]
    have h1 := Subgroup.card_subgroup_dvd_card σ.range
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd]
      exact Nat.card_zmod 2
    rwa [h2] at h1
  have hN₁X₀ : ∀ x ∈ σ.ker, x ∈ Subgroup.normalizer (N₁ : Set X) := fun x hx =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr ((hX₀ x).mp hx)
  have hN₂X₀ : ∀ x ∈ σ.ker, x ∈ Subgroup.normalizer (N₂ : Set X) := by
    intro x hx
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rcases QWr.conj_N₂_cases hF.conj hF.perm x with h | h
    · exact absurd (QWr.map_conj_injective x (((hX₀ x).mp hx).trans h.symm)) hne
    · exact h
  have hNX₀ : N₁ ⊔ N₂ ≤ σ.ker := by
    intro x hx
    rw [hX₀]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (q_sup_le_normalizer hF hx)
  let ν : ↥σ.ker →* MulAut ↥N₁ × MulAut ↥N₂ :=
    ((N₁.normalizerMonoidHom).comp (Subgroup.inclusion (fun x hx => hN₁X₀ x hx) :
        ↥σ.ker →* ↥(Subgroup.normalizer (N₁ : Set X)))).prod
      ((N₂.normalizerMonoidHom).comp (Subgroup.inclusion (fun x hx => hN₂X₀ x hx) :
        ↥σ.ker →* ↥(Subgroup.normalizer (N₂ : Set X))))
  have hν : Function.Injective ν := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : N₁.normalizerMonoidHom ⟨(x : X), hN₁X₀ x x.2⟩ = 1 := congrArg Prod.fst hx
    have h2 : N₂.normalizerMonoidHom ⟨(x : X), hN₂X₀ x x.2⟩ = 1 := congrArg Prod.snd hx
    have hc₁ : ∀ n ∈ N₁, (x : X) * n = n * (x : X) := fun n hn => by
      have := Subgroup.normalizerMonoidHom_apply_apply_coe N₁ ⟨(x : X), hN₁X₀ x x.2⟩ ⟨n, hn⟩
      rw [h1] at this
      simp only [MulAut.one_apply] at this
      calc (x : X) * n = (x : X) * n * (x : X)⁻¹ * (x : X) := by group
        _ = n * (x : X) := by rw [← this]
    have hc₂ : ∀ n ∈ N₂, (x : X) * n = n * (x : X) := fun n hn => by
      have := Subgroup.normalizerMonoidHom_apply_apply_coe N₂ ⟨(x : X), hN₂X₀ x x.2⟩ ⟨n, hn⟩
      rw [h2] at this
      simp only [MulAut.one_apply] at this
      calc (x : X) * n = (x : X) * n * (x : X)⁻¹ * (x : X) := by group
        _ = n * (x : X) := by rw [← this]
    exact Subtype.ext (q_eq_one_of_centralizes hF hc₁ hc₂)
  have hfin₁ : Finite (MulAut ↥N₁) :=
    Finite.of_injective (fun g : MulAut ↥N₁ => (g : ↥N₁ → ↥N₁)) DFunLike.coe_injective
  have hfin₂ : Finite (MulAut ↥N₂) :=
    Finite.of_injective (fun g : MulAut ↥N₂ => (g : ↥N₂ → ↥N₂)) DFunLike.coe_injective
  have hAut₂ : Nat.card (MulAut ↥N₂) = Nat.card (MulAut ↥N₁) := by
    let e : ↥N₁ ≃* ↥N₂ :=
      (N₁.equivMapOfInjective (MulAut.conj ŝ).toMonoidHom (MulAut.conj ŝ).injective).trans
        (MulEquiv.subgroupCongr hF.conj.symm)
    exact (Nat.card_congr (MulAut.congr e).toEquiv).symm
  have hd1 : Nat.card ↥σ.ker ∣ Nat.card (MulAut ↥N₁) * Nat.card (MulAut ↥N₂) := by
    have := Subgroup.card_dvd_of_injective ν hν
    rwa [Nat.card_prod] at this
  rw [hAut₂, hA] at hd1
  have hn : 0 < Nat.card ↥N₁ := Nat.card_pos
  have hd2 : Nat.card ↥σ.ker ∣ 4 * Nat.card ↥N₁ ^ 2 := by
    have : 2 * Nat.card ↥N₁ * (2 * Nat.card ↥N₁) = 4 * Nat.card ↥N₁ ^ 2 := by ring
    rwa [this] at hd1
  have hX : Nat.card X ∣ 8 * Nat.card ↥N₁ ^ 2 := by
    have h1 := Subgroup.index_mul_card σ.ker
    rw [← h1]
    have := Nat.mul_dvd_mul hidx hd2
    rwa [show 2 * (4 * Nat.card ↥N₁ ^ 2) = 8 * Nat.card ↥N₁ ^ 2 by ring] at this
  have h8 : (N₁ ⊔ N₂).index ∣ 8 := by
    have h1 := Subgroup.index_mul_card (N₁ ⊔ N₂)
    rw [q_card_sup_pair hF] at h1
    rw [← h1] at hX
    have hpos : 0 < Nat.card ↥N₁ ^ 2 := pow_pos hn 2
    have : (N₁ ⊔ N₂).index * Nat.card ↥N₁ ^ 2 ∣ 8 * Nat.card ↥N₁ ^ 2 := hX
    exact Nat.dvd_of_mul_dvd_mul_right hpos this
  have h8' : (N₁ ⊔ N₂).index ∣ 2 ^ 3 := by norm_num; exact h8
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 3)).mp h8'
  exact IsPGroup.of_card (n := k) (by rw [← Subgroup.index_eq_card, hk])

theorem q_exists_mul_of_sylow {N : Subgroup X} [N.Normal] (hq : IsPGroup 2 (X ⧸ N))
    {P : Subgroup X} (hPi : ¬ 2 ∣ P.index) (x : X) :
    ∃ n ∈ N, ∃ t ∈ P, x = n * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : X →* X ⧸ N := QuotientGroup.mk' N with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective N
  have htop : P.map ρ = ⊤ := by
    have h1 : (P.map ρ).index ∣ P.index := Subgroup.index_map_dvd P hρs
    obtain ⟨m, hm⟩ := hq.index (P.map ρ)
    rw [← Subgroup.index_eq_one]
    by_contra hne
    have hm0 : m ≠ 0 := fun h0 => hne (by rw [hm, h0, pow_zero])
    exact hPi ((dvd_pow_self 2 hm0).trans (hm ▸ h1))
  have hx : ρ x ∈ P.map ρ := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨t, htP, ht⟩ := hx
  refine ⟨x * t⁻¹, ?_, t, htP, by group⟩
  have : ρ (x * t⁻¹) = 1 := by rw [map_mul, map_inv, ← ht, mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff _).mp this

end Pure

end CFSG.Quasithin
