module

public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup
open scoped Pointwise commutatorElement

variable {C : Type*} [Group C]

@[expose] def permProd (A U : Subgroup C) (hAU : (A : Set C) * (U : Set C) = (U : Set C) * A) :
    Subgroup C where
  carrier := (A : Set C) * (U : Set C)
  mul_mem' := by
    rintro _ _ ⟨x, hx, s, hs, rfl⟩ ⟨x', hx', s', hs', rfl⟩
    have hsx : s * x' ∈ (U : Set C) * (A : Set C) := ⟨s, hs, x', hx', rfl⟩
    rw [← hAU] at hsx
    obtain ⟨x'', hx'', s'', hs'', he⟩ := hsx
    have he : x'' * s'' = s * x' := he
    refine ⟨x * x'', A.mul_mem hx hx'', s'' * s', U.mul_mem hs'' hs', ?_⟩
    calc x * x'' * (s'' * s') = x * (x'' * s'') * s' := by group
      _ = x * s * (x' * s') := by rw [he]; group
  one_mem' := ⟨1, A.one_mem, 1, U.one_mem, one_mul 1⟩
  inv_mem' := by
    rintro _ ⟨x, hx, s, hs, rfl⟩
    have h : s⁻¹ * x⁻¹ ∈ (U : Set C) * (A : Set C) :=
      ⟨s⁻¹, U.inv_mem hs, x⁻¹, A.inv_mem hx, rfl⟩
    rw [← hAU] at h
    simpa [mul_inv_rev] using h

theorem le_permProd_left (A U : Subgroup C) (hAU : (A : Set C) * (U : Set C) = (U : Set C) * A) :
    A ≤ permProd A U hAU :=
  fun x hx => ⟨x, hx, 1, U.one_mem, mul_one x⟩

theorem le_permProd_right (A U : Subgroup C) (hAU : (A : Set C) * (U : Set C) = (U : Set C) * A) :
    U ≤ permProd A U hAU :=
  fun s hs => ⟨1, A.one_mem, s, hs, one_mul s⟩

theorem card_permProd [Finite C] (A U : Subgroup C)
    (hAU : (A : Set C) * (U : Set C) = (U : Set C) * A) :
    ∃ d, d ∣ Nat.card A ∧ Nat.card (permProd A U hAU) = Nat.card U * d := by
  classical
  set d := Nat.card ((QuotientGroup.mk : C → C ⧸ U) '' (A : Set C)) with hd
  refine ⟨d, ?_, Subgroup.card_mul_eq_card_subgroup_mul_card_quotient U (A : Set C)⟩
  have h1 : (QuotientGroup.mk : C → C ⧸ U) '' (A : Set C) =
      MulAction.orbit A ((1 : C) : C ⧸ U) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      change g • ((1 : C) : C ⧸ U) = (g : C ⧸ U)
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
    · rintro ⟨⟨g, hg⟩, rfl⟩
      refine ⟨g, hg, ?_⟩
      change (g : C ⧸ U) = g • ((1 : C) : C ⧸ U)
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
  have h2 := MulAction.index_stabilizer A ((1 : C) : C ⧸ U)
  rw [← h1, ← Nat.card_coe_set_eq] at h2
  rw [hd, ← h2]
  exact Subgroup.index_dvd_card _

theorem not_three_dvd_card_permProd [Finite C] (A U : Subgroup C)
    (hAU : (A : Set C) * (U : Set C) = (U : Set C) * A) (hA : ¬ 3 ∣ Nat.card A)
    (hU : IsPGroup 2 U) : ¬ 3 ∣ Nat.card (permProd A U hAU) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hdA, hcard⟩ := card_permProd A U hAU
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  rw [hcard, hk]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  · exact hA (h.trans hdA)

theorem commutator_le_of_coe_eq_mul {G : Type*} [Group G] {B U H : Subgroup G}
    (hB : (B : Set G) = (U : Set G) * (H : Set G)) (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hN : ∀ t ∈ H, ∀ u ∈ U, t * u * t⁻¹ ∈ U) : ⁅B, B⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h1 : g₁ ∈ (U : Set G) * (H : Set G) := hB ▸ hg₁
  have h2 : g₂ ∈ (U : Set G) * (H : Set G) := hB ▸ hg₂
  obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := h1
  obtain ⟨u₂, hu₂, t₂, ht₂, rfl⟩ := h2
  have hc : t₂ * t₁⁻¹ = t₁⁻¹ * t₂ := by
    calc t₂ * t₁⁻¹ = t₁⁻¹ * (t₁ * t₂) * t₁⁻¹ := by group
      _ = t₁⁻¹ * (t₂ * t₁) * t₁⁻¹ := by rw [hH t₁ ht₁ t₂ ht₂]
      _ = t₁⁻¹ * t₂ := by group
  have e : ⁅u₁ * t₁, u₂ * t₂⁆ = u₁ * (t₁ * u₂ * t₁⁻¹) * (t₂ * u₁⁻¹ * t₂⁻¹) * u₂⁻¹ := by
    calc ⁅u₁ * t₁, u₂ * t₂⁆ = u₁ * t₁ * u₂ * (t₂ * t₁⁻¹) * u₁⁻¹ * t₂⁻¹ * u₂⁻¹ := by group
      _ = u₁ * t₁ * u₂ * (t₁⁻¹ * t₂) * u₁⁻¹ * t₂⁻¹ * u₂⁻¹ := by rw [hc]
      _ = u₁ * (t₁ * u₂ * t₁⁻¹) * (t₂ * u₁⁻¹ * t₂⁻¹) * u₂⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hu₁ (hN t₁ ht₁ u₂ hu₂)) (hN t₂ ht₂ _ (inv_mem hu₁)))
    (inv_mem hu₂)

theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    rw [mul_left_inj, mul_right_inj] at hyx'
    rwa [← hyx']

structure ThreeFreeBorelDatum (U B : Subgroup C) : Prop where
  le : U ≤ B
  commutator_le : ⁅B, B⁆ ≤ U
  normalizer_le : normalizer (U : Set C) ≤ B
  isPGroup : IsPGroup 2 U
  three_free : ∀ D : Subgroup C, U ≤ D → ¬ 3 ∣ Nat.card D → D ≤ B

namespace ThreeFreeBorelDatum

variable {U B : Subgroup C}

theorem map (h : ThreeFreeBorelDatum U B) (e : C ≃* C) :
    ThreeFreeBorelDatum (U.map e.toMonoidHom) (B.map e.toMonoidHom) where
  le := Subgroup.map_mono h.le
  commutator_le := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono h.commutator_le
  normalizer_le := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono h.normalizer_le
  isPGroup := h.isPGroup.map _
  three_free D hUD h3 := by
    have hD : D = (D.map e.symm.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map]
      ext x
      simp
    rw [hD]
    refine Subgroup.map_mono (h.three_free _ ?_ ?_)
    · have := Subgroup.map_mono (f := e.symm.toMonoidHom) hUD
      rwa [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id C from
        MonoidHom.ext fun x => by simp, Subgroup.map_id] at this
    · rwa [Subgroup.card_map_of_injective e.symm.injective]

theorem commute_of_permutable [Finite C] (h : ThreeFreeBorelDatum U B) (A : Subgroup C)
    (hodd : Odd (Nat.card A)) (h3 : ¬ 3 ∣ Nat.card A)
    (hAU : (A : Set C) * (U : Set C) = (U : Set C) * A) :
    A ≤ B ∧ A ⊓ U = ⊥ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ∀ g ∈ normalizer (U : Set C), g ∈ normalizer (A : Set C) → ∀ a ∈ A, g * a * g⁻¹ = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAB : A ≤ B := (le_permProd_left A U hAU).trans
    (h.three_free _ (le_permProd_right A U hAU)
      (not_three_dvd_card_permProd A U hAU h3 h.isPGroup))
  have hAU' : A ⊓ U = ⊥ := by
    obtain ⟨k, hk⟩ := h.isPGroup.exists_card_eq
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
  have hkey : ∀ x ∈ A, ∀ y ∈ B, x ∈ B → y * x * y⁻¹ ∈ A → y * x * y⁻¹ = x := by
    intro x hx y hy hxB hyx
    have hc : ⁅y, x⁆ ∈ U :=
      h.commutator_le (Subgroup.commutator_mem_commutator hy hxB)
    have hcA : ⁅y, x⁆ ∈ A := by
      rw [commutatorElement_def]
      exact A.mul_mem hyx (A.inv_mem hx)
    have h1 : ⁅y, x⁆ = 1 := by
      have : ⁅y, x⁆ ∈ A ⊓ U := ⟨hcA, hc⟩
      rwa [hAU', Subgroup.mem_bot] at this
    rw [commutatorElement_def] at h1
    calc y * x * y⁻¹ = y * x * y⁻¹ * x⁻¹ * x := by group
      _ = x := by rw [h1, one_mul]
  refine ⟨hAB, hAU', fun a ha b hb => ?_, fun g hgU hgA a ha => ?_⟩
  · have := hkey b hb a (hAB ha) (hAB hb) (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha))
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [this]
  · exact hkey a ha g (h.normalizer_le hgU) (hAB ha) ((mem_normalizer_iff.1 hgA a).1 ha)

end ThreeFreeBorelDatum

theorem map_isCyclic_of_ker_le {Γ F M : Type*} [Group Γ] [Group F] [Group M] [Finite F]
    [IsCyclic F] (θ : Γ →* F) (ρ : Γ →* M) (hker : θ.ker ≤ ρ.ker) (Δ : Subgroup Γ) :
    IsCyclic (Δ.map ρ) ∧ Nat.card (Δ.map ρ) ∣ Nat.card F := by
  set θ' := θ.comp Δ.subtype
  set ρ' := ρ.comp Δ.subtype
  have hk : θ'.ker ≤ ρ'.ker := fun x hx => hker hx
  have hr : ρ'.range = Δ.map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hsurj : Function.Surjective (QuotientGroup.map θ'.ker ρ'.ker (MonoidHom.id Δ) hk) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hθc : IsCyclic (Δ ⧸ θ'.ker) :=
    isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange θ').symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange θ').symm.surjective
  have hρc : IsCyclic (Δ ⧸ ρ'.ker) := isCyclic_of_surjective _ hsurj
  have : Finite (Δ ⧸ θ'.ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange θ').symm.toEquiv
  rw [← hr]
  refine ⟨isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange ρ').toMonoidHom
    (QuotientGroup.quotientKerEquivRange ρ').surjective, ?_⟩
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ').toEquiv]
  refine (Subgroup.card_dvd_of_surjective hsurj).trans ?_
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange θ').toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

end CFSG.Quasithin.H13.NQTerm
