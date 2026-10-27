module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestCover
public import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed

public section

namespace CFSG.StandardType

namespace TableBUR

open CFSG.Assembly Subgroup CFSG.LieType.Steinberg.CentralExt CFSG.ClassicalGroups.UnitaryFlag

theorem not_dvd_card_ker_of_cover_trivial {H : Type*} [Group H] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (htriv : ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* H),
      Function.Surjective η → η.ker ≤ center P → IsPGroup ℓ η.ker → η.ker = ⊥)
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* H)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) : ¬ ℓ ∣ Nat.card π.ker := by
  intro hdvd
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set N := CoprimeSplit.copPart ℓ π.ker hcen
  have hNker : N ≤ π.ker := fun _ h => h.1
  let π₁ : E ⧸ N →* H := QuotientGroup.lift N π hNker
  have hπ₁e : ∀ e : E, π₁ (e : E ⧸ N) = π e := fun e => rfl
  have hπ₁ : Function.Surjective π₁ := fun g => by
    obtain ⟨e, rfl⟩ := hπ g
    exact ⟨(e : E ⧸ N), rfl⟩
  have hker₁ : π₁.ker ≤ center (E ⧸ N) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁e]
      exact hy
    rw [mem_center_iff]
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 (hcen he) z']
  have hp₁ : IsPGroup ℓ π₁.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁e]
      exact hy
    obtain ⟨a, ha⟩ := CoprimeSplit.exists_pow_prime_pow_mem_copPart (p := ℓ) hcen he
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  have : Group.IsPerfect (E ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have h0 := htriv (E ⧸ N) π₁ hπ₁ hker₁ hp₁
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hgN : (g : E) ∈ N := by
    have hmem : ((g : E) : E ⧸ N) ∈ π₁.ker := by
      rw [MonoidHom.mem_ker, hπ₁e]
      exact g.2
    rw [h0, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  have hord : orderOf (g : E) = ℓ := by rw [Subgroup.orderOf_coe, hg]
  have hcop := hgN.2
  rw [hord] at hcop
  exact hℓ.one_lt.ne' ((Nat.coprime_self ℓ).1 hcop)

section SU

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem suScalars_eq_bot_four (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : ¬ 3 ∣ d) :
    (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K (2 ^ 1)) = ⊥ := by
  have h := TableBU.unitaryFieldData_of_card hK (le_refl 1)
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : z ∈ (LargeEvenProjMk (unitarySU 2 1 K d)).ker := by
    rw [LargeEvenProjMk, QuotientGroup.ker_mk']
    exact hz
  refine TableBUE.eq_one_of_mem_suScalars h Nat.prime_three hd hz' ?_
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  have hc3 : c ^ 3 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have := FiniteField.pow_card_sub_one_eq_one (c : K) c.ne_zero
    rwa [hcard] at this
  apply Subtype.ext
  change ((z : GL (Fin d) K)) ^ 3 = 1
  rw [← hc, ← map_pow, hc3, map_one]

@[expose] noncomputable def projEquivSU {q : ℕ}
    (hbot : (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K q) = ⊥) :
    LargeEvenProj (LargeEvenSUGroup (Fin d) K q) ≃* LargeEvenSUGroup (Fin d) K q :=
  (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot

theorem not_three_dvd_card_ker
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : d = 4 ∨ d = 5)
    (L' : Type) [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center L') (hperf : commutator L' = ⊤) : ¬ 3 ∣ Nat.card ψ.ker := by
  have h := TableBU.unitaryFieldData_of_card hK (le_refl 1)
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd3 : ¬ 3 ∣ d := by rcases hd with rfl | rfl <;> norm_num
  have hbot := suScalars_eq_bot_four hK hd3
  have : Group.IsPerfect L' := ⟨hperf⟩
  set e : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)) ≃*
      CFSG.LieType.Universal.Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 1) d :=
    (projEquivSU hbot).trans (CFSG.LieType.Universal.Unitary.equivStatedSU hK d).symm with he
  refine not_dvd_card_ker_of_cover_trivial Nat.prime_three
    (fun P _ _ _ η hη hcen hk => ?_) ψ hψ hker
  set η' := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hη', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective]
  have hsurj : Function.Surjective η' := e.surjective.comp hη
  have hcen' : η'.ker ≤ center P := hker' ▸ hcen
  have hk' : IsPGroup 3 η'.ker := hker' ▸ hk
  suffices hs : ∃ s : CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution K 2 1) d →* P, ∀ x, η' (s x) = x by
    obtain ⟨s, hs⟩ := hs
    rw [← hker']
    exact SUOdd.ker_eq_bot_of_section hcen' hs
  rcases hd with rfl | rfl
  · obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hk'
    exact SUClosed.su_exists_section_of_coprime hK (by decide) (by norm_num) hsurj hcen'
      (by rw [hm]; exact Nat.Coprime.pow_right m (by norm_num))
  · exact SUOdd.su_odd_exists_section_of_ne hK (le_refl 1) Nat.prime_three (by norm_num)
      (by norm_num) (by decide) hsurj hcen' hk'

end SU

end TableBUR

end CFSG.StandardType
