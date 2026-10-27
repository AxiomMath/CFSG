module

public import CFSG.Quasithin.Vol2.Ch11SecO6P
public import CFSG.Quasithin.Vol2.Ch11SecEFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Quasithin CFSG.Open CFSG.Blueprint

variable {X : Type} [Group X]

theorem mul_comm_of_homocyclic {r : ℕ} (hP : IsHomocyclicRank2 r ↥(CFSG.pCore r X)) :
    ∀ d ∈ CFSG.pCore r X, ∀ e ∈ CFSG.pCore r X, d * e = e * d := by
  obtain ⟨n, -, ⟨φ⟩⟩ := hP
  intro d hd e he
  have h : (⟨d, hd⟩ : ↥(CFSG.pCore r X)) * ⟨e, he⟩ = ⟨e, he⟩ * ⟨d, hd⟩ := by
    apply φ.injective
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val h

theorem shape_of_elemAbelian [Finite X] {q : ℕ} [Fact q.Prime]
    (hE : IsElemAbelianOfRank q 2 ↥(CFSG.fittingSubgroup X)) :
    Nat.card (CFSG.fittingSubgroup X) = q ^ 2 ∧
      (∀ d ∈ CFSG.pCore q X, ∀ e ∈ CFSG.pCore q X, d * e = e * d) ∧
      ∀ e ∈ CFSG.pCore q X, e ^ q = 1 := by
  obtain ⟨φ⟩ := hE
  set F := CFSG.fittingSubgroup X
  refine ⟨?_, fun d hd e he => ?_, fun e he => ?_⟩
  · rw [Nat.card_congr φ.toEquiv]
    change Nat.card (Fin 2 → ZMod q) = q ^ 2
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  · have hdF := CFSG.pCore_le_fitting X q hd
    have heF := CFSG.pCore_le_fitting X q he
    have h : (⟨d, hdF⟩ : ↥F) * ⟨e, heF⟩ = ⟨e, heF⟩ * ⟨d, hdF⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val h
  · have heF := CFSG.pCore_le_fitting X q he
    have h : (⟨e, heF⟩ : ↥F) ^ q = 1 := by
      apply φ.injective
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      funext i
      rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        Pi.zero_apply]
    have := congrArg Subtype.val h
    simpa using this


theorem factOut2Case1_of_inverts
    (hinvP : ∀ (X : Type) [Group X] [Finite X], Case1Data X →
      ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ → ∀ r : ℕ, ∀ _ : Fact r.Prime,
      r ∣ Nat.card (CFSG.fittingSubgroup X) → ∀ s : X, s ∉ CFSG.fittingSubgroup X →
      s ^ 2 ∈ CFSG.fittingSubgroup X → IsPGroup 2 (Subgroup.zpowers s) →
      ActsScalar r (MulAut.conj s) (r - 1)) :
    SecE.FactOut2Case1 := by
  intro G _ _ K n hl h1 hperf
  have hD := case1Data_kBar hl h1
  have hX := SecG.Bar.commutator_top_eq_top hperf
  obtain ⟨p, hp, hp5, φ, hφ, -⟩ := SecG.exists_oddCore_of_case11_1_2One h1
  have : Fact p.Prime := ⟨hp⟩
  rcases shape_of_lists hl (by omega) hφ with h4 | ⟨q, hq, -, -, -, hE, -⟩
  · refine out2Closed_of_case1 hD hX (fun r hr hrF => ?_) (hinvP _ hD hX)
    have : Fact r.Prime := ⟨hr⟩
    rcases (h4.2.2.2 r hr hrF).2 with hP | hP
    · exact Or.inl hP
    · exact Or.inr ⟨mul_comm_of_homocyclic hP, fun u hu hu' b hub =>
        zpow_eq_one_of_homocyclic r hP hu hu' hub⟩
  · have : Fact q.Prime := ⟨hq⟩
    obtain ⟨hcard, hab, hexp⟩ := shape_of_elemAbelian hE
    have hrq : ∀ r : ℕ, r.Prime → r ∣ Nat.card (CFSG.fittingSubgroup (SecG.Bar.KBar K)) →
        r = q := fun r hr hrF =>
      (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow (hcard ▸ hrF))
    have hFq : IsPGroup q (CFSG.fittingSubgroup (SecG.Bar.KBar K)) := IsPGroup.of_card hcard
    refine out2Closed_of_case1 hD hX (fun r hr hrF => ?_) (fun r _ hrF s hs hs2 h2 => ?_)
    · obtain rfl := hrq r hr hrF
      exact Or.inr ⟨hab, fun u hu hu' b hub => zpow_eq_one_of_exponent r hexp hu hu' hub⟩
    · obtain rfl := hrq r Fact.out hrF
      exact inverts_of_pGroup r hD hrF hFq hs hs2 h2

end CFSG.Quasithin.Vol2.Ch11.O6
