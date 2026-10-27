module

public import CFSG.Quasithin.EmptyFaithful.SBd13El
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHe
public import CFSG.Quasithin.Background.A318POutHe

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

@[expose] def FactHeCentralizer : Prop :=
  F420.SmallCentralizerWitness (NativeSporadic.Carrier .He)

end CFSG.Quasithin.ModH

namespace CFSG.Quasithin.ModH.HeEl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c14 CFSG.Quasithin.F420 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem pow_apply_of_fix {X : Type} [Group X] {S : Subgroup X} (ζ : MulAut X)
    (h : ∀ s ∈ S, ζ s = s) (k : ℕ) : ∀ s ∈ S, (ζ ^ k) s = s := by
  intro s hs
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, h s hs, ih]

theorem not_elConfig_of_prime_inner {X : Type} [Group X] [Finite X]
    (hinner : ∀ S : Subgroup X, quasithinIsSylowTwo S → ∀ α : MulAut X, (∀ s ∈ S, α s = s) →
      (orderOf α).Prime → ∃ x : X, ∀ y : X, α y = x⁻¹ * y * x)
    (hW : SmallCentralizerWitness X) : ¬ ElConfig X := by
  rintro ⟨T, V, H, ζ, hT, hd⟩
  have hTS : quasithinIsSylowTwo T := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
    exact ⟨hp, hi⟩
  have : Finite (MulAut X) := inferInstanceAs (Finite (X ≃* X))
  have hm0 : orderOf ζ ≠ 0 := (orderOf_pos ζ).ne'
  have hm1 : orderOf ζ ≠ 1 := fun h => hd.ne (orderOf_eq_one_iff.1 h)
  have hp : (orderOf ζ).minFac.Prime := Nat.minFac_prime hm1
  set ζ' : MulAut X := ζ ^ (orderOf ζ / (orderOf ζ).minFac) with hζ'
  have hord : orderOf ζ' = (orderOf ζ).minFac := orderOf_pow_orderOf_div hm0 (Nat.minFac_dvd _)
  have hfixT : ∀ t ∈ T, ζ' t = t := pow_apply_of_fix ζ hd.fixT _
  have hfixH : ∀ h ∈ H, ζ' h = h := pow_apply_of_fix ζ hd.fixH _
  have hne : ζ' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact hp.one_lt.ne hord
  obtain ⟨x, hx⟩ := hinner T hTS ζ' hfixT (by rw [hord]; exact hp)
  have hcomm : ∀ s : X, ζ' s = s → x * s = s * x := by
    intro s hs
    have h1 : x⁻¹ * s * x = s := (hx s).symm.trans hs
    calc x * s = x * (x⁻¹ * s * x) := by rw [h1]
      _ = s * x := by group
  have hxT : ∀ t ∈ T, x * t = t * x := fun t ht => hcomm t (hfixT t ht)
  have hxH : ∀ h ∈ H, x * h = h * x := fun h hh => hcomm h (hfixH h hh)
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    ext y
    rw [hx y, h]
    simp
  obtain ⟨v₀, hv₀V, hv₀1, hv₀T⟩ := SBd13.exists_fixed_ne_one hTS.1 hd.TV hd.V4
  rcases centralizer_le_two hW hTS x v₀ hxT hv₀T with h | h | h
  · exact hx1 h
  · exact hv₀1 h
  · refine hv₀1 (hd.fix v₀ hv₀V fun k hk => ?_)
    rw [← h]
    exact (hxH k hk).symm

theorem he_prime_inner
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.Carrier .He)
    (S : Subgroup X) (hS : quasithinIsSylowTwo S) (α : MulAut X) (hα : ∀ s ∈ S, α s = s)
    (hp : (orderOf α).Prime) : ∃ x : X, ∀ y : X, α y = x⁻¹ * y * x := by
  by_cases h2 : orderOf α = 2
  · have hsq : α * α = 1 := by
      rw [← sq, ← h2]
      exact pow_orderOf_eq_one α
    have hinv : ∀ x, α (α x) = x := fun x => by
      have := congrArg (fun β : MulAut X => β x) hsq
      simpa using this
    obtain ⟨P, hP⟩ := exists_sylow_eq hS
    exact CFSG.QuasithinUnique.Ch1.heAutInner X ⟨e⟩ α hinv ⟨P, fun t ht => hα t (hP ▸ ht)⟩
  · have hnd := A318P.not_dvd_outer_He e hp h2
    have hq : (QuotientGroup.mk α : Outer X) = 1 := by
      by_contra hne
      have hdvd : orderOf (QuotientGroup.mk α : Outer X) ∣ orderOf α :=
        orderOf_map_dvd (QuotientGroup.mk' (inner X)) α
      rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
      · exact hne (orderOf_eq_one_iff.1 h1)
      · exact hnd (h1 ▸ orderOf_dvd_natCard _)
    obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff α).1 hq
    exact ⟨g⁻¹, fun y => by rw [← hg]; simp [MulAut.conj_apply]⟩

theorem not_elConfig_he
    (hHe : FactHeCentralizer) : ¬ ElConfig (NativeSporadic.Carrier .He) := by
  have : Finite (NativeSporadic.Carrier .He) := (CFSG.Sporadic.He.fam_he_simplicity).1
  exact not_elConfig_of_prime_inner
    (fun S hS α hα hp => he_prime_inner (MulEquiv.refl _) S hS α hα hp) hHe

end CFSG.Quasithin.ModH.HeEl
