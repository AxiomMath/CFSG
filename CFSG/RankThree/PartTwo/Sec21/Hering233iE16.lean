module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iFaithful
public import CFSG.RankThree.PartTwo.Sec21.Hering233iCriticalInv
import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

theorem conj_mem_map_subtype_of_invariant {G : Type*} [Group G] {L : Subgroup G}
    {D : Subgroup L} (hD : ∀ σ : MulAut L, D.map σ.toMonoidHom = D) {e : G}
    (he : e ∈ Subgroup.normalizer (L : Set G)) {d : G} (hd : d ∈ D.map L.subtype) :
    e * d * e⁻¹ ∈ D.map L.subtype := by
  obtain ⟨d', hd', rfl⟩ := hd
  have hmem : L.normalizerMonoidHom ⟨e, he⟩ d' ∈ D := by
    rw [← hD (L.normalizerMonoidHom ⟨e, he⟩)]
    exact ⟨d', hd', rfl⟩
  exact ⟨_, hmem, rfl⟩

theorem mem_normalizer_map_subtype_of_invariant {G : Type*} [Group G] {L : Subgroup G}
    {D : Subgroup L} (hD : ∀ σ : MulAut L, D.map σ.toMonoidHom = D) {e : G}
    (he : e ∈ Subgroup.normalizer (L : Set G)) :
    e ∈ Subgroup.normalizer ((D.map L.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_map_subtype_of_invariant hD he hh, fun hh => ?_⟩
  have := conj_mem_map_subtype_of_invariant hD (Subgroup.inv_mem _ he) hh
  simpa [mul_assoc] using this

theorem linearOutcome_of_e16 {G : Type} [Group G] [Finite G]
    (hlocal : ∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3) {L : Subgroup G}
    [Group.IsPerfect L] {K₀ : Subgroup L} [K₀.Normal] [IsSimpleGroup (L ⧸ K₀)]
    (hK₀ : Group.IsSolvable K₀) (hO2 : CFSG.pCore 2 L = ⊥)
    (hO3 : CFSG.pCore 3 L ≤ Subgroup.center L) {E : Subgroup G}
    (hEc : ∀ a b : E, a * b = b * a) (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE16 : Nat.card E = 2 ^ 4)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) (p : ℕ) (hp : p.Prime)
    (hpS : Subgroup.centralizer (CFSG.pCore p L : Set L) ≤ K₀) :
    ∃ (N : Subgroup L) (_ : N.Normal), LinearOutcome L p N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hK₀top : K₀ ≠ ⊤ := QuotientGroup.nontrivial_iff.mp inferInstance
  have hctop : ∀ N : Subgroup L, N ≤ Subgroup.center L →
      ¬ Subgroup.centralizer (N : Set L) ≤ K₀ := by
    intro N hN hle
    rw [Subgroup.centralizer_eq_top_iff_subset.mpr hN, top_le_iff] at hle
    exact hK₀top hle
  have hne : CFSG.pCore p L ≠ ⊥ := by
    intro h
    rw [h] at hpS
    exact hctop ⊥ bot_le hpS
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hne hO2
  have hp3 : 3 < p := by
    have hp3' : p ≠ 3 := by
      rintro rfl
      exact hctop _ hO3 hpS
    have := hp.two_le
    omega
  obtain ⟨D, hD, hDinv⟩ := exists_criticalAt_invariant hp2 hne
  set DG : Subgroup G := D.map L.subtype with hDG
  have hDGp : IsPGroup p DG := (CFSG.pCore_isPGroup.to_le hD.le : IsPGroup p D).map L.subtype
  by_cases hinv : ∃ t : G, orderOf t = 2 ∧ ∀ d ∈ DG, d * t = t * d
  ·
    obtain ⟨t, ht, hDt⟩ := hinv
    have h1 : CFSG.pRank p DG ≤ localRank p G :=
      pRank_le_localRank_of_centralizes hp hp2 ht hDt
    have h2 := hlocal p hp hp3
    have h3 : CFSG.pRank p D = CFSG.pRank p DG :=
      CFSG.RankThree.PartTwo.pRank_congr_mulEquiv hp.one_lt
        (D.equivMapOfInjective L.subtype L.subtype_injective)
    have hD2 : CFSG.pRank p D ≤ 2 := by omega
    exact linearOutcome_of_criticalAt hK₀ hp3 hpS hD hD2
  ·
    exfalso
    push Not at hinv
    have hEN : E ≤ Subgroup.normalizer (DG : Set G) := fun e he =>
      mem_normalizer_map_subtype_of_invariant hDinv (hEL he)
    have hexp : ∀ x ∈ DG, x ^ p = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hD.exp x hx, map_one]
    have hcl : ∀ a ∈ DG, ∀ b ∈ DG, ∀ c ∈ DG, ⁅a, b⁆ * c = c * ⁅a, b⁆ := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      have := (hD.comm a ha b (hD.le hb)).2 c hc
      rw [← map_commutatorElement, ← map_mul, ← map_mul, this]
    have hfaith : ∀ e ∈ E, e ≠ 1 → ∃ d ∈ DG, e * d * e⁻¹ ≠ d := by
      intro e he he1
      by_contra hcon
      push Not at hcon
      have hord : orderOf e = 2 := orderOf_eq_prime (hE2 e he) he1
      obtain ⟨d, hd, hne'⟩ := hinv e hord
      apply hne' 
      have := hcon d hd
      calc d * e = e * d * e⁻¹ * e := by rw [this]
        _ = e * d := by group
    have hrank : ∀ e ∈ E, e ≠ 1 → ∀ H : Subgroup G, H ≤ DG → (∀ h ∈ H, h * e = e * h) →
        CFSG.pRank p H ≤ 2 := by
      intro e he he1 H _ hH
      have hord : orderOf e = 2 := orderOf_eq_prime (hE2 e he) he1
      have h1 := pRank_le_localRank_of_centralizes hp hp2 hord hH
      have h2 := hlocal p hp hp3
      omega
    have := card_le_eight_of_faithful hp2 hDGp hexp hcl hEc hE2 hEN hfaith hrank hE16
    omega

end CFSG.RankThree.PartTwo.Sec21.Hering233i
