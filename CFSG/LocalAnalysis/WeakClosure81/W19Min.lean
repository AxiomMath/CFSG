module

public import CFSG.LocalAnalysis.WeakClosure81.W19Basic
public import CFSG.LocalAnalysis.WeakClosure81.W19Fstar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo W19Aux
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp193

variable {D : Data G} {V₀ : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem card_eq_of_isSylowIn (h : Hyp193 D V₀ p X) {L S : Subgroup G} (hTL : D.T ≤ L)
    (hLH : L ≤ X ⊔ D.T) (hS : IsSylowIn p S L) :
    Nat.card ↥L = Nat.card ↥S * Nat.card ↥D.T := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 h.isPGroup
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 D.sylowM.isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.isPGroup
  have h1 := Subgroup.relIndex_mul_card S L
  rw [inf_eq_left.mpr hS.le] at h1
  have hLdvd : Nat.card ↥L ∣ p ^ a * 2 ^ b := by
    have := Subgroup.card_dvd_of_le hLH
    rwa [card_sup h, ha, hb] at this
  have hTdvd : 2 ^ b ∣ Nat.card ↥L := by
    have := Subgroup.card_dvd_of_le hTL
    rwa [hb] at this
  have hmp : ¬ p ∣ S.relIndex L := hS.not_dvd_relIndex
  have hcop : Nat.Coprime (S.relIndex L) (p ^ a) :=
    Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd h.prime).2 hmp).symm
  have hm1 : S.relIndex L ∣ 2 ^ b := hcop.dvd_of_dvd_mul_left ((Dvd.intro _ h1).trans hLdvd)
  have hcop2 : Nat.Coprime (2 ^ b) (p ^ k) :=
    Nat.Coprime.pow b k ((Nat.coprime_primes Nat.prime_two h.prime).2 (Ne.symm h.odd))
  have hm2 : 2 ^ b ∣ S.relIndex L := by
    have : 2 ^ b ∣ S.relIndex L * p ^ k := by rw [← hk, h1]; exact hTdvd
    exact hcop2.dvd_of_dvd_mul_right this
  have hmeq : S.relIndex L = 2 ^ b := Nat.dvd_antisymm hm1 hm2
  rw [← h1, hmeq, hk, hb, mul_comm]

theorem mul_eq_of_isSylowIn (h : Hyp193 D V₀ p X) {L S : Subgroup G} (hTL : D.T ≤ L)
    (hLH : L ≤ X ⊔ D.T) (hS : IsSylowIn p S L) :
    (S : Set G) * (D.T : Set G) = (L : Set G) ∧ (D.T : Set G) * (S : Set G) = (L : Set G) := by
  have hcard := h.card_eq_of_isSylowIn hTL hLH hS
  have hSbot : S ⊓ D.T = ⊥ :=
    inf_eq_bot_of_isPGroup h.prime h.odd hS.isPGroup D.sylowM.isPGroup
  refine ⟨coe_mul_eq_of_card hS.le hTL hSbot hcard, ?_⟩
  exact coe_mul_eq_of_card hTL hS.le (by rw [inf_comm]; exact hSbot) (by rw [hcard, mul_comm])

theorem sup_eq_of_isSylowIn (h : Hyp193 D V₀ p X) {L S : Subgroup G} (hTL : D.T ≤ L)
    (hLH : L ≤ X ⊔ D.T) (hS : IsSylowIn p S L) : S ⊔ D.T = L :=
  sup_eq_of_card hS.le hTL
    (inf_eq_bot_of_isPGroup h.prime h.odd hS.isPGroup D.sylowM.isPGroup)
    (h.card_eq_of_isSylowIn hTL hLH hS)

theorem of_isSylowIn (h : Hyp193 D V₀ p X) (hN₀ : D.M ≤ normalizer (V₀ : Set G))
    {L S : Subgroup G} (hTL : D.T ≤ L) (hLH : L ≤ X ⊔ D.T) (hS : IsSylowIn p S L)
    (hnc : ¬ IsCyclic S) : Hyp193 D V₀ p S where
  prime := h.prime
  odd := h.odd
  isPGroup := hS.isPGroup
  noncyclic := hnc
  exponent := by
    intro s hs
    obtain ⟨y, -, hSy⟩ := h.exists_conj_le (hS.le.trans hLH) hS.isPGroup
    have hs' : y * s * y⁻¹ ∈ X := mem_conjSubgroup_iff.1 (hSy hs)
    have := h.exponent _ hs'
    rw [conj_pow] at this
    exact conj_eq_one_iff.1 this
  inf_eq_bot := fun g hg hV => h.inf_conj_M_eq_bot hN₀ (hS.le.trans hLH) hS.isPGroup hg hV
  uniqueMax := fun Y hY hYc => by
    obtain ⟨y, hy, hSy⟩ := h.exists_conj_le (hS.le.trans hLH) hS.isPGroup
    exact h.uniqueMax_of_le_conj (h.le_M hy) (hY.trans hSy) hYc
  perm := by
    rw [(h.mul_eq_of_isSylowIn hTL hLH hS).1, (h.mul_eq_of_isSylowIn hTL hLH hS).2]
  le_M := by
    rw [h.sup_eq_of_isSylowIn hTL hLH hS]
    exact hLH.trans h.le_M
  fstar := by
    rw [h.sup_eq_of_isSylowIn hTL hLH hS]
    exact fstar_eq_pCoreOf_of_le hLH ((pCoreOf_le_T h).trans hTL) h.fstar

end Hyp193

theorem exists_minCex193 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    (hset : WeakClosureSetting D V₀ V) (hV₀ : V₀ ≠ ⊥) (hmbar : MBarGT D.M V₀ V 2)
    (hgamma : rankThreeGamma 1 2 (centerOf D.T) ≤ D.M) (hfail : ¬ Concl193 D V) :
    ∀ n : ℕ, ∀ X : Subgroup G, Nat.card ↥(X ⊔ D.T) = n → Hyp193 D V₀ p X →
      ∃ X' : Subgroup G, MinCex193 D V₀ V p X' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hn h
    by_cases hcyc : ∀ L : Subgroup G, D.T ≤ L → L < X ⊔ D.T →
        ∀ P : Subgroup G, P ≤ L → IsPGroup p P → IsCyclic P
    · exact ⟨X, ⟨hset, hV₀, hmbar, hgamma, h, hfail, hcyc⟩⟩
    · push_neg at hcyc
      obtain ⟨L, hTL, hLlt, P, hPL, hPp, hPnc⟩ := hcyc
      haveI : Fact p.Prime := ⟨h.prime⟩
      obtain ⟨S, hS, hPS⟩ := exists_isSylowIn_ge p hPL hPp
      have hSnc : ¬ IsCyclic S := fun hc => hPnc (isCyclic_of_le' hc hPS)
      have hSh : Hyp193 D V₀ p S :=
        h.of_isSylowIn (hset.normalizer₀ hV₀).ge hTL hLlt.le hS hSnc
      have hSL : S ⊔ D.T = L := h.sup_eq_of_isSylowIn hTL hLlt.le hS
      have hlt : Nat.card ↥(S ⊔ D.T) < n := by
        rw [hSL, ← hn]
        exact Subgroup.card_lt_of_lt hLlt
      exact ih _ hlt S rfl hSh

end CFSG.LocalAnalysis.WeakClosure81
