module

public import CFSG.Quasithin.Vol2.Ch3T313A
public import CFSG.Quasithin.Vol2.Ch3T313B
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.EmptyFaithfulMultiple (L3213.vOf)

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_isXi {T X : Subgroup G} (hX : IsXi T X) : Group.IsSolvable X := by
  obtain ⟨-, -, -, p, hp, hp2, -, hidx, -⟩ := id hX
  have hpX : p ∣ Nat.card X := by
    have h : p ∣ (pCoreOf 2 X).relIndex X := by
      rcases hidx with h | ⟨h, -⟩ <;> rw [h] <;> exact dvd_pow_self p (by norm_num)
    exact h.trans (relIndex_dvd_card _ _)
  apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
  have hsub : (Nat.card X).primeFactors ⊆ {2, p} := by
    intro q hq
    obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.1 hq
    rcases hX.prime_dvd_card hp hp2 hpX hqp hqd with h | h <;> simp [h]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem isXiMinus_of_isHStar (h316 : Theorem316Statement)
    (h137 : EmptyFaithfulMultiple.Input137) {T X : Subgroup G} (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hXs : IsXiStarF T X) (hH : ∃ H : Subgroup G, IsHStar T (normalizer (X : Set G)) H) :
    IsXiMinus T X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : IsXi T X := hXs.1.1
  obtain ⟨-, -, -, p, hp, hp2, hpow, hidx, -⟩ := id hX
  have : Fact p.Prime := ⟨hp⟩
  have hpX : p ∣ Nat.card X := by
    have h : p ∣ (pCoreOf 2 X).relIndex X := by
      rcases hidx with h | ⟨h, -⟩ <;> rw [h] <;> exact dvd_pow_self p (by norm_num)
    exact h.trans (relIndex_dvd_card _ _)
  have hU := h137 G T hs hnab hQ hT X hXs.1
  have hsolv := isSolvable_of_isXi hX
  have hsubXT : IsSubnormal X (X ⊔ T) :=
    A3.subnormal_of_normal le_sup_left ((normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (EmptyFaithfulMultiple.L3213.sup_le_normalizer_of_isXi hX))
  have hVne : L3213.vOf T X ≠ ⊥ := (a4_9 hXs.2.1 hsubXT).mpr hXs.2.2
  obtain ⟨H, hHs⟩ := hH
  have hyp : Hyp318 T (normalizer (X : Set G)) X (L3213.vOf T X) :=
    { inM := ⟨hU.1.1, le_sup_right.trans hU.1.2⟩
      nonempty := ⟨H, hHs⟩
      perfect := hX.1
      le_M := le_normalizer
      normal := le_rfl
      unique := hU
      reduced := EmptyFaithfulMultiple.L3213.isTwoReducedIn_vOf hT hX hsolv hVne
      centralizer := T313.pCoreOf_sup_eq_inf_centralizer_vOf hT hX hsolv hVne }
  have hqh : qhatInt (X ⊔ T) (L3213.vOf T X) hyp.reduced.2.2.1 ≤ 2 := by
    rcases h316 G T hs hnab hQ hT _ (X ⊔ T) H (L3213.vOf T X) hyp.inM (hyp.hyp315 hT hHs) with
      h1 | ⟨-, h2, -⟩ | h3
    · exact absurd h1 (hyp.not_exists_normal hHs)
    · exact h2
    · exact (qhatInt_le_qInt _ _ _).trans h3
  have hp35 : p = 3 ∨ p = 5 := by
    obtain ⟨h1, h2, h3, h5⟩ := EmptyFaithfulMultiple.L3213.autOn_vOf_facts hT hX hpow
    have hV := hyp.reduced.2.2.1
    have hO2 := EmptyFaithfulMultiple.L3213.pCoreOf_autOn_vOf_eq_bot hT hX hsolv hVne
    let _ := commGroupOfElemAbelian hV
    have hVsq : ∀ v : ↥(L3213.vOf T X), v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
    exact (EmptyFaithfulMultiple.L3213.d2_13_data hVsq hp2 hqh hO2 h1 h2
      (fun y => ⟨1, Subtype.ext (by simpa using h3 y y.2)⟩) h5).1
  refine ⟨hX, ?_⟩
  rcases hp35 with rfl | rfl
  · exact Or.inl fun q hq hqX => hX.prime_dvd_card Nat.prime_three (by norm_num) hpX hq hqX
  · refine Or.inr ⟨fun q hq hqd => ?_,
      EmptyFaithfulMultiple.L3213.T313.prime_dvd_aut_eq_two_or_five hT hX hsolv hVne hqh hpow
        hidx⟩
    have hq5 : q ∣ 5 := by
      rcases hidx with h | ⟨h, -⟩ <;> rw [h] at hqd <;> exact hq.dvd_of_dvd_pow hqd
    exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hq5

end CFSG.Quasithin.H13.NQBlock
