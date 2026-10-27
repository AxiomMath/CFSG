module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHS
public import CFSG.Quasithin.EmptyFaithful.ModHJ2Core
public import CFSG.Quasithin.EmptyFaithful.ModHEl

public section

namespace CFSG.Quasithin.ModH.HSEl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.SporAutHS
open CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.Quasithin.ModH.SylowCore CFSG.Quasithin.R3c14

theorem eq_one_or_conj_of_pair {N : Type*} [Group N] (a b : N)
    (hgen : Subgroup.closure ({a, b} : Set N) = ⊤) (α : MulAut N) (ha : α a = a)
    (hb : α b = b ∨ α b = a * b * a⁻¹) : α = 1 ∨ α = MulAut.conj a := by
  rcases hb with hb | hb
  · left
    have h : α.toMonoidHom = MonoidHom.id N := by
      refine MonoidHom.eq_of_eqOn_top ?_
      rw [← hgen]
      refine MonoidHom.eqOn_closure ?_
      intro y hy
      rcases hy with h | h
      · rw [h]; exact ha
      · rw [Set.mem_singleton_iff] at h
        rw [h]; exact hb
    exact MulEquiv.ext fun x => by simpa using DFunLike.congr_fun h x
  · right
    have h : α.toMonoidHom = (MulAut.conj a).toMonoidHom := by
      refine MonoidHom.eq_of_eqOn_top ?_
      rw [← hgen]
      refine MonoidHom.eqOn_closure ?_
      intro y hy
      rcases hy with h | h
      · rw [h]
        change α a = a * a * a⁻¹
        rw [ha]; group
      · rw [Set.mem_singleton_iff] at h
        rw [h]; exact hb
    exact MulEquiv.ext fun x => by simpa using DFunLike.congr_fun h x

theorem hs_fixing_strong
    (α : MulAut hsChain.originalSubgroup)
    (hα : ∀ s : hsChain.originalSubgroup, (s : Equiv.Perm (Fin 3850)) ∈ s0Chain.originalSubgroup →
      α s = s) : α = 1 ∨ α = MulAut.conj A0 := by
  obtain ⟨hA0, hA1⟩ := hs_fixing_A1 α hα
  exact eq_one_or_conj_of_pair A0 A1 closure_A0_A1 α hA0 hA1

theorem card_P :
    Nat.card ↥hsChain.originalSubgroup = 44352000 := by
  rw [← hsP_eq_original]
  exact card_hsP

theorem factorization_two_card : (44352000 : ℕ).factorization 2 = 9 := by
  have h : (44352000 : ℕ) = 2 ^ 9 * 86625 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem s0_le_P :
    s0Chain.originalSubgroup ≤ hsChain.originalSubgroup :=
  s0_le_hs

theorem s0_le_centralizer_A0 :
    s0Chain.originalSubgroup ≤ Subgroup.centralizer {(A0 : Equiv.Perm (Fin 3850))} :=
  s0_le_centralizer

theorem strongSylow_hsOriginal :
    StrongSylow ↥hsChain.originalSubgroup := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := s0_le_P
  let T : Subgroup ↥hsChain.originalSubgroup :=
    s0Chain.originalSubgroup.subgroupOf hsChain.originalSubgroup
  have hTcard : Nat.card T = 2 ^ 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, s0_card]
    norm_num
  let S : Sylow 2 ↥hsChain.originalSubgroup :=
    Sylow.ofCard T (by rw [hTcard, card_P, factorization_two_card])
  have hS : (S : Subgroup ↥hsChain.originalSubgroup) = T := Sylow.coe_ofCard _ _
  have hA0S : (A0 : Equiv.Perm (Fin 3850)) ∈ s0Chain.originalSubgroup :=
    hsGen_zero_memS0
  refine ⟨S, A0, by rw [hS]; exact Subgroup.mem_subgroupOf.2 hA0S, ?_, ?_⟩
  · intro t ht
    rw [hS] at ht
    have h1 := Subgroup.mem_centralizer_iff.1 (s0_le_centralizer_A0 (Subgroup.mem_subgroupOf.1 ht))
      (A0 : Equiv.Perm (Fin 3850)) (Set.mem_singleton _)
    exact Subtype.ext h1
  · intro α hfix
    rw [hS] at hfix
    exact hs_fixing_strong α fun s hs => hfix s (Subgroup.mem_subgroupOf.2 hs)

theorem strongSylow_hs :
    StrongSylow (NativeSporadic.Carrier .HS) :=
  @StrongSylow.of_equiv (NativeSporadic.Carrier .HS) ↥hsChain.originalSubgroup _ _ _
    (hsPermEquiv.trans (MulEquiv.subgroupCongr hsP_eq_original)) strongSylow_hsOriginal

theorem center_eq_bot_hs :
    Subgroup.center (NativeSporadic.Carrier .HS) = ⊥ := by
  have hs : IsSimpleGroup (NativeSporadic.Carrier .HS) := (CFSG.Sporadic.HS.fam_hs_simplicity).2.2
  have hc : Nat.card (NativeSporadic.Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (NativeSporadic.Carrier .HS)) with h1 | h1
  · exact h1
  · exfalso
    have : IsMulCommutative (NativeSporadic.Carrier .HS) := Subgroup.center_eq_top_iff.1 h1
    have hp := Group.is_simple_iff_prime_card.1 hs
    rw [hc] at hp
    norm_num at hp

theorem not_elConfig_hs :
    ¬ ElConfig (NativeSporadic.Carrier .HS) := by
  have hs := strongSylow_hs
  have hZ := center_eq_bot_hs
  have : Finite (NativeSporadic.Carrier .HS) := (CFSG.Sporadic.HS.fam_hs_simplicity).1
  obtain ⟨P, hP⟩ := hs.exists_center_small hZ
  exact ModH.not_elConfig_of_center hs.pointwise
    (ModH.centerSmall_of_one (K1.isSylowTwoOf_top_iff.2 ⟨P.isPGroup', P.not_dvd_index⟩) hP)

end CFSG.Quasithin.ModH.HSEl
