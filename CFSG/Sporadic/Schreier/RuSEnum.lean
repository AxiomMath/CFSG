module

public import CFSG.Sporadic.Schreier.RuCheckInv
public import CFSG.Sporadic.Schreier.RuCentralizer
public import CFSG.Sporadic.Schreier.RuConj

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] def ruChainS4060 : RawSchreierDatum 4060 :=
  RawSchreierDatum.ofArrays 4060 (by decide) (ruField4060 4) 4
    (by rw [ruField4060, Array.size_ofFn]; decide) (ruFinList 4060 (by decide) ruS4060ChainBase)
    (by decide) (ruWordsArr 4 6 ruS4060ChainDerivations)

theorem ruChainS4060_original :
    ruChainS4060.original.toList = ruSGens := by
  have h := ruInv_check.1
  have hg := ruInv_check.2.2.1
  rw [show ruChainS4060.original.toList = (List.range 4).map fun i => permOfArr 4060
    (ruField4060 4)[i]! from ofArrays_original_toList, show List.range 4 = [0, 1, 2, 3] from rfl,
    List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruSGens 0 (by decide))
      (hg 0 (by decide)),
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruSGens 1 (by decide))
      (hg 1 (by decide)),
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruSGens 2 (by decide))
      (hg 2 (by decide)),
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruSGens 3 (by decide))
      (hg 3 (by decide))]
  simp [ruSGens, ruSWords]

theorem ruChainS4060_sub :
    ruChainS4060.originalSubgroup = ruS := by
  rw [RawSchreierDatum.originalSubgroup, ruChainS4060_original]
  rfl

theorem ruS_card_of_count
    {p : Array ℕ → Bool} {P : Equiv.Perm (Fin 4060) → Prop}
    (hp : ∀ t g, Rep 4060 t g → (p t = true ↔ P g)) :
    Nat.card {g : ruS // P g} = count2 4060 ruLevS p := by
  have h := ruInv_check.1
  have key : Nat.card {g : ruChainS4060.originalSubgroup // P g} = count2 4060 ruLevS p :=
    chain_card_of_count2 (ruChain_arrays h) (by norm_num : 0 < 4) h rfl hp
  rw [ruChainS4060_sub] at key
  exact key

theorem ruS_forall
    {p : Array ℕ → Bool} {P : Equiv.Perm (Fin 4060) → Prop}
    (hp : ∀ t g, Rep 4060 t g → p t = true → P g) (hall : all2 4060 ruLevS p = true) :
    ∀ g ∈ ruS, P g := by
  have h := ruInv_check.1
  have hb : ruChainS4060.baseCount = 2 := rfl
  have key : ∀ g ∈ ruChainS4060.originalSubgroup, P g :=
    chain_forall_of_all2 (ruChain_arrays h) (by norm_num : 0 < 4) h (le_of_eq hb.symm)
      (fun i hi hi' => by
        have : i < 2 := lt_of_lt_of_eq hi' hb
        omega) hp hall
  rw [ruChainS4060_sub] at key
  exact key

theorem ncard_setOf_mem_and {G : Type*} [Group G] (H : Subgroup G) (P : G → Prop) :
    {t | t ∈ H ∧ P t}.ncard = Nat.card {g : H // P g} := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ H) P).symm

theorem ruIsInvolA_iff {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    ruIsInvolA t = true ↔ orderOf g = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_iff, ruIsInvolA, Bool.and_eq_true, Bool.not_eq_true',
    eqA_iff (rep_compA ht ht) rep_idA, pow_two]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h => ?_⟩
    rw [(eqA_iff ht rep_idA).2 h] at h2
    exact Bool.false_ne_true h2.symm
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases h : eqA 4060 t (idA 4060)
    · rfl
    · exact absurd ((eqA_iff ht rep_idA).1 h) h2

theorem ruFixCount_eq {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    ruFixCount t = (fixSet g).ncard := by
  rw [ruFixCount, ← ncard_finSet (pointList_fixedList t), finSet_fixedList ht]

end CFSG.Sporadic.RuSchreier
