module

public import CFSG.Sporadic.Schreier.RuCheckL
public import CFSG.Sporadic.Schreier.RuWitness
public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Sporadic.Schreier.RuLocalFactsBase
public import CFSG.Sporadic.Schreier.RuWitReps

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] def ruChainL : RawSchreierDatum 4060 :=
  RawSchreierDatum.ofArrays 4060 (by decide) (ruField4060 5) 3
    (by rw [ruField4060, Array.size_ofFn]; decide) (ruFinList 4060 (by decide) ruLChainBase)
    (by decide) (ruWordsArr 3 6 ruLChainDerivations)

theorem ruChainL_original :
    ruChainL.original.toList = ruLGens := by
  have h := ruL_check.1
  have hg := ruL_check.2.2.1
  rw [show ruChainL.original.toList = (List.range 3).map fun i => permOfArr 4060
    (ruField4060 5)[i]! from ofArrays_original_toList, show List.range 3 = [0, 1, 2] from rfl,
    List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruLGen (i := 0) (by decide))
      (hg 0 (by decide)),
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruLGen (i := 1) (by decide))
      (hg 1 (by decide)),
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruLGen (i := 2) (by decide))
      (hg 2 (by decide)), ruLGens_eq]

theorem ruChainL_sub :
    ruChainL.originalSubgroup = ruL := by
  rw [RawSchreierDatum.originalSubgroup, ruChainL_original]
  rfl

theorem card_ruL :
    Nat.card ruL = 116480 := by
  have h : Nat.card ruChainL.originalSubgroup = _ := ruChain_card ruL_check.1
  rw [ruL_check.2.1, ruChainL_sub] at h
  exact h

theorem ruLGens_comm :
    ∀ g ∈ ruLGens, g * ruA0 = ruA0 * g := by
  intro g hg
  rw [ruLGens_eq] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  have key : ∀ i < 3, ruLGen (i + 1) * ruA0 = ruA0 * ruLGen (i + 1) := fun i hi =>
    eq_of_eqA (rep_compA (rep_ruLGen hi) rep_ruA0) (rep_compA rep_ruA0 (rep_ruLGen hi))
      (ruL_check.2.2.2.1 i hi)
  rcases hg with rfl | rfl | rfl
  · exact key 0 (by decide)
  · exact key 1 (by decide)
  · exact key 2 (by decide)

theorem ruL_le_centralizer :
    ruL ≤ ruP ⊓ Subgroup.centralizer {ruA0} :=
  closure_list_le fun g hg => ⟨ruLGens_mem g hg,
    Subgroup.mem_centralizer_singleton_iff.2 (ruLGens_comm g hg)⟩

theorem ruYp_pow
    {p : ℕ} (hp : p ∈ [5, 7, 13]) : ruYp p ^ p = 1 :=
  eq_of_eqA (rep_powA (rep_ruYp hp) p) rep_idA (ruL_check.2.2.2.2.1 p hp).1

theorem ruYp_ne_one
    {p : ℕ} (hp : p ∈ [5, 7, 13]) : ruYp p ≠ 1 := fun h => by
  have := (eqA_iff (rep_ruYp hp) rep_idA).2 h
  rw [(ruL_check.2.2.2.2.1 p hp).2] at this
  exact Bool.false_ne_true this

theorem prime_of_mem {p : ℕ} (hp : p ∈ [5, 7, 13]) : p.Prime := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem orderOf_ruYp
    {p : ℕ} (hp : p ∈ [5, 7, 13]) : orderOf (ruYp p) = p := by
  have : Fact p.Prime := ⟨prime_of_mem hp⟩
  exact orderOf_eq_prime (ruYp_pow hp) (ruYp_ne_one hp)

abbrev ruVp (p : ℕ) : Equiv.Perm (Fin 4060) :=
  (ruYp p * (ruLGen 3 * ruYp p * (ruLGen 3)⁻¹)) ^ 455

theorem rep_ruVp
    {p : ℕ} (hp : p ∈ [5, 7, 13]) : Rep 4060 (ruVpA p) (ruVp p) :=
  rep_powA (rep_compA (rep_ruYp hp) (rep_compA (rep_compA (rep_ruLGen (i := 2) (by decide))
    (rep_ruYp hp)) (rep_ruInv (rep_ruLGen (i := 2) (by decide))
      (ruWit_check.2.2.2.2.2.1 2 (by decide))))) 455

theorem ruVp_ne_one
    {p : ℕ} (hp : p ∈ [5, 7, 13]) : ruVp p ≠ 1 := fun h => by
  have := (eqA_iff (rep_ruVp hp) rep_idA).2 h
  rw [(ruL_check.2.2.2.2.2 p hp).1] at this
  exact Bool.false_ne_true this

theorem ruVp_pow
    {p : ℕ} (hp : p ∈ [5, 7, 13]) : ruVp p ^ 256 = 1 :=
  eq_of_eqA (rep_powA (rep_ruVp hp) 256) rep_idA (ruL_check.2.2.2.2.2 p hp).2

end CFSG.Sporadic.RuSchreier
