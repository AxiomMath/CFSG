
module

public import CFSG.Sporadic.Schreier.RuCheckOrbLABase
public import CFSG.Sporadic.Schreier.RuCheckOrbLBBase
public import CFSG.Sporadic.Schreier.RuCheckBasicInputs
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
public import CFSG.Sporadic.Schreier.RuCheckLInputs
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Certificates.NativeSetOrbit
public import CFSG.Sporadic.Schreier.RuOrbLFacts
public import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
public meta import CFSG.Sporadic.Schreier.RuOrbLDefs
public import CFSG.Sporadic.Schreier.RuCheckTreeInputs
public import CFSG.Sporadic.Schreier.RuWitArrays
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Sporadic.Schreier.RuLOdd
public import CFSG.Sporadic.Schreier.RuZClass

@[expose] public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

theorem ruC_card_of_count
    {p : Array ℕ → Bool} {P : Equiv.Perm (Fin 4060) → Prop}
    (hp : ∀ t g, Rep 4060 t g → (p t = true ↔ P g)) :
    Nat.card {g : ruC // P g} = count3 4060 ruLevC p := by
  have h := ruChainC_check.1
  have key : Nat.card {g : ruChainC.originalSubgroup // P g} = count3 4060 ruLevC p :=
    chain_card_of_count3 (ruChain_arrays h) (by norm_num : 0 < 4) h rfl hp
  rw [ruChainC_sub] at key
  exact key

theorem ruLGens_getD_eq {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruLGens) :
    ∃ i < 3, g = ruLGen (i + 1) := by
  rw [ruLGens_eq] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩

theorem ruRepZ_mem (k : ℕ) : ruRepZ k ∈ ruZP := ruTZ_mem _

theorem ruReps_lt {k : ℕ} (hk : k < 19) : ruReps.getD k 0 < 593775 := by
  interval_cases k <;> decide

theorem ruOrb_sub (k : ℕ) : ruOrb k ⊆ ruZP := by
  rintro t ⟨l, hl, rfl⟩
  exact conj_mem_conjSet (ruRepZ_mem k) (ruL_le hl)

theorem getD_map_range {α : Type*} {f : ℕ → α} {n k : ℕ} (d : α) (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem ruSqZA_iff
    {r : Array ℕ} {R : Equiv.Perm (Fin 4060)} (hr : Rep 4060 r R) :
    ruSqZA r = true ↔ R * R = ruZ := by
  rw [ruSqZA, allLt_iff]
  constructor
  · intro H
    refine Equiv.ext fun x => Fin.ext ?_
    have := H x x.2
    rwa [beq_iff_eq, hr x, hr (R x), rep_ruZ x] at this
  · intro h i hi
    rw [beq_iff_eq, hr.apply hi, hr (R _), rep_ruZ.apply hi]
    exact congrArg Fin.val (congrArg (fun f : Equiv.Perm (Fin 4060) => f ⟨i, hi⟩) h)

instance :

    Finite ruL := Nat.finite_of_card_ne_zero (by rw [card_ruL]; norm_num)

theorem orderOf_eq_fourteen_iff {G : Type*} [Monoid G] {x : G} :
    orderOf x = 14 ↔ x ^ 14 = 1 ∧ x ^ 7 ≠ 1 ∧ x ^ 2 ≠ 1 := by
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one x, fun h7 => ?_, fun h2 => ?_⟩
    · have := orderOf_le_of_pow_eq_one (by norm_num) h7
      omega
    · have := orderOf_le_of_pow_eq_one (by norm_num) h2
      omega
  · rintro ⟨h14, h7, h2⟩
    exact orderOf_eq_fourteen h14 h7 h2

theorem ruOrd14_iff {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    ruOrd14 t = true ↔ orderOf g = 14 := by
  rw [orderOf_eq_fourteen_iff, ruOrd14, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.not_eq_true', eqA_iff (rep_powA ht 14) rep_idA]
  have e7 : eqA 4060 (powA 4060 t 7) (idA 4060) = false ↔ g ^ 7 ≠ 1 := by
    rw [← Bool.not_eq_true, eqA_iff (rep_powA ht 7) rep_idA]
  have e2 : eqA 4060 (powA 4060 t 2) (idA 4060) = false ↔ g ^ 2 ≠ 1 := by
    rw [← Bool.not_eq_true, eqA_iff (rep_powA ht 2) rep_idA]
  rw [e7, e2, and_assoc]

theorem orderOf_mul_of_mem_ruOrb
    {k : ℕ} {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruOrb k) :
    orderOf (ruA0 * t) = orderOf (ruA0 * ruRepZ k) := by
  obtain ⟨l, hl, rfl⟩ := ht
  have hc : l * ruA0 = ruA0 * l :=
    Subgroup.mem_centralizer_singleton_iff.1 (ruL_le_centralizer hl).2
  have e : ruA0 * (l * ruRepZ k * l⁻¹) = l * (ruA0 * ruRepZ k) * l⁻¹ := by
    calc ruA0 * (l * ruRepZ k * l⁻¹) = (ruA0 * l) * ruRepZ k * l⁻¹ := by group
      _ = (l * ruA0) * ruRepZ k * l⁻¹ := by rw [hc]
      _ = l * (ruA0 * ruRepZ k) * l⁻¹ := by group
  rw [e, orderOf_conj']

abbrev ruSpecial : List ℕ := [3, 6, 11]

end CFSG.Sporadic.RuSchreier
