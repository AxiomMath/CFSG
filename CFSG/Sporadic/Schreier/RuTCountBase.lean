
module

public import CFSG.Sporadic.Schreier.RuOrbLBase
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

@[expose] public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

abbrev ruT : Set (Equiv.Perm (Fin 4060)) :=
  {x | x ∈ ruP ∧ x ^ 2 ∈ ruZP ∧ (ruA0 * x) ^ 13 = 1 ∧ orderOf (ruA0 * x ^ 2) = 14 ∧
    (ruA0 * x * ruA0 * x ^ 2) ^ 29 = 1}

abbrev ruFib (t : Equiv.Perm (Fin 4060)) : Set (Equiv.Perm (Fin 4060)) :=
  {x | x ∈ ruP ∧ x ^ 2 = t ∧ (ruA0 * x) ^ 13 = 1 ∧ (ruA0 * x * ruA0 * x ^ 2) ^ 29 = 1}

theorem conj_injective' (g : Equiv.Perm (Fin 4060)) :
    Function.Injective fun x : Equiv.Perm (Fin 4060) => g * x * g⁻¹ := fun x y h => by
  simpa using h

theorem mem_ruC_of_sq
    {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruP) (h : x ^ 2 = ruZ) :
    x ∈ ruC := by
  rw [ruC_eq_centralizer]
  refine ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [← h, pow_two, mul_assoc]

theorem ruFibTest_iff
    {gA giA t : Array ℕ} {g r : Equiv.Perm (Fin 4060)} (hg : Rep 4060 gA g)
    (hgi : Rep 4060 giA g⁻¹) (ht : Rep 4060 t r) :
    ruFibTest gA giA t = true ↔ (ruA0 * (g * r * g⁻¹)) ^ 13 = 1 ∧
      (ruA0 * (g * r * g⁻¹) * ruA0 * (g * r * g⁻¹) ^ 2) ^ 29 = 1 := by
  have hx : Rep 4060 (compA 4060 (compA 4060 gA t) giA) (g * r * g⁻¹) :=
    rep_compA (rep_compA hg ht) hgi
  have hax := rep_compA rep_ruA0 hx
  rw [ruFibTest, Bool.and_eq_true, eqA_iff (rep_powA hax 13) rep_idA,
    eqA_iff (rep_powA (rep_compA (rep_compA hax rep_ruA0) (rep_compA hx hx)) 29) rep_idA,
    pow_two]

abbrev ruRepG (k : ℕ) : Equiv.Perm (Fin 4060) := ruTElt 64 (ruReps.getD k 0)

theorem ruFib_rep_eq
    (k : ℕ) : ruFib (ruRepZ k) = (fun r => ruRepG k * r * (ruRepG k)⁻¹) ''
    {r | r ∈ ruC ∧ (r ^ 2 = ruZ ∧ (ruA0 * (ruRepG k * r * (ruRepG k)⁻¹)) ^ 13 = 1 ∧
      (ruA0 * (ruRepG k * r * (ruRepG k)⁻¹) * ruA0 *
        (ruRepG k * r * (ruRepG k)⁻¹) ^ 2) ^ 29 = 1)} := by
  set g := ruRepG k
  have hg : g ∈ ruP := ruTElt_mem 64 _
  have hz : ruRepZ k = g * ruZ * g⁻¹ := rfl
  ext x
  constructor
  · rintro ⟨hx, h2, h13, h29⟩
    have hr : g⁻¹ * x * g ∈ ruP := ruP.mul_mem (ruP.mul_mem (ruP.inv_mem hg) hx) hg
    have hsq : (g⁻¹ * x * g) ^ 2 = ruZ := by
      have := conj_pow (a := g⁻¹) (b := x) (i := 2)
      rw [inv_inv] at this
      rw [this, h2, hz]
      group
    have he : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    refine ⟨g⁻¹ * x * g, ⟨mem_ruC_of_sq hr hsq, hsq, ?_, ?_⟩, he⟩
    · rw [he]
      exact h13
    · rw [he]
      exact h29
  · rintro ⟨r, ⟨hr, hsq, h13, h29⟩, rfl⟩
    refine ⟨ruP.mul_mem (ruP.mul_mem hg (ruC_le hr)) (ruP.inv_mem hg), ?_, h13, h29⟩
    rw [conj_pow, hsq, hz]

theorem ncard_ruFib_rep
    (k : ℕ) : (ruFib (ruRepZ k)).ncard = ruFibCount k := by
  rw [ruFib_rep_eq, Set.ncard_image_of_injective _ (conj_injective' _),
    ncard_setOf_mem_and ruC (fun r => r ^ 2 = ruZ ∧
      (ruA0 * (ruRepG k * r * (ruRepG k)⁻¹)) ^ 13 = 1 ∧
      (ruA0 * (ruRepG k * r * (ruRepG k)⁻¹) * ruA0 * (ruRepG k * r * (ruRepG k)⁻¹) ^ 2) ^ 29 =
        1),
    ruC_card_of_count (P := fun r => r ^ 2 = ruZ ∧
      (ruA0 * (ruRepG k * r * (ruRepG k)⁻¹)) ^ 13 = 1 ∧
      (ruA0 * (ruRepG k * r * (ruRepG k)⁻¹) * ruA0 * (ruRepG k * r * (ruRepG k)⁻¹) ^ 2) ^ 29 =
        1) (p := fun r => ruSqZA r &&
      ruFibTest (ruTEltA 64 (ruReps.getD k 0)) (ruTEltInvA 64 (ruReps.getD k 0)) r)
      fun t r ht => by
        rw [Bool.and_eq_true, ruSqZA_iff ht, ← pow_two,
          ruFibTest_iff (rep_ruTElt 64 _) (rep_ruTEltInv 64 _) ht]]
  rfl

theorem conj_mul_comm_ruA0
    {l : Equiv.Perm (Fin 4060)} (hl : l ∈ ruL) (x : Equiv.Perm (Fin 4060)) :
    ruA0 * (l * x * l⁻¹) = l * (ruA0 * x) * l⁻¹ := by
  have hc : l * ruA0 = ruA0 * l :=
    Subgroup.mem_centralizer_singleton_iff.1 (ruL_le_centralizer hl).2
  calc ruA0 * (l * x * l⁻¹) = (ruA0 * l) * x * l⁻¹ := by group
    _ = (l * ruA0) * x * l⁻¹ := by rw [hc]
    _ = l * (ruA0 * x) * l⁻¹ := by group

theorem ruFib_conj_sub
    {l : Equiv.Perm (Fin 4060)} (hl : l ∈ ruL) (t : Equiv.Perm (Fin 4060)) :
    (fun x => l * x * l⁻¹) '' ruFib t ⊆ ruFib (l * t * l⁻¹) := by
  rintro _ ⟨x, ⟨hx, h2, h13, h29⟩, rfl⟩
  have hlP := ruL_le hl
  refine ⟨ruP.mul_mem (ruP.mul_mem hlP hx) (ruP.inv_mem hlP), by rw [conj_pow, h2], ?_, ?_⟩
  · rw [conj_mul_comm_ruA0 hl, conj_pow, h13]
    group
  · have e : ruA0 * (l * x * l⁻¹) * ruA0 * (l * x * l⁻¹) ^ 2 =
        l * (ruA0 * x * ruA0 * x ^ 2) * l⁻¹ := by
      rw [conj_mul_comm_ruA0 hl, conj_pow]
      have hc : l * ruA0 = ruA0 * l :=
        Subgroup.mem_centralizer_singleton_iff.1 (ruL_le_centralizer hl).2
      calc l * (ruA0 * x) * l⁻¹ * ruA0 * (l * x ^ 2 * l⁻¹)
          = l * (ruA0 * x) * (l⁻¹ * (ruA0 * l)) * x ^ 2 * l⁻¹ := by group
        _ = l * (ruA0 * x) * (l⁻¹ * (l * ruA0)) * x ^ 2 * l⁻¹ := by rw [hc]
        _ = l * (ruA0 * x * ruA0 * x ^ 2) * l⁻¹ := by group
    rw [e, conj_pow, h29]
    group

theorem ncard_ruFib_conj
    {l : Equiv.Perm (Fin 4060)} (hl : l ∈ ruL) (t : Equiv.Perm (Fin 4060)) :
    (ruFib (l * t * l⁻¹)).ncard = (ruFib t).ncard := by
  have heq : ruFib (l * t * l⁻¹) = (fun x => l * x * l⁻¹) '' ruFib t := by
    refine (Set.Subset.antisymm ?_ (ruFib_conj_sub hl t))
    intro y hy
    have h := ruFib_conj_sub (ruL.inv_mem hl) (l * t * l⁻¹) ⟨y, hy, rfl⟩
    have e : l⁻¹ * (l * t * l⁻¹) * l⁻¹⁻¹ = t := by group
    rw [e] at h
    exact ⟨l⁻¹ * y * l⁻¹⁻¹, h, by group⟩
  rw [heq, Set.ncard_image_of_injective _ (conj_injective' l)]

theorem ncard_ruFib_of_mem_ruOrb
    {k : ℕ} {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruOrb k) :
    (ruFib t).ncard = (ruFib (ruRepZ k)).ncard := by
  obtain ⟨l, hl, rfl⟩ := ht
  exact ncard_ruFib_conj hl _

end CFSG.Sporadic.RuSchreier
