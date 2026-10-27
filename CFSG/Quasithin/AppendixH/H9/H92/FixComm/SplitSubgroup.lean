module

public import CFSG.Quasithin.AppendixH.H9.H92.RadHyperplane
public import CFSG.Quasithin.AppendixH.H9.H92.RadCard.NatCardSubmodule

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def splitSub (n : ℕ) (D D₂ : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Subgroup (PairN n) where
  carrier := {x | ∃ a ∈ D, ∃ b ∈ D₂, x = pairVec a b}
  one_mem' := ⟨0, D.zero_mem, 0, D₂.zero_mem, pairVec_one⟩
  mul_mem' := by
    rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    exact ⟨a + a', D.add_mem ha ha', b + b', D₂.add_mem hb hb', pairVec_mul a b a' b'⟩
  inv_mem' := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, pairVec_inv a b⟩

theorem pairVec_mem_splitSub {n : ℕ} {D D₂ : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {a b : Fin n → ZMod 2} : pairVec a b ∈ splitSub n D D₂ ↔ a ∈ D ∧ b ∈ D₂ := by
  constructor
  · rintro ⟨a', ha', b', hb', h⟩
    obtain ⟨rfl, rfl⟩ := pairVec_inj.mp h
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl⟩

theorem splitSub_dotPerp_eq {n : ℕ} {U : Subgroup (PairN n)} (hU : U ≤ V1n n) :
    splitSub n (v1Space n U) (dotPerp n (v1Space n U)) = U ⊔ (V2n n ⊓ perpN n U) := by
  apply le_antisymm
  · rintro x ⟨a, ha, b, hb, rfl⟩
    have h1 : pairVec a 0 ∈ U := ha
    have h2 : pairVec 0 b ∈ V2n n ⊓ perpN n U := by
      refine Subgroup.mem_inf.mpr ⟨pairVec_mem_V2n b, mem_perpN.mpr fun s hs => ?_⟩
      obtain ⟨a', b', rfl⟩ := pairVec_surj s
      have hb' : b' = 0 := ofAdd_eq_one.mp (mem_V1n.mp (hU hs))
      subst hb'
      have ha' : a' ∈ v1Space n U := hs
      rw [polarN_pairVec, dotProduct_zero, zero_add, dotProduct_comm]
      exact hb a' ha'
    have hx : pairVec a b = pairVec a 0 * pairVec 0 b := by
      rw [pairVec_mul, add_zero, zero_add]
    rw [hx]
    exact Subgroup.mul_mem_sup h1 h2
  · refine sup_le ?_ ?_
    · intro u hu
      obtain ⟨a, b, rfl⟩ := pairVec_surj u
      have hb : b = 0 := ofAdd_eq_one.mp (mem_V1n.mp (hU hu))
      subst hb
      exact pairVec_mem_splitSub.mpr ⟨hu, Submodule.zero_mem _⟩
    · intro x hx
      obtain ⟨hx2, hxp⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨a, b, rfl⟩ := pairVec_surj x
      have ha : a = 0 := ofAdd_eq_one.mp (mem_V2n.mp hx2)
      subst ha
      refine pairVec_mem_splitSub.mpr ⟨Submodule.zero_mem _, fun d hd => ?_⟩
      have h := mem_perpN.mp hxp (pairVec d 0) hd
      rw [polarN_pairVec, dotProduct_zero, zero_add, dotProduct_comm] at h
      exact h

theorem card_splitSub {n : ℕ} (D D₂ : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card (splitSub n D D₂) = Nat.card D * Nat.card D₂ := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : D × D₂ => (⟨pairVec p.1 p.2, pairVec_mem_splitSub.mpr ⟨p.1.2, p.2.2⟩⟩ :
      splitSub n D D₂)) ⟨?_, ?_⟩)).symm
  · intro p q h
    obtain ⟨h1, h2⟩ := pairVec_inj.mp (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro ⟨x, a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem rk_splitSub_dotPerp (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    rk (splitSub n D (dotPerp n D)) = n := by
  have h := finrank_dotPerp_add n D
  show padicValNat 2 (Nat.card (splitSub n D (dotPerp n D))) = n
  rw [card_splitSub, natCard_submodule_zmod_two, natCard_submodule_zmod_two, ← pow_add,
    add_comm (Module.finrank (ZMod 2) D), h]
  exact padicValNat.prime_pow n

end CFSG.ASVolI.ChH
