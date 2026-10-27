module

public import CFSG.Sporadic.HeldB.OuterArith
public import CFSG.Sporadic.HeldB.CertPBridge
public import CFSG.Sporadic.HeldB.AutModelCheck
public import CFSG.Sporadic.Schreier.Outer

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Schreier

theorem heStrongPerm_mem
    {j : ℕ} (hj : j < 9) : heStrongPerm j ∈ heP := by
  rw [heP_eq_originalSubgroup]
  have h := heChain.strong_get_mem_originalSubgroup heChain_valid.1 ⟨j, hj⟩
  rwa [heChain_strong_get] at h

theorem heStabIdx_lt {j : ℕ} (hj : j ∈ heStabIdx) : j < 9 := by
  simp only [heStabIdx, List.mem_cons, List.not_mem_nil, or_false] at hj
  omega

theorem heStab_fix0
    {j : ℕ} (hj : j ∈ heStabIdx) : heStrongPerm j 0 = 0 := by
  apply Fin.ext
  rw [← rep_heStrong (heStabIdx_lt hj), Fin.val_zero]
  exact heStab_check.1 j hj

theorem heStab_moves
    (y : Fin 8330) (hy : y ≠ 0) : ∃ j ∈ heStabIdx, heStrongPerm j y ≠ y := by
  rcases heStab_check.2 y.val y.isLt with h | ⟨j, hj, hmove⟩
  · exact absurd (Fin.ext h) hy
  · refine ⟨j, hj, fun h => hmove ?_⟩
    rw [rep_heStrong (heStabIdx_lt hj), h]

theorem eq_one_of_centralizes_heP
    {x : Equiv.Perm (Fin 8330)} (hx : ∀ g ∈ heP, g * x = x * g) :
    x = 1 := by
  have h0 : x 0 = 0 := by
    by_contra hne
    obtain ⟨j, hj, hmove⟩ := heStab_moves (x 0) hne
    apply hmove
    have h := hx (heStrongPerm j) (heStrongPerm_mem (heStabIdx_lt hj))
    have e : (heStrongPerm j * x) 0 = (x * heStrongPerm j) 0 := by rw [h]
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at e
    rw [e, heStab_fix0 hj]
  refine Equiv.ext fun y => ?_
  have := heP_pretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq heP (0 : Fin 8330) y
  have hgy : (g : Equiv.Perm (Fin 8330)) 0 = y := hg
  have hgx := hx g g.2
  have e : ((g : Equiv.Perm (Fin 8330)) * x) 0 = (x * g) 0 := by rw [hgx]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at e
  rw [Equiv.Perm.one_apply, ← hgy, ← e, h0]

@[expose] def heConjR :
    heAutGroup →* MulAut heP :=
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe heP_le_heAutGroup)).toMonoidHom.comp
    (@MulAut.conjNormal _ _ (heP.subgroupOf heAutGroup) heP_normal_heAutGroup)

theorem heConjR_apply
    (x : heAutGroup) (g : heP) :
    ((heConjR x g : heP) : Equiv.Perm (Fin 8330)) = x * g * x⁻¹ := rfl

theorem heConjR_injective :
    Function.Injective heConjR := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply eq_one_of_centralizes_heP
  intro g hg
  have e := congrArg (fun α : MulAut heP => ((α ⟨g, hg⟩ : heP) : Equiv.Perm (Fin 8330)))
    (MonoidHom.mem_ker.1 hx)
  simp only [heConjR_apply, MulAut.one_apply, Subgroup.coe_inv] at e
  calc g * x = x * g * (x : Equiv.Perm (Fin 8330))⁻¹ * x := by rw [e]
    _ = x * g := by group

theorem card_heAutGroup :
    Nat.card heAutGroup = 8060774400 := by
  have h := Subgroup.card_mul_index (heP.subgroupOf heAutGroup)
  have hi : (heP.subgroupOf heAutGroup).index = 2 := heP_relIndex_heAutGroup
  rw [hi, Nat.card_congr (Subgroup.subgroupOfEquivOfLe heP_le_heAutGroup).toEquiv,
    card_heP] at h
  omega

theorem heP_center_eq_bot :
    Subgroup.center heP = ⊥ := by
  have hs := heP_simple
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center heP) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative heP := ⟨⟨fun a b => (Subgroup.mem_center_iff.1
      (h ▸ Subgroup.mem_top b) a)⟩⟩
    have hp := Group.is_simple_iff_prime_card.1 hs
    rw [card_heP] at hp
    exact absurd hp (by norm_num)

theorem card_inner_heP :
    Nat.card (inner heP) = 4030387200 := by
  rw [card_inner_of_center_eq_bot heP_center_eq_bot, card_heP]

theorem card_mulAut_le_of_equiv {G H : Type*} [Group G] [Group H] [Finite G] {k : ℕ}
    (hout : Nat.card (Outer G) ≤ k) (f : G ≃* H) : Nat.card (MulAut H) ≤ k * Nat.card G := by
  rw [← Nat.card_congr (MulAut.congr f).toEquiv,
    (inner G).card_eq_card_quotient_mul_card_subgroup]
  have hinn : Nat.card (inner G) ≤ Nat.card G :=
    Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  exact Nat.mul_le_mul hout hinn

theorem card_mulAut_heP_le
    (hout : Nat.card (Outer Blueprint.NativeSporadic.He) ≤ 2) :
    Nat.card (MulAut heP) ≤ 8060774400 := by
  have h := card_mulAut_le_of_equiv hout heEquivP
  rw [CFSG.Sporadic.He.card_He] at h
  exact h

theorem heConjR_map_heP :
    (heP.subgroupOf heAutGroup).map heConjR = (MulAut.conj : heP →* MulAut heP).range := by
  ext α
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx⟩, MulEquiv.ext fun g => Subtype.ext ?_⟩
    rw [heConjR_apply]
    rfl
  · rintro ⟨p, rfl⟩
    refine ⟨⟨p, heP_le_heAutGroup p.2⟩, p.2, MulEquiv.ext fun g => Subtype.ext ?_⟩
    rw [heConjR_apply]
    rfl

theorem heConjR_facts
    (hout : Nat.card (Outer Blueprint.NativeSporadic.He) ≤ 2) :
    Function.Bijective heConjR ∧ Nat.card (MulAut heP) = 8060774400 ∧
      IsCyclic (Outer heP) ∧ Nat.card (Outer heP) = 2 := by
  have hbij : Function.Bijective heConjR := heConjR_injective.bijective_of_nat_card_le
    (by rw [card_heAutGroup]; exact card_mulAut_heP_le hout)
  have hcard : Nat.card (MulAut heP) = 8060774400 := by
    rw [← card_heAutGroup]
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  have hout2 : Nat.card (Outer heP) = 2 := by
    have h := (inner heP).card_eq_card_quotient_mul_card_subgroup
    rw [hcard, card_inner_heP] at h
    change 8060774400 = Nat.card (Outer heP) * 4030387200 at h
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨hbij, hcard, isCyclic_of_prime_card hout2, hout2⟩

end CFSG.Sporadic.HeldB
